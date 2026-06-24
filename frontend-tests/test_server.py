#!/usr/bin/env python3
"""End-to-end tests for server.py, driven against mock-loogle.py.

Race-free: every concurrency assertion synchronizes through a FIFO that
the mock blocks on. The test pairs the FIFO's open() with the mock's
open() to know exactly when the worker has been taken from the pool —
no sleeps gating concurrent state.

Run directly:   ./frontend-tests/test_server.py
Or via Python:  python3 -m unittest frontend-tests.test_server -v
"""
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TESTS_DIR = Path(__file__).resolve().parent
MOCK_PATH = TESTS_DIR / "mock-loogle.py"

# Polling intervals used while waiting for an observable state change
# (worker readiness, log line appearing, port opening). These are NOT
# synchronization sleeps — they just bound how often we re-check a
# condition that will deterministically become true.
POLL_INTERVAL = 0.02
DEFAULT_TIMEOUT = 15.0

WORKER_READY_RE = re.compile(r"Worker \d+ ready\.")


def _free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


class Server:
    """Lifecycle wrapper around a `python3 server.py` subprocess."""

    def __init__(self, workers, env_overrides=None, startup_timeout=5.0):
        self.workers = workers
        self.env_overrides = env_overrides or {}
        self.startup_timeout = startup_timeout
        self.port = _free_port()
        self.proc = None
        self.log_path = None
        self._log_fh = None

    @property
    def base_url(self):
        return f"http://127.0.0.1:{self.port}"

    def start(self):
        fd, log_path = tempfile.mkstemp(prefix="loogle-test-", suffix=".log")
        self._log_fh = os.fdopen(fd, "wb")
        self.log_path = Path(log_path)
        env = os.environ.copy()
        env.update(self.env_overrides)
        self.proc = subprocess.Popen(
            [sys.executable, "server.py",
             "--host", "127.0.0.1",
             "--port", str(self.port),
             "--workers", str(self.workers),
             "--restart-delay", "0.05",
             "--startup-timeout", str(self.startup_timeout),
             "--loogle-bin", str(MOCK_PATH)],
            cwd=str(ROOT),
            env=env,
            stdout=self._log_fh,
            stderr=subprocess.STDOUT,
        )

    def stop(self):
        if self.proc and self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait()
        if self._log_fh:
            self._log_fh.close()
            self._log_fh = None
        if self.log_path and self.log_path.exists():
            self.log_path.unlink()

    def _read_log(self):
        if not self.log_path or not self.log_path.exists():
            return ""
        return self.log_path.read_text(errors="replace")

    def _assert_alive(self):
        if self.proc.poll() is not None:
            raise RuntimeError(
                f"server exited with code {self.proc.returncode}\n--- log ---\n{self._read_log()}")

    def wait_listening(self, timeout=DEFAULT_TIMEOUT):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            self._assert_alive()
            try:
                with socket.create_connection(("127.0.0.1", self.port), timeout=0.2):
                    return
            except OSError:
                time.sleep(POLL_INTERVAL)
        raise RuntimeError(f"server never opened port {self.port}\n--- log ---\n{self._read_log()}")

    def wait_workers_ready(self, n, timeout=DEFAULT_TIMEOUT):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            self._assert_alive()
            if len(WORKER_READY_RE.findall(self._read_log())) >= n:
                return
            time.sleep(POLL_INTERVAL)
        raise RuntimeError(
            f"only saw {len(WORKER_READY_RE.findall(self._read_log()))}/{n} workers ready\n"
            f"--- log ---\n{self._read_log()}")

    def wait_log(self, needle, timeout=DEFAULT_TIMEOUT):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if needle in self._read_log():
                return
            time.sleep(POLL_INTERVAL)
        raise RuntimeError(f"log never contained {needle!r}\n--- log ---\n{self._read_log()}")


TEST_USER_AGENT = "loogle-tests/0"


def _do_request(req):
    """Run a urllib request, returning (status, headers_dict, body_text).
    Treats 4xx/5xx as values rather than exceptions."""
    req.add_unredirected_header("User-Agent", TEST_USER_AGENT)
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.status, dict(r.headers), r.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers), e.read().decode("utf-8")


def http_get(server, path):
    req = urllib.request.Request(server.base_url + path)
    return _do_request(req)


def http_post_json(server, path, payload):
    req = urllib.request.Request(
        server.base_url + path,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    return _do_request(req)


class WorkerHold:
    """Hold one worker on the server by issuing a `block <fifo>` query.

    Usage::

        with WorkerHold(server) as hold:
            # control is yielded only after the worker is committed
            # (mock is inside read()) — assert overload state here.
            ...
        # __exit__ releases the FIFO and joins the request thread.
        assert hold.status == 200
    """

    def __init__(self, server):
        self.server = server
        self.fifo = Path(tempfile.mkdtemp(prefix="loogle-test-")) / "f"
        self._fd = None
        self._thread = None
        self.status = None
        self.body = None
        self.headers = None
        self._error = None

    def __enter__(self):
        os.mkfifo(str(self.fifo))
        encoded = urllib.parse.quote(f"block {self.fifo}")
        url = self.server.base_url + "/json?q=" + encoded

        def fetch():
            try:
                self.status, self.headers, self.body = _do_request(
                    urllib.request.Request(url))
            except Exception as e:
                self._error = e

        self._thread = threading.Thread(target=fetch, daemon=True)
        self._thread.start()
        # Pair the FIFO. open(WR) blocks until the mock has opened the
        # read side, which only happens AFTER server.py's pool.get()
        # committed and the mock has read the query. When this returns:
        # - the worker is out of the pool,
        # - the mock is parked in read(), waiting for us to write.
        self._fd = os.open(str(self.fifo), os.O_WRONLY)
        return self

    def __exit__(self, *exc):
        if self._fd is not None:
            try:
                os.write(self._fd, b"x")
            finally:
                os.close(self._fd)
                self._fd = None
        if self._thread is not None:
            self._thread.join(timeout=15)
        try:
            self.fifo.unlink()
        except OSError:
            pass
        try:
            self.fifo.parent.rmdir()
        except OSError:
            pass
        if self._error is not None:
            raise self._error


# ---------------------------------------------------------------------------
# Single-worker scenarios
# ---------------------------------------------------------------------------

class SingleWorkerTests(unittest.TestCase):
    server: Server

    @classmethod
    def setUpClass(cls):
        cls.server = Server(workers=1)
        cls.server.start()
        cls.server.wait_listening()
        cls.server.wait_workers_ready(1)

    @classmethod
    def tearDownClass(cls):
        cls.server.stop()

    def test_normal_query_returns_hit(self):
        status, _, body = http_get(self.server, "/json?q=hello")
        self.assertEqual(status, 200)
        data = json.loads(body)
        self.assertEqual(data["hits"][0]["name"], "Mock.example")

    def test_backend_error_surfaces_in_200(self):
        status, _, body = http_get(self.server, "/json?q=error")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body)["error"], "mock error message")

    def test_json_load_shed(self):
        with WorkerHold(self.server) as hold:
            status, headers, body = http_get(self.server, "/json?q=hello")
            self.assertEqual(status, 503)
            self.assertEqual(headers.get("Retry-After"), "5")
            self.assertIn("under load", json.loads(body).get("error", ""))
        self.assertEqual(hold.status, 200)

    def test_html_load_shed(self):
        with WorkerHold(self.server) as hold:
            status, headers, body = http_get(self.server, "/?q=hello")
            self.assertEqual(status, 503)
            self.assertEqual(headers.get("Retry-After"), "5")
            self.assertIn("Loogle is currently under load", body)
        self.assertEqual(hold.status, 200)

    def test_zulipbot_load_shed_stays_200(self):
        with WorkerHold(self.server) as hold:
            status, _, body = http_post_json(
                self.server, "/zulipbot",
                {"data": "@**loogle** anything"})
            self.assertEqual(status, 200)
            self.assertIn("under load", json.loads(body)["content"])
        self.assertEqual(hold.status, 200)

    def test_z_crash_triggers_restart(self):
        # Prefixed `z_` so it runs after the load-shed tests (unittest sorts
        # alphabetically). The 5s restart-wait inside server.py burns real
        # wall clock, so we'd rather pay it once.
        status, _, body = http_get(self.server, "/json?q=crash")
        self.assertEqual(status, 200)
        self.assertIn("died with code", json.loads(body)["error"])
        # Worker is respawned synchronously inside the same request, so the
        # next call should succeed without further waiting.
        status, _, body = http_get(self.server, "/json?q=after-crash")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body)["hits"][0]["name"], "Mock.example")

    def test_z_sandbox_triggers_restart(self):
        status, _, body = http_get(self.server, "/json?q=sandbox")
        self.assertEqual(status, 200)
        self.assertIn("sandbox", json.loads(body)["error"])
        status, _, body = http_get(self.server, "/json?q=after-sandbox")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body)["hits"][0]["name"], "Mock.example")


# ---------------------------------------------------------------------------
# Two-worker scenario
# ---------------------------------------------------------------------------

class TwoWorkerTests(unittest.TestCase):
    server: Server

    @classmethod
    def setUpClass(cls):
        cls.server = Server(workers=2)
        cls.server.start()
        cls.server.wait_listening()
        cls.server.wait_workers_ready(2)

    @classmethod
    def tearDownClass(cls):
        cls.server.stop()

    def test_two_parallel_succeed_third_503s(self):
        with WorkerHold(self.server) as a, WorkerHold(self.server) as b:
            # Both workers are now held. A third request must 503 instantly.
            status, headers, _ = http_get(self.server, "/json?q=hello")
            self.assertEqual(status, 503)
            self.assertEqual(headers.get("Retry-After"), "5")
        self.assertEqual(a.status, 200)
        self.assertEqual(b.status, 200)


# ---------------------------------------------------------------------------
# Greeting failure: worker never enters the pool
# ---------------------------------------------------------------------------

class NoGreetingTests(unittest.TestCase):
    server: Server

    @classmethod
    def setUpClass(cls):
        cls.server = Server(workers=1, env_overrides={"MOCK_NO_GREETING": "1"})
        cls.server.start()
        cls.server.wait_listening()
        # Block until server.py has logged the bring-up failure. Without
        # this, our query might race against the bring-up thread.
        cls.server.wait_log("did not send expected greeting")
        cls.server.wait_log("did not come up cleanly")

    @classmethod
    def tearDownClass(cls):
        cls.server.stop()

    def test_query_503s_when_pool_empty(self):
        status, headers, body = http_get(self.server, "/json?q=hello")
        self.assertEqual(status, 503)
        self.assertEqual(headers.get("Retry-After"), "5")
        self.assertIn("under load", json.loads(body).get("error", ""))


class StartupTimeoutTests(unittest.TestCase):
    """A backend that hangs without printing a greeting must hit the
    startup-timeout, get killed, and stay out of the pool — never
    leaving a request thread blocked on readline()."""

    server: Server

    @classmethod
    def setUpClass(cls):
        cls.server = Server(
            workers=1,
            env_overrides={"MOCK_HANG_BEFORE_GREETING": "1"},
            startup_timeout=0.3,
        )
        cls.server.start()
        cls.server.wait_listening()

    @classmethod
    def tearDownClass(cls):
        cls.server.stop()

    def test_hanging_startup_times_out(self):
        # Wait for the bring-up thread to log the timeout.
        self.server.wait_log("did not send greeting within 0.3s")
        self.server.wait_log("did not come up cleanly")
        # Pool stays empty; queries load-shed.
        status, _, _ = http_get(self.server, "/json?q=hello")
        self.assertEqual(status, 503)


class WorkerLostTests(unittest.TestCase):
    """If a worker dies AND the restart attempt also fails, the worker
    should be dropped from the pool entirely (not silently re-pooled in
    a broken state)."""

    server: Server
    fail_marker: Path

    @classmethod
    def setUpClass(cls):
        # Path is passed to the mock; the file is absent at startup so
        # the initial spawn sends a valid greeting. The test creates the
        # file later, arming the *next* spawn to fail.
        fd, path = tempfile.mkstemp(prefix="loogle-test-fail-")
        os.close(fd)
        cls.fail_marker = Path(path)
        cls.fail_marker.unlink()
        cls.server = Server(workers=1, env_overrides={
            "MOCK_FAIL_GREETING_IF": str(cls.fail_marker),
        })
        cls.server.start()
        cls.server.wait_listening()
        cls.server.wait_workers_ready(1)

    @classmethod
    def tearDownClass(cls):
        cls.server.stop()
        if cls.fail_marker.exists():
            cls.fail_marker.unlink()

    def test_failed_restart_drops_worker(self):
        # Arm: the next mock subprocess will see this file and refuse
        # to send a valid greeting.
        self.fail_marker.touch()
        status, _, body = http_get(self.server, "/json?q=crash")
        self.assertEqual(status, 200)
        self.assertIn("removing worker from pool", json.loads(body)["error"])
        # Pool is now empty for the rest of the process's life.
        status, _, _ = http_get(self.server, "/json?q=hello")
        self.assertEqual(status, 503)
        # And the server should have logged the loss.
        self.server.wait_log("Worker is dead after attempted restart")


if __name__ == "__main__":
    unittest.main(verbosity=2)
