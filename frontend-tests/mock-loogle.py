#!/usr/bin/env python3
"""Mock loogle backend for testing server.py.

Speaks the same line-based JSON protocol as `loogle --json --interactive`:
prints `Loogle is ready.` on stdout, then for each newline-terminated query
read from stdin, writes one JSON line to stdout.

Pass to server.py with `--loogle-bin ./mock-loogle.py`. Any --json /
--interactive / other args are accepted and ignored.

Special query strings (matched verbatim) trigger specific behaviours:

  block <path>     Open <path> for reading and block until a writer attaches
                   *and* sends at least one byte. The test driver creates
                   <path> as a FIFO and pairs the open() to know exactly
                   when the worker is committed — no sleeps, no races.
                   Returns once unblocked.
  crash            Exit with code 1 (simulates a crashed backend).
  sandbox          Kill self with SIGSYS so `Popen.poll()` returns -31
                   (the sandbox-escape path).
  error            Return {"error": "mock error message"}.
  <anything else>  Return a sample result with one hit.

Env vars:
  MOCK_NO_GREETING=1       Send a wrong greeting line, to exercise the
                           greeting-failure path in Loogle.start().
  MOCK_FAIL_GREETING_IF=<path>
                           Send a wrong greeting iff <path> exists at
                           startup. Lets a test arm the next subprocess
                           invocation to fail without affecting the
                           first one — useful for exercising the
                           "restart itself failed" branch.
"""
import sys
import os
import json
import signal


def handle(query):
    if query == "crash":
        sys.exit(1)
    if query == "sandbox":
        os.kill(os.getpid(), signal.SIGSYS)  # signal 31 on Linux -> poll() == -31
        sys.exit(1)  # in case the signal is queued
    if query == "error":
        return {"error": "mock error message"}
    if query.startswith("block "):
        path = query[len("block "):]
        # open() on a FIFO blocks until a writer attaches; the subsequent
        # read() blocks until the writer sends a byte. Both halves give
        # the test a deterministic synchronization point with no sleeps.
        with open(path, "r") as f:
            f.read(1)
        return {"header": f"unblocked {path}", "count": 0, "hits": [], "heartbeats": 0}
    return {
        "header": f"Mock results for: {query}",
        "count": 1,
        "hits": [{
            "name": "Mock.example",
            "module": "Mock.Example",
            "type": "Nat → Nat",
        }],
        "heartbeats": 1,
    }


def main():
    fail_if = os.environ.get("MOCK_FAIL_GREETING_IF")
    bad = bool(os.environ.get("MOCK_NO_GREETING")) \
        or (fail_if is not None and os.path.exists(fail_if))
    if bad:
        sys.stdout.write("not a greeting\n")
    else:
        sys.stdout.write("Loogle is ready.\n")
    sys.stdout.flush()

    for line in sys.stdin:
        query = line.rstrip("\n")
        result = handle(query)
        sys.stdout.write(json.dumps(result) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
