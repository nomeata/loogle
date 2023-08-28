#!/usr/bin/env python3

from http.server import BaseHTTPRequestHandler, HTTPServer
import urllib
import subprocess
import json
import html
import sys
import time

hostName = "localhost"
serverPort = 8080

blurb = open("blurb.html","rb").read()

class Loogle():
    def start(self):
        self.loogle = subprocess.Popen(
            ["./build/bin/loogle","--json", "--interactive"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )

    def __init__(self):
        self.start()

    def query(self, query):
        try:
            self.loogle.stdin.write(bytes(query, "utf8"));
            self.loogle.stdin.write(b"\n");
            self.loogle.stdin.flush();
            output = self.loogle.stdout.readline()
            return json.loads(output)
        except (IOError, json.JSONDecodeError) as e:
            time.sleep(5) # to allow the process to die
            code = self.loogle.poll()
            if code == -31:
                sys.stderr.write(f"Backend died trying to escape the sandbox.\n")
                self.start()
                return {"error":
                    f"Backend died trying to escape the sandbox. Restarting..."
                }
            if code is not None:
                sys.stderr.write(f"Backend died with code {code}.\n")
                self.start()
                return {"error":
                    f"The backend process died with code {code}. Restarting..."
                }
            else:
                sys.stderr.write(f"Backend did not respond ({e}).\n")
                self.loogle.kill() # just to be sure
                self.start()
                return {"error": "The backend process did not respond, killing and restarting..."}

loogle = Loogle()

class MyHandler(BaseHTTPRequestHandler):

    def return404(self):
        self.send_response(404)
        self.send_header("Content-type", "text/plain")
        self.end_headers()
        try:
            self.wfile.write(b"Not found.\n")
        except BrokenPipeError:
            # browsers seem to like to close this early
            pass

    def returnJSON(self, data):
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.end_headers()
        try:
            self.wfile.write(bytes(json.dumps(data), "utf8"))
        except BrokenPipeError:
            pass

    def do_POST(self):
        url = urllib.parse.urlparse(self.path)
        if url.path != "/zulipbot":
            self.return404()
            return

        if self.headers.get_content_type() != 'application/json':
            self.send_response(400)
            self.end_headers()
            return
        length = int(self.headers.get('content-length'))
        message = json.loads(self.rfile.read(length))

        query = message['data'].split('\n', 1)[0].removeprefix("@**loogle** ")
        result = loogle.query(query)

        if "error" in result:
            if "\n" in result['error']:
                reply = f"❗\n```\n{result['error']}\n```"
            else:
                reply = f"❗ {result['error']}"
        elif len(result["names"]) == 0:
            reply = f"🤷 nothing found"
        elif len(result["names"]) == 1:
            reply = f"🔍 docs#{result['names'][0]}"
        elif len(result["names"]) == 2:
            reply = f"🔍 docs#{result['names'][0]}, docs#{result['names'][1]}"
        else:
            weburl = f"https://loogle.lean-fro.org/?q={urllib.parse.quote(query)}"
            n = len(result["names"]) - 2
            reply = f"🔍 docs#{result['names'][0]}, docs#{result['names'][1]}, [and {n} more]({weburl})"
        self.returnJSON({ "content": reply })

    def do_GET(self):
        query = ""
        result = {}
        url = urllib.parse.urlparse(self.path)
        want_json = False
        if url.path == "/json":
            want_json = True
        elif url.path != "/":
            self.return404()
            return

        url_query = url.query
        params = urllib.parse.parse_qs(url_query)
        if "q" in params and len(params["q"]) == 1:
            query = params["q"][0].removeprefix("#find ")
            if "\n" in query:
                return
            result = loogle.query(query)

        if want_json:
            self.returnJSON(result)
        else:
            self.send_response(200)
            self.send_header("Content-type", "text/html")
            self.end_headers()
            self.wfile.write(bytes(f"""
                <!doctype html>
                <html lang="de">
                <head>
                <meta charset="utf-8">
                <meta name="viewport" content="width=device-width, initial-scale=1">
                <link rel="stylesheet" href="https://unpkg.com/chota@latest">
                <title>Loogle!</title>
                <body>
                <main class="container">

                <section>
                <h1>Loogle!</h1>
                <form method="GET">
                <p class="grouped">
                <input type="text" name="q" value="{html.escape(query)}"/>
                <input type="submit" value="#find"/>
                </p>
                </form>
                </section>
            """, "utf-8"))
            if "error" in result:
                self.wfile.write(bytes(f"""
                    <h2>Error</h2>
                    <pre>{html.escape(result['error'])}</pre>
                """, "utf-8"))
            if "header" in result:
                self.wfile.write(b"""
                    <h2>Result</h2>
                """)
                self.wfile.write(bytes(f"""
                    <p>{html.escape(result['header'])}</p>
                """, "utf-8"))
            if "names" in result:
                self.wfile.write(bytes(f"""
                    <ul>
                """, "utf-8"))
                for name in result["names"]:
                    self.wfile.write(bytes(f"""
                        <li><a href="https://leanprover-community.github.io/mathlib4_docs/find/?pattern={html.escape(name)}#doc">{html.escape(name)}</a></li>
                    """, "utf-8"))
                self.wfile.write(b"""
                    </ul>
                """)
            self.wfile.write(blurb)
            self.wfile.write(b"""
                </main>
                </body>
                </html>
            """)

if __name__ == "__main__":
    webServer = HTTPServer((hostName, serverPort), MyHandler)
    print("Server started http://%s:%s" % (hostName, serverPort))

    try:
        webServer.serve_forever()
    except KeyboardInterrupt:
        pass

    webServer.server_close()
    print("Server stopped.")
