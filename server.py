#!/usr/bin/env python3

from http.server import BaseHTTPRequestHandler, HTTPServer
import urllib
import subprocess
import json
import html
import sys
import time
import re
import os
import select


hostName = "localhost"
serverPort = 8088

blurb = open("./blurb.html","rb").read()
icon = open("./loogle.png","rb").read()

rev1 = "UNKNOWN"
try:
    rev1 = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode('ascii').strip()
except _:
    pass

rev2 = "UNKNOWN"
try:
    manifest = json.load(open('lake-manifest.json'))
    for package in manifest['packages']:
        if package['name'] == "mathlib":
            rev2 = package['rev']
except _:
    pass

# Prometheus setup
import prometheus_client
m_info = prometheus_client.Info('versions', 'Lean and mathlib versions')
m_info.info({'loogle': rev1, 'mathlib': rev2})
m_queries = prometheus_client.Counter('queries', 'Total number of queries')
m_errors = prometheus_client.Counter('errors', 'Total number of failing queries')
m_results = prometheus_client.Histogram('results', 'Results per query', buckets=(0,1,2,5,10,50,100,200,500,1000))
m_heartbeats = prometheus_client.Histogram('heartbeats', 'Heartbeats per query', buckets=(0,2e0,2e1,2e2,2e3,2e4))
m_client = prometheus_client.Counter('clients', 'Clients used', ["client"])
for l in ("web", "zulip", "json", "nvim", "vscode-lean4", "vscode-loogle", "LeanSearchClient", "lean-lsp-mcp"): m_client.labels(l)

examples = [
    "Real.sin",
    "Real.sin, tsum",
    "Real.sin (_ + 2*Real.pi)",
    "List.replicate (_ + _) _",
    "Real.sqrt ?a * Real.sqrt ?a",
]

class Loogle():
    def __init__(self):
        self.start()

    def start(self):
        self.starting = True
        self.loogle = subprocess.Popen(
            #[".lake/build/bin/loogle","--json", "--interactive", "--module","Init.Data.List.Basic"],
            [".lake/build/bin/loogle","--json", "--interactive"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )

    def do_query(self, query):
        if self.starting:
            r, w, e = select.select([ self.loogle.stdout ], [], [], 0)
            if self.loogle.stdout in r:
                greeting = self.loogle.stdout.readline()
                if greeting != b"Loogle is ready.\n":
                    self.loogle.kill() # just to be sure
                    self.start()
                    return {"error": "The backend process did not send greeting, killing and restarting..."}
                else:
                    self.starting = False
            else:
                return {"error": "The backend process is starting up, please try again later..."}
        try:
            self.loogle.stdin.write(bytes(query, "utf8"));
            self.loogle.stdin.write(b"\n");
            self.loogle.stdin.flush();
            output_json = self.loogle.stdout.readline()
            output = json.loads(output_json)
            return output
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

    def query(self, query):
        m_queries.inc()
        print(f"Query: {json.dumps(query)}", flush=True)
        output = self.do_query(query)
        # Update metrics
        if "error" in output:
            m_errors.inc()
        if "count" in output:
            m_results.observe(output["count"])
        if "heartbeats" in output:
            m_heartbeats.observe(output["heartbeats"])
        return output



loogle = Loogle()

# link formatting
def locallink(query):
    return f"?q={urllib.parse.quote(query)}"

def querylink(query):
    return f"https://loogle.lean-lang.org/?q={urllib.parse.quote(query)}"

def doclink(hit):
    name = hit["name"]
    modpath = hit["module"].replace(".","/")
    return f"https://leanprover-community.github.io/mathlib4_docs/{urllib.parse.quote(modpath)}.html#{urllib.parse.quote(name)}"

def zulHit(hit):
    return f"[{hit['name']}]({doclink(hit)})"

def zulQuery(sugg):
    return f"[`{sugg}`]({querylink(sugg)})"

class MyHandler(prometheus_client.MetricsHandler):

    def return404(self):
        self.send_response(404)
        self.send_header("Content-type", "text/plain")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
        self.end_headers()
        self.wfile.write(b"Not found.\n")

    def return400(self):
        self.send_response(400)
        self.send_header("Content-type", "text/plain")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
        self.end_headers()
        try:
            self.wfile.write(b"Invalid request.\n")
        except BrokenPipeError:
            # browsers seem to like to close this early
            pass

    def returnRedirect(self, url):
        self.send_response(302)
        self.send_header("Location", url)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
        self.end_headers()

    def returnJSON(self, data):
        self.send_response(200)
        self.send_header("Content-type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
        self.end_headers()
        try:
            self.wfile.write(bytes(json.dumps(data), "utf8"))
        except BrokenPipeError:
            pass

    def returnIcon(self):
        self.send_response(200)
        self.send_header("Content-type", "image/png")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
        self.end_headers()
        try:
            self.wfile.write(icon)
        except BrokenPipeError:
            pass

    def do_OPTIONS(self):
        url = urllib.parse.urlparse(self.path)
        if url.path == "/json":
            self.send_response(200)
            self.send_header("Content-type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Methods", "GET")
            self.send_header("Access-Control-Allow-Headers", "User-Agent, X-Loogle-Client")
            self.end_headers()
        else:
            self.return404()

    def do_POST(self):
        try:
            url = urllib.parse.urlparse(self.path)
            if url.path != "/zulipbot":
                self.return404()
                return

            if self.headers.get_content_type() != 'application/json':
                self.send_response(400)
                self.end_headers()
                return
            m_client.labels("zulip").inc()

            length = int(self.headers.get('content-length'))
            message = json.loads(self.rfile.read(length))

            m = re.search('@\*\*loogle\*\*[:,\?]?\s*(.*)$', message['data'], flags = re.MULTILINE)
            if m:
                query = m.group(1)
            else:
                query = message['data'].split('\n', 1)[0]

            result = loogle.query(query)

            if "error" in result:
                if "\n" in result['error']:
                    reply = f"❗\n```\n{result['error']}\n```"
                else:
                    reply = f"❗ {result['error']}"
                if "suggestions" in result:
                    suggs = result["suggestions"]
                    reply += "\n"

                    if len(suggs) == 1:
                        reply += f"Did you mean {zulQuery(suggs[0])}?"
                    elif len(suggs) == 2:
                        reply += f"Did you mean {zulQuery(suggs[0])} or {zulQuery(suggs[1])}?"
                    else:
                        reply += f"Did you mean {zulQuery(suggs[0])}, {zulQuery(suggs[1])}, or [something else]({querylink(query)})?"

            else:
                hits = result["hits"]
                if len(hits) == 0:
                    reply = f"🤷 nothing found"
                elif len(hits) == 1:
                    reply = f"🔍 {zulHit(hits[0])}"
                elif len(hits) == 2:
                    reply = f"🔍 {zulHit(hits[0])}, {zulHit(hits[1])}"
                else:
                    n = result["count"] - 2
                    reply = f"🔍 {zulHit(hits[0])}, {zulHit(hits[1])}, and [{n} more]({querylink(query)})"
            self.returnJSON({ "content": reply })
        except BrokenPipeError:
            # browsers seem to like to close this early
            pass

    def do_GET(self):
        try:
            query = ""
            result = {}
            url = urllib.parse.urlparse(self.path)
            want_json = False

            if url.path == "/loogle.png":
               self.returnIcon()
               return
            if url.path == "/json":
                want_json = True
            elif url.path == "/metrics":
                return super(MyHandler, self).do_GET()
            elif url.path != "/":
                self.return404()
                return

            url_query = url.query
            params = urllib.parse.parse_qs(url_query)
            if "q" in params and len(params["q"]) == 1:
                if want_json:
                    if "lean4/" in self.headers.get("x-loogle-client", ""):
                        m_client.labels("vscode-lean4").inc()
                    elif "LeanSearchClient" in self.headers["user-agent"]:
                        m_client.labels("LeanSearchClient").inc()
                    elif "vscode" in self.headers["user-agent"]:
                        m_client.labels("vscode-loogle").inc()
                    elif "lean.nvim" in self.headers["user-agent"]:
                        m_client.labels("nvim").inc()
                    elif "lean+nvim" in self.headers["user-agent"]:
                        m_client.labels("nvim").inc()
                    elif "lean-lsp-mcp" in self.headers["user-agent"]:
                        m_client.labels("lean-lsp-mcp").inc()
                    else:
                        m_client.labels("json").inc()
                else:
                    m_client.labels("web").inc()

                query = params["q"][0].strip().removeprefix("#find ").strip()
                if query:
                    if "\n" in query:
                        self.return400()
                        return
                    result = loogle.query(query)

                if "lucky" in params:
                    if "hits" in result and len(result["hits"]) >= 1:
                        self.returnRedirect(doclink(result["hits"][0]))
                        return


            if want_json:
                self.returnJSON(result)
                return

            self.send_response(200)
            self.send_header("Content-type", "text/html")
            self.end_headers()
            self.wfile.write(bytes("""
                <!doctype html>
                <html lang="en">
                <head>
                <meta charset="utf-8">
                <meta name="viewport" content="width=device-width, initial-scale=1">
                <link rel="stylesheet"
                      href="https://unpkg.com/chota@0.9.2/dist/chota.min.css"
                      integrity="sha384-A2UBIkgVTcNWgv+snhw7PKvU/L9N0JqHwgwDwyNcbsLiVhGG5KAuR64N4wuDYd99"
                      crossorigin="anonymous">
                <link rel="modulepreload"
                      href="https://cdn.skypack.dev/-/@leanprover/unicode-input@v0.1.0-8CqsXR89dtD7hIU0c6wN/dist=es2020,mode=imports,min/optimized/@leanprover/unicode-input.js"
                      integrity="sha384-IR290YsDJ1+Rzd4fgZM4K+v1E2kG2NzQ3XYgGhSxE4cNodMg0JQ9BWn/0JMgk5Xa"
                      crossorigin="anonymous">
                <link rel="modulepreload"
                      href="https://cdn.skypack.dev/-/@leanprover/unicode-input-component@v0.1.0-cAcOWoqAnOWevp4vHscs/dist=es2020,mode=imports,min/optimized/@leanprover/unicode-input-component.js"
                      integrity="sha384-yX1xThTPuhw06x65fHJAV8FLLmaKxiyeKkBTGsI5R1dHRQmHbXU0ylBBu2+56Bc/"
                      crossorigin="anonymous">
                <link rel="modulepreload"
                      href="https://cdn.skypack.dev/pin/@leanprover/unicode-input-component@v0.1.0-cAcOWoqAnOWevp4vHscs/mode=imports,min/optimized/@leanprover/unicode-input-component.js"
                      integrity="sha384-3jdol3AWL3guud0hEWfo7ysqRxI6grINH5ElwPuStNcMb887NNz08TqkGNgy+2q6"
                      crossorigin="anonymous">
                <style>
                  @import url('https://cdnjs.cloudflare.com/ajax/libs/juliamono/0.051/juliamono.css');
                  :root {
                    --font-family-mono: 'JuliaMono', monospace;
                  }

                  /* Browser fix for unicode editing */
                  .textinput { white-space: -moz-pre-space; }

                  /* Copied from chota for textinput */
                  .textinput {
                      font-family: inherit;
                      padding: 0.8rem 1rem;
                      border-radius: 4px;
                      border: 1px solid var(--color-lightGrey);
                      font-size: 1em;
                      -webkit-transition: all 0.2s ease;
                      transition: all 0.2s ease;
                      display: block;
                      width: 100%;
                    }
                   .textinput:focus {
                      outline: none;
                      border-color: var(--color-primary);
                      box-shadow: 0 0 1px var(--color-primary);
                    }

                    /* Copy buttons */
                    span.copy { cursor: pointer; }
                </style>
                <link rel="icon" type="image/png" href="loogle.png" />
                <title>Loogle!</title>
                <body autocomplete="off" autocorrect="off" autocapitalize="off" spellcheck="false">
                <main class="container">

                <section>
                <h1><a href="." style="color:#333;">Loogle!</a></h1>
            """, "utf-8"))
            self.wfile.write(bytes(f"""
                <form method="GET" id="queryform">
                <div class="grouped">
                <input id="hiddenquery" type="hidden" name="q" value=""/>
                <div class="textinput" id="query" name="q" contenteditable="true" autofocus="true">{html.escape(query)}</div>
                <button type="submit" id="submit">#find</button>
                <button type="submit" name="lucky" value="yes" title="Directly jump to the documentation of the first hit.">#lucky</button>
                </div>
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
            if "hits" in result:
                self.wfile.write(bytes(f"""
                    <ul>
                """, "utf-8"))
                for hit in result["hits"]:
                    name = hit["name"]
                    mod = hit["module"]
                    type = hit["type"]
                    self.wfile.write(bytes(f"""
                        <li><a href="{doclink(hit)}">{html.escape(name)}</a> <small><span class="copy" title="Copy to clipboard" data-text="{html.escape(name)}">📋</span> {html.escape(mod)}</small><br><tt>{html.escape(type)}</tt></li>
                    """, "utf-8"))
                self.wfile.write(b"""
                    </ul>
                """)
            if "suggestions" in result:
                self.wfile.write(b'<h2>Did you maybe mean</h2><ul>')
                for sugg in result["suggestions"]:
                    link = locallink(sugg)
                    self.wfile.write(bytes(f'<li>🔍 <a href={link}><code>{html.escape(sugg)}</code></a></li>', "utf-8"))
                self.wfile.write(b'</ul>')

            self.wfile.write(blurb)

            self.wfile.write(bytes(f"""
                <p><small>This is Loogle revision <a href="https://github.com/nomeata/loogle/commit/{rev1}"><code>{rev1[:7]}</code></a> serving mathlib revision <a href="https://github.com/leanprover-community/mathlib4/commit/{rev2}"><code>{rev2[:7]}</code></a></small></p>
            """, "utf-8"))

            self.wfile.write(b"""
                </main>
                <script type="module">
                import { InputAbbreviationRewriter } from "https://cdn.skypack.dev/pin/@leanprover/unicode-input-component@v0.1.0-cAcOWoqAnOWevp4vHscs/mode=imports,min/optimized/@leanprover/unicode-input-component.js";
                const queryInput = document.getElementById('query');
                const hiddenInput = document.getElementById('hiddenquery');
                const form = document.getElementById('queryform');
                const submitButton = document.getElementById('submit');
                const rewriter = new InputAbbreviationRewriter(
                    { abbreviationCharacter: "\\\\",
                      customTranslations: [],
                      eagerReplacementEnabled: true },
                    queryInput,
                )
                queryInput.addEventListener('keydown', event => {
                    if (event.key === 'Enter') {
                        event.preventDefault();
                        submitButton.click();
                    }
                })
                form.addEventListener('submit', event => {
                    hiddenInput.value = queryInput.innerText;
                })

                // Implement the copy buttons
                document.querySelectorAll('span.copy').forEach(element => {
                    element.addEventListener('click', () => {
                        navigator.clipboard.writeText(element.getAttribute('data-text'));
                    });
                });
                </script>
                </body>
                </html>
            """)
        except BrokenPipeError:
            # browsers seem to like to close this early
            pass

if __name__ == "__main__":
    webServer = HTTPServer((hostName, serverPort), MyHandler)
    print("Server started http://%s:%s" % (hostName, serverPort), flush=True)

    try:
        webServer.serve_forever()
    except KeyboardInterrupt:
        pass

    webServer.server_close()
    print("Server stopped.")
