Update the JS/CSS library versions embedded in server.py's HTML.

Steps:
1. Find all CDN URLs in server.py (search for esm.sh, unpkg, cdnjs, jsdelivr, or other CDN patterns in script/link tags and import statements).
2. For each library, check the latest version on npm (via registry.npmjs.org) or the relevant CDN API.
3. For libraries served via esm.sh as ES modules:
   - Update the version in the modulepreload `href` attributes AND the `import` statement (they must stay consistent).
   - The modulepreload links point to the resolved module files (e.g. `esm.sh/pkg@version/es2022/file.mjs`), while the import statement uses the entry point (e.g. `esm.sh/pkg@version`).
   - Recompute SRI integrity hashes (`sha384-...`) for the modulepreload URLs by fetching the content and hashing it: `curl -sL '<url>' | python3 -c "import sys,hashlib,base64; d=sys.stdin.buffer.read(); print('sha384-'+base64.b64encode(hashlib.sha384(d).digest()).decode())"`.
4. For other CDN libraries (unpkg, cdnjs), update the version in the URL and recompute any SRI integrity hashes the same way.
5. Report what was updated and what was already at the latest version.
6. Commit the changes (but do not push). Use a commit message summarizing which libraries were bumped and to what versions.
