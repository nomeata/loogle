loogle
======

Loogle is a search tool for [Lean]/[Mathlib], and can be used on the web, via a
zulip bot, via APIs, from VSCode or nvim extensions as a Lean command or a command line tool.

Try it at <https://loogle.lean-lang.org/>!


    $ loogle '(List.replicate (_ + _) _ = _)'
    Found 5 declarations mentioning List.replicate, HAdd.hAdd and Eq.
    Of these, 3 match your patterns.

    List.replicate_add
    List.replicate_succ
    List.replicate_succ'

[lean]: https://leanprover.github.io/
[mathlib]: https://github.com/leanprover-community/mathlib4

Running locally
---------------

The loogle binary searches any Lake project of the same Lean toolchain — your
project does **not** need to depend on loogle. The setup is:

1. Install [elan](https://github.com/leanprover/elan).
2. Clone this repository, `cd` into it, and run `lake build`. (The
   toolchain in `lean-toolchain` will be installed automatically.) This
   produces the binary at `.lake/build/bin/loogle`.
3. From any other Lake project of the same toolchain, point loogle at
   the module you want to search. Use `--use-index` to cache the search
   index across runs so the second invocation onward is fast:

       lake env /path/to/loogle/.lake/build/bin/loogle \
         --use-index --module MyModule "<query>"

   The first call builds the index and writes it to a file next to
   `MyModule.olean`; subsequent calls reload it as long as the
   underlying `.olean`s haven't changed. When they do change, loogle
   rebuilds the index in place. If the default location is not
   writable, pass `--index-file PATH` to choose another.

`lake env` sets up `LEAN_PATH` for the calling project; loogle honours it
and falls back to its build-time search path only when no environment is
set.

[elan]: https://github.com/leanprover/elan

CLI Usage
---------

    USAGE:
      loogle [OPTIONS] [QUERY]

    OPTIONS:
      --help
      --interactive, -i     read querys from stdin
      --json, -j            print result in JSON format
      --module mod          import this module (default: Mathlib)
      --path path           search for .olean files here (default: the build time path)
      --write-index         build the search index and persist it to disk
      --read-index          load the search index from disk; fail if it is stale
      --use-index           load the index from disk if present and up-to-date,
                            otherwise build it and write it to disk
      --index-file PATH     override the default index path. The default lives
                            next to the root module's .olean (with .loogle-index
                            extension); pass this if that location is read-only.
      --max-results n       limit the number of returned hits (default: 200)

Indices are tagged with the Lake `depHash` of the root module they were built
against, so loogle can detect when an index is out of date with respect to the
current `.olean`s and refuse to use it (`--read-index`) or rebuild it
(`--use-index`).

Web service
-----------

This tool is the backend of <https://loogle.lean-lang.org/>. This is currently
running on a virtual host with a nixos system with a ngingx reverse proxy (for
SSL) in front of a small python HTTP server (see `./server.py`) that uses
`loogle`. The query processing is locked down using SECCOMP (see
`./loogle_seccomp.c`). It automatically tries to upgrade to the latest
mathlib every 6 hours.

You can run this server locally as well, either using `./server.py` after you
built `loogle` via `lake`. The wrapper accepts `--host`, `--port`, and
`--loogle-bin`, and forwards any arguments after `--` to the loogle binary, so
you can e.g. point the web frontend at a smaller module:

    python3 server.py --port 9000 -- --module Init.Data.List.Basic --max-results 50

At the path `/json?q=…` (instead of `/?q=…`), the result is returned in JSON
format. No stability of the format is guaranteed at this point.

Zulip bot
---------

The [leanprover Zulip chat](https://leanprover.zulipchat.com/) has a bot called
`loogle` that will respond to messages with the first two hits from loogle.
Just write `@**loogle** query` in a public stream.

It is implemented via an outgoing webhook to the above web service.

Editor integration
------------------

These are created by their respective maintainers; reach out to them if you have questions

* [VS Code extension “Loogle Lean”](https://marketplace.visualstudio.com/items?itemName=ShreyasSrinivas.loogle-lean)
* [`lean.nvim`](https://github.com/Julian/lean.nvim#features) has built-in support for loogle.

Declaration filtering
---------------------

Auto-generated declarations (e.g. `injEq`, `sizeOf_spec`, `casesOn`) are hidden
from search results. The filtering logic follows doc-gen4's `isBlackListed`
(see `Loogle/BlackListed.lean`).

Contact
-------

This tool was created by Joachim Breitner <<mail@joachim-breitner.de>>. Feel free
to use this repository to report issues or (even better) submit PRs that
resolves such issues.
