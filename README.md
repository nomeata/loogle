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

1. Clone this repository and `cd` into it.
2. Copy the target project's `lean-toolchain` into this checkout, so the
   loogle binary is built with the same toolchain as the oleans it will
   read:

       cp /path/to/project/lean-toolchain .

3. Run `lake build`. This produces the binary at `.lake/build/bin/loogle`.
4. From the target project, point loogle at the module you want to search:

       lake env /path/to/loogle/.lake/build/bin/loogle \
         --module MyModule "<query>"

   The first call builds the search index (slow); by default loogle caches
   it on disk next to the module's `.olean` so subsequent calls are fast,
   and quietly rebuilds it whenever the underlying `.olean`s change. If the
   default location is not writable, pass `--index-file PATH` to choose
   another, or `--index-mode none` to skip the cache entirely.

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
      --index-mode MODE     how to manage the on-disk search index. One of:
                              use   (default) load if present and up-to-date,
                                    otherwise build and write
                              read  load existing index; refuse to start if it
                                    is missing or out of date
                              write always (re)build the index and write it
                              none  build in memory and discard on exit
      --index-file PATH     override the default index path. The default lives
                            next to the root module's .olean (with .loogle-index
                            extension); pass this if that location is read-only.
      --max-results n       limit the number of returned hits (default: 200)

Web service
-----------

This tool is the backend of <https://loogle.lean-lang.org/>. This is currently
running on a virtual host with a nixos system with a nginx reverse proxy (for
SSL) in front of a small python HTTP server (see `./server.py`) that uses
`loogle`. It automatically tries to upgrade to the latest mathlib every 6
hours.

You can run this server locally as well. The wrapper has to run from the
loogle checkout (it opens `blurb.html`, `loogle.png`, … from the current
directory), and pass the directory of the project you want to search via
`--project-dir`:

    lake build
    ./server.py --project-dir /path/to/project -- --module RootModule

The wrapper accepts `--host`, `--port`, `--loogle-bin`, and `--project-dir`,
and forwards any arguments after `--` to the loogle binary.

At the path `/json?q=…` (instead of `/?q=…`), the result is returned in JSON
format. No stability of the format is guaranteed at this point.

You can add `&limit=10` to restrict the number if responses returned. Note that
this (currently) still generates more responses, but just doesn't send them to
the client.

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
