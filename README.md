loogle
======

Loogle is a search tool for [Lean]/[Mathlib], and can be used on the web, via a
zulip bot, via APIs, from VSCode or nvim extensions as a Lean command or a command line tool.

Try it at <https://loogle.lean-lang.org/>!


    $ loogle '(List.replicate (_ + _) _ = _)'
    Found 5 definitions mentioning List.replicate, HAdd.hAdd and Eq.
    Of these, 3 match your patterns.

    List.replicate_add
    List.replicate_succ
    List.replicate_succ'

[lean]: https://leanprover.github.io/
[mathlib]: https://github.com/leanprover-community/mathlib4

Running locally
---------------

To use `loogle` locally:

1. check out this repository
2. install [elan](https://github.com/leanprover/elan)
3. run `lake exe cache get`
4. run `lake exe loogle --help` (or other options)

If you use `loogle` on a large repository like Mathlib, the startup-time will
be rather large. Run `lake build LoogleMathlibCache` if you want to pre-compute
the index for Mathlib.

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
      --write-index file    persists the search index to a file
      --read-index file     read the search index from a file. This file is blindly trusted!

By default, it will create an internal index upon starting,  which takes a bit.
You can use `--write-index` and `--read-index` to cache that, but it is your
responsibility to pass the right index for the given module and search path. In
the nix setup, the index is built as part of the build process.

Web service
-----------

This tool is the backend of <https://loogle.lean-lang.org/>. This is currently
running on a virtual host with a nixos system with a ngingx reverse proxy (for
SSL) in front of a small python HTTP server (see `./server.py`) that uses
`loogle`. The query processing is locked down using SECCOMP (see
`./loogle_seccomp.c`). It automatically tries to upgrade to the latest
mathlib every 6 hours.

You can run this server locally as well, either using `./server.py` after you
built `loogle` via `lake`.

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

Contact
-------

This tool was created by Joachim Breitner <<mail@joachim-breitner.de>>. Feel free
to use this repository to report issues or (even better) submit PRs that
resolves such issues.
