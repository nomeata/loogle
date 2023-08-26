loogle
======

Loogle is a search tool for [Lean]/[Mathlib]. It wraps the `#find` command as a
command line tool or web service. Try it at <https://loogle.nomeata.de/>!

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

[elan]: https://github.com/leanprover/elan

Running locally (with nix)
--------------------------

You can also build it with nix. Teh first time this will take several hours as
it builds all of mathlib:

1. check out this repository
2. nix run -L ./#loogle -- --help

Usage
-----

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
You can use `--write-index` and `--read-index` to cache that, but it it is your
responsibility to pass the right index for the given module and search path. In
the nix setup, the index is built as part of the build process.

Web service
-----------

This tools is the backend of <https://loogle.nomeata.de/>. This is currently
running on a 2GB Hetzner virtual host with a nixos system (see `./nixos`) with
a ngingx reverse proxy (for SSL) in front of a small python HTTP server (see
`./server.py`) that uses `loogle`. The query processing is locked down using
SECCOMP (see `./loogle_seccomp.c`).

You can run this server locally as well, either using `./server.py` if you
built `loogle` via `lake`, or using `nix run ./#loogle_server` if you use nix.

Contact
-------

This tool was created by Joachim Breitner <<mail@joachim-breitner.de>>. Feel free
to use this repository to report issues or (even better) submit PRs that
resolves such issues.


