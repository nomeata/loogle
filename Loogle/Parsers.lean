/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Lean.Parser.Term

/-!
# Parsers used by the loogle binary

* `Loogle.Find.turnstileTerm` / `turnstileTermAscii` are `⊢ T` / `|- T`
  registered as **builtin** term parsers, so the parser and its tokens
  are available in every environment at runtime — including projects
  that have never imported any `Loogle.*` module — and the `(⊢ $s)`
  quotation patterns elsewhere in `Loogle.*` find them at compile time.

* `Loogle.queryParser` is the composite parser for a full query (a
  comma-separated list of terms).

* `Loogle.runStandaloneParser` runs a `Parser` *value* (rather than
  one looked up by name in the env), merging the parser's own tokens
  into the env's token table on the fly.

This module is precompiled (see `lakefile.lean`) so that its
`@[builtin_term_parser]` declarations register at native init time
when other Loogle modules import it during compilation.
-/

@[expose] public section

namespace Loogle.Find

open Lean.Parser

/-- The turnstile (`⊢ T`) marking conclusion patterns in `#find`. -/
@[builtin_term_parser]
def turnstileTerm : Parser :=
  leading_parser "⊢ " >> termParser

/-- ASCII variant (`|- T`) of `turnstileTerm`. -/
@[builtin_term_parser]
def turnstileTermAscii : Parser :=
  leading_parser "|- " >> termParser

end Loogle.Find

namespace Loogle

open Lean Parser

/-- Parser for a `#find` query: a comma-separated list of terms. The turnstile
forms `⊢ T` and `|- T` are themselves term-category builtin parsers (see
`Loogle.Find.turnstileTerm` above), so this composite parser works in any
environment without requiring the user's project to import loogle's modules. -/
def queryParser : Parser :=
  sepBy (categoryParser `term 0) ", " (symbol ", ")

/-- Run a stand-alone `Parser` value (rather than one looked up by name in the
environment) on the given input string, merging the parser's own tokens into
the env's token table on the fly. -/
def runStandaloneParser (env : Environment) (p : Parser) (input : String)
    (fileName := "<input>") :
    Except String Syntax :=
  let pfn := andthenFn whitespace p.fn
  let baseTable := getTokenTable env
  let table := (p.info.collectTokens []).foldl (fun t tk => t.insert tk tk) baseTable
  let ictx := mkInputContext input fileName
  let s := pfn.run ictx { env, options := {} } table (mkParserState input)
  if s.hasError then
     Except.error (s.toErrorMsg ictx)
  else if s.pos.atEnd input then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

end Loogle
