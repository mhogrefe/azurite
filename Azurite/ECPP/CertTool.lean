/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search

/-!
# `lake exe ecpp_cert`: certificates for exchange

`lake exe ecpp_cert <pari|flint> <file>` reads one decimal number per line of `<file>` (empty
lines are skipped) and writes to standard output, for every number `n`, the certificate the
search finds (`ecppCertificateExport`), after checking it (`checkExport`):

* `pari`: one line `<n>: <certificate in the one-line format>`;
* `flint`: a line `<n>:`, the certificate in the multi-line format, and an empty line;
* `<n>: none` when the search finds nothing (in particular for a composite `n`) or the
  certificate is not accepted.

The exit code is `0` unless the arguments or a line cannot be read.
-/

namespace Azurite.ECPP

/-- The text for one `n` (see the file header). -/
def certText (flint : Bool) (n : AzNat) : String :=
  match (ecppCertificateExport n).filter (checkExport n) with
  | none => s!"{n}: none\n"
  | some cert => if flint then s!"{n}:\n{printFlint cert}\n" else s!"{n}: {printPari cert}\n"

/-- The program behind `lake exe ecpp_cert`. -/
def certMain (args : List String) : IO UInt32 := do
  let usage : IO UInt32 := do
    IO.eprintln "Usage: ecpp_cert <pari|flint> <file>   (one decimal number per line)"
    return 2
  match args with
  | [format, path] =>
    if format ≠ "pari" ∧ format ≠ "flint" then return ← usage
    let out ← IO.getStdout
    for line in ← IO.FS.lines ⟨path⟩ do
      let cs := line.toList.filter (!·.isWhitespace)
      if cs.isEmpty then continue
      match parseDecimal cs with
      | none =>
        IO.eprintln s!"not a decimal number: {line}"
        return 1
      | some n =>
        out.putStr (certText (format == "flint") n)
        out.flush
    return 0
  | _ => usage

end Azurite.ECPP
