/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.Parse
import Azurite.ECPP.Export

/-!
# Oracle modes for elliptic curve primality certificates

Certificates are read in the one-line format of `Azurite/ECPP/Export.lean`
(`[[N, t, s, a, [x, y]], …]`).

* `az_ecpp_cert_check`: lines `ecpp_verify(<n>, <certificate>) = true` or `= false`.  A
  certificate Malachite accepts must be accepted by the proven `ECPP.checkExport` and
  satisfy `ECPP.strictCert`.  One that
  Malachite rejects and Azurite accepts is a disagreement only if every step also satisfies
  the conditions of Malachite's verifier that `checkExport` does not impose
  (`strictCert`); otherwise the two verdicts differ because the rules differ, and the line
  passes.
* `az_ecpp_cert_roundtrip`: lines `<certificate>`; parsing and printing must give the line
  back unchanged.
-/

namespace Azurite.Oracle

open Azurite Azurite.ECPP

/-- `ecpp_verify(n, cert) = true` or `= false`. -/
def checkEcppCertCheck (line : String) : Verdict := do
  let (args, result) ← expect "an ecpp_verify line" (functionCall line "ecpp_verify")
  let (n, cert) ← match args with
    | [n, cert] => pure (n, cert)
    | _ => fail "ecpp_verify takes a number and a certificate"
  let n ← expect "n" (parseAzNat n)
  let cert ← expect "the certificate" (parsePari cert)
  let expected ← expect "the verdict" (parseBool result)
  let accepted := checkExport n cert
  if expected then
    if !accepted then
      disagree "ecpp_verify: Malachite accepted a certificate that Azurite's checker rejects"
    else if !strictCert n cert then
      disagree "ecpp_verify: Malachite accepted a certificate that fails its own conditions"
    else .ok ()
  else if accepted && strictCert n cert then
    disagree "ecpp_verify: Malachite rejected a certificate that Azurite's checker accepts \
      and that satisfies Malachite's own conditions"
  else .ok ()

/-- A certificate in the one-line format: parsing and printing gives the line back. -/
def checkEcppCertRoundtrip (line : String) : Verdict := do
  let cert ← expect "a certificate" (parsePari line)
  expectEq "certificate round trip" (printPari cert) (trim line)

end Azurite.Oracle
