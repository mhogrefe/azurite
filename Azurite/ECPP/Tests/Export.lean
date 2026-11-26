/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search

/-!
# Tests of the certificates for exchange
-/

namespace Azurite.ECPP.Tests.Export

open Azurite Azurite.ECPP

private def N (k : Nat) : AzNat := AzNat.ofNat k

/-! ## The formats -/

private def toy : List ExportStep :=
  [⟨N 7, N 3, N 1, N 2, N 10, N 5, N 3, N 4⟩, ⟨N 5, N 0, N 0, N 1, N 6, N 3, N 2, N 3⟩]

#guard printFlint toy ==
  "ecpp certificate, 2 steps\n" ++
  "[0] n = 7\n    D = 3\n    a = 1\n    b = 2\n    m = 10\n    q = 5\n    x = 3\n    y = 4\n" ++
  "[1] n = 5\n    D = 0\n    a = 0\n    b = 1\n    m = 6\n    q = 3\n    x = 2\n    y = 3\n"
#guard printFlint [] == "ecpp certificate, 0 steps\n"
#guard parseFlint (printFlint toy) == some toy
#guard parseFlint "ecpp certificate, 0 steps" == some []
#guard parseFlint "  ecpp   certificate,\n1 steps [0] n = 7 D = 3 a = 1 b = 2\n\n m = 10 q = 5 \
  x = 3 y = 4 " == some (toy.take 1)
-- the number of steps, the numbering, the names and the numbers are checked
#guard parseFlint "ecpp certificate, 2 steps [0] n = 7 D = 3 a = 1 b = 2 m = 10 q = 5 x = 3 \
  y = 4" == none
#guard parseFlint "ecpp certificate, 1 steps [1] n = 7 D = 3 a = 1 b = 2 m = 10 q = 5 x = 3 \
  y = 4" == none
#guard parseFlint "ecpp certificate, 1 steps [0] n = 7 D = 3 b = 1 a = 2 m = 10 q = 5 x = 3 \
  y = 4" == none
#guard parseFlint "ecpp certificate, 1 steps [0] n = 07 D = 3 a = 1 b = 2 m = 10 q = 5 x = 3 \
  y = 4" == none

-- one line: `t = n + 1 − m` (negative for the first step), `s = m/q`
#guard printPari toy == "[[7, -2, 2, 1, [3, 4]], [5, 0, 2, 0, [2, 3]]]"
#guard printPari [] == "[]"
#guard parsePari "[]" == some []
-- `b = y² − x³ − ax mod N` and `D = 0` on the way back
#guard parsePari (printPari toy) ==
  some [⟨N 7, N 0, N 1, N 0, N 10, N 5, N 3, N 4⟩, ⟨N 5, N 0, N 0, N 1, N 6, N 3, N 2, N 3⟩]
#guard (parsePari " [ [7, -2,2 ,1, [3,\n4] ] ]").map printPari == some "[[7, -2, 2, 1, [3, 4]]]"
#guard parsePari "[[7, 8, 1, 1, [3, 4]]]" == some [⟨N 7, N 0, N 1, N 0, N 0, N 0, N 3, N 4⟩]
-- rejected: `t > N + 1`, `s ∤ m`, `s = 0`, `−0`, a leading zero, a missing bracket
#guard parsePari "[[7, 9, 1, 1, [3, 4]]]" == none
#guard parsePari "[[7, -2, 3, 1, [3, 4]]]" == none
#guard parsePari "[[7, -2, 0, 1, [3, 4]]]" == none
#guard parsePari "[[7, -0, 2, 1, [3, 4]]]" == none
#guard parsePari "[[7, -2, 2, 01, [3, 4]]]" == none
#guard parsePari "[[7, -2, 2, 1, [3, 4]]" == none
#guard parsePari "[[7, -2, 2, 1, 3, 4]]" == none

/-! ## The bound of other verifiers -/

-- `(⌊√q⌋ − 1)⁴ > n`: for `n = 10007`, `(⌊√q⌋ − 1)⁴ > n` from `⌊√q⌋ = 12`, i.e. `q ≥ 144`
#guard !strictBound (N 10007) (N 143)
#guard strictBound (N 10007) (N 144)
#guard !strictBound (N 14641) (N 144) && strictBound (N 14640) (N 144)
#guard !strictBound (N 5) (N 0) && !strictBound (N 0) (N 3) && strictBound (N 0) (N 4)

/-! ## Certificates found by the search -/

/-- Replace step `i`. -/
private def tamper (cert : List ExportStep) (i : Nat) (f : ExportStep → ExportStep) :
    List ExportStep :=
  cert.zipIdx.map fun (e, j) => if j = i then f e else e

/-- For the certificate the search finds for `n`: accepted; the conditions of other verifiers
hold at every step (`strictCert`); both formats come back (the
one-line format with `D = 0`); the chain ends at 64 bits; and it is rejected after a change
of `x`, `a`, `m` (by `±1`), `q`, or of a link of the chain. -/
private def suite (n : AzNat) : List Bool :=
  match ecppCertificateExport n with
  | none => []
  | some cert =>
    let last := (cert.getLast?.map (·.q)).getD n
    [checkExport n cert, strictCert n cert, parseFlint (printFlint cert) == some cert,
      parsePari (printPari cert) == some (cert.map fun e => { e with D := 0 }),
      (parsePari (printPari cert)).map printPari == some (printPari cert),
      decide (last.size ≤ 64) && decide (1 < cert.length),
      checkExport n (tamper cert 0 fun e => { e with x := e.x + 1 }),
      checkExport n (tamper cert 0 fun e => { e with a := e.a + 1 }),
      checkExport n (tamper cert 0 fun e => { e with m := e.m + 1 }),
      checkExport n (tamper cert 0 fun e => { e with m := e.m - 1 }),
      checkExport n (tamper cert 0 fun e => { e with q := e.q + 2 }),
      checkExport n (tamper cert 1 fun e => { e with n := e.n + 2 }),
      checkExport (n + 2) cert, checkExport n (cert.drop 1), checkExport n []]

private def expected : List Bool :=
  [true, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

#guard suite (N (10 ^ 50 + 151)) == expected
#guard suite (N (2 ^ 127 - 1)) == expected
#guard suite (N (10 ^ 100 + 267)) == expected

-- the first step the search finds for `2^64 + 961` leads to `246241 · 279073`, a strong
-- pseudoprime to the base 2 of 37 bits: the chain must not end there
#guard ((ecppCertificateExport (N (2 ^ 64 + 961))).map fun c =>
  checkExport (N (2 ^ 64 + 961)) c && strictCert (N (2 ^ 64 + 961)) c && c.length == 1)
    == some true
#guard provePrime (N (2 ^ 64 + 961))
#guard ecppCertificateExport (N 68719214593) == none

-- the empty certificate: a prime of at most 64 bits
#guard ecppCertificateExport (N (2 ^ 61 - 1)) == some []
#guard checkExport (N (2 ^ 61 - 1)) []
#guard !checkExport (N (2 ^ 61 + 1)) []
#guard !checkExport (N (2 ^ 89 - 1)) []

end Azurite.ECPP.Tests.Export
