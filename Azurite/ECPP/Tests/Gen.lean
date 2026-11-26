/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search
import Azurite.AzNat.ParseBase
import Azurite.AzInt.ToString

/-!
# Tests: the generator of elliptic curve primality certificates
-/

namespace Azurite.ECPP.Tests

private def N (s : String) : AzNat := (AzNat.parse s).get!

/-! ## Class polynomials -/

private def H (D : Nat) : Option (List String) :=
  (hilbertClassPoly D).map fun l => l.map toString

#guard H 3 == some ["0", "1"]
#guard H 4 == some ["-1728", "1"]
#guard H 7 == some ["3375", "1"]
#guard H 163 == some ["262537412640768000", "1"]
#guard H 15 == some ["-121287375", "191025", "1"]
#guard H 23 == some ["12771880859375", "-5151296875", "3491750", "1"]
#guard H 47 == some ["16042929600623870849609375", "-14982472850828613281250",
  "5115161850595703125", "-9987963828125", "2257834125", "1"]

/-! ## Cornacchia -/

-- 4 · 1000003 = 2000² + 3 · 2², with √−3 ≡ 1000 (mod 1000003)
#guard (cornacchia4 (N "1000003") 3 (N "1000")).map (fun r => (toString r.1, toString r.2))
  == some ("2000", "2")
#guard (trialDivide (N "1000") [2, 3, 5]) == (N "1", N "1000")
#guard (trialDivide (N "2002") [2, 3, 5, 7]) == (N "143", N "14")
#guard smallPrimes 30 == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
#guard smoothParts (AzNat.primorial 7) #[N "1000", N "2002", N "143", N "1", N "210"] ==
  #[(N "1", N "1000"), (N "143", N "14"), (N "143", N "1"), (N "1", N "1"), (N "1", N "210")]
#guard smoothParts (AzNat.primorial 16) #[N "5184", N "33614", N "1000000007"] ==
  #[(N "1", N "5184"), (N "1", N "33614"), (N "1000000007", N "1")]
#guard smoothParts (AzNat.primorial 100) #[] == #[]

/-! ## Roots of split polynomials (packed powers) -/

/-- `(X − 1)(X − 2)(X − 3)(X − 5)(X − 7)(X − 11)(X − 13)(X − 17)`. -/
private def splitPoly : List AzInt :=
  [510510, -1226677, 1106405, -497553, 123501, -17535, 1407, -59, 1].map AzInt.ofInt

/-- The root found of `splitPoly` modulo `n`, and the packed power `(X + 3)^e` compared
with `AzPolyMod`'s. -/
private def rootTest (n : AzNat) : Bool :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    let g := polyOfInts n splitPoly
    let rootOk := match rootOfSplitPoly n g with
      | some r => [1, 2, 3, 5, 7, 11, 13, 17].contains r.val.toNat
      | none => false
    let e := (n - 1).shiftRight 1
    let M := PackedMod.make n ((Array.range 8).map fun i => (g.coeff i).val)
    let x : AzPolynomial (AzZMod n) := AzPolynomial.normalize #[AzZMod.ofAzNat n 3, 1]
    let ref := (AzPolyMod.powAzNat (AzPolyMod.ofPoly (f := g) x) e).val
    let got := AzPolynomial.normalize ((M.powLinear 3 e).map (AzZMod.ofAzNat n))
    rootOk && decide (ref = got)
  else false

#guard rootTest (N "1000003")
#guard rootTest (N "675904957021146642687026859253")
#guard rootTest (N "1000000000000000000000000000000000000000000000000000000000007")

/-! ## Factors of class polynomials over the genus field -/

/-- A root of the genus factor of `H_{−D}` modulo `n` is a root of `H_{−D}`, and the factor
has degree `deg`. -/
private def genusTest (D deg : Nat) (n : AzNat) : Bool :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    match genusClassPoly D with
    | none => false
    | some G =>
      match genusPolyMod n G, (hilbertClassPoly D).map (polyOfInts n) with
      | some g, some H =>
        g.natDegree == deg &&
          match rootOfSplitPoly n g with
          | some r => decide (AzPolynomial.eval H r = 0)
          | none => false
      | _, _ => false
  else false

#guard genusTest 15 1 (N "1000000096000002439")
#guard genusTest 20 1 (N "1000000226000018549")
#guard genusTest 84 1 (N "1000000054000017193")
#guard genusTest 55 2 (N "1000000058000006341")
#guard genusTest 244 3 (N "1000000068000075881")
#guard genusTest 1615 6 (N "1000000218000173381")
#guard genusTest 1155 1 (N "1000000084000002919")
#guard (genusClassPoly 23).isNone
#guard positiveSubsets [-3, 5] == [[false, false], [false, true]]
#guard positiveSubsets [-4, -3, -7] ==
  [[false, false, false], [true, true, false], [true, false, true], [false, true, true]]

/-! ## Weber class polynomials

The known `W_23 = X³ − X² + 1`, `W_31 = X³ + X − 1`, `W_47 = X⁵ + 2X⁴ + 2X³ + X² − 1` (up
to `X ↦ −X`); and, modulo a prime `n` with `4n = x² + D y²`, the number obtained from a root
of the Weber polynomial is a root of `H_{−D}` (prime and composite discriminants, with and
without the factor `3`). -/

#guard (weberClassPoly 23).map (·.map AzInt.toInt) == some [1, 0, -1, 1]
#guard (weberClassPoly 31).map (·.map AzInt.toInt) == some [-1, 1, 0, 1]
#guard (weberClassPoly 47).map (·.map AzInt.toInt) == some [-1, 0, 1, 2, 2, 1]
#guard (weberClassPoly 15).map (·.map AzInt.toInt) == some [-1, 1, 1]
#guard (weberClassPoly 19).isNone
#guard (genusWeberPoly 23).isNone
#guard (genusWeberPoly 95).isSome

private def weberOk (D : Nat) (n : AzNat) : Bool :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    match weberRoot n D, hilbertClassPoly D with
    | some j, some H => decide ((polyOfInts n H).eval j = 0)
    | _, _ => false
  else false

#guard weberOk 23 (N "307519000361")
#guard weberOk 31 (N "327509000081")
#guard weberOk 47 (N "367531000961")
#guard weberOk 71 (N "427501000001")
#guard weberOk 95 (N "487507000049")
#guard weberOk 119 (N "547507000049")
#guard weberOk 191 (N "727519000361")
#guard weberOk 15 (N "287521000441")
#guard weberOk 39 (N "347511000121")
#guard weberOk 87 (N "467527000729")
#guard weberOk 255 (N "887511000121")
/-! ## Certificates -/

private def P : GenParams := { dMax := 200, hMax := 4, trialBound := 1000, baseBits := 30 }

#guard provePrime (N "655863716953") P
#guard !provePrime (N "655863716955") P
#guard (ecppCertificate (N "655863716953") P).isSome
#guard provePrime (N "675904957021146642687026859253") P
#guard !provePrime (N "675904957021146642687026859251") P

/-! With the default parameters.  The Mersenne prime `2^521 − 1` (157 digits; about two
minutes in the interpreter), and two strong pseudoprimes to the first twelve prime bases, on
which the search gives up at once. -/

#guard provePrime (AzNat.ofNat (2 ^ 521 - 1))
#guard !provePrime (N "3317044064679887385961981")
#guard !provePrime (N "318665857834031151167461")

end Azurite.ECPP.Tests
