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

/-! ## Certificates -/

private def P : GenParams := { dMax := 200, hMax := 4, trialBound := 1000, baseBits := 30 }

#guard provePrime (N "655863716953") P
#guard !provePrime (N "655863716955") P
#guard (ecppCertificate (N "655863716953") P).isSome
#guard provePrime (N "675904957021146642687026859253") P
#guard !provePrime (N "675904957021146642687026859251") P

end Azurite.ECPP.Tests
