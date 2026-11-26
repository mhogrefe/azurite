/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Kronecker
import Azurite.AzNat.Square
import Azurite.AzInt.Instances
import Azurite.AzInt.Conversion

/-!
# Kronecker substitution at two points: packing and unpacking

For coefficients `aᵢ < β^(2w)` (`β = 2^64`) and `B = β^w`, the values of `∑ aᵢ Xⁱ` at `B` and
at `−B` are `E + O` and `E − O`, with `E = ∑ a₂ⱼ B^(2j)` and `O = ∑ a₂ⱼ₊₁ B^(2j+1)` packed
`2w` limbs apart (`kroneckerPackEven`, `kroneckerPackOdd`, `kroneckerEvalPair`).  From the
product `u` of the two values at `B` and the product `v` of the two values at `−B`,
`kroneckerHalves u v = ((u + v) / 2, (u − v) / 2)` are the even and the odd half of the
product polynomial at `B`, and `kroneckerCoeff2 w` reads the `k`-th coefficient from the
half of the parity of `k`.  The arithmetic is in `Kronecker/Theory.lean`, the values in
`Equiv/Kronecker2.lean`.
-/

namespace Azurite.AzNat

/-- `n` limbs from limb `i` on: `⌊x / 2^(64 i)⌋ mod 2^(64 n)`. -/
def limbBlock (x : AzNat) (i n : Nat) : AzNat :=
  ofLimbs (x.limbs.extract i (i + n))

/-- `∑ a₂ⱼ · 2^(64 w · 2j)`, for coefficients below `2^(128 w)`. -/
def kroneckerPackEven (w : Nat) (a : Array AzNat) : AzNat :=
  kroneckerPack (2 * w) (Array.ofFn fun (i : Fin ((a.size + 1) / 2)) => a[2 * i.val]'(by omega))

/-- `∑ a₂ⱼ₊₁ · 2^(64 w · (2j + 1))`, for coefficients below `2^(128 w)`: `w` zero limbs, then
the coefficients of odd index `2 w` limbs apart. -/
def kroneckerPackOdd (w : Nat) (a : Array AzNat) : AzNat :=
  ofLimbs ((Array.ofFn fun (i : Fin (a.size / 2)) => a[2 * i.val + 1]'(by omega)).foldl
    (fun out c => out ++ truncatePad c.limbs (2 * w)) (Array.replicate w 0))

/-- The values of `∑ aᵢ Xⁱ` at `2^(64 w)` and at `−2^(64 w)`. -/
def kroneckerEvalPair (w : Nat) (a : Array AzNat) : AzNat × AzInt :=
  let e := kroneckerPackEven w a
  let o := kroneckerPackOdd w a
  (e + o, e.toAzInt - o.toAzInt)

/-- `((u + v) / 2, (u − v) / 2)` for `|v| ≤ u` of the parity of `u`; the second as `u` minus
the first. -/
def kroneckerHalves (u : AzNat) (v : AzInt) : AzNat × AzNat :=
  let e := (u.toAzInt + v).abs >>> 1
  (e, u - e)

/-- The `k`-th block of `2 w` limbs, `w` limbs apart, of the half of the parity of `k`. -/
def kroneckerCoeff2 (w : Nat) (xe xo : AzNat) (k : Nat) : AzNat :=
  limbBlock (if k % 2 = 0 then xe else xo) (k * w) (2 * w)

#guard limbBlock (ofNat (2 ^ 200 + 5 * 2 ^ 64 + 3)) 1 2 == ofNat 5
#guard limbBlock (ofNat (2 ^ 200 + 5 * 2 ^ 64 + 3)) 3 5 == ofNat (2 ^ 8)
#guard kroneckerPackEven 1 #[ofNat 5, ofNat 7, ofNat 11] == ofNat (5 + 11 * 2 ^ 128)
#guard kroneckerPackOdd 1 #[ofNat 5, ofNat 7, ofNat 11] == ofNat (7 * 2 ^ 64)
#guard kroneckerPackOdd 1 #[ofNat 5] == 0
#guard (kroneckerEvalPair 1 #[ofNat 5, ofNat 7, ofNat 11]).1
  == ofNat (5 + 7 * 2 ^ 64 + 11 * 2 ^ 128)
#guard (kroneckerEvalPair 1 #[ofNat 5, ofNat 7]).2 == (ofNat 5).toAzInt - (ofNat (7 * 2 ^ 64)).toAzInt
#guard kroneckerHalves (ofNat 10) (-(ofNat 4).toAzInt) == (ofNat 3, ofNat 7)
#guard kroneckerCoeff2 1 (ofNat (5 + 11 * 2 ^ 128)) (ofNat (7 * 2 ^ 64)) 1 == ofNat 7
#guard kroneckerCoeff2 1 (ofNat (5 + 11 * 2 ^ 128)) (ofNat (7 * 2 ^ 64)) 2 == ofNat 11

end Azurite.AzNat
