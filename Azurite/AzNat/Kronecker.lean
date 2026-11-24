/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Mul.ToomCook3

/-!
# Packing coefficients into one number (Kronecker substitution)

`kroneckerPack w a` is `∑ aᵢ · 2^(64 w i)`: the coefficients `w` limbs apart, so that a
product of polynomials becomes one product of numbers; `kroneckerCoeff w x k` reads the
`k`-th block of `w` limbs back.  Both only copy limbs.  The values are in
`Equiv/Kronecker.lean`.
-/

namespace Azurite.AzNat

/-- The limbs of the coefficients, each cut or padded to `w` limbs, one after the other. -/
def kroneckerLimbs (w : Nat) (a : Array AzNat) : Array UInt64 :=
  a.foldl (fun out c => out ++ truncatePad c.limbs w) (Array.mkEmpty (w * a.size))

/-- `∑ aᵢ · 2^(64 w i)`, for coefficients below `2^(64 w)`. -/
def kroneckerPack (w : Nat) (a : Array AzNat) : AzNat :=
  ofLimbs (kroneckerLimbs w a)

/-- The `k`-th block of `w` limbs: `⌊x / 2^(64 w k)⌋ mod 2^(64 w)`. -/
def kroneckerCoeff (w : Nat) (x : AzNat) (k : Nat) : AzNat :=
  ofLimbs (x.limbs.extract (k * w) (k * w + w))

/-- The largest number of limbs of an entry. -/
def maxLimbs (a : Array AzNat) : Nat :=
  a.foldl (fun s c => max s c.limbs.size) 0

/-- The total number of limbs of the entries. -/
def sumLimbs (a : Array AzNat) : Nat :=
  a.foldl (fun s c => s + c.limbs.size) 0

#guard sumLimbs #[ofNat 5, ofNat (2 ^ 100), 0] == 3
#guard maxLimbs #[ofNat 5, ofNat (2 ^ 100), 0] == 2
#guard kroneckerPack 1 #[ofNat 5, ofNat 7, ofNat 11] == ofNat (5 + 7 * 2 ^ 64 + 11 * 2 ^ 128)
#guard kroneckerPack 2 #[ofNat (2 ^ 100), 0, ofNat 3] == ofNat (2 ^ 100 + 3 * 2 ^ 256)
#guard kroneckerPack 2 #[ofNat 9, 0, 0] == ofNat 9
#guard kroneckerPack 3 #[] == 0
#guard kroneckerCoeff 2 (ofNat (2 ^ 100 + 3 * 2 ^ 256)) 0 == ofNat (2 ^ 100)
#guard kroneckerCoeff 2 (ofNat (2 ^ 100 + 3 * 2 ^ 256)) 1 == 0
#guard kroneckerCoeff 2 (ofNat (2 ^ 100 + 3 * 2 ^ 256)) 2 == ofNat 3
#guard kroneckerCoeff 2 (ofNat (2 ^ 100 + 3 * 2 ^ 256)) 5 == 0

end Azurite.AzNat
