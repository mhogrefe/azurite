/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZModPow2.Instances
import Azurite.AzZModPow2.ToString
import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Mul
import Mathlib.Data.Nat.Log

/-!
## Square roots in `ℤ / 2^k`

`sqrt? a` returns the **least** square root of `a` in `ℤ / 2^k`, or `none` when `a` is not a
square.  Everything here is derived from first principles; no library code was consulted.

**Structure of the squares.**  Write a nonzero residue as `a = 2^v u` with `u` odd and `v < k`.
If `r² ≡ a (mod 2^k)` then `v = 2w` is even and `r = 2^w t` with `t` odd and `t² ≡ u (mod 2^n)`,
`n = k − v`; conversely such a `t` gives a root.  An odd `u` is a square modulo `2^n` exactly
when `u ≡ 1 (mod 8)` (for `n ≤ 2` this says `u = 1`, the only odd square below `4`), and its
roots modulo `2^n` are `±s` and `±s + 2^(n−1)` for any one root `s` (for `n ≥ 3` these are four
distinct roots).  So the least root of `a` is `2^w` times the least of those four residues that
squares to `u` modulo `2^n`.

**One root of an odd square (`oddSqrt`).**  Newton iteration for the inverse square root in the
2-adic integers: with `e = 1 − u y²` the step `y ↦ y (1 + e / 2)` (`e` is even) gives
`1 − u y'² = e² (3 + e) / 4`, so if `2^j ∣ e` with `j ≥ 3` then `2^(2j−2)` divides the new error —
the precision `j − 2` doubles each step.  Starting from `y = 1` (valid since `u ≡ 1 (mod 8)`),
`⌈log₂ k⌉` steps reach precision `k`, and `s = u y` is a root (`s² = u² y² = u`).  The halving
of `e` is done on its canonical residue; the result is only determined modulo `2^(k−1)`, which
is harmless since the top bit of `y` does not affect `u y²` modulo `2^k`.  Each step is two
multiplications at full width, `O(M(k) log k)` in total (increasing the precision step by step
would give `O(M(k))`; not done).

The candidate is verified by one squaring, so `sqrt?_some` (`sqrt? a = some r → r * r = a`)
holds without any analysis; `sqrt?_isSome_iff` (a root is returned exactly when `a` is a
square) and `sqrt?_le` (the returned root is the least) rest on the structure above.
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- One Newton step for the inverse square root: `y ↦ y (1 + e/2)` with `e = 1 − u y²`
(halved on its canonical residue). -/
def invSqrtStep (u y : AzZModPow2 k) : AzZModPow2 k :=
  let e := 1 - u * y * y
  y + y * ofAzNat k (e.val >>> 1)

/-- `n` Newton steps from `y = 1`. -/
def invSqrtAux (u : AzZModPow2 k) : Nat → AzZModPow2 k
  | 0 => 1
  | n + 1 => invSqrtStep u (invSqrtAux u n)

/-- A square root of `u ≡ 1 (mod 8)`: `u y` with `y` the inverse square root after `⌈log₂ k⌉`
Newton steps. -/
def oddSqrt (u : AzZModPow2 k) : AzZModPow2 k := u * invSqrtAux u (Nat.clog 2 k)

/-- The least `c` in the list with `c² ≡ u (mod 2^n)`, if any. -/
def leastRoot (u : AzNat) (n : Nat) : List AzNat → Option AzNat
  | [] => none
  | c :: cs =>
    let rest := leastRoot u n cs
    if (c * c).modPow2 n = u then
      some (match rest with | none => c | some m => min c m)
    else rest

/-- **Least square root in `ℤ / 2^k`**, or `none` for a non-square. -/
def sqrt? (a : AzZModPow2 k) : Option (AzZModPow2 k) :=
  match a.val.trailingZeros with
  | none => some 0
  | some v =>
    if v % 2 = 1 then none
    else
      let u := a.val >>> v
      if u.modPow2 3 ≠ 1 then none
      else
        let n := k - v
        let s := (oddSqrt (ofAzNat k u)).val
        let S : AzZModPow2 n := ofAzNat n s
        let H : AzZModPow2 n := ofAzNat n ((1 : AzNat) <<< (n - 1))
        match leastRoot u n [S.val, (-S).val, (S + H).val, (-S + H).val] with
        | none => none
        | some c =>
          let r := ofAzNat k (c <<< (v / 2))
          if r * r = a then some r else none

end Azurite.AzZModPow2

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZModPow2

/-- `sqrt?` of `a` modulo `2^k`, as a decimal string (`"none"` for a non-square). -/
private def S (k a : Nat) : String :=
  match sqrt? (AzZModPow2.ofNat k a) with
  | none => "none"
  | some r => AzZModPow2.toString r

-- tiny moduli
#guard S 0 0 == "0"
#guard S 1 0 == "0"
#guard S 1 1 == "1"
#guard S 2 1 == "1"
#guard S 2 2 == "none"
#guard S 2 3 == "none"
#guard S 3 1 == "1"                 -- roots 1, 3, 5, 7
#guard S 3 4 == "2"                 -- roots 2, 6
#guard S 3 3 == "none"
#guard S 3 5 == "none"
#guard S 3 2 == "none"
#guard S 4 9 == "3"                 -- roots 3, 5, 11, 13
#guard S 4 12 == "none"             -- 4 · 3, and 3 is not a square modulo 4
#guard S 4 8 == "none"              -- odd valuation
#guard S 5 17 == "7"                -- roots 7, 9, 23, 25
#guard S 5 25 == "5"                -- roots 5, 11, 21, 27
#guard S 5 4 == "2"
#guard S 5 16 == "4"                -- roots 4, 12, 20, 28
-- one limb
#guard S 64 17 == "405959429219100393"
#guard S 64 (17 <<< 20) == "2195515552539648"
#guard S 64 (3 <<< 4) == "none"
#guard S 64 0 == "0"
-- multi-limb: the least root of `x²` is `x` itself when `x < 2^(k−1) − x`
#guard S 200 (12345678901234567890123456789 ^ 2) == "12345678901234567890123456789"
#guard S 200 ((12345678901234567890123456789 ^ 2) <<< 6) == "98765431209876543120987654312"
#guard S 200 ((12345678901234567890123456789 ^ 2) <<< 7) == "none"
#guard S 200 (12345678901234567890123456789 ^ 2 + 2) == "none"
-- every result squares back to the input
#guard [(5, 17), (5, 25), (64, 17), (64, 17 <<< 20), (200, 12345678901234567890123456789 ^ 2),
    (200, (12345678901234567890123456789 ^ 2) <<< 6), (130, 33), (130, 33 <<< 64)].all
  fun (k, a) =>
    match sqrt? (AzZModPow2.ofNat k a) with
    | none => false
    | some r => r * r = AzZModPow2.ofNat k a

end Tests
