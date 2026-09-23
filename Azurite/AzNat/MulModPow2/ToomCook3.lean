/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook3
import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.OfLimbs

/-!
## `AzNat.mulToomCook3ModPow2` — low (mod `2 ^ k`) Toom-Cook-3 multiplication

The same Mulders short-product recursion as `karatsubaMulLowLimbs`, but the corner
full product is computed by **full Toom-Cook 3** rather than Karatsuba, and the
split point is retuned for Toom-3's exponent.

The short-product recurrence `SP(n) = M(k) + 2·SP(n − k)` has leading constant
`(k/n)^α / (1 − 2·(1 − k/n)^α)`.  With a Toom-3 corner (`α = log₃5 ≈ 1.465`) this
minimizes near `k/n ≈ 0.8` (value `≈ 0.889`), versus `0.694` for a Karatsuba
corner — so the tuned split here is `k = ⌈4·len/5⌉` (clamped to `len − 1`).  The
recursion stays correct for any `⌈len/2⌉ ≤ k ≤ len − 1`.
-/

namespace Azurite.AzNat

/-- Low `len` limbs of `a[loA : loA+len] * b[loB : loB+len]`, returned as an
    `AzNat`.  Short-product recursion with a full **Toom-Cook 3** corner product
    and a Toom-tuned split; falls back to `schoolbookMulLowLimbs` at the base. -/
def toomCook3MulLowLimbs (toomThreshold karaThreshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat) (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : AzNat :=
  if h_base : len < 2 ∨ len < toomThreshold then
    ofLimbs (schoolbookMulLowLimbs a b loA len loB len len hA hB)
  else
    have hlen : 2 ≤ len := by omega
    let k := min ((4 * len + 4) / 5) (len - 1)
    let m := len - k
    have hk_pos : 0 < k := by show 0 < min ((4 * len + 4) / 5) (len - 1); omega
    have hm_pos : 0 < m := by show 0 < len - min ((4 * len + 4) / 5) (len - 1); omega
    have hm_le : m ≤ k := by
      show len - min ((4 * len + 4) / 5) (len - 1) ≤ min ((4 * len + 4) / 5) (len - 1)
      omega
    have hkm : k + m = len := by
      show min ((4 * len + 4) / 5) (len - 1) + (len - min ((4 * len + 4) / 5) (len - 1)) = len
      omega
    have hm_lt : m < len := by show len - min ((4 * len + 4) / 5) (len - 1) < len; omega
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    let C0 := ofLimbs (toomCook3MulLimbs toomThreshold karaThreshold a b loA loB k hA0 hB0)
    have hMidA_a : loA + m ≤ a.size := by omega
    have hMidA_b : loB + k + m ≤ b.size := by omega
    let midA := toomCook3MulLowLimbs toomThreshold karaThreshold a b loA (loB + k) m hMidA_a hMidA_b
    have hMidB_a : loA + k + m ≤ a.size := by omega
    have hMidB_b : loB + m ≤ b.size := by omega
    let midB := toomCook3MulLowLimbs toomThreshold karaThreshold a b (loA + k) loB m hMidB_a hMidB_b
    let middle := addModPow2 midA midB (64 * m)
    let shifted := ofLimbs (Array.replicate k 0 ++ middle.limbs)
    addModPow2 C0 shifted (64 * len)
  termination_by len
  decreasing_by all_goals (simp_wf; omega)

/-- **Low (mod `2 ^ k`) Toom-Cook-3 multiplication.** `(a * b) mod 2 ^ k`,
    computing only the low `L = (k + 63) / 64` limbs of the product via the
    short-product recursion with a full Toom-Cook-3 corner.  `toomThreshold` is
    the low-recursion / Toom base cutoff, `karaThreshold` the Karatsuba fallback
    inside the corner Toom-3. -/
def mulToomCook3ModPow2 (toomThreshold karaThreshold : Nat) (a b : AzNat) (k : Nat) : AzNat :=
  let L := (k + 63) / 64
  let aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0
  let bPad : Array UInt64 := b.limbs ++ Array.replicate (L - b.limbs.size) 0
  have hA : 0 + L ≤ aPad.size := by
    show 0 + L ≤ (a.limbs ++ Array.replicate (L - a.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  have hB : 0 + L ≤ bPad.size := by
    show 0 + L ≤ (b.limbs ++ Array.replicate (L - b.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  modPow2 (toomCook3MulLowLimbs toomThreshold karaThreshold aPad bPad 0 0 L hA hB) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

-- Force the recursion (toomThreshold 2) and cross-check against `(x * y) % 2^k`.
#guard (mulToomCook3ModPow2 2 2 (parse "7") (parse "9") 4).toNat == 63 % 16
#guard (mulToomCook3ModPow2 2 2 (parse "255") (parse "255") 8).toNat == 65025 % 256
#guard (mulToomCook3ModPow2 2 2 (parse "255") (parse "255") 16).toNat == 65025
#guard (mulToomCook3ModPow2 2 2 (parse "0") (parse "12345") 32).toNat == 0
#guard (mulToomCook3ModPow2 2 2 (parse "1") (parse "12345") 32).toNat == 12345
#guard (mulToomCook3ModPow2 2 2 (parse "18446744073709551617")
  (parse "18446744073709551617") 64).toNat == 1
#guard (mulToomCook3ModPow2 2 2 (parse "18446744073709551617")
  (parse "18446744073709551617") 128).toNat == 36893488147419103233
#guard (mulToomCook3ModPow2 2 2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 200).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 200)
#guard (mulToomCook3ModPow2 3 2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 100).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 100)
#guard (mulToomCook3ModPow2 2 2
  (parse "31415926535897932384626433832795028841971693993751058209749445923")
  (parse "27182818284590452353602874713526624977572470936999595749669676277") 333).toNat ==
  (31415926535897932384626433832795028841971693993751058209749445923 *
   27182818284590452353602874713526624977572470936999595749669676277) % (2 ^ 333)
#guard (mulToomCook3ModPow2 2 2 (parse "123456789") (parse "987654321") 0).toNat == 0
-- Agreement with the Karatsuba-low and schoolbook-low variants.
#guard (mulToomCook3ModPow2 2 2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 150).toNat ==
  (mulSchoolbookModPow2 (parse "123456789012345678901234567890")
    (parse "987654321098765432109876543210") 150).toNat

end Tests
