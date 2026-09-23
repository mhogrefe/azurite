/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square.Karatsuba
import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.SquareModPow2.Schoolbook
import Azurite.AzNat.MulModPow2.Karatsuba
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.OfLimbs

/-!
## `AzNat.squareKaratsubaModPow2` — low (mod `2 ^ k`) Karatsuba squaring

Combines the squaring symmetry with the top-half-skipping low product.  Writing
`a = A₀ + A₁·βˢ` (with `β = 2^64`),
\[ a^2 \equiv A_0^2 + 2\,A_0 A_1\,β^s \pmod{β^L}, \]
since the `A₁²·β^{2s}` term vanishes modulo `β^L` (`2s ≥ L`).  So the low square
is **non-recursive**: one full Karatsuba *square* of the low part `A₀` (the
symmetry win), plus one low Karatsuba *multiply* of the cross `A₀·A₁` (doubled),
dropping the high square entirely.  The split is Mulders' tuned point
`s = ⌈11·L/16⌉` (as for the low Karatsuba product).
-/

namespace Azurite.AzNat

/-- **Low Karatsuba squaring.** `(a ^ 2) mod 2 ^ k`, computing only the low
    `L = (k + 63) / 64` limbs via a full-square corner plus a low cross product,
    dropping the high square. -/
def squareKaratsubaModPow2 (threshold : Nat) (a : AzNat) (k : Nat) : AzNat :=
  let L := (k + 63) / 64
  let aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0
  have hL : 0 + L ≤ aPad.size := by
    show 0 + L ≤ (a.limbs ++ Array.replicate (L - a.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  if h : L < 2 ∨ L < threshold then
    modPow2 (ofLimbs (schoolbookSquareLimbs aPad 0 L (by omega))) k
  else
    let s := min ((11 * L + 15) / 16) (L - 1)
    let m := L - s
    have hs : 0 + s ≤ aPad.size := by
      have : s ≤ L := by omega
      omega
    have hcrossA : 0 + m ≤ aPad.size := by
      have : m ≤ L := by omega
      omega
    have hcrossB : s + m ≤ aPad.size := by
      have : s + m = L := by omega
      omega
    let cornerFull := ofLimbs (karatsubaSquareLimbs threshold aPad 0 s (by omega))
    let cross := karatsubaMulLowLimbs threshold aPad aPad 0 s m hcrossA hcrossB
    let doubled := addModPow2 cross cross (64 * m)
    let shifted := ofLimbs (Array.replicate s 0 ++ doubled.limbs)
    modPow2 (addModPow2 cornerFull shifted (64 * L)) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

-- Force the recursion (threshold 2); cross-check against `(x^2) % 2^k`.
#guard (squareKaratsubaModPow2 2 (parse "7") 4).toNat == 49 % 16
#guard (squareKaratsubaModPow2 2 (parse "255") 8).toNat == 65025 % 256
#guard (squareKaratsubaModPow2 2 (parse "255") 16).toNat == 65025
#guard (squareKaratsubaModPow2 2 (parse "0") 32).toNat == 0
#guard (squareKaratsubaModPow2 2 (parse "1") 32).toNat == 1
#guard (squareKaratsubaModPow2 2 (parse "18446744073709551617") 64).toNat == 1
#guard (squareKaratsubaModPow2 2 (parse "18446744073709551617") 128).toNat ==
  (18446744073709551617 ^ 2) % (2 ^ 128)
#guard (squareKaratsubaModPow2 2 (parse "123456789012345678901234567890") 200).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 200)
#guard (squareKaratsubaModPow2 3 (parse "123456789012345678901234567890") 100).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 100)
#guard (squareKaratsubaModPow2 2
  (parse "31415926535897932384626433832795028841971693993751058209749445923") 333).toNat ==
  (31415926535897932384626433832795028841971693993751058209749445923 ^ 2) % (2 ^ 333)
#guard (squareKaratsubaModPow2 2 (parse "123456789") 0).toNat == 0
-- Agreement with the schoolbook-low square.
#guard (squareKaratsubaModPow2 2 (parse "123456789012345678901234567890") 150).toNat ==
  (squareSchoolbookModPow2 (parse "123456789012345678901234567890") 150).toNat

end Tests
