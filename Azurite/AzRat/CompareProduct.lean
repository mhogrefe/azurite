/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzRat.Mul
import Azurite.AzRat.Compare
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString
import Azurite.AzNat.CompareProducts

/-!
## Comparing a product of rationals with a rational without multiplying

`compareProduct x y z` compares `x · y` with `z`.  With `x = ±nx/dx`, `y = ±ny/dy` and
`z = ±nz/dz`, the signs settle every case except nonzero `x · y` and `z` of the same sign, where
the magnitudes compare as `nx · ny · dz` against `nz · dx · dy`.  That comparison of two
three-factor products (`compareProductMag`) multiplies only as a last resort:

1. the bit lengths, `2^(s₁+s₂+s₃−3) ≤ a₁ a₂ a₃ < 2^(s₁+s₂+s₃)`, a surplus of three bits
   deciding — six constant-time bit counts, before any comparison of limbs;
2. three factorwise screens (`screen3`), each pairing the three factors of one side with the
   three of the other and deciding when the three comparisons all point one way: `(nx, dx)`,
   `(ny, dy)`, `(dz, nz)` — that is, `|x| ≤ 1`, `|y| ≤ 1`, `|z| ≥ 1` or the reverse — then
   `(nx, nz)`, `(ny, dy)`, `(dz, dx)` and `(nx, dx)`, `(ny, nz)`, `(dz, dy)`;
3. the products `nx · ny` and `dx · dy`, handed with `dz` and `nz` to `AzNat.compareProducts`,
   whose own screens may still avoid the last two multiplications.

No reduction of `x · y` (no gcd) is ever performed.

Correctness: `Equiv/CompareProduct.lean` (`compareProduct_eq`).
-/

namespace Azurite.AzRat

/-- Three factorwise comparisons decide a comparison of products when they all point one way
(equalities allowed): `some .lt`, `some .eq`, `some .gt`, or `none`. -/
def screen3 (o₁ o₂ o₃ : Ordering) : Option Ordering :=
  if o₁ ≠ .gt ∧ o₂ ≠ .gt ∧ o₃ ≠ .gt then
    some (if o₁ = .eq ∧ o₂ = .eq ∧ o₃ = .eq then .eq else .lt)
  else if o₁ ≠ .lt ∧ o₂ ≠ .lt ∧ o₃ ≠ .lt then some .gt
  else none

/-- Compare `nx · ny · dz` with `nz · dx · dy` (all positive), multiplying only as a last
resort. -/
def compareProductMag (nx dx ny dy nz dz : AzNat) : Ordering :=
  let s₁ := nx.size + ny.size + dz.size
  let s₂ := nz.size + dx.size + dy.size
  if s₂ + 3 ≤ s₁ then .gt
  else if s₁ + 3 ≤ s₂ then .lt
  else
  match screen3 (AzNat.compare nx dx) (AzNat.compare ny dy) (AzNat.compare dz nz) with
  | some o => o
  | none =>
  match screen3 (AzNat.compare nx nz) (AzNat.compare ny dy) (AzNat.compare dz dx) with
  | some o => o
  | none =>
  match screen3 (AzNat.compare nx dx) (AzNat.compare ny nz) (AzNat.compare dz dy) with
  | some o => o
  | none => AzNat.compareProducts (nx * ny) dz (dx * dy) nz

/-- **Compare `x · y` with `z`**, multiplying only as a last resort. -/
def compareProduct (x y z : AzRat) : Ordering :=
  if x.num = 0 ∨ y.num = 0 then
    if z.num = 0 then .eq else if z.sign then .lt else .gt
  else if z.num = 0 then (if x.sign == y.sign then .gt else .lt)
  else if x.sign == y.sign then
    if z.sign then compareProductMag x.num x.den y.num y.den z.num z.den else .gt
  else if z.sign then .lt
  else (compareProductMag x.num x.den y.num y.den z.num z.den).swap

end Azurite.AzRat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

#guard compareProduct (Q "3/7") (Q "7/3") (Q "1") == .eq
#guard compareProduct (Q "3/7") (Q "7/3") (Q "2") == .lt
#guard compareProduct (Q "-3/7") (Q "-7/3") (Q "1/2") == .gt
#guard compareProduct (Q "-3/7") (Q "7/3") (Q "-1") == .eq
#guard compareProduct (Q "-3/7") (Q "7/3") (Q "-2") == .gt
#guard compareProduct (Q "-3/7") (Q "7/3") (Q "-1/2") == .lt
#guard compareProduct (Q "3/7") (Q "7/3") (Q "-5") == .gt
#guard compareProduct (Q "-3/7") (Q "7/3") (Q "5") == .lt
#guard compareProduct (Q "0") (Q "7/3") (Q "0") == .eq
#guard compareProduct (Q "0") (Q "7/3") (Q "-1/9") == .gt
#guard compareProduct (Q "3/7") (Q "0") (Q "1/9") == .lt
#guard compareProduct (Q "3/7") (Q "7/3") (Q "0") == .gt
#guard compareProduct (Q "3/7") (Q "-7/3") (Q "0") == .lt
#guard compareProduct (Q "1/3") (Q "1/5") (Q "7") == .lt              -- the first screen
#guard compareProduct (Q "5") (Q "3") (Q "1/7") == .gt
#guard compareProduct (Q "2/3") (Q "1/5") (Q "3/5") == .lt            -- `x ≤ z`, `y ≤ 1`
#guard compareProduct (Q "7/5") (Q "6/5") (Q "7/5") == .gt
#guard compareProduct (Q "11/10") (Q "9/10") (Q "99/100") == .eq      -- the last resort
#guard compareProduct (Q "11/10") (Q "9/10") (Q "49/50") == .gt
#guard compareProduct (Q "11/10") (Q "9/10") (Q "1") == .lt
-- agreement with the multiplied comparison on a grid
private def grid : List AzRat :=
  ["0", "1", "-1", "2", "-1/2", "3/7", "-7/3", "255/256", "-256/255", "65535/65536",
   "18446744073709551616/3", "-3/18446744073709551615",
   "340282366920938463463374607431768211456/7", "-7/340282366920938463463374607431768211457",
   "1000000000000000000000000000000000000001/1000000000000000000000000000000000000000"].map Q
#guard grid.all fun x => grid.all fun y => grid.all fun z =>
  compareProduct x y z == AzRat.cmp (x * y) z

end Tests
