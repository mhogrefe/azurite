/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.CompareProduct

/-!
## Comparing two products of rationals without multiplying

`compareProducts w x y z` compares `w · x` with `y · z`.  With `w = ±nw/dw` and so on, the signs
settle every case except nonzero products of the same sign, where the magnitudes compare as
`nw · nx · dy · dz` against `ny · nz · dw · dx`.  As in `compareProduct`, that comparison of two
four-factor products (`compareProductsMag`) multiplies only as a last resort: the bit lengths
with a surplus of four bits (eight constant-time bit counts, before any comparison of limbs),
then three factorwise screens (`screen4`) — `|w|, |x| ≤ 1` against `|y|, |z| ≥ 1` or the
reverse, then the pairings matching `w` with `y` and `x` with `z`, and `w` with `z` and `x` with
`y` — and finally the products `nw · nx`, `dw · dx`, `ny · nz`, `dy · dz` handed to
`AzNat.compareProducts`, whose own screens may still avoid the last two multiplications.
Neither `w · x` nor `y · z` is formed or reduced.

Correctness: `Equiv/CompareProducts.lean` (`compareProducts_eq`).
-/

namespace Azurite.AzRat

/-- Four factorwise comparisons decide a comparison of products when they all point one way
(equalities allowed). -/
def screen4 (o₁ o₂ o₃ o₄ : Ordering) : Option Ordering :=
  if o₁ ≠ .gt ∧ o₂ ≠ .gt ∧ o₃ ≠ .gt ∧ o₄ ≠ .gt then
    some (if o₁ = .eq ∧ o₂ = .eq ∧ o₃ = .eq ∧ o₄ = .eq then .eq else .lt)
  else if o₁ ≠ .lt ∧ o₂ ≠ .lt ∧ o₃ ≠ .lt ∧ o₄ ≠ .lt then some .gt
  else none

/-- Compare `nw · nx · dy · dz` with `ny · nz · dw · dx` (all positive), multiplying only as a
last resort. -/
def compareProductsMag (nw dw nx dx ny dy nz dz : AzNat) : Ordering :=
  let s₁ := nw.size + nx.size + dy.size + dz.size
  let s₂ := ny.size + nz.size + dw.size + dx.size
  if s₂ + 4 ≤ s₁ then .gt
  else if s₁ + 4 ≤ s₂ then .lt
  else
  match screen4 (AzNat.compare nw dw) (AzNat.compare nx dx) (AzNat.compare dy ny)
      (AzNat.compare dz nz) with
  | some o => o
  | none =>
  match screen4 (AzNat.compare nw ny) (AzNat.compare nx nz) (AzNat.compare dy dw)
      (AzNat.compare dz dx) with
  | some o => o
  | none =>
  match screen4 (AzNat.compare nw nz) (AzNat.compare nx ny) (AzNat.compare dy dx)
      (AzNat.compare dz dw) with
  | some o => o
  | none => AzNat.compareProducts (nw * nx) (dy * dz) (ny * nz) (dw * dx)

/-- **Compare `w · x` with `y · z`**, multiplying only as a last resort. -/
def compareProducts (w x y z : AzRat) : Ordering :=
  if w.num = 0 ∨ x.num = 0 then
    if y.num = 0 ∨ z.num = 0 then .eq else if y.sign == z.sign then .lt else .gt
  else if y.num = 0 ∨ z.num = 0 then (if w.sign == x.sign then .gt else .lt)
  else if w.sign == x.sign then
    if y.sign == z.sign then compareProductsMag w.num w.den x.num x.den y.num y.den z.num z.den
    else .gt
  else if y.sign == z.sign then .lt
  else (compareProductsMag w.num w.den x.num x.den y.num y.den z.num z.den).swap

end Azurite.AzRat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

#guard compareProducts (Q "3/7") (Q "7/3") (Q "1/2") (Q "2") == .eq
#guard compareProducts (Q "3/7") (Q "7/3") (Q "1/2") (Q "3") == .lt
#guard compareProducts (Q "-3/7") (Q "-7/3") (Q "-1/2") (Q "-3") == .lt
#guard compareProducts (Q "-3/7") (Q "7/3") (Q "1/2") (Q "-2") == .eq
#guard compareProducts (Q "-3/7") (Q "7/3") (Q "1/2") (Q "-3") == .gt
#guard compareProducts (Q "3/7") (Q "7/3") (Q "-1/2") (Q "3") == .gt
#guard compareProducts (Q "-3/7") (Q "7/3") (Q "1/2") (Q "3") == .lt
#guard compareProducts (Q "0") (Q "7/3") (Q "0") (Q "-5") == .eq
#guard compareProducts (Q "0") (Q "7/3") (Q "1/2") (Q "-5") == .gt
#guard compareProducts (Q "3/7") (Q "7/3") (Q "0") (Q "-5") == .gt
#guard compareProducts (Q "3/7") (Q "-7/3") (Q "0") (Q "5") == .lt
#guard compareProducts (Q "1/3") (Q "1/5") (Q "7") (Q "9/2") == .lt      -- the first screen
#guard compareProducts (Q "2/3") (Q "1/5") (Q "3/5") (Q "1/4") == .lt    -- `w ≤ y`, `x ≤ z`
#guard compareProducts (Q "2/3") (Q "1/4") (Q "3/5") (Q "1/5") == .gt
#guard compareProducts (Q "11/10") (Q "9/10") (Q "9/10") (Q "11/10") == .eq
#guard compareProducts (Q "11/10") (Q "9/10") (Q "99/100") (Q "1") == .eq   -- the last resort
#guard compareProducts (Q "11/10") (Q "9/10") (Q "49/50") (Q "1") == .gt
#guard compareProducts (Q "11/10") (Q "9/10") (Q "1") (Q "1") == .lt
-- agreement with the multiplied comparison on a grid
private def grid : List AzRat :=
  ["0", "1", "-1", "-1/2", "3/7", "-7/3", "255/256", "65535/65536", "-18446744073709551616/3",
   "340282366920938463463374607431768211456/7",
   "1000000000000000000000000000000000000001/1000000000000000000000000000000000000000"].map Q
#guard grid.all fun w => grid.all fun x => grid.all fun y => grid.all fun z =>
  compareProducts w x y z == AzRat.cmp (w * x) (y * z)

end Tests
