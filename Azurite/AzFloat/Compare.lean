/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Compare
import Azurite.AzNat.Compare
import Azurite.AzNat.ShiftLeft

/-!
# Comparing `AzFloat`s

`partialCompare x y : Option Ordering` compares the values, `none` when either operand is
`NaN` (IEEE 754 semantics: `NaN` is unordered, even against itself).  Two finite values of the
same sign are compared by exponent, then by significand; since both significands are
left-aligned at limb boundaries, the shorter one is padded with whole zero limbs
(`compareMagnitude`).  `Equiv/Compare.lean` proves `partialCompare_eq`: the result is the
comparison of the `toVal`s.

The Boolean relations `eqIEEE`, `lt`, `le`, `gt`, `ge` are all `false` when a `NaN` is
involved; structural equality (`=`, `DecidableEq`) distinguishes precisions and is what `==`
means on `AzFloat`.
-/

namespace Azurite.AzFloat

/-- Compare `m₁ · 2^(e₁ − |m₁|)` with `m₂ · 2^(e₂ − |m₂|)` for left-aligned significands. -/
def compareMagnitude (e₁ : AzInt) (m₁ : AzNat) (e₂ : AzInt) (m₂ : AzNat) : Ordering :=
  match AzInt.compare e₁ e₂ with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
    if m₁.size ≤ m₂.size then AzNat.compare (m₁.shiftLeft (m₂.size - m₁.size)) m₂
    else AzNat.compare m₁ (m₂.shiftLeft (m₁.size - m₂.size))

/-- The comparison of two signs, `true` (positive) being the greater. -/
def compareSigns (s t : Bool) : Ordering :=
  if s = t then .eq else if s then .gt else .lt

/-- Compare the values of two floats; `none` when either is `NaN`. -/
def partialCompare : AzFloat → AzFloat → Option Ordering
  | nan, _ => none
  | _, nan => none
  | infinity s, infinity t => some (compareSigns s t)
  | infinity s, _ => some (if s then .gt else .lt)
  | _, infinity t => some (if t then .lt else .gt)
  | zero, zero => some .eq
  | zero, finite t _ _ _ _ => some (if t then .lt else .gt)
  | finite s _ _ _ _, zero => some (if s then .gt else .lt)
  | finite s e₁ _ m₁ _, finite t e₂ _ m₂ _ =>
    if s = t then
      let c := compareMagnitude e₁ m₁ e₂ m₂
      some (if s then c else c.swap)
    else some (if s then .gt else .lt)

/-- IEEE equality: equal values, `false` whenever a `NaN` is involved. -/
def eqIEEE (x y : AzFloat) : Bool := partialCompare x y == some .eq

/-- `x < y` on values, `false` whenever a `NaN` is involved. -/
def lt (x y : AzFloat) : Bool := partialCompare x y == some .lt

/-- `x ≤ y` on values, `false` whenever a `NaN` is involved. -/
def le (x y : AzFloat) : Bool := partialCompare x y != some .gt && partialCompare x y != none

/-- `x > y` on values, `false` whenever a `NaN` is involved. -/
def gt (x y : AzFloat) : Bool := partialCompare x y == some .gt

/-- `x ≥ y` on values, `false` whenever a `NaN` is involved. -/
def ge (x y : AzFloat) : Bool := partialCompare x y != some .lt && partialCompare x y != none

end Azurite.AzFloat
