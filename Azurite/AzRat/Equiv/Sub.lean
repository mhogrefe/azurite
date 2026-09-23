/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Sub
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Unary

/-!
# Equivalence of `AzRat` subtraction with `Rat` subtraction

The key fact is structural: although `AzRat.sub` is implemented directly
(to avoid allocating an intermediate `-y`), it is *definitionally* the
composition `x + (-y)` — negation only flips the sign bit, so `add`'s body
applied to `-y` is syntactically `sub`'s body applied to `y`
(`sub_eq_add_neg`). Field-level correctness in both directions
(`toRat_sub`, `ofRat_sub`) then follows from the addition and negation
theorems.
-/

namespace Azurite.AzRat

/-- `AzRat.sub` is `x + (-y)`, structurally: negation only flips the sign
bit, and every gcd and invariant proof in `sub`'s body is sign-blind, so
the two sides build identical fields and the equality holds by unfolding —
no `toRat`-level reasoning needed. The direct implementation just avoids
materializing the intermediate `-y`. -/
theorem sub_eq_add_neg (x y : AzRat) : x - y = x + -y := by
  show AzRat.sub x y = AzRat.add x (AzRat.neg y)
  by_cases hx : x.num = 0
  · rw [AzRat.sub, dite_eq_left hx, AzRat.add, dite_eq_left hx]
    rfl
  · by_cases hy : y.num = 0
    · rw [AzRat.sub, dite_eq_right hx, dite_eq_left hy, AzRat.add, dite_eq_right hx,
          dite_eq_left (show (AzRat.neg y).num = 0 from hy)]
    · have hneg : AzRat.neg y = ⟨!y.sign, y.num, y.den, y.den_nz,
          fun h => absurd h hy, y.reduced⟩ :=
        AzRat.ext (ite_eq_right hy) rfl rfl
      rw [AzRat.sub, dite_eq_right hx, dite_eq_right hy, hneg, AzRat.add, dite_eq_right hx,
          dite_eq_right (show ¬((⟨!y.sign, y.num, y.den, y.den_nz,
            fun h => absurd h hy, y.reduced⟩ : AzRat).num = 0) from hy)]

@[simp] theorem toRat_sub (x y : AzRat) : toRat (x - y) = toRat x - toRat y := by
  rw [sub_eq_add_neg, toRat_add, toRat_neg, _root_.sub_eq_add_neg]

@[simp] theorem ofRat_sub (r s : ℚ) : ofRat (r - s) = ofRat r - ofRat s :=
  toRat_injective (by rw [toRat_ofRat, toRat_sub, toRat_ofRat, toRat_ofRat])

end Azurite.AzRat
