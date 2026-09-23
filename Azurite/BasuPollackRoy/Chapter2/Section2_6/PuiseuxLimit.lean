/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.Notation_2_100
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Corollary_2_98

/-! # BPR §2.6 — the base-field embedding `R ↪ R⟨ε⟩` and `lim_ε` foundations

Foundations for Proposition 3.5: the embedding `R ↪ R⟨ε⟩ = algebraicPuiseux R` (constants are
algebraic over `R(ε)`), that `lim_ε` fixes the base field, and the infinitesimal characterization
`lim_ε y = x ↔ y − x` is infinitesimal. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- `R(ε) = RatFunc R` acts on `R⟨ε⟩ = algebraicPuiseux R` (its relative algebraic closure). -/
noncomputable instance ratFuncAlgebraicPuiseuxAlgebra :
    Algebra (RatFunc R) (algebraicPuiseux R) :=
  inferInstanceAs (Algebra (RatFunc R) (algebraicClosure (RatFunc R) (PuiseuxSeries R)))

/-- **The base-field embedding `R ↪ R⟨ε⟩`**, as the composite `R → R(ε) → R⟨ε⟩`. -/
noncomputable instance algebraRAlgebraicPuiseux : Algebra R (algebraicPuiseux R) :=
  ((algebraMap (RatFunc R) (algebraicPuiseux R)).comp (algebraMap R (RatFunc R))).toAlgebra

theorem algebraMap_algebraicPuiseux_eq (c : R) :
    algebraMap R (algebraicPuiseux R) c
      = algebraMap (RatFunc R) (algebraicPuiseux R) (algebraMap R (RatFunc R) c) := rfl

/-- `ε = single 1 1` is algebraic over `R(ε)` (it is `R(ε)`'s indeterminate `X`), hence in `R⟨ε⟩`. -/
theorem puiseuxEps_mem_algebraicPuiseux :
    (puiseuxEps : PuiseuxSeries R) ∈ algebraicPuiseux R := by
  rw [mem_algebraicPuiseux]
  have h : (puiseuxEps : PuiseuxSeries R) = algebraMap (RatFunc R) (PuiseuxSeries R) RatFunc.X := by
    rw [RingHom.algebraMap_toAlgebra]
    apply Subtype.ext
    rw [ratFuncToPuiseuxHom_apply, ratFuncToPuiseux_coe, RatFunc.coe_X, puiseuxEmb_single,
      show puiseuxExpHom (1 : ℕ+) (1 : ℤ) = (1 : ℚ) from by simp]
    rfl
  rw [h]; exact isAlgebraic_algebraMap _

/-- **`ε` as an element of `R⟨ε⟩`.** -/
noncomputable def epsAP (R : Type*) [Field R] : algebraicPuiseux R :=
  ⟨puiseuxEps, puiseuxEps_mem_algebraicPuiseux⟩

@[simp] theorem coe_epsAP : ((epsAP R : algebraicPuiseux R) : PuiseuxSeries R) = puiseuxEps := rfl

/-- **The gate lemma**: the Puiseux embedding of a constant rational function is the constant series
`single 0 c`. -/
theorem ratFuncToPuiseux_algebraMap (c : R) :
    ratFuncToPuiseux (algebraMap R (RatFunc R) c) = constPuiseux c := by
  apply Subtype.ext
  rw [ratFuncToPuiseux_coe, coe_constPuiseux]
  have hL : ((algebraMap R (RatFunc R) c : RatFunc R) : LaurentSeries R)
      = HahnSeries.single (0 : ℤ) c := by
    rw [RatFunc.algebraMap_eq_C,
      show (RatFunc.C c : RatFunc R) = ((Polynomial.C c : Polynomial R) : RatFunc R) from by
        rw [← RatFunc.algebraMap_C]; rfl,
      ← RatFunc.coe_coe, Polynomial.coe_C, PowerSeries.coe_C, HahnSeries.C_apply]
  rw [hL, puiseuxEmb_single, show puiseuxExpHom (1 : ℕ+) (0 : ℤ) = (0 : ℚ) from by simp]

/-- The base-field embedding sends `c` to the constant series `single 0 c`. -/
theorem algebraMap_algebraicPuiseux_coe (c : R) :
    ((algebraMap R (algebraicPuiseux R) c : algebraicPuiseux R) : PuiseuxSeries R)
      = constPuiseux c := by
  rw [algebraMap_algebraicPuiseux_eq]
  have hcoe : ((algebraMap (RatFunc R) (algebraicPuiseux R) (algebraMap R (RatFunc R) c) :
      algebraicPuiseux R) : PuiseuxSeries R)
      = algebraMap (RatFunc R) (PuiseuxSeries R) (algebraMap R (RatFunc R) c) := rfl
  rw [hcoe]
  show ratFuncToPuiseuxHom R (algebraMap R (RatFunc R) c) = constPuiseux c
  rw [ratFuncToPuiseuxHom_apply, ratFuncToPuiseux_algebraMap]

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- `R⟨ε⟩` is real closed (Corollary 2.98), registered as an instance for the `Ext`-to-`R⟨ε⟩`
machinery used in Proposition 3.5. -/
instance instIsRealClosedAlgebraicPuiseux [IsRealClosed R] : IsRealClosed (algebraicPuiseux R) :=
  isRealClosed_algebraicPuiseux R

/-- **`ε > 0`** in `R⟨ε⟩`. -/
theorem epsAP_pos : (0 : algebraicPuiseux R) < epsAP R := by
  rw [← Subtype.coe_lt_coe]; simpa using puiseuxEps_pos

/-- **`ε < b`** in `R⟨ε⟩` for every positive *real* `b`: `ε` is infinitesimal. -/
theorem epsAP_lt_algebraMap {b : R} (hb : 0 < b) :
    epsAP R < algebraMap R (algebraicPuiseux R) b := by
  rw [← Subtype.coe_lt_coe, coe_epsAP, algebraMap_algebraicPuiseux_coe, ← algebraMap_eq_constPuiseux]
  exact puiseuxEps_lt_algebraMap hb

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The embedding of a base-field element is bounded. -/
theorem algebraMap_mem_puiseuxBounded (c : R) :
    algebraMap R (algebraicPuiseux R) c ∈ puiseuxBounded R := by
  rw [mem_puiseuxBounded, algebraMap_algebraicPuiseux_coe]
  exact puiseuxOrder_constPuiseux_nonneg c

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **`lim_ε` fixes the base field.** -/
theorem puiseuxLim_algebraMap (c : R) :
    puiseuxLim R ⟨algebraMap R (algebraicPuiseux R) c, algebraMap_mem_puiseuxBounded c⟩ = c := by
  rw [puiseuxLim_apply,
    show (((⟨algebraMap R (algebraicPuiseux R) c, algebraMap_mem_puiseuxBounded c⟩ :
        puiseuxBounded R) : algebraicPuiseux R) : PuiseuxSeries R) = constPuiseux c from
      algebraMap_algebraicPuiseux_coe c,
    coe_constPuiseux, HahnSeries.coeff_single_same]

/-- **Positive order ⟹ infinitesimal.** -/
theorem infinitesimal_of_puiseuxOrder_pos {z : PuiseuxSeries R} (h : 0 < puiseuxOrder R z)
    (a : R) (ha : 0 < a) : |z| < algebraMap R (PuiseuxSeries R) a := by
  rw [puiseux_lt_iff_initCoeff,
    show algebraMap R (PuiseuxSeries R) a - |z| = algebraMap R (PuiseuxSeries R) a + (-|z|) from by
      ring,
    puiseuxInitCoeff_add_eq_left _ _ (by
      rw [puiseuxOrder_algebraMap_of_ne ha.ne', puiseuxOrder_neg, puiseuxOrder_abs]; exact h),
    puiseuxInitCoeff_algebraMap]
  exact ha

/-- **Infinitesimal ⟹ positive order.** -/
theorem puiseuxOrder_pos_of_infinitesimal {z : PuiseuxSeries R}
    (hinf : ∀ a : R, 0 < a → |z| < algebraMap R (PuiseuxSeries R) a) : 0 < puiseuxOrder R z := by
  have h0 : 0 ≤ puiseuxOrder R z :=
    (bounded_iff_puiseuxOrder_nonneg z).mp ⟨1, one_pos, hinf 1 one_pos⟩
  rcases eq_or_ne z 0 with rfl | hz
  · rw [puiseuxOrder_zero]; exact lt_of_lt_of_le (WithTop.coe_lt_top 0) le_rfl
  by_contra hnpos
  rw [not_lt] at hnpos
  have hord0 : puiseuxOrder R z = 0 := le_antisymm hnpos h0
  -- `c = initCoeff|z| > 0`; then `|z| − c` is infinitesimal, so `|z| > c/2 = alg(c/2)`
  set c := puiseuxInitCoeff R |z| with hc
  have hcpos : 0 < c := (puiseux_pos_iff _).mp (abs_pos.mpr hz)
  have hsub : 0 < puiseuxOrder R (|z| - algebraMap R (PuiseuxSeries R) c) := by
    rw [algebraMap_eq_constPuiseux]
    exact puiseuxOrder_sub_constPuiseux_leadingCoeff_pos (by rw [puiseuxOrder_abs, hord0])
  have key := hinf (c / 2) (show (0 : R) < c / 2 by linarith)
  rw [show |z| = algebraMap R (PuiseuxSeries R) c + (|z| - algebraMap R (PuiseuxSeries R) c) from
      by abel, puiseux_lt_iff_initCoeff,
    show algebraMap R (PuiseuxSeries R) (c / 2)
          - (algebraMap R (PuiseuxSeries R) c + (|z| - algebraMap R (PuiseuxSeries R) c))
        = algebraMap R (PuiseuxSeries R) (c / 2 - c) + (-(|z| - algebraMap R (PuiseuxSeries R) c))
      from by rw [map_sub]; ring,
    puiseuxInitCoeff_add_eq_left _ _ (by
      rw [puiseuxOrder_algebraMap_of_ne (ne_of_lt (show (c / 2 - c : R) < 0 by linarith)),
        puiseuxOrder_neg]; exact hsub), puiseuxInitCoeff_algebraMap] at key
  linarith

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- For a bounded series, the order-0 coefficient vanishes iff the order is strictly positive. -/
theorem coeff_zero_iff_puiseuxOrder_pos {w : PuiseuxSeries R} (hw : 0 ≤ puiseuxOrder R w) :
    (w : HahnSeries ℚ R).coeff 0 = 0 ↔ 0 < puiseuxOrder R w := by
  unfold puiseuxOrder at hw ⊢
  constructor
  · intro hc
    refine lt_of_le_of_ne hw (Ne.symm ?_)
    rw [← WithTop.coe_zero]; exact HahnSeries.orderTop_ne_of_coeff_eq_zero hc
  · intro hpos
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (by rwa [WithTop.coe_zero])

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **`lim_ε y = x` iff `y − x` has positive order** (for bounded `y`). -/
theorem puiseuxLim_eq_iff (y : puiseuxBounded R) (x : R) :
    puiseuxLim R y = x ↔
      0 < puiseuxOrder R (((y : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux x) := by
  have hord : 0 ≤ puiseuxOrder R (((y : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux x) := by
    rw [sub_eq_add_neg]
    refine le_trans (le_min ?_ ?_) (min_le_puiseuxOrder_add _ _)
    · exact y.2
    · rw [puiseuxOrder_neg]; exact puiseuxOrder_constPuiseux_nonneg x
  rw [← coeff_zero_iff_puiseuxOrder_pos hord, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub,
    coe_constPuiseux, HahnSeries.coeff_single_same, sub_eq_zero, puiseuxLim_apply]

end Ordered

end Azurite.BPR
