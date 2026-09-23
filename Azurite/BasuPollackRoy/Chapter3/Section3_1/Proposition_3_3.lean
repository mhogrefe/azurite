/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Continuity
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_84
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_85

/-! # BPR §3.1, Proposition 3.3 — composition; the ring of continuous semialgebraic functions

The composite of semialgebraic continuous functions is semialgebraic (Proposition 2.84) and
continuous (`ContinuousOn.comp`), giving **Proposition 3.3** (`proposition_3_3`). The semialgebraic
*continuous* functions `A → R` form a ring (`continuousSemialgebraicFunctions`): semialgebraicity is
closed under `+`, `×`, `−` by Proposition 2.85, and continuity by the ε–δ estimates
(`ContinuousOn.fin_one_add/mul/neg`) — our euclidean topology carries no `ContinuousAdd`/`ContinuousMul`
instance, so these are proved directly from `continuousOn_iff_ball`. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Proposition 3.3 — composition -/

/-- **BPR Proposition 3.3.** If `f : A → B` and `g : B → C` are semialgebraic and continuous, then
`g ∘ f : A → C` is semialgebraic and continuous. -/
theorem proposition_3_3 {k ℓ m : ℕ} {A : Set (Fin k → R)} {B : Set (Fin ℓ → R)}
    {C : Set (Fin m → R)} {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin m → R)}
    (hfsa : IsSemialgebraicFunction A f) (hgsa : IsSemialgebraicFunction B g)
    (hfc : ContinuousOn f A) (hgc : ContinuousOn g B)
    (hfAB : Set.MapsTo f A B) (hgBC : Set.MapsTo g B C) :
    IsSemialgebraicFunction A (g ∘ f) ∧ ContinuousOn (g ∘ f) A ∧ Set.MapsTo (g ∘ f) A C :=
  ⟨proposition_2_84 hfsa hgsa hfAB, hgc.comp hfc hfAB, hgBC.comp hfAB⟩

/-! ### Real-valued (`Fin 1`) continuity: the ε–δ bridge and closure under `+`, `×`, `−` -/

/-- The euclidean norm on `R^1` is the absolute value of the single coordinate. -/
theorem euclideanNorm_fin_one (z : Fin 1 → R) : euclideanNorm z = |z 0| := by
  have h : euclideanNorm z ^ 2 = |z 0| ^ 2 := by
    rw [euclideanNorm_sq, euclideanNormSq, Fin.sum_univ_one, sq_abs]
  exact (pow_left_inj₀ (euclideanNorm_nonneg z) (abs_nonneg _) (by norm_num)).mp h

/-- ε–δ continuity on `A` for an `R^1`-valued function, phrased via the single coordinate. -/
theorem continuousOn_fin_one_iff {k : ℕ} {f : (Fin k → R) → (Fin 1 → R)} {A : Set (Fin k → R)} :
    ContinuousOn f A ↔ ∀ x ∈ A, ∀ r, 0 < r → ∃ δ, 0 < δ ∧
      ∀ y ∈ A, euclideanNorm (y - x) < δ → |f y 0 - f x 0| < r := by
  rw [continuousOn_iff_ball]
  refine forall₂_congr fun x _ => forall₂_congr fun r _ => exists_congr fun δ =>
    and_congr_right fun _ => forall₂_congr fun y _ => imp_congr_right fun _ => ?_
  rw [euclideanNorm_fin_one, Pi.sub_apply]

theorem ContinuousOn.fin_one_neg {k : ℕ} {f : (Fin k → R) → (Fin 1 → R)} {A : Set (Fin k → R)}
    (hf : ContinuousOn f A) : ContinuousOn (-f) A := by
  rw [continuousOn_fin_one_iff] at hf ⊢
  intro x hx r hr
  obtain ⟨δ, hδ, h⟩ := hf x hx r hr
  refine ⟨δ, hδ, fun y hyA hyd => ?_⟩
  have hexp : (-f) y 0 - (-f) x 0 = -(f y 0 - f x 0) := by simp only [Pi.neg_apply]; ring
  rw [hexp, abs_neg]
  exact h y hyA hyd

theorem ContinuousOn.fin_one_add {k : ℕ} {f g : (Fin k → R) → (Fin 1 → R)} {A : Set (Fin k → R)}
    (hf : ContinuousOn f A) (hg : ContinuousOn g A) : ContinuousOn (f + g) A := by
  rw [continuousOn_fin_one_iff] at hf hg ⊢
  intro x hx r hr
  obtain ⟨δ1, hδ1, h1⟩ := hf x hx (r / 2) (by linarith)
  obtain ⟨δ2, hδ2, h2⟩ := hg x hx (r / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hyA hyd => ?_⟩
  have b1 := h1 y hyA (lt_of_lt_of_le hyd (min_le_left _ _))
  have b2 := h2 y hyA (lt_of_lt_of_le hyd (min_le_right _ _))
  have hexp : (f + g) y 0 - (f + g) x 0 = (f y 0 - f x 0) + (g y 0 - g x 0) := by
    simp only [Pi.add_apply]; ring
  rw [hexp]
  calc |(f y 0 - f x 0) + (g y 0 - g x 0)| ≤ |f y 0 - f x 0| + |g y 0 - g x 0| := abs_add_le _ _
    _ < r := by linarith

theorem ContinuousOn.fin_one_mul {k : ℕ} {f g : (Fin k → R) → (Fin 1 → R)} {A : Set (Fin k → R)}
    (hf : ContinuousOn f A) (hg : ContinuousOn g A) : ContinuousOn (f * g) A := by
  rw [continuousOn_fin_one_iff] at hf hg ⊢
  intro x hx r hr
  obtain ⟨δ0, hδ0, hf0⟩ := hf x hx 1 one_pos
  obtain ⟨δ1, hδ1, hf1⟩ := hf x hx (r / (2 * (|g x 0| + 1))) (by positivity)
  obtain ⟨δ2, hδ2, hg2⟩ := hg x hx (r / (2 * (|f x 0| + 1))) (by positivity)
  refine ⟨min δ0 (min δ1 δ2), lt_min hδ0 (lt_min hδ1 hδ2), fun y hyA hyd => ?_⟩
  have b0 : |f y 0 - f x 0| < 1 := hf0 y hyA (lt_of_lt_of_le hyd (min_le_left _ _))
  have b1 : |g y 0 - g x 0| < r / (2 * (|f x 0| + 1)) :=
    hg2 y hyA (lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_right _ _)))
  have b2 : |f y 0 - f x 0| < r / (2 * (|g x 0| + 1)) :=
    hf1 y hyA (lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hfx1 : (0 : R) < |f x 0| + 1 := by positivity
  have hgx1 : (0 : R) < |g x 0| + 1 := by positivity
  have hfy : |f y 0| < |f x 0| + 1 := by
    calc |f y 0| = |f x 0 + (f y 0 - f x 0)| := by ring_nf
      _ ≤ |f x 0| + |f y 0 - f x 0| := abs_add_le _ _
      _ < |f x 0| + 1 := by linarith
  have key : |(f * g) y 0 - (f * g) x 0| ≤
      |f y 0| * |g y 0 - g x 0| + |f y 0 - f x 0| * |g x 0| := by
    have hexp : (f * g) y 0 - (f * g) x 0 =
        f y 0 * (g y 0 - g x 0) + (f y 0 - f x 0) * g x 0 := by simp only [Pi.mul_apply]; ring
    rw [hexp]
    calc |f y 0 * (g y 0 - g x 0) + (f y 0 - f x 0) * g x 0|
        ≤ |f y 0 * (g y 0 - g x 0)| + |(f y 0 - f x 0) * g x 0| := abs_add_le _ _
      _ = |f y 0| * |g y 0 - g x 0| + |f y 0 - f x 0| * |g x 0| := by rw [abs_mul, abs_mul]
  have e1 : (|f x 0| + 1) * (r / (2 * (|f x 0| + 1))) = r / 2 := by field_simp
  have e2 : (r / (2 * (|g x 0| + 1))) * (|g x 0| + 1) = r / 2 := by field_simp
  have t1 : |f y 0| * |g y 0 - g x 0| < r / 2 := by
    rw [← e1]; exact mul_lt_mul' hfy.le b1 (abs_nonneg _) hfx1
  have t2 : |f y 0 - f x 0| * |g x 0| < r / 2 := by
    calc |f y 0 - f x 0| * |g x 0| ≤ |f y 0 - f x 0| * (|g x 0| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < (r / (2 * (|g x 0| + 1))) * (|g x 0| + 1) := mul_lt_mul_of_pos_right b2 hgx1
      _ = r / 2 := e2
  linarith [key, t1, t2]

/-! ### The ring of continuous semialgebraic functions `A → R` -/

/-- **BPR Proposition 3.3 (ring).** For a semialgebraic set `A ⊆ R^k`, the semialgebraic continuous
functions `A → R` form a ring. -/
def continuousSemialgebraicFunctions {k : ℕ} {A : Set (Fin k → R)} (hA : IsSemialgebraicSet A) :
    Subring ((Fin k → R) → (Fin 1 → R)) where
  carrier := {f | IsSemialgebraicFunction A f ∧ ContinuousOn f A}
  zero_mem' := ⟨isSemialgebraicFunction_zero hA, continuousOn_const⟩
  one_mem' := ⟨isSemialgebraicFunction_one hA, continuousOn_const⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, ContinuousOn.fin_one_add hf.2 hg.2⟩
  mul_mem' hf hg := ⟨hf.1.mul hg.1, ContinuousOn.fin_one_mul hf.2 hg.2⟩
  neg_mem' hf := ⟨hf.1.neg, ContinuousOn.fin_one_neg hf.2⟩

end Azurite.BPR
