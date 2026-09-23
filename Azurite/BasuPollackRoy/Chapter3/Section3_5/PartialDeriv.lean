/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_22

/-! # BPR §3.5 — partial derivatives of multivariate semialgebraic functions

**Partial derivatives of multivariate semialgebraic functions are defined in the usual way**:
for `c : R^k → R`, the `i`-th partial derivative at `x` is the derivative of the one-variable
slice `t ↦ c(x with the i-th coordinate replaced by t)` at `x i`, within the slice of the
domain (`HasPartialDerivAtIn`). On an open domain the slice admits an interval around `x i`,
so partial derivatives are unique (`HasPartialDerivAtIn.unique`).

**These partial derivatives are clearly semialgebraic functions**
(`isSemialgebraicFunction_partialDeriv`): as in Proposition 3.22, the graph of `∂c/∂X_i` is
described by a formula in the language of ordered fields with parameters in `R` — membership
in the graph of `c` at the slice point together with the squared difference-quotient
condition — and Corollary 2.78 (in its set-level Boolean/projection form) applies. Note that
only the *existence* of the partial derivative is needed for its semialgebraicity; the
continuity hypothesis in BPR's text sets up the `C¹` notions that follow. For a map
`f : U → R^p` the statement applies to each coordinate function separately. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### The definition, and uniqueness on open domains -/

/-- **The `i`-th partial derivative** of `c : R^k → R` at `x`, within `U` (BPR §3.5,
"defined in the usual way"): the one-variable function `t ↦ c (x[i := t])` has derivative `d`
at `x i`, within the slice `{t | x[i := t] ∈ U}` of the domain. -/
def HasPartialDerivAtIn {k : ℕ} (c : (Fin k → R) → R) (U : Set (Fin k → R)) (i : Fin k)
    (x : Fin k → R) (d : R) : Prop :=
  HasDerivAtIn (fun t => c (Function.update x i t))
    {t : R | Function.update x i t ∈ U} (x i) d

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The displacement `x[i := t] − x` is supported on the `i`-th coordinate. -/
theorem euclideanNormSq_update_sub {k : ℕ} (x : Fin k → R) (i : Fin k) (t : R) :
    euclideanNormSq (Function.update x i t - x) = (t - x i) ^ 2 := by
  rw [euclideanNormSq, Finset.sum_eq_single i]
  · rw [Pi.sub_apply, Function.update_self]
  · intro j _ hj
    rw [Pi.sub_apply, Function.update_of_ne hj, sub_self]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- On an open domain, the slice through `x ∈ U` in direction `i` clusters at `x i`. -/
theorem accPt'_slice {k : ℕ} {U : Set (Fin k → R)} (hUopen : IsOpen U) {x : Fin k → R}
    (hx : x ∈ U) (i : Fin k) : AccPt' {t : R | Function.update x i t ∈ U} (x i) := by
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff_ball_self.mp hUopen x hx
  intro δ hδ
  have h1 : 0 < min (δ / 2) (ρ / 2) := lt_min (by linarith) (by linarith)
  refine ⟨x i + min (δ / 2) (ρ / 2), ?_, ne_of_gt (by linarith), ?_⟩
  · show Function.update x i (x i + min (δ / 2) (ρ / 2)) ∈ U
    refine hball ?_
    rw [mem_openBall, euclideanNormSq_update_sub, add_sub_cancel_left]
    have h2 := min_le_right (δ / 2) (ρ / 2)
    nlinarith
  · rw [add_sub_cancel_left, abs_of_pos h1]
    have h2 := min_le_left (δ / 2) (ρ / 2)
    linarith

/-- **Partial derivatives on an open domain are unique.** -/
theorem HasPartialDerivAtIn.unique {k : ℕ} {c : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d₀ d₁ : R} (hUopen : IsOpen U) (hx : x ∈ U)
    (h₀ : HasPartialDerivAtIn c U i x d₀) (h₁ : HasPartialDerivAtIn c U i x d₁) : d₀ = d₁ :=
  HasDerivAtIn.unique (accPt'_slice hUopen hx i) h₀ h₁

/-! ### Partial derivatives of semialgebraic functions are semialgebraic -/

/-- **BPR §3.5 (unnumbered).** Partial derivatives of multivariate semialgebraic functions
are semialgebraic: if `c : R^k → R` is semialgebraic on the semialgebraic open set `U` and
its `i`-th partial derivative exists on `U` with value `g x` at `x`, then `g` is a
semialgebraic function on `U`. (As in Proposition 3.22, only existence is needed — and the
semialgebraicity of `U` itself is not needed either, since the formula only consults the
graph of `c`; for a map `f : U → R^p`, apply to each coordinate function.) -/
theorem isSemialgebraicFunction_partialDeriv {k : ℕ} {U : Set (Fin k → R)}
    {c g : (Fin k → R) → R} {i : Fin k} (hUopen : IsOpen U)
    (hSc : IsSemialgebraicFunction U (scalarFun c))
    (hdiff : ∀ x ∈ U, HasPartialDerivAtIn c U i x (g x)) :
    IsSemialgebraicFunction U (scalarFun g) := by
  classical
  -- membership in the graph of a scalar function, value-wise
  have hmemGraph : ∀ (c' : (Fin k → R) → R) (w : Fin (k + 1) → R),
      w ∈ funGraph U (scalarFun c')
        ↔ (w ∘ Fin.castAdd 1 ∈ U) ∧ w (Fin.natAdd k 0) = c' (w ∘ Fin.castAdd 1) := by
    intro c' w
    rw [mem_funGraph]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, congrFun h2 0⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun j => ?_⟩
      rw [Fin.eq_zero j]
      exact h2
  set G : Set (Fin (k + 1) → R) := funGraph U (scalarFun c) with hGd
  have hG : IsSemialgebraicSet G := hSc
  /- Working coordinates, by blocks: `z = (x, d) : Fin (k+1)` (graph layout: the `x`-block at
     `castAdd 1`, `d` last), then `y_x`, `r`, `δ` (one each), then `(t, y_t) : Fin 2`. -/
  set tIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.natAdd ((((k + 1) + 1) + 1) + 1) 0 with htIdxd
  set ytIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.natAdd ((((k + 1) + 1) + 1) + 1) 1 with hytIdxd
  set xIdx : Fin k → Fin (((((k + 1) + 1) + 1) + 1) + 2) := fun j =>
    Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 j))))
    with hxIdxd
  set dIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd k 0))))
    with hdIdxd
  set yxIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd (k + 1) 0))) with hyxIdxd
  set rIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.castAdd 2 (Fin.castAdd 1 (Fin.natAdd ((k + 1) + 1) 0)) with hrIdxd
  set δIdx : Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.castAdd 2 (Fin.natAdd (((k + 1) + 1) + 1) 0) with hδIdxd
  -- the slice-point index map: the `(k+1)`-tuple `(x[i := t], y_t)`
  set σ : Fin (k + 1) → Fin (((((k + 1) + 1) + 1) + 1) + 2) :=
    Fin.append (fun j : Fin k => if j = i then tIdx else xIdx j) (fun _ : Fin 1 => ytIdx)
    with hσd
  -- the innermost implication, over the full space
  set GS : Set (Fin (((((k + 1) + 1) + 1) + 1) + 2) → R) := {w | w ∘ σ ∈ G} with hGSd
  have hGS : IsSemialgebraicSet GS := IsSemialgebraicSet.comap _ hG
  set NE : Set (Fin (((((k + 1) + 1) + 1) + 1) + 2) → R) :=
    {w | eval w ((X tIdx - X (xIdx i)) ^ 2) > 0} with hNEd
  have hNE : IsSemialgebraicSet NE := IsSemialgebraicSet.gtZero _
  set NEAR : Set (Fin (((((k + 1) + 1) + 1) + 1) + 2) → R) :=
    {w | eval w ((X tIdx - X (xIdx i)) ^ 2 - (X δIdx) ^ 2) < 0} with hNEARd
  have hNEAR : IsSemialgebraicSet NEAR := IsSemialgebraicSet.ltZero _
  set TARGET : Set (Fin (((((k + 1) + 1) + 1) + 1) + 2) → R) :=
    {w | eval w (((X ytIdx - X yxIdx) - X dIdx * (X tIdx - X (xIdx i))) ^ 2
      - (X rIdx) ^ 2 * (X tIdx - X (xIdx i)) ^ 2) < 0} with hTARGETd
  have hTARGET : IsSemialgebraicSet TARGET := IsSemialgebraicSet.ltZero _
  set A : Set (Fin (((((k + 1) + 1) + 1) + 1) + 2) → R) :=
    (GS ∩ NE ∩ NEAR)ᶜ ∪ TARGET with hAd
  have hA : IsSemialgebraicSet A := (((hGS.inter hNE).inter hNEAR).compl).union hTARGET
  -- `∀ (t, y_t)`
  set B : Set (Fin ((((k + 1) + 1) + 1) + 1) → R) :=
    {w | ∀ ty : Fin 2 → R, Fin.append w ty ∈ A} with hBd
  have hB : IsSemialgebraicSet B := by
    have heq : B = {w : Fin ((((k + 1) + 1) + 1) + 1) → R |
        ∃ ty : Fin 2 → R, Fin.append w ty ∈ Aᶜ}ᶜ := by
      ext w
      simp only [hBd, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
    rw [heq]
    exact (IsSemialgebraicSet.exists_append_right hA.compl).compl
  -- `∃ δ > 0`
  set DPOS : Set (Fin ((((k + 1) + 1) + 1) + 1) → R) :=
    {w | eval w (X (Fin.natAdd (((k + 1) + 1) + 1) 0) :
      MvPolynomial (Fin ((((k + 1) + 1) + 1) + 1)) R) > 0} with hDPOSd
  have hDPOS : IsSemialgebraicSet DPOS := IsSemialgebraicSet.gtZero _
  set C : Set (Fin (((k + 1) + 1) + 1) → R) :=
    {w | ∃ dv : Fin 1 → R, Fin.append w dv ∈ DPOS ∩ B} with hCd
  have hC : IsSemialgebraicSet C := IsSemialgebraicSet.exists_append_right (hDPOS.inter hB)
  -- `∀ r (r > 0 → ⋯)`
  set RPOS : Set (Fin (((k + 1) + 1) + 1) → R) :=
    {w | eval w (X (Fin.natAdd ((k + 1) + 1) 0) :
      MvPolynomial (Fin (((k + 1) + 1) + 1)) R) > 0} with hRPOSd
  have hRPOS : IsSemialgebraicSet RPOS := IsSemialgebraicSet.gtZero _
  set DD : Set (Fin ((k + 1) + 1) → R) :=
    {w | ∀ rv : Fin 1 → R, Fin.append w rv ∈ RPOSᶜ ∪ C} with hDDd
  have hDD : IsSemialgebraicSet DD := by
    have heq : DD = {w : Fin ((k + 1) + 1) → R | ∃ rv : Fin 1 → R,
        Fin.append w rv ∈ (RPOSᶜ ∪ C)ᶜ}ᶜ := by
      ext w
      simp only [hDDd, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
    rw [heq]
    exact (IsSemialgebraicSet.exists_append_right (hRPOS.compl.union hC).compl).compl
  -- `∃ y_x ((x, y_x) ∈ G ∧ ⋯)`
  set τ : Fin (k + 1) → Fin ((k + 1) + 1) :=
    Fin.append (fun j : Fin k => Fin.castAdd 1 (Fin.castAdd 1 j))
      (fun _ : Fin 1 => Fin.natAdd (k + 1) 0) with hτd
  set GX : Set (Fin ((k + 1) + 1) → R) := {w | w ∘ τ ∈ G} with hGXd
  have hGX : IsSemialgebraicSet GX := IsSemialgebraicSet.comap _ hG
  set E : Set (Fin (k + 1) → R) :=
    {w | ∃ yv : Fin 1 → R, Fin.append w yv ∈ GX ∩ DD} with hEd
  have hE : IsSemialgebraicSet E := IsSemialgebraicSet.exists_append_right (hGX.inter hDD)
  -- ## Membership characterizations
  -- coordinates of the quadruple append (all by `Fin.append_left/right`)
  have hcoX : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R) (j : Fin k),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty (xIdx j)
        = z (Fin.castAdd 1 j) := by
    intro z yv rv dv ty j
    simp only [hxIdxd, Fin.append_left]
  have hcoD : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty dIdx
        = z (Fin.natAdd k 0) := by
    intro z yv rv dv ty
    simp only [hdIdxd, Fin.append_left]
  have hcoYX : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty yxIdx = yv 0 := by
    intro z yv rv dv ty
    simp only [hyxIdxd, Fin.append_left, Fin.append_right]
  have hcoR : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty rIdx = rv 0 := by
    intro z yv rv dv ty
    simp only [hrIdxd, Fin.append_left, Fin.append_right]
  have hcoδ : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty δIdx = dv 0 := by
    intro z yv rv dv ty
    simp only [hδIdxd, Fin.append_left, Fin.append_right]
  have hcoT : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty tIdx = ty 0 := by
    intro z yv rv dv ty
    simp only [htIdxd, Fin.append_right]
  have hcoYT : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ytIdx = ty 1 := by
    intro z yv rv dv ty
    simp only [hytIdxd, Fin.append_right]
  -- the slice point read off through `σ`
  have hσcast : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∘ σ)
          ∘ Fin.castAdd 1
        = Function.update (z ∘ Fin.castAdd 1) i (ty 0) := by
    intro z yv rv dv ty
    funext j
    show Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        (σ (Fin.castAdd 1 j)) = _
    rw [hσd, Fin.append_left]
    by_cases hj : j = i
    · rw [ite_eq_left hj, hcoT, hj, Function.update_self]
    · rw [ite_eq_right hj, hcoX, Function.update_of_ne hj]
      rfl
  have hσnat : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∘ σ)
          (Fin.natAdd k 0)
        = ty 1 := by
    intro z yv rv dv ty
    show Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        (σ (Fin.natAdd k 0)) = _
    rw [hσd, Fin.append_right]
    exact hcoYT z yv rv dv ty
  -- the inner implication, for the quadruple append
  have hmemA : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ A) ↔
        (((Function.update (z ∘ Fin.castAdd 1) i (ty 0) ∈ U ∧
            ty 1 = c (Function.update (z ∘ Fin.castAdd 1) i (ty 0))) ∧
          ty 0 ≠ z (Fin.castAdd 1 i) ∧
          (ty 0 - z (Fin.castAdd 1 i)) ^ 2 < dv 0 ^ 2) →
          ((ty 1 - yv 0) - z (Fin.natAdd k 0) * (ty 0 - z (Fin.castAdd 1 i))) ^ 2
            < rv 0 ^ 2 * (ty 0 - z (Fin.castAdd 1 i)) ^ 2) := by
    intro z yv rv dv ty
    have hGSm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ GS)
        ↔ (Function.update (z ∘ Fin.castAdd 1) i (ty 0) ∈ U ∧
            ty 1 = c (Function.update (z ∘ Fin.castAdd 1) i (ty 0))) := by
      rw [hGSd, Set.mem_ofPred_eq, hGd, hmemGraph c, hσcast, hσnat]
    have hNEm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ NE)
        ↔ ty 0 ≠ z (Fin.castAdd 1 i) := by
      rw [hNEd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, eval_X]
      rw [hcoT, hcoX]
      exact sq_pos_iff_ne.trans sub_ne_zero
    have hNEARm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ NEAR)
        ↔ (ty 0 - z (Fin.castAdd 1 i)) ^ 2 < dv 0 ^ 2 := by
      rw [hNEARd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, eval_X]
      rw [hcoT, hcoX, hcoδ]
      exact sub_neg
    have hTARGETm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        ∈ TARGET)
        ↔ ((ty 1 - yv 0) - z (Fin.natAdd k 0) * (ty 0 - z (Fin.castAdd 1 i))) ^ 2
            < rv 0 ^ 2 * (ty 0 - z (Fin.castAdd 1 i)) ^ 2 := by
      rw [hTARGETd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, map_mul, eval_X]
      rw [hcoT, hcoX, hcoD, hcoYX, hcoYT, hcoR]
      exact sub_neg
    rw [hAd, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      hGSm, hNEm, hNEARm, hTARGETm]
    exact compl_or_iff_imp
  -- the `∃ δ` layer
  have hmemDB : ∀ (z : Fin (k + 1) → R) (yv rv dv : Fin 1 → R),
      (Fin.append (Fin.append (Fin.append z yv) rv) dv ∈ DPOS ∩ B) ↔
        (0 < dv 0 ∧ ∀ t yt : R,
          ((Function.update (z ∘ Fin.castAdd 1) i t ∈ U ∧
              yt = c (Function.update (z ∘ Fin.castAdd 1) i t)) ∧
            t ≠ z (Fin.castAdd 1 i) ∧ (t - z (Fin.castAdd 1 i)) ^ 2 < dv 0 ^ 2) →
            ((yt - yv 0) - z (Fin.natAdd k 0) * (t - z (Fin.castAdd 1 i))) ^ 2
              < rv 0 ^ 2 * (t - z (Fin.castAdd 1 i)) ^ 2) := by
    intro z yv rv dv
    rw [Set.mem_inter_iff]
    have hd4 : Fin.append (Fin.append (Fin.append z yv) rv) dv
        (Fin.natAdd (((k + 1) + 1) + 1) 0) = dv 0 := Fin.append_right _ _ _
    have hDPm : (Fin.append (Fin.append (Fin.append z yv) rv) dv ∈ DPOS) ↔ 0 < dv 0 := by
      rw [hDPOSd, Set.mem_ofPred_eq, eval_X, hd4]
    rw [hDPm, hBd, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h t yt
      exact (hmemA z yv rv dv ![t, yt]).mp (h ![t, yt])
    · intro h ty
      rw [hmemA z yv rv dv ty]
      exact h (ty 0) (ty 1)
  -- the described set is exactly the graph of `g`
  suffices hgoal : funGraph U (scalarFun g) = E by
    show IsSemialgebraicSet _
    rw [hgoal]
    exact hE
  ext z
  rw [hmemGraph g]
  -- `GX` membership for the witness append
  have hGXm : ∀ yv : Fin 1 → R, (Fin.append z yv ∈ GX)
      ↔ ((z ∘ Fin.castAdd 1 ∈ U) ∧ yv 0 = c (z ∘ Fin.castAdd 1)) := by
    intro yv
    have hτcast : (Fin.append z yv ∘ τ) ∘ Fin.castAdd 1 = z ∘ Fin.castAdd 1 := by
      funext j
      show Fin.append z yv (τ (Fin.castAdd 1 j)) = _
      rw [hτd, Fin.append_left, Fin.append_left]
      rfl
    have hτnat : (Fin.append z yv ∘ τ) (Fin.natAdd k 0) = yv 0 := by
      show Fin.append z yv (τ (Fin.natAdd k 0)) = _
      rw [hτd, Fin.append_right, Fin.append_right]
    rw [hGXd, Set.mem_ofPred_eq, hGd, hmemGraph c, hτcast, hτnat]
  -- `RPOS` membership for the `r` append
  have hRPm : ∀ (yv rv : Fin 1 → R),
      (Fin.append (Fin.append z yv) rv ∈ RPOS) ↔ 0 < rv 0 := by
    intro yv rv
    have hr3 : Fin.append (Fin.append z yv) rv (Fin.natAdd ((k + 1) + 1) 0) = rv 0 :=
      Fin.append_right _ _ _
    rw [hRPOSd, Set.mem_ofPred_eq, eval_X, hr3]
  constructor
  · -- graph of `∂c/∂X_i` ⊆ described set
    rintro ⟨hx, hd⟩
    rw [hEd, Set.mem_ofPred_eq]
    refine ⟨fun _ => c (z ∘ Fin.castAdd 1),
      Set.mem_inter ((hGXm _).mpr ⟨hx, rfl⟩) ?_⟩
    rw [hDDd, Set.mem_ofPred_eq]
    intro rv
    rw [Set.mem_union, Set.mem_compl_iff, hRPm]
    by_cases hr : 0 < rv 0
    · right
      obtain ⟨δ, hδ, hball⟩ := hdiff (z ∘ Fin.castAdd 1) hx (rv 0) hr
      rw [hCd, Set.mem_ofPred_eq]
      refine ⟨fun _ => δ, (hmemDB z _ rv _).mpr ⟨hδ, fun t yt hprem => ?_⟩⟩
      obtain ⟨⟨htdom, htval⟩, htne, htδ⟩ := hprem
      have htδ' : |t - z (Fin.castAdd 1 i)| < δ := (abs_lt_iff_sq_lt_sq hδ).mpr htδ
      have hq := hball t htdom htne htδ'
      have hslice : c (Function.update (z ∘ Fin.castAdd 1) i ((z ∘ Fin.castAdd 1) i))
          = c (z ∘ Fin.castAdd 1) := by
        rw [Function.update_eq_self]
      have hq' : |(yt - c (z ∘ Fin.castAdd 1)) / (t - z (Fin.castAdd 1 i))
          - z (Fin.natAdd k 0)| < rv 0 := by
        rw [htval, hd]
        have : (z ∘ Fin.castAdd 1) i = z (Fin.castAdd 1 i) := rfl
        rw [← this]
        rw [← hslice]
        exact hq
      exact (quot_sq_iff (sub_ne_zero.mpr htne) hr).mp hq'
    · left
      exact hr
  · -- described set ⊆ graph of `∂c/∂X_i`
    intro hzE
    rw [hEd, Set.mem_ofPred_eq] at hzE
    obtain ⟨yv, hyvGX, hyvDD⟩ := hzE
    rw [hGXm] at hyvGX
    obtain ⟨hx, hyx⟩ := hyvGX
    -- the condition says `z (natAdd k 0)` is the `i`-th partial derivative at `x`
    have hderiv : HasPartialDerivAtIn c U i (z ∘ Fin.castAdd 1) (z (Fin.natAdd k 0)) := by
      intro r hr
      rw [hDDd, Set.mem_ofPred_eq] at hyvDD
      have hmem := hyvDD (fun _ => r)
      rw [Set.mem_union, Set.mem_compl_iff, hRPm] at hmem
      rcases hmem with hcon | hCm
      · exact absurd hr hcon
      · rw [hCd, Set.mem_ofPred_eq] at hCm
        obtain ⟨dv, hdv⟩ := hCm
        rw [hmemDB z yv (fun _ => r) dv] at hdv
        obtain ⟨hδ, hall⟩ := hdv
        refine ⟨dv 0, hδ, fun t htM htne htδ => ?_⟩
        have htne' : t ≠ z (Fin.castAdd 1 i) := htne
        have happ := hall t (c (Function.update (z ∘ Fin.castAdd 1) i t))
          ⟨⟨htM, rfl⟩, htne', (abs_lt_iff_sq_lt_sq hδ).mp htδ⟩
        rw [hyx] at happ
        have hslice : c (Function.update (z ∘ Fin.castAdd 1) i ((z ∘ Fin.castAdd 1) i))
            = c (z ∘ Fin.castAdd 1) := by
          rw [Function.update_eq_self]
        have hq := (quot_sq_iff (sub_ne_zero.mpr htne') hr).mpr happ
        rw [← hslice] at hq
        exact hq
    have hd : z (Fin.natAdd k 0) = g (z ∘ Fin.castAdd 1) :=
      hderiv.unique hUopen hx (hdiff (z ∘ Fin.castAdd 1) hx)
    exact ⟨hx, hd⟩

end Azurite.BPR
