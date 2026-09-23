/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.Derivative
import Azurite.BasuPollackRoy.Chapter3.Section3_5.ExtremeValue

/-! # BPR §3.5, Proposition 3.22 — the derivative is semialgebraic

**Let `f : (a, b) → R` be a semialgebraic function differentiable on the interval `(a, b)`.
Then its derivative `f′` is a semialgebraic function.**

Following BPR's proof, the graph of `f′` is described by a formula in the language of ordered
fields with parameters in `R`: `(x, d)` lies in the graph iff there is `y_x` with
`(x, y_x) ∈ G` (the graph of `f`, a semialgebraic set) such that for all `r > 0` there is
`δ > 0` such that for all `(t, y_t) ∈ G` with `0 < (t − x)² < δ²`,
`((y_t − y_x) − d(t − x))² < r²(t − x)²` — the difference-quotient condition with the division
and the absolute values cleared into polynomial sign conditions. Corollary 2.78 (here in its
set-level form: semialgebraic sets are closed under Boolean operations and coordinate
projection, `IsSemialgebraicSet.exists_append_right`, exactly as in Proposition 3.1) then
shows the graph is semialgebraic; uniqueness of derivatives (`HasDerivAtIn.unique`) pins the
described value to `f′(x)`. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### `Fin 1` and square-inequality helpers -/

omit [Field R] [IsRealClosed R] in
/-- Membership in the open segment `(constPt a, constPt b) ⊆ R¹`. -/
theorem mem_Ioo_fin_one {a b : R} {y : Fin 1 → R} :
    y ∈ Set.Ioo (constPt a) (constPt b) ↔ a < y 0 ∧ y 0 < b := by
  rw [Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨-, i, hi⟩ := Pi.lt_def.mp h1
    obtain ⟨-, j, hj⟩ := Pi.lt_def.mp h2
    rw [Fin.eq_zero i] at hi
    rw [Fin.eq_zero j] at hj
    exact ⟨hi, hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Pi.lt_def.mpr ⟨fun i => by rw [Fin.eq_zero i]; exact h1.le, 0, h1⟩,
      Pi.lt_def.mpr ⟨fun i => by rw [Fin.eq_zero i]; exact h2.le, 0, h2⟩⟩

omit [IsRealClosed R] in
theorem sq_pos_iff_ne {u : R} : 0 < u ^ 2 ↔ u ≠ 0 :=
  ⟨fun h he => by rw [he] at h; simp at h, fun h => by positivity⟩

omit [IsRealClosed R] in
theorem abs_lt_iff_sq_lt_sq {w r : R} (hr : 0 < r) : |w| < r ↔ w ^ 2 < r ^ 2 := by
  constructor
  · intro h
    nlinarith [sq_abs w, abs_nonneg w]
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [sq_abs w, abs_nonneg w]

omit [IsRealClosed R] in
/-- The difference-quotient inequality `|(u − v)/s − d| < r`, with the division and the
absolute value cleared into a polynomial inequality (for `s ≠ 0`, `r > 0`). -/
theorem quot_sq_iff {u v d s r : R} (hs : s ≠ 0) (hr : 0 < r) :
    |(u - v) / s - d| < r ↔ ((u - v) - d * s) ^ 2 < r ^ 2 * s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hq : (u - v) - d * s = ((u - v) / s - d) * s := by field_simp
  rw [abs_lt_iff_sq_lt_sq hr, hq, mul_pow]
  constructor
  · intro h
    exact mul_lt_mul_of_pos_right h hs2
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h (not_lt.mpr (mul_le_mul_of_nonneg_right hcon hs2.le))

theorem compl_or_iff_imp {P Q S T : Prop} :
    (¬((P ∧ Q) ∧ S) ∨ T) ↔ ((P ∧ Q ∧ S) → T) := by
  constructor
  · rintro (hn | ht) ⟨hP, hQ, hS⟩
    · exact absurd ⟨⟨hP, hQ⟩, hS⟩ hn
    · exact ht
  · intro h
    rcases Classical.em ((P ∧ Q) ∧ S) with hp | hn
    · exact Or.inr (h ⟨hp.1.1, hp.1.2, hp.2⟩)
    · exact Or.inl hn

/-! ### Proposition 3.22 -/

/-- **BPR Proposition 3.22.** Let `f : (a, b) → R` be a semialgebraic function differentiable
on the interval `(a, b)`. Then its derivative `f′` is a semialgebraic function. -/
theorem proposition_3_22 {f : (Fin 1 → R) → (Fin 1 → R)} {f' : R → R} {a b : R}
    (hSf : IsSemialgebraicFunction (Set.Ioo (constPt a) (constPt b)) f)
    (hdiff : ∀ x, a < x → x < b →
      HasDerivAtIn (fun t => f (constPt t) 0) (Set.Ioo a b) x (f' x)) :
    IsSemialgebraicFunction (Set.Ioo (constPt a) (constPt b))
      (scalarFun (fun y => f' (y 0))) := by
  classical
  set g : R → R := fun t => f (constPt t) 0 with hgd
  set G : Set (Fin (1 + 1) → R) := funGraph (Set.Ioo (constPt a) (constPt b)) f with hGd
  have hG : IsSemialgebraicSet G := hSf
  -- membership in the graph of `f`, coordinatewise
  have hmemG : ∀ w : Fin (1 + 1) → R, w ∈ G ↔ (a < w 0 ∧ w 0 < b) ∧ w 1 = g (w 0) := by
    intro w
    rw [hGd, mem_funGraph]
    have hcast : w ∘ Fin.castAdd 1 = constPt (w 0) :=
      funext fun i => by rw [Fin.eq_zero i]; rfl
    rw [hcast, mem_Ioo_fin_one]
    constructor
    · rintro ⟨hdom, hval⟩
      exact ⟨hdom, congrFun hval 0⟩
    · rintro ⟨hdom, hval⟩
      refine ⟨hdom, funext fun i => ?_⟩
      rw [Fin.eq_zero i]
      exact hval
  /- Coordinates of the ambient spaces (flat indexing):
     `0 = x`, `1 = d`, `2 = y_x`, `3 = r`, `4 = δ`, `5 = t`, `6 = y_t`. -/
  -- the innermost implication, over `R⁷`
  set GT : Set (Fin (5 + 2) → R) := {w | w ∘ ![(5 : Fin 7), 6] ∈ G} with hGTd
  have hGT : IsSemialgebraicSet GT := IsSemialgebraicSet.comap _ hG
  set NE : Set (Fin (5 + 2) → R) := {w | eval w ((X 5 - X 0) ^ 2) > 0} with hNEd
  have hNE : IsSemialgebraicSet NE := IsSemialgebraicSet.gtZero _
  set NEAR : Set (Fin (5 + 2) → R) :=
    {w | eval w ((X 5 - X 0) ^ 2 - (X 4) ^ 2) < 0} with hNEARd
  have hNEAR : IsSemialgebraicSet NEAR := IsSemialgebraicSet.ltZero _
  set TARGET : Set (Fin (5 + 2) → R) :=
    {w | eval w (((X 6 - X 2) - X 1 * (X 5 - X 0)) ^ 2 - (X 3) ^ 2 * (X 5 - X 0) ^ 2) < 0}
    with hTARGETd
  have hTARGET : IsSemialgebraicSet TARGET := IsSemialgebraicSet.ltZero _
  set A : Set (Fin (5 + 2) → R) := (GT ∩ NE ∩ NEAR)ᶜ ∪ TARGET with hAd
  have hA : IsSemialgebraicSet A := (((hGT.inter hNE).inter hNEAR).compl).union hTARGET
  -- `∀ (t, y_t)` : complement of the projection of the complement
  set B : Set (Fin (4 + 1) → R) :=
    {w | ∀ ty : Fin 2 → R, Fin.append w ty ∈ A} with hBd
  have hB : IsSemialgebraicSet B := by
    have heq : B = {w : Fin 5 → R | ∃ ty : Fin 2 → R, Fin.append w ty ∈ Aᶜ}ᶜ := by
      ext w
      simp only [hBd, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
    rw [heq]
    exact (IsSemialgebraicSet.exists_append_right hA.compl).compl
  -- `∃ δ > 0`
  set DPOS : Set (Fin (4 + 1) → R) := {w | eval w (X 4 : MvPolynomial (Fin 5) R) > 0}
    with hDPOSd
  have hDPOS : IsSemialgebraicSet DPOS := IsSemialgebraicSet.gtZero _
  set C : Set (Fin (3 + 1) → R) :=
    {w | ∃ dv : Fin 1 → R, Fin.append w dv ∈ DPOS ∩ B} with hCd
  have hC : IsSemialgebraicSet C := IsSemialgebraicSet.exists_append_right (hDPOS.inter hB)
  -- `∀ r (r > 0 → ⋯)`
  set RPOS : Set (Fin (3 + 1) → R) := {w | eval w (X 3 : MvPolynomial (Fin 4) R) > 0}
    with hRPOSd
  have hRPOS : IsSemialgebraicSet RPOS := IsSemialgebraicSet.gtZero _
  set DD : Set (Fin (2 + 1) → R) :=
    {w | ∀ rv : Fin 1 → R, Fin.append w rv ∈ RPOSᶜ ∪ C} with hDDd
  have hDD : IsSemialgebraicSet DD := by
    have heq : DD = {w : Fin 3 → R | ∃ rv : Fin 1 → R,
        Fin.append w rv ∈ (RPOSᶜ ∪ C)ᶜ}ᶜ := by
      ext w
      simp only [hDDd, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
    rw [heq]
    exact (IsSemialgebraicSet.exists_append_right (hRPOS.compl.union hC).compl).compl
  -- `∃ y_x ((x, y_x) ∈ G ∧ ⋯)`
  set GX : Set (Fin (2 + 1) → R) := {w | w ∘ ![(0 : Fin 3), 2] ∈ G} with hGXd
  have hGX : IsSemialgebraicSet GX := IsSemialgebraicSet.comap _ hG
  set E : Set (Fin (1 + 1) → R) :=
    {w | ∃ yv : Fin 1 → R, Fin.append w yv ∈ GX ∩ DD} with hEd
  have hE : IsSemialgebraicSet E := IsSemialgebraicSet.exists_append_right (hGX.inter hDD)
  -- ## Membership characterizations (all coordinate facts hold by `rfl`)
  -- the inner implication, for the quadruple append
  have hmemA : ∀ (z : Fin (1 + 1) → R) (yv rv dv : Fin 1 → R) (ty : Fin 2 → R),
      (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ A) ↔
        ((((a < ty 0 ∧ ty 0 < b) ∧ ty 1 = g (ty 0)) ∧ ty 0 ≠ z 0 ∧
            (ty 0 - z 0) ^ 2 < dv 0 ^ 2) →
          ((ty 1 - yv 0) - z 1 * (ty 0 - z 0)) ^ 2 < rv 0 ^ 2 * (ty 0 - z 0) ^ 2) := by
    intro z yv rv dv ty
    -- coordinates of the quadruple append (each holds by `rfl`)
    have b0 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 0 = z 0 := rfl
    have b1 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 1 = z 1 := rfl
    have b2 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 2 = yv 0 := rfl
    have b3 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 3 = rv 0 := rfl
    have b4 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 4 = dv 0 := rfl
    have b5 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 5 = ty 0 := rfl
    have b6 : Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty 6 = ty 1 := rfl
    have c0 : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        ∘ ![(5 : Fin 7), 6]) 0 = ty 0 := rfl
    have c1 : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        ∘ ![(5 : Fin 7), 6]) 1 = ty 1 := rfl
    have hGTm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ GT)
        ↔ ((a < ty 0 ∧ ty 0 < b) ∧ ty 1 = g (ty 0)) := by
      rw [hGTd, Set.mem_ofPred_eq, hmemG, c0, c1]
    have hNEm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ NE)
        ↔ ty 0 ≠ z 0 := by
      rw [hNEd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, eval_X]
      rw [b5, b0]
      exact sq_pos_iff_ne.trans sub_ne_zero
    have hNEARm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty ∈ NEAR)
        ↔ (ty 0 - z 0) ^ 2 < dv 0 ^ 2 := by
      rw [hNEARd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, eval_X]
      rw [b5, b0, b4]
      exact sub_neg
    have hTARGETm : (Fin.append (Fin.append (Fin.append (Fin.append z yv) rv) dv) ty
        ∈ TARGET)
        ↔ ((ty 1 - yv 0) - z 1 * (ty 0 - z 0)) ^ 2 < rv 0 ^ 2 * (ty 0 - z 0) ^ 2 := by
      rw [hTARGETd, Set.mem_ofPred_eq]
      simp only [map_sub, map_pow, map_mul, eval_X]
      rw [b5, b0, b1, b2, b3, b6]
      exact sub_neg
    rw [hAd, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      hGTm, hNEm, hNEARm, hTARGETm]
    exact compl_or_iff_imp
  -- the `∃ δ` layer
  have hmemDB : ∀ (z : Fin (1 + 1) → R) (yv rv dv : Fin 1 → R),
      (Fin.append (Fin.append (Fin.append z yv) rv) dv ∈ DPOS ∩ B) ↔
        (0 < dv 0 ∧ ∀ t yt : R,
          (((a < t ∧ t < b) ∧ yt = g t) ∧ t ≠ z 0 ∧ (t - z 0) ^ 2 < dv 0 ^ 2) →
            ((yt - yv 0) - z 1 * (t - z 0)) ^ 2 < rv 0 ^ 2 * (t - z 0) ^ 2) := by
    intro z yv rv dv
    rw [Set.mem_inter_iff]
    have d4 : Fin.append (Fin.append (Fin.append z yv) rv) dv 4 = dv 0 := rfl
    have hDPm : (Fin.append (Fin.append (Fin.append z yv) rv) dv ∈ DPOS) ↔ 0 < dv 0 := by
      rw [hDPOSd, Set.mem_ofPred_eq, eval_X, d4]
    rw [hDPm, hBd, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h t yt
      exact (hmemA z yv rv dv ![t, yt]).mp (h ![t, yt])
    · intro h ty
      rw [hmemA z yv rv dv ty]
      exact h (ty 0) (ty 1)
  -- the described set is exactly the graph of `f′`
  suffices hgoal : funGraph (Set.Ioo (constPt a) (constPt b))
      (scalarFun (fun y => f' (y 0))) = E by
    show IsSemialgebraicSet _
    rw [hgoal]
    exact hE
  ext z
  rw [mem_funGraph]
  have hcast : z ∘ Fin.castAdd 1 = constPt (z 0) :=
    funext fun i => by rw [Fin.eq_zero i]; rfl
  rw [hcast, mem_Ioo_fin_one]
  -- `GX` membership for the witness append
  have hGXm : ∀ yv : Fin 1 → R, (Fin.append z yv ∈ GX)
      ↔ ((a < z 0 ∧ z 0 < b) ∧ yv 0 = g (z 0)) := by
    intro yv
    have x0 : (Fin.append z yv ∘ ![(0 : Fin 3), 2]) 0 = z 0 := rfl
    have x1 : (Fin.append z yv ∘ ![(0 : Fin 3), 2]) 1 = yv 0 := rfl
    rw [hGXd, Set.mem_ofPred_eq, hmemG, x0, x1]
  -- `RPOS` membership for the `r` append
  have hRPm : ∀ (yv rv : Fin 1 → R),
      (Fin.append (Fin.append z yv) rv ∈ RPOS) ↔ 0 < rv 0 := by
    intro yv rv
    have r3 : Fin.append (Fin.append z yv) rv 3 = rv 0 := rfl
    rw [hRPOSd, Set.mem_ofPred_eq, eval_X, r3]
  constructor
  · -- graph of `f′` ⊆ described set
    rintro ⟨⟨hax, hxb⟩, hval⟩
    have hd : z 1 = f' (z 0) := congrFun hval 0
    rw [hEd, Set.mem_ofPred_eq]
    refine ⟨fun _ => g (z 0), Set.mem_inter ((hGXm _).mpr ⟨⟨hax, hxb⟩, rfl⟩) ?_⟩
    rw [hDDd, Set.mem_ofPred_eq]
    intro rv
    rw [Set.mem_union, Set.mem_compl_iff, hRPm]
    by_cases hr : 0 < rv 0
    · right
      obtain ⟨δ, hδ, hball⟩ := hdiff (z 0) hax hxb (rv 0) hr
      rw [hCd, Set.mem_ofPred_eq]
      refine ⟨fun _ => δ, (hmemDB z _ rv _).mpr ⟨hδ, fun t yt hprem => ?_⟩⟩
      obtain ⟨⟨htdom, htval⟩, htne, htδ⟩ := hprem
      have htδ' : |t - z 0| < δ := (abs_lt_iff_sq_lt_sq hδ).mpr htδ
      have hq : |(g t - g (z 0)) / (t - z 0) - z 1| < rv 0 := by
        rw [hd]
        exact hball t ⟨htdom.1, htdom.2⟩ htne htδ'
      rw [htval]
      exact (quot_sq_iff (sub_ne_zero.mpr htne) hr).mp hq
    · left
      exact hr
  · -- described set ⊆ graph of `f′`
    intro hzE
    rw [hEd, Set.mem_ofPred_eq] at hzE
    obtain ⟨yv, hyvGX, hyvDD⟩ := hzE
    rw [hGXm] at hyvGX
    obtain ⟨⟨hax, hxb⟩, hyx⟩ := hyvGX
    -- the condition says `z 1` is a derivative of `g` at `z 0`
    have hderiv : HasDerivAtIn g (Set.Ioo a b) (z 0) (z 1) := by
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
        have happ := hall t (g t)
          ⟨⟨⟨htM.1, htM.2⟩, rfl⟩, htne, (abs_lt_iff_sq_lt_sq hδ).mp htδ⟩
        rw [hyx] at happ
        exact (quot_sq_iff (sub_ne_zero.mpr htne) hr).mpr happ
    have hd : z 1 = f' (z 0) :=
      hderiv.unique (accPt'_Ioo hax hxb) (hdiff (z 0) hax hxb)
    refine ⟨⟨hax, hxb⟩, funext fun i => ?_⟩
    rw [Fin.eq_zero i]
    exact hd

end Azurite.BPR
