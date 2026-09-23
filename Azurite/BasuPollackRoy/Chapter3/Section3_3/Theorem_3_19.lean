/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_17
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Notation_3_15
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_1

/-! # BPR §3.3 — Theorem 3.19: the curve selection lemma

Let `S ⊆ Rᵏ` be semialgebraic and `x ∈ closure S`. Then there is a continuous semialgebraic map
`γ : [0, 1) → Rᵏ` with `γ(0) = x` and `γ((0, 1)) ⊆ S`.

The proof produces an infinitesimal curve germ. Since `x ∈ closure S`, the `R[ε]`-sentence
`∃ y, φ_S(y) ∧ ∑ᵢ(yᵢ − xᵢ)² < ε²` is, for every `t ∈ (0, 1)`, true over `R` (it says the ball
`B(x, t)` meets `S`), so by Proposition 3.17 it is true in `R⟨ε⟩`: there is a germ tuple
`ϕ ∈ Ext(S, R⟨ε⟩)` with `∑ᵢ(ϕᵢ − xᵢ)² < ε²` (i.e. `ϕ` is infinitesimally close to `x`). Writing
`ϕᵢ = germHom t cᵢ`, Proposition 3.16 turns `ϕ ∈ Ext(S)` into "`f(t') ∈ S` for all small `t'`", and
the germ order turns the infinitesimal bound into "`‖f(t') − x‖ < t'` for all small `t'`". Rescaling
the representatives to `(0, 1)` and extending continuously by `γ(0) = x` (Proposition 3.18; the
explicit bound makes the limit `x`) yields the curve. -/

namespace Azurite.BPR

open MvPolynomial Formula

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### `existsList` over all coordinates: sentence-hood and truth -/

/-- The free variables of an existential closure over a list: `Φ.freeVars` minus the list. -/
theorem freeVars_existsList {σ α : Type*} [AtomVars α σ] [DecidableEq σ]
    (L : List σ) (Φ : Formula σ α) :
    (Formula.existsList L Φ).freeVars = Φ.freeVars \ L.toFinset := by
  induction L with
  | nil => simp [Formula.existsList]
  | cons x rest ih =>
    show (Formula.exists_ x (Formula.existsList rest Φ)).freeVars = _
    show (Formula.existsList rest Φ).freeVars \ {x} = _
    rw [ih, List.toFinset_cons]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
    tauto

/-- Existentially closing over all of `Fin k` yields a sentence. -/
theorem isSentence_existsList_finRange {α : Type*} [AtomVars α (Fin k)]
    (Φ : Formula (Fin k) α) :
    Formula.isSentence (Formula.existsList (List.finRange k) Φ) := by
  rw [Formula.isSentence, freeVars_existsList]
  have huniv : (List.finRange k).toFinset = (Finset.univ : Finset (Fin k)) := by ext i; simp
  rw [huniv]
  exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)

/-- The existential closure over all coordinates is true exactly when the inner realization is
nonempty. -/
theorem isTrue_existsList_finRange_iff {C : Type*} [Nonempty C] {α : Type*}
    [AtomRealization α (Fin k) C] (Φ : Formula (Fin k) α) :
    (Formula.existsList (List.finRange k) Φ).IsTrue (C := C)
      ↔ (Φ.realization (C := C)).Nonempty := by
  rw [Formula.IsTrue]
  constructor
  · intro h
    obtain ⟨z⟩ : Nonempty (Fin k → C) := inferInstance
    have hmem : z ∈ (Formula.existsList (List.finRange k) Φ).realization (C := C) := by
      rw [h]; exact Set.mem_univ z
    rw [Formula.realization_existsList] at hmem
    obtain ⟨v, _, hv⟩ := hmem
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    rw [Formula.realization_existsList, Set.eq_univ_iff_forall]
    exact fun z => ⟨v, fun s hs => absurd (List.mem_finRange s) hs, hv⟩

/-- `mapAtom` commutes with `existsList`. -/
theorem mapAtom_existsList {σ α β : Type*} (f : α → β) (L : List σ) (Φ : Formula σ α) :
    (Formula.existsList L Φ).mapAtom f = Formula.existsList L (Φ.mapAtom f) := by
  induction L with
  | nil => rfl
  | cons x rest ih =>
    show Formula.exists_ x ((Formula.existsList rest Φ).mapAtom f)
      = Formula.exists_ x (Formula.existsList rest (Φ.mapAtom f))
    rw [ih]

/-! ### The ball polynomial and its substitutions -/

/-- The polynomial `∑ᵢ (Xᵢ − xᵢ)² − ε²` over `R[ε] = Polynomial R`, with `ε = Polynomial.X`. -/
noncomputable def ballPolyEps (x : Fin k → R) : MvPolynomial (Fin k) (Polynomial R) :=
  (∑ i : Fin k, (X i - C (Polynomial.C (x i))) ^ 2) - C Polynomial.X ^ 2

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Substituting `ε ↦ t` in the ball polynomial and evaluating at `y` gives `‖y − x‖² − t²`. -/
theorem aeval_substAtom_ballPolyEps (x : Fin k → R) (t : R) (y : Fin k → R) :
    aeval y ((ballPolyEps x).map (Polynomial.aeval t).toRingHom)
      = euclideanNormSq (y - x) - t ^ 2 := by
  rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom,
    ballPolyEps, euclideanNormSq]
  simp only [map_sub, map_sum, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self_apply, Pi.sub_apply]

/-- Evaluating the ball polynomial at a germ tuple `ϕ` (with `ε ↦ idGerm`) gives
`∑ᵢ(ϕᵢ − xᵢ)² − idGerm²`. -/
theorem aeval_ballPolyEps_germ (x : Fin k → R) (ϕ : Fin k → SemialgGerm R) :
    aeval ϕ (ballPolyEps x)
      = (∑ i, (ϕ i - algebraMap R (SemialgGerm R) (x i)) ^ 2) - idGerm ^ 2 := by
  rw [ballPolyEps]
  simp only [map_sub, map_sum, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    show algebraMap (Polynomial R) (SemialgGerm R) (Polynomial.C (x i)) = _
    rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_C _ _
  · congr 1
    show algebraMap (Polynomial R) (SemialgGerm R) Polynomial.X = idGerm
    rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_X _

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The coefficient base-change `R → R[ε]` followed by the substitution `ε ↦ t` is the identity on
formulas over `R`. -/
theorem mapCoeffO_mapAtom_substAtom (t : R)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) :
    (Φ.mapCoeffO (D' := Polynomial R)).mapAtom (substAtom t) = Φ := by
  induction Φ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    show Formula.atom (substAtom t
        ⟨P.map (algebraMap R (Polynomial R)), rel⟩) = Formula.atom ⟨P, rel⟩
    rw [substAtom]
    congr 2
    rw [MvPolynomial.map_map,
      show (Polynomial.aeval t).toRingHom.comp (algebraMap R (Polynomial R)) = RingHom.id R from by
        ext a
        simp only [RingHom.comp_apply, Polynomial.algebraMap_eq, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, Polynomial.aeval_C, Algebra.algebraMap_self_apply,
          RingHom.id_apply],
      MvPolynomial.map_id]
  | not _ ih => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih]
  | and _ _ ih₁ ih₂ => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih₁, ih₂]
  | exists_ x _ ih => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih]
  | forall_ x _ ih => simp only [Formula.mapCoeffO, Formula.mapAtom] at *; rw [ih]

/-- The scalar-tower compatibility `R → R[ε] → R⟨ε⟩` equals `R → R⟨ε⟩` (`ε ↦ idGerm`). -/
noncomputable instance : IsScalarTower R (Polynomial R) (SemialgGerm R) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    have h : algebraMap (Polynomial R) (SemialgGerm R) (algebraMap R (Polynomial R) a)
        = algebraMap R (SemialgGerm R) a := by
      rw [Polynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_C]
    exact h.symm

/-! ### Producing the infinitesimal curve germ -/

/-- **Curve germ.** Given `x ∈ closure S`, there is a germ tuple `ϕ ∈ Ext(S, R⟨ε⟩)` that is
infinitesimally close to `x`: `∑ᵢ(ϕᵢ − xᵢ)² < ε²`. This is the transfer step (Proposition 3.17): the
ball `B(x, t)` meets `S` for every small `t > 0`, hence the analogous statement holds at radius `ε`
in `R⟨ε⟩`. -/
theorem exists_germ_in_ext_ball (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S)
    (x : Fin k → R) (hx : x ∈ closure S) :
    ∃ ϕ : Fin k → SemialgGerm R,
      ϕ ∈ extension (R' := SemialgGerm R) S hS ∧
      (∑ i, (ϕ i - algebraMap R (SemialgGerm R) (x i)) ^ 2) < idGerm ^ 2 := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  obtain ⟨φS, hφSqf, hφS⟩ := semialgebraic_isQFRealizable S hS
  set Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)) :=
    (φS.mapCoeffO (D' := Polynomial R)).and (Formula.atom ⟨ballPolyEps x, OrderRel.lt⟩) with hΨ
  set Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)) :=
    Formula.existsList (List.finRange k) Ψ with hΦ
  have hΦsent : Formula.isSentence Φ := isSentence_existsList_finRange Ψ
  -- the R-side: for each `t`, the realization of `Ψ′(t)` is `S ∩ B(x, t)`.
  have hreal : ∀ t : R, (Ψ.mapAtom (substAtom t)).realization (C := R) = S ∩ openBall x t := by
    intro t
    rw [hΨ]
    show ((φS.mapCoeffO).mapAtom (substAtom t)).realization (C := R)
        ∩ (Formula.atom (substAtom t ⟨ballPolyEps x, OrderRel.lt⟩)).realization (C := R) = _
    rw [mapCoeffO_mapAtom_substAtom, ← hφS]
    ext y
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    refine and_congr_right fun _ => ?_
    show aeval y ((ballPolyEps x).map (Polynomial.aeval t).toRingHom) < 0 ↔ y ∈ openBall x t
    rw [aeval_substAtom_ballPolyEps, mem_openBall]
    constructor <;> intro h <;> linarith
  -- discharge the R-side using `x ∈ closure S` (`B(x, t)` meets `S` for all `t > 0`).
  have hRtrue : ∀ t : R, 0 < t → t < 1 → (Φ.mapAtom (substAtom t)).IsTrue (C := R) := by
    intro t ht _
    rw [hΦ, mapAtom_existsList, isTrue_existsList_finRange_iff, hreal t]
    obtain ⟨y, hyS, hylt⟩ := (mem_closure_iff_ball.mp hx) t ht
    exact ⟨y, hyS, mem_openBall.mpr hylt⟩
  -- transfer to the germ field.
  have hgermTrue : Φ.IsTrue (C := SemialgGerm R) :=
    (proposition_3_17 Φ hΦsent).mpr ⟨1, one_pos, hRtrue⟩
  -- extract `ϕ`.
  rw [hΦ, isTrue_existsList_finRange_iff] at hgermTrue
  obtain ⟨ϕ, hϕ⟩ := hgermTrue
  rw [hΨ, Formula.realization] at hϕ
  obtain ⟨hϕS, hϕB⟩ := hϕ
  refine ⟨ϕ, ?_, ?_⟩
  · rw [Formula.realization_mapCoeffO] at hϕS
    rwa [ext_eq hS hφS]
  · have hlt : aeval ϕ (ballPolyEps x) < 0 := hϕB
    rw [aeval_ballPolyEps_germ] at hlt
    linarith

/-! ### Extracting representatives and the eventual pointwise bounds -/

/-- `germHom` of the constant `a` is the constant germ `algebraMap R (R⟨ε⟩) a`. -/
theorem germHom_constSub (t : R) (ht : 0 < t) (a : R) :
    germHom t ht (constSub t a) = algebraMap R (SemialgGerm R) a := by
  show germHom t ht (constSub t a) = constGermHom a
  rw [germHom_apply, constGermHom, RingHom.comp_apply, germHom_apply]
  exact Quotient.sound ⟨min t 1, lt_min ht one_pos, fun _ _ _ => rfl⟩

/-- The underlying function of `constSub t a` is the constant `a`. -/
theorem constSub_coe_apply (t : R) (a : R) (u : Fin 1 → R) :
    ((constSub t a : semialgContSubring t) : (Fin 1 → R) → R) u = a := rfl

/-- **Curve data.** From `x ∈ closure S` we extract a common bound `t`, a representative tuple
`c = (c₁, …, c_k)` of semialgebraic continuous functions on `(0, t)`, and a threshold `τ ∈ (0, t]`
such that on `(0, τ)` the trajectory `f(s) = (c₁(s), …, c_k(s))` lies in `S` and is within distance
`s` of `x` (so `f → x` as `s → 0⁺`). -/
theorem exists_curve_data (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S)
    (x : Fin k → R) (hx : x ∈ closure S) :
    ∃ (t : R) (_ : 0 < t) (c : Fin k → semialgContSubring t) (τ : R), 0 < τ ∧ τ ≤ t ∧
      ∀ s : R, 0 < s → s < τ →
        (fun i => (c i : (Fin 1 → R) → R) (constPt s)) ∈ S ∧
        ∑ i, ((c i : (Fin 1 → R) → R) (constPt s) - x i) ^ 2 < s ^ 2 := by
  obtain ⟨ϕ, hϕext, hϕball⟩ := exists_germ_in_ext_ball S hS x hx
  -- pick a representative of each germ.
  choose rep hrep using fun i => Quotient.exists_rep (ϕ i)
  -- a common bound `t ≤ (rep i).bound` for all `i`.
  obtain ⟨t, ht0, htle⟩ : ∃ t : R, 0 < t ∧ ∀ i, t ≤ (rep i).bound := by
    rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · exact ⟨1, one_pos, fun i => (hk.false i).elim⟩
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => (rep i).bound), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]; exact fun i _ => (rep i).bound_pos
      · exact fun i => Finset.inf'_le _ (Finset.mem_univ i)
  -- restrict each representative to `(0, t)`.
  set c : Fin k → semialgContSubring t := fun i =>
    ⟨(rep i).toFun, mem_semialgContSubring.mpr ((rep i).isSemialgContinuous.mono
      (isSemialgebraicSet_rightNbhd t) (rightNbhd_subset (htle i)))⟩ with hc
  have hgi : ∀ i, germHom t ht0 (c i) = ϕ i := by
    intro i
    rw [germHom_apply, ← hrep i]
    exact Quotient.sound ⟨t, ht0, fun _ _ _ => rfl⟩
  have heq : (fun i => germHom t ht0 (c i)) = ϕ := funext hgi
  -- `ϕ ∈ Ext(S)` ⇒ eventually `f(s) ∈ S`.
  obtain ⟨t₁, ht₁, H₁⟩ := (proposition_3_16_mem t ht0 c S hS).mp (heq ▸ hϕext)
  -- the infinitesimal bound ⇒ eventually `‖f(s) − x‖² < s²`.
  have hballgerm : (∑ i, (ϕ i - algebraMap R (SemialgGerm R) (x i)) ^ 2)
      = germHom t ht0 (∑ i, (c i - constSub t (x i)) ^ 2) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, map_sub, hgi i, germHom_constSub]
  have hidsq : (idGerm : SemialgGerm R) ^ 2 = germHom t ht0 ((idSub t) ^ 2) := by
    rw [map_pow, germHom_idSub]
  rw [hballgerm, hidsq, germHom_apply, germHom_apply] at hϕball
  obtain ⟨t₂, ht₂, H₂⟩ := germ_lt_eventually hϕball
  -- the underlying-function values of the two germ representatives.
  have hAval : ∀ s : R,
      ((∑ i, (c i - constSub t (x i)) ^ 2 : semialgContSubring t) : (Fin 1 → R) → R) (constPt s)
        = ∑ i, ((c i : (Fin 1 → R) → R) (constPt s) - x i) ^ 2 := by
    intro s
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SubmonoidClass.coe_pow, Pi.pow_apply, AddSubgroupClass.coe_sub, Pi.sub_apply,
      constSub_coe_apply]
  have hBval : ∀ s : R,
      (((idSub t) ^ 2 : semialgContSubring t) : (Fin 1 → R) → R) (constPt s) = s ^ 2 := by
    intro s
    rw [SubmonoidClass.coe_pow, Pi.pow_apply]
    show ((idSub t : (Fin 1 → R) → R) (constPt s)) ^ 2 = s ^ 2
    rfl
  -- assemble on the common interval.
  refine ⟨t, ht0, c, min (min t₁ t₂) t, lt_min (lt_min ht₁ ht₂) ht0, min_le_right _ _,
    fun s hs hst => ⟨?_, ?_⟩⟩
  · exact H₁ s hs (lt_of_lt_of_le hst ((min_le_left _ _).trans (min_le_left _ _)))
  · have key : ((∑ i, (c i - constSub t (x i)) ^ 2 : semialgContSubring t) :
          (Fin 1 → R) → R) (constPt s)
        < (((idSub t) ^ 2 : semialgContSubring t) : (Fin 1 → R) → R) (constPt s) :=
      H₂ s hs (lt_of_lt_of_le hst ((min_le_left _ _).trans (min_le_right _ _)))
    rwa [hAval, hBval] at key

/-! ### Endpoint extension of a semialgebraic continuous function -/

open scoped Classical in
/-- The half-open interval `[0, a) ⊆ R¹`. -/
def closedRightNbhd (a : R) : Set (Fin 1 → R) := {u | 0 ≤ u 0 ∧ u 0 < a}

omit [IsRealClosed R] in
theorem isSemialgebraicSet_closedRightNbhd (a : R) :
    IsSemialgebraicSet (closedRightNbhd a) := by
  have heq : closedRightNbhd a = {u : Fin 1 → R | eval u (-MvPolynomial.X 0) ≤ 0}
      ∩ {u : Fin 1 → R | eval u (MvPolynomial.X 0 - MvPolynomial.C a) < 0} := by
    ext u
    simp only [closedRightNbhd, Set.mem_inter_iff, Set.mem_ofPred_eq, map_neg, MvPolynomial.eval_X,
      map_sub, MvPolynomial.eval_C, Left.neg_nonpos_iff, sub_neg]
  rw [heq]
  exact (IsSemialgebraicSet.leZero _).inter (IsSemialgebraicSet.ltZero _)

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `funGraph` splits along a union of the domain. -/
theorem funGraph_union {ℓ : ℕ} {S T : Set (Fin k → R)}
    (f : (Fin k → R) → (Fin ℓ → R)) :
    funGraph (S ∪ T) f = funGraph S f ∪ funGraph T f := by
  ext z
  simp only [funGraph, Set.mem_union, Set.mem_ofPred_eq]
  tauto

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `funGraph` depends only on the values of `f` on the domain. -/
theorem funGraph_congr {ℓ : ℕ} {S : Set (Fin k → R)} {f g : (Fin k → R) → (Fin ℓ → R)}
    (h : ∀ u ∈ S, f u = g u) : funGraph S f = funGraph S g := by
  ext z
  simp only [funGraph, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨h1, by rw [h2, h _ h1]⟩
  · exact ⟨h1, by rw [h2, ← h _ h1]⟩

/-- **Endpoint extension.** If `g` is semialgebraic and continuous on `(0, a)` and has a right limit
`b` at `0` (the explicit `ε`–`δ` condition `hlim`), then extending it by `b` at `0` is semialgebraic
and continuous on `[0, a)`. -/
theorem isSemialgContinuousOn_endpointExtend {a : R} {g : (Fin 1 → R) → R}
    (hg : IsSemialgContinuousOn (rightNbhd a) g) (b : R)
    (hlim : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → |g (constPt s) - b| < r) :
    IsSemialgContinuousOn (closedRightNbhd a) (fun u => if u 0 = 0 then b else g u) := by
  classical
  set ghat : (Fin 1 → R) → R := fun u => if u 0 = 0 then b else g u with hghat
  have hZsemi : IsSemialgebraicSet {u : Fin 1 → R | u 0 = 0 ∧ u 0 < a} := by
    have heq : {u : Fin 1 → R | u 0 = 0 ∧ u 0 < a}
        = {u : Fin 1 → R | eval u (MvPolynomial.X 0) = 0}
          ∩ {u : Fin 1 → R | eval u (MvPolynomial.X 0 - MvPolynomial.C a) < 0} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, MvPolynomial.eval_X, map_sub,
        MvPolynomial.eval_C, sub_neg]
    rw [heq]
    exact (IsSemialgebraicSet.eqZero _).inter (IsSemialgebraicSet.ltZero _)
  have hunion : closedRightNbhd a = rightNbhd a ∪ {u : Fin 1 → R | u 0 = 0 ∧ u 0 < a} := by
    ext u
    simp only [closedRightNbhd, rightNbhd, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, ha⟩
      rcases eq_or_lt_of_le h0 with h | h
      · exact Or.inr ⟨h.symm, ha⟩
      · exact Or.inl ⟨h, ha⟩
    · rintro (⟨h0, ha⟩ | ⟨h0, ha⟩)
      · exact ⟨h0.le, ha⟩
      · exact ⟨h0.ge, ha⟩
  refine ⟨?_, ?_⟩
  · -- semialgebraic: split the graph along the union.
    show IsSemialgebraicSet (funGraph (closedRightNbhd a) (scalarFun ghat))
    rw [hunion, funGraph_union]
    apply IsSemialgebraicSet.union
    · rw [funGraph_congr (f := scalarFun ghat) (g := scalarFun g) (fun u hu => by
        show constPt (if u 0 = 0 then b else g u) = constPt (g u)
        rw [ite_eq_right hu.1.ne'])]
      exact hg.1
    · rw [funGraph_congr (f := scalarFun ghat) (g := scalarFun (fun _ : Fin 1 → R => b))
        (fun u hu => by
          show constPt (if u 0 = 0 then b else g u) = constPt b
          rw [ite_eq_left hu.1])]
      have hpoly : scalarFun (fun _ : Fin 1 → R => b) = polynomialMap ![MvPolynomial.C b] := by
        funext u i
        rw [Subsingleton.elim i 0]
        simp [scalarFun, constPt, polynomialMap]
      rw [hpoly]
      exact isSemialgebraicFunction_polynomialMap hZsemi _
  · -- continuous: `g`-continuity on the interior, the limit at `0`.
    rw [continuousOn_fin_one_iff]
    intro p hp r hr
    by_cases hp0 : p 0 = 0
    · -- boundary point `p 0 = 0`: use the limit.
      obtain ⟨δ, hδ, hld⟩ := hlim r hr
      refine ⟨δ, hδ, fun y hy hyd => ?_⟩
      rw [euclideanNorm_fin_one, Pi.sub_apply, hp0, sub_zero] at hyd
      show |scalarFun ghat y 0 - scalarFun ghat p 0| < r
      have hgp : ghat p = b := by rw [hghat]; exact ite_eq_left hp0
      show |ghat y - ghat p| < r
      rw [hgp]
      by_cases hy0 : y 0 = 0
      · rw [hghat]; simp only [ite_eq_left hy0, sub_self, abs_zero]; exact hr
      · have hy0' : 0 < y 0 := lt_of_le_of_ne hy.1 (Ne.symm hy0)
        have hyeq : y = constPt (y 0) := by funext i; rw [Subsingleton.elim i 0]; rfl
        rw [hghat]
        simp only [ite_eq_right hy0]
        rw [hyeq]
        exact hld (y 0) hy0' (by rw [abs_of_pos hy0'] at hyd; exact hyd)
    · -- interior point `p 0 > 0`: use continuity of `g`.
      have hp0' : 0 < p 0 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
      have hpin : p ∈ rightNbhd a := ⟨hp0', hp.2⟩
      have hgcont := hg.2
      rw [continuousOn_fin_one_iff] at hgcont
      obtain ⟨δ', hδ', h'⟩ := hgcont p hpin r hr
      refine ⟨min δ' (p 0), lt_min hδ' hp0', fun y hy hyd => ?_⟩
      rw [euclideanNorm_fin_one, Pi.sub_apply] at hyd
      have hyd' : |y 0 - p 0| < p 0 := lt_of_lt_of_le hyd (min_le_right _ _)
      have hy0 : 0 < y 0 := by rw [abs_lt] at hyd'; linarith [hyd'.1]
      have hyin : y ∈ rightNbhd a := ⟨hy0, hy.2⟩
      show |scalarFun ghat y 0 - scalarFun ghat p 0| < r
      show |ghat y - ghat p| < r
      rw [hghat]
      simp only [ite_eq_right hy0.ne', ite_eq_right hp0]
      have := h' y hyin (by
        rw [euclideanNorm_fin_one, Pi.sub_apply]
        exact lt_of_lt_of_le hyd (min_le_left _ _))
      exact this

/-! ### Theorem 3.19 -/

/-- **BPR Theorem 3.19 (Curve selection lemma).** Let `S ⊆ Rᵏ` be semialgebraic and `x ∈ closure S`.
Then there is a continuous semialgebraic map `γ : [0, 1) → Rᵏ` with `γ(0) = x` and `γ((0, 1)) ⊆ S`.
The domain `[0, 1)` is `closedRightNbhd 1 ⊆ R¹`. -/
theorem theorem_3_19 (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S)
    (x : Fin k → R) (hx : x ∈ closure S) :
    ∃ γ : (Fin 1 → R) → (Fin k → R),
      IsSemialgebraicFunction (closedRightNbhd 1) γ ∧
      ContinuousOn γ (closedRightNbhd 1) ∧
      γ (constPt 0) = x ∧
      ∀ s : R, 0 < s → s < 1 → γ (constPt s) ∈ S := by
  obtain ⟨t, ht, c, τ, hτ0, hτt, hdata⟩ := exists_curve_data S hS x hx
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · -- `k = 0`: the curve is the constant `x` (and `x ∈ S` by subsingleton).
    obtain ⟨hmem, _⟩ := hdata (τ / 2) (half_pos hτ0) (by linarith)
    have hxS : x ∈ S := by
      rwa [Subsingleton.elim (fun i => (c i : (Fin 1 → R) → R) (constPt (τ / 2))) x] at hmem
    refine ⟨fun _ => x, ?_, continuousOn_const, rfl, fun s _ _ => hxS⟩
    show IsSemialgebraicSet (funGraph (closedRightNbhd 1) (fun _ : Fin 1 → R => x))
    have hfg : funGraph (closedRightNbhd 1) (fun _ : Fin 1 → R => x)
        = {z : Fin (1 + k) → R | z ∘ Fin.castAdd k ∈ closedRightNbhd 1} := by
      ext z
      simp only [funGraph, Set.mem_ofPred_eq, and_iff_left_iff_imp]
      exact fun _ => Subsingleton.elim _ _
    rw [hfg]
    exact (isSemialgebraicSet_closedRightNbhd 1).comap (Fin.castAdd k)
  · -- `k > 0`: rescale to `(0, 1)` and extend by `x` at `0`.
    have hsf : scalarFun (fun u : Fin 1 → R => τ * u 0)
        = polynomialMap ![MvPolynomial.C τ * MvPolynomial.X 0] := by
      funext u i
      rw [Subsingleton.elim i 0]
      simp [scalarFun, constPt, polynomialMap]
    set scaleRep : SemialgGermRep R :=
      { bound := 1, bound_pos := one_pos, toFun := fun u => τ * u 0,
        isSemialgContinuous :=
          ⟨by rw [hsf]; exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_rightNbhd 1) _,
            by rw [hsf]; exact (continuous_polynomialMap _).continuousOn⟩ } with hscaleRep
    have hmaps : Set.MapsTo (scalarFun scaleRep.toFun) (rightNbhd scaleRep.bound) (rightNbhd t) := by
      intro u hu
      refine ⟨?_, ?_⟩
      · show 0 < τ * u 0
        exact mul_pos hτ0 hu.1
      · show τ * u 0 < t
        have : τ * u 0 < τ := by nlinarith [hu.2, hτ0]
        linarith [hτt]
    -- the scaled representatives are semialgebraic continuous on `(0, 1)`.
    have hdj : ∀ j, IsSemialgContinuousOn (rightNbhd 1)
        (fun u => (c j : (Fin 1 → R) → R) (constPt (τ * u 0))) := fun j =>
      (compRep (c j).1 (mem_semialgContSubring.mp (c j).2) scaleRep hmaps).isSemialgContinuous
    -- each scaled representative has right limit `x j` at `0`.
    have hlim_j : ∀ j, ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
        |(fun u => (c j : (Fin 1 → R) → R) (constPt (τ * u 0))) (constPt s) - x j| < r := by
      intro j r hr
      refine ⟨min 1 (r / τ), lt_min one_pos (by positivity), fun s hs hsδ => ?_⟩
      have hs1 : s < 1 := lt_of_lt_of_le hsδ (min_le_left _ _)
      have hsτr : τ * s < r := by
        have hsr : s < r / τ := lt_of_lt_of_le hsδ (min_le_right _ _)
        calc τ * s < τ * (r / τ) := mul_lt_mul_of_pos_left hsr hτ0
          _ = r := by field_simp
      have hτs0 : 0 < τ * s := mul_pos hτ0 hs
      have hτsτ : τ * s < τ := by nlinarith [hs1, hτ0]
      obtain ⟨_, hbound⟩ := hdata (τ * s) hτs0 hτsτ
      have hsq : ((c j : (Fin 1 → R) → R) (constPt (τ * s)) - x j) ^ 2 < (τ * s) ^ 2 :=
        lt_of_le_of_lt (Finset.single_le_sum
          (f := fun i => ((c i : (Fin 1 → R) → R) (constPt (τ * s)) - x i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)) hbound
      show |(c j : (Fin 1 → R) → R) (constPt (τ * (constPt s : Fin 1 → R) 0)) - x j| < r
      rw [show ((constPt s : Fin 1 → R)) 0 = s from rfl]
      have habs : |(c j : (Fin 1 → R) → R) (constPt (τ * s)) - x j| < τ * s :=
        abs_lt_of_sq_lt_sq hsq hτs0.le
      linarith
    -- endpoint-extend each component.
    have hγ : ∀ j, IsSemialgContinuousOn (closedRightNbhd 1)
        (fun u => if u 0 = 0 then x j else (c j : (Fin 1 → R) → R) (constPt (τ * u 0))) := fun j =>
      isSemialgContinuousOn_endpointExtend (hdj j) (x j) (hlim_j j)
    refine ⟨fun u j => if u 0 = 0 then x j else (c j : (Fin 1 → R) → R) (constPt (τ * u 0)),
      isSemialgebraicFunction_of_coords (fun j => (hγ j).1),
      continuousOn_of_components (fun j => (hγ j).2), ?_, ?_⟩
    · funext j
      show (if ((constPt (0 : R)) : Fin 1 → R) 0 = 0 then x j else _) = x j
      rw [ite_eq_left (show ((constPt (0 : R)) : Fin 1 → R) 0 = 0 from rfl)]
    · intro s hs hs1
      have hτs0 : 0 < τ * s := mul_pos hτ0 hs
      have hτsτ : τ * s < τ := by nlinarith [hs1, hτ0]
      obtain ⟨hmem, _⟩ := hdata (τ * s) hτs0 hτsτ
      have hfun : (fun j => if ((constPt s : Fin 1 → R)) 0 = 0 then x j
            else (c j : (Fin 1 → R) → R) (constPt (τ * (constPt s : Fin 1 → R) 0)))
          = fun i => (c i : (Fin 1 → R) → R) (constPt (τ * s)) := by
        funext j
        rw [show ((constPt s : Fin 1 → R)) 0 = s from rfl, ite_eq_right hs.ne']
      show (fun j => if ((constPt s : Fin 1 → R)) 0 = 0 then x j
          else (c j : (Fin 1 → R) → R) (constPt (τ * (constPt s : Fin 1 → R) 0))) ∈ S
      rw [hfun]
      exact hmem

end Azurite.BPR
