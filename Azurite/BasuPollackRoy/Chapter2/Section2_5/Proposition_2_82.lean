/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_80
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Finset.Sort

/-! # BPR Proposition 2.82: semialgebraic sets over a real closure are `F`-definable

**Proposition 2.82.** Let `F` be an ordered field and `R` its real closure. A
semialgebraic set `S ⊆ Rᵏ` can be defined by a quantifier-free formula with
coefficients in `F`.

This file follows BPR's proof. Every `a ∈ R` is algebraic over `F`, a root of its
minimal polynomial `P_a ∈ F[X]`. If `a = a_j` among the roots `a_1 < … < a_ℓ` of
`P_a` in `R`, the *F*-formula

`∆_a(Y) := ∃Y_1…Y_ℓ (Y_1<…<Y_ℓ ∧ ⋀ P_a(Y_i)=0 ∧ (∀X, P_a(X)=0 ⇒ ⋁ X=Y_i) ∧ Y=Y_j)`

has `R`-realization `{a}`. Collecting the finite set `A` of `R`-coefficients of a
quantifier-free `Φ` defining `S`, replacing each `a ∈ A` by a fresh variable gives
`Ψ(X, Y)` over `F`, and `S = {x | ∀ y, (⋀_a ∆_a(y_a)) ⇒ Ψ(x, y)}`. The big `∀`-formula
is over `F`; by Theorem 2.77 it is equivalent to a quantifier-free formula over `F`.
-/

open MvPolynomial Polynomial

namespace Azurite.BPR

namespace Formula

/-! ### Existential quantification over a list of coordinates -/

variable {σ : Type*} {α : Type*} {C : Type*}

/-- Existentially quantify each coordinate in a list. -/
def existsList (L : List σ) (Φ : Formula σ α) : Formula σ α :=
  L.foldr Formula.exists_ Φ

variable [AtomRealization α σ C] [DecidableEq σ]

/-- **Realization of a multi-existential.** Quantifying every coordinate in `L`
existentially yields the set of `z` admitting an assignment `v` that agrees with `z`
*outside* `L` and realizes `Φ`. -/
theorem realization_existsList (L : List σ) (Φ : Formula σ α) :
    (existsList L Φ).realization (C := C) =
      {z | ∃ v : σ → C, (∀ s ∉ L, v s = z s) ∧ v ∈ Φ.realization (C := C)} := by
  induction L with
  | nil =>
    simp only [existsList, List.foldr_nil]
    ext z
    simp only [Set.mem_ofPred_eq, List.not_mem_nil, not_false_eq_true, forall_const]
    constructor
    · intro hz; exact ⟨z, fun _ => rfl, hz⟩
    · rintro ⟨v, hv, hvΦ⟩
      have : v = z := funext hv
      rwa [this] at hvΦ
  | cons s L' ih =>
    ext z
    have hstep : z ∈ (existsList (s :: L') Φ).realization (C := C) ↔
        ∃ w, Function.update z s w ∈ (existsList L' Φ).realization (C := C) := Iff.rfl
    rw [hstep]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, hw⟩
      rw [ih] at hw
      obtain ⟨v, hagree, hvΦ⟩ := hw
      refine ⟨v, fun t ht => ?_, hvΦ⟩
      rw [List.mem_cons, not_or] at ht
      rw [hagree t ht.2, Function.update_of_ne ht.1]
    · rintro ⟨v, hagree, hvΦ⟩
      refine ⟨v s, ?_⟩
      rw [ih]
      refine ⟨v, fun t ht => ?_, hvΦ⟩
      by_cases hts : t = s
      · subst hts; rw [Function.update_self]
      · rw [Function.update_of_ne hts]
        exact hagree t (by rw [List.mem_cons, not_or]; exact ⟨hts, ht⟩)

/-- Universally quantify each coordinate in a list. -/
def forallList (L : List σ) (Φ : Formula σ α) : Formula σ α :=
  L.foldr Formula.forall_ Φ

/-- **Realization of a multi-universal.** Quantifying every coordinate in `L`
universally yields the set of `z` such that *every* assignment `v` agreeing with `z`
outside `L` realizes `Φ`. -/
theorem realization_forallList (L : List σ) (Φ : Formula σ α) :
    (forallList L Φ).realization (C := C) =
      {z | ∀ v : σ → C, (∀ s ∉ L, v s = z s) → v ∈ Φ.realization (C := C)} := by
  induction L with
  | nil =>
    simp only [forallList, List.foldr_nil]
    ext z
    simp only [Set.mem_ofPred_eq, List.not_mem_nil, not_false_eq_true, forall_const]
    constructor
    · intro hz v hv; rwa [show v = z from funext hv]
    · intro h; exact h z (fun _ => rfl)
  | cons s L' ih =>
    ext z
    have hstep : z ∈ (forallList (s :: L') Φ).realization (C := C) ↔
        ∀ c, Function.update z s c ∈ (forallList L' Φ).realization (C := C) := Iff.rfl
    rw [hstep]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h v hv
      have hc := h (v s)
      rw [ih] at hc
      apply hc
      intro t ht
      by_cases hts : t = s
      · subst hts; rw [Function.update_self]
      · rw [Function.update_of_ne hts]
        exact hv t (by rw [List.mem_cons, not_or]; exact ⟨hts, ht⟩)
    · intro h c
      rw [ih]
      intro v hv
      apply h v
      intro t ht
      rw [List.mem_cons, not_or] at ht
      rw [hv t ht.2, Function.update_of_ne ht.1]

end Formula

/-! ### Univariate-to-multivariate atom embedding

`P_a(Y_i)` is `P_a ∈ F[X]` with its single variable substituted by the multivariate
coordinate variable `X i`. Evaluating at `z` recovers the univariate evaluation at
`z i`. -/

/-- Substitute the univariate variable of `Q ∈ F[X]` by the multivariate coordinate
`X i`. -/
noncomputable def uniSubst {σ : Type*} {F : Type*} [CommRing F] (i : σ) (Q : F[X]) :
    MvPolynomial σ F :=
  Polynomial.aeval (MvPolynomial.X i) Q

theorem aeval_uniSubst {σ : Type*} {F : Type*} [CommRing F]
    {R : Type*} [CommRing R] [Algebra F R] (z : σ → R) (i : σ) (Q : F[X]) :
    MvPolynomial.aeval z (uniSubst i Q) = Polynomial.aeval (z i) Q := by
  have h : (MvPolynomial.aeval z).comp (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ F))
      = Polynomial.aeval (z i) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h Q

/-! ### The formula `∆_a`

For `a ∈ R` algebraic over `F`, with `P = minpoly F a` and roots `a_1 < … < a_ℓ` of `P`
in `R`, the formula `∆_a(Y) = ∃ Y_1…Y_ℓ (Y_1<…<Y_ℓ ∧ ⋀ P(Y_i)=0 ∧ (∀X, P(X)=0 ⇒ ⋁ X=Y_i)
∧ Y=Y_j)` has `R`-realization `{a}`.

We build it generically over a variable type `σ`, given distinct coordinates for the free
variable `Y` (`y0`), the bound roots `Y_1,…,Y_ℓ` (`rc : Fin ℓ → σ`), and the universally
quantified `X` (`xc`). -/

namespace Formula

section Delta

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- The atom `Y_i < Y_j` (as `X (rc i) - X (rc j) < 0`). -/
noncomputable def ltPairForm {ℓ : ℕ} (rc : Fin ℓ → σ) (i j : Fin ℓ) :
    Formula σ (OrderedFieldAtom σ F) :=
  ltZeroO (MvPolynomial.X (rc i) - MvPolynomial.X (rc j))

/-- `Y_1 < Y_2 < … < Y_ℓ`: the strict-monotonicity conjunction over the root coordinates. -/
noncomputable def orderingForm {ℓ : ℕ} (rc : Fin ℓ → σ) :
    Formula σ (OrderedFieldAtom σ F) :=
  conjListO
    ((Finset.univ.filter (fun p : Fin ℓ × Fin ℓ => p.1 < p.2)).toList.map
      (fun p => ltPairForm rc p.1 p.2))

/-- `P(Y_1) = … = P(Y_ℓ) = 0`: every root coordinate is a root of `P`. -/
noncomputable def allRootsForm {ℓ : ℕ} (P : F[X]) (rc : Fin ℓ → σ) :
    Formula σ (OrderedFieldAtom σ F) :=
  conjListO (List.ofFn (fun t => eqZeroO (uniSubst (rc t) P)))

/-- `∀ X, P(X) = 0 ⇒ (X = Y_1 ∨ … ∨ X = Y_ℓ)`: the root coordinates exhaust the roots. -/
noncomputable def exhaustForm {ℓ : ℕ} (P : F[X]) (rc : Fin ℓ → σ) (xc : σ) :
    Formula σ (OrderedFieldAtom σ F) :=
  forall_ xc (implies (eqZeroO (uniSubst xc P))
    (disjListO (List.ofFn (fun t => eqZeroO (MvPolynomial.X xc - MvPolynomial.X (rc t))))))

/-- `Y = Y_j`: the free variable equals the `j`-th root. -/
noncomputable def yEqForm {ℓ : ℕ} (rc : Fin ℓ → σ) (y0 : σ) (jdx : Fin ℓ) :
    Formula σ (OrderedFieldAtom σ F) :=
  eqZeroO (MvPolynomial.X y0 - MvPolynomial.X (rc jdx))

/-- The formula `∆_a`. -/
noncomputable def deltaForm {ℓ : ℕ} (P : F[X]) (rc : Fin ℓ → σ) (xc y0 : σ) (jdx : Fin ℓ) :
    Formula σ (OrderedFieldAtom σ F) :=
  existsList (List.ofFn rc)
    (and (orderingForm rc) (and (allRootsForm P rc)
      (and (exhaustForm P rc xc) (yEqForm rc y0 jdx))))

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra F R]

theorem realization_ltPairForm {ℓ : ℕ} (rc : Fin ℓ → σ) (i j : Fin ℓ) :
    (ltPairForm (F := F) rc i j).realization (C := R) = {v | v (rc i) < v (rc j)} := by
  rw [ltPairForm, realization_ltZeroO]
  ext v
  simp only [Set.mem_ofPred_eq, map_sub, MvPolynomial.aeval_X, sub_neg]

theorem mem_orderingForm {ℓ : ℕ} (rc : Fin ℓ → σ) (v : σ → R) :
    v ∈ (orderingForm (F := F) rc).realization (C := R) ↔
      StrictMono (fun t => v (rc t)) := by
  rw [orderingForm, realization_conjListO]
  simp only [Set.mem_ofPred_eq, List.forall_mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i j hij
    have := h (i, j) hij
    rwa [realization_ltPairForm] at this
  · intro hmono p hp
    rw [realization_ltPairForm]
    exact hmono hp

theorem mem_allRootsForm {ℓ : ℕ} (P : F[X]) (rc : Fin ℓ → σ) (v : σ → R) :
    v ∈ (allRootsForm P rc).realization (C := R) ↔
      ∀ t, Polynomial.aeval (v (rc t)) P = 0 := by
  rw [allRootsForm, realization_conjListO]
  simp only [Set.mem_ofPred_eq, List.forall_mem_ofFn_iff, realization_eqZeroO,
    aeval_uniSubst]

theorem mem_yEqForm {ℓ : ℕ} (rc : Fin ℓ → σ) (y0 : σ) (jdx : Fin ℓ) (v : σ → R) :
    v ∈ (yEqForm (F := F) rc y0 jdx).realization (C := R) ↔ v y0 = v (rc jdx) := by
  rw [yEqForm, realization_eqZeroO]
  simp only [Set.mem_ofPred_eq, map_sub, MvPolynomial.aeval_X, sub_eq_zero]

theorem mem_exhaustForm {ℓ : ℕ} (P : F[X]) (rc : Fin ℓ → σ) (xc : σ)
    (hxc : ∀ t, rc t ≠ xc) (v : σ → R) :
    v ∈ (exhaustForm P rc xc).realization (C := R) ↔
      ∀ x : R, Polynomial.aeval x P = 0 → ∃ t, x = v (rc t) := by
  rw [exhaustForm]
  show (∀ c : R, Function.update v xc c ∈ _) ↔ _
  refine forall_congr' (fun c => ?_)
  set w := Function.update v xc c with hw
  have hwxc : w xc = c := Function.update_self ..
  have hwrc : ∀ t, w (rc t) = v (rc t) := fun t => Function.update_of_ne (hxc t) ..
  have hA : w ∈ (eqZeroO (uniSubst xc P)).realization (C := R) ↔
      Polynomial.aeval c P = 0 := by
    rw [realization_eqZeroO]; simp only [Set.mem_ofPred_eq, aeval_uniSubst, hwxc]
  have hB : w ∈ (disjListO (List.ofFn
      (fun t => eqZeroO ((MvPolynomial.X xc : MvPolynomial σ F) -
        MvPolynomial.X (rc t))))).realization (C := R) ↔
      ∃ t, c = v (rc t) := by
    rw [realization_disjListO]
    simp only [Set.mem_ofPred_eq, List.mem_ofFn, exists_exists_eq_and,
      realization_eqZeroO, map_sub, MvPolynomial.aeval_X, hwxc, hwrc, sub_eq_zero]
  show w ∈ ((eqZeroO (uniSubst xc P)).implies _).realization (C := R) ↔ _
  rw [show ((eqZeroO (uniSubst xc P)).implies
      (disjListO (List.ofFn
        (fun t => eqZeroO (MvPolynomial.X xc - MvPolynomial.X (rc t)))))).realization (C := R)
      = ((eqZeroO (uniSubst xc P)).realization (C := R))ᶜ ∪
        (disjListO (List.ofFn
          (fun t => eqZeroO (MvPolynomial.X xc - MvPolynomial.X (rc t))))).realization (C := R)
      from rfl]
  rw [Set.mem_union, Set.mem_compl_iff, hA, hB]
  tauto

/-- **`∆_a` realizes to the singleton `{a}`** (presented as `{z | z y0 = a}`, the
coordinate-`y0` slice). Here `a` is the `jdx`-th root of `P` in `R`, the root
coordinates `rc` are distinct from each other, from the universally-quantified `xc`,
and from the free coordinate `y0`. The ordered + exhaustive root conditions force the
existential witnesses to be exactly the increasing enumeration of the roots
(`Finset.orderEmbOfFin_unique`), so `Y = Y_j` pins `Y` to the `j`-th root. -/
theorem deltaForm_realization {ℓ : ℕ} (P : F[X]) (hP : P ≠ 0)
    (hinj : Function.Injective (algebraMap F R))
    (rc : Fin ℓ → σ) (xc y0 : σ) (jdx : Fin ℓ)
    (hℓ : ((P.map (algebraMap F R)).roots.toFinset).card = ℓ)
    (hrc_inj : Function.Injective rc)
    (hxc_rc : ∀ t, rc t ≠ xc)
    (hy0_rc : ∀ t, rc t ≠ y0) :
    (deltaForm P rc xc y0 jdx).realization (C := R) =
      {z | z y0 = ((P.map (algebraMap F R)).roots.toFinset).orderEmbOfFin hℓ jdx} := by
  classical
  rw [deltaForm, realization_existsList]
  set s := (P.map (algebraMap F R)).roots.toFinset with hs
  set a := s.orderEmbOfFin hℓ jdx with ha
  have hQ0 : (P.map (algebraMap F R)) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hP
  have hmemroots : ∀ x : R, x ∈ s ↔ Polynomial.aeval x P = 0 := by
    intro x
    rw [hs, Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def,
      show Polynomial.eval x (P.map (algebraMap F R)) = Polynomial.aeval x P from by
        rw [Polynomial.aeval_def, Polynomial.eval_map]]
  have hy0_notmem : y0 ∉ List.ofFn rc := by
    rw [List.mem_ofFn]; rintro ⟨t, ht⟩; exact hy0_rc t ht
  have hbody : ∀ v : σ → R,
      v ∈ (Formula.and (orderingForm rc) (Formula.and (allRootsForm P rc)
        (Formula.and (exhaustForm P rc xc) (yEqForm rc y0 jdx)))).realization (C := R) ↔
      StrictMono (fun t => v (rc t)) ∧ (∀ t, Polynomial.aeval (v (rc t)) P = 0) ∧
        (∀ x, Polynomial.aeval x P = 0 → ∃ t, x = v (rc t)) ∧ v y0 = v (rc jdx) := by
    intro v
    simp only [realization_and, Set.mem_inter_iff, mem_orderingForm, mem_allRootsForm,
      mem_exhaustForm P rc xc hxc_rc, mem_yEqForm]
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hagree, hv⟩
    rw [hbody] at hv
    obtain ⟨hmono, hroots, _hexh, hyeq⟩ := hv
    have hvy0 : v y0 = z y0 := hagree y0 hy0_notmem
    have hgmem : ∀ t, (fun t => v (rc t)) t ∈ s := fun t => (hmemroots _).mpr (hroots t)
    have hg : (fun t => v (rc t)) = ⇑(s.orderEmbOfFin hℓ) :=
      Finset.orderEmbOfFin_unique hℓ hgmem hmono
    have hjdx : v (rc jdx) = a := by rw [ha]; exact congrFun hg jdx
    rw [← hvy0, hyeq]; exact hjdx
  · intro hz
    set g := ⇑(s.orderEmbOfFin hℓ) with hgdef
    refine ⟨fun s' => if h : ∃ t, rc t = s' then g h.choose else z s', ?_, ?_⟩
    · intro s' hs'
      show (if h : ∃ t, rc t = s' then g h.choose else z s') = z s'
      rw [dite_eq_right]; rintro ⟨t, ht⟩
      exact hs' (List.mem_ofFn.mpr ⟨t, ht⟩)
    · rw [hbody]
      have hvrc : ∀ t, (if h : ∃ t', rc t' = rc t then g h.choose else z (rc t)) = g t := by
        intro t
        rw [dite_eq_left ⟨t, rfl⟩]
        congr 1
        exact hrc_inj (Exists.choose_spec (⟨t, rfl⟩ : ∃ t', rc t' = rc t))
      have hvy0 : (if h : ∃ t, rc t = y0 then g h.choose else z y0) = z y0 := by
        rw [dite_eq_right]; rintro ⟨t, ht⟩; exact hy0_rc t ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [hvrc]; exact (s.orderEmbOfFin hℓ).strictMono
      · intro t; rw [hvrc]; exact (hmemroots (g t)).mp (Finset.orderEmbOfFin_mem s hℓ t)
      · intro x hx
        have hxs : x ∈ s := (hmemroots x).mpr hx
        have hxr : x ∈ Set.range g := by
          rw [hgdef, Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hxs
        obtain ⟨t, ht⟩ := hxr
        exact ⟨t, by rw [hvrc]; exact ht.symm⟩
      · rw [hvy0, hvrc, hz, ha]

end Delta

/-! ### Coefficient set of a formula -/

/-- The finite set of all coefficient values appearing in the atom polynomials of a
formula. -/
noncomputable def coeffSet {k : ℕ} {R : Type*} [CommRing R] [DecidableEq R] :
    Formula (Fin k) (OrderedFieldAtom (Fin k) R) → Finset R
  | .atom a => a.poly.support.image (fun α => a.poly.coeff α)
  | .not Φ => Φ.coeffSet
  | .and Φ₁ Φ₂ => Φ₁.coeffSet ∪ Φ₂.coeffSet
  | .or Φ₁ Φ₂ => Φ₁.coeffSet ∪ Φ₂.coeffSet
  | .implies Φ₁ Φ₂ => Φ₁.coeffSet ∪ Φ₂.coeffSet
  | .exists_ _ Φ => Φ.coeffSet
  | .forall_ _ Φ => Φ.coeffSet

end Formula

/-! ### The coefficient lift `P ↦ P̃`

For a polynomial `P ∈ R[X_1,…,X_k]`, we build `P̃ ∈ F[X_1,…,X_N]` by replacing each
`R`-coefficient `r` (which lies in the finite set `A`) by the variable `X (Yembed (idx r))`
and each `X_i` by `X (Xembed i)`. This is *not* a ring homomorphism (the coefficient map is
a non-canonical section), so `P̃` is built as an explicit `Finset` sum and the evaluation
identity is proved by `aeval`-linearity. -/

section Lift

variable {k N : ℕ} {F : Type*} [CommRing F] {R : Type*} [CommRing R] [Algebra F R]
  [DecidableEq R]

/-- The enumeration `Fin A.card → R` of the coefficient set `A`. -/
noncomputable def coeffEnum (A : Finset R) : Fin A.card → R :=
  fun j => ((A.equivFin).symm j : R)

/-- The non-canonical lift of a single coefficient `r`: the variable `X (Yembed (idx r))`
if `r ∈ A`, else `0`. -/
noncomputable def coeffLift (A : Finset R) (Yembed : Fin A.card → Fin N) (r : R) :
    MvPolynomial (Fin N) F :=
  if h : r ∈ A then MvPolynomial.X (Yembed (A.equivFin ⟨r, h⟩)) else 0

/-- The lift `P̃` of a multivariate polynomial. -/
noncomputable def polyLift (A : Finset R) (Xembed : Fin k → Fin N)
    (Yembed : Fin A.card → Fin N) (P : MvPolynomial (Fin k) R) : MvPolynomial (Fin N) F :=
  ∑ α ∈ P.support, coeffLift A Yembed (P.coeff α) *
    ∏ i ∈ α.support, (MvPolynomial.X (Xembed i) : MvPolynomial (Fin N) F) ^ (α i)

theorem coeffLift_eval (A : Finset R) (Yembed : Fin A.card → Fin N) (w : Fin N → R)
    (hw : ∀ j, w (Yembed j) = coeffEnum A j) (r : R) (hr : r ∈ A) :
    MvPolynomial.aeval w (coeffLift (F := F) A Yembed r) = r := by
  rw [coeffLift, dite_eq_left hr, MvPolynomial.aeval_X, hw, coeffEnum, Equiv.symm_apply_apply]

theorem polyLift_eval (A : Finset R) (Xembed : Fin k → Fin N) (Yembed : Fin A.card → Fin N)
    (w : Fin N → R) (hw : ∀ j, w (Yembed j) = coeffEnum A j)
    (P : MvPolynomial (Fin k) R) (hPA : ∀ α ∈ P.support, P.coeff α ∈ A) :
    MvPolynomial.aeval w (polyLift (F := F) A Xembed Yembed P) =
      MvPolynomial.aeval (fun i => w (Xembed i)) P := by
  have hRHS : MvPolynomial.aeval (fun i => w (Xembed i)) P
      = ∑ α ∈ P.support, P.coeff α *
        ∏ i ∈ α.support, (w (Xembed i)) ^ (α i) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]
  rw [hRHS, polyLift, map_sum]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  rw [map_mul, map_prod, coeffLift_eval A Yembed w hw (P.coeff α) (hPA α hα)]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_pow, MvPolynomial.aeval_X]

end Lift

/-! ### Lifting a formula and the evaluation bridge -/

section Bridge

variable {k N : ℕ} {F : Type*} [CommRing F]
  {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra F R] [DecidableEq R]

/-- Lift an atom: replace its `R`-coefficient polynomial by the `F`-lift. -/
noncomputable def liftAtom (A : Finset R) (Xembed : Fin k → Fin N)
    (Yembed : Fin A.card → Fin N) (a : OrderedFieldAtom (Fin k) R) :
    OrderedFieldAtom (Fin N) F :=
  ⟨polyLift (F := F) A Xembed Yembed a.poly, a.rel⟩

/-- Lift a whole formula: rename variables by `Xembed` and lift each atom. -/
noncomputable def liftForm (A : Finset R) (Xembed : Fin k → Fin N)
    (Yembed : Fin A.card → Fin N)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) :
    Formula (Fin N) (OrderedFieldAtom (Fin N) F) :=
  Φ.rename Xembed (liftAtom A Xembed Yembed)

/-- **The evaluation bridge.** For `w` whose `Y`-coordinates carry the coefficient values
`c`, a point `w` realizes the lifted formula `Ψ` over `R` iff its `X`-coordinate part
`w ∘ Xembed` realizes the original `Φ`. The coefficient substitution is undone exactly by
`polyLift_eval`. -/
theorem liftForm_bridge (A : Finset R) (Xembed : Fin k → Fin N) (Yembed : Fin A.card → Fin N)
    (w : Fin N → R) (hw : ∀ j, w (Yembed j) = coeffEnum A j)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) :
    Φ.IsQuantifierFree → Formula.coeffSet Φ ⊆ A →
    (w ∈ (liftForm (F := F) A Xembed Yembed Φ).realization (C := R) ↔
      (fun i => w (Xembed i)) ∈ Φ.realization (C := R)) := by
  induction Φ with
  | atom a =>
    intro _ hA
    obtain ⟨P, rel⟩ := a
    have hPA : ∀ α ∈ P.support, P.coeff α ∈ A := by
      intro α hα
      exact hA (by rw [Formula.coeffSet]; exact Finset.mem_image.mpr ⟨α, hα, rfl⟩)
    have heval : MvPolynomial.aeval w (polyLift (F := F) A Xembed Yembed P) =
        MvPolynomial.aeval (fun i => w (Xembed i)) P :=
      polyLift_eval A Xembed Yembed w hw P hPA
    cases rel <;>
      simp only [liftForm, liftAtom, Formula.rename, Formula.realization,
        AtomRealization.interpret, Set.mem_ofPred_eq, heval]
  | not Φ ih =>
    intro hqf hA
    simp only [liftForm, Formula.rename, Formula.realization, Set.mem_compl_iff]
    rw [show Φ.rename Xembed (liftAtom A Xembed Yembed) =
      liftForm A Xembed Yembed Φ from rfl, ih hqf hA]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf hA
    rw [Formula.coeffSet, Finset.union_subset_iff] at hA
    simp only [liftForm, Formula.rename, Formula.realization, Set.mem_inter_iff]
    rw [show Φ₁.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₁ from rfl,
      show Φ₂.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₂ from rfl,
      ih₁ hqf.1 hA.1, ih₂ hqf.2 hA.2]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf hA
    rw [Formula.coeffSet, Finset.union_subset_iff] at hA
    simp only [liftForm, Formula.rename, Formula.realization, Set.mem_union]
    rw [show Φ₁.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₁ from rfl,
      show Φ₂.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₂ from rfl,
      ih₁ hqf.1 hA.1, ih₂ hqf.2 hA.2]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf hA
    rw [Formula.coeffSet, Finset.union_subset_iff] at hA
    simp only [liftForm, Formula.rename, Formula.realization, Set.mem_union, Set.mem_compl_iff]
    rw [show Φ₁.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₁ from rfl,
      show Φ₂.rename Xembed (liftAtom A Xembed Yembed) =
        liftForm A Xembed Yembed Φ₂ from rfl,
      ih₁ hqf.1 hA.1, ih₂ hqf.2 hA.2]
  | exists_ x Φ _ => intro hqf _; exact absurd hqf id
  | forall_ x Φ _ => intro hqf _; exact absurd hqf id

end Bridge

/-! ### Descent `Fin N → Fin k`: setting the auxiliary coordinates to `0`

After quantifier elimination we have a quantifier-free formula over `Fin N` whose
realization is the cylinder over `S`. Substituting `0` for the auxiliary coordinates
(`k, …, N-1`) and keeping the first `k` recovers a quantifier-free formula over `Fin k`
realizing `S`. -/

section Descent

variable {k N : ℕ} {F : Type*} [CommRing F]
  {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra F R]

/-- Extend `x : Fin k → R` to `Fin N → R` by `0` on the auxiliary coordinates. -/
def extendZero (x : Fin k → R) : Fin N → R :=
  fun j => if h : (j : ℕ) < k then x ⟨j, h⟩ else 0

/-- Substitute the auxiliary variables `X_k, …, X_{N-1}` by `0`. -/
noncomputable def descPoly (Q : MvPolynomial (Fin N) F) : MvPolynomial (Fin k) F :=
  MvPolynomial.aeval
    (fun j : Fin N => if h : (j : ℕ) < k then MvPolynomial.X ⟨j, h⟩ else 0) Q

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem aeval_descPoly (x : Fin k → R) (Q : MvPolynomial (Fin N) F) :
    MvPolynomial.aeval x (descPoly Q) = MvPolynomial.aeval (extendZero x) Q := by
  rw [descPoly]
  have h : (MvPolynomial.aeval x).comp
        (MvPolynomial.aeval (R := F)
          (fun j : Fin N => if h : (j : ℕ) < k then MvPolynomial.X ⟨j, h⟩ else 0))
      = MvPolynomial.aeval (R := F) (extendZero x) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, extendZero]
    split <;> simp [MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h Q

/-- Descend a formula from `Fin N` to `Fin k` by setting auxiliary variables to `0`.
Quantifier cases are junk (never used: applied only to quantifier-free formulas). -/
noncomputable def descForm :
    Formula (Fin N) (OrderedFieldAtom (Fin N) F) → Formula (Fin k) (OrderedFieldAtom (Fin k) F)
  | .atom a => .atom ⟨descPoly a.poly, a.rel⟩
  | .not Φ => .not (descForm Φ)
  | .and Φ₁ Φ₂ => .and (descForm Φ₁) (descForm Φ₂)
  | .or Φ₁ Φ₂ => .or (descForm Φ₁) (descForm Φ₂)
  | .implies Φ₁ Φ₂ => .implies (descForm Φ₁) (descForm Φ₂)
  | .exists_ _ _ => Formula.eqZeroO 0
  | .forall_ _ _ => Formula.eqZeroO 0

theorem descForm_isQF (Φ : Formula (Fin N) (OrderedFieldAtom (Fin N) F)) :
    Φ.IsQuantifierFree → (descForm (k := k) Φ).IsQuantifierFree := by
  induction Φ with
  | atom a => intro _; exact trivial
  | not Φ ih => intro hqf; exact ih hqf
  | and Φ₁ Φ₂ ih₁ ih₂ => intro hqf; exact ⟨ih₁ hqf.1, ih₂ hqf.2⟩
  | or Φ₁ Φ₂ ih₁ ih₂ => intro hqf; exact ⟨ih₁ hqf.1, ih₂ hqf.2⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ => intro hqf; exact ⟨ih₁ hqf.1, ih₂ hqf.2⟩
  | exists_ x Φ _ => intro hqf; exact absurd hqf id
  | forall_ x Φ _ => intro hqf; exact absurd hqf id

/-- **Descent bridge.** For a quantifier-free formula `Φ` over `Fin N`, a point
`x : Fin k → R` realizes the descended formula iff its `0`-extension realizes `Φ`. -/
theorem descForm_bridge (x : Fin k → R)
    (Φ : Formula (Fin N) (OrderedFieldAtom (Fin N) F)) :
    Φ.IsQuantifierFree →
    (x ∈ (descForm Φ).realization (C := R) ↔
      extendZero x ∈ Φ.realization (C := R)) := by
  induction Φ with
  | atom a =>
    intro _
    obtain ⟨P, rel⟩ := a
    cases rel <;>
      simp only [descForm, Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq,
        aeval_descPoly]
  | not Φ ih =>
    intro hqf
    simp only [descForm, Formula.realization, Set.mem_compl_iff, ih hqf]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    simp only [descForm, Formula.realization, Set.mem_inter_iff, ih₁ hqf.1, ih₂ hqf.2]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    simp only [descForm, Formula.realization, Set.mem_union, ih₁ hqf.1, ih₂ hqf.2]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    simp only [descForm, Formula.realization, Set.mem_union, Set.mem_compl_iff,
      ih₁ hqf.1, ih₂ hqf.2]
  | exists_ x Φ _ => intro hqf; exact absurd hqf id
  | forall_ x Φ _ => intro hqf; exact absurd hqf id

end Descent

/-! ### BPR Proposition 2.82 -/

section Proposition

open Formula

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable [Algebra F R]

set_option linter.unusedSectionVars false in
/-- **BPR Proposition 2.82.** Let `F` be an ordered field and `R` its real closure (here:
`R` real closed, algebraic over `F`, with `F → R` order-preserving). Every semialgebraic
set `S ⊆ Rᵏ` is the realization of a quantifier-free formula with coefficients in `F`.

Following BPR: a quantifier-free `Φ` over `R` defines `S`; each `R`-coefficient `a` is
algebraic over `F` and pinned by the `F`-formula `∆_a` (`deltaForm`); replacing the
coefficients by fresh universally quantified variables (`liftForm`) and conjoining the
`∆`-constraints gives an `F`-formula `∀Y (⋀_a ∆_a(Y_a) ⇒ Ψ(X,Y))` realizing the cylinder
over `S`; Theorem 2.77 makes it quantifier-free, and setting the auxiliary variables to `0`
(`descForm`) descends it to `Fin k`. -/
theorem proposition_2_82 (halg : Algebra.IsAlgebraic F R) (hmono : StrictMono (algebraMap F R))
    {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) F), Φ.IsQuantifierFree ∧
      S = Φ.realization (C := R) := by
  classical
  have hinj : Function.Injective (algebraMap F R) := hmono.injective
  have : Algebra.IsIntegral F R := halg.isIntegral
  -- Step A: a quantifier-free formula over `R` defining `S`.
  obtain ⟨Φ_R, hΦR_qf, hSΦ⟩ := semialgebraic_isQFRealizable S hS
  set A : Finset R := Formula.coeffSet Φ_R with hA_def
  set n : ℕ := A.card with hn_def
  set a : Fin n → R := coeffEnum A with ha_def
  -- For each coefficient, its minimal polynomial and root data.
  set P : Fin n → F[X] := fun j => minpoly F (a j) with hP_def
  have hP : ∀ j, P j ≠ 0 := fun j => minpoly.ne_zero (Algebra.IsIntegral.isIntegral (a j))
  have hPa : ∀ j, Polynomial.aeval (a j) (P j) = 0 := fun j => minpoly.aeval F (a j)
  set ℓ : Fin n → ℕ := fun j => ((P j).map (algebraMap F R)).roots.toFinset.card with hℓ_def
  have hmapne : ∀ j, (P j).map (algebraMap F R) ≠ 0 :=
    fun j => (Polynomial.map_ne_zero_iff hinj).mpr (hP j)
  have ha_mem : ∀ j, a j ∈ ((P j).map (algebraMap F R)).roots.toFinset := by
    intro j
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmapne j), Polynomial.IsRoot.def,
      show Polynomial.eval (a j) ((P j).map (algebraMap F R)) = Polynomial.aeval (a j) (P j) from by
        rw [Polynomial.aeval_def, Polynomial.eval_map]]
    exact hPa j
  have hjdx_ex : ∀ j, ∃ t : Fin (ℓ j),
      ((P j).map (algebraMap F R)).roots.toFinset.orderEmbOfFin rfl t = a j := by
    intro j
    have hmem : a j ∈ Set.range ⇑(((P j).map (algebraMap F R)).roots.toFinset.orderEmbOfFin
        (rfl : _ = ℓ j)) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr (ha_mem j)
    exact hmem
  choose jdx hjdx_eq using hjdx_ex
  -- Coordinate layout in `Fin N`.
  set L : ℕ := Finset.univ.sup ℓ with hL_def
  have hℓL : ∀ j, ℓ j ≤ L := fun j => Finset.le_sup (Finset.mem_univ j)
  set N : ℕ := k + n + (L + 1) with hN_def
  set Xembed : Fin k → Fin N := fun i => ⟨i, by omega⟩ with hXe
  set Yembed : Fin n → Fin N := fun j => ⟨k + (j : ℕ), by omega⟩ with hYe
  set rc : ∀ j, Fin (ℓ j) → Fin N := fun j t => ⟨k + n + (t : ℕ), by have := hℓL j; omega⟩ with hrce
  set xc : Fin n → Fin N := fun j => ⟨k + n + L, by omega⟩ with hxce
  -- Coordinate values and distinctness.
  have hXval : ∀ i, (Xembed i : ℕ) = i := fun _ => rfl
  have hYval : ∀ j, (Yembed j : ℕ) = k + j := fun _ => rfl
  have hrcval : ∀ j t, (rc j t : ℕ) = k + n + t := fun _ _ => rfl
  have hxcval : ∀ j, (xc j : ℕ) = k + n + L := fun _ => rfl
  have hrc_inj : ∀ j, Function.Injective (rc j) := by
    intro j t t' h
    rw [Fin.ext_iff, hrcval j t, hrcval j t'] at h
    exact Fin.ext (by omega)
  have hxc_rc : ∀ j t, rc j t ≠ xc j := by
    intro j t h
    rw [Fin.ext_iff, hrcval j t, hxcval j] at h
    have hb := hℓL j; have ht := t.isLt; omega
  have hy0_rc : ∀ j t, rc j t ≠ Yembed j := by
    intro j t h
    rw [Fin.ext_iff, hrcval j t, hYval j] at h
    have hb := j.isLt; omega
  have hYinj : Function.Injective Yembed := by
    intro j j' h
    rw [Fin.ext_iff, hYval j, hYval j'] at h
    exact Fin.ext (by omega)
  have hX_notY : ∀ i j, Xembed i ≠ Yembed j := by
    intro i j h
    rw [Fin.ext_iff, hXval i, hYval j] at h
    have hb := i.isLt; omega
  -- The lifted body `Ψ`, the `∆`-conjunction, the implication, and the big `∀`-formula.
  set Ψ : Formula (Fin N) (OrderedFieldAtom (Fin N) F) := liftForm A Xembed Yembed Φ_R with hΨ_def
  set Δhat : Fin n → Formula (Fin N) (OrderedFieldAtom (Fin N) F) :=
    fun j => Formula.deltaForm (P j) (rc j) (xc j) (Yembed j) (jdx j) with hΔhat
  have hΔ : ∀ j, (Δhat j).realization (C := R) = {z : Fin N → R | z (Yembed j) = a j} := by
    intro j
    rw [hΔhat, Formula.deltaForm_realization (P j) (hP j) hinj (rc j) (xc j) (Yembed j)
      (jdx j) rfl (hrc_inj j) (hxc_rc j) (hy0_rc j), hjdx_eq j]
  -- `⋀ ∆_a` realizes to the assignments carrying the coefficient values.
  have hconj : (Formula.conjListO (List.ofFn Δhat)).realization (C := R) =
      {v : Fin N → R | ∀ j, v (Yembed j) = a j} := by
    rw [Formula.realization_conjListO]
    ext v
    simp only [Set.mem_ofPred_eq, List.forall_mem_ofFn_iff]
    exact forall_congr' (fun j => by rw [hΔ j]; rfl)
  set body : Formula (Fin N) (OrderedFieldAtom (Fin N) F) :=
    Formula.implies (Formula.conjListO (List.ofFn Δhat)) Ψ with hbody_def
  set bigΦ : Formula (Fin N) (OrderedFieldAtom (Fin N) F) :=
    Formula.forallList (List.ofFn Yembed) body with hbigΦ_def
  -- The bridge for assignments carrying the coefficient values.
  have hbridge : ∀ v : Fin N → R, (∀ j, v (Yembed j) = a j) →
      (v ∈ Ψ.realization (C := R) ↔ (fun i => v (Xembed i)) ∈ Φ_R.realization (C := R)) := by
    intro v hv
    exact liftForm_bridge A Xembed Yembed v hv Φ_R hΦR_qf subset_rfl
  have hbody_mem : ∀ v : Fin N → R, v ∈ body.realization (C := R) ↔
      ((∀ j, v (Yembed j) = a j) → v ∈ Ψ.realization (C := R)) := by
    intro v
    rw [hbody_def]
    show v ∈ (_ᶜ ∪ _) ↔ _
    rw [Set.mem_union, Set.mem_compl_iff, hconj]
    simp only [Set.mem_ofPred_eq]
    tauto
  -- The big formula realizes to the cylinder over `Φ_R`.
  set zc : (Fin N → R) → (Fin N → R) :=
    fun z s => if h : ∃ j, Yembed j = s then a h.choose else z s with hzc_def
  have hzc_Y : ∀ z j, zc z (Yembed j) = a j := by
    intro z j
    show (if h : ∃ j', Yembed j' = Yembed j then a h.choose else z (Yembed j)) = a j
    rw [dite_eq_left ⟨j, rfl⟩]
    congr 1
    exact hYinj (Exists.choose_spec (⟨j, rfl⟩ : ∃ j', Yembed j' = Yembed j))
  have hzc_X : ∀ z i, zc z (Xembed i) = z (Xembed i) := by
    intro z i
    show (if h : ∃ j, Yembed j = Xembed i then a h.choose else z (Xembed i)) = z (Xembed i)
    rw [dite_eq_right]; rintro ⟨j, hj⟩; exact hX_notY i j hj.symm

  have hcyl : bigΦ.realization (C := R) =
      {z : Fin N → R | (fun i => z (Xembed i)) ∈ Φ_R.realization (C := R)} := by
    rw [hbigΦ_def, Formula.realization_forallList]
    ext z
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have hzcoff : ∀ s ∉ List.ofFn Yembed, zc z s = z s := by
        intro s hs
        show (if h : ∃ j, Yembed j = s then a h.choose else z s) = z s
        rw [dite_eq_right]; rintro ⟨j, hj⟩; exact hs (List.mem_ofFn.mpr ⟨j, hj⟩)
      have hzcbody := h (zc z) hzcoff
      rw [hbody_mem] at hzcbody
      have := hzcbody (fun j => hzc_Y z j)
      rw [hbridge (zc z) (fun j => hzc_Y z j)] at this
      simp only [hzc_X] at this
      exact this
    · intro hzS v hvoff
      rw [hbody_mem]
      intro hvY
      rw [hbridge v hvY]
      have hvX : ∀ i, v (Xembed i) = z (Xembed i) := by
        intro i
        exact hvoff (Xembed i) (by
          rw [List.mem_ofFn]; rintro ⟨j, hj⟩; exact hX_notY i j hj.symm)
      simp only [hvX]
      exact hzS
  -- Quantifier elimination over `F`, then descend to `Fin k`.
  obtain ⟨Ψ', hΨ'_qf, hΨ'_eq⟩ := theorem_2_77 (D := F) hinj bigΦ
  refine ⟨descForm Ψ', descForm_isQF Ψ' hΨ'_qf, ?_⟩
  ext x
  have hext : (fun i => extendZero x (Xembed i)) = x := by
    funext i
    show (if h : (Xembed i : ℕ) < k then x ⟨Xembed i, h⟩ else 0) = x i
    rw [dite_eq_left (by rw [hXval]; exact i.isLt)]
  rw [hSΦ, descForm_bridge x Ψ' hΨ'_qf, ← hΨ'_eq, hcyl]
  show x ∈ Φ_R.realization (C := R) ↔
    (fun i => extendZero x (Xembed i)) ∈ Φ_R.realization (C := R)
  rw [hext]

end Proposition

end Azurite.BPR
