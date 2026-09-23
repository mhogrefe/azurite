/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Corollary_2_79
import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction

/-! # BPR Proposition 2.86

Let `S ⊆ R` be a semialgebraic set and `φ : S → R` a semialgebraic function. There is a
nonzero polynomial `P ∈ R[X, Y]` with `P(x, φ(x)) = 0` for every `x ∈ S`.

The graph `Γ` of `φ` is a finite union of basic semialgebraic cells
`{(x, y) | Pᵢ(x, y) = 0 ∧ ⋀ⱼ Qᵢⱼ(x, y) > 0}`. Each `Pᵢ` is *not* identically zero: otherwise
the cell would be `{⋀ Qᵢⱼ > 0}`, whose fiber over a point `x` is a nonempty positivity locus
in `R` and hence contains an interval (two distinct points), contradicting that `Γ`, being a
graph, meets each vertical line in at most one point. Take `P = ∏ Pᵢ`.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The point `(x, y) ∈ R²`. -/
def pt (x y : R) : Fin 2 → R := fun i => if i = 0 then x else y

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem pt_zero (x y : R) : pt x y 0 = x := ite_eq_left rfl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem pt_one (x y : R) : pt x y 1 = y := ite_eq_right (by decide)

/-- The univariate slice `q(x, ·) ∈ R[Y]` of a bivariate polynomial at `X = x`. -/
noncomputable def slice (q : MvPolynomial (Fin 2) R) (x : R) : Polynomial R :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.C x else Polynomial.X) q

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem slice_eval (q : MvPolynomial (Fin 2) R) (x y : R) :
    Polynomial.eval y (slice q x) = MvPolynomial.eval (pt x y) q := by
  show Polynomial.eval y (slice q x) = MvPolynomial.aeval (pt x y) q
  rw [slice]
  have h : (MvPolynomial.aeval (pt x y) : MvPolynomial (Fin 2) R →ₐ[R] R)
      = (Polynomial.aeval y).comp (MvPolynomial.aeval
          (fun i : Fin 2 => if i = 0 then Polynomial.C x else Polynomial.X)) := by
    apply MvPolynomial.algHom_ext
    intro i; fin_cases i <;> simp [pt]
  rw [congrFun (congrArg DFunLike.coe h) q]
  simp

variable [IsRealClosed R]

/-- **The fiber sub-lemma.** If at `(x, y₀)` all the polynomials of a finset `Q₀` are
positive, then there are two distinct `y₁ ≠ y₂` at which all of `Q₀` is still positive at `x`:
a nonempty positivity locus contains an interval. -/
theorem cell_fiber_two_points (Q₀ : Finset (MvPolynomial (Fin 2) R)) (x y₀ : R)
    (hy₀ : ∀ q ∈ Q₀, 0 < MvPolynomial.eval (pt x y₀) q) :
    ∃ y₁ y₂ : R, y₁ ≠ y₂ ∧
      (∀ q ∈ Q₀, 0 < MvPolynomial.eval (pt x y₁) q) ∧
      (∀ q ∈ Q₀, 0 < MvPolynomial.eval (pt x y₂) q) := by
  classical
  -- the slices are nonzero polynomials, positive at `y₀`.
  have hslice0 : ∀ q ∈ Q₀, 0 < (slice q x).eval y₀ := fun q hq => by
    rw [slice_eval]; exact hy₀ q hq
  have hsne : ∀ q ∈ Q₀, slice q x ≠ 0 := fun q hq h => by
    have := hslice0 q hq; rw [h] at this; simp at this
  -- the product of the slices, and its roots.
  set Qp : Polynomial R := ∏ q ∈ Q₀, slice q x with hQp
  have hQpne : Qp ≠ 0 := Finset.prod_ne_zero_iff.mpr hsne
  set rs : Finset R := Qp.roots.toFinset with hrs
  have hy₀rs : y₀ ∉ rs := by
    rw [hrs, Multiset.mem_toFinset, Polynomial.mem_roots hQpne, Polynomial.IsRoot.def, hQp,
      Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (hslice0 q hq).ne'
  -- a root-free interval `(a, b)` around `y₀`.
  obtain ⟨a, b, hay, hyb, hgap⟩ :
      ∃ a b, a < y₀ ∧ y₀ < b ∧ ∀ y ∈ Set.Ioo a b, Qp.eval y ≠ 0 := by
    rcases rs.eq_empty_or_nonempty with hrse | hrse
    · refine ⟨y₀ - 1, y₀ + 1, by linarith, by linarith, fun y _ hy0 => ?_⟩
      have : y ∈ rs := by rw [hrs, Multiset.mem_toFinset, Polynomial.mem_roots hQpne]; exact hy0
      rw [hrse] at this; exact absurd this (Finset.notMem_empty y)
    · set δ : R := (rs.image fun r => |r - y₀|).min' (hrse.image _) with hδ
      have hδpos : 0 < δ := by
        rw [hδ, Finset.lt_min'_iff]
        rintro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨r, hr, rfl⟩ := hd
        exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hy₀rs (h ▸ hr)))
      refine ⟨y₀ - δ, y₀ + δ, by linarith, by linarith, fun y hy hy0 => ?_⟩
      have hyr : y ∈ rs := by rw [hrs, Multiset.mem_toFinset, Polynomial.mem_roots hQpne]; exact hy0
      have hle : δ ≤ |y - y₀| := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hyr)
      obtain ⟨h1, h2⟩ := hy
      have hlt : |y - y₀| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
  -- each slice has constant (positive) sign on `(a, b)`.
  have hpos : ∀ q ∈ Q₀, ∀ y ∈ Set.Ioo a b, 0 < (slice q x).eval y := by
    intro q hq y hy
    have hrf : ∀ z ∈ Set.Ioo a b, (slice q x).eval z ≠ 0 := by
      intro z hz hz0
      refine hgap z hz ?_
      rw [hQp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hq hz0
    rcases const_sign_ordConnected Set.ordConnected_Ioo (slice q x) hrf with hp | hn
    · exact hp y hy
    · exact absurd (hslice0 q hq) (not_lt.mpr (le_of_lt (hn y₀ ⟨hay, hyb⟩)))
  -- two distinct points in `(a, b)`.
  obtain ⟨y₁, hay₁, hy₁0⟩ := exists_between hay
  obtain ⟨y₂, h0y₂, hy₂b⟩ := exists_between hyb
  refine ⟨y₁, y₂, by linarith, ?_, ?_⟩
  · intro q hq; rw [← slice_eval]; exact hpos q hq y₁ ⟨hay₁, by linarith⟩
  · intro q hq; rw [← slice_eval]; exact hpos q hq y₂ ⟨by linarith, hy₂b⟩

/-- **The recursion.** For a finite union of basic cells contained in a "graph" `Γ` (vertical
line test), there is a nonzero polynomial vanishing on it: cells with `Pᵢ = 0` are empty (the
fiber sub-lemma), and the product of the `Pᵢ` of the others works. -/
theorem exists_poly_vanishing_of_finUnion (Γ : Set (Fin 2 → R))
    (hΓ : ∀ z ∈ Γ, ∀ z' ∈ Γ, z 0 = z' 0 → z 1 = z' 1)
    {V : Set (Fin 2 → R)} (hV : IsFinUnionOfBasic V) :
    V ⊆ Γ → ∃ P : MvPolynomial (Fin 2) R, P ≠ 0 ∧ ∀ z ∈ V, MvPolynomial.eval z P = 0 := by
  induction hV with
  | empty => intro _; exact ⟨1, one_ne_zero, fun z hz => absurd hz (Set.notMem_empty z)⟩
  | @basic B hB =>
    intro hVΓ
    obtain ⟨P0, Q0, rfl⟩ := hB
    by_cases hP0 : P0 = 0
    · refine ⟨1, one_ne_zero, fun z hz => ?_⟩
      exfalso
      obtain ⟨_, hzQ⟩ := hz
      have hzpt : z = pt (z 0) (z 1) := by funext i; fin_cases i <;> simp [pt]
      have hQ0pos : ∀ q ∈ Q0, 0 < MvPolynomial.eval (pt (z 0) (z 1)) q := by
        intro q hq; rw [← hzpt]; exact hzQ q hq
      obtain ⟨y₁, y₂, hne, hp1, hp2⟩ := cell_fiber_two_points Q0 (z 0) (z 1) hQ0pos
      have hm1 : pt (z 0) y₁ ∈ {z | MvPolynomial.eval z P0 = 0 ∧ ∀ q ∈ Q0, MvPolynomial.eval z q > 0} :=
        ⟨by rw [hP0]; simp, hp1⟩
      have hm2 : pt (z 0) y₂ ∈ {z | MvPolynomial.eval z P0 = 0 ∧ ∀ q ∈ Q0, MvPolynomial.eval z q > 0} :=
        ⟨by rw [hP0]; simp, hp2⟩
      have hyy := hΓ (pt (z 0) y₁) (hVΓ hm1) (pt (z 0) y₂) (hVΓ hm2) (by simp)
      simp only [pt_one] at hyy
      exact hne hyy
    · exact ⟨P0, hP0, fun z hz => hz.1⟩
  | @union V W _ _ ihV ihW =>
    intro hVΓ
    obtain ⟨PV, hPVne, hPV⟩ := ihV (fun z hz => hVΓ (Set.mem_union_left _ hz))
    obtain ⟨PW, hPWne, hPW⟩ := ihW (fun z hz => hVΓ (Set.mem_union_right _ hz))
    refine ⟨PV * PW, mul_ne_zero hPVne hPWne, fun z hz => ?_⟩
    rcases hz with hz | hz
    · rw [map_mul, hPV z hz, zero_mul]
    · rw [map_mul, hPW z hz, mul_zero]

/-- **BPR Proposition 2.86.** Let `S ⊆ R` be semialgebraic and `φ : S → R` a semialgebraic
function. There is a nonzero polynomial `P ∈ R[X, Y]` with `P(x, φ(x)) = 0` for every
`x ∈ S`. -/
theorem proposition_2_86 {S : Set (Fin 1 → R)} {ϕ : (Fin 1 → R) → (Fin 1 → R)}
    (hϕ : IsSemialgebraicFunction S ϕ) :
    ∃ P : MvPolynomial (Fin 2) R, P ≠ 0 ∧
      ∀ x ∈ S, MvPolynomial.eval (pt (x 0) (ϕ x 0)) P = 0 := by
  have hc0 : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hn0 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  -- the graph is a graph (vertical line test).
  have hΓ : ∀ z ∈ funGraph S ϕ, ∀ z' ∈ funGraph S ϕ, z 0 = z' 0 → z 1 = z' 1 := by
    intro z hz z' hz' hx
    rw [mem_funGraph] at hz hz'
    have hxx : z ∘ Fin.castAdd 1 = z' ∘ Fin.castAdd 1 := by
      funext i; rw [Subsingleton.elim i 0]
      show z (Fin.castAdd 1 0) = z' (Fin.castAdd 1 0); rw [hc0]; exact hx
    have hyy : z ∘ Fin.natAdd 1 = z' ∘ Fin.natAdd 1 := by rw [hz.2, hxx, ← hz'.2]
    have := congrFun hyy 0
    rw [Function.comp_apply, hn0, Function.comp_apply, hn0] at this
    exact this
  obtain ⟨P, hPne, hP⟩ := exists_poly_vanishing_of_finUnion (funGraph S ϕ) hΓ
    (IsFinUnionOfBasic.of_isSemialgebraicSet hϕ) subset_rfl
  refine ⟨P, hPne, fun x hx => ?_⟩
  -- the point `(x, φ x)` is in the graph.
  have hmem : pt (x 0) (ϕ x 0) ∈ funGraph S ϕ := by
    rw [mem_funGraph]
    have hcx : pt (x 0) (ϕ x 0) ∘ Fin.castAdd 1 = x := by
      funext i; rw [Subsingleton.elim i 0]
      show pt (x 0) (ϕ x 0) (Fin.castAdd 1 (0 : Fin 1)) = x 0; rw [hc0, pt_zero]
    refine ⟨by rw [hcx]; exact hx, ?_⟩
    funext i; rw [Subsingleton.elim i 0]
    show pt (x 0) (ϕ x 0) (Fin.natAdd 1 (0 : Fin 1)) = ϕ (pt (x 0) (ϕ x 0) ∘ Fin.castAdd 1) 0
    rw [hn0, pt_one, hcx]
  exact hP _ hmem

end Azurite.BPR
