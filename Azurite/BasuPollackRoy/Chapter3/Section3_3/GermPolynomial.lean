import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula
import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGermField
import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGermOrdered
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # BPR §3.3 — lifting a polynomial over germs to a bivariate representative

For the intermediate value property over the germ field one starts with a polynomial
`P ∈ (SemialgGerm R)[Y]`, picks representatives of its (finitely many) coefficient germs on a common
interval `(0, t₀)`, and obtains a polynomial `Q` whose coefficients are semialgebraic continuous
functions on `(0, t₀)` — exactly the data of the §3.3 framework (`HasSemialgContinuousCoeffs`).

This file provides that lift: `exists_germPoly_rep` produces `t₀ > 0` and such a `Q`, with every
lifted coefficient function representing the original germ coefficient. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Common interval of definition for the coefficients of a germ polynomial.** Given
`P ∈ (SemialgGerm R)[Y]`, there is an interval `(0, t₀)` and a polynomial `Q` with semialgebraic
continuous coefficients on `(0, t₀)` such that each coefficient function `Q.coeff i` represents the
germ `P.coeff i`. -/
theorem exists_germPoly_rep (P : Polynomial (SemialgGerm R)) :
    ∃ (t₀ : R) (ht₀ : 0 < t₀) (Q : Polynomial ((Fin 1 → R) → R))
      (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q),
      (∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i) ∧
        Q.natDegree ≤ P.natDegree := by
  classical
  -- the bivariate lift: i-th coefficient is the canonical representative of `P.coeff i`
  set Q : Polynomial ((Fin 1 → R) → R) :=
    ∑ i ∈ P.support, Polynomial.monomial i (Quotient.out (P.coeff i)).toFun with hQdef
  have hcoeff : ∀ j, Q.coeff j =
      if j ∈ P.support then (Quotient.out (P.coeff j)).toFun else 0 := by
    intro j
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' P.support j fun i => (Quotient.out (P.coeff i)).toFun]
  -- a positive lower bound for the (finitely many) representative bounds
  have hbound : ∃ t₀ : R, 0 < t₀ ∧ ∀ i ∈ P.support, t₀ ≤ (Quotient.out (P.coeff i)).bound := by
    by_cases hne : P.support.Nonempty
    · exact ⟨P.support.inf' hne fun i => (Quotient.out (P.coeff i)).bound,
        (Finset.lt_inf'_iff hne).mpr fun i _ => (Quotient.out (P.coeff i)).bound_pos,
        fun i hi => Finset.inf'_le _ hi⟩
    · refine ⟨1, one_pos, fun i hi => ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact absurd hi (hne ▸ Finset.notMem_empty i)
  obtain ⟨t₀, ht₀, ht₀le⟩ := hbound
  -- the coefficients of `Q` are semialgebraic continuous on `(0, t₀)`
  have hQcont : HasSemialgContinuousCoeffs (rightNbhd t₀) Q := by
    intro j
    rw [hcoeff j]
    by_cases hj : j ∈ P.support
    · rw [if_pos hj]
      exact (Quotient.out (P.coeff j)).isSemialgContinuous.mono
        (isSemialgebraicSet_rightNbhd _) (rightNbhd_subset (ht₀le j hj))
    · rw [if_neg hj]
      exact isSemialgContinuousOn_zero (isSemialgebraicSet_rightNbhd _)
  refine ⟨t₀, ht₀, Q, hQcont, fun j => ?_, ?_⟩
  · by_cases hj : j ∈ P.support
    · -- the lifted coefficient agrees with the canonical representative, hence the same germ
      have hcj : Q.coeff j = (Quotient.out (P.coeff j)).toFun := by rw [hcoeff j, if_pos hj]
      have heqv : (⟨t₀, ht₀, Q.coeff j, hQcont j⟩ : SemialgGermRep R) ≈ Quotient.out (P.coeff j) :=
        ⟨t₀, ht₀, fun s _ _ => congrFun hcj (constPt s)⟩
      rw [Quotient.sound heqv, Quotient.out_eq]
    · -- outside the support both sides are zero
      have hcj : Q.coeff j = 0 := by rw [hcoeff j, if_neg hj]
      rw [Polynomial.notMem_support_iff.mp hj]
      exact Quotient.sound ⟨t₀, ht₀, fun s _ _ => by
        simp only [hcj, SemialgGermRep.zero_toFun]⟩
  · -- the lift has degree at most that of `P`
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hcoeff m, if_neg]
    rw [Polynomial.mem_support_iff, not_not]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hm

end Azurite.BPR

/-! # BPR §3.3 — evaluating a germ polynomial through representatives

Continuing the lift of `GermPolynomialRep.lean`: evaluating a polynomial `P ∈ (SemialgGerm R)[Y]` at
a germ `⟦g⟧` is the germ of the pointwise evaluation `u ↦ P(u, g(u))`.

The clean tool is the ring homomorphism `germHom t ht : (functions semialgebraic-continuous on (0,t))
→+* SemialgGerm R` sending a function to its germ. Since germ addition and multiplication are
pointwise, this is a ring homomorphism, and evaluation commutes with it. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The subring of functions `(Fin 1 → R) → R` that are semialgebraic and continuous on `(0, t)`. -/
def semialgContSubring (t : R) : Subring ((Fin 1 → R) → R) where
  carrier := {c | IsSemialgContinuousOn (rightNbhd t) c}
  zero_mem' := isSemialgContinuousOn_zero (isSemialgebraicSet_rightNbhd t)
  one_mem' := isSemialgContinuousOn_one (isSemialgebraicSet_rightNbhd t)
  add_mem' ha hb := IsSemialgContinuousOn.add (isSemialgebraicSet_rightNbhd t) ha hb
  mul_mem' ha hb := IsSemialgContinuousOn.mul (isSemialgebraicSet_rightNbhd t) ha hb
  neg_mem' ha := IsSemialgContinuousOn.neg (isSemialgebraicSet_rightNbhd t) ha

@[simp] theorem mem_semialgContSubring {t : R} {c : (Fin 1 → R) → R} :
    c ∈ semialgContSubring t ↔ IsSemialgContinuousOn (rightNbhd t) c := Iff.rfl

/-- The ring homomorphism sending a function semialgebraic-continuous on `(0, t)` to its germ. -/
noncomputable def germHom (t : R) (ht : 0 < t) : semialgContSubring t →+* SemialgGerm R where
  toFun c := Quotient.mk _ ⟨t, ht, c.1, c.2⟩
  map_one' := Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩
  map_mul' a b := by
    rw [germ_mk_mul]
    exact Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩
  map_zero' := Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩
  map_add' a b := by
    rw [germ_mk_add]
    exact Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩

theorem germHom_apply {t : R} (ht : 0 < t) (c : semialgContSubring t) :
    germHom t ht c = Quotient.mk _ ⟨t, ht, c.1, c.2⟩ := rfl

/-- The germ of a representative on `(0, t)` is `germHom` of its underlying function. -/
theorem germ_eq_germHom {t : R} (ht : 0 < t) (g : SemialgGermRep R)
    (hg : IsSemialgContinuousOn (rightNbhd t) g.toFun) :
    (Quotient.mk (semialgGermSetoid R) g : SemialgGerm R) = germHom t ht ⟨g.toFun, hg⟩ :=
  Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Evaluating a polynomial over the function ring at a point is the pointwise specialized
evaluation: `(Polynomial.eval c Q) u = (specializeAt Q u).eval (c u)`. -/
theorem eval_pi_apply {k : ℕ} (Q : Polynomial ((Fin k → R) → R)) (c : (Fin k → R) → R)
    (u : Fin k → R) : (Polynomial.eval c Q) u = (specializeAt Q u).eval (c u) := by
  have h := Polynomial.hom_eval₂ Q (RingHom.id ((Fin k → R) → R))
    (Pi.evalRingHom (fun _ : Fin k → R => R) u) c
  rw [RingHom.comp_id] at h
  simp only [Pi.evalRingHom_apply, Polynomial.eval₂_id] at h
  rw [h, specializeAt, ← Polynomial.eval_map]

/-- **Evaluation through representatives.** Given the lift `(t₀, Q)` of a germ polynomial `P` (so each
`Q.coeff i` represents `P.coeff i` on `(0, t₀)`), evaluating `P` at a germ `⟦g⟧` is the germ of the
pointwise evaluation `u ↦ P(u, g(u)) = Polynomial.eval g.toFun Q` on `(0, min t₀ g.bound)`. -/
theorem germPoly_eval {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
    {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
    (hrep : ∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i)
    (g : SemialgGermRep R) :
    ∃ hcont : IsSemialgContinuousOn (rightNbhd (min t₀ g.bound)) (Polynomial.eval g.toFun Q),
      Polynomial.eval (Quotient.mk (semialgGermSetoid R) g) P =
        Quotient.mk _ ⟨min t₀ g.bound, lt_min ht₀ g.bound_pos, Polynomial.eval g.toFun Q, hcont⟩ := by
  set t₁ := min t₀ g.bound with ht₁def
  have ht₁ : 0 < t₁ := lt_min ht₀ g.bound_pos
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  -- lift `Q` into the subring of functions semialgebraic-continuous on `(0, t₁)`
  have hp : (↑Q.coeffs : Set ((Fin 1 → R) → R)) ⊆ semialgContSubring t₁ := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨n, _, rfl⟩ := hc
    exact (hQ n).mono (isSemialgebraicSet_rightNbhd _) (rightNbhd_subset ht₁t₀)
  set Q' := Q.toSubring (semialgContSubring t₁) hp with hQ'def
  -- `g.toFun` lies in the subring
  have hg' : g.toFun ∈ semialgContSubring t₁ :=
    g.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _) (rightNbhd_subset (min_le_right _ _))
  -- `Q'.map germHom = P`
  have hPmap : P = Q'.map (germHom t₁ ht₁) := by
    ext i
    rw [Polynomial.coeff_map, germHom_apply, ← hrep i]
    symm
    exact Quotient.sound ⟨t₁, ht₁, fun s _ _ =>
      congrFun (Polynomial.coeff_toSubring' (p := Q) (T := semialgContSubring t₁) (hp := hp)
        (n := i)) (constPt s)⟩
  -- the underlying function of `Q'.eval ⟨g.toFun⟩` is `Polynomial.eval g.toFun Q`
  have hval : ((Q'.eval ⟨g.toFun, hg'⟩ : semialgContSubring t₁) : (Fin 1 → R) → R)
      = Polynomial.eval g.toFun Q := by
    have h := Polynomial.eval₂_at_apply (p := Q') (Subring.subtype (semialgContSubring t₁))
      (⟨g.toFun, hg'⟩ : semialgContSubring t₁)
    rw [← Polynomial.eval_map, hQ'def, Polynomial.map_toSubring] at h
    exact h.symm
  have hcont : IsSemialgContinuousOn (rightNbhd t₁) (Polynomial.eval g.toFun Q) := by
    rw [← hval]; exact (Q'.eval ⟨g.toFun, hg'⟩).2
  refine ⟨hcont, ?_⟩
  rw [hPmap, germ_eq_germHom ht₁ g hg', Polynomial.eval_map, Polynomial.eval₂_at_apply, germHom_apply]
  exact Quotient.sound ⟨t₁, ht₁, fun s _ _ => congrFun hval (constPt s)⟩

end Azurite.BPR

/-! # BPR §3.3 — pointwise degree and sign for a germ polynomial near `0⁺`

Towards the intermediate value property over the germ field: given a polynomial `P ∈ (SemialgGerm
R)[Y]` with `P(ϕ₁)·P(ϕ₂) < 0` and the lift `(t₀, Q)` of `GermPolynomialRep.lean`, we shrink the
interval so that, pointwise for small `t`, the specialized polynomial `P(t, Y) = specializeAt Q t` has
the same leading coefficient (so the same degree) and `P(t, f₁(t))·P(t, f₂(t)) < 0`.

(The remaining shrinking condition of BPR — `gcd(P(t,·), P'(t,·)) = 1`, i.e. separability of every
fiber — requires the subresultant / signed-remainder machinery and is treated separately.) -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A germ is negative iff its negation is positive. -/
theorem SemialgGerm.lt_zero_iff' {a : SemialgGerm R} : a < 0 ↔ IsPosGerm (-a) := by
  show IsPosGerm (0 - a) ↔ IsPosGerm (-a); rw [zero_sub]

/-- A negative germ is represented by an eventually-negative function. -/
theorem germ_neg_eventually {r : SemialgGermRep R}
    (h : (Quotient.mk (semialgGermSetoid R) r : SemialgGerm R) < 0) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → r.toFun (constPt s) < 0 := by
  rw [SemialgGerm.lt_zero_iff', germ_mk_neg, isPosGerm_mk] at h
  obtain ⟨t, ht, H⟩ := h
  refine ⟨t, ht, fun s hs hst => ?_⟩
  have hH := H s hs hst
  simp only [SemialgGermRep.neg_toFun, Pi.neg_apply] at hH
  linarith

/-- A nonzero germ is represented by an eventually-nonzero function. -/
theorem germ_ne_zero_eventually {r : SemialgGermRep R}
    (h : (Quotient.mk (semialgGermSetoid R) r : SemialgGerm R) ≠ 0) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → r.toFun (constPt s) ≠ 0 := by
  have hr : ¬ r ≈ SemialgGermRep.zero := fun heq => h (Quotient.sound heq)
  obtain ⟨t, ht, _, hne⟩ := r.eventually_nonzero_of_not_equiv_zero hr
  exact ⟨t, ht, hne⟩

/-- **Pointwise sign change.** If `P(ϕ₁)·P(ϕ₂) < 0` over the germ field, then for the representatives
`f₁, f₂` the specialized polynomial `P(t, Y) = specializeAt Q t` satisfies
`P(t, f₁(t))·P(t, f₂(t)) < 0` for all small `t`. -/
theorem germPoly_sign_change {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
    {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
    (hrep : ∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i)
    (f₁ f₂ : SemialgGermRep R)
    (hsign : Polynomial.eval (Quotient.mk (semialgGermSetoid R) f₁) P *
      Polynomial.eval (Quotient.mk (semialgGermSetoid R) f₂) P < 0) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t →
      (specializeAt Q (constPt s)).eval (f₁.toFun (constPt s)) *
        (specializeAt Q (constPt s)).eval (f₂.toFun (constPt s)) < 0 := by
  obtain ⟨h₁, he₁⟩ := germPoly_eval ht₀ hQ hrep f₁
  obtain ⟨h₂, he₂⟩ := germPoly_eval ht₀ hQ hrep f₂
  rw [he₁, he₂, germ_mk_mul] at hsign
  obtain ⟨t, ht, H⟩ := germ_neg_eventually hsign
  refine ⟨t, ht, fun s hs hst => ?_⟩
  have hH := H s hs hst
  simp only [SemialgGermRep.mul_toFun, Pi.mul_apply] at hH
  rw [eval_pi_apply, eval_pi_apply] at hH
  exact hH

/-- **Pointwise nonvanishing of the leading coefficient.** If the germ coefficient `P.coeff i` is
nonzero, then its representative `Q.coeff i` is nonzero for all small `t` — so when `i = deg P`, the
specialized polynomial keeps degree `i`. -/
theorem germPoly_coeff_ne_zero {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
    {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
    (hrep : ∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i)
    (i : ℕ) (hi : P.coeff i ≠ 0) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → (Q.coeff i) (constPt s) ≠ 0 := by
  have h : (Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ : SemialgGerm R) ≠ 0 := by
    rw [hrep i]; exact hi
  exact germ_ne_zero_eventually h

end Azurite.BPR

/-! # BPR §3.3 — fiberwise separability of a germ polynomial

The last shrinking condition of BPR's intermediate-value argument: if `P ∈ (SemialgGerm R)[Y]` is
separable, then for the lift `(t₀, Q)`, the specialized polynomial `P(t, Y) = specializeAt Q t` is
separable for all small `t` — equivalently `gcd(P(t,·), P'(t,·)) = 1`.

Via the **resultant**: `resultant Ps Ps'` (over the subring of functions semialgebraic-continuous on
`(0,t₀)`) is a subring element whose germ is `resultant P̄ P̄' ≠ 0` (separable ⇒ resultant nonzero).
So it is eventually nonzero, and `resultant(P(t,·), P'(t,·)) ≠ 0`, giving coprimality of each fiber. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- In characteristic zero, the derivative drops the degree by exactly one. -/
theorem natDegree_derivative_eq_charZero {K : Type*} [Field K] [CharZero K] {f : Polynomial K}
    (hf : 1 ≤ f.natDegree) : (Polynomial.derivative f).natDegree = f.natDegree - 1 := by
  have hf0 : f ≠ 0 := fun h => by subst h; simp at hf
  refine le_antisymm (Polynomial.natDegree_derivative_le f) (Polynomial.le_natDegree_of_ne_zero ?_)
  rw [Polynomial.coeff_derivative]
  refine mul_ne_zero ?_ ?_
  · rw [Nat.sub_add_cancel hf]; exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  · rw [← Nat.cast_add_one, Nat.sub_add_cancel hf]
    exact Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hf)

/-- **Fiberwise separability.** If `P` is separable, then for the lift `(t₀, Q)` the specialized
polynomial `P(t, Y)` is coprime with its derivative for all small `t`. -/
theorem germPoly_coprime {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
    {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
    (hrep : ∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i)
    (hQdeg : Q.natDegree ≤ P.natDegree) (hp1 : 1 ≤ P.natDegree) (hsep : P.Separable) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t →
      IsCoprime (specializeAt Q (constPt s)) (Polynomial.derivative (specializeAt Q (constPt s))) := by
  classical
  set p := P.natDegree with hpdef
  set q := (Polynomial.derivative P).natDegree with hqdef
  -- lift `Q` into the subring of functions semialgebraic-continuous on `(0, t₀)`
  have hp : (↑Q.coeffs : Set ((Fin 1 → R) → R)) ⊆ semialgContSubring t₀ := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨n, _, rfl⟩ := hc
    exact hQ n
  set Ps := Q.toSubring (semialgContSubring t₀) hp with hPsdef
  -- `Ps.map germHom = P`
  have hPmapG : Ps.map (germHom t₀ ht₀) = P := by
    ext i
    rw [Polynomial.coeff_map, germHom_apply, ← hrep i]
    exact Quotient.sound ⟨t₀, ht₀, fun s _ _ =>
      congrFun (Polynomial.coeff_toSubring' (p := Q) (T := semialgContSubring t₀) (hp := hp)
        (n := i)) (constPt s)⟩
  have hderivG : (Polynomial.derivative Ps).map (germHom t₀ ht₀) = Polynomial.derivative P := by
    rw [← Polynomial.derivative_map, hPmapG]
  -- the resultant over the subring; its germ is `resultant P P' ≠ 0`
  have hres_germ : germHom t₀ ht₀ (Ps.resultant (Polynomial.derivative Ps) p q) = Polynomial.resultant P (Polynomial.derivative P) p q :=
    by rw [← Polynomial.resultant_map_map, hPmapG, hderivG]
  have hres_ne : Polynomial.resultant P (Polynomial.derivative P) p q ≠ 0 := fun h =>
    (Polynomial.resultant_eq_zero_iff.mp h).2 hsep
  -- so the subring resultant is eventually nonzero
  have hgerm_ne : (germHom t₀ ht₀ (Ps.resultant (Polynomial.derivative Ps) p q) : SemialgGerm R) ≠ 0 := by
    rw [hres_germ]; exact hres_ne
  rw [germHom_apply] at hgerm_ne
  obtain ⟨t₁, ht₁, Hres⟩ := germ_ne_zero_eventually hgerm_ne
  -- the leading coefficient is eventually nonzero (so the degree is preserved)
  have hPne : P ≠ 0 := hsep.ne_zero
  have hlead : P.coeff p ≠ 0 := by rw [hpdef]; exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  obtain ⟨t₂, ht₂, Hlead⟩ := germPoly_coeff_ne_zero ht₀ hQ hrep p hlead
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, fun s hs hst => ?_⟩
  have hs1 : s < t₁ := lt_of_lt_of_le hst (min_le_left _ _)
  have hs2 : s < t₂ := lt_of_lt_of_le hst (min_le_right _ _)
  -- degree of the specialized polynomial is `p`
  have hcoeffp : (specializeAt Q (constPt s)).coeff p = (Q.coeff p) (constPt s) := by
    rw [specializeAt, Polynomial.coeff_map, Pi.evalRingHom_apply]
  have hd1 : (specializeAt Q (constPt s)).natDegree = p := by
    refine le_antisymm (le_trans Polynomial.natDegree_map_le hQdeg) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hcoeffp]; exact Hlead s hs hs2
  have hfne : specializeAt Q (constPt s) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hd1; omega
  -- degree of the derivative is `q = p - 1`
  have hqeq : q = p - 1 := by rw [hqdef, hpdef]; exact natDegree_derivative_eq_charZero hp1
  have hd2 : (Polynomial.derivative (specializeAt Q (constPt s))).natDegree = q := by
    rw [hqeq, ← hd1]; exact natDegree_derivative_eq_charZero (by omega)
  -- the fiber resultant is nonzero
  have hresfib : Polynomial.resultant (specializeAt Q (constPt s)) (Polynomial.derivative (specializeAt Q (constPt s))) p q
      ≠ 0 := by
    have hval : (Ps.resultant (Polynomial.derivative Ps) p q).1 (constPt s)
        = Polynomial.resultant (specializeAt Q (constPt s)) (Polynomial.derivative (specializeAt Q (constPt s))) p q := by
      have heval : Ps.map ((Pi.evalRingHom (fun _ : Fin 1 → R => R) (constPt s)).comp
          (Subring.subtype (semialgContSubring t₀))) = specializeAt Q (constPt s) := by
        rw [← Polynomial.map_map, hPsdef, Polynomial.map_toSubring]; rfl
      calc (Ps.resultant (Polynomial.derivative Ps) p q).1 (constPt s)
          = (Pi.evalRingHom (fun _ : Fin 1 → R => R) (constPt s)).comp
              (Subring.subtype (semialgContSubring t₀)) (Ps.resultant (Polynomial.derivative Ps) p q) := rfl
        _ = Polynomial.resultant (specializeAt Q (constPt s)) (Polynomial.derivative (specializeAt Q (constPt s))) p q := by
            rw [← Polynomial.resultant_map_map, heval, ← Polynomial.derivative_map, heval]
    rw [← hval]; exact Hres s hs hs1
  -- nonzero resultant (at the actual degrees) ⇒ coprime
  by_contra hnc
  apply hresfib
  have := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hfne, hnc⟩
  rwa [hd1, hd2] at this

end Azurite.BPR

/-! # BPR §3.3 — each fiber of a germ polynomial has a root in the relevant interval

If `P(ϕ₁)·P(ϕ₂) < 0` over the germ field and `ϕ₁ < ϕ₂`, then for the representatives `f₁, f₂` and all
small `t`, the specialized polynomial `P(t, Y) = specializeAt Q t` has a root in the interval
`(f₁(t), f₂(t))`. This is immediate from the pointwise sign change (`germPoly_sign_change`), the
pointwise order `f₁(t) < f₂(t)`, and the intermediate value property of the real closed field `R`
(`hasIVP_of_isRealClosed`). -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- If `⟦r₁⟧ < ⟦r₂⟧` as germs, then `r₁ < r₂` pointwise near `0⁺`. -/
theorem germ_lt_eventually {r₁ r₂ : SemialgGermRep R}
    (h : (Quotient.mk (semialgGermSetoid R) r₁ : SemialgGerm R) < Quotient.mk _ r₂) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → r₁.toFun (constPt s) < r₂.toFun (constPt s) := by
  have hneg : (Quotient.mk (semialgGermSetoid R) (r₁.add r₂.neg) : SemialgGerm R) < 0 := by
    rw [← germ_mk_add, ← germ_mk_neg, ← sub_eq_add_neg, sub_neg]; exact h
  obtain ⟨t, ht, H⟩ := germ_neg_eventually hneg
  refine ⟨t, ht, fun s hs hst => ?_⟩
  have hH := H s hs hst
  simp only [SemialgGermRep.add_toFun, SemialgGermRep.neg_toFun, Pi.add_apply, Pi.neg_apply] at hH
  linarith

/-- **Each fiber has a root.** If `P(ϕ₁)·P(ϕ₂) < 0` and `ϕ₁ < ϕ₂`, then for all small `t` the
specialized polynomial `P(t, Y)` has a root strictly between `f₁(t)` and `f₂(t)`. -/
theorem germPoly_fiber_root {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
    {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
    (hrep : ∀ i, Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ = P.coeff i)
    (f₁ f₂ : SemialgGermRep R)
    (hlt : (Quotient.mk (semialgGermSetoid R) f₁ : SemialgGerm R) < Quotient.mk _ f₂)
    (hsign : Polynomial.eval (Quotient.mk (semialgGermSetoid R) f₁) P *
      Polynomial.eval (Quotient.mk (semialgGermSetoid R) f₂) P < 0) :
    ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t →
      ∃ y, f₁.toFun (constPt s) < y ∧ y < f₂.toFun (constPt s) ∧
        (specializeAt Q (constPt s)).eval y = 0 := by
  obtain ⟨t₁, ht₁, Hsign⟩ := germPoly_sign_change ht₀ hQ hrep f₁ f₂ hsign
  obtain ⟨t₂, ht₂, Hlt⟩ := germ_lt_eventually hlt
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, fun s hs hst => ?_⟩
  have hsgn := Hsign s hs (lt_of_lt_of_le hst (min_le_left _ _))
  have hflt := Hlt s hs (lt_of_lt_of_le hst (min_le_right _ _))
  exact hasIVP_of_isRealClosed (specializeAt Q (constPt s)) (f₁.toFun (constPt s))
    (f₂.toFun (constPt s)) hflt hsgn

end Azurite.BPR
