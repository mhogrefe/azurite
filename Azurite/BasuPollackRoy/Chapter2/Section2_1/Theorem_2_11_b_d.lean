import Azurite.BasuPollackRoy.Chapter2.Section2_1.HasNoNontrivialRealAlgebraicExtension
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c
import Mathlib.FieldTheory.Minpoly.Basic

/-!
# BPR Theorem 2.11 b) => d): R[i] Algebraically Closed => No Non-trivial Real Algebraic Extension

**Theorem 2.11 (b => d) (BPR).** If R is an ordered field and R[i] := R[X]/(X² + 1)
is algebraically closed, then R is a real field with no non-trivial real algebraic
extension.

**Proof strategy.**
1. R is real: automatic since R is an ordered field (IsSemireal instance).
2. R[i] is not real: i² = −1, so −1 is a square.
3. Every irreducible polynomial over R of degree > 1 has degree exactly 2, and
   AdjoinRoot of such a polynomial contains a square root of −1 (hence is not real).
4. If R₁ is algebraic over R and real, every element's minimal polynomial must have
   degree 1 (otherwise we'd embed a non-real extension into R₁). So R₁ = R.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Part 1: R is real (automatic from ordered field) -/

theorem ordered_field_isRealField : Azurite.BPR.IsRealField R :=
  show IsSemireal R from inferInstance

/-! ## Part 2: Irreducible polynomials of degree > 1 have degree 2 -/

/-- A root of p in the range of algebraMap would give a linear factor,
    contradicting irreducibility when deg > 1. -/
theorem root_not_real [IsAlgClosed (Ri R)]
    {p : R[X]} (hp : Irreducible p) (hdeg : 1 < p.natDegree)
    {α : Ri R} (hα : Polynomial.aeval α p = 0)  :
    (Ri.conj R) α ≠ α := by
  intro hconj
  obtain ⟨r, hr⟩ := Ri.conj_fixed_mem_range_ordered α hconj
  have hpr : p.IsRoot r := by
    have : Polynomial.aeval (algebraMap R (Ri R) r) p = 0 := hr ▸ hα
    rw [Polynomial.aeval_algebraMap_apply] at this
    exact (algebraMap R (Ri R)).injective (this.trans (map_zero _).symm)
  have hdvd : (X - C r) ∣ p := dvd_iff_isRoot.mpr hpr
  obtain ⟨q, hq⟩ := hdvd
  rcases hp.isUnit_or_isUnit hq with h | h
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit h) (by simp)
  · have : p.natDegree = (X - C r).natDegree + q.natDegree := by
      rw [hq]; exact Polynomial.natDegree_mul (monic_X_sub_C r).ne_zero (IsUnit.ne_zero h)
    rw [natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit h] at this; omega

/-- If p is irreducible over R with deg(p) > 1 and R[i] is alg closed, then deg(p) = 2. -/
theorem irred_degree_eq_two [IsAlgClosed (Ri R)]
    {p : R[X]} (hp : Irreducible p) (hdeg : 1 < p.natDegree) :
    p.natDegree = 2 := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  -- p.map ι has a root α in R[i]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (p.map (algebraMap R (Ri R))) (by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap R (Ri R)).injective]
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)))
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hα
  have hα_not_real := root_not_real hp hdeg hα
  -- Get the quadratic factor
  obtain ⟨M, hM_monic, hM_deg, hM_map, _⟩ := quad_of_conj_pair α hα_not_real
  have hM_dvd_map : M.map (algebraMap R (Ri R)) ∣ p.map (algebraMap R (Ri R)) := by
    rw [hM_map]; exact conj_pair_dvd_map p α hα hα_not_real
  have hM_dvd : M ∣ p := dvd_of_map_dvd_monic M p hM_monic hM_dvd_map
  obtain ⟨q, hpq⟩ := hM_dvd
  rcases hp.isUnit_or_isUnit hpq with hM_unit | hq_unit
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hM_unit) (by omega)
  · have : p.natDegree = M.natDegree + q.natDegree := by
      rw [hpq]; exact Polynomial.natDegree_mul hM_monic.ne_zero (IsUnit.ne_zero hq_unit)
    rw [hM_deg, Polynomial.natDegree_eq_zero_of_isUnit hq_unit] at this; exact this

/-! ## Part 3: AdjoinRoot of irreducible degree-2 polynomial is not semireal -/

/-- If p is irreducible of degree 2 over R (with R[i] alg closed),
    then AdjoinRoot p contains a square root of −1. -/
theorem adjoinRoot_irred_sq_neg_one [IsAlgClosed (Ri R)]
    {p : R[X]} (hp : Irreducible p) (hdeg : p.natDegree = 2) :
    ∃ j : AdjoinRoot p, j ^ 2 = -1 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  -- p has a root α in R[i]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (p.map (algebraMap R (Ri R))) (by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap R (Ri R)).injective]
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)))
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hα
  -- α is not real
  have hα_not_real := root_not_real hp (by omega) hα
  -- Representation α = ι(a) + ι(b) * i with b ≠ 0
  obtain ⟨a, b, hab⟩ := Ri.repr_exists α
  have hb_ne : b ≠ 0 := by
    intro hb; apply hα_not_real
    rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]
  -- R-algebra hom φ : AdjoinRoot p → Ri R sending root ↦ α
  have hα_aeval : Polynomial.aeval α p = 0 := hα
  let φ : AdjoinRoot p →ₐ[R] Ri R :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId R (Ri R)) α (by rwa [Polynomial.aeval_def] at hα_aeval)
  have hφ_inj : Function.Injective φ := RingHom.injective φ.toRingHom
  -- Construct j = (root - a) / b in AdjoinRoot p
  set r := AdjoinRoot.root p
  set j := (r - algebraMap R (AdjoinRoot p) a) * (algebraMap R (AdjoinRoot p) b)⁻¹
  refine ⟨j, ?_⟩
  -- Show j² = -1 by mapping through φ and using injectivity
  have hφ_r : φ r = α := AdjoinRoot.liftAlgHom_root p _ α _
  have hb_ne' : (algebraMap R (Ri R) b) ≠ 0 := by
    intro h; exact hb_ne ((algebraMap R (Ri R)).injective (h.trans (map_zero _).symm))
  have hφ_j : φ j = Ri.i R := by
    simp only [j, map_mul, map_sub, AlgHom.commutes, map_inv₀, hφ_r, hab]
    rw [add_sub_cancel_left]
    rw [mul_assoc, mul_comm (Ri.i R) _, ← mul_assoc, mul_inv_cancel₀ hb_ne', one_mul]
  apply hφ_inj
  rw [map_pow, map_neg, map_one, hφ_j]
  exact Ri.i_sq R

/-! ## Part 4: No non-trivial real algebraic extension -/

/-- If R₁ is algebraic over R and real, then algebraMap R R₁ is surjective. -/
theorem algebraMap_surjective_of_real_algebraic [IsAlgClosed (Ri R)]
    {R₁ : Type*} [Field R₁] [Algebra R R₁]
    (hAlg : Algebra.IsAlgebraic R R₁) (hReal : Azurite.BPR.IsRealField R₁) :
    Function.Surjective (algebraMap R R₁) := by
  intro x
  -- If x is not in the image, derive contradiction
  by_contra hx; push Not at hx
  have hx_int : IsIntegral R x := (hAlg.isAlgebraic x).isIntegral
  set p := minpoly R x
  have hp_irred : Irreducible p := minpoly.irreducible hx_int
  -- degree > 1 (degree 0 contradicts integrality, degree 1 means x ∈ R)
  have hp_deg : 1 < p.natDegree := by
    by_contra h; push Not at h
    have h0 : 0 < p.natDegree := minpoly.natDegree_pos hx_int
    have h1 : p.natDegree = 1 := by omega
    have haeval : Polynomial.aeval x p = 0 := minpoly.aeval R x
    have hm : p.Monic := minpoly.monic hx_int
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h1)] at haeval
    simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X] at haeval
    have hc1 : p.coeff 1 = 1 := by
      have := hm.leadingCoeff; rwa [Polynomial.leadingCoeff, h1] at this
    simp [hc1, map_one] at haeval
    -- haeval : x + (algebraMap R R₁) (p.coeff 0) = 0
    have : x = (algebraMap R R₁) (-(p.coeff 0)) := by
      simp only [map_neg]; linear_combination haeval
    exact hx _ this.symm
  -- degree = 2 by Part 2
  have hp_deg2 := irred_degree_eq_two hp_irred hp_deg
  -- AdjoinRoot p has j² = -1
  obtain ⟨j, hj_sq⟩ := adjoinRoot_irred_sq_neg_one hp_irred hp_deg2
  -- Map j into R₁ via ψ : AdjoinRoot p →ₐ[R] R₁
  haveI : Fact (Irreducible p) := ⟨hp_irred⟩
  let ψ : AdjoinRoot p →ₐ[R] R₁ :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId R R₁) x (minpoly.aeval R x)
  -- ψ(j)² = ψ(j²) = ψ(-1) = -1 in R₁
  have : (ψ j) ^ 2 = -1 := by
    have := congr_arg ψ hj_sq
    simp [map_pow, map_neg, map_one] at this; exact this
  -- So -1 is a square in R₁, contradicting R₁ being real
  have hsq : ψ j * ψ j = -1 := by rw [← sq]; exact this
  have hIsSquare : IsSquare (-1 : R₁) := ⟨ψ j, hsq.symm⟩
  exact (Azurite.BPR.isRealField_iff R₁).mp hReal hIsSquare.isSumSq

/-! ## Part 5: Main theorem -/

/-- **BPR Theorem 2.11 (b => d).** If R[i] is algebraically closed,
    then R is a real field with no non-trivial real algebraic extension. -/
theorem theorem_2_11_b_d [IsAlgClosed (Ri R)] :
    Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R :=
  ⟨ordered_field_isRealField, fun _ _ _ hAlg hReal =>
    algebraMap_surjective_of_real_algebraic hAlg hReal⟩

end Azurite.BPR.Theorem2_11
