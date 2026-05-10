import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c

/-!
# BPR Proposition 2.19: Form of Irreducible Factors

**Proposition 2.19 (BPR).** Let R be a real closed field, P ∈ R[X].
The irreducible factors of P are linear or have the form
(X − c)² + d² = (X − c − id)(X − c + id), d ≠ 0, with c, d ∈ R.

The proof assumes R is an ordered field with R[i] algebraically closed
(which holds for real closed fields by Theorem 2.11).
-/

namespace Azurite.BPR.Proposition2_19

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Proposition 2.19.** Over an ordered field R with R[i] algebraically
    closed, every monic irreducible polynomial is either linear (degree 1) or
    has the form (X − c)² + d² with d ≠ 0. -/
theorem proposition_2_19 [IsAlgClosed (Ri R)]
    {q : R[X]} (hq : Irreducible q) (hm : q.Monic) :
    q.natDegree = 1 ∨ ∃ c d : R, d ≠ 0 ∧ q = (X - C c) ^ 2 + C (d ^ 2) := by
  -- Case 1: degree ≤ 1
  by_cases h1 : q.natDegree ≤ 1
  · left
    have h0 : 0 < q.natDegree := Irreducible.natDegree_pos hq
    omega
  · right
    push Not at h1
    -- Root α in R[i] (R[i] is algebraically closed)
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (q.map (algebraMap R (Ri R))) (by
      rw [degree_map_eq_of_injective (algebraMap R (Ri R)).injective]
      exact ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
    rw [IsRoot, eval_map, ← aeval_def] at hα
    -- α is not real (conj α ≠ α), otherwise (X - r) | q contradicts deg > 1
    have hα_ne : (Ri.conj R) α ≠ α := by
      intro hconj
      obtain ⟨r, hr⟩ := Ri.conj_fixed_mem_range_ordered α hconj
      have hpr : q.IsRoot r := by
        have : aeval (algebraMap R (Ri R) r) q = 0 := hr ▸ hα
        rw [aeval_algebraMap_apply] at this
        exact (algebraMap R (Ri R)).injective (this.trans (map_zero _).symm)
      obtain ⟨w, hw⟩ := dvd_iff_isRoot.mpr hpr
      rcases hq.isUnit_or_isUnit hw with h | h
      · exact absurd (natDegree_eq_zero_of_isUnit h) (by simp)
      · have := hw ▸ natDegree_mul (monic_X_sub_C r).ne_zero (IsUnit.ne_zero h)
        rw [natDegree_X_sub_C, natDegree_eq_zero_of_isUnit h] at this; omega
    -- Decompose α = ι(a) + ι(b) · i with b ≠ 0
    obtain ⟨a, b, hab⟩ := Azurite.BPR.Ri.repr_exists α
    have hb_ne : b ≠ 0 := by
      intro hb; apply hα_ne
      rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]
    -- Build M = (X - C a)² + C(b²)
    set M := (X - C a) ^ 2 + C (b ^ 2) with hM_def
    -- M is monic of degree 2
    have h_sq_deg : ((X - C a) ^ 2 : R[X]).natDegree = 2 := by
      simp [natDegree_pow]
    have hC_deg_lt : (C (b ^ 2) : R[X]).natDegree < ((X - C a) ^ 2 : R[X]).natDegree := by
      rw [natDegree_C, h_sq_deg]; norm_num
    have hC_deg_lt' : (C (b ^ 2) : R[X]).degree < ((X - C a) ^ 2 : R[X]).degree := by
      calc (C (b ^ 2) : R[X]).degree ≤ 0 := degree_C_le
        _ < (2 : ℕ) := by norm_num
        _ = ((X - C a) ^ 2 : R[X]).degree := by
          simp [degree_pow, degree_X_sub_C]
    have hM_monic : M.Monic := by
      show M.leadingCoeff = 1
      rw [show M = C (b ^ 2) + (X - C a) ^ 2 from by ring,
          leadingCoeff_add_of_degree_lt hC_deg_lt']
      exact ((monic_X_sub_C a).pow 2).leadingCoeff
    have hM_deg : M.natDegree = 2 := by
      rw [show M = C (b ^ 2) + (X - C a) ^ 2 from by ring,
          natDegree_add_eq_right_of_natDegree_lt hC_deg_lt]
      exact h_sq_deg
    -- Conjugation on the representation
    have hconj_α : (Ri.conj R) α =
        algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R := by
      rw [hab]
      simp only [map_add, map_mul, AlgHom.commutes, Ri.conj_i, mul_neg]
      ring
    -- M.map ι = (X - α)(X - conj α) via trace/norm
    have h_trace : algebraMap R (Ri R) (2 * a) = α + (Ri.conj R) α := by
      rw [hconj_α, hab, map_mul, map_ofNat]; ring
    have h_norm : algebraMap R (Ri R) (a ^ 2 + b ^ 2) = α * (Ri.conj R) α := by
      rw [hconj_α, hab, map_add, map_pow, map_pow]
      have hi_sq : (Ri.i R) ^ 2 = -(1 : Ri R) := Ri.i_sq R
      ring_nf; rw [hi_sq]; ring
    have hM_expand : M = X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2) := by
      simp only [hM_def, map_add, map_pow, map_mul, map_ofNat]; ring
    have hM_map : M.map (algebraMap R (Ri R)) =
        (X - C α) * (X - C ((Ri.conj R) α)) := by
      simp only [hM_expand, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, map_C]
      rw [h_trace, h_norm]
      simp only [map_add, map_mul]
      ring
    -- (X - α)(X - conj α) | q.map ι
    have hM_dvd_map : M.map (algebraMap R (Ri R)) ∣ q.map (algebraMap R (Ri R)) :=
      hM_map ▸ conj_pair_dvd_map q α hα hα_ne
    -- Lift to M | q in R[X]
    have hM_dvd : M ∣ q := dvd_of_map_dvd_monic M q hM_monic hM_dvd_map
    -- Irreducibility forces q = M
    obtain ⟨u, hu⟩ := hM_dvd
    rcases hq.isUnit_or_isUnit hu with hMu | huu
    · -- M can't be a unit (degree 2)
      exact absurd (natDegree_eq_zero_of_isUnit hMu) (by omega)
    · -- u is a unit, so q = M
      have hu_deg0 : u.natDegree = 0 := natDegree_eq_zero_of_isUnit huu
      have hu_one : u = 1 := by
        have hu_eq : u = C (u.coeff 0) := eq_C_of_natDegree_eq_zero hu_deg0
        have h_lc : (M * u).leadingCoeff = M.leadingCoeff * u.leadingCoeff :=
          leadingCoeff_mul M u
        rw [← hu, hm.leadingCoeff, hM_monic.leadingCoeff, one_mul] at h_lc
        rw [leadingCoeff, hu_deg0] at h_lc
        rw [hu_eq, ← h_lc, map_one]
      exact ⟨a, b, hb_ne, by rw [hu, hu_one, mul_one]⟩

/-- **BPR Proposition 2.19** (real closed form). Over a real closed field R,
    every monic irreducible polynomial is either linear or has the form
    (X − c)² + d² with d ≠ 0. -/
theorem proposition_2_19_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    {q : R[X]} (hq : Irreducible q) (hm : q.Monic) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    q.natDegree = 1 ∨ ∃ c d : R, d ≠ 0 ∧ q = (X - C c) ^ 2 + C (d ^ 2) := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_19 hq hm

end Azurite.BPR.Proposition2_19
