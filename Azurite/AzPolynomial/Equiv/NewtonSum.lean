import Azurite.AzPolynomial.NewtonSum
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_8
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Correctness of `AzPolynomial.newtonSumMonic` and the inverse algorithm

For a monic polynomial `P : AzPolynomial K` (with `K` a field and `C`
an algebraically closed extension), the iterative Newton sum
`P.newtonSumMonic i` computed via the Newton recurrence (BPR
Proposition 4.8) agrees with the mathematical Newton sum
`∑_{x ∈ aroots P} x^i` (where roots are taken in `C` with multiplicity).

The inverse algorithm `polyFromNewtonSumsMonic` (BPR Algorithm 8.11)
recovers `P` from its Newton sums; the round-trip
`polyFromNewtonSumsMonic ∘ newtonSumsMonic = id` is proved here for
monic polynomials over a `[Field K] [CharZero K]`.
-/

namespace Azurite.AzPolynomial

open Azurite.BPR.Chapter4 Polynomial _root_.AzPolynomial

variable {K : Type _} [Field K] {C : Type _} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Correctness of `newtonSumMonic`.** For a monic polynomial
    `P : AzPolynomial K` and any `i : ℕ`, the iterative
    `P.newtonSumMonic i : K` (computed via the Newton recurrence) agrees,
    after the algebra-map `K → C`, with the mathematical Newton sum
    `newtonSum (toPoly P) i` (the sum of `i`-th powers of `P`'s roots in
    `C`, counted with multiplicity). -/
theorem newtonSumMonic_toPoly (P : Azurite.AzPolynomial K) (hMonic : P.Monic) (i : ℕ) :
    algebraMap K C (P.newtonSumMonic i) = newtonSum (toPoly P) i := by
  set Q : K[X] := toPoly P with hQ_def
  set p : ℕ := P.natDegree with hp_def
  have hQ_monic : Q.Monic := (Monic_toPoly P).mpr hMonic
  have hQ_natDeg : Q.natDegree = p := natDegree_toPoly P
  have hQ_coeff : ∀ m, Q.coeff m = P.coeff m := fun m => coeff_toPoly_eq P m
  have hQ_coeff_p : Q.coeff p = 1 := by
    rw [← hQ_natDeg]; exact hQ_monic.coeff_natDegree
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
      -- Base case: newtonSumMonic P 0 = p; newtonSum Q 0 = (Q.aroots C).card = p.
      simp only [newtonSumMonic]
      rw [newtonSum_zero]
      have hcard : (Q.aroots C).card = p := by
        rw [← hQ_natDeg]
        exact IsAlgClosed.card_aroots_eq_natDegree
      rw [hcard, map_natCast]
    | n + 1 =>
      -- Recursive case. Unfold newtonSumMonic.
      simp only [newtonSumMonic]
      -- Push algebraMap through subtraction, if-then-else, multiplication, sum.
      rw [map_sub, map_sum]
      -- For the leading term, push algebraMap through (if then else) and multiplication.
      rw [show algebraMap K C
            (if n + 1 ≤ p then ((p - (n + 1) : ℕ) : K) * P.coeff (p - (n + 1)) else 0) =
          if n + 1 ≤ p then ((p - (n + 1) : ℕ) : C) *
              algebraMap K C (P.coeff (p - (n + 1))) else 0 from by
        split_ifs with hle
        · rw [map_mul, map_natCast]
        · exact map_zero _]
      -- For each summand, apply algebraMap distributivity and induction hypothesis.
      have hsum_eq : ∑ k ∈ Finset.range (min (n + 1) p),
            algebraMap K C (P.coeff (p - (k + 1)) * P.newtonSumMonic (n - k)) =
          ∑ k ∈ Finset.range (min (n + 1) p),
            algebraMap K C (P.coeff (p - (k + 1))) * newtonSum Q (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [map_mul, ih (n - k) (by omega)]
      rw [hsum_eq]
      -- Two cases: n + 1 ≤ p (use Prop 4.8) or n + 1 > p (use orthogonality).
      by_cases hle : n + 1 ≤ p
      · -- Case n + 1 ≤ p. Apply Prop 4.8 at j = p - (n + 1).
        rw [ite_eq_left hle]
        rw [show min (n + 1) p = n + 1 from min_eq_left hle]
        have hj_le : p - (n + 1) ≤ Q.natDegree := by rw [hQ_natDeg]; omega
        have hProp48 := proposition_4_8 (C := C) Q (p - (n + 1)) hj_le
        rw [hQ_natDeg] at hProp48
        -- Reindex: ∑_{m ∈ Ico (p-(n+1)) (p+1)} f(m) = f(p) + ∑_{k ∈ range (n+1)} f(p - (k+1))
        have hbij : ∑ m ∈ Finset.Ico (p - (n + 1)) (p + 1),
              (algebraMap K C) (Q.coeff m) * newtonSum Q (m - (p - (n + 1))) =
            (algebraMap K C) (Q.coeff p) * newtonSum Q (n + 1) +
            ∑ k ∈ Finset.range (n + 1),
              (algebraMap K C) (Q.coeff (p - (k + 1))) * newtonSum Q (n - k) := by
          rw [Finset.sum_Ico_eq_sum_range,
              show (p + 1) - (p - (n + 1)) = n + 2 from by omega,
              Finset.sum_range_succ, add_comm]
          congr 1
          · -- m = p - (n + 1) + (n + 1) = p term
            rw [show p - (n + 1) + (n + 1) = p from by omega,
                show p - (p - (n + 1)) = n + 1 from by omega]
          · -- Re-index ∑_{k ∈ range (n+1)} f(p - (n+1) + k) = ∑_{k} f(p - (k+1))
            rw [← Finset.sum_range_reflect (fun k =>
                (algebraMap K C) (Q.coeff (p - (n + 1) + k)) *
                  newtonSum Q (p - (n + 1) + k - (p - (n + 1)))) (n + 1)]
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_range] at hk
            rw [show p - (n + 1) + (n + 1 - 1 - k) = p - (k + 1) from by omega,
                show p - (k + 1) - (p - (n + 1)) = n - k from by omega]
        -- Substitute hbij into hProp48 and simplify.
        rw [hbij, hQ_coeff_p, map_one, one_mul] at hProp48
        -- Bridge Q.coeff to P.coeff in hProp48.
        simp_rw [hQ_coeff] at hProp48
        -- Goal: (cast) * algMap (P.coeff (p - (n+1))) - sum = newtonSum Q (n+1).
        -- hProp48: same LHS = newtonSum Q (n+1) + sum.
        rw [sub_eq_iff_eq_add]
        exact hProp48
      · -- Case n + 1 > p: leading = 0; use orthogonality at q = n + 1 - p.
        rw [ite_eq_right hle]
        push Not at hle
        rw [zero_sub]
        rw [show min (n + 1) p = p from min_eq_right (by omega)]
        set q : ℕ := n + 1 - p with hq_def
        have hq_pos : 1 ≤ q := by omega
        have horth := newtonSum_orthogonality (C := C) Q q
        rw [hQ_natDeg] at horth
        rw [Finset.range_add_one, Finset.sum_insert (by simp),
            hQ_coeff_p, map_one, one_mul,
            show p + q = n + 1 from by omega] at horth
        -- Re-index via sum_range_reflect: m ↦ p - 1 - m.
        have hbij : ∑ m ∈ Finset.range p,
              (algebraMap K C) (Q.coeff m) * newtonSum Q (m + q) =
            ∑ k ∈ Finset.range p,
              (algebraMap K C) (P.coeff (p - (k + 1))) * newtonSum Q (n - k) := by
          rw [← Finset.sum_range_reflect (fun m =>
              (algebraMap K C) (Q.coeff m) * newtonSum Q (m + q)) p]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          rw [hQ_coeff, hq_def,
              show p - 1 - k = p - (k + 1) from by omega,
              show p - (k + 1) + (n + 1 - p) = n - k from by omega]
        rw [hbij] at horth
        linear_combination -horth

/-! ### Correctness of `polyFromNewtonSumsMonic` (BPR Algorithm 8.11)

The inverse algorithm `polyFromNewtonSumsMonic` produces a polynomial
whose BPR Newton sums (in `C`) agree with the input. -/

variable [CharZero K]

omit [CharZero K] in
/-- The `k`-th coefficient of `polyFromNewtonSumsMonic N` matches the
    recursive specification `coeffFromNewtonSums N (N.size - 1) k`,
    when `N` is nonempty. -/
lemma polyFromNewtonSumsMonic_coeff_eq {N : Array K}
    (hN : 0 < N.size) (k : ℕ) :
    (polyFromNewtonSumsMonic N).coeff k = coeffFromNewtonSums N (N.size - 1) k := by
  set p := N.size - 1 with hp_def
  -- Unfold `polyFromNewtonSumsMonic N` to its else branch.
  have hcoeffs : (polyFromNewtonSumsMonic N).coeffs =
      ((Array.range p).map (coeffFromNewtonSums N p)).push 1 := by
    unfold polyFromNewtonSumsMonic
    split_ifs with hN_empty
    · exfalso
      rw [Array.isEmpty_iff_size_eq_zero] at hN_empty
      omega
    · rfl
  show ((polyFromNewtonSumsMonic N).coeffs)[k]?.getD 0 = _
  rw [hcoeffs]
  rw [Array.getElem?_push, Array.size_map, Array.size_range]
  rcases lt_trichotomy k p with hlt | heq | hgt
  · -- k < p
    rw [ite_eq_right hlt.ne, Array.getElem?_map, Array.getElem?_range, ite_eq_left hlt]
    rfl
  · -- k = p
    subst heq
    rw [ite_eq_left rfl]
    show (some (1 : K)).getD 0 = _
    conv_rhs => rw [coeffFromNewtonSums]
    simp
  · -- k > p
    rw [ite_eq_right hgt.ne', Array.getElem?_map, Array.getElem?_range,
        ite_eq_right (by omega : ¬ k < p)]
    show (Option.map _ none).getD 0 = _
    conv_rhs => rw [coeffFromNewtonSums]
    simp [show ¬ k < p from by omega, show k ≠ p from by omega]

omit [CharZero K] in
/-- **K-side Newton recurrence.** For a monic `P : AzPolynomial K` and
    `k ≤ P.natDegree`,
    `(k : K) · P.coeff k = ∑_{m = k}^{p} P.coeff m · P.newtonSumMonic (m - k)`.
    Derived from BPR Proposition 4.8 (which lives in an algebraic
    closure) by injectivity of the `algebraMap` into that closure. -/
lemma newtonSumMonic_recurrence (P : Azurite.AzPolynomial K)
    (hMonic : P.Monic) (k : ℕ) (hk : k ≤ P.natDegree) :
    ((k : ℕ) : K) * P.coeff k =
    ∑ m ∈ Finset.Ico k (P.natDegree + 1),
      P.coeff m * P.newtonSumMonic (m - k) := by
  -- Use `AlgebraicClosure K` internally; pull the K-side equation back
  -- via injectivity of `algebraMap K (AlgebraicClosure K)`.
  let A := AlgebraicClosure K
  suffices h : algebraMap K A (((k : ℕ) : K) * P.coeff k) =
      algebraMap K A (∑ m ∈ Finset.Ico k (P.natDegree + 1),
        P.coeff m * P.newtonSumMonic (m - k)) by
    exact FaithfulSMul.algebraMap_injective K A h
  rw [map_mul, map_natCast]
  have hQ_natDeg : (toPoly P).natDegree = P.natDegree := natDegree_toPoly P
  have hProp48 := proposition_4_8 (C := A) (toPoly P) k (by rw [hQ_natDeg]; exact hk)
  rw [hQ_natDeg] at hProp48
  -- Bridge `(toPoly P).coeff = P.coeff` in hProp48.
  simp_rw [coeff_toPoly_eq] at hProp48
  rw [hProp48, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul, newtonSumMonic_toPoly (C := A) P hMonic]

/-- **Round-trip correctness for BPR Algorithm 8.11.** For a monic
    polynomial `P : AzPolynomial K` (with `K` of characteristic zero),
    recovering `P` from its first `p + 1` Newton sums yields back
    exactly `P`. -/
theorem polyFromNewtonSumsMonic_newtonSumsMonic
    (P : Azurite.AzPolynomial K) (hMonic : P.Monic) :
    polyFromNewtonSumsMonic (P.newtonSumsMonic (P.natDegree + 1)) = P := by
  set N : Array K := P.newtonSumsMonic (P.natDegree + 1) with hN_def
  set p : ℕ := P.natDegree with hp_def
  have hN_size : N.size = p + 1 := by
    rw [hN_def]; unfold newtonSumsMonic; simp
  have hN_pos : 0 < N.size := by rw [hN_size]; omega
  have hN_p_eq : N.size - 1 = p := by omega
  have hN_getD : ∀ j : ℕ, j < p + 1 → N.getD j 0 = P.newtonSumMonic j := by
    intro j hj
    rw [hN_def]
    unfold newtonSumsMonic
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
        ite_eq_left hj]
    rfl
  classical
  ext k
  rw [polyFromNewtonSumsMonic_coeff_eq hN_pos k]
  rw [hN_p_eq]
  -- Strong induction on `p + 1 - k`.
  induction h : (p + 1 - k) using Nat.strong_induction_on generalizing k with
  | _ m ih =>
    by_cases hkp : k ≤ p
    · by_cases heq : k = p
      · -- k = p: leading coefficient is 1.
        subst heq
        rw [coeffFromNewtonSums]
        simp only [lt_irrefl, ↓reduceIte]
        symm
        exact hMonic
      · -- k < p: apply the K-side Newton recurrence.
        have hlt : k < p := lt_of_le_of_ne hkp heq
        rw [coeffFromNewtonSums, ite_eq_left hlt]
        have hrec := newtonSumMonic_recurrence P hMonic k hkp
        -- IH: coeffFromNewtonSums N p (k + j + 1) = P.coeff (k + j + 1) for j ∈ range (p - k).
        have hIH : ∀ j ∈ Finset.range (p - k),
            coeffFromNewtonSums N p (k + (j + 1)) = P.coeff (k + (j + 1)) := by
          intro j hj
          rw [Finset.mem_range] at hj
          exact ih (p + 1 - (k + (j + 1))) (by omega) (k + (j + 1)) rfl
        have hsum_rw : ∑ j ∈ Finset.range (p - k),
              coeffFromNewtonSums N p (k + (j + 1)) * N.getD (j + 1) 0 =
            ∑ j ∈ Finset.range (p - k),
              P.coeff (k + (j + 1)) * P.newtonSumMonic (j + 1) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hIH j hj]
          rw [Finset.mem_range] at hj
          congr 1
          exact hN_getD (j + 1) (by omega)
        rw [hsum_rw]
        -- Reindex Finset.range (p - k) ↔ Finset.Ico (k + 1) (p + 1).
        have hreindex : ∑ j ∈ Finset.range (p - k),
              P.coeff (k + (j + 1)) * P.newtonSumMonic (j + 1) =
            ∑ m ∈ Finset.Ico (k + 1) (p + 1),
              P.coeff m * P.newtonSumMonic (m - k) := by
          rw [Finset.sum_Ico_eq_sum_range]
          rw [show (p + 1) - (k + 1) = p - k from by omega]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          congr 2
          · ring
          · omega
        rw [hreindex]
        -- Split off `m = k` term in the K-side recurrence.
        have hsplit : ∑ m ∈ Finset.Ico k (p + 1),
              P.coeff m * P.newtonSumMonic (m - k) =
            P.coeff k * ((p : ℕ) : K) +
            ∑ m ∈ Finset.Ico (k + 1) (p + 1),
              P.coeff m * P.newtonSumMonic (m - k) := by
          rw [show Finset.Ico k (p + 1) =
              insert k (Finset.Ico (k + 1) (p + 1)) from by
            ext x
            simp only [Finset.mem_Ico, Finset.mem_insert]
            omega]
          rw [Finset.sum_insert (by rw [Finset.mem_Ico]; omega)]
          congr 1
          rw [show k - k = 0 from Nat.sub_self k]
          simp only [newtonSumMonic]
          rfl
        rw [hsplit] at hrec
        have hcast : ((k : ℕ) : K) - ((p : ℕ) : K) = -(((p - k : ℕ) : K)) := by
          rw [Nat.cast_sub hkp]; ring
        have hsub : ∑ m ∈ Finset.Ico (k + 1) (p + 1),
              P.coeff m * P.newtonSumMonic (m - k) =
            -(((p - k : ℕ) : K)) * P.coeff k := by
          linear_combination -hrec + P.coeff k * hcast
        rw [hsub]
        have hpk_ne : ((p - k : ℕ) : K) ≠ 0 := by
          have : (p - k : ℕ) ≠ 0 := by omega
          exact_mod_cast this
        field_simp
    · -- k > p: both sides 0.
      rw [coeffFromNewtonSums]
      simp only [show ¬ k < p from by omega, ↓reduceIte,
                 show k ≠ p from by omega]
      symm
      show P.coeff k = 0
      have hk_gt : P.natDegree < k := by omega
      rw [show P.coeff k = (toPoly P).coeff k from (coeff_toPoly_eq P k).symm]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [AzPolynomial.natDegree_toPoly]; exact hk_gt)

omit [IsAlgClosed C] in
/-- **BPR Algorithm 8.11 correctness, stated in BPR's `newtonSum` form.**
    For a monic `P : AzPolynomial K`, the algorithm's output has the
    same BPR Newton sums (over an algebraically closed `C`) as `P`. -/
theorem polyFromNewtonSumsMonic_newtonSum
    (P : Azurite.AzPolynomial K) (hMonic : P.Monic) (j : ℕ) :
    newtonSum (C := C)
      (toPoly (polyFromNewtonSumsMonic (P.newtonSumsMonic (P.natDegree + 1)))) j =
    newtonSum (C := C) (toPoly P) j := by
  rw [polyFromNewtonSumsMonic_newtonSumsMonic P hMonic]

end Azurite.AzPolynomial
