import Azurite.AzPolynomial.PRem
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.MulXPow
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic.LinearCombination

/-!
# Equivalence: `AzPolynomial.pRem` ↔ BPR's `PRem`

This file proves that the computational signed pseudo-remainder
`Azurite.AzPolynomial.pRem` matches the mathematical signed
pseudo-remainder `Azurite.BPR.PRem` from Basu, Pollack, Roy,
*Algorithms in Real Algebraic Geometry*, Section 1.3.

Given a commutative domain `D` with fraction field `K`, polynomials
`P, Q : AzPolynomial D` with `Q ≠ 0`, the theorem

  `toPoly_pRem_map : (AzPolynomial.toPoly (pRem P Q)).map (algebraMap D K) =`
  `                    Azurite.BPR.PRem K (toPoly P) (toPoly Q)`

identifies the two. The proof structure mirrors `BPR.PRem_descends`:
we construct the pseudo-division equation in `D[X]` by induction on
the fold, then appeal to uniqueness of Euclidean division in `K[X]`.
-/

namespace Azurite.AzPolynomial

open Polynomial

variable {D : Type*} [CommRing D] [DecidableEq D]

/-! ### Helpers for converting between coefficient bounds and size bounds -/

omit [DecidableEq D] in
private lemma coeff_eq_zero_of_size_le' (p : AzPolynomial D) (k : ℕ)
    (hk : p.coeffs.size ≤ k) : p.coeff k = 0 := by
  simp [coeff, Array.getElem?_eq_none_iff.mpr hk]

omit [DecidableEq D] in
private lemma size_le_of_coeff_zero_above (p : AzPolynomial D) (N : ℕ)
    (h : ∀ k, k ≥ N → p.coeff k = 0) : p.coeffs.size ≤ N := by
  by_contra h1
  push Not at h1
  have hN_le : N ≤ p.coeffs.size - 1 := by omega
  have h2 : p.coeff (p.coeffs.size - 1) = 0 := h _ hN_le
  have hsize_pos : 0 < p.coeffs.size := by omega
  have hidx : p.coeffs[p.coeffs.size - 1]? =
      some (p.coeffs[p.coeffs.size - 1]'(by omega)) :=
    Array.getElem?_eq_getElem (by omega)
  unfold Azurite.AzPolynomial.coeff at h2
  rw [hidx] at h2
  simp at h2
  have hback : p.coeffs.back? = some 0 := by
    rw [Array.back?_eq_getElem?, hidx, h2]
  exact p.last_ne_zero hback

/-! ### Existence of the pseudo-division equation after the fold -/

/-- Fold invariant: after `n` reduction steps starting from `P`, the running
    remainder `R_n` satisfies `C(b^n) * toPoly P = A_n * toPoly Q + toPoly R_n`
    for some `A_n : Polynomial D`. -/
private lemma pRem_fold_exists (P Q : AzPolynomial D) (q : ℕ) (b : D)
    (n : ℕ) :
    ∃ A : Polynomial D,
      Polynomial.C (b^n) * AzPolynomial.toPoly P =
        A * AzPolynomial.toPoly Q +
          AzPolynomial.toPoly ((List.range n).foldl
            (fun rem _ => pRemStep q b Q rem) P) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨A_n, hA_n⟩ := ih
    set rem_n := (List.range n).foldl (fun rem _ => pRemStep q b Q rem) P
      with h_def_rem_n
    have h_fold : (List.range (n + 1)).foldl
        (fun rem _ => pRemStep q b Q rem) P = pRemStep q b Q rem_n := by
      rw [List.range_succ, List.foldl_append]; rfl
    rw [h_fold]
    by_cases hsize : rem_n.coeffs.size > q
    · -- High case: rem_{n+1} = b • rem_n - mulXPow e (lead • Q)
      refine ⟨Polynomial.C b * A_n +
        Polynomial.X ^ (rem_n.coeffs.size - 1 - q) *
          Polynomial.C rem_n.leadingCoeff, ?_⟩
      have hstep : AzPolynomial.toPoly (pRemStep q b Q rem_n) =
          Polynomial.C b * AzPolynomial.toPoly rem_n -
            Polynomial.X ^ (rem_n.coeffs.size - 1 - q) *
              Polynomial.C rem_n.leadingCoeff *
              AzPolynomial.toPoly Q := by
        unfold pRemStep
        rw [if_pos hsize]
        rw [toPoly_sub, toPoly_smul, toPoly_mulXPow, toPoly_smul]
        rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
        ring
      rw [hstep]
      have hb_pow : Polynomial.C (b ^ (n + 1)) =
          Polynomial.C b * Polynomial.C (b ^ n) := by
        rw [pow_succ, mul_comm (b^n) b, Polynomial.C_mul]
      rw [hb_pow]
      linear_combination (Polynomial.C b) * hA_n
    · -- Low case: rem_{n+1} = b • rem_n
      refine ⟨Polynomial.C b * A_n, ?_⟩
      have hstep : AzPolynomial.toPoly (pRemStep q b Q rem_n) =
          Polynomial.C b * AzPolynomial.toPoly rem_n := by
        unfold pRemStep
        rw [if_neg hsize]
        rw [toPoly_smul, Polynomial.smul_eq_C_mul]
      rw [hstep]
      have hb_pow : Polynomial.C (b ^ (n + 1)) =
          Polynomial.C b * Polynomial.C (b ^ n) := by
        rw [pow_succ, mul_comm (b^n) b, Polynomial.C_mul]
      rw [hb_pow]
      linear_combination (Polynomial.C b) * hA_n

/-! ### Coefficient decay after fold steps -/

/-- Fold invariant for the degree bound: after `n` reduction steps, the
    running remainder has zero coefficients at every index
    `k ≥ max (P.coeffs.size - n) q`, where `q = Q.coeffs.size - 1`. -/
private lemma pRem_fold_coeff_zero (P Q : AzPolynomial D)
    (hQ : 0 < Q.coeffs.size) (b : D) (hb : b = Q.leadingCoeff)
    (n : ℕ) :
    ∀ k, k ≥ max (P.coeffs.size - n) (Q.coeffs.size - 1) →
      ((List.range n).foldl
        (fun rem _ => pRemStep (Q.coeffs.size - 1) b Q rem) P).coeff k = 0 := by
  induction n with
  | zero =>
    intro k hk
    simp only [List.range_zero, List.foldl_nil, Nat.sub_zero] at hk ⊢
    have : P.coeffs.size ≤ k := le_of_max_le_left hk
    exact coeff_eq_zero_of_size_le' P k this
  | succ n ih =>
    intro k hk
    set q := Q.coeffs.size - 1 with h_q
    set rem_n := (List.range n).foldl
      (fun rem _ => pRemStep q b Q rem) P with h_def_rem_n
    have h_fold : (List.range (n + 1)).foldl
        (fun rem _ => pRemStep q b Q rem) P = pRemStep q b Q rem_n := by
      rw [List.range_succ, List.foldl_append]; rfl
    rw [h_fold]
    have ih' : ∀ k', k' ≥ max (P.coeffs.size - n) q → rem_n.coeff k' = 0 := ih
    have h_rem_n_size : rem_n.coeffs.size ≤ max (P.coeffs.size - n) q :=
      size_le_of_coeff_zero_above rem_n _ ih'
    unfold pRemStep
    split
    · -- High case: rem_n.size > q
      next hsize =>
      simp only [coeff_sub, coeff_smul, coeff_mulXPow]
      have hk1 : k ≥ max (P.coeffs.size - (n + 1)) q := hk
      by_cases hk_ge_size : k ≥ rem_n.coeffs.size
      · -- rem_n.coeff k = 0 and the mulXPow contribution is also 0
        have h1 : rem_n.coeff k = 0 := coeff_eq_zero_of_size_le' rem_n k hk_ge_size
        rw [h1]
        split
        · next he_le =>
          have hge : k - (rem_n.coeffs.size - 1 - q) ≥ Q.coeffs.size := by
            have h1' : k - (rem_n.coeffs.size - 1 - q) ≥
              rem_n.coeffs.size - (rem_n.coeffs.size - 1 - q) :=
              Nat.sub_le_sub_right hk_ge_size _
            have h_eq : rem_n.coeffs.size - (rem_n.coeffs.size - 1 - q) = q + 1 := by
              omega
            rw [h_eq] at h1'
            have hQeq : Q.coeffs.size = q + 1 := by rw [h_q]; omega
            omega
          have hQ_zero : Q.coeff (k - (rem_n.coeffs.size - 1 - q)) = 0 :=
            coeff_eq_zero_of_size_le' Q _ hge
          rw [hQ_zero]
          simp
        · simp
      · -- k in [rem_n.size - 1, rem_n.size)
        push Not at hk_ge_size
        have hkq : k ≥ q := le_of_max_le_right hk1
        have h_rem_n_size_sub1 : rem_n.coeffs.size - 1 ≤
            max (P.coeffs.size - (n + 1)) q := by
          rcases Nat.lt_or_ge q (P.coeffs.size - n) with h | h
          · -- q < P.size - n, so max = P.size - n
            have h_max : max (P.coeffs.size - n) q = P.coeffs.size - n :=
              max_eq_left (le_of_lt h)
            rw [h_max] at h_rem_n_size
            have h1' : rem_n.coeffs.size - 1 ≤ P.coeffs.size - n - 1 := by omega
            have h2' : P.coeffs.size - n - 1 = P.coeffs.size - (n + 1) := by omega
            rw [h2'] at h1'
            exact le_max_of_le_left h1'
          · -- q ≥ P.size - n, so max = q
            have : rem_n.coeffs.size ≤ q := by
              calc rem_n.coeffs.size ≤ max (P.coeffs.size - n) q := h_rem_n_size
                _ = q := max_eq_right h
            omega
        have hk_ge_size_m1 : k ≥ rem_n.coeffs.size - 1 :=
          le_trans h_rem_n_size_sub1 hk1
        have h_k_eq : k = rem_n.coeffs.size - 1 := by omega
        rw [h_k_eq]
        have he_eq : rem_n.coeffs.size - 1 - (rem_n.coeffs.size - 1 - q) = q := by omega
        have h_idx : rem_n.coeffs.size - 1 ≥ rem_n.coeffs.size - 1 - q := by omega
        rw [if_pos h_idx]
        have h_lead : rem_n.coeff (rem_n.coeffs.size - 1) = rem_n.leadingCoeff := by
          unfold leadingCoeff natDegree; rfl
        rw [h_lead, he_eq]
        have hQlead : Q.coeff q = Q.leadingCoeff := by
          unfold leadingCoeff natDegree
          rw [h_q]
        rw [hQlead, ← hb]
        show b • rem_n.leadingCoeff - rem_n.leadingCoeff • b = 0
        rw [smul_eq_mul, smul_eq_mul, mul_comm]
        ring
    · -- Low case: rem_n.size ≤ q
      next hsize =>
      push Not at hsize
      have hkq : k ≥ Q.coeffs.size - 1 := le_of_max_le_right hk
      have h_size_le_k : rem_n.coeffs.size ≤ k := by
        calc rem_n.coeffs.size ≤ Q.coeffs.size - 1 := hsize
          _ ≤ k := hkq
      show (b • rem_n).coeff k = 0
      rw [coeff_smul, coeff_eq_zero_of_size_le' rem_n k h_size_le_k]
      simp

/-! ### Degree bound on `toPoly (pRem P Q)` -/

theorem degree_toPoly_pRem_lt (P Q : AzPolynomial D)
    (hQ : AzPolynomial.toPoly Q ≠ 0) :
    (AzPolynomial.toPoly (pRem P Q)).degree < (AzPolynomial.toPoly Q).degree := by
  rw [AzPolynomial.degree_toPoly Q]
  have hQsize : Q.coeffs.size ≠ 0 := by
    intro h
    apply hQ
    have : Q = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  have hQne : Q.coeffs ≠ #[] := fun h => hQsize (by rw [h]; rfl)
  simp only [Azurite.AzPolynomial.degree, hQne, ↓reduceIte]
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_toPoly_eq]
  have hn_nat : n ≥ Q.coeffs.size - 1 := by
    have : (n : ℤ) ≥ ↑(Q.coeffs.size - 1) := by exact_mod_cast hn
    omega
  by_cases hPQ : P.coeffs.size < Q.coeffs.size
  · -- deg P < deg Q: pRem = P
    have h_pRem : pRem P Q = P := by
      unfold pRem; rw [if_neg hQsize, if_pos hPQ]
    rw [h_pRem]
    exact coeff_eq_zero_of_size_le' P n (by omega)
  · push Not at hPQ
    set numSteps := P.coeffs.size - Q.coeffs.size + 1 with h_numSteps
    set R := (List.range numSteps).foldl
      (fun rem _ => pRemStep (Q.coeffs.size - 1) Q.leadingCoeff Q rem) P
        with h_R
    have h_pRem : pRem P Q =
        if numSteps % 2 = 1 then Q.leadingCoeff • R else R := by
      unfold pRem
      rw [if_neg hQsize, if_neg (by omega : ¬ P.coeffs.size < Q.coeffs.size)]
    have h_threshold : P.coeffs.size - numSteps = Q.coeffs.size - 1 := by
      simp only [h_numSteps]; omega
    have h_fold_coeff : R.coeff n = 0 := by
      have := pRem_fold_coeff_zero P Q
        (Nat.pos_of_ne_zero hQsize) Q.leadingCoeff rfl numSteps n
        (by rw [h_threshold, max_self]; exact hn_nat)
      exact this
    rw [h_pRem]
    split_ifs with h
    · rw [coeff_smul, h_fold_coeff, smul_zero]
    · exact h_fold_coeff

/-! ### The `D[X]` equation -/

lemma toPoly_pRem_div_eq (P Q : AzPolynomial D)
    (hQ : AzPolynomial.toPoly Q ≠ 0) :
    ∃ A : Polynomial D,
      Polynomial.C (Q.leadingCoeff ^
          Azurite.BPR.pRemExp (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) *
        AzPolynomial.toPoly P =
        A * AzPolynomial.toPoly Q + AzPolynomial.toPoly (pRem P Q) := by
  -- Extract the hypothesis that Q.coeffs is nonempty
  have hQsize : Q.coeffs.size ≠ 0 := by
    intro h
    apply hQ
    have : Q = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  by_cases hP : AzPolynomial.toPoly P = 0
  · -- P = 0: equation is trivial with A = 0
    refine ⟨0, ?_⟩
    have hP' : P = 0 := by apply toPoly_inj.mp; rw [hP, toPoly_zero]
    rw [hP, mul_zero, zero_mul, zero_add]
    rw [hP']
    -- pRem 0 Q = 0
    have : pRem (0 : AzPolynomial D) Q = 0 := by
      unfold pRem
      rw [if_neg hQsize]
      have : (0 : AzPolynomial D).coeffs.size = 0 := rfl
      rw [if_pos (by rw [this]; exact Nat.pos_of_ne_zero hQsize)]
    rw [this, toPoly_zero]
  · -- P ≠ 0
    by_cases hPQ_deg : (AzPolynomial.toPoly P).natDegree <
        (AzPolynomial.toPoly Q).natDegree
    · -- deg P < deg Q: pRem P Q = P, d_BPR = 0
      refine ⟨0, ?_⟩
      have hexp : Azurite.BPR.pRemExp (AzPolynomial.toPoly P)
          (AzPolynomial.toPoly Q) = 0 := by
        unfold Azurite.BPR.pRemExp Azurite.BPR.smallestEvenGe
        rw [if_pos hPQ_deg]
      rw [hexp, pow_zero, map_one, one_mul, zero_mul, zero_add]
      have hPne : P ≠ 0 := fun h => hP (by rw [h]; exact toPoly_zero)
      have hPsize : P.coeffs.size > 0 := by
        by_contra h
        push Not at h
        exact hPne (AzPolynomial.ext (Array.eq_empty_of_size_eq_zero
          (Nat.le_zero.mp h)))
      have hP_nd : (AzPolynomial.toPoly P).natDegree = P.natDegree :=
        AzPolynomial.natDegree_toPoly P
      have hQ_nd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree :=
        AzPolynomial.natDegree_toPoly Q
      rw [hP_nd, hQ_nd] at hPQ_deg
      have hPQ_size : P.coeffs.size < Q.coeffs.size := by
        unfold AzPolynomial.natDegree at hPQ_deg
        have hQs : Q.coeffs.size > 0 := Nat.pos_of_ne_zero hQsize
        omega
      unfold pRem
      rw [if_neg hQsize, if_pos hPQ_size]
    · -- deg P ≥ deg Q
      push Not at hPQ_deg
      have hPne : P ≠ 0 := fun h => hP (by rw [h]; exact toPoly_zero)
      have hPsize : P.coeffs.size > 0 := by
        by_contra h
        push Not at h
        exact hPne (AzPolynomial.ext (Array.eq_empty_of_size_eq_zero
          (Nat.le_zero.mp h)))
      have hP_nd : (AzPolynomial.toPoly P).natDegree = P.natDegree :=
        AzPolynomial.natDegree_toPoly P
      have hQ_nd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree :=
        AzPolynomial.natDegree_toPoly Q
      rw [hP_nd, hQ_nd] at hPQ_deg
      have hQs : Q.coeffs.size > 0 := Nat.pos_of_ne_zero hQsize
      have hPQ_size : P.coeffs.size ≥ Q.coeffs.size := by
        unfold AzPolynomial.natDegree at hPQ_deg
        omega
      set numSteps := P.coeffs.size - Q.coeffs.size + 1 with h_numSteps
      have hexp_eq : Azurite.BPR.pRemExp (AzPolynomial.toPoly P)
          (AzPolynomial.toPoly Q) = numSteps + numSteps % 2 := by
        unfold Azurite.BPR.pRemExp Azurite.BPR.smallestEvenGe
        rw [if_neg (by
          rw [hP_nd, hQ_nd]
          unfold AzPolynomial.natDegree
          omega)]
        rw [hP_nd, hQ_nd]
        unfold AzPolynomial.natDegree
        show (P.coeffs.size - 1 - (Q.coeffs.size - 1) + 1) +
          (P.coeffs.size - 1 - (Q.coeffs.size - 1) + 1) % 2 =
          numSteps + numSteps % 2
        have h_eq : P.coeffs.size - 1 - (Q.coeffs.size - 1) + 1 = numSteps := by
          simp only [h_numSteps]; omega
        rw [h_eq]
      rw [hexp_eq]
      obtain ⟨A_fold, hA_fold⟩ := pRem_fold_exists P Q
        (Q.coeffs.size - 1) Q.leadingCoeff numSteps
      set R := (List.range numSteps).foldl
        (fun rem _ => pRemStep (Q.coeffs.size - 1) Q.leadingCoeff Q rem) P
          with h_R
      have h_pRem_eq :
          pRem P Q = if numSteps % 2 = 1 then Q.leadingCoeff • R else R := by
        unfold pRem
        rw [if_neg hQsize]
        rw [if_neg (by omega : ¬ P.coeffs.size < Q.coeffs.size)]
      rw [h_pRem_eq]
      by_cases hparity : numSteps % 2 = 1
      · rw [if_pos hparity]
        have h_exp : numSteps + numSteps % 2 = numSteps + 1 := by rw [hparity]
        rw [h_exp]
        refine ⟨Polynomial.C Q.leadingCoeff * A_fold, ?_⟩
        rw [toPoly_smul, Polynomial.smul_eq_C_mul]
        have h_pow_succ :
            Polynomial.C (Q.leadingCoeff ^ (numSteps + 1)) =
            Polynomial.C Q.leadingCoeff * Polynomial.C (Q.leadingCoeff ^ numSteps) := by
          rw [pow_succ, mul_comm (Q.leadingCoeff^numSteps) _, Polynomial.C_mul]
        rw [h_pow_succ]
        linear_combination Polynomial.C Q.leadingCoeff * hA_fold
      · rw [if_neg hparity]
        have h_mod : numSteps % 2 = 0 := by omega
        rw [h_mod, Nat.add_zero]
        exact ⟨A_fold, hA_fold⟩

/-! ### Main theorem: mapping to `K[X]` identifies the two -/

section Main
variable {K : Type*} [Field K] [Algebra D K] [IsDomain D] [IsFractionRing D K]

omit [IsDomain D] in
/-- **Main equivalence**: our computational `pRem` matches BPR's
signed pseudo-remainder `PRem` after mapping to the fraction field `K[X]`. -/
theorem toPoly_pRem_map (P Q : AzPolynomial D) (hQ : Q ≠ 0) :
    (AzPolynomial.toPoly (pRem P Q)).map (algebraMap D K) =
      Azurite.BPR.PRem K (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  have hQP : AzPolynomial.toPoly Q ≠ 0 := by
    intro h
    apply hQ
    apply toPoly_inj.mp; rw [h, toPoly_zero]
  obtain ⟨A, hAR⟩ := toPoly_pRem_div_eq P Q hQP
  have hdR := degree_toPoly_pRem_lt P Q hQP
  have hmap := congrArg (Polynomial.map (algebraMap D K)) hAR
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hmap
  unfold Azurite.BPR.PRem Azurite.BPR.Rem
  rw [leadingCoeff_toPoly]
  simp only [Polynomial.map_mul, Polynomial.map_C]
  have hQmap_ne : (AzPolynomial.toPoly Q).map (algebraMap D K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective D K)).mpr hQP
  have hdR_map :
      ((AzPolynomial.toPoly (pRem P Q)).map (algebraMap D K)).degree <
      ((AzPolynomial.toPoly Q).map (algebraMap D K)).degree := by
    rwa [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective D K),
         Polynomial.degree_map_eq_of_injective (IsFractionRing.injective D K)]
  have hdvd : (AzPolynomial.toPoly Q).map (algebraMap D K) ∣
      (Polynomial.C ((algebraMap D K) (Q.leadingCoeff ^
        Azurite.BPR.pRemExp (AzPolynomial.toPoly P)
          (AzPolynomial.toPoly Q))) *
        (AzPolynomial.toPoly P).map (algebraMap D K)) -
      (AzPolynomial.toPoly (pRem P Q)).map (algebraMap D K) :=
    ⟨A.map (algebraMap D K), by linear_combination hmap⟩
  have hmod_sub :
      ((Polynomial.C ((algebraMap D K) (Q.leadingCoeff ^
        Azurite.BPR.pRemExp (AzPolynomial.toPoly P)
          (AzPolynomial.toPoly Q))) *
        (AzPolynomial.toPoly P).map (algebraMap D K)) -
        (AzPolynomial.toPoly (pRem P Q)).map (algebraMap D K)) %
          (AzPolynomial.toPoly Q).map (algebraMap D K) = 0 :=
    EuclideanDomain.mod_eq_zero.mpr hdvd
  rw [Polynomial.sub_mod, sub_eq_zero] at hmod_sub
  rw [hmod_sub, (Polynomial.mod_eq_self_iff hQmap_ne).mpr hdR_map]

omit [IsDomain D] in
/-- **`ofPoly` version**: for Mathlib polynomials `P Q : D[X]` with `Q ≠ 0`,
feeding them through `ofPoly` into our computational `pRem` and mapping to
`K[X]` recovers BPR's `PRem K P Q`. -/
theorem ofPoly_pRem_map (P Q : Polynomial D) (hQ : Q ≠ 0) :
    (AzPolynomial.toPoly (pRem (AzPolynomial.ofPoly P)
      (AzPolynomial.ofPoly Q))).map (algebraMap D K) =
      Azurite.BPR.PRem K P Q := by
  have hQ' : AzPolynomial.ofPoly Q ≠ 0 := by
    intro h
    apply hQ
    rw [← toPoly_ofPoly Q, h, toPoly_zero]
  rw [toPoly_pRem_map _ _ hQ', toPoly_ofPoly, toPoly_ofPoly]

end Main

end Azurite.AzPolynomial
