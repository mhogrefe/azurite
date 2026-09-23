import Azurite.AzPolynomial.QuoRem
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.SMul
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

/-!
# Equivalence of `AzPolynomial.quoRem` with Mathlib's Euclidean Division
-/

namespace Azurite.AzPolynomial

open Polynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-! ### Abstract fold invariant -/

private theorem foldl_preserves_inv
    {S : Type _} (step : ℕ → S → S) (P : S → Prop)
    (h_step : ∀ j s, P s → P (step j s))
    (n : ℕ) (p : ℕ) (s₀ : S) (h₀ : P s₀) :
    P ((List.range n).foldl (fun s k => step (p - k) s) s₀) := by
  induction n generalizing s₀ with
  | zero => exact h₀
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact h_step _ _ (ih _ h₀)

/-! ### Step-level algebraic identity -/

private theorem step_identity (C m R Q : AzPolynomial K) :
    mulBasecaseFold (C + m) Q + (R - mulBasecaseFold m Q)
      = mulBasecaseFold C Q + R := by
  show (C + m) * Q + (R - m * Q) = C * Q + R
  ext n
  simp only [coeff_add, coeff_sub, coeff_mul, add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-! ### Division equation -/

private theorem quoRem_fold_eq (q : ℕ) (bq : K) (Q P : AzPolynomial K)
    (p : ℕ) (n : ℕ) (C₀ R₀ : AzPolynomial K)
    (h : P = mulBasecaseFold C₀ Q + R₀) :
    let (C', R') :=
      (List.range n).foldl (fun cr k => quoRemStep q bq Q (p - k) cr) (C₀, R₀)
    P = mulBasecaseFold C' Q + R' := by
  apply foldl_preserves_inv (fun j cr => quoRemStep q bq Q j cr)
      (fun cr => P = mulBasecaseFold cr.1 Q + cr.2)
  · intro j ⟨C, R⟩ hCR
    show P = mulBasecaseFold (C + monomial (j - q) (R.coeff j / bq)) Q +
      (R - mulBasecaseFold (monomial (j - q) (R.coeff j / bq)) Q)
    rw [step_identity]; exact hCR
  · exact h

private theorem base_invariant (P Q : AzPolynomial K) :
    P = mulBasecaseFold 0 Q + P := by
  show P = (0 : AzPolynomial K) * Q + P
  ext n
  simp only [coeff_add, coeff_mul]
  simp [coeff]

theorem quoRem_eq (P Q : AzPolynomial K) :
    P = mulBasecaseFold (quo P Q) Q + rem P Q := by
  unfold quo rem quoRem
  split
  · dsimp only; exact base_invariant P Q
  · split
    · dsimp only; exact base_invariant P Q
    · split
      · dsimp only; exact base_invariant P Q
      · rename_i hQ hP hPQ
        exact quoRem_fold_eq
          (Q.coeffs.size - 1) Q.leadingCoeff Q P
          (P.coeffs.size - 1) (P.coeffs.size - Q.coeffs.size + 1) 0 P
          (base_invariant P Q)

theorem toPoly_quoRem_eq (P Q : AzPolynomial K) :
    AzPolynomial.toPoly P =
      AzPolynomial.toPoly (quo P Q) * AzPolynomial.toPoly Q +
        AzPolynomial.toPoly (rem P Q) := by
  have h := quoRem_eq P Q
  have h2 := congr_arg AzPolynomial.toPoly h
  simp only [toPoly_add, toPoly_mulBasecaseFold] at h2
  exact h2
/-! ### Coefficient helpers for degree bound -/

private theorem coeff_monomial_mul' (Q : AzPolynomial K) (d : ℕ) (c : K) (k : ℕ) :
    coeff ((monomial d c) * Q) (d + k) = c * Q.coeff k := by
  have h := toPoly_mul (monomial d c) Q
  have hc := congrArg (fun p => Polynomial.coeff p (d + k)) h
  rw [coeff_toPoly_eq] at hc
  rw [hc, toPoly_monomial, Polynomial.coeff_mul]
  simp_rw [Polynomial.coeff_monomial]
  have hmem : (d, k) ∈ Finset.antidiagonal (d + k) := by simp [Finset.mem_antidiagonal]
  rw [← Finset.add_sum_erase _ _ hmem]
  simp only [ite_true]
  suffices h : ∑ x ∈ (Finset.antidiagonal (d + k)).erase (d, k),
      (if d = x.1 then c else 0) * (AzPolynomial.toPoly Q).coeff x.2 = 0 by
    rw [h, add_zero, coeff_toPoly_eq]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_erase, Finset.mem_antidiagonal, Ne, Prod.mk.injEq] at hab
  obtain ⟨hne, hab⟩ := hab
  by_cases ha : d = a
  · subst ha; exfalso; exact hne ⟨rfl, by omega⟩
  · simp [ha]

private theorem coeff_monomial_mul_eq_zero (Q : AzPolynomial K) (d : ℕ) (c : K) (k : ℕ)
    (hk : k > d + (Q.coeffs.size - 1)) :
    coeff ((monomial d c) * Q) k = 0 := by
  have h := toPoly_mul (monomial d c) Q
  have hc := congrArg (fun p => Polynomial.coeff p k) h
  rw [coeff_toPoly_eq] at hc
  rw [hc, toPoly_monomial, Polynomial.coeff_mul]
  simp_rw [Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  by_cases ha : d = a
  · subst ha
    simp only [ite_true]
    have : (AzPolynomial.toPoly Q).coeff b = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hnd := AzPolynomial.natDegree_toPoly Q
      change (AzPolynomial.toPoly Q).natDegree < b
      rw [hnd]
      show Q.coeffs.size - 1 < b
      omega
    rw [this, mul_zero]
  · simp [ha]

/-! ### Step coefficient properties -/

-- Abstract step: R - monomial * Q zeroes out coefficients at j and above
private theorem sub_monomial_mul_coeffs_zero (q : ℕ) (Q : AzPolynomial K)
    (j : ℕ) (R : AzPolynomial K) (bq : K) (hbq : bq = Q.coeff q) (hbq_ne : bq ≠ 0)
    (hjq : j ≥ q) (hq : q = Q.coeffs.size - 1)
    (h_above : ∀ i, i > j → R.coeff i = 0) :
    ∀ i, i ≥ j → (R - monomial (j - q) (R.coeff j / bq) * Q).coeff i = 0 := by
  intro i hi
  rcases eq_or_lt_of_le hi with rfl | hgt
  · simp only [coeff_sub]
    have hjq2 : j - q + q = j := by omega
    have hmul : coeff (monomial (j - q) (R.coeff j / bq) * Q) (j - q + q) =
        (R.coeff j / bq) * Q.coeff q :=
      coeff_monomial_mul' Q (j - q) _ q
    rw [hjq2] at hmul
    have : coeff (monomial (j - q) (R.coeff j / bq) * Q) j =
        (R.coeff j / bq) * Q.coeff q := hmul
    rw [this, hbq, div_mul_cancel₀]
    · simp
    · rwa [hbq] at hbq_ne
  · simp only [coeff_sub]
    rw [coeff_monomial_mul_eq_zero Q (j - q) _ i (by omega)]; simp [h_above i hgt]

-- Link quoRemStep to the abstract form
private theorem quoRemStep_snd_eq (q : ℕ) (bq : K) (Q : AzPolynomial K)
    (j : ℕ) (C R : AzPolynomial K) :
    (quoRemStep q bq Q j (C, R)).2 = R - monomial (j - q) (R.coeff j / bq) * Q := by
  rfl

-- Combined step coefficient theorem
private theorem quoRemStep_coeffs_zero (q : ℕ) (bq : K) (Q : AzPolynomial K)
    (j : ℕ) (C R : AzPolynomial K) (hbq : bq = Q.coeff q) (hbq_ne : bq ≠ 0)
    (hjq : j ≥ q) (hq : q = Q.coeffs.size - 1)
    (h_above : ∀ i, i > j → R.coeff i = 0) :
    ∀ i, i ≥ j → (quoRemStep q bq Q j (C, R)).2.coeff i = 0 := by
  rw [quoRemStep_snd_eq]
  exact sub_monomial_mul_coeffs_zero q Q j R bq hbq hbq_ne hjq hq h_above

/-! ### Fold degree bound -/

private theorem rem_coeffs_zero_fold
    (q : ℕ) (bq : K) (Q : AzPolynomial K) (p : ℕ)
    (hbq : bq = Q.coeff q) (hbq_ne : bq ≠ 0) (hq : q = Q.coeffs.size - 1)
    (hpq : p ≥ q)
    (n : ℕ) (hn : n ≤ p - q + 1)
    (C₀ R₀ : AzPolynomial K)
    (h₀ : ∀ i, i ≥ p + 1 → R₀.coeff i = 0) :
    let (_, R') := (List.range n).foldl
      (fun cr k => quoRemStep q bq Q (p - k) cr) (C₀, R₀)
    ∀ i, i ≥ p + 1 - n → R'.coeff i = 0 := by
  induction n generalizing C₀ R₀ with
  | zero => simp; intro i hi; exact h₀ i (by omega)
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cr_n := (List.range n).foldl (fun cr k => quoRemStep q bq Q (p - k) cr) (C₀, R₀)
    have ih_result := ih (by omega) C₀ R₀ h₀
    have h_step := quoRemStep_coeffs_zero q bq Q (p - n) cr_n.1 cr_n.2 hbq hbq_ne
      (by omega) hq (fun i hi => ih_result i (by omega))
    intro i hi
    exact h_step i (by omega)
/-! ### Degree bound on remainder -/

omit [DecidableEq K] in
private theorem coeff_zero_above_size (P : AzPolynomial K) (i : ℕ) (hi : i ≥ P.coeffs.size) :
    P.coeff i = 0 := by
  simp [coeff, Array.getElem?_eq_none (by omega : P.coeffs.size ≤ i)]

theorem degree_toPoly_rem_lt (P Q : AzPolynomial K)
    (hQ : AzPolynomial.toPoly Q ≠ 0) :
    (AzPolynomial.toPoly (rem P Q)).degree < (AzPolynomial.toPoly Q).degree := by
  rw [AzPolynomial.degree_toPoly Q]
  by_cases hQs : Q.coeffs = #[]
  · exfalso; apply hQ
    have : Q = 0 := AzPolynomial.ext hQs
    rw [this]; exact toPoly_zero
  · have hQne : Q.coeffs.size ≠ 0 := by intro h; apply hQs; exact Array.eq_empty_of_size_eq_zero h
    simp only [Azurite.AzPolynomial.degree, hQs, ↓reduceIte]
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    rw [coeff_toPoly_eq]
    by_cases hPs : P.coeffs.size = 0
    · unfold rem quoRem; simp [hPs]
      simp [coeff, Array.getElem?_eq_none (by omega : P.coeffs.size ≤ n)]
    · by_cases hPQ : P.coeffs.size < Q.coeffs.size
      · unfold rem quoRem
        have hQne2 : ¬(Q.coeffs.size = 0) := hQne
        simp only [hQne2, hPs, hPQ, ↓reduceIte]
        exact coeff_zero_above_size P n (by
          have : (n : ℤ) ≥ ↑(Q.coeffs.size - 1) := by exact_mod_cast hn
          omega)
      · unfold rem quoRem
        have hQne2 : ¬(Q.coeffs.size = 0) := hQne
        have hPne : ¬(P.coeffs.size = 0) := hPs
        simp only [hQne2, hPne, hPQ, ↓reduceIte]
        have hle : Q.coeffs.size ≤ P.coeffs.size := Nat.not_lt.mp hPQ
        have hbq_ne : Q.leadingCoeff ≠ 0 := by
          rw [← leadingCoeff_toPoly]
          exact Polynomial.leadingCoeff_ne_zero.mpr hQ
        have h := rem_coeffs_zero_fold
          (Q.coeffs.size - 1) Q.leadingCoeff Q (P.coeffs.size - 1)
          rfl hbq_ne rfl (by omega)
          (P.coeffs.size - Q.coeffs.size + 1) (by omega)
          0 P (fun i hi => coeff_zero_above_size P i (by omega))
        have hnd : Q.natDegree = Q.coeffs.size - 1 := rfl
        have hn3 : n ≥ Q.coeffs.size - 1 := by rw [← hnd]; exact hn
        have hthresh : P.coeffs.size - 1 + 1 - (P.coeffs.size - Q.coeffs.size + 1) = Q.coeffs.size - 1 := by
          omega
        rw [hthresh] at h
        exact h n hn3

/-! ### Equivalence with Mathlib's div/mod -/

theorem toPoly_quo (P Q : AzPolynomial K) (hQ : AzPolynomial.toPoly Q ≠ 0) :
    AzPolynomial.toPoly (quo P Q) = AzPolynomial.toPoly P / AzPolynomial.toPoly Q := by
  have h_our := toPoly_quoRem_eq P Q
  have h_ml := EuclideanDomain.div_add_mod (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
  have h_deg_our := degree_toPoly_rem_lt P Q hQ
  have h_deg_ml := Polynomial.degree_mod_lt (AzPolynomial.toPoly P) hQ
  by_contra h_ne
  have h_ne2 : AzPolynomial.toPoly (quo P Q) - AzPolynomial.toPoly P / AzPolynomial.toPoly Q ≠ 0 :=
    sub_ne_zero.mpr h_ne
  have h_sub : (AzPolynomial.toPoly (quo P Q) - AzPolynomial.toPoly P / AzPolynomial.toPoly Q) *
      AzPolynomial.toPoly Q =
      AzPolynomial.toPoly P % AzPolynomial.toPoly Q - AzPolynomial.toPoly (rem P Q) := by
    have h_eq : AzPolynomial.toPoly (quo P Q) * AzPolynomial.toPoly Q +
        AzPolynomial.toPoly (rem P Q) =
        (AzPolynomial.toPoly P / AzPolynomial.toPoly Q) * AzPolynomial.toPoly Q +
          AzPolynomial.toPoly P % AzPolynomial.toPoly Q := by
      have : AzPolynomial.toPoly (quo P Q) * AzPolynomial.toPoly Q +
        AzPolynomial.toPoly (rem P Q) = AzPolynomial.toPoly P := h_our.symm
      rw [this]; rw [mul_comm] at h_ml; exact h_ml.symm
    have h3 : AzPolynomial.toPoly (quo P Q) * AzPolynomial.toPoly Q =
        (AzPolynomial.toPoly P / AzPolynomial.toPoly Q) * AzPolynomial.toPoly Q +
          AzPolynomial.toPoly P % AzPolynomial.toPoly Q -
            AzPolynomial.toPoly (rem P Q) := by rw [← h_eq]; ring
    calc (AzPolynomial.toPoly (quo P Q) - AzPolynomial.toPoly P / AzPolynomial.toPoly Q) *
          AzPolynomial.toPoly Q =
        AzPolynomial.toPoly (quo P Q) * AzPolynomial.toPoly Q -
          (AzPolynomial.toPoly P / AzPolynomial.toPoly Q) * AzPolynomial.toPoly Q := by ring
      _ = AzPolynomial.toPoly P % AzPolynomial.toPoly Q -
            AzPolynomial.toPoly (rem P Q) := by rw [h3]; ring
  have h_rhs : (AzPolynomial.toPoly P % AzPolynomial.toPoly Q -
      AzPolynomial.toPoly (rem P Q)).degree < (AzPolynomial.toPoly Q).degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt h_deg_ml h_deg_our)
  have h_lhs : ((AzPolynomial.toPoly (quo P Q) - AzPolynomial.toPoly P / AzPolynomial.toPoly Q) *
      AzPolynomial.toPoly Q).degree ≥ (AzPolynomial.toPoly Q).degree := by
    rw [@Polynomial.degree_mul K _ _]
    rw [Polynomial.degree_eq_natDegree h_ne2, Polynomial.degree_eq_natDegree hQ]
    exact_mod_cast Nat.le_add_left _ _
  rw [h_sub] at h_lhs
  exact absurd h_rhs (not_lt.mpr h_lhs)

theorem toPoly_rem (P Q : AzPolynomial K) (hQ : AzPolynomial.toPoly Q ≠ 0) :
    AzPolynomial.toPoly (rem P Q) = AzPolynomial.toPoly P % AzPolynomial.toPoly Q := by
  have h_eq := toPoly_quoRem_eq P Q
  have h_quo := toPoly_quo P Q hQ
  have h_ml := EuclideanDomain.div_add_mod (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
  rw [h_quo] at h_eq
  have h_ml2 : AzPolynomial.toPoly P =
      (AzPolynomial.toPoly P / AzPolynomial.toPoly Q) * AzPolynomial.toPoly Q +
        AzPolynomial.toPoly P % AzPolynomial.toPoly Q := by
    rw [mul_comm]; exact h_ml.symm
  exact _root_.add_left_cancel (h_eq.symm.trans h_ml2)

theorem ofPoly_quo (p q : Polynomial K) (hq : q ≠ 0) :
    AzPolynomial.ofPoly (p / q) = quo (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q) := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_quo _ _ (by rwa [toPoly_ofPoly]), toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

theorem ofPoly_rem (p q : Polynomial K) (hq : q ≠ 0) :
    AzPolynomial.ofPoly (p % q) = rem (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q) := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_rem _ _ (by rwa [toPoly_ofPoly]), toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
