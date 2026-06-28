/-
  Correctness of `AzPolynomial.exactDiv` (synthetic exact division).

  When `Q ∣ P` in `Polynomial R` and `Q ≠ 0`, the function
  `Azurite.AzPolynomial.exactDiv P Q` returns a quotient `C` with
  `C * Q = P` (`exactDiv_spec`). The proof has two parts:

  * **Fold invariant** (mirroring `AzPolynomial.Equiv.QuoRem`):
    after running the synthetic-division loop, `P = C * Q + Rem`
    holds regardless of whether the coefficient division was exact.
  * **Remainder vanishes**: when `Q ∣ P`, every step's leading-coefficient
    division is exact (by the `ExactDiv` lawfulness field), so each step
    zeros out the next coefficient of the running remainder. After the
    fold, `Rem` has degree below `Q`, and the divisibility relation
    `Q ∣ Rem` (preserved by the algorithm) forces `Rem = 0`.
-/
import Azurite.AzPolynomial.ExactDiv
import Azurite.AzPolynomial.Equiv.QuoRem
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Algebra
import Mathlib.Algebra.Polynomial.Div

set_option linter.unusedSectionVars false

namespace Azurite.AzPolynomial

open Polynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]

/-! ### Step-level lemma -/

/-- One step of `exactDivStep` preserves the dividend `P` modulo the
    `(C, R) → C * Q + R` accounting. Same shape as `quoRemStep_identity`
    from the Field-side file. -/
private theorem exactDivStep_preserves
    (q : ℕ) (bq : R) (Q : AzPolynomial R) (j : ℕ)
    (C R₀ : AzPolynomial R) :
    mulBasecaseFold (exactDivStep q bq Q j (C, R₀)).1 Q +
        (exactDivStep q bq Q j (C, R₀)).2 =
      mulBasecaseFold C Q + R₀ := by
  show (C + monomial (j - q) (Azurite.ExactDiv.exactDiv (R₀.coeff j) bq)) * Q +
      (R₀ - monomial (j - q) (Azurite.ExactDiv.exactDiv (R₀.coeff j) bq) * Q) =
      C * Q + R₀
  ring

/-! ### Fold invariant -/

/-- Generic foldl invariant — reusable for both `exactDivStep`-folds. -/
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

private theorem exactDiv_fold_eq (q : ℕ) (bq : R) (Q P : AzPolynomial R)
    (p : ℕ) (n : ℕ) (C₀ R₀ : AzPolynomial R)
    (h : P = mulBasecaseFold C₀ Q + R₀) :
    let (C', R') :=
      (List.range n).foldl (fun cr k => exactDivStep q bq Q (p - k) cr) (C₀, R₀)
    P = mulBasecaseFold C' Q + R' := by
  apply foldl_preserves_inv (fun j cr => exactDivStep q bq Q j cr)
      (fun cr => P = mulBasecaseFold cr.1 Q + cr.2)
  · intro j ⟨C, R⟩ hCR
    have h_step := exactDivStep_preserves q bq Q j C R
    rw [hCR]
    rw [← h_step]
  · exact h

private theorem base_invariant (P Q : AzPolynomial R) :
    P = mulBasecaseFold 0 Q + P := by
  show P = (0 : AzPolynomial R) * Q + P
  ext n
  simp only [coeff_add, coeff_mul]
  simp [coeff]

theorem exactDivQuoRem_eq (P Q : AzPolynomial R) :
    P = mulBasecaseFold (exactDivQuoRem P Q).1 Q + (exactDivQuoRem P Q).2 := by
  unfold exactDivQuoRem
  split
  · dsimp only; exact base_invariant P Q
  · split
    · dsimp only; exact base_invariant P Q
    · split
      · dsimp only; exact base_invariant P Q
      · exact exactDiv_fold_eq
          (Q.coeffs.size - 1) Q.leadingCoeff Q P
          (P.coeffs.size - 1) (P.coeffs.size - Q.coeffs.size + 1) 0 P
          (base_invariant P Q)

theorem toPoly_exactDivQuoRem_eq (P Q : AzPolynomial R) :
    AzPolynomial.toPoly P =
      AzPolynomial.toPoly (exactDivQuoRem P Q).1 * AzPolynomial.toPoly Q +
        AzPolynomial.toPoly (exactDivQuoRem P Q).2 := by
  have h := exactDivQuoRem_eq P Q
  have h2 := congr_arg AzPolynomial.toPoly h
  simp only [toPoly_add, Azurite.AzPolynomial.toPoly_mulBasecaseFold] at h2
  exact h2

/-! ### Coefficient helpers (CommRing-only versions of `Equiv/QuoRem.lean` helpers) -/

private theorem coeff_monomial_mul' (Q : AzPolynomial R) (d : ℕ) (c : R) (k : ℕ) :
    coeff ((monomial d c) * Q) (d + k) = c * Q.coeff k := by
  have h := Azurite.AzPolynomial.toPoly_mul (monomial d c) Q
  have hc := congr_fun (congr_arg Polynomial.coeff h) (d + k)
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

private theorem coeff_monomial_mul_eq_zero (Q : AzPolynomial R) (d : ℕ) (c : R) (k : ℕ)
    (hk : k > d + (Q.coeffs.size - 1)) :
    coeff ((monomial d c) * Q) k = 0 := by
  have h := Azurite.AzPolynomial.toPoly_mul (monomial d c) Q
  have hc := congr_fun (congr_arg Polynomial.coeff h) k
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

omit [DecidableEq R] in
private theorem coeff_zero_above_size (P : AzPolynomial R) (i : ℕ)
    (hi : i ≥ P.coeffs.size) : P.coeff i = 0 := by
  simp [coeff, Array.getElem?_eq_none (by omega : P.coeffs.size ≤ i)]

/-! ### Step-level coefficient-vanishing lemma -/

section LawfulExactDiv

variable [IsDomain R]

/-- One step of `exactDivStep` at index `j` zeros out coefficient `j`
    (when the leading coefficient divides) and all higher coefficients
    (which were already zero by induction). -/
private theorem exactDivStep_snd_coeffs_zero
    (q : ℕ) (Q : AzPolynomial R) (j : ℕ) (C R₀ : AzPolynomial R)
    (hbq : Q.leadingCoeff = Q.coeff q) (hbq_ne : Q.leadingCoeff ≠ 0)
    (hjq : j ≥ q) (hq : q = Q.coeffs.size - 1)
    (h_dvd_lead : Q.leadingCoeff ∣ R₀.coeff j)
    (h_above : ∀ i, i > j → R₀.coeff i = 0) :
    ∀ i, i ≥ j → (exactDivStep q Q.leadingCoeff Q j (C, R₀)).2.coeff i = 0 := by
  intro i hi
  show (R₀ - monomial (j - q) (Azurite.ExactDiv.exactDiv (R₀.coeff j) Q.leadingCoeff) * Q).coeff i = 0
  rcases eq_or_lt_of_le hi with rfl | hgt
  · simp only [coeff_sub]
    have hjq2 : j - q + q = j := by omega
    have hmul : coeff (monomial (j - q) (Azurite.ExactDiv.exactDiv (R₀.coeff j) Q.leadingCoeff) * Q) (j - q + q) =
        (Azurite.ExactDiv.exactDiv (R₀.coeff j) Q.leadingCoeff) * Q.coeff q :=
      coeff_monomial_mul' Q (j - q) _ q
    rw [hjq2] at hmul
    rw [hmul, ← hbq]
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ h_dvd_lead hbq_ne]
    simp
  · simp only [coeff_sub]
    rw [coeff_monomial_mul_eq_zero Q (j - q) _ i (by omega)]
    simp [h_above i hgt]

/-! ### Polynomial-level divisibility implies coefficient-level divisibility at the top -/

private theorem leadingCoeff_dvd_top_coeff (R₀ Q : AzPolynomial R) (j q : ℕ)
    (hQ_dvd : AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly R₀) (hq : q = Q.coeffs.size - 1)
    (hQne : Q.leadingCoeff ≠ 0) (hjq : j ≥ q)
    (h_above : ∀ i, i > j → R₀.coeff i = 0) :
    Q.leadingCoeff ∣ R₀.coeff j := by
  -- Decompose AzPolynomial.toPoly R₀ = AzPolynomial.toPoly Q * C'.
  rcases hQ_dvd with ⟨C', hC'⟩
  -- AzPolynomial.toPoly Q is nonzero (its leadingCoeff is Q.leadingCoeff ≠ 0).
  have hQ_toPoly_ne : AzPolynomial.toPoly Q ≠ 0 := by
    intro h
    apply hQne
    have := leadingCoeff_toPoly Q
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact this.symm
  by_cases hC'_zero : C' = 0
  · -- C' = 0 means AzPolynomial.toPoly R₀ = 0, so R₀.coeff j = 0.
    subst hC'_zero
    have hR_zero : AzPolynomial.toPoly R₀ = 0 := by rw [hC', mul_zero]
    have : R₀.coeff j = 0 := by
      rw [← coeff_toPoly_eq R₀ j, hR_zero, Polynomial.coeff_zero]
    rw [this]; exact dvd_zero _
  · -- C' ≠ 0. Use the natDegree factorization in the domain.
    have h_natDeg : (AzPolynomial.toPoly Q * C').natDegree =
        (AzPolynomial.toPoly Q).natDegree + C'.natDegree :=
      Polynomial.natDegree_mul hQ_toPoly_ne hC'_zero
    have hQ_natDeg : (AzPolynomial.toPoly Q).natDegree = q := by
      rw [AzPolynomial.natDegree_toPoly Q]; exact hq.symm
    have hR_natDeg : (AzPolynomial.toPoly Q * C').natDegree ≤ j := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [← hC']; rw [coeff_toPoly_eq R₀ i]; exact h_above i hi
    have hC'_natDeg : C'.natDegree ≤ j - q := by
      rw [h_natDeg, hQ_natDeg] at hR_natDeg; omega
    -- Compute (AzPolynomial.toPoly Q * C').coeff j.
    have h_coeff : (AzPolynomial.toPoly Q * C').coeff j = Q.leadingCoeff * C'.coeff (j - q) := by
      rw [Polynomial.coeff_mul]
      have hmem : (q, j - q) ∈ Finset.antidiagonal j := by
        simp [Finset.mem_antidiagonal]; omega
      rw [← Finset.add_sum_erase _ _ hmem]
      have h_other : ∑ x ∈ (Finset.antidiagonal j).erase (q, j - q),
          (AzPolynomial.toPoly Q).coeff x.1 * C'.coeff x.2 = 0 := by
        apply Finset.sum_eq_zero
        intro ⟨a, b⟩ hab
        simp only [Finset.mem_erase, Finset.mem_antidiagonal, Ne, Prod.mk.injEq] at hab
        obtain ⟨hne, hab⟩ := hab
        by_cases ha_le : a ≤ q
        · rcases lt_or_eq_of_le ha_le with ha_lt | ha_eq
          · have hb_gt : b > j - q := by omega
            have : C'.coeff b = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            rw [this, mul_zero]
          · exfalso; apply hne; exact ⟨ha_eq, by omega⟩
        · push Not at ha_le
          have : (AzPolynomial.toPoly Q).coeff a = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ_natDeg]; omega)
          rw [this, zero_mul]
      rw [h_other, add_zero]
      have h_lead : (AzPolynomial.toPoly Q).coeff q = Q.leadingCoeff := by
        have := leadingCoeff_toPoly Q
        have hnd : (AzPolynomial.toPoly Q).natDegree = q := hQ_natDeg
        rw [Polynomial.leadingCoeff, hnd] at this
        exact this
      rw [h_lead]
    have hR_coeff_eq : R₀.coeff j = Q.leadingCoeff * C'.coeff (j - q) := by
      rw [← coeff_toPoly_eq R₀ j, hC']; exact h_coeff
    rw [hR_coeff_eq]; exact ⟨C'.coeff (j - q), rfl⟩

/-! ### Divisibility preserved across one step -/

private theorem exactDivStep_preserves_dvd
    (q : ℕ) (bq : R) (Q : AzPolynomial R) (j : ℕ)
    (C R₀ : AzPolynomial R) (hdvd : AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly R₀) :
    AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly (exactDivStep q bq Q j (C, R₀)).2 := by
  show AzPolynomial.toPoly Q ∣
    AzPolynomial.toPoly (R₀ - monomial (j - q) (Azurite.ExactDiv.exactDiv (R₀.coeff j) bq) * Q)
  rw [toPoly_sub, Azurite.AzPolynomial.toPoly_mul]
  exact dvd_sub hdvd ⟨_, mul_comm _ _⟩

/-! ### Fold-level invariants (coefficient vanishing + divisibility) -/

private theorem rem_coeffs_zero_and_dvd_fold
    (q : ℕ) (Q : AzPolynomial R) (p : ℕ)
    (hbq : Q.leadingCoeff = Q.coeff q) (hbq_ne : Q.leadingCoeff ≠ 0)
    (hq : q = Q.coeffs.size - 1) (hpq : p ≥ q)
    (n : ℕ) (hn : n ≤ p - q + 1)
    (C₀ R₀ : AzPolynomial R)
    (h₀_zeros : ∀ i, i ≥ p + 1 → R₀.coeff i = 0)
    (h₀_dvd : AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly R₀) :
    let (_, R') := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀)
    (∀ i, i ≥ p + 1 - n → R'.coeff i = 0) ∧
      AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly R' := by
  induction n generalizing C₀ R₀ with
  | zero =>
    refine ⟨?_, h₀_dvd⟩
    intro i hi; exact h₀_zeros i (by omega)
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cr_n := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀)
    have ih_result := ih (by omega) C₀ R₀ h₀_zeros h₀_dvd
    obtain ⟨ih_zeros, ih_dvd⟩ := ih_result
    -- Step at j = p - n.
    have h_jq : p - n ≥ q := by omega
    -- Get bq ∣ R.coeff (p - n).
    have h_lead_dvd : Q.leadingCoeff ∣ cr_n.2.coeff (p - n) :=
      leadingCoeff_dvd_top_coeff cr_n.2 Q (p - n) q ih_dvd hq hbq_ne h_jq
        (fun i hi => ih_zeros i (by omega))
    refine ⟨?_, ?_⟩
    · -- Coefficient vanishing after the step.
      intro i hi
      exact exactDivStep_snd_coeffs_zero q Q (p - n) cr_n.1 cr_n.2 hbq hbq_ne
        h_jq hq h_lead_dvd (fun i hi => ih_zeros i (by omega)) i (by omega)
    · -- Divisibility preserved.
      exact exactDivStep_preserves_dvd q Q.leadingCoeff Q (p - n) cr_n.1 cr_n.2 ih_dvd

/-! ### Fold-level invariant for the general (with-remainder) Euclidean division -/

/-- **Euclidean fold invariant (general remainder).**  Like `rem_coeffs_zero_and_dvd_fold`, but
    tracking a fixed target remainder `Rem` of degree `< deg Q`: the running remainder stays
    congruent to `Rem` modulo `Q` (`Q ∣ R' − Rem`), and its coefficients above the processed window
    vanish.  Combined with the unconditional division identity this forces the synthetic remainder to
    have degree `< deg Q`, i.e. the synthetic division recovers the integral Euclidean division. -/
private theorem rem_coeffs_zero_euclidean_fold
    (q : ℕ) (Q : AzPolynomial R) (p : ℕ) (Rem : Polynomial R)
    (hbq : Q.leadingCoeff = Q.coeff q) (hbq_ne : Q.leadingCoeff ≠ 0)
    (hq : q = Q.coeffs.size - 1) (hpq : p ≥ q)
    (hRem_deg : ∀ i, i ≥ q → Rem.coeff i = 0)
    (n : ℕ) (hn : n ≤ p - q + 1)
    (C₀ R₀ : AzPolynomial R)
    (h₀_zeros : ∀ i, i ≥ p + 1 → R₀.coeff i = 0)
    (h₀_dvd : AzPolynomial.toPoly Q ∣ (AzPolynomial.toPoly R₀ - Rem)) :
    let (_, R') := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀)
    (∀ i, i ≥ p + 1 - n → R'.coeff i = 0) ∧
      AzPolynomial.toPoly Q ∣ (AzPolynomial.toPoly R' - Rem) := by
  induction n generalizing C₀ R₀ with
  | zero =>
    refine ⟨?_, h₀_dvd⟩
    intro i hi; exact h₀_zeros i (by omega)
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cr_n := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀)
    have ih_result := ih (by omega) C₀ R₀ h₀_zeros h₀_dvd
    obtain ⟨ih_zeros, ih_dvd⟩ := ih_result
    have h_jq : p - n ≥ q := by omega
    have hcoe : ∀ i, (AzPolynomial.ofPoly (AzPolynomial.toPoly cr_n.2 - Rem)).coeff i
        = (AzPolynomial.toPoly cr_n.2 - Rem).coeff i := by
      intro i; rw [← coeff_toPoly_eq, toPoly_ofPoly]
    have h_lead_dvd : Q.leadingCoeff ∣ cr_n.2.coeff (p - n) := by
      have hd := leadingCoeff_dvd_top_coeff (AzPolynomial.ofPoly (AzPolynomial.toPoly cr_n.2 - Rem)) Q (p - n) q
        (by rw [toPoly_ofPoly]; exact ih_dvd) hq hbq_ne h_jq
        (fun i hi => by
          rw [hcoe, Polynomial.coeff_sub, coeff_toPoly_eq, ih_zeros i (by omega),
            hRem_deg i (by omega), sub_zero])
      rw [hcoe, Polynomial.coeff_sub, coeff_toPoly_eq, hRem_deg (p - n) h_jq, sub_zero] at hd
      exact hd
    refine ⟨?_, ?_⟩
    · intro i hi
      exact exactDivStep_snd_coeffs_zero q Q (p - n) cr_n.1 cr_n.2 hbq hbq_ne
        h_jq hq h_lead_dvd (fun i hi => ih_zeros i (by omega)) i (by omega)
    · show AzPolynomial.toPoly Q ∣
        (AzPolynomial.toPoly (exactDivStep q Q.leadingCoeff Q (p - n) cr_n).2 - Rem)
      have hstep : (exactDivStep q Q.leadingCoeff Q (p - n) cr_n).2
          = cr_n.2 - mulBasecaseFold (monomial (p - n - q)
              (Azurite.ExactDiv.exactDiv (cr_n.2.coeff (p - n)) Q.leadingCoeff)) Q := rfl
      rw [hstep, toPoly_sub, Azurite.AzPolynomial.toPoly_mulBasecaseFold]
      have hrw : AzPolynomial.toPoly cr_n.2
            - AzPolynomial.toPoly (monomial (p - n - q)
                (Azurite.ExactDiv.exactDiv (cr_n.2.coeff (p - n)) Q.leadingCoeff))
              * AzPolynomial.toPoly Q - Rem
          = (AzPolynomial.toPoly cr_n.2 - Rem)
            - AzPolynomial.toPoly (monomial (p - n - q)
                (Azurite.ExactDiv.exactDiv (cr_n.2.coeff (p - n)) Q.leadingCoeff))
              * AzPolynomial.toPoly Q := by ring
      rw [hrw]
      exact dvd_sub ih_dvd ⟨_, mul_comm _ _⟩

/-- **Synthetic division recovers the integral Euclidean division.**  If an integral Euclidean
    division `toPoly A = Q · toPoly B + Rem` exists with `deg Rem < deg(toPoly B)` (and `B ≠ 0`),
    then `exactDivQuoRem A B` produces exactly that remainder: `toPoly (exactDivQuoRem A B).2 = Rem`.
    This is the fraction-free analogue of `toPoly_rem`/`degree_toPoly_rem_lt` from the field side —
    the exactness of every coefficient division is *supplied* by the existence of `Q`, `Rem`. -/
theorem toPoly_exactDivQuoRem_snd_of_euclidean (A B : AzPolynomial R) (Q Rem : Polynomial R)
    (hB : AzPolynomial.toPoly B ≠ 0)
    (hdiv : AzPolynomial.toPoly A = Q * AzPolynomial.toPoly B + Rem)
    (hdeg : Rem.degree < (AzPolynomial.toPoly B).degree) :
    AzPolynomial.toPoly (exactDivQuoRem A B).2 = Rem := by
  have hB_lead_ne : B.leadingCoeff ≠ 0 := by
    intro h; apply hB; rw [← leadingCoeff_toPoly] at h
    exact Polynomial.leadingCoeff_eq_zero.mp h
  have hB_size : B.coeffs.size ≠ 0 := by
    intro h; apply hB
    have : B = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  have hdB : (AzPolynomial.toPoly B).degree = (B.coeffs.size - 1 : ℕ) := by
    rw [Polynomial.degree_eq_natDegree hB]
    norm_cast
    exact AzPolynomial.natDegree_toPoly B
  have hRem_deg : ∀ i, i ≥ B.coeffs.size - 1 → Rem.coeff i = 0 := by
    intro i hi
    apply Polynomial.coeff_eq_zero_of_degree_lt
    exact lt_of_lt_of_le (hdeg.trans_eq hdB) (by exact_mod_cast hi)
  -- Step 1: the synthetic remainder has degree `< deg B`.
  have hrem_deg : (AzPolynomial.toPoly (exactDivQuoRem A B).2).degree
      < (AzPolynomial.toPoly B).degree := by
    rw [hdB]
    unfold exactDivQuoRem
    split_ifs with hBs hAs hABs
    · exact absurd hBs hB_size
    · -- `A = 0`
      have hA0 : AzPolynomial.toPoly A = 0 := by
        have : A = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hAs)
        rw [this]; exact toPoly_zero
      show (AzPolynomial.toPoly A).degree < _
      rw [hA0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · -- `deg A < deg B`
      show (AzPolynomial.toPoly A).degree < _
      apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
      intro m hm
      rw [coeff_toPoly_eq]
      exact coeff_zero_above_size A m (by omega)
    · -- main fold branch: `deg A ≥ deg B`
      have hP_size : A.coeffs.size ≥ B.coeffs.size := Nat.not_lt.mp hABs
      have h₀dvd : AzPolynomial.toPoly B ∣ (AzPolynomial.toPoly A - Rem) :=
        ⟨Q, by rw [hdiv]; ring⟩
      have h_fold := rem_coeffs_zero_euclidean_fold (B.coeffs.size - 1) B (A.coeffs.size - 1) Rem
        rfl hB_lead_ne rfl (by omega) hRem_deg (A.coeffs.size - B.coeffs.size + 1) (by omega)
        0 A (fun i hi => coeff_zero_above_size A i (by omega)) h₀dvd
      obtain ⟨h_zeros, _⟩ := h_fold
      apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
      intro m hm
      rw [coeff_toPoly_eq]
      exact h_zeros m (by omega)
  -- Step 2: an integral Euclidean division is unique, so the remainders agree.
  have hkey : (AzPolynomial.toPoly (exactDivQuoRem A B).1 - Q) * AzPolynomial.toPoly B
      = Rem - AzPolynomial.toPoly (exactDivQuoRem A B).2 := by
    have huncond := toPoly_exactDivQuoRem_eq A B
    linear_combination hdiv - huncond
  by_contra hne
  have hne' : Rem - AzPolynomial.toPoly (exactDivQuoRem A B).2 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hne)
  have hdvd : AzPolynomial.toPoly B ∣ (Rem - AzPolynomial.toPoly (exactDivQuoRem A B).2) :=
    ⟨AzPolynomial.toPoly (exactDivQuoRem A B).1 - Q, by rw [← hkey]; ring⟩
  have h1 := Polynomial.degree_le_of_dvd hdvd hne'
  have h2 : (Rem - AzPolynomial.toPoly (exactDivQuoRem A B).2).degree
      < (AzPolynomial.toPoly B).degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg hrem_deg)
  exact absurd h1 (not_le.mpr h2)

/-! ### Pseudo-division: a `lcof(Q)^M`-scaled dividend divides exactly -/

/-- **Pseudo-division fold invariant.**  Running the synthetic-division loop on a dividend whose every
    coefficient is divisible by `lcof(Q)^M` (with `M = p - q + 1` the number of steps), each step's
    leading-coefficient division is exact: after `n` steps the running remainder has its high
    coefficients zeroed *and* every coefficient is divisible by `lcof(Q)^(M-n)` (the scaling supplies
    exactly one `lcof(Q)` per step).  This is the classical fraction-free pseudo-division integrality. -/
private theorem pseudoDiv_coeffs_zero_dvd_fold
    (q : ℕ) (Q : AzPolynomial R) (p M : ℕ)
    (hbq : Q.leadingCoeff = Q.coeff q) (hbq_ne : Q.leadingCoeff ≠ 0)
    (hq : q = Q.coeffs.size - 1) (hpq : p ≥ q) (hM : M = p - q + 1)
    (n : ℕ) (hn : n ≤ M)
    (C₀ R₀ : AzPolynomial R)
    (h₀_zeros : ∀ i, i ≥ p + 1 → R₀.coeff i = 0)
    (h₀_dvd : ∀ i, Q.leadingCoeff ^ M ∣ R₀.coeff i) :
    let (_, R') := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀)
    (∀ i, i ≥ p + 1 - n → R'.coeff i = 0) ∧
      (∀ i, Q.leadingCoeff ^ (M - n) ∣ R'.coeff i) := by
  induction n generalizing C₀ R₀ with
  | zero =>
    refine ⟨fun i hi => h₀_zeros i (by omega), ?_⟩
    intro i; rw [Nat.sub_zero]; exact h₀_dvd i
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cr_n := (List.range n).foldl
      (fun cr k => exactDivStep q Q.leadingCoeff Q (p - k) cr) (C₀, R₀) with hcr
    obtain ⟨ih_zeros, ih_dvd⟩ := ih (by omega) C₀ R₀ h₀_zeros h₀_dvd
    have h_jq : p - n ≥ q := by omega
    have hMn0 : M - n ≠ 0 := by omega
    -- `bq ∣ cr_n.2.coeff (p - n)` because `bq^(M-n) ∣` it and `M - n ≥ 1`.
    have hbq_dvd_top : Q.leadingCoeff ∣ cr_n.2.coeff (p - n) :=
      (dvd_pow_self _ hMn0).trans (ih_dvd (p - n))
    set t := Azurite.ExactDiv.exactDiv (cr_n.2.coeff (p - n)) Q.leadingCoeff with ht
    have ht_mul : t * Q.leadingCoeff = cr_n.2.coeff (p - n) :=
      Azurite.ExactDiv.exactDiv_mul_self _ _ hbq_dvd_top hbq_ne
    -- `bq^(M-n-1) ∣ t`, by cancelling one `bq` from `bq^(M-n) ∣ bq * t`.
    have ht_dvd : Q.leadingCoeff ^ (M - n - 1) ∣ t := by
      have h1 : Q.leadingCoeff ^ (M - n) ∣ Q.leadingCoeff * t := by
        rw [mul_comm, ht_mul]; exact ih_dvd (p - n)
      have h2 : Q.leadingCoeff * Q.leadingCoeff ^ (M - n - 1) = Q.leadingCoeff ^ (M - n) := by
        rw [← pow_succ']; congr 1; omega
      rw [← h2] at h1
      exact (mul_dvd_mul_iff_left hbq_ne).mp h1
    refine ⟨?_, ?_⟩
    · -- High coefficients stay zeroed (one more index killed by the exact step).
      intro i hi
      exact exactDivStep_snd_coeffs_zero q Q (p - n) cr_n.1 cr_n.2 hbq hbq_ne
        h_jq hq hbq_dvd_top (fun i hi => ih_zeros i (by omega)) i (by omega)
    · -- Divisibility drops by exactly one power of `bq`.
      intro i
      have hstep : AzPolynomial.toPoly (exactDivStep q Q.leadingCoeff Q (p - n) cr_n).2
          = AzPolynomial.toPoly cr_n.2
            - AzPolynomial.toPoly (monomial (p - n - q) t) * AzPolynomial.toPoly Q := by
        show AzPolynomial.toPoly (cr_n.2 - mulBasecaseFold (monomial (p - n - q) t) Q) = _
        rw [toPoly_sub, Azurite.AzPolynomial.toPoly_mulBasecaseFold]
      rw [← coeff_toPoly_eq, hstep, Polynomial.coeff_sub, toPoly_monomial]
      apply dvd_sub
      · rw [coeff_toPoly_eq]; exact (pow_dvd_pow _ (by omega)).trans (ih_dvd i)
      · have hmcoeff : (Polynomial.monomial (p - n - q) t * AzPolynomial.toPoly Q).coeff i
            = t * ((Polynomial.X ^ (p - n - q) * AzPolynomial.toPoly Q).coeff i) := by
          rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul]
        rw [hmcoeff]
        exact ht_dvd.mul_right _

/-- **Pseudo-division remainder degree bound.**  If every coefficient of `A` is divisible by
    `lcof(Q)^M` where `M = deg A - deg B + 1` is the number of synthetic-division steps (so the
    dividend is a textbook pseudo-division scaling), then `exactDivQuoRem A Q` is exact: its
    remainder has degree `< deg Q`.  Concretely, the algorithm's `lcof(Q)^M`-scaled dividends
    (`tj^2 • P`, `(tj·sk) • P`, …) divide cleanly. -/
theorem degree_exactDivQuoRem_snd_lt_of_pow_dvd (A Q : AzPolynomial R)
    (hQ : AzPolynomial.toPoly Q ≠ 0) (hA : Q.coeffs.size ≤ A.coeffs.size)
    (hdvd : ∀ i, Q.leadingCoeff ^ (A.coeffs.size - Q.coeffs.size + 1) ∣ A.coeff i) :
    (AzPolynomial.toPoly (exactDivQuoRem A Q).2).degree < (AzPolynomial.toPoly Q).degree := by
  have hQ_lead_ne : Q.leadingCoeff ≠ 0 := by
    intro h; apply hQ; rw [← leadingCoeff_toPoly] at h
    exact Polynomial.leadingCoeff_eq_zero.mp h
  have hQ_size : Q.coeffs.size ≠ 0 := by
    intro h; apply hQ
    have : Q = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  have hA_size : A.coeffs.size ≠ 0 := by omega
  have hdQ : (AzPolynomial.toPoly Q).degree = (Q.coeffs.size - 1 : ℕ) := by
    rw [Polynomial.degree_eq_natDegree hQ]; norm_cast; exact AzPolynomial.natDegree_toPoly Q
  rw [hdQ]
  unfold exactDivQuoRem
  split_ifs with hQs hAQs
  · exact absurd hQs hQ_size
  · exact absurd hAQs (by omega)
  · -- main fold branch (`A.size = 0` auto-discharged by `hA_size`)
    have h_fold := pseudoDiv_coeffs_zero_dvd_fold (Q.coeffs.size - 1) Q (A.coeffs.size - 1)
      (A.coeffs.size - Q.coeffs.size + 1) rfl hQ_lead_ne rfl (by omega) (by omega)
      (A.coeffs.size - Q.coeffs.size + 1) le_rfl
      0 A (fun i hi => coeff_zero_above_size A i (by omega)) hdvd
    obtain ⟨h_zeros, _⟩ := h_fold
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro m hm
    rw [coeff_toPoly_eq]
    exact h_zeros m (by omega)

/-! ### Main correctness theorem -/

/-- **Correctness of `AzPolynomial.exactDiv`.** When `Q ≠ 0` and `Q ∣ P`
    (as polynomials over `R`), the synthetic exact-division loop produces
    a quotient `C` with `C * Q = P`. -/
theorem exactDiv_spec (P Q : AzPolynomial R) (hQ : AzPolynomial.toPoly Q ≠ 0)
    (hdvd : AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly P) :
    AzPolynomial.toPoly (exactDiv P Q) * AzPolynomial.toPoly Q = AzPolynomial.toPoly P := by
  have hQ_lead_ne : Q.leadingCoeff ≠ 0 := by
    intro h
    apply hQ
    rw [← leadingCoeff_toPoly] at h
    exact Polynomial.leadingCoeff_eq_zero.mp h
  have hQ_size_ne : Q.coeffs.size ≠ 0 := by
    intro h
    apply hQ
    show AzPolynomial.toPoly Q = 0
    have : Q = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  -- The fold invariant gives `P = exactDiv P Q * Q + rem`. Show rem = 0.
  have h_main : AzPolynomial.toPoly (exactDivQuoRem P Q).2 = 0 := by
    -- Case split: either P = 0 or sizes work for the main branch.
    unfold exactDivQuoRem
    by_cases hQs : Q.coeffs.size = 0
    · exact absurd hQs hQ_size_ne
    by_cases hPs : P.coeffs.size = 0
    · -- P = 0 (size 0), so toPoly P = 0; the spec is trivial.
      have hP_zero : AzPolynomial.toPoly P = 0 := by
        have : P = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hPs)
        rw [this, toPoly_zero]
      simp only [hQs, hPs, ↓reduceIte]
      exact hP_zero
    by_cases hPQ : P.coeffs.size < Q.coeffs.size
    · -- Need to show P = 0 in this branch, because Q ∣ P with Q ≠ 0 and deg P < deg Q.
      simp only [hQs, hPs, hPQ, ↓reduceIte]
      -- Use deg argument: deg P < deg Q and Q ∣ P → P = 0.
      have hP_natDeg_lt : (AzPolynomial.toPoly P).natDegree < (AzPolynomial.toPoly Q).natDegree := by
        rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
        show P.coeffs.size - 1 < Q.coeffs.size - 1
        omega
      have hP_zero : AzPolynomial.toPoly P = 0 :=
        Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hP_natDeg_lt
      exact hP_zero
    · -- The main fold case.
      simp only [hQs, hPs, hPQ, ↓reduceIte]
      have hP_size : P.coeffs.size ≥ Q.coeffs.size := Nat.not_lt.mp hPQ
      have h_fold := rem_coeffs_zero_and_dvd_fold (Q.coeffs.size - 1) Q
        (P.coeffs.size - 1) rfl hQ_lead_ne rfl (by omega)
        (P.coeffs.size - Q.coeffs.size + 1) (by omega)
        0 P (fun i hi => coeff_zero_above_size P i (by omega)) hdvd
      obtain ⟨h_zeros, h_dvd⟩ := h_fold
      -- h_zeros: R'.coeff i = 0 for i ≥ q. Combined with h_dvd, conclude R'.toPoly = 0.
      set fold_result := (List.range (P.coeffs.size - Q.coeffs.size + 1)).foldl
        (fun cr k => exactDivStep (Q.coeffs.size - 1) Q.leadingCoeff Q
          (P.coeffs.size - 1 - k) cr) (0, P) with h_fold_eq
      -- If R'.toPoly were nonzero, its natDegree would be < q (from h_zeros).
      -- But Q ∣ R' with both nonzero implies natDegree R' ≥ natDegree Q = q.
      by_contra h_R'_ne
      have h_lead_R' : (AzPolynomial.toPoly fold_result.2).coeff
          (AzPolynomial.toPoly fold_result.2).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr h_R'_ne
      have h_natDeg_lt : (AzPolynomial.toPoly fold_result.2).natDegree
          < Q.coeffs.size - 1 := by
        apply Nat.lt_of_not_le
        intro h_le
        apply h_lead_R'
        rw [coeff_toPoly_eq]
        exact h_zeros _ (by omega)
      have h_natDeg_ge : (AzPolynomial.toPoly Q).natDegree
          ≤ (AzPolynomial.toPoly fold_result.2).natDegree :=
        Polynomial.natDegree_le_of_dvd h_dvd h_R'_ne
      rw [AzPolynomial.natDegree_toPoly Q] at h_natDeg_ge
      have h_Q_nd_eq : Q.natDegree = Q.coeffs.size - 1 := rfl
      omega
  -- Combine with the fold invariant `P = exactDiv * Q + rem`.
  have h_invariant := toPoly_exactDivQuoRem_eq P Q
  rw [h_invariant, h_main, add_zero]
  show AzPolynomial.toPoly (exactDiv P Q) * AzPolynomial.toPoly Q = _
  rfl

end LawfulExactDiv

end Azurite.AzPolynomial

/-! ### Bundled `ExactDiv (AzPolynomial R)` instance -/

namespace Azurite

instance {R : Type _} [CommRing R] [IsDomain R] [DecidableEq R]
    [Azurite.ExactDiv R] :
    Azurite.ExactDiv (AzPolynomial R) where
  exactDiv := AzPolynomial.exactDiv
  exactDiv_mul_self P Q hdvd hQ_ne := by
    have hQ_toPoly_ne : AzPolynomial.toPoly Q ≠ 0 := by
      intro h
      apply hQ_ne
      apply toPoly_inj.mp
      rw [h, toPoly_zero]
    have hdvd_toPoly : AzPolynomial.toPoly Q ∣ AzPolynomial.toPoly P := by
      rcases hdvd with ⟨C, hC⟩
      exact ⟨AzPolynomial.toPoly C, by rw [hC, Azurite.AzPolynomial.toPoly_mul]⟩
    apply toPoly_inj.mp
    rw [Azurite.AzPolynomial.toPoly_mul]
    exact AzPolynomial.exactDiv_spec P Q hQ_toPoly_ne hdvd_toPoly

end Azurite
