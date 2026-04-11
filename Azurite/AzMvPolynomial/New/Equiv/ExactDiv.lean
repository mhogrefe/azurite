/-
  Equivalence proofs for `AzMvPolynomialNew.exactDiv` (Algorithm 8.6).
-/
import Azurite.AzMvPolynomial.New.ExactDiv
import Azurite.AzMvPolynomial.New.Equiv.Algebra
import Azurite.AzMvPolynomial.New.Equiv.MonomialOrder
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

namespace Azurite

open AzMvPolynomialNew MvPolynomial

/-! ### Monomial-level equivalence lemmas -/

variable {R : Type _} [Field R]
         {n : ℕ} {ord : MonomialOrder}

/-- `toMvPoly` of a single-monomial polynomial. -/
theorem toMvPoly_ofMonomial_new (m : MonomialNew n R ord) :
    (AzMvPolynomialNew.ofMonomial m).toMvPoly = m.toMvPoly := by
  simp [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.ofMonomial]

/-- `toMvPoly` distributes over left-multiplication by a monomial. -/
theorem toMvPoly_monomialMul_new (m : MonomialNew n R ord) (p : AzMvPolynomialNew n R ord) :
    (AzMvPolynomialNew.monomialMul m p).toMvPoly = m.toMvPoly * p.toMvPoly := by
  simp only [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.monomialMul]
  rw [← Array.foldl_toList, ← Array.foldl_toList,
      foldl_add_map_eq_sum_new, foldl_add_map_eq_sum_new, List.map_map]
  simp only [Function.comp_def, MonomialNew.toMvPoly_mul]
  rw [← List.sum_map_mul_left]

/-! ### Loop invariant -/

variable [DecidableEq R]

/-- The remainder polynomial after `fuel` steps of the division loop. -/
private def remainderNew
    (q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomialNew n R ord → AzMvPolynomialNew n R ord
  | 0, r => r
  | fuel + 1, r =>
    if hr : r.terms.size > 0 then
      remainderNew q hq fuel (exactDivStepNew r q hr hq).2
    else r

/-- The loop invariant: at every point during the division loop,
    `result * Q + remainder = C * Q + R` is preserved. -/
private theorem exactDivAux_invariant_new
    (q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (c r : AzMvPolynomialNew n R ord) :
    (AzMvPolynomialNew.exactDivAux q hq fuel c r).toMvPoly * q.toMvPoly
    + (remainderNew q hq fuel r).toMvPoly
    = c.toMvPoly * q.toMvPoly + r.toMvPoly := by
  induction fuel generalizing c r with
  | zero => simp [AzMvPolynomialNew.exactDivAux, remainderNew]
  | succ fuel ih =>
    simp only [AzMvPolynomialNew.exactDivAux, remainderNew]
    split
    · next hr =>
      specialize ih (c + AzMvPolynomialNew.ofMonomial (exactDivStepNew r q hr hq).1)
                    (exactDivStepNew r q hr hq).2
      rw [ih, toMvPoly_add_new, toMvPoly_ofMonomial_new]
      simp only [exactDivStepNew]; rw [toMvPoly_sub_new, toMvPoly_monomialMul_new]; ring
    · simp

/-! ### Termination helpers -/

omit [DecidableEq R] in
/-- For `m ∈ c.support`, each entry `m v ≤ c.totalDegree`. -/
private theorem support_entry_le_totalDegree_new
    (c : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ)
    (hm : m ∈ c.support) (v : Fin n) : m v ≤ c.totalDegree := by
  have h1 : (Finsupp.single v (m v)).sum (fun _ e => e) ≤ m.sum (fun _ e => e) :=
    Finsupp.single_le_sum m (fun _ _ => Nat.zero_le _) v
  simp at h1
  exact h1.trans (MvPolynomial.le_totalDegree hm)

/-- Injection from `c.support` to `Fin n → Fin (d+1)` when entries are bounded. -/
private noncomputable def supportEmbedNew (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    c.support → (Fin n → Fin (d + 1)) :=
  fun ⟨m, hm⟩ i => ⟨m i, Nat.lt_succ_of_le (hd m hm _)⟩

omit [DecidableEq R] in
private theorem supportEmbedNew_injective (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    Function.Injective (supportEmbedNew c d hd) := by
  intro ⟨m1, _⟩ ⟨m2, _⟩ heq
  simp only [Subtype.mk.injEq]; ext v
  have h := congr_fun heq v
  simp only [supportEmbedNew, Fin.mk.injEq] at h; exact h

omit [DecidableEq R] in
/-- **Finite bound.** A polynomial whose monomials have each exponent
    `≤ d` has at most `(d+1)^n` terms. -/
theorem support_card_le_pow_new (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    c.support.card ≤ (d + 1) ^ n := by
  rw [show c.support.card = Fintype.card c.support from (Fintype.card_coe _).symm]
  calc Fintype.card c.support
      ≤ Fintype.card (Fin n → Fin (d + 1)) :=
        Fintype.card_le_of_injective _ (supportEmbedNew_injective c d hd)
    _ = (d + 1) ^ n := by simp [Fintype.card_fin]

omit [DecidableEq R] in
/-- **Quotient degree bound (from Mathlib).** -/
theorem quotient_totalDegree_le_new (c q : MvPolynomial (Fin n) R) (hc : c ≠ 0) (hq : q ≠ 0) :
    c.totalDegree ≤ (c * q).totalDegree := by
  rw [MvPolynomial.totalDegree_mul_of_isDomain hc hq]; omega

/-! ### Termination -/

omit [DecidableEq R] in
/-- `terms.size = 0 → toMvPoly = 0`. -/
private theorem toMvPoly_eq_zero_of_terms_empty_new (r : AzMvPolynomialNew n R ord)
    (h : r.terms.size = 0) : r.toMvPoly = 0 := by
  simp [AzMvPolynomialNew.toMvPoly, Array.eq_empty_of_size_eq_zero h]

omit [DecidableEq R] in
/-- `toMvPoly = 0 → terms.size = 0`. -/
private theorem terms_empty_of_toMvPoly_eq_zero_new (r : AzMvPolynomialNew n R ord)
    (h : r.toMvPoly = 0) : r.terms.size = 0 := by
  have := numTerms_eq_support_card_new r
  rw [AzMvPolynomialNew.numTerms, h, support_zero, Finset.card_empty] at this; omega

omit [DecidableEq R] in
/-- `terms.size > 0 → toMvPoly ≠ 0`. -/
private theorem toMvPoly_ne_zero_new (r : AzMvPolynomialNew n R ord)
    (h : r.terms.size > 0) : r.toMvPoly ≠ 0 :=
  fun h0 => absurd (terms_empty_of_toMvPoly_eq_zero_new r h0) (by omega)

omit [DecidableEq R] in
/-- Subtracting a matching monomial from a polynomial reduces `support.card`. -/
private theorem support_card_sub_monomial_new (c : MvPolynomial (Fin n) R) (s : Fin n →₀ ℕ)
    (hs : s ∈ c.support) :
    (c - monomial s (coeff s c)).support.card < c.support.card := by
  have h_not_mem : s ∉ (c - monomial s (coeff s c)).support := by
    rw [mem_support_iff, not_not, coeff_sub, coeff_monomial, if_pos rfl]; ring
  have h_sub : (c - monomial s (coeff s c)).support ⊆ c.support.erase s := by
    intro t ht
    rw [Finset.mem_erase]; exact ⟨fun h => by subst h; exact h_not_mem ht,
      by rw [mem_support_iff] at ht ⊢; intro h; apply ht
         simp [coeff_sub, coeff_monomial, h]
         intro heq; subst heq; exact absurd h (mem_support_iff.mp hs)⟩
  have : c.support.card ≥ 1 := Finset.card_pos.mpr ⟨s, hs⟩
  calc (c - monomial s (coeff s c)).support.card
      ≤ (c.support.erase s).card := Finset.card_le_card h_sub
    _ = c.support.card - 1 := Finset.card_erase_of_mem hs
    _ < c.support.card := by omega

/-- `MonicMonomialNew.div` computes the Finsupp difference. -/
private theorem toFinsupp_div_new (a b : MonicMonomialNew n ord) :
    (MonicMonomialNew.div a b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  ext v; simp [MonicMonomialNew.toFinsupp, MonicMonomialNew.div, Finsupp.onFinset_apply,
    Finsupp.tsub_apply]

/-- **Leading term extraction.** -/
private theorem exactDivStep_is_leading_term_new
    (r q : AzMvPolynomialNew n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hc : c ≠ 0) (hqnz : q.toMvPoly ≠ 0) :
    ∃ s ∈ c.support,
      (exactDivStepNew r q hr hq).1.toMvPoly = monomial s (coeff s c) := by
  set mo := toMathlibMonomialOrderNew (n := n) ord
  have hdeg_r := degree_eq_terms_zero_new r hr
  have hdeg_q := degree_eq_terms_zero_new q hq
  have hdeg_c : mo.degree c =
      (r.terms[0]'(by omega)).monic.toFinsupp - (q.terms[0]'(by omega)).monic.toFinsupp := by
    have h1 : mo.degree r.toMvPoly = mo.degree c + mo.degree q.toMvPoly := by
      rw [hcq]; exact _root_.MonomialOrder.degree_mul hc hqnz
    rw [hdeg_r, hdeg_q] at h1; rw [h1, add_tsub_cancel_right]
  have hlc_c : coeff (mo.degree c) c =
      (r.terms[0]'(by omega)).coeff.val / (q.terms[0]'(by omega)).coeff.val := by
    have hlc_eq : (r.terms[0]'(by omega)).coeff.val =
        coeff (mo.degree c) c * (q.terms[0]'(by omega)).coeff.val := by
      conv_lhs => rw [← leadingCoeff_eq_terms_zero_new r hr, hcq,
        show mo.leadingCoeff (c * q.toMvPoly) =
          mo.leadingCoeff c * mo.leadingCoeff q.toMvPoly from
          _root_.MonomialOrder.leadingCoeff_mul,
        leadingCoeff_eq_terms_zero_new q hq]
      rfl
    rw [hlc_eq, mul_div_cancel_right₀ _ (q.terms[0]'(by omega)).coeff.property]
  refine ⟨mo.degree c, _root_.MonomialOrder.degree_mem_support hc, ?_⟩
  simp only [exactDivStepNew, MonomialNew.toMvPoly, MonomialNew.exactDiv]
  congr 1
  · rw [toFinsupp_div_new, hdeg_c]
  · exact hlc_c.symm

/-- One step of division preserves divisibility and reduces quotient support. -/
private theorem exactDivStep_quotient_support_shrinks_new
    (r q : AzMvPolynomialNew n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly) (hc : c ≠ 0) :
    ∃ c' : MvPolynomial (Fin n) R,
      (exactDivStepNew r q hr hq).2.toMvPoly = c' * q.toMvPoly ∧
      c'.support.card < c.support.card := by
  have hqnz : q.toMvPoly ≠ 0 := fun h => absurd (terms_empty_of_toMvPoly_eq_zero_new q
    (by have := numTerms_eq_support_card_new q
        rw [AzMvPolynomialNew.numTerms, h, support_zero, Finset.card_empty] at this;
        omega)) (by omega)
  obtain ⟨s, hs, ht_eq⟩ := exactDivStep_is_leading_term_new r q hr hq c hcq hc hqnz
  refine ⟨c - (exactDivStepNew r q hr hq).1.toMvPoly, ?_, ?_⟩
  · simp only [exactDivStepNew]; rw [toMvPoly_sub_new, toMvPoly_monomialMul_new, hcq]; ring
  · rw [ht_eq]; exact support_card_sub_monomial_new c s hs

/-- When `fuel ≥ c.support.card` and `r.toMvPoly = c * q.toMvPoly`,
    the remainder is zero. -/
private theorem remainder_zero_of_support_card_new
    (q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (r : AzMvPolynomialNew n R ord)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hfuel : fuel ≥ c.support.card) :
    (remainderNew q hq fuel r).toMvPoly = 0 := by
  induction fuel generalizing r c with
  | zero =>
    simp only [remainderNew]
    have : c = 0 := by
      have : c.support.card = 0 := by omega
      rwa [Finset.card_eq_zero, support_eq_empty] at this
    rw [hcq, this, zero_mul]
  | succ fuel ih =>
    simp only [remainderNew]; split
    · next hr' =>
      have hc : c ≠ 0 := fun h =>
        absurd (terms_empty_of_toMvPoly_eq_zero_new r (by rw [hcq, h, zero_mul])) (by omega)
      obtain ⟨c', hcq', hlt⟩ :=
        exactDivStep_quotient_support_shrinks_new r q hr' hq c hcq hc
      exact ih _ c' hcq' (by omega)
    · exact toMvPoly_eq_zero_of_terms_empty_new r (by omega)

/-- The remainder reaches zero within `(totalDegree P + 1)^n` steps when `Q | P`. -/
theorem remainder_zero_of_dvd_new (p q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (remainderNew q hq ((p.totalDegree + 1) ^ n) p).toMvPoly = 0 := by
  obtain ⟨c, hcq⟩ := hdvd
  rw [mul_comm] at hcq
  exact remainder_zero_of_support_card_new q hq _ p c hcq
    (by rcases eq_or_ne c 0 with rfl | hc
        · simp
        · have hqnz : q.toMvPoly ≠ 0 := toMvPoly_ne_zero_new q hq
          calc c.support.card
              ≤ (p.toMvPoly.totalDegree + 1) ^ n :=
                support_card_le_pow_new c p.toMvPoly.totalDegree (fun m hm v => by
                  calc m v ≤ c.totalDegree :=
                          support_entry_le_totalDegree_new c m hm v
                    _ ≤ (c * q.toMvPoly).totalDegree :=
                        quotient_totalDegree_le_new c q.toMvPoly hc hqnz
                    _ = p.toMvPoly.totalDegree := by rw [hcq])
            _ ≤ (p.totalDegree + 1) ^ n := by
                apply Nat.pow_le_pow_left
                exact Nat.succ_le_succ ((totalDegree_toMvPoly_new p).symm ▸ le_refl _))

/-! ### Main correctness theorems -/

/-- **Correctness of Algorithm 8.6 (toMvPoly version).** -/
theorem exactDiv_spec_new (p q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (p.exactDiv q hq).toMvPoly * q.toMvPoly = p.toMvPoly := by
  have hinv := exactDivAux_invariant_new q hq ((p.totalDegree + 1) ^ n) 0 p
  simp only [AzMvPolynomialNew.exactDiv, toMvPoly_zero_new, zero_mul, zero_add] at hinv ⊢
  rw [remainder_zero_of_dvd_new p q hq hdvd, add_zero] at hinv; exact hinv

/-- Variant with multiplication on the other side. -/
theorem exactDiv_mul_eq_new (p q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    q.toMvPoly * (p.exactDiv q hq).toMvPoly = p.toMvPoly := by
  rw [mul_comm]; exact exactDiv_spec_new p q hq hdvd

/-! ### ofMvPoly versions -/

/-- **Correctness (ofMvPoly version).** -/
theorem ofMvPoly_exactDiv_mul_new (p' q' : MvPolynomial (Fin n) R) (hdvd : q' ∣ p')
    (hq : (AzMvPolynomialNew.ofMvPoly q' : AzMvPolynomialNew n R ord).terms.size > 0) :
    (AzMvPolynomialNew.ofMvPoly p' : AzMvPolynomialNew n R ord) =
      ((AzMvPolynomialNew.ofMvPoly p').exactDiv (AzMvPolynomialNew.ofMvPoly q') hq) *
       AzMvPolynomialNew.ofMvPoly q' := by
  have hdvd' : (AzMvPolynomialNew.ofMvPoly q' : AzMvPolynomialNew n R ord).toMvPoly ∣
               (AzMvPolynomialNew.ofMvPoly p' : AzMvPolynomialNew n R ord).toMvPoly := by
    rwa [toMvPoly_ofMvPoly_new, toMvPoly_ofMvPoly_new]
  apply toMvPoly_injective_new
  rw [toMvPoly_mul_new]; exact (exactDiv_spec_new _ _ hq hdvd').symm

/-- The quotient from exact division divides the dividend. -/
theorem toMvPoly_exactDiv_dvd_new
    (p q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (p.exactDiv q hq).toMvPoly ∣ p.toMvPoly :=
  ⟨q.toMvPoly, (exactDiv_spec_new p q hq hdvd).symm⟩

end Azurite
