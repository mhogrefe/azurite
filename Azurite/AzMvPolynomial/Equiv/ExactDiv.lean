/-
  Equivalence proofs for `AzMvPolynomial.exactDiv` (Algorithm 8.6).

  Since Mathlib does not provide a general exact division operation for
  `MvPolynomial`, we prove the **defining property** of exact division:

    If `Q | P` in `K[X₁, …, Xₖ]`, then `exactDiv P Q * Q = P`.

  The proof has two parts:
  1. **Loop invariant** (`exactDivAux_invariant`): fully proved.
     `result * Q + remainder = C * Q + R` is preserved at every step
     of the division loop, by a ring identity.
  2. **Termination** (`remainder_zero_of_dvd`): proved via the
     MonomialOrder bridge.  When `Q | R`, the remainder reaches zero
     within `(totalDegree P + 1)^k` steps, because the leading monomial
     strictly decreases under the monomial ordering at each step.
     The key lemma `exactDivStep_is_leading_term` uses Mathlib's
     `MonomialOrder.degree_mul` and `MonomialOrder.leadingCoeff_mul`
     to show that each step extracts the leading term of the quotient.
-/
import Azurite.AzMvPolynomial.ExactDiv
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.MonomialOrder
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

namespace Azurite

open AzMvPolynomial MvPolynomial

/-! ### Monomial-level equivalence lemmas -/

variable {R : Type _} [Field R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- `toMvPoly` of a single-monomial polynomial. -/
theorem toMvPoly_ofMonomial (m : Monomial σ R ord) :
    (AzMvPolynomial.ofMonomial m).toMvPoly = m.toMvPoly := by
  simp [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMonomial]

/-- `toMvPoly` distributes over left-multiplication by a monomial. -/
theorem toMvPoly_monomialMul (m : Monomial σ R ord) (p : AzMvPolynomial σ R ord) :
    (AzMvPolynomial.monomialMul m p).toMvPoly = m.toMvPoly * p.toMvPoly := by
  simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.monomialMul]
  rw [← Array.foldl_toList, ← Array.foldl_toList,
      foldl_add_map_eq_sum, foldl_add_map_eq_sum, List.map_map]
  simp only [Function.comp_def, Monomial.toMvPoly_mul]
  rw [← List.sum_map_mul_left]

/-! ### Loop invariant -/

variable [DecidableEq R]

/-- The remainder polynomial after `fuel` steps of the division loop. -/
private def remainder
    (q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomial σ R ord → AzMvPolynomial σ R ord
  | 0, r => r
  | fuel + 1, r =>
    if hr : r.terms.size > 0 then
      remainder q hq fuel (exactDivStep r q hr hq).2
    else r

/-- The loop invariant: at every point during the division loop,
    `result * Q + remainder = C * Q + R` is preserved.

    Proved by induction on fuel. The one-step case reduces to the
    ring identity `(C + t) * Q + (R − t * Q) = C * Q + R`. -/
private theorem exactDivAux_invariant
    (q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (c r : AzMvPolynomial σ R ord) :
    (AzMvPolynomial.exactDivAux q hq fuel c r).toMvPoly * q.toMvPoly
    + (remainder q hq fuel r).toMvPoly
    = c.toMvPoly * q.toMvPoly + r.toMvPoly := by
  induction fuel generalizing c r with
  | zero => simp [AzMvPolynomial.exactDivAux, remainder]
  | succ fuel ih =>
    simp only [AzMvPolynomial.exactDivAux, remainder]
    split
    · next hr =>
      specialize ih (c + AzMvPolynomial.ofMonomial (exactDivStep r q hr hq).1)
                    (exactDivStep r q hr hq).2
      rw [ih, toMvPoly_add, toMvPoly_ofMonomial]
      simp only [exactDivStep]; rw [toMvPoly_sub, toMvPoly_monomialMul]; ring
    · simp

/-! ### Termination helpers -/

omit [LinearOrder σ] [DecidableEq R] in
/-- For `m ∈ c.support`, each entry `m v ≤ c.totalDegree`. -/
private theorem support_entry_le_totalDegree (c : MvPolynomial σ R) (m : σ →₀ ℕ)
    (hm : m ∈ c.support) (v : σ) : m v ≤ c.totalDegree := by
  have h1 : (Finsupp.single v (m v)).sum (fun _ e => e) ≤ m.sum (fun _ e => e) :=
    Finsupp.single_le_sum m (fun _ _ => Nat.zero_le _) v
  simp at h1
  exact h1.trans (MvPolynomial.le_totalDegree hm)

/-- Injection from `c.support` to `Fin n → Fin (d+1)` when entries are bounded. -/
private noncomputable def supportEmbed (c : MvPolynomial σ R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : σ, m v ≤ d) :
    c.support → (Fin n → Fin (d + 1)) :=
  fun ⟨m, hm⟩ i => ⟨m (Var.ofFin i), Nat.lt_succ_of_le (hd m hm _)⟩

omit [DecidableEq R] in
private theorem supportEmbed_injective (c : MvPolynomial σ R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : σ, m v ≤ d) :
    Function.Injective (supportEmbed c d hd) := by
  intro ⟨m1, _⟩ ⟨m2, _⟩ heq
  simp only [Subtype.mk.injEq]; ext v
  have h := congr_fun heq (Var.toFin v)
  simp only [supportEmbed, Fin.mk.injEq, Var.ofFin_toFin] at h; exact h

omit [DecidableEq R] in
/-- **Finite bound.** A polynomial whose monomials have each exponent
    `≤ d` has at most `(d+1)^k` terms. -/
theorem support_card_le_pow (c : MvPolynomial σ R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : σ, m v ≤ d) :
    c.support.card ≤ (d + 1) ^ n := by
  rw [show c.support.card = Fintype.card c.support from (Fintype.card_coe _).symm]
  calc Fintype.card c.support
      ≤ Fintype.card (Fin n → Fin (d + 1)) :=
        Fintype.card_le_of_injective _ (supportEmbed_injective c d hd)
    _ = (d + 1) ^ n := by simp [Fintype.card_fin]

omit [LinearOrder σ] [DecidableEq R] in
/-- **Quotient degree bound (from Mathlib).** If `p = c * q` with `c, q ≠ 0`
    over a domain, then `c.totalDegree ≤ p.totalDegree`. -/
theorem quotient_totalDegree_le (c q : MvPolynomial σ R) (hc : c ≠ 0) (hq : q ≠ 0) :
    c.totalDegree ≤ (c * q).totalDegree := by
  rw [MvPolynomial.totalDegree_mul_of_isDomain hc hq]; omega

/-! ### Termination -/

omit [DecidableEq R] in
/-- `terms.size = 0 → toMvPoly = 0`. -/
private theorem toMvPoly_eq_zero_of_terms_empty (r : AzMvPolynomial σ R ord)
    (h : r.terms.size = 0) : r.toMvPoly = 0 := by
  simp [AzMvPolynomial.toMvPoly, Array.eq_empty_of_size_eq_zero h]

omit [DecidableEq R] in
/-- `toMvPoly = 0 → terms.size = 0`. -/
private theorem terms_empty_of_toMvPoly_eq_zero (r : AzMvPolynomial σ R ord)
    (h : r.toMvPoly = 0) : r.terms.size = 0 := by
  have := numTerms_eq_support_card r
  rw [numTerms, h, support_zero, Finset.card_empty] at this; omega

omit [DecidableEq R] in
/-- `terms.size > 0 → toMvPoly ≠ 0`. -/
private theorem toMvPoly_ne_zero (r : AzMvPolynomial σ R ord)
    (h : r.terms.size > 0) : r.toMvPoly ≠ 0 :=
  fun h0 => absurd (terms_empty_of_toMvPoly_eq_zero r h0) (by omega)

omit [DecidableEq R] in
/-- Subtracting a matching monomial from a polynomial reduces `support.card`. -/
private theorem support_card_sub_monomial (c : MvPolynomial σ R) (s : σ →₀ ℕ)
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

/-- `MonicMonomial.div` computes the Finsupp difference. -/
private theorem toFinsupp_div (a b : MonicMonomial σ ord) :
    (MonicMonomial.div a b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  ext v; simp [MonicMonomial.toFinsupp, MonicMonomial.div, Finsupp.onFinset_apply,
    Finsupp.tsub_apply]

/-- **Leading term extraction.** When `r.toMvPoly = c * q.toMvPoly` with
    `c ≠ 0` and `q ≠ 0`, the monomial extracted by `exactDivStep` corresponds
    to a term `s ∈ c.support` with coefficient `coeff s c`.

    Uses the MonomialOrder bridge: `degree(c * q) = degree(c) + degree(q)`
    and `leadCoeff(c * q) = leadCoeff(c) * leadCoeff(q)` from Mathlib,
    translated to our sorted representation via `degree_eq_terms_zero`. -/
private theorem exactDivStep_is_leading_term
    (r q : AzMvPolynomial σ R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial σ R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hc : c ≠ 0) (hqnz : q.toMvPoly ≠ 0) :
    ∃ s ∈ c.support, (exactDivStep r q hr hq).1.toMvPoly = monomial s (coeff s c) := by
  set mo := toMathlibMonomialOrder (σ := σ) (n := n) ord
  have hdeg_r := degree_eq_terms_zero r hr
  have hdeg_q := degree_eq_terms_zero q hq
  -- degree(c) = leadR.toFinsupp - leadQ.toFinsupp
  have hdeg_c : mo.degree c =
      (r.terms[0]'(by omega)).monic.toFinsupp - (q.terms[0]'(by omega)).monic.toFinsupp := by
    have h1 : mo.degree r.toMvPoly = mo.degree c + mo.degree q.toMvPoly := by
      rw [hcq]; exact _root_.MonomialOrder.degree_mul hc hqnz
    rw [hdeg_r, hdeg_q] at h1; rw [h1, add_tsub_cancel_right]
  -- coeff at degree(c) = leadR.coeff / leadQ.coeff
  have hlc_c : coeff (mo.degree c) c =
      (r.terms[0]'(by omega)).coeff.val / (q.terms[0]'(by omega)).coeff.val := by
    have hlc_eq : (r.terms[0]'(by omega)).coeff.val =
        coeff (mo.degree c) c * (q.terms[0]'(by omega)).coeff.val := by
      conv_lhs => rw [← leadingCoeff_eq_terms_zero r hr, hcq,
        show mo.leadingCoeff (c * q.toMvPoly) =
          mo.leadingCoeff c * mo.leadingCoeff q.toMvPoly from
          _root_.MonomialOrder.leadingCoeff_mul,
        leadingCoeff_eq_terms_zero q hq]
      rfl
    rw [hlc_eq, mul_div_cancel_right₀ _ (q.terms[0]'(by omega)).coeff.property]
  -- Construct the witness
  refine ⟨mo.degree c, _root_.MonomialOrder.degree_mem_support hc, ?_⟩
  simp only [exactDivStep, Monomial.toMvPoly, Monomial.exactDiv]
  congr 1
  · rw [toFinsupp_div, hdeg_c]
  · exact hlc_c.symm

/-- One step of division preserves divisibility and reduces quotient support. -/
private theorem exactDivStep_quotient_support_shrinks
    (r q : AzMvPolynomial σ R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial σ R) (hcq : r.toMvPoly = c * q.toMvPoly) (hc : c ≠ 0) :
    ∃ c' : MvPolynomial σ R,
      (exactDivStep r q hr hq).2.toMvPoly = c' * q.toMvPoly ∧
      c'.support.card < c.support.card := by
  have hqnz : q.toMvPoly ≠ 0 := fun h => absurd (terms_empty_of_toMvPoly_eq_zero q
    (by have := numTerms_eq_support_card q
        rw [numTerms, h, support_zero, Finset.card_empty] at this; omega)) (by omega)
  obtain ⟨s, hs, ht_eq⟩ := exactDivStep_is_leading_term r q hr hq c hcq hc hqnz
  refine ⟨c - (exactDivStep r q hr hq).1.toMvPoly, ?_, ?_⟩
  · simp only [exactDivStep]; rw [toMvPoly_sub, toMvPoly_monomialMul, hcq]; ring
  · rw [ht_eq]; exact support_card_sub_monomial c s hs

/-- When `fuel ≥ c.support.card` and `r.toMvPoly = c * q.toMvPoly`,
    the remainder is zero. -/
private theorem remainder_zero_of_support_card
    (q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (r : AzMvPolynomial σ R ord)
    (c : MvPolynomial σ R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hfuel : fuel ≥ c.support.card) :
    (remainder q hq fuel r).toMvPoly = 0 := by
  induction fuel generalizing r c with
  | zero =>
    simp only [remainder]
    have : c = 0 := by
      have : c.support.card = 0 := by omega
      rwa [Finset.card_eq_zero, support_eq_empty] at this
    rw [hcq, this, zero_mul]
  | succ fuel ih =>
    simp only [remainder]; split
    · next hr' =>
      have hc : c ≠ 0 := fun h =>
        absurd (terms_empty_of_toMvPoly_eq_zero r (by rw [hcq, h, zero_mul])) (by omega)
      obtain ⟨c', hcq', hlt⟩ := exactDivStep_quotient_support_shrinks r q hr' hq c hcq hc
      exact ih _ c' hcq' (by omega)
    · exact toMvPoly_eq_zero_of_terms_empty r (by omega)

/-- The remainder reaches zero within `(totalDegree P + 1)^k` steps
    when `Q | P`. -/
theorem remainder_zero_of_dvd (p q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (remainder q hq ((p.totalDegree + 1) ^ n) p).toMvPoly = 0 := by
  obtain ⟨c, hcq⟩ := hdvd
  rw [mul_comm] at hcq
  exact remainder_zero_of_support_card q hq _ p c hcq
    (by rcases eq_or_ne c 0 with rfl | hc
        · simp
        · have hqnz : q.toMvPoly ≠ 0 := toMvPoly_ne_zero q hq
          calc c.support.card
              ≤ (p.toMvPoly.totalDegree + 1) ^ n :=
                support_card_le_pow c p.toMvPoly.totalDegree (fun m hm v => by
                  calc m v ≤ c.totalDegree := support_entry_le_totalDegree c m hm v
                    _ ≤ (c * q.toMvPoly).totalDegree :=
                        quotient_totalDegree_le c q.toMvPoly hc hqnz
                    _ = p.toMvPoly.totalDegree := by rw [hcq])
            _ ≤ (p.totalDegree + 1) ^ n := by
                apply Nat.pow_le_pow_left
                exact Nat.succ_le_succ ((totalDegree_toMvPoly p).symm ▸ le_refl _))

/-! ### Main correctness theorems -/

/-- **Correctness of Algorithm 8.6 (toMvPoly version).**
    If `Q | P` in `MvPolynomial` and `Q ≠ 0`,
    then `toMvPoly (exactDiv P Q) * toMvPoly Q = toMvPoly P`. -/
theorem exactDiv_spec (p q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (p.exactDiv q hq).toMvPoly * q.toMvPoly = p.toMvPoly := by
  have hinv := exactDivAux_invariant q hq ((p.totalDegree + 1) ^ n) 0 p
  simp only [AzMvPolynomial.exactDiv, toMvPoly_zero, zero_mul, zero_add] at hinv ⊢
  rw [remainder_zero_of_dvd p q hq hdvd, add_zero] at hinv; exact hinv

/-- Variant with multiplication on the other side. -/
theorem exactDiv_mul_eq (p q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    q.toMvPoly * (p.exactDiv q hq).toMvPoly = p.toMvPoly := by
  rw [mul_comm]; exact exactDiv_spec p q hq hdvd

/-! ### ofMvPoly versions -/

/-- **Correctness (ofMvPoly version).**
    If `Q | P` in `MvPolynomial`, then
    `ofMvPoly P = exactDiv (ofMvPoly P) (ofMvPoly Q) * ofMvPoly Q`. -/
theorem ofMvPoly_exactDiv_mul (p' q' : MvPolynomial σ R) (hdvd : q' ∣ p')
    (hq : (AzMvPolynomial.ofMvPoly q' : AzMvPolynomial σ R ord).terms.size > 0) :
    (AzMvPolynomial.ofMvPoly p' : AzMvPolynomial σ R ord) =
      ((AzMvPolynomial.ofMvPoly p').exactDiv (AzMvPolynomial.ofMvPoly q') hq) *
       AzMvPolynomial.ofMvPoly q' := by
  have hdvd' : (AzMvPolynomial.ofMvPoly q' : AzMvPolynomial σ R ord).toMvPoly ∣
               (AzMvPolynomial.ofMvPoly p' : AzMvPolynomial σ R ord).toMvPoly := by
    rwa [toMvPoly_ofMvPoly, toMvPoly_ofMvPoly]
  apply toMvPoly_injective
  rw [toMvPoly_mul]; exact (exactDiv_spec _ _ hq hdvd').symm

/-- The quotient from exact division divides the dividend. -/
theorem toMvPoly_exactDiv_dvd (p q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (p.exactDiv q hq).toMvPoly ∣ p.toMvPoly :=
  ⟨q.toMvPoly, (exactDiv_spec p q hq hdvd).symm⟩

end Azurite
