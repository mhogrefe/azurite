/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Correctness of `AzMvPolynomial.exactDivCR` (Algorithm 8.6 over a domain
  with `ExactDiv` on coefficients).

  When `q ∣ p` in `MvPolynomial (Fin n) R` and `q ≠ 0`, the fraction-free
  variant `AzMvPolynomial.exactDivCR p q` returns a quotient `c` with
  `c * q = p` (`exactDivCR_spec`). Mirrors the Field-side proof in
  `Equiv/ExactDiv.lean` but uses the `ExactDiv` lawfulness field to argue
  that each step's leading-coefficient division gives the true quotient.

  Proof structure (parallel to the Field version):
  * Loop invariant: `result * q + remainder = c_in * q + r_in`.
  * Each step extracts the *leading* monomial of the running cofactor.
  * Each step shrinks the cofactor's support by one.
  * `(p.totalDegree + 1)^n` steps suffice; the remainder reaches zero.
-/
import Azurite.AzMvPolynomial.ExactDivCommRing
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.MonomialOrder
import Azurite.AzMvPolynomial.Equiv.ExactDiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

set_option linter.unusedSectionVars false

namespace Azurite

open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommRing R] [IsDomain R] [DecidableEq R]
         [Azurite.ExactDiv R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Generic helpers (re-stated for the CR setting) -/

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem support_entry_le_totalDegree
    (c : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ)
    (hm : m ∈ c.support) (v : Fin n) : m v ≤ c.totalDegree := by
  have h1 : (Finsupp.single v (m v)).sum (fun _ e => e) ≤ m.sum (fun _ e => e) :=
    Finsupp.single_le_sum m (fun _ _ => Nat.zero_le _) v
  simp at h1
  exact h1.trans (MvPolynomial.le_totalDegree hm)

private noncomputable def supportEmbed (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    c.support → (Fin n → Fin (d + 1)) :=
  fun ⟨m, hm⟩ i => ⟨m i, Nat.lt_succ_of_le (hd m hm _)⟩

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem supportEmbed_injective (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    Function.Injective (supportEmbed c d hd) := by
  intro ⟨m1, _⟩ ⟨m2, _⟩ heq
  simp only [Subtype.mk.injEq]; ext v
  have h := congr_fun heq v
  simp only [supportEmbed, Fin.mk.injEq] at h; exact h

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem cr_support_card_le_pow (c : MvPolynomial (Fin n) R) (d : ℕ)
    (hd : ∀ m ∈ c.support, ∀ v : Fin n, m v ≤ d) :
    c.support.card ≤ (d + 1) ^ n := by
  rw [show c.support.card = Fintype.card c.support from (Fintype.card_coe _).symm]
  calc Fintype.card c.support
      ≤ Fintype.card (Fin n → Fin (d + 1)) :=
        Fintype.card_le_of_injective _ (supportEmbed_injective c d hd)
    _ = (d + 1) ^ n := by simp [Fintype.card_fin]

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem cr_quotient_totalDegree_le (c q : MvPolynomial (Fin n) R)
    (hc : c ≠ 0) (hq : q ≠ 0) :
    c.totalDegree ≤ (c * q).totalDegree := by
  rw [MvPolynomial.totalDegree_mul_of_isDomain hc hq]; omega

omit [Azurite.ExactDiv R] in
private theorem support_card_sub_monomial (c : MvPolynomial (Fin n) R) (s : Fin n →₀ ℕ)
    (hs : s ∈ c.support) :
    (c - monomial s (c.coeff s)).support.card < c.support.card := by
  have h_not_mem : s ∉ (c - monomial s (c.coeff s)).support := by
    rw [mem_support_iff, not_not, coeff_sub, coeff_monomial, ite_eq_left rfl]; ring
  have h_sub : (c - monomial s (c.coeff s)).support ⊆ c.support.erase s := by
    intro t ht
    rw [Finset.mem_erase]; exact ⟨fun h => by subst h; exact h_not_mem ht,
      by rw [mem_support_iff] at ht ⊢; intro h; apply ht
         simp [coeff_monomial, h]
         intro heq; subst heq; exact absurd h (mem_support_iff.mp hs)⟩
  have : c.support.card ≥ 1 := Finset.card_pos.mpr ⟨s, hs⟩
  calc (c - monomial s (c.coeff s)).support.card
      ≤ (c.support.erase s).card := Finset.card_le_card h_sub
    _ = c.support.card - 1 := Finset.card_erase_of_mem hs
    _ < c.support.card := by omega

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem toMvPoly_eq_zero_of_terms_empty (r : AzMvPolynomial n R ord)
    (h : r.terms.size = 0) : r.toMvPoly = 0 := by
  simp [AzMvPolynomial.toMvPoly, Array.eq_empty_of_size_eq_zero h]

omit [Azurite.ExactDiv R] in
private theorem terms_empty_of_toMvPoly_eq_zero (r : AzMvPolynomial n R ord)
    (h : r.toMvPoly = 0) : r.terms.size = 0 := by
  have := numTerms_eq_support_card r
  rw [AzMvPolynomial.numTerms, h, support_zero, Finset.card_empty] at this; omega

omit [Azurite.ExactDiv R] in
private theorem toMvPoly_ne_zero (r : AzMvPolynomial n R ord)
    (h : r.terms.size > 0) : r.toMvPoly ≠ 0 :=
  fun h0 => absurd (terms_empty_of_toMvPoly_eq_zero r h0) (by omega)

omit [DecidableEq R] [Azurite.ExactDiv R] in
/-- `MonicMonomial.div` computes the Finsupp difference. -/
private theorem toFinsupp_div (a b : MonicMonomial n ord) :
    (MonicMonomial.div a b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  ext v; simp [MonicMonomial.toFinsupp, MonicMonomial.div, Finsupp.onFinset_apply,
    Finsupp.tsub_apply]

/-! ### Bridge: `toMvPoly` of `ofMonomial`. -/

omit [DecidableEq R] [Azurite.ExactDiv R] in
private theorem cr_toMvPoly_ofMonomial (m : Monomial n R ord) :
    (AzMvPolynomial.ofMonomial m).toMvPoly = m.toMvPoly := by
  simp [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMonomial]

/-! ### `remainderCR`: running remainder for the loop -/

/-- The remainder polynomial after `fuel` steps of the CR division loop. -/
private def remainderCR
    (q : AzMvPolynomial n R ord) (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomial n R ord → AzMvPolynomial n R ord
  | 0, r => r
  | fuel + 1, r =>
    if hr : r.terms.size > 0 then
      remainderCR q hq fuel (exactDivStepCR r q hr hq).2
    else r

/-! ### Loop invariant -/

private theorem exactDivAuxCR_invariant
    (q : AzMvPolynomial n R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (c r : AzMvPolynomial n R ord) :
    (AzMvPolynomial.exactDivAuxCR q hq fuel c r).toMvPoly * q.toMvPoly
    + (remainderCR q hq fuel r).toMvPoly
    = c.toMvPoly * q.toMvPoly + r.toMvPoly := by
  induction fuel generalizing c r with
  | zero => simp [AzMvPolynomial.exactDivAuxCR, remainderCR]
  | succ fuel ih =>
    simp only [AzMvPolynomial.exactDivAuxCR, remainderCR]
    split
    · next hr =>
      specialize ih (c + AzMvPolynomial.ofMonomial (exactDivStepCR r q hr hq).1)
                    (exactDivStepCR r q hr hq).2
      rw [ih, toMvPoly_add, cr_toMvPoly_ofMonomial]
      simp only [exactDivStepCR]
      rw [toMvPoly_sub, toMvPoly_mul, cr_toMvPoly_ofMonomial]
      ring
    · simp

/-! ### Step extracts the leading monomial of the cofactor -/

private theorem exactDivStepCR_is_leading_term
    (r q : AzMvPolynomial n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hc : c ≠ 0) (hqnz : q.toMvPoly ≠ 0) :
    ∃ s ∈ c.support,
      (AzMvPolynomial.ofMonomial (exactDivStepCR r q hr hq).1).toMvPoly =
        monomial s (c.coeff s) := by
  set mo := toMathlibMonomialOrder (n := n) ord
  have hdeg_r := degree_eq_terms_zero r hr
  have hdeg_q := degree_eq_terms_zero q hq
  have hdeg_c : mo.degree c =
      (r.terms[0]'(by omega)).monic.toFinsupp - (q.terms[0]'(by omega)).monic.toFinsupp := by
    have h1 : mo.degree r.toMvPoly = mo.degree c + mo.degree q.toMvPoly := by
      rw [hcq]; exact _root_.MonomialOrder.degree_mul hc hqnz
    rw [hdeg_r, hdeg_q] at h1; rw [h1, add_tsub_cancel_right]
  -- Coefficient identity: r's leading coeff = c's leading coeff * q's leading coeff.
  have hlc_eq : (r.terms[0]'(by omega)).coeff.val =
      c.coeff (mo.degree c) * (q.terms[0]'(by omega)).coeff.val := by
    conv_lhs => rw [← leadingCoeff_eq_terms_zero r hr, hcq,
      show mo.leadingCoeff (c * q.toMvPoly) =
        mo.leadingCoeff c * mo.leadingCoeff q.toMvPoly from
        _root_.MonomialOrder.leadingCoeff_mul,
      leadingCoeff_eq_terms_zero q hq]
    rfl
  -- LawfulExactDiv on the coefficient ring: exactDiv recovers the cofactor's leading coeff.
  have hqlead_ne : (q.terms[0]'(by omega)).coeff.val ≠ 0 :=
    (q.terms[0]'(by omega)).coeff.property
  have h_dvd : (q.terms[0]'(by omega)).coeff.val ∣ (r.terms[0]'(by omega)).coeff.val :=
    ⟨c.coeff (mo.degree c), by rw [hlc_eq]; ring⟩
  have h_law := Azurite.ExactDiv.exactDiv_mul_self
    (r.terms[0]'(by omega)).coeff.val (q.terms[0]'(by omega)).coeff.val h_dvd hqlead_ne
  -- The cancellation: `exactDiv leadR leadQ = coeff (deg c) c`.
  have hlc_c : Azurite.ExactDiv.exactDiv (r.terms[0]'(by omega)).coeff.val
      (q.terms[0]'(by omega)).coeff.val = c.coeff (mo.degree c) := by
    have h_eq : Azurite.ExactDiv.exactDiv (r.terms[0]'(by omega)).coeff.val
        (q.terms[0]'(by omega)).coeff.val * (q.terms[0]'(by omega)).coeff.val =
        c.coeff (mo.degree c) * (q.terms[0]'(by omega)).coeff.val := by
      rw [h_law]; exact hlc_eq
    exact mul_right_cancel₀ hqlead_ne h_eq
  -- The chosen monomial is nonzero (coefficient is leading coeff of c).
  have h_lead_c_ne : c.coeff (mo.degree c) ≠ 0 := by
    rw [show c.coeff (mo.degree c) = mo.leadingCoeff c from rfl]
    exact MonomialOrder.leadingCoeff_ne_zero_iff.mpr hc
  -- The exactDiv result is nonzero, so we hit the `else` branch of `Monomial.exactDivCR`.
  have h_exactDiv_ne : Azurite.ExactDiv.exactDiv (r.terms[0]'(by omega)).coeff.val
      (q.terms[0]'(by omega)).coeff.val ≠ 0 := by rw [hlc_c]; exact h_lead_c_ne
  refine ⟨mo.degree c, _root_.MonomialOrder.degree_mem_support hc, ?_⟩
  simp only [exactDivStepCR, cr_toMvPoly_ofMonomial, Monomial.toMvPoly,
    Monomial.exactDivCR]
  rw [dite_eq_right h_exactDiv_ne]
  have hfs : (MonicMonomial.div (r.terms[0]'(by omega)).monic
      (q.terms[0]'(by omega)).monic).toFinsupp = mo.degree c := by
    rw [toFinsupp_div, hdeg_c]
  show monomial _ _ = monomial _ _
  apply congr_arg₂ (fun s c => MvPolynomial.monomial s c)
  · exact hfs
  · exact hlc_c

/-! ### Quotient support shrinks per step -/

private theorem exactDivStepCR_quotient_support_shrinks
    (r q : AzMvPolynomial n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly) (hc : c ≠ 0) :
    ∃ c' : MvPolynomial (Fin n) R,
      (exactDivStepCR r q hr hq).2.toMvPoly = c' * q.toMvPoly ∧
      c'.support.card < c.support.card := by
  have hqnz : q.toMvPoly ≠ 0 := toMvPoly_ne_zero q hq
  obtain ⟨s, hs, ht_eq⟩ := exactDivStepCR_is_leading_term r q hr hq c hcq hc hqnz
  refine ⟨c - (AzMvPolynomial.ofMonomial (exactDivStepCR r q hr hq).1).toMvPoly, ?_, ?_⟩
  · simp only [exactDivStepCR]
    rw [toMvPoly_sub, toMvPoly_mul, cr_toMvPoly_ofMonomial, hcq]
    ring
  · rw [ht_eq]; exact support_card_sub_monomial c s hs

/-! ### Remainder reaches zero -/

private theorem remainderCR_zero_of_support_card
    (q : AzMvPolynomial n R ord) (hq : q.terms.size > 0)
    (fuel : ℕ) (r : AzMvPolynomial n R ord)
    (c : MvPolynomial (Fin n) R) (hcq : r.toMvPoly = c * q.toMvPoly)
    (hfuel : fuel ≥ c.support.card) :
    (remainderCR q hq fuel r).toMvPoly = 0 := by
  induction fuel generalizing r c with
  | zero =>
    simp only [remainderCR]
    have : c = 0 := by
      have : c.support.card = 0 := by omega
      rwa [Finset.card_eq_zero, support_eq_empty] at this
    rw [hcq, this, zero_mul]
  | succ fuel ih =>
    simp only [remainderCR]; split
    · next hr' =>
      have hc : c ≠ 0 := fun h =>
        absurd (terms_empty_of_toMvPoly_eq_zero r (by rw [hcq, h, zero_mul])) (by omega)
      obtain ⟨c', hcq', hlt⟩ :=
        exactDivStepCR_quotient_support_shrinks r q hr' hq c hcq hc
      exact ih _ c' hcq' (by omega)
    · exact toMvPoly_eq_zero_of_terms_empty r (by omega)

theorem remainderCR_zero_of_dvd (p q : AzMvPolynomial n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (remainderCR q hq ((p.totalDegree + 1) ^ n) p).toMvPoly = 0 := by
  obtain ⟨c, hcq⟩ := hdvd
  rw [mul_comm] at hcq
  exact remainderCR_zero_of_support_card q hq _ p c hcq
    (by rcases eq_or_ne c 0 with rfl | hc
        · simp
        · have hqnz : q.toMvPoly ≠ 0 := toMvPoly_ne_zero q hq
          calc c.support.card
              ≤ (p.toMvPoly.totalDegree + 1) ^ n :=
                cr_support_card_le_pow c p.toMvPoly.totalDegree (fun m hm v => by
                  calc m v ≤ c.totalDegree :=
                          support_entry_le_totalDegree c m hm v
                    _ ≤ (c * q.toMvPoly).totalDegree :=
                        cr_quotient_totalDegree_le c q.toMvPoly hc hqnz
                    _ = p.toMvPoly.totalDegree := by rw [hcq])
            _ ≤ (p.totalDegree + 1) ^ n := by
                apply Nat.pow_le_pow_left
                exact Nat.succ_le_succ ((totalDegree_toMvPoly p).symm ▸ le_refl _))

/-! ### Main correctness theorem -/

/-- **Correctness of `AzMvPolynomial.exactDivCR`.** When `q ≠ 0` and `q ∣ p` in
    `MvPolynomial (Fin n) R`, the fraction-free exact-division loop produces a
    quotient `c` with `c * q = p`. -/
theorem exactDivCR_spec (p q : AzMvPolynomial n R ord) (hq : q.terms.size > 0)
    (hdvd : q.toMvPoly ∣ p.toMvPoly) :
    (AzMvPolynomial.exactDivCR p q).toMvPoly * q.toMvPoly = p.toMvPoly := by
  have hinv := exactDivAuxCR_invariant q hq ((p.totalDegree + 1) ^ n) 0 p
  simp only [AzMvPolynomial.exactDivCR, dite_eq_left hq, toMvPoly_zero,
    zero_mul, zero_add] at hinv ⊢
  rw [remainderCR_zero_of_dvd p q hq hdvd, add_zero] at hinv
  exact hinv

/-! ### Bundled `ExactDiv (AzMvPolynomial n R ord)` instance -/

instance : Azurite.ExactDiv (AzMvPolynomial n R ord) where
  exactDiv := AzMvPolynomial.exactDivCR
  exactDiv_mul_self p q hdvd hq_ne := by
    have hq_size : q.terms.size > 0 := by
      by_contra h
      push Not at h
      apply hq_ne
      apply toMvPoly_injective
      rw [toMvPoly_zero]
      exact toMvPoly_eq_zero_of_terms_empty q (by omega)
    have hdvd_toMv : q.toMvPoly ∣ p.toMvPoly := by
      rcases hdvd with ⟨c, hc⟩
      refine ⟨c.toMvPoly, ?_⟩
      have := congrArg AzMvPolynomial.toMvPoly hc
      rwa [toMvPoly_mul] at this
    apply toMvPoly_injective
    rw [toMvPoly_mul]
    exact exactDivCR_spec p q hq_size hdvd_toMv

end Azurite
