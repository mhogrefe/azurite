/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-! # BPR §2.6 Lemma 2.97 — the characteristic polynomial is a polynomial in `X^q`

For an edge `E = [M_j, M_k]` of the Newton polygon of `P`, write the slope `−ξ` as `−c/(mq)`
with `q > 0` and `gcd(c, q) = 1` (the reduced denominator over the common denominator `m` of the
orders). Then every column `h` on `E` satisfies `q ∣ (h − j)`, so the characteristic polynomial
factors as `Q(P, E, X) = X^j · φ(X^q)`.

The mathematical heart is the number-theoretic divisibility `q ∣ (h − j)`
(`dvd_sub_of_collinear`): clearing denominators in the collinearity of `M_j`, `M_h`, `M_k` gives
`(m_h − m_j)(k − j) = (m_k − m_j)(h − j)`, whence `q ∣ c(h − j)` and, by coprimality, `q ∣
(h − j)`. The structural consequence — a sum of monomials whose exponents are `≡ j (mod q)`
factors as `X^j` times a polynomial in `X^q` — is `sum_monomial_factor`, and its application to
the characteristic polynomial is `charPoly_factor`.
-/

namespace Azurite.BPR

open Polynomial

/-- **The number-theoretic core of Lemma 2.97.** If the integer points `(j, a_j)`, `(h, a_h)`,
`(k, a_k)` are collinear, i.e. `(a_h − a_j)(k − j) = (a_k − a_j)(h − j)`, then the reduced
denominator `q = (k − j)/gcd(a_k − a_j, k − j)` of the slope divides `h − j`. -/
theorem dvd_sub_of_collinear {j k h aj ak ah : ℤ} (hjk : j < k)
    (hcol : (ah - aj) * (k - j) = (ak - aj) * (h - j)) :
    (k - j) / (Int.gcd (ak - aj) (k - j) : ℤ) ∣ (h - j) := by
  have hkj : k - j ≠ 0 := by omega
  have hgpos : 0 < Int.gcd (ak - aj) (k - j) := Int.gcd_pos_iff.mpr (Or.inr hkj)
  set G : ℤ := (Int.gcd (ak - aj) (k - j) : ℤ) with hG
  have hG0 : G ≠ 0 := by rw [hG]; exact_mod_cast hgpos.ne'
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right (ak - aj) (k - j)
  obtain ⟨c, hc⟩ := Int.gcd_dvd_left (ak - aj) (k - j)
  have hqeq : (k - j) / G = q := by rw [hq, Int.mul_ediv_cancel_left q hG0]
  have hcop : IsCoprime q c := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    have key := Int.gcd_div_gcd_div_gcd hgpos
    rw [hqeq, show (ak - aj) / G = c by rw [hc, Int.mul_ediv_cancel_left c hG0]] at key
    exact key
  have hqdvd : q ∣ c * (h - j) := by
    have hd : G * q ∣ G * c * (h - j) := by
      rw [← hq, ← hc]; exact ⟨ah - aj, by linarith [hcol]⟩
    rw [mul_assoc] at hd
    exact (mul_dvd_mul_iff_left hG0).mp hd
  rw [hqeq]
  exact hcop.dvd_of_dvd_mul_left hqdvd

/-- **The structural form of `Q`.** A sum of monomials `∑ c_h X^h` whose exponents are all `≥ j`
and `≡ j (mod q)` factors as `X^j` times a polynomial in `X^q`:
`∑_h c_h X^h = X^j · φ(X^q)` with `φ = ∑_h c_h Y^{(h−j)/q}`. -/
theorem sum_monomial_factor {R : Type*} [CommRing R] {S : Finset ℕ} {j q : ℕ}
    (hj : ∀ h ∈ S, j ≤ h) (hd : ∀ h ∈ S, q ∣ (h - j)) (c : ℕ → R) :
    ∑ h ∈ S, monomial h (c h)
      = X ^ j * (∑ h ∈ S, monomial ((h - j) / q) (c h)).comp (X ^ q) := by
  have hcomp : ∀ s : Finset ℕ, (∑ h ∈ s, monomial ((h - j) / q) (c h)).comp (X ^ q)
      = ∑ h ∈ s, (monomial ((h - j) / q) (c h)).comp (X ^ q) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.add_comp, ih]
  rw [hcomp, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [Polynomial.monomial_comp, ← C_mul_X_pow_eq_monomial, ← pow_mul, Nat.mul_div_cancel' (hd h hh),
    show X ^ j * (C (c h) * X ^ (h - j)) = C (c h) * X ^ (j + (h - j)) by ring,
    Nat.add_sub_cancel' (hj h hh)]

/-- **The constant term of `φ`.** With `φ = ∑_{h ∈ S} c_h Y^{(h−j)/q}` (exponents `≥ j` and
`≡ j (mod q)`), the constant term is `φ(0) = c_j`: every other exponent `(h − j)/q` is nonzero. -/
theorem coeff_zero_sum_monomial {R : Type*} [CommRing R] {S : Finset ℕ} {j q : ℕ}
    (hj : ∀ h ∈ S, j ≤ h) (hd : ∀ h ∈ S, q ∣ (h - j)) (c : ℕ → R) (hjS : j ∈ S) :
    (∑ h ∈ S, monomial ((h - j) / q) (c h)).coeff 0 = c j := by
  rw [Polynomial.finsetSum_coeff]; simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj; rw [ite_eq_right]; intro he
    have hbj' : j < b := lt_of_le_of_ne (hj b hb) (Ne.symm hbj)
    have h1 := Nat.div_mul_cancel (hd b hb); rw [he, zero_mul] at h1; omega
  · intro h; exact absurd hjS h

/-- **The degree of `φ`.** With `φ = ∑_{h ∈ S} c_h Y^{(h−j)/q}` (exponents `≥ j` and `≡ j
(mod q)`, top column `k ∈ S` with `c_k ≠ 0`), the degree is `deg φ = (k − j)/q`. -/
theorem natDegree_sum_monomial {R : Type*} [CommRing R] {S : Finset ℕ} {j k q : ℕ}
    (hj : ∀ h ∈ S, j ≤ h) (hk : ∀ h ∈ S, h ≤ k) (hd : ∀ h ∈ S, q ∣ (h - j)) (c : ℕ → R)
    (hkS : k ∈ S) (hck : c k ≠ 0) :
    (∑ h ∈ S, monomial ((h - j) / q) (c h)).natDegree = (k - j) / q := by
  have hcoeff : (∑ h ∈ S, monomial ((h - j) / q) (c h)).coeff ((k - j) / q) = c k := by
    rw [Polynomial.finsetSum_coeff]; simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk; rw [ite_eq_right]; intro he; apply hbk
      have h1 := Nat.div_mul_cancel (hd b hb)
      have h2 := Nat.div_mul_cancel (hd k hkS)
      rw [he] at h1; have := hj b hb; have := hj k hkS; omega
    · intro h; exact absurd hkS h
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hck))
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro e he
  rw [Polynomial.finsetSum_coeff]; simp only [Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro h hh; rw [ite_eq_right]; intro heq
  have hle : (h - j) / q ≤ (k - j) / q := Nat.div_le_div_right (Nat.sub_le_sub_right (hk h hh) j)
  omega

variable {R : Type*} [Field R]

open Classical in
/-- **Lemma 2.97 for the characteristic polynomial.** If `q ∣ (h − j)` for every column `h` on
the edge `E = [A, B]` (`j = A.1`), then `Q(P, E, X) = X^j · φ(X^q)` for an explicit `φ ∈ R[X]`. -/
theorem charPoly_factor {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {q : ℕ}
    (hdvd : ∀ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B), q ∣ (h - A.1)) :
    charPoly P A B
      = X ^ A.1 * (∑ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
          monomial ((h - A.1) / q) (puiseuxInitCoeff R (P.coeff h))).comp (X ^ q) := by
  rw [charPoly]
  exact sum_monomial_factor
    (fun h hh => (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1) hdvd _

/-- **The `m`-extraction.** Given a common denominator `m` (so that `aj = m·A.2`, `ak = m·B.2`,
`ah = m·o(a_h)` are integers), a column `h` on the edge `E = [A, B]` satisfies `q ∣ (h − A.1)`
where `q = (B.1 − A.1)/gcd(ak − aj, B.1 − A.1)` is the reduced slope denominator. The
collinearity `o(a_h) = lineValue A B h` (i.e. `h` on `E`) clears to the integer hypothesis of
`dvd_sub_of_collinear`. -/
theorem colOnLine_dvd {A B : ℕ × ℚ} (hAB : A.1 < B.1) {m : ℚ} {aj ak ah : ℤ}
    (hmA : (aj : ℚ) = m * A.2) (hmB : (ak : ℚ) = m * B.2)
    {h : ℕ} (hjh : A.1 ≤ h) (hmh : (ah : ℚ) = m * lineValue A B h) :
    (B.1 - A.1) / (Int.gcd (ak - aj) ((B.1 : ℤ) - A.1)) ∣ (h - A.1) := by
  have hAB' : (A.1 : ℤ) < B.1 := by exact_mod_cast hAB
  have hne : ((B.1 : ℚ) - A.1) ≠ 0 := by
    have h2 : (A.1 : ℚ) < B.1 := by exact_mod_cast hAB
    intro hc; apply absurd h2; linarith [hc]
  have hcolZ : (ah - aj) * ((B.1 : ℤ) - A.1) = (ak - aj) * ((h : ℤ) - A.1) := by
    have hQ : ((ah - aj : ℤ) : ℚ) * (((B.1 : ℤ) - A.1 : ℤ) : ℚ)
        = ((ak - aj : ℤ) : ℚ) * (((h : ℤ) - A.1 : ℤ) : ℚ) := by
      simp only [lineValue, newtonSlope] at hmh
      push_cast [hmA, hmB, hmh]; field_simp; ring
    exact_mod_cast hQ
  have hdvdZ := dvd_sub_of_collinear hAB' hcolZ
  set g : ℕ := Int.gcd (ak - aj) ((B.1 : ℤ) - A.1) with hg
  have hsub : ((B.1 : ℤ) - A.1) = ((B.1 - A.1 : ℕ) : ℤ) := by rw [Nat.cast_sub (le_of_lt hAB)]
  have hhsub : ((h : ℤ) - A.1) = ((h - A.1 : ℕ) : ℤ) := by rw [Nat.cast_sub hjh]
  have hg0 : g ≠ 0 := by rw [hg]; exact (Int.gcd_pos_iff.mpr (Or.inr (by omega))).ne'
  have hgdvd : g ∣ (B.1 - A.1) := by
    have := Int.gcd_dvd_right (ak - aj) ((B.1 : ℤ) - A.1)
    rw [← hg, hsub] at this; exact_mod_cast this
  obtain ⟨q, hq⟩ := hgdvd
  rw [show (B.1 - A.1) / g = q from by rw [hq, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hg0)],
    ← Int.natCast_dvd_natCast, ← hhsub]
  have hqz : ((B.1 : ℤ) - A.1) / (g : ℤ) = (q : ℤ) := by
    rw [hsub, hq]; push_cast; rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0)]
  rw [← hqz]; exact hdvdZ

open Classical in
/-- **Lemma 2.97, fully discharged from `colOnLine`.** Given a common denominator `m` for the
orders along the edge `E = [A, B]`, the characteristic polynomial factors as
`Q(P, E, X) = X^j · φ(X^q)` with `q = (B.1 − A.1)/gcd(ak − aj, B.1 − A.1)`. -/
theorem charPoly_factor' {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} (hAB : A.1 < B.1)
    {m : ℚ} {aj ak : ℤ} (hmA : (aj : ℚ) = m * A.2) (hmB : (ak : ℚ) = m * B.2)
    (hmh : ∀ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
      ∃ z : ℤ, (z : ℚ) = m * lineValue A B h) :
    ∃ φ : Polynomial R, charPoly P A B
      = X ^ A.1 * φ.comp (X ^ ((B.1 - A.1) / Int.gcd (ak - aj) ((B.1 : ℤ) - A.1))) :=
  ⟨_, charPoly_factor fun h hh => by
    obtain ⟨ah, hah⟩ := hmh h hh
    exact colOnLine_dvd hAB hmA hmB (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1 hah⟩

/-- **A column on the edge has nonzero initial coefficient.** If `h` lies on `E`, then
`o(a_h) = lineValue A B h` is finite, so `a_h ≠ 0` and `In(a_h) ≠ 0`. -/
theorem initCoeff_ne_zero_of_colOnLine {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {h : ℕ}
    (hh : colOnLine P A B h) : puiseuxInitCoeff R (P.coeff h) ≠ 0 := by
  rw [puiseuxInitCoeff]
  apply HahnSeries.leadingCoeff_ne_zero.mpr
  intro h0
  rw [colOnLine, puiseuxOrder, h0] at hh
  simp at hh

open Classical in
/-- **`φ(0) = In(a_j)`.** The constant term of the polynomial `φ` of `charPoly_factor` is the
initial coefficient `In(a_{A.1})` of the left endpoint of the edge. -/
theorem charPoly_factor_phi_coeff_zero {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {q : ℕ}
    (hAB : A.1 ≤ B.1) (hA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ))
    (hdvd : ∀ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B), q ∣ (h - A.1)) :
    (∑ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
        monomial ((h - A.1) / q) (puiseuxInitCoeff R (P.coeff h))).coeff 0
      = puiseuxInitCoeff R (P.coeff A.1) :=
  coeff_zero_sum_monomial (fun h hh => (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1) hdvd _
    (by rw [Finset.mem_filter]
        exact ⟨Finset.mem_Icc.mpr ⟨le_refl _, hAB⟩, colOnLine_left (B := B) hA⟩)

open Classical in
/-- **`φ(0) ≠ 0`.** Since `In(a_{A.1}) ≠ 0`, the polynomial `φ` of `charPoly_factor` has nonzero
constant term, hence `φ(0) ≠ 0`. -/
theorem charPoly_factor_phi_coeff_zero_ne {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {q : ℕ}
    (hAB : A.1 ≤ B.1) (hA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ))
    (hdvd : ∀ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B), q ∣ (h - A.1)) :
    (∑ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
        monomial ((h - A.1) / q) (puiseuxInitCoeff R (P.coeff h))).coeff 0 ≠ 0 := by
  rw [charPoly_factor_phi_coeff_zero hAB hA hdvd]
  exact initCoeff_ne_zero_of_colOnLine (colOnLine_left (B := B) hA)

open Classical in
/-- **`deg φ = (k − j)/q`.** The polynomial `φ` of `charPoly_factor` has degree `(B.1 − A.1)/q`:
its top column is the right endpoint `B.1`, whose initial coefficient is nonzero. -/
theorem charPoly_factor_phi_natDegree {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {q : ℕ}
    (hAB : A.1 < B.1) (hB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ))
    (hdvd : ∀ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B), q ∣ (h - A.1)) :
    (∑ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
        monomial ((h - A.1) / q) (puiseuxInitCoeff R (P.coeff h))).natDegree
      = (B.1 - A.1) / q :=
  natDegree_sum_monomial (fun h hh => (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1)
    (fun h hh => (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).2) hdvd _
    (by rw [Finset.mem_filter]
        exact ⟨Finset.mem_Icc.mpr ⟨le_of_lt hAB, le_refl _⟩, colOnLine_right hAB.ne hB⟩)
    (initCoeff_ne_zero_of_colOnLine (colOnLine_right hAB.ne hB))

end Azurite.BPR
