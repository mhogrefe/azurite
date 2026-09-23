/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.Definition_4_67
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Reduction
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Remark_4_66
import Azurite.BasuPollackRoy.Chapter4.Section4_4.IdealOfPolynomials
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# BPR Proposition 4.68: membership via reduction to zero

If `𝒢` is a Gröbner basis of an ideal `I` for the monomial ordering `m`, then a polynomial `P`
belongs to `I` if and only if `P` is reducible to `0` modulo `𝒢` (`proposition_4_68`).

The "if" direction is immediate from Remark 4.66 (`remark_4_66`): a reduction to zero exhibits
`P` as an element of `Ideal(𝒢, K) ⊆ I`. The "only if" direction is the heart of the
correctness of the reduction algorithm: by well-founded induction on the leading monomial, the
Gröbner-basis property lets us reduce the leading term of any nonzero `P ∈ I` by some `G ∈ 𝒢`,
strictly decreasing the leading monomial, until we reach `0`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- The single reduction `Red(P, lmon(P), G)` of `P` at its leading monomial by `G` agrees with
Mathlib's `m.reduce`, when `lmon(G) ∣ lmon(P)`. -/
private theorem Red_eq_reduce (m : MonomialOrder (Fin k)) (P G : MvPolynomial (Fin k) K)
    (hb : IsUnit (m.leadingCoeff G)) (hbf : m.degree G ≤ m.degree P) :
    Red m P (m.degree P) G = m.reduce hb P := by
  rw [Red_of_le m P G hbf, MonomialOrder.reduce]
  congr 2
  -- equate the two monomial coefficients
  have hlcG : (↑hb.unit⁻¹ : K) = (m.leadingCoeff G)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hb.unit_spec]
  -- `P.coeff (m.degree P) = m.leadingCoeff P` by definition
  have hlcP : P.coeff (m.degree P) = m.leadingCoeff P := rfl
  rw [hlcG, hlcP, div_eq_inv_mul, mul_comm]

/-- **BPR Proposition 4.68.** Let `𝒢` be a Gröbner basis of the ideal `I` for the monomial
ordering `m`. Then a polynomial `P` belongs to `I` if and only if `P` is reducible to `0`
modulo `𝒢`. -/
theorem proposition_4_68 (m : MonomialOrder (Fin k)) {I : Ideal (MvPolynomial (Fin k) K)}
    {𝒢 : Finset (MvPolynomial (Fin k) K)} (hG : IsGrobnerBasisOf m I 𝒢)
    (P : MvPolynomial (Fin k) K) :
    P ∈ I ↔ ReducibleTo m 𝒢 P 0 := by
  constructor
  · -- Hard direction: P ∈ I → ReducibleTo m 𝒢 P 0
    intro hPI
    -- well-founded induction on the leading monomial m.toSyn (m.degree P)
    have key : ∀ d : m.syn, ∀ P : MvPolynomial (Fin k) K, m.toSyn (m.degree P) = d →
        P ∈ I → ReducibleTo m 𝒢 P 0 := by
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro P hdeg hPI
        by_cases hP0 : P = 0
        · subst hP0; exact Relation.ReflTransGen.refl
        · obtain ⟨G, hG𝒢, hG0, hdeg_le⟩ := hG.2.1 P hPI hP0
          have hlc : m.leadingCoeff G ≠ 0 :=
            fun hc => hG0 (MonomialOrder.leadingCoeff_eq_zero_iff.mp hc)
          have hb : IsUnit (m.leadingCoeff G) := isUnit_iff_ne_zero.mpr hlc
          set Q := Red m P (m.degree P) G with hQdef
          have hstep : IsReduction m 𝒢 P Q :=
            ⟨G, hG𝒢, m.degree P, MonomialOrder.degree_mem_support hP0, rfl⟩
          -- Q ∈ I
          have hQI : Q ∈ I := by
            rw [hQdef, Red_of_le m P G hdeg_le]
            exact Ideal.sub_mem I hPI (Ideal.mul_mem_left I _ (hG.1 G hG𝒢))
          -- Q = 0 or degree strictly decreases
          have hQ : Q = 0 ∨ m.toSyn (m.degree Q) < m.toSyn (m.degree P) := by
            by_cases hdP : m.degree P = 0
            · -- both P and G are constants; Q = 0
              left
              have hdG : m.degree G = 0 := le_antisymm (hdP ▸ hdeg_le) (by positivity)
              have hPC : P = C (m.leadingCoeff P) := MonomialOrder.eq_C_of_degree_eq_zero hdP
              have hGC : G = C (m.leadingCoeff G) := MonomialOrder.eq_C_of_degree_eq_zero hdG
              rw [hQdef, Red_of_le m P G hdeg_le, hdP, hdG, tsub_zero, monomial_zero']
              show P - C (P.coeff 0 / m.leadingCoeff G) * G = 0
              have hc0 : P.coeff 0 = m.leadingCoeff P := by rw [← hdP]; rfl
              have hmul : C (P.coeff 0 / m.leadingCoeff G) * G = P := by
                rw [hc0]
                nth_rewrite 2 [hGC]
                rw [← C_mul, div_mul_cancel₀ _ hlc, ← hPC]
              rw [hmul, sub_self]
            · -- m.degree P ≠ 0: reduce decreases the leading monomial
              right
              have hQr : Q = m.reduce hb P := by rw [hQdef, Red_eq_reduce m P G hb hdeg_le]
              rw [hQr]
              exact MonomialOrder.degree_reduce_lt hb hdeg_le hdP
          rcases hQ with hQ0 | hQlt
          · exact hQ0 ▸ Relation.ReflTransGen.single hstep
          · have hQd : m.toSyn (m.degree Q) < d := hdeg ▸ hQlt
            exact Relation.ReflTransGen.head hstep
              (ih (m.toSyn (m.degree Q)) hQd Q rfl hQI)
    exact key _ P rfl hPI
  · -- Easy direction: ReducibleTo m 𝒢 P 0 → P ∈ I
    intro h
    have hsub := remark_4_66 m 𝒢 h
    rw [sub_zero] at hsub
    have hle : Ideal.span (↑𝒢 : Set _) ≤ I :=
      Ideal.span_le.mpr (fun x hx => hG.1 x (Finset.mem_coe.mp hx))
    exact hle hsub

end Azurite.BPR.Chapter4
