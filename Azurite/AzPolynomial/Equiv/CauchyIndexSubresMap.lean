/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.CauchyIndexSubres
import Azurite.AzPolynomial.Equiv.Map
import Azurite.AzPolynomial.Equiv.TarskiQuerySubres
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_33
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_51
import Azurite.AzInt.Equiv.RingEquiv

/-!
# Transport of `cauchyIndex` across an order-preserving ring homomorphism

`cauchyIndex` (BPR Algorithm 9.4) is a *fraction-free* integer computation
over any ordered domain, so it runs over e.g. `AzInt`. Its meaning — the Cauchy
index — lives in a real closed field. This file bridges the two:

`cauchyIndex_map_eq_BPR`: for a **strictly monotone** (hence
injective, sign- and degree-preserving) ring hom `f : D →+* R` into a real closed
field `R`,
`cauchyIndex Q P = Ind((toPoly Q).map f / (toPoly P).map f)`.

The proof transports the computation itself: `cauchyIndex Q P` equals
`cauchyIndex (Q.map f) (P.map f)` (over `R`), because the signed
subresultant coefficients commute with `f` (`Chapter4.sRes_map`, via the
Sylvester–Habicht determinant), the pseudo-remainder normalization commutes
(`pRem_map`), and `PmV` reads only signs (`Chapter4.PmV_map`); then the
real-closed-field correctness `cauchyIndex_eq_BPR` applies.

Specialized to `D = AzInt` (`cauchyIndex_azInt_eq_BPR`), where the
embedding is `AzInt → ℤ → R` (`Int.cast ∘ toInt`).
-/

open Polynomial

namespace Azurite.AzPolynomial

/-! ### `AzPolynomial.map` along an injective ring hom -/

section MapHelpers
variable {D E : Type*} [CommRing D] [DecidableEq D] [CommRing E] [DecidableEq E]

omit [DecidableEq D] in
/-- Degree is preserved by `AzPolynomial.map` along an injective ring hom. -/
theorem natDegree_map_of_injective (f : D →+* E) (hf : Function.Injective f) (P : AzPolynomial D) :
    (P.map f).natDegree = P.natDegree := by
  rw [← AzPolynomial.natDegree_toPoly, ← AzPolynomial.natDegree_toPoly, toPoly_map]
  exact natDegree_map_eq_of_injective hf _

/-- `AzPolynomial.map` along an injective ring hom is zero only on zero. -/
theorem map_eq_zero_iff_of_injective (f : D →+* E) (hf : Function.Injective f) (Q : AzPolynomial D) :
    Q.map f = 0 ↔ Q = 0 := by
  rw [← toPoly_inj (p := Q.map f) (q := 0), ← toPoly_inj (p := Q) (q := 0)]
  simp only [toPoly_map, toPoly_zero, Polynomial.map_eq_zero_iff hf]

omit [DecidableEq D] in
/-- `AzPolynomial.map` along an injective ring hom sends leading coefficients to
their images. -/
theorem leadingCoeff_map_of_injective (f : D →+* E) (hf : Function.Injective f) (P : AzPolynomial D) :
    (P.map f).leadingCoeff = f P.leadingCoeff := by
  rw [← leadingCoeff_toPoly, ← leadingCoeff_toPoly, toPoly_map,
    Polynomial.leadingCoeff_map_of_injective hf]

/-- `AzPolynomial.map` distributes over multiplication. -/
theorem map_mul' (f : D →+* E) (P Q : AzPolynomial D) : (P * Q).map f = P.map f * Q.map f := by
  apply toPoly_inj.mp
  rw [toPoly_map, toPoly_mul, toPoly_mul, toPoly_map, toPoly_map, Polynomial.map_mul]

/-- `AzPolynomial.map` distributes over negation. -/
theorem map_neg' (f : D →+* E) (P : AzPolynomial D) : (-P).map f = -(P.map f) := by
  apply toPoly_inj.mp; rw [toPoly_map, toPoly_neg, toPoly_neg, toPoly_map, Polynomial.map_neg]

/-- `AzPolynomial.map` distributes over subtraction. -/
theorem map_sub' (f : D →+* E) (P Q : AzPolynomial D) : (P - Q).map f = P.map f - Q.map f := by
  apply toPoly_inj.mp
  rw [toPoly_map, toPoly_sub, toPoly_sub, toPoly_map, toPoly_map, Polynomial.map_sub]

omit [DecidableEq D] in
/-- Coefficients of `AzPolynomial.map` are the images of the coefficients. -/
theorem coeff_map' (f : D →+* E) (P : AzPolynomial D) (n : ℕ) : (P.map f).coeff n = f (P.coeff n) := by
  rw [← coeff_toPoly, ← coeff_toPoly, toPoly_map, Polynomial.coeff_map]

/-- `AzPolynomial.map` sends `c • P` to `f c • (P.map f)`. -/
theorem map_smul' (f : D →+* E) (c : D) (P : AzPolynomial D) : (c • P).map f = f c • (P.map f) := by
  apply toPoly_inj.mp
  rw [toPoly_map, toPoly_smul, toPoly_smul, toPoly_map, Polynomial.smul_eq_C_mul,
    Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C]

/-- `AzPolynomial.map` commutes with the formal derivative. -/
theorem map_derivative' [PolynomialDerivative D] [PolynomialDerivative E]
    (f : D →+* E) (P : AzPolynomial D) : (derivative P).map f = derivative (P.map f) := by
  apply toPoly_inj.mp
  rw [toPoly_map, toPoly_derivative, toPoly_derivative, toPoly_map, Polynomial.derivative_map]

end MapHelpers

/-! ### `pRem` transport (target field) -/

section PRemMap
variable {D E : Type*} [CommRing D] [DecidableEq D] [Field E] [DecidableEq E]

/-- **`pRem` commutes with an injective ring hom into a field.** Both
`pRem (P.map f) (Q.map f)` and `(pRem P Q).map f` are the (unique) polynomial
remainder of `C(lc Q ^ e) · P` modulo `Q` after mapping to `E[X]`. -/
theorem pRem_map (f : D →+* E) (hf : Function.Injective f) (P Q : AzPolynomial D) :
    pRem (P.map f) (Q.map f) = (pRem P Q).map f := by
  apply toPoly_inj.mp
  rw [toPoly_map]
  rcases eq_or_ne (AzPolynomial.toPoly Q) 0 with hQ0 | hQm
  · have hQ : Q = 0 := toPoly_inj.mp (by rw [hQ0, toPoly_zero])
    subst hQ
    rw [(map_eq_zero_iff_of_injective f hf 0).mpr rfl,
      show pRem (P.map f) 0 = P.map f by simp [pRem],
      show pRem P 0 = P by simp [pRem], toPoly_map]
  · have hQfm : AzPolynomial.toPoly (Q.map f) ≠ 0 := by
      rw [toPoly_map]; exact (Polynomial.map_ne_zero_iff hf).mpr hQm
    have hGne : (AzPolynomial.toPoly Q).map f ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hQm
    obtain ⟨A, hA⟩ := toPoly_pRem_div_eq P Q hQm
    obtain ⟨A', hA'⟩ := toPoly_pRem_div_eq (P.map f) (Q.map f) hQfm
    set e := Azurite.BPR.pRemExp (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) with he
    set M := Polynomial.C (f Q.leadingCoeff ^ e) * (AzPolynomial.toPoly P).map f with hM
    set G := (AzPolynomial.toPoly Q).map f with hG
    have hAmap : M = A.map f * G + (AzPolynomial.toPoly (pRem P Q)).map f := by
      have := congrArg (Polynomial.map f) hA
      simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow,
        map_pow, hM, hG] using this
    have hA'2 : M = A' * G + AzPolynomial.toPoly (pRem (P.map f) (Q.map f)) := by
      rw [hM, hG, ← toPoly_map, ← toPoly_map (f := f) (p := Q),
        ← leadingCoeff_map_of_injective f hf Q,
        show e = Azurite.BPR.pRemExp (AzPolynomial.toPoly (P.map f)) (AzPolynomial.toPoly (Q.map f)) from by
          simp only [he, toPoly_map, Azurite.BPR.pRemExp, Polynomial.natDegree_map_eq_of_injective hf]]
      exact hA'
    have hdeg1 : ((AzPolynomial.toPoly (pRem P Q)).map f).degree < G.degree := by
      rw [hG, Polynomial.degree_map_eq_of_injective hf, Polynomial.degree_map_eq_of_injective hf]
      exact degree_toPoly_pRem_lt P Q hQm
    have hdeg2 : (AzPolynomial.toPoly (pRem (P.map f) (Q.map f))).degree < G.degree := by
      rw [hG, ← toPoly_map (f := f) (p := Q)]
      exact degree_toPoly_pRem_lt (P.map f) (Q.map f) hQfm
    have h1 : (AzPolynomial.toPoly (pRem P Q)).map f = M % G := by
      rw [mod_eq_of_dvd_sub (show G ∣ M - (AzPolynomial.toPoly (pRem P Q)).map f from
          ⟨A.map f, by rw [hAmap]; ring⟩), (Polynomial.mod_eq_self_iff hGne).mpr hdeg1]
    have h2 : AzPolynomial.toPoly (pRem (P.map f) (Q.map f)) = M % G := by
      rw [mod_eq_of_dvd_sub (show G ∣ M - AzPolynomial.toPoly (pRem (P.map f) (Q.map f)) from
          ⟨A', by rw [hA'2]; ring⟩), (Polynomial.mod_eq_self_iff hGne).mpr hdeg2]
    rw [h2, h1]

end PRemMap

/-! ### `signedSubresultant` coefficient list transport -/

section SignedSubresMap
variable {D E : Type*} [CommRing D] [LinearOrder D] [IsStrictOrderedRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [CommRing E] [LinearOrder E] [IsStrictOrderedRing E] [DecidableEq E]
    [Azurite.ExactDiv E]

open Azurite.BPR.Chapter4 (sRes)

omit [LinearOrder D] [IsStrictOrderedRing D] [LinearOrder E] [IsStrictOrderedRing E] in
/-- `f (epsilonSign n) = epsilonSign n` for a ring hom `f` (it is `±1`). -/
theorem map_epsilonSign (f : D →+* E) (n : ℕ) : f (epsilonSign n) = epsilonSign n := by
  rw [epsilonSign_eq, epsilonSign_eq, map_pow, map_neg, map_one]

/-- **The `.2` signed-subresultant coefficient list commutes with an injective ring hom.** -/
theorem signedSubresultant_snd_toList_map (f : D →+* E) (hf : Function.Injective f)
    (P Q : AzPolynomial D) :
    (signedSubresultant (P.map f) (Q.map f)).2.toList
      = (signedSubresultant P Q).2.toList.map f := by
  by_cases hc : Q = 0 ∨ P.natDegree ≤ Q.natDegree
  · have hc' : Q.map f = 0 ∨ (P.map f).natDegree ≤ (Q.map f).natDegree := by
      rcases hc with h | h
      · exact Or.inl ((map_eq_zero_iff_of_injective f hf Q).mpr h)
      · exact Or.inr (by rw [natDegree_map_of_injective f hf, natDegree_map_of_injective f hf]; exact h)
    rw [signedSubresultant, ite_eq_left hc', signedSubresultant, ite_eq_left hc]; simp
  · obtain ⟨hQ, hle⟩ := not_or.mp hc
    have hlt : Q.natDegree < P.natDegree := not_le.mp hle
    have hP : P ≠ 0 := fun h => by rw [h, show (0 : AzPolynomial D).natDegree = 0 from rfl] at hlt; omega
    have hQ' : Q.map f ≠ 0 := fun h => hQ ((map_eq_zero_iff_of_injective f hf Q).mp h)
    have hP' : P.map f ≠ 0 := fun h => hP ((map_eq_zero_iff_of_injective f hf P).mp h)
    have hlt' : (Q.map f).natDegree < (P.map f).natDegree := by
      rw [natDegree_map_of_injective f hf, natDegree_map_of_injective f hf]; exact hlt
    rcases Nat.eq_zero_or_pos Q.natDegree with hq0 | hq1
    · have hq0' : (Q.map f).natDegree = 0 := by rw [natDegree_map_of_injective f hf]; exact hq0
      rw [snd_toList_deg0 (P.map f) (Q.map f) hQ' hq0'
            (by rw [natDegree_map_of_injective f hf]; omega),
          snd_toList_deg0 P Q hQ hq0 (by omega)]
      simp only [List.map_cons, List.map_append, List.map_replicate, List.map_nil, map_zero,
        natDegree_map_of_injective f hf, leadingCoeff_map_of_injective f hf, one_pow]
      rw [exactDiv_one', exactDiv_one', map_mul, map_pow, map_epsilonSign]
    · rw [(signedSubresultant_toPoly_domain (P.map f) (Q.map f) hP' hQ' hlt'
            (by rw [natDegree_map_of_injective f hf]; omega)).2,
          (signedSubresultant_toPoly_domain P Q hP hQ hlt hq1).2, List.map_map,
          natDegree_map_of_injective f hf]
      apply List.map_congr_left; intro j hj
      simp only [List.mem_range] at hj
      simp only [Function.comp_apply, toPoly_map]
      rw [Azurite.BPR.Chapter8.sRes_map hf (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (by rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hlt)
        (by rw [AzPolynomial.natDegree_toPoly]; omega)]

end SignedSubresMap

/-! ### Transport of `cauchyIndex` -/

section Transport
variable {D R : Type*} [CommRing D] [LinearOrder D] [IsStrictOrderedRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    [Azurite.ExactDiv R] [IsRealClosed R]

open Azurite.BPR.Chapter4 (PmV)

/-- **Transport of `cauchyIndex` (BPR Algorithm 9.4) across an order
embedding.** For a strictly monotone ring hom `f : D →+* R` into a real closed
field `R`, the fraction-free `cauchyIndex` computed over the ordered domain
`D` equals the Cauchy index of the polynomials pushed into `R`. -/
theorem cauchyIndex_map_eq_BPR (f : D →+* R) (hf : StrictMono f)
    (Q P : AzPolynomial D) :
    cauchyIndex Q P
      = Azurite.BPR.cauchyIndex ((AzPolynomial.toPoly Q).map f) ((AzPolynomial.toPoly P).map f) := by
  have hfi := hf.injective
  rw [← toPoly_map, ← toPoly_map, ← cauchyIndex_eq_BPR (Q.map f) (P.map f)]
  show PmV (signedSubresultant P
        (if P.natDegree ≤ Q.natDegree then pRem Q P else Q)).2.toList.reverse
    = PmV (signedSubresultant (P.map f)
        (if (P.map f).natDegree ≤ (Q.map f).natDegree then pRem (Q.map f) (P.map f)
          else Q.map f)).2.toList.reverse
  rw [natDegree_map_of_injective f hfi, natDegree_map_of_injective f hfi,
    show (if P.natDegree ≤ Q.natDegree then pRem (Q.map f) (P.map f) else Q.map f)
        = (if P.natDegree ≤ Q.natDegree then pRem Q P else Q).map f from by
      split_ifs with h
      · exact pRem_map f hfi Q P
      · rfl,
    signedSubresultant_snd_toList_map f hfi, ← List.map_reverse,
    Azurite.BPR.Chapter4.PmV_map hf]

end Transport

/-! ### Specialization to `AzInt` -/

/-- The order embedding `AzInt → ℤ → R` (strictly monotone ring hom into any
strictly ordered ring). -/
theorem azIntCast_strictMono {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] :
    StrictMono ((Int.castRingHom R).comp AzInt.toIntRingHom) := fun a b h => by
  simp only [RingHom.comp_apply, AzInt.toIntRingHom_apply, Int.coe_castRingHom]
  exact_mod_cast show a.toInt < b.toInt by simpa using AzInt.orderIsoInt.strictMono h

/-- **Correctness of `cauchyIndex` over `AzInt`.** For integer-coefficient
polynomials, the fraction-free signed-subresultant Cauchy index equals the Cauchy
index of the polynomials cast into any real closed field `R` (via `AzInt → ℤ → R`). -/
theorem cauchyIndex_azInt_eq_BPR {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [DecidableEq R] [Azurite.ExactDiv R] [IsRealClosed R]
    (Q P : AzPolynomial AzInt) :
    cauchyIndex Q P
      = Azurite.BPR.cauchyIndex
          ((AzPolynomial.toPoly Q).map ((Int.castRingHom R).comp AzInt.toIntRingHom))
          ((AzPolynomial.toPoly P).map ((Int.castRingHom R).comp AzInt.toIntRingHom)) :=
  cauchyIndex_map_eq_BPR _ azIntCast_strictMono Q P

/-! ### Transport of `tarskiQuery` -/

section TarskiTransport
open Azurite.BPR.Chapter4 (PmV PmV_map)
variable {D R : Type*} [CommRing D] [LinearOrder D] [IsStrictOrderedRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq R] [Azurite.ExactDiv R] [IsRealClosed R]

/-- **Transport of `tarskiQuery` (BPR Algorithm 9.5) across an order
embedding.** For a strictly monotone ring hom `f : D →+* R` into a real closed
field `R` and non-constant `P` (`1 ≤ deg P`), the fraction-free signed-subresultant
Tarski query computed over the ordered domain `D` equals the Tarski query of the
polynomials pushed into `R`. -/
theorem tarskiQuery_map_eq_BPR (f : D →+* R) (hf : StrictMono f)
    (Q P : AzPolynomial D) (hP1 : 1 ≤ P.natDegree) :
    tarskiQuery Q P
      = Azurite.BPR.tarskiQuery ((AzPolynomial.toPoly Q).map f) ((AzPolynomial.toPoly P).map f) := by
  have hfi := hf.injective
  have hsign : ∀ x : D, (SignType.sign (f x) : ℤ) = (SignType.sign x : ℤ) := fun x => by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [sign_neg h, sign_neg (map_zero f ▸ hf h)]
    · simp [h, map_zero f]
    · rw [sign_pos h, sign_pos (map_zero f ▸ hf h)]
  rw [← toPoly_map, ← toPoly_map, ← tarskiQuery_eq_BPR (Q.map f) (P.map f)
    (by rw [natDegree_map_of_injective f hfi]; exact hP1)]
  show (if Q.natDegree = 0 then
      (SignType.sign (Q.coeff 0) : ℤ) * PmV (signedSubresultant P (derivative P)).2.toList.reverse
    else if Q.natDegree = 1 then
      PmV (signedSubresultant P (derivative P * Q - ((P.natDegree : D) * Q.coeff 1) • P)).2.toList.reverse
    else if (Q.natDegree - 1) % 2 = 1 then
      PmV (signedSubresultant (-(derivative P * Q)) P).2.toList.reverse + (SignType.sign Q.leadingCoeff : ℤ)
    else PmV (signedSubresultant (-(derivative P * Q)) P).2.toList.reverse)
    = (if (Q.map f).natDegree = 0 then
      (SignType.sign ((Q.map f).coeff 0) : ℤ)
        * PmV (signedSubresultant (P.map f) (derivative (P.map f))).2.toList.reverse
    else if (Q.map f).natDegree = 1 then
      PmV (signedSubresultant (P.map f)
        (derivative (P.map f) * Q.map f
          - (((P.map f).natDegree : R) * (Q.map f).coeff 1) • P.map f)).2.toList.reverse
    else if ((Q.map f).natDegree - 1) % 2 = 1 then
      PmV (signedSubresultant (-(derivative (P.map f) * Q.map f)) (P.map f)).2.toList.reverse
        + (SignType.sign (Q.map f).leadingCoeff : ℤ)
    else PmV (signedSubresultant (-(derivative (P.map f) * Q.map f)) (P.map f)).2.toList.reverse)
  simp only [natDegree_map_of_injective f hfi]
  split_ifs with ha hb hc
  · rw [coeff_map' f, hsign, ← map_derivative' f P, signedSubresultant_snd_toList_map f hfi,
      ← List.map_reverse, PmV_map hf]
  · rw [show (derivative (P.map f) * Q.map f - ((P.natDegree : R) * (Q.map f).coeff 1) • P.map f)
          = (derivative P * Q - ((P.natDegree : D) * Q.coeff 1) • P).map f from by
        rw [map_sub', map_mul', map_smul', map_derivative', coeff_map', map_mul, map_natCast],
      signedSubresultant_snd_toList_map f hfi, ← List.map_reverse, PmV_map hf]
  · rw [show (-(derivative (P.map f) * Q.map f)) = (-(derivative P * Q)).map f from by
        rw [map_neg', map_mul', map_derivative'],
      signedSubresultant_snd_toList_map f hfi, ← List.map_reverse, PmV_map hf,
      leadingCoeff_map_of_injective f hfi, hsign]
  · rw [show (-(derivative (P.map f) * Q.map f)) = (-(derivative P * Q)).map f from by
        rw [map_neg', map_mul', map_derivative'],
      signedSubresultant_snd_toList_map f hfi, ← List.map_reverse, PmV_map hf]

end TarskiTransport

/-- **Correctness of `tarskiQuery` over `AzInt`.** For integer-coefficient
polynomials with non-constant `P`, the fraction-free signed-subresultant Tarski
query equals the Tarski query of the polynomials cast into any real closed field
`R` (via `AzInt → ℤ → R`). -/
theorem tarskiQuery_azInt_eq_BPR {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [DecidableEq R] [Azurite.ExactDiv R] [IsRealClosed R]
    (Q P : AzPolynomial AzInt) (hP1 : 1 ≤ P.natDegree) :
    tarskiQuery Q P
      = Azurite.BPR.tarskiQuery
          ((AzPolynomial.toPoly Q).map ((Int.castRingHom R).comp AzInt.toIntRingHom))
          ((AzPolynomial.toPoly P).map ((Int.castRingHom R).comp AzInt.toIntRingHom)) :=
  tarskiQuery_map_eq_BPR _ azIntCast_strictMono Q P hP1

end Azurite.AzPolynomial
