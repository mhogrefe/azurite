/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Equiv.IntContentMul
import Azurite.AzMvPolynomial.Equiv.GcdCofactor
import Azurite.AzNat.Equiv.RingEquiv
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Multivariate Gauss content-descent

The multivariate Gauss lemma that Mathlib lacks for `MvPolynomial`: a primitive
integer polynomial dividing a polynomial over `ℚ` already divides it over `ℤ`.
Proven by the classical route — clear denominators of the `ℚ`-witness, take
`intContent`, and peel the resulting integer constant using primitivity — using
the delivered `intContent_mul` / `intContent_C_mul` / `C_dvd_iff_dvd_coeff`.

This is the linchpin unlocking `coprime → IsRelPrime` (`coprime_isRelPrime`),
and thence injectivity of the `AzMvRationalFunction → ℚ(x⃗)` representation.
-/

namespace Azurite.AzMvPolynomial

open _root_.Azurite.MvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- **Denominator clearing**: any `h ∈ ℚ[x⃗]` has a nonzero integer multiple
`C c · h` with integer coefficients (the image of some `H ∈ ℤ[x⃗]`). -/
theorem mvClearDenom (h : MvPolynomial (Fin n) ℚ) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ H : MvPolynomial (Fin n) ℤ,
      MvPolynomial.C (c : ℚ) * h = H.map (Int.castRingHom ℚ) := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) h.support h.coeff
  choose z hz using hb
  refine ⟨(b : ℤ), nonZeroDivisors.coe_ne_zero b,
    ∑ m ∈ h.support, MvPolynomial.monomial m (if hm : m ∈ h.support then z m hm else 0), ?_⟩
  ext m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' h.support m
    (fun m => if hm : m ∈ h.support then z m hm else 0)]
  by_cases hm : m ∈ h.support
  · rw [ite_eq_left hm, dite_eq_left hm]
    have hval := hz m hm
    rw [zsmul_eq_mul] at hval
    exact hval.symm
  · rw [ite_eq_right hm, MvPolynomial.notMem_support_iff.mp hm, mul_zero, map_zero]

/-- If `|c|` divides the content of `K`, then `C c` divides `K`. -/
theorem C_dvd_of_abs_dvd_intContent {c : AzInt} {K : AzMvPolynomial n AzInt ord}
    (h : c.abs ∣ intContent K) : AzMvPolynomial.C c ∣ K := by
  rw [← map_dvd_iff (Azurite.ringEquivMvPolynomial (R := AzInt) (n := n) (ord := ord))]
  show toMvPoly (AzMvPolynomial.C c) ∣ toMvPoly K
  rw [toMvPoly_C, MvPolynomial.C_dvd_iff_dvd_coeff]
  intro f
  by_cases hz : K.toMvPoly.coeff f = 0
  · rw [hz]; exact dvd_zero _
  · have hmem : f ∈ K.toMvPoly.support := MvPolynomial.mem_support_iff.mpr hz
    rw [support_toMvPoly, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨mm, hmm, rfl⟩ := hmem
    rw [coeff_toMvPoly_of_mem hmm]
    apply (map_dvd_iff Azurite.AzInt.ringEquivInt).mp
    show c.toInt ∣ (mm.coeff.val).toInt
    rw [← Int.natAbs_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast,
      Azurite.AzInt.toNat_abs, Azurite.AzInt.toNat_abs]
    have hcdvd : c.abs.toNat ∣ (intContent K).toNat := by
      have hd := map_dvd Azurite.AzNat.ringEquivNat h
      rwa [Azurite.AzNat.ringEquivNat_apply, Azurite.AzNat.ringEquivNat_apply] at hd
    refine hcdvd.trans ?_
    rw [toNat_intContent]
    exact Azurite.AzPolynomial.foldl_gcd_dvd_mem _ 0 (List.mem_map_of_mem hmm)

/-- `intImg (C c)`, mapped to `ℚ[x⃗]`, is the constant `c`. -/
private theorem map_intImg_C (c : AzInt) :
    (intImg (AzMvPolynomial.C c : AzMvPolynomial n AzInt ord)).map (Int.castRingHom ℚ)
      = MvPolynomial.C ((c.toInt : ℚ)) := by
  rw [intImg, ringEquivMvPolynomialInt_apply, toMvPoly_C, MvPolynomial.map_C, MvPolynomial.map_C]
  rfl

/-- **Multivariate Gauss content-descent**: a primitive `P` dividing `M` over
`ℚ[x⃗]` (through `intImg`) already divides `M` over `ℤ[x⃗]`. -/
theorem dvd_of_map_intImg_dvd {P M : AzMvPolynomial n AzInt ord}
    (hP : intContent P = 1)
    (hdvd : (intImg P).map (Int.castRingHom ℚ) ∣ (intImg M).map (Int.castRingHom ℚ)) :
    P ∣ M := by
  by_cases hM : M = 0
  · subst hM; exact dvd_zero P
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [show intContent (0 : AzMvPolynomial n AzInt ord) = 0 from rfl] at hP
    exact zero_ne_one hP
  obtain ⟨hq, hh⟩ := hdvd
  obtain ⟨c, hc0, H, hHmap⟩ := mvClearDenom hq
  set cAz := Azurite.AzInt.ringEquivInt.symm c with hcAz
  have hcAztoInt : cAz.toInt = c := Azurite.AzInt.ringEquivInt.apply_symm_apply c
  have hcAz0 : cAz ≠ 0 := by rintro h; apply hc0; rw [← hcAztoInt, h]; rfl
  set K := (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm H with hKdef
  have hintK : intImg K = H := by
    rw [hKdef]; exact (AzMvPolynomial.ringEquivMvPolynomialInt).apply_symm_apply H
  have hmapQ : (intImg (AzMvPolynomial.C cAz * M)).map (Int.castRingHom ℚ)
      = (intImg (P * K)).map (Int.castRingHom ℚ) := by
    rw [intImg_mul, intImg_mul, map_mul, map_mul, hintK,
      map_intImg_C, hcAztoInt, hh, ← hHmap]
    ring
  have hkey : AzMvPolynomial.C cAz * M = P * K :=
    (AzMvPolynomial.ringEquivMvPolynomialInt).injective
      (MvPolynomial.map_injective _ Int.cast_injective hmapQ)
  have hCne : (AzMvPolynomial.C cAz : AzMvPolynomial n AzInt ord) ≠ 0 := by
    intro h; apply hcAz0
    have hh2 := congrArg toMvPoly h
    rw [toMvPoly_C, toMvPoly_zero] at hh2
    exact MvPolynomial.C_eq_zero.mp hh2
  have hK0 : K ≠ 0 := by
    intro h; rw [h, mul_zero] at hkey
    exact (mul_ne_zero hCne hM) hkey
  have hcontent : cAz.abs * intContent M = intContent K := by
    have h1 : intContent (AzMvPolynomial.C cAz * M) = intContent (P * K) := by rw [hkey]
    rwa [intContent_C_mul, intContent_mul, hP, one_mul] at h1
  obtain ⟨K', hK'⟩ := C_dvd_of_abs_dvd_intContent (K := K)
    (c := cAz) ⟨intContent M, hcontent.symm⟩
  refine ⟨K', mul_left_cancel₀ hCne ?_⟩
  rw [hkey, hK']; ring

/-! ### `coprime → IsRelPrime` over `ℚ[x⃗]` -/

/-- The `ℚ[x⃗]`-image `ratImg` factors as `intImg` followed by the `ℤ → ℚ` cast. -/
theorem ratImg_eq_map_intImg (P : AzMvPolynomial n AzInt ord) :
    ratImg P = (intImg P).map (Int.castRingHom ℚ) := by
  rw [intImg, ringEquivMvPolynomialInt_apply, MvPolynomial.map_map]
  rfl

private theorem toInt_ne_zero {z : AzInt} (hz : z ≠ 0) : z.toInt ≠ 0 :=
  fun h => hz (Azurite.AzInt.ringEquivInt.injective (by simpa using h))

private theorem map_intImg_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    (intImg P).map (Int.castRingHom ℚ) ≠ 0 := by
  intro h
  apply hP
  have h1 : intImg P = 0 := MvPolynomial.map_injective _ Int.cast_injective (by rw [h, map_zero])
  exact (AzMvPolynomial.ringEquivMvPolynomialInt).injective (h1.trans (map_zero _).symm)

/-- **The primitive `ℤ`-preimage of a nonzero `ℚ[x⃗]` polynomial.** For any
nonzero `d : ℚ[x⃗]` there is a primitive `q : AzMvPolynomial n AzInt ord`
(`intContent q = 1`) whose `ℚ[x⃗]`-image is an associate of `d`, and which
divides any `M` whose `ℚ[x⃗]`-image `d` divides. This packages the shared
denominator-clearing / content-descent step used by both `coprime_isRelPrime`
and `squarefree_of_isSquarefree`. -/
theorem exists_primitive_preimage {d : MvPolynomial (Fin n) ℚ} (hd0 : d ≠ 0) :
    ∃ q : AzMvPolynomial n AzInt ord,
      intContent q = 1 ∧ Associated (ratImg q) d ∧
        ∀ M : AzMvPolynomial n AzInt ord, d ∣ ratImg M → q ∣ M := by
  obtain ⟨e, he0, Dz, hDz⟩ := mvClearDenom d
  set Daz := (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm Dz with hDazdef
  have hDazImg : intImg Daz = Dz := by
    rw [hDazdef]; exact (AzMvPolynomial.ringEquivMvPolynomialInt).apply_symm_apply Dz
  have hCe_unit : IsUnit (MvPolynomial.C (e : ℚ) : MvPolynomial (Fin n) ℚ) :=
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast he0)).map MvPolynomial.C
  have hDazImgQ : (intImg Daz).map (Int.castRingHom ℚ) = MvPolynomial.C (e : ℚ) * d := by
    rw [hDazImg, ← hDz]
  have hDaz0 : Daz ≠ 0 := by
    intro h
    have hz : MvPolynomial.C (e : ℚ) * d = 0 := by
      rw [← hDazImgQ, h,
        show intImg (0 : AzMvPolynomial n AzInt ord) = 0 from
          map_zero AzMvPolynomial.ringEquivMvPolynomialInt, map_zero]
    exact (mul_ne_zero hCe_unit.ne_zero hd0) hz
  set q := primPos Daz with hqdef
  have hq_prim : intContent q = 1 := intContent_primPos hDaz0
  have hq_dvd_Daz : q ∣ Daz := Dvd.intro_left _ (primPos_factorization Daz)
  have hqImg_dvd : (intImg q).map (Int.castRingHom ℚ) ∣ MvPolynomial.C (e : ℚ) * d := by
    rw [← hDazImgQ]
    exact map_dvd (MvPolynomial.map (Int.castRingHom ℚ))
      ((map_dvd_iff AzMvPolynomial.ringEquivMvPolynomialInt).mpr hq_dvd_Daz)
  refine ⟨q, hq_prim, ?_, ?_⟩
  · -- `ratImg q` is an associate of `d`: `C(e)·d = C(s)·ratImg q` with both units
    have hfac : MvPolynomial.C (e : ℚ) * d
        = MvPolynomial.C (((signedIntContent Daz).toInt : ℚ))
            * (intImg q).map (Int.castRingHom ℚ) := by
      rw [← hDazImgQ]
      conv_lhs => rw [← primPos_factorization Daz]
      rw [intImg_mul, map_mul, map_intImg_C, ← hqdef]
    have hs0 : ((signedIntContent Daz).toInt : ℚ) ≠ 0 := by
      exact_mod_cast toInt_ne_zero (signedIntContent_ne_zero hDaz0)
    have hCs_unit : IsUnit (MvPolynomial.C (((signedIntContent Daz).toInt : ℚ))
        : MvPolynomial (Fin n) ℚ) := (isUnit_iff_ne_zero.mpr hs0).map MvPolynomial.C
    -- `C(e)·d = C(s)·ratImg q` with both `C(e)`, `C(s)` units, so `ratImg q ~ d`
    rw [ratImg_eq_map_intImg]
    have h1 : Associated (MvPolynomial.C (e : ℚ) * d) d :=
      associated_unit_mul_left d _ hCe_unit
    have h2 : Associated (MvPolynomial.C (e : ℚ) * d) ((intImg q).map (Int.castRingHom ℚ)) := by
      rw [hfac]; exact associated_unit_mul_left _ _ hCs_unit
    exact h2.symm.trans h1
  · intro M hdM
    apply dvd_of_map_intImg_dvd hq_prim
    rw [← ratImg_eq_map_intImg M]
    exact hqImg_dvd.trans ((hCe_unit.mul_left_dvd).mpr hdM)

/-- **`coprime → IsRelPrime`** over `ℚ[x⃗]` — the converse of
`coprime_of_isRelPrime`, i.e. the *hard* multivariate-Gauss direction, closed
by the content-descent above. -/
theorem coprime_isRelPrime {P Q : AzMvPolynomial n AzInt ord}
    (hcop : AzMvPolynomial.coprime P Q = true) :
    IsRelPrime (ratImg P) (ratImg Q) := by
  by_cases hP : P = 0
  · -- `coprime 0 Q` forces `ratImg Q` (hence its unit-associate `gcd`-image) to
    -- be a unit; `IsRelPrime 0 x ↔ IsUnit x`.
    subst hP
    rw [show (ratImg (0 : AzMvPolynomial n AzInt ord)) = 0 by
      rw [ratImg, toMvPoly_zero, map_zero], isRelPrime_zero_left]
    have hg : IsUnit (ratImg (AzMvPolynomial.gcd (0 : AzMvPolynomial n AzInt ord) Q)) :=
      AzMvPolynomial.coprime_iff.mp hcop
    exact isUnit_of_dvd_unit
      (map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
        (map_dvd AzMvPolynomial.toMvPolyHom
          (AzMvPolynomial.dvd_gcd (dvd_zero Q) (dvd_refl Q)))) hg
  rw [ratImg_eq_map_intImg P, ratImg_eq_map_intImg Q,
    UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors (map_intImg_ne_zero hP)]
  intro d hdP hdQ hdprime
  -- descend `d` to a primitive `q ∣ gcd P Q` whose `ℚ`-image is an associate of `d`
  obtain ⟨q, -, hassoc, hdvd⟩ := exists_primitive_preimage (ord := ord) hdprime.ne_zero
  have hq_gcd : q ∣ AzMvPolynomial.gcd P Q :=
    dvd_gcd (hdvd P (ratImg_eq_map_intImg P ▸ hdP)) (hdvd Q (ratImg_eq_map_intImg Q ▸ hdQ))
  -- coprimality: `ratImg (gcd P Q)` is a unit, hence `ratImg q` is, hence `d` is
  have hunit_gcd : IsUnit (ratImg (AzMvPolynomial.gcd P Q)) :=
    AzMvPolynomial.coprime_iff.mp hcop
  have hunit_qImg : IsUnit (ratImg q) :=
    isUnit_of_dvd_unit (map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
      (map_dvd AzMvPolynomial.toMvPolyHom hq_gcd)) hunit_gcd
  exact hdprime.not_isUnit (hassoc.isUnit_iff.mp hunit_qImg)

/-- **The full `coprime ↔ IsRelPrime` characterization** over `ℚ[x⃗]` (for
nonzero `P`), combining `coprime_isRelPrime` (the multivariate-Gauss direction,
above) with `coprime_of_isRelPrime` (the easy direction). -/
theorem coprime_iff_isRelPrime {P Q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.coprime P Q = true ↔ IsRelPrime (ratImg P) (ratImg Q) :=
  ⟨coprime_isRelPrime, coprime_of_isRelPrime⟩

/-! ### Squarefreeness (the reverse direction) -/

/-- Reverse universal property of the `gcd`-fold over a family: a common
divisor of the initial value and every family member divides the fold. -/
private theorem dvd_foldl_gcd_mv (l : List (Fin n))
    (init : AzMvPolynomial n AzInt ord) (f : Fin n → AzMvPolynomial n AzInt ord)
    {d : AzMvPolynomial n AzInt ord} (hi : d ∣ init) (hm : ∀ k, d ∣ f k) :
    d ∣ l.foldl (fun acc k => AzMvPolynomial.gcd acc (f k)) init := by
  induction l generalizing init with
  | nil => exact hi
  | cons a t ih => exact ih _ (AzMvPolynomial.dvd_gcd hi (hm a))

/-- The gradient gcd of `0` is `0`. -/
private theorem squarefreeGradientGcd_zero :
    AzMvPolynomial.squarefreeGradientGcd (0 : AzMvPolynomial n AzInt ord) = 0 := by
  rw [AzMvPolynomial.squarefreeGradientGcd]
  have hz : ∀ l : List (Fin n),
      l.foldl (fun acc j => AzMvPolynomial.gcd acc (AzMvPolynomial.pderivGeneral j 0))
        (0 : AzMvPolynomial n AzInt ord) = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons a t ih =>
      have hz0 : AzMvPolynomial.pderivGeneral a (0 : AzMvPolynomial n AzInt ord) = 0 := by
        apply toMvPoly_injective
        simp only [toMvPoly_pderivGeneral, toMvPoly_zero, _root_.map_zero]
      simp only [List.foldl_cons, hz0, AzMvPolynomial.gcd_zero_zero]
      exact ih
  exact hz _

/-- **The reverse (multivariate-Gauss) direction of squarefreeness**: if `P`
passes the `isSquarefree` test, then its `ℚ[x⃗]`-image is genuinely
`Squarefree`. A repeated prime factor `d` of `ratImg P` also divides every
partial derivative, so (by content-descent) its primitive `ℤ`-part divides the
gradient gcd `g`; but `ratImg g` is a unit — contradiction. -/
theorem squarefree_of_isSquarefree {P : AzMvPolynomial n AzInt ord}
    (h : AzMvPolynomial.isSquarefree P = true) :
    Squarefree (AzMvPolynomial.ratImg P) := by
  by_cases hu : IsUnit (AzMvPolynomial.ratImg P)
  · exact hu.squarefree
  have hgU : IsUnit ((intImg (AzMvPolynomial.squarefreeGradientGcd P)).map (Int.castRingHom ℚ)) := by
    have h1 : IsUnit (AzMvPolynomial.ratImg (AzMvPolynomial.squarefreeGradientGcd P)) :=
      AzMvPolynomial.isSquarefree_iff.mp h
    rw [ratImg_eq_map_intImg] at h1; exact h1
  have hPne : P ≠ 0 := by
    rintro rfl
    simp [AzMvPolynomial.isSquarefree, squarefreeGradientGcd_zero] at h
  have hP0 : AzMvPolynomial.ratImg P ≠ 0 := by
    rw [ratImg_eq_map_intImg]; exact map_intImg_ne_zero hPne
  obtain ⟨w, hw, -⟩ := WfDvdMonoid.exists_irreducible_factor hu hP0
  rw [squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨w, hw⟩]
  intro d hd hsq
  have hdP : d ∣ AzMvPolynomial.ratImg P := (dvd_mul_right d d).trans hsq
  obtain ⟨bb, hbb⟩ := hsq
  have hdD : ∀ j, d ∣ MvPolynomial.pderiv j (AzMvPolynomial.ratImg P) := by
    intro j
    rw [hbb]
    have hpd : MvPolynomial.pderiv j (d * d * bb)
        = d * (MvPolynomial.pderiv j d * bb + MvPolynomial.pderiv j (d * bb)) := by
      rw [show d * d * bb = d * (d * bb) from by ring, Derivation.leibniz]
      simp only [smul_eq_mul]; ring
    rw [hpd]; exact Dvd.intro _ rfl
  -- descend `d` to a primitive `qaz` dividing the gradient gcd; its image is a unit
  obtain ⟨qaz, -, hassoc, hdvd_of⟩ := exists_primitive_preimage (ord := ord) hd.ne_zero
  have hqazg : qaz ∣ AzMvPolynomial.squarefreeGradientGcd P := by
    rw [AzMvPolynomial.squarefreeGradientGcd]
    exact dvd_foldl_gcd_mv _ P _ (hdvd_of P hdP)
      (fun k => hdvd_of _ (by rw [AzMvPolynomial.ratImg_pderivGeneral]; exact hdD k))
  have hgU' : IsUnit (AzMvPolynomial.ratImg (AzMvPolynomial.squarefreeGradientGcd P)) := by
    rw [ratImg_eq_map_intImg]; exact hgU
  have hunit_qImg : IsUnit (AzMvPolynomial.ratImg qaz) :=
    isUnit_of_dvd_unit (map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
      (map_dvd AzMvPolynomial.toMvPolyHom hqazg)) hgU'
  exact hd.prime.not_isUnit (hassoc.isUnit_iff.mp hunit_qImg)

/-- **The full squarefreeness characterization** over `ℚ[x⃗]`: `isSquarefree`
decides genuine `Squarefree`ness of the `ℚ[x⃗]`-image, combining
`isSquarefree_of_squarefree` with `squarefree_of_isSquarefree`. -/
theorem isSquarefree_iff_squarefree {P : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.isSquarefree P = true ↔ Squarefree (AzMvPolynomial.ratImg P) :=
  ⟨squarefree_of_isSquarefree, AzMvPolynomial.isSquarefree_of_squarefree⟩

end Azurite.AzMvPolynomial
