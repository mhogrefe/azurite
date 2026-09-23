/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Equiv.IntContent
import Azurite.AzMvPolynomial.Equiv.Gcd
import Azurite.AzMvPolynomial.Equiv.SMul
import Azurite.AzMvPolynomial.SMul
import Azurite.AzPolynomial.Equiv.Content
import Azurite.AzInt.Equiv.Compare
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Int.Basic

/-!
# Multiplicativity of `intContent` (multivariate Gauss, via reduction mod `p`)

`intContent (P * Q) = intContent P * intContent Q` over `AzMvPolynomial n AzInt ord`,
proved by the textbook reduction-mod-`p` argument — **no** `NormalizedGCDMonoid`
on `MvPolynomial (Fin n) ℤ` is required.

The core bridge (`intContent_dvd_prime_iff`): for a prime `p`,
`p ∣ intContent P ⟺ P vanishes after reduction mod p`, because both say
"`p` divides every coefficient". Gauss (`intContent_mul_primitive`) then
follows from `MvPolynomial (Fin n) (ZMod p)` being a domain.
-/

namespace Azurite.AzMvPolynomial

open scoped Classical

variable {n : ℕ} {ord : MonomialOrder}

/-- The `ℤ`-image of `P` (a `MvPolynomial (Fin n) ℤ`). -/
noncomputable def intImg (P : AzMvPolynomial n AzInt ord) : MvPolynomial (Fin n) ℤ :=
  ringEquivMvPolynomialInt P

theorem intImg_mul (P Q : AzMvPolynomial n AzInt ord) :
    intImg (P * Q) = intImg P * intImg Q :=
  map_mul _ _ _

/-! ### `intContent` as a `Nat.gcd` fold -/

/-- `intContent` descends to a `Nat.gcd` fold over the coefficient
magnitudes. -/
theorem toNat_intContent (P : AzMvPolynomial n AzInt ord) :
    (intContent P).toNat
      = (P.terms.toList.map (fun m => m.coeff.val.abs.toNat)).foldl Nat.gcd 0 := by
  rw [intContent, ← Array.foldl_toList]
  have aux : ∀ (l : List (Monomial n AzInt ord)) (acc : AzNat),
      (l.foldl (fun acc m => AzNat.gcd acc m.coeff.val.abs) acc).toNat
        = (l.map (fun m => m.coeff.val.abs.toNat)).foldl Nat.gcd acc.toNat := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons m l ih =>
      intro acc
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, Azurite.AzNat.toNat_gcd]
  rw [aux]; rfl

/-- `p` divides the content iff it divides every term-coefficient
magnitude. -/
theorem prime_dvd_intContent_iff {p : ℕ} (P : AzMvPolynomial n AzInt ord) :
    p ∣ (intContent P).toNat
      ↔ ∀ m ∈ P.terms.toList, p ∣ m.coeff.val.abs.toNat := by
  rw [toNat_intContent]
  set l := P.terms.toList.map (fun m => m.coeff.val.abs.toNat) with hl
  constructor
  · intro hd m hm
    refine hd.trans (Azurite.AzPolynomial.foldl_gcd_dvd_mem l 0 ?_)
    rw [hl]; exact List.mem_map_of_mem hm
  · intro h
    apply Azurite.AzPolynomial.dvd_foldl_gcd l 0 (dvd_zero _)
    intro a ha
    rw [hl, List.mem_map] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    exact h m hm

/-! ### The coefficient bridge -/

/-- `intImg`'s coefficient is the `ℤ`-cast of the represented coefficient. -/
theorem coeff_intImg (P : AzMvPolynomial n AzInt ord) (f : Fin n →₀ ℕ) :
    (intImg P).coeff f = (P.toMvPoly.coeff f).toInt := by
  rw [intImg, ringEquivMvPolynomialInt_apply, MvPolynomial.coeff_map]
  rfl

/-- The coefficient of a term's monic part is the term coefficient. -/
theorem coeff_toMvPoly_of_mem {P : AzMvPolynomial n AzInt ord}
    {m : Monomial n AzInt ord} (hm : m ∈ P.terms.toList) :
    P.toMvPoly.coeff m.monic.toFinsupp = m.coeff.val := by
  rw [coeff_toMvPoly]
  exact list_sum_ite_eq_of_nodup_map _ _ (toFinsupp_nodup P) m hm (fun m => m.coeff.val)

/-- **`p` divides the content iff it divides every coefficient of the
`ℤ`-image.** -/
theorem prime_dvd_intContent_iff_coeff {p : ℕ} (P : AzMvPolynomial n AzInt ord) :
    p ∣ (intContent P).toNat ↔ ∀ f, (p : ℤ) ∣ (intImg P).coeff f := by
  rw [prime_dvd_intContent_iff]
  constructor
  · intro h f
    rw [coeff_intImg]
    by_cases hz : P.toMvPoly.coeff f = 0
    · rw [hz]; simp
    · have hmem : f ∈ P.toMvPoly.support := MvPolynomial.mem_support_iff.mpr hz
      rw [support_toMvPoly, List.mem_toFinset, List.mem_map] at hmem
      obtain ⟨m, hm, rfl⟩ := hmem
      rw [coeff_toMvPoly_of_mem hm]
      have := h m hm
      rw [← Azurite.AzInt.toNat_abs] at this
      exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr this)
  · intro h m hm
    have hf := h m.monic.toFinsupp
    rw [coeff_intImg, coeff_toMvPoly_of_mem hm] at hf
    rw [← Azurite.AzInt.toNat_abs]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hf)

/-! ### Reduction mod `p` -/

/-- Reduction of a `MvPolynomial (Fin n) ℤ` modulo `p`. -/
noncomputable def redp (p : ℕ) (Q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin n) (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p)) Q

theorem redp_mul (p : ℕ) (A B : MvPolynomial (Fin n) ℤ) :
    redp p (A * B) = redp p A * redp p B :=
  map_mul _ _ _

/-- `redp p Q = 0` iff `p` divides every coefficient of `Q`. -/
theorem redp_eq_zero_iff {p : ℕ} (Q : MvPolynomial (Fin n) ℤ) :
    redp p Q = 0 ↔ ∀ f, (p : ℤ) ∣ Q.coeff f := by
  rw [redp, MvPolynomial.ext_iff]
  refine forall_congr' (fun f => ?_)
  rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- **The core bridge (content ↔ vanishing mod `p`).** -/
theorem intContent_dvd_prime_iff {p : ℕ} (P : AzMvPolynomial n AzInt ord) :
    p ∣ (intContent P).toNat ↔ redp p (intImg P) = 0 := by
  rw [prime_dvd_intContent_iff_coeff, redp_eq_zero_iff]

/-! ### Primitivity ↔ nonvanishing mod every prime -/

theorem intContent_toNat_eq_one_iff (P : AzMvPolynomial n AzInt ord) :
    (intContent P).toNat = 1 ↔ ∀ p : ℕ, p.Prime → redp p (intImg P) ≠ 0 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  refine forall_congr' (fun p => imp_congr_right (fun _ => ?_))
  exact not_iff_not.mpr (intContent_dvd_prime_iff P)

theorem intContent_eq_one_iff (P : AzMvPolynomial n AzInt ord) :
    intContent P = 1 ↔ ∀ p : ℕ, p.Prime → redp p (intImg P) ≠ 0 := by
  rw [← intContent_toNat_eq_one_iff]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Azurite.AzNat.toNat_injective (by rw [h]; rfl)

/-! ### Gauss's lemma: product of primitives is primitive -/

/-- `P * Q ≠ 0` when both are nonzero (domain). -/
theorem mul_ne_zero_of {P Q : AzMvPolynomial n AzInt ord} (hP : P ≠ 0)
    (hQ : Q ≠ 0) : P * Q ≠ 0 := by
  intro h
  have h0 : toMvPoly (P * Q) = 0 := by rw [h, toMvPoly_zero]
  rw [toMvPoly_mul] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hP (toMvPoly_injective (by rw [h1, toMvPoly_zero]))
  · exact hQ (toMvPoly_injective (by rw [h1, toMvPoly_zero]))

/-- **Gauss's lemma.** The product of primitive polynomials is primitive. -/
theorem intContent_mul_primitive {P Q : AzMvPolynomial n AzInt ord}
    (hP : intContent P = 1) (hQ : intContent Q = 1) :
    intContent (P * Q) = 1 := by
  rw [intContent_eq_one_iff] at hP hQ ⊢
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  rw [intImg_mul, redp_mul]
  exact mul_ne_zero (hP p hp) (hQ p hp)

/-! ### Content scaling and the full multiplicativity -/

/-- Multiplication by a constant is scalar multiplication. -/
theorem C_mul_eq_smul (k : AzInt) (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.C k * P = k • P := by
  apply toMvPoly_injective
  rw [toMvPoly_mul, toMvPoly_C, toMvPoly_smul, MvPolynomial.smul_eq_C_mul]

private theorem abs_toNat_mul (k c : AzInt) :
    (k * c).abs.toNat = k.abs.toNat * c.abs.toNat := by
  rw [← Azurite.AzInt.toNat_abs, ← Azurite.AzInt.toNat_abs, ← Azurite.AzInt.toNat_abs,
    Azurite.AzInt.toInt_mul, Int.natAbs_mul]

private theorem smulMonomial_eq_some {k : AzInt} (hk : k ≠ 0)
    (m : Monomial n AzInt ord) :
    Azurite.smulMonomial k m
      = some ⟨⟨k * m.coeff.val, mul_ne_zero hk m.coeff.property⟩, m.monic⟩ := by
  unfold Azurite.smulMonomial
  rw [dite_eq_right (mul_ne_zero hk m.coeff.property)]

private theorem filterMap_smul_coeff_map {k : AzInt} (hk : k ≠ 0)
    (l : List (Monomial n AzInt ord)) :
    (l.filterMap (Azurite.smulMonomial k)).map (fun m => m.coeff.val.abs.toNat)
      = l.map (fun m => k.abs.toNat * m.coeff.val.abs.toNat) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [List.filterMap_cons_some (smulMonomial_eq_some hk m), List.map_cons,
      List.map_cons, ih]
    congr 1
    exact abs_toNat_mul k m.coeff.val

private theorem foldl_gcd_scale (a : ℕ) (L : List ℕ) :
    (L.map (fun x => a * x)).foldl Nat.gcd 0 = a * L.foldl Nat.gcd 0 := by
  have gen : ∀ acc, (L.map (fun x => a * x)).foldl Nat.gcd (a * acc)
      = a * L.foldl Nat.gcd acc := by
    intro acc
    induction L generalizing acc with
    | nil => rfl
    | cons x l ih =>
      simp only [List.map_cons, List.foldl_cons, Nat.gcd_mul_left]
      exact ih (Nat.gcd acc x)
  have := gen 0
  rwa [Nat.mul_zero] at this

/-- **Content scaling.** `intContent (C k * P) = |k| · intContent P`. -/
theorem intContent_C_mul (k : AzInt) (P : AzMvPolynomial n AzInt ord) :
    intContent (AzMvPolynomial.C k * P) = k.abs * intContent P := by
  by_cases hk : k = 0
  · subst hk
    have hC0 : (AzMvPolynomial.C (0 : AzInt) : AzMvPolynomial n AzInt ord) = 0 := by
      apply toMvPoly_injective; rw [toMvPoly_C, toMvPoly_zero, map_zero]
    rw [hC0, zero_mul, show (0 : AzInt).abs = 0 from rfl, zero_mul]
    rfl
  · apply Azurite.AzNat.toNat_injective
    rw [Azurite.AzNat.toNat_mul, toNat_intContent, C_mul_eq_smul, toNat_intContent]
    have hterms : (AzMvPolynomial.smul k P).terms.toList
        = P.terms.toList.filterMap (Azurite.smulMonomial k) := by
      unfold AzMvPolynomial.smul; rw [List.toList_toArray]
    show ((AzMvPolynomial.smul k P).terms.toList.map _).foldl Nat.gcd 0 = _
    rw [hterms, filterMap_smul_coeff_map hk,
      show (fun m : Monomial n AzInt ord => k.abs.toNat * m.coeff.val.abs.toNat)
        = (fun x => k.abs.toNat * x) ∘ (fun m => m.coeff.val.abs.toNat) from rfl,
      ← List.map_map, foldl_gcd_scale]

private theorem AzInt_abs_neg (z : AzInt) : (-z).abs = z.abs := by
  show (Azurite.AzInt.neg z).abs = z.abs
  unfold Azurite.AzInt.neg Azurite.AzInt.mkNorm
  split <;> simp_all

private theorem AzInt_abs_mul (a b : AzInt) : (a * b).abs = a.abs * b.abs :=
  Azurite.AzNat.toNat_injective (by rw [abs_toNat_mul, Azurite.AzNat.toNat_mul])

/-- `|signedIntContent P| = intContent P`. -/
theorem abs_signedIntContent (P : AzMvPolynomial n AzInt ord) :
    (signedIntContent P).abs = intContent P := by
  rw [signedIntContent]
  split
  · rfl
  · rw [AzInt_abs_neg]; rfl

/-! ### `primPos` factorization -/

private theorem sic_toInt_natAbs (P : AzMvPolynomial n AzInt ord) :
    (signedIntContent P).toInt.natAbs = (intContent P).toNat := by
  rw [Azurite.AzInt.toNat_abs, abs_signedIntContent]

/-- The signed content divides every term coefficient. -/
theorem sic_dvd_coeff {P : AzMvPolynomial n AzInt ord} {m : Monomial n AzInt ord}
    (hm : m ∈ P.terms.toList) : signedIntContent P ∣ m.coeff.val := by
  apply (map_dvd_iff Azurite.AzInt.ringEquivInt).mp
  show (signedIntContent P).toInt ∣ (m.coeff.val).toInt
  rw [← Int.natAbs_dvd, sic_toInt_natAbs, ← Int.dvd_natAbs, Int.natCast_dvd_natCast,
    Azurite.AzInt.toNat_abs, toNat_intContent]
  exact Azurite.AzPolynomial.foldl_gcd_dvd_mem _ 0 (List.mem_map_of_mem hm)

/-- `C (signedIntContent P)` divides `P`. -/
theorem C_sic_dvd (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.C (signedIntContent P) ∣ P := by
  rw [← map_dvd_iff (Azurite.ringEquivMvPolynomial (R := AzInt) (n := n) (ord := ord))]
  show toMvPoly (AzMvPolynomial.C (signedIntContent P)) ∣ toMvPoly P
  rw [toMvPoly_C, MvPolynomial.C_dvd_iff_dvd_coeff]
  intro f
  by_cases hz : P.toMvPoly.coeff f = 0
  · rw [hz]; exact dvd_zero _
  · have hmem : f ∈ P.toMvPoly.support := MvPolynomial.mem_support_iff.mpr hz
    rw [support_toMvPoly, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨m, hm, rfl⟩ := hmem
    rw [coeff_toMvPoly_of_mem hm]
    exact sic_dvd_coeff hm

/-- The content of a nonzero polynomial is nonzero. -/
theorem intContent_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    intContent P ≠ 0 := by
  intro h
  have hne : P.terms.toList ≠ [] :=
    List.ne_nil_of_length_pos (by rw [Array.length_toList]; exact size_pos_of_ne_zero hP)
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
  have hdvd : (intContent P).toNat ∣ m.coeff.val.abs.toNat := by
    rw [toNat_intContent]
    exact Azurite.AzPolynomial.foldl_gcd_dvd_mem _ 0 (List.mem_map_of_mem hm)
  rw [h] at hdvd
  have hz : m.coeff.val.abs.toNat = 0 := Nat.eq_zero_of_zero_dvd (by simpa using hdvd)
  rw [← Azurite.AzInt.toNat_abs, Int.natAbs_eq_zero] at hz
  exact m.coeff.property (Azurite.AzInt.ringEquivInt.injective (by rw [map_zero]; exact hz))

/-- **Factorization** `P = C (signedIntContent P) * primPos P`. -/
theorem primPos_factorization (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.C (signedIntContent P) * primPos P = P := by
  by_cases hP : P = 0
  · subst hP
    have h0 : signedIntContent (0 : AzMvPolynomial n AzInt ord) = 0 := by
      rw [signedIntContent]; split <;> rfl
    have hC0 : (AzMvPolynomial.C (0 : AzInt) : AzMvPolynomial n AzInt ord) = 0 := by
      apply toMvPoly_injective; rw [toMvPoly_C, toMvPoly_zero, map_zero]
    rw [h0, hC0, zero_mul]
  · have hsicne : signedIntContent P ≠ 0 := by
      intro h; apply intContent_ne_zero hP
      rw [← abs_signedIntContent, h]; rfl
    have hCne : (AzMvPolynomial.C (signedIntContent P) : AzMvPolynomial n AzInt ord) ≠ 0 := by
      intro h; apply hsicne
      have hh := congrArg toMvPoly h
      rw [toMvPoly_C, toMvPoly_zero] at hh
      exact MvPolynomial.C_eq_zero.mp hh
    have hfac := Azurite.ExactDiv.exactDiv_mul_self P
      (AzMvPolynomial.C (signedIntContent P)) (C_sic_dvd P) hCne
    show AzMvPolynomial.C (signedIntContent P)
        * Azurite.ExactDiv.exactDiv P (AzMvPolynomial.C (signedIntContent P)) = P
    rw [mul_comm]; exact hfac

/-- The signed content of a nonzero polynomial is nonzero. -/
theorem signedIntContent_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    signedIntContent P ≠ 0 := by
  intro h; apply intContent_ne_zero hP; rw [← abs_signedIntContent, h]; rfl

/-- `primPos P` is nonzero for nonzero `P`. -/
theorem primPos_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) : primPos P ≠ 0 :=
  fun h => hP (by rw [← primPos_factorization P, h, mul_zero])

/-- **`primPos P` is primitive** for nonzero `P` (`intContent = 1`). -/
theorem intContent_primPos {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    intContent (primPos P) = 1 := by
  have hfac := intContent_C_mul (signedIntContent P) (primPos P)
  rw [primPos_factorization P, abs_signedIntContent] at hfac
  apply Azurite.AzNat.toNat_injective
  have hn : (intContent P).toNat ≠ 0 :=
    fun hz => intContent_ne_zero hP (Azurite.AzNat.toNat_injective (by rw [hz]; rfl))
  have h2 : (intContent P).toNat * 1 = (intContent P).toNat * (intContent (primPos P)).toNat := by
    rw [mul_one, ← Azurite.AzNat.toNat_mul, ← hfac]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) h2).symm

/-- **A divisor of a primitive polynomial is primitive.** (No full `intContent_mul`
needed — pure reduction-mod-`p`.) -/
theorem intContent_eq_one_of_dvd {N M : AzMvPolynomial n AzInt ord}
    (hdvd : N ∣ M) (hM : intContent M = 1) : intContent N = 1 := by
  rw [intContent_eq_one_iff] at hM ⊢
  intro p hp
  have himg : intImg N ∣ intImg M := by
    obtain ⟨K, hK⟩ := hdvd; exact ⟨intImg K, by rw [hK, intImg_mul]⟩
  have hr : redp p (intImg N) ∣ redp p (intImg M) := by
    obtain ⟨K, hK⟩ := himg; exact ⟨redp p K, by rw [hK, redp_mul]⟩
  intro h0
  rw [h0] at hr
  exact hM p hp (zero_dvd_iff.mp hr)

/-- **The exact quotient by a divisor of a primitive is primitive.** Directly
gives the `intContent = 1` obligations for the `ofNumDen` cofactors. -/
theorem intContent_exactDiv_eq_one {M g : AzMvPolynomial n AzInt ord}
    (hdvd : g ∣ M) (hg : g ≠ 0) (hM : intContent M = 1) :
    intContent (Azurite.ExactDiv.exactDiv M g) = 1 :=
  intContent_eq_one_of_dvd
    ⟨g, (Azurite.ExactDiv.exactDiv_mul_self M g hdvd hg).symm⟩ hM

/-- **`intContent` is multiplicative.** (`intContent 0 = 0` trivializes the
zero cases.) -/
theorem intContent_mul {P Q : AzMvPolynomial n AzInt ord} :
    intContent (P * Q) = intContent P * intContent Q := by
  by_cases hP : P = 0
  · rw [hP, zero_mul, show intContent (0 : AzMvPolynomial n AzInt ord) = 0 from rfl,
      zero_mul]
  by_cases hQ : Q = 0
  · rw [hQ, mul_zero, show intContent (0 : AzMvPolynomial n AzInt ord) = 0 from rfl,
      mul_zero]
  have hppP := intContent_primPos hP
  have hppQ := intContent_primPos hQ
  -- factor the product
  have hfacP := primPos_factorization P
  have hfacQ := primPos_factorization Q
  calc intContent (P * Q)
      = intContent (AzMvPolynomial.C (signedIntContent P) * primPos P
          * (AzMvPolynomial.C (signedIntContent Q) * primPos Q)) := by
        congr 1; rw [hfacP, hfacQ]
    _ = intContent (AzMvPolynomial.C (signedIntContent P * signedIntContent Q)
          * (primPos P * primPos Q)) := by
        congr 1
        rw [show AzMvPolynomial.C (signedIntContent P * signedIntContent Q)
            = AzMvPolynomial.C (signedIntContent P) * AzMvPolynomial.C (signedIntContent Q) by
          apply toMvPoly_injective
          rw [toMvPoly_mul, toMvPoly_C, toMvPoly_C, toMvPoly_C, map_mul]]
        ring
    _ = (signedIntContent P * signedIntContent Q).abs
          * intContent (primPos P * primPos Q) := intContent_C_mul _ _
    _ = (signedIntContent P * signedIntContent Q).abs := by
        rw [intContent_mul_primitive hppP hppQ, mul_one]
    _ = intContent P * intContent Q := by
        rw [AzInt_abs_mul, abs_signedIntContent, abs_signedIntContent]

/-! ### Positive leading coefficient of the primitive part -/

/-- The leading coefficient of a nonzero polynomial is nonzero. -/
theorem leadingCoeff_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    leadingCoeff P ≠ 0 := by
  rw [← leadingCoeff_toMvPoly hP, Azurite.leadingCoeff_eq_terms_zero P (size_pos_of_ne_zero hP)]
  exact (P.terms[0]'(size_pos_of_ne_zero hP)).coeff.property

/-- The leading coefficient of a nonzero constant is that constant. -/
theorem leadingCoeff_C {c : AzInt} (hc : c ≠ 0) :
    leadingCoeff (AzMvPolynomial.C c : AzMvPolynomial n AzInt ord) = c := by
  rw [show (AzMvPolynomial.C c : AzMvPolynomial n AzInt ord)
      = ofMonomial ⟨⟨c, hc⟩, MonicMonomial.one⟩ from by unfold AzMvPolynomial.C; exact dite_eq_right hc]
  rfl

private theorem toAzInt_pos {m : AzNat} (hm : m ≠ 0) : (0 : AzInt) < m.toAzInt := by
  rw [Azurite.AzInt.lt_iff_toInt_lt]
  show (0 : ℤ) < (m.toNat : ℤ)
  exact_mod_cast Nat.pos_of_ne_zero
    (fun h => hm (Azurite.AzNat.toNat_injective (by rw [h]; rfl)))

/-- **`primPos P` has positive leading coefficient** for nonzero `P`. -/
theorem leadingCoeff_primPos_pos {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    0 < leadingCoeff (primPos P) := by
  have hpp : primPos P ≠ 0 := fun h => hP (by rw [← primPos_factorization P, h, mul_zero])
  have hCsic : (AzMvPolynomial.C (signedIntContent P) : AzMvPolynomial n AzInt ord) ≠ 0 := by
    intro h; apply signedIntContent_ne_zero hP
    have hh := congrArg toMvPoly h; rw [toMvPoly_C, toMvPoly_zero] at hh
    exact MvPolynomial.C_eq_zero.mp hh
  have hlc : leadingCoeff P = signedIntContent P * leadingCoeff (primPos P) := by
    conv_lhs => rw [← primPos_factorization P]
    rw [leadingCoeff_mul hCsic hpp, leadingCoeff_C (signedIntContent_ne_zero hP)]
  by_cases hsign : (0 : AzInt) < leadingCoeff P
  · have hsicpos : 0 < signedIntContent P := by
      rw [signedIntContent, ite_eq_left hsign]; exact toAzInt_pos (intContent_ne_zero hP)
    rw [hlc] at hsign
    exact (pos_iff_pos_of_mul_pos hsign).mp hsicpos
  · have hlcneg : leadingCoeff P < 0 :=
      lt_of_le_of_ne (not_lt.mp hsign) (leadingCoeff_ne_zero hP)
    have hsicneg : signedIntContent P < 0 := by
      rw [signedIntContent, ite_eq_right hsign]
      exact neg_neg_of_pos (toAzInt_pos (intContent_ne_zero hP))
    have h1 : 0 < -leadingCoeff P := neg_pos.mpr hlcneg
    rw [hlc, ← neg_mul] at h1
    exact (pos_iff_pos_of_mul_pos h1).mp (neg_pos.mpr hsicneg)

end Azurite.AzMvPolynomial
