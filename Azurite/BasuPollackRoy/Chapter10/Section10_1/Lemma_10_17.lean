/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_16
import Mathlib.RingTheory.Localization.Integral

/-!
# BPR Lemma 10.17: rational factorizations of integer polynomials descend

`lemma_10_17`: if `P ∈ ℤ[X]` factors as `P = P₁·P₂` with `P₁, P₂ ∈ ℚ[X]`,
there exist `Q₁, Q₂ ∈ ℤ[X]`, proportional to `P₁` and `P₂` respectively,
with `Q₁·Q₂ = P`.

BPR's proof: take `Q₁ ∈ ℤ[X]` proportional to `P₁` with `cont(Q₁) = 1`; let
`c` be the lcm of the denominators of the complementary factor `P/Q₁` and
`d` the content of the cleared polynomial; Gauss's Lemma 10.16 forces
`c = 1`, so the complementary factor is already integral.

The formalization: clear denominators of `P₁` with
`IsLocalization.integerNormalization` and take the primitive part (`Q₁`,
content one); clear denominators of the complementary rational factor `R₂`
by `b₂`, giving the integer identity `C b₂ · P = Q₁ · B₂`; contents
(`content_mul`, the multiplicative Gauss lemma) give
`cont(B₂) = |b₂|·cont(P)`, so `b₂` divides every coefficient of `B₂` and
`Q₂ := B₂/b₂ ∈ ℤ[X]` — the book's coprimality argument packaged as a single
divisibility.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Lemma 10.17.** A factorization of `P ∈ ℤ[X]` over `ℚ` is realized
over `ℤ` by polynomials proportional to the rational factors. -/
theorem lemma_10_17 {P : ℤ[X]} {P₁ P₂ : ℚ[X]} (hP : P ≠ 0)
    (hfac : P.map (Int.castRingHom ℚ) = P₁ * P₂) :
    ∃ (Q₁ Q₂ : ℤ[X]) (c₁ c₂ : ℚ), c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      Q₁.map (Int.castRingHom ℚ) = C c₁ * P₁ ∧
      Q₂.map (Int.castRingHom ℚ) = C c₂ * P₂ ∧ Q₁ * Q₂ = P := by
  classical
  have hcast : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hmap0 : P.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hcast).mpr hP
  have h₁0 : P₁ ≠ 0 := fun h => hmap0 (by rw [hfac, h, zero_mul])
  have halg : algebraMap ℤ ℚ = Int.castRingHom ℚ := algebraMap_int_eq ℚ
  -- Step 1: a primitive integer polynomial proportional to `P₁`
  obtain ⟨b₁, hb₁M, hb₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P₁
  set B₁ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P₁ with hB₁def
  have hb₁0 : b₁ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₁M
  have hb₁Q0 : (b₁ : ℚ) ≠ 0 := by exact_mod_cast hb₁0
  rw [halg] at hb₁
  replace hb₁ : B₁.map (Int.castRingHom ℚ) = C (b₁ : ℚ) * P₁ := by
    rw [hb₁]
    ext n
    simp [zsmul_eq_mul]
  have hB₁0 : B₁ ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hb₁
    exact h₁0 ((mul_eq_zero.mp hb₁.symm).resolve_left (Polynomial.C_ne_zero.mpr hb₁Q0))
  set A₁ := B₁.primPart with hA₁def
  have hA₁cont : A₁.content = 1 := B₁.content_primPart
  have hcontB₁0 : ((B₁.content : ℤ) : ℚ) ≠ 0 := by
    have h := Polynomial.content_eq_zero_iff.not.mpr hB₁0
    exact_mod_cast h
  set c₁ : ℚ := (b₁ : ℚ) / ((B₁.content : ℤ) : ℚ) with hc₁def
  have hc₁0 : c₁ ≠ 0 := div_ne_zero hb₁Q0 hcontB₁0
  have hA₁map : A₁.map (Int.castRingHom ℚ) = C c₁ * P₁ := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hcontB₁0)
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) B₁.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, Polynomial.map_C,
      show (Int.castRingHom ℚ) B₁.content = ((B₁.content : ℤ) : ℚ) from rfl, hb₁] at h
    calc C ((B₁.content : ℤ) : ℚ) * A₁.map (Int.castRingHom ℚ)
        = C (b₁ : ℚ) * P₁ := h.symm
      _ = C ((B₁.content : ℤ) : ℚ) * (C c₁ * P₁) := by
          rw [← mul_assoc, ← Polynomial.C_mul, hc₁def, mul_comm ((B₁.content : ℤ) : ℚ),
            div_mul_cancel₀ _ hcontB₁0]
  -- Step 2: the complementary rational factor
  set R₂ : ℚ[X] := C c₁⁻¹ * P₂ with hR₂def
  have hfac' : P.map (Int.castRingHom ℚ) = A₁.map (Int.castRingHom ℚ) * R₂ := by
    rw [hfac, hA₁map, hR₂def]
    have hCc : C c₁ * C c₁⁻¹ = (1 : ℚ[X]) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc₁0, Polynomial.C_1]
    calc P₁ * P₂ = (C c₁ * C c₁⁻¹) * (P₁ * P₂) := by rw [hCc, one_mul]
      _ = C c₁ * P₁ * (C c₁⁻¹ * P₂) := by ring
  -- Step 3: clear denominators of the complementary factor
  obtain ⟨b₂, hb₂M, hb₂⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) R₂
  set B₂ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) R₂ with hB₂def
  have hb₂0 : b₂ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₂M
  have hb₂Q0 : (b₂ : ℚ) ≠ 0 := by exact_mod_cast hb₂0
  rw [halg] at hb₂
  replace hb₂ : B₂.map (Int.castRingHom ℚ) = C (b₂ : ℚ) * R₂ := by
    rw [hb₂]
    ext n
    simp [zsmul_eq_mul]
  -- the integer identity `b₂·P = A₁·B₂`
  have hZ : C b₂ * P = A₁ * B₂ := by
    apply Polynomial.map_injective _ hcast
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, hb₂, hfac']
    show C ((b₂ : ℤ) : ℚ) * _ = _
    ring
  -- contents: Gauss's lemma forces `b₂ ∣ cont(B₂)`
  have hcont : B₂.content = normalize b₂ * P.content := by
    have h := congrArg Polynomial.content hZ
    rw [Polynomial.content_C_mul, Polynomial.content_mul, hA₁cont, one_mul] at h
    exact h.symm
  have hb₂dvd : C b₂ ∣ B₂ := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have h1 : b₂ ∣ B₂.content := by
      rw [hcont]
      exact Dvd.dvd.mul_right (by
        rw [← Int.abs_eq_normalize]
        exact self_dvd_abs b₂) _
    exact dvd_trans h1 (B₂.content_dvd_coeff i)
  obtain ⟨A₂, hA₂⟩ := hb₂dvd
  -- assembly
  have hPQQ : A₁ * A₂ = P := by
    apply mul_left_cancel₀ (show (C b₂ : ℤ[X]) ≠ 0 from Polynomial.C_ne_zero.mpr hb₂0)
    rw [hZ, hA₂]
    ring
  have hA₂map : A₂.map (Int.castRingHom ℚ) = C c₁⁻¹ * P₂ := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) hA₂
    rw [Polynomial.map_mul, Polynomial.map_C, hb₂] at h
    have h2 := mul_left_cancel₀ (Polynomial.C_ne_zero.mpr
      (show ((b₂ : ℤ) : ℚ) ≠ 0 from hb₂Q0)) h
    rw [← h2, hR₂def]
  exact ⟨A₁, A₂, c₁, c₁⁻¹, hc₁0, inv_ne_zero hc₁0, hA₁map, hA₂map, hPQQ⟩

end Azurite.BPR
