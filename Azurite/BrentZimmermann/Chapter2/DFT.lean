/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Brent–Zimmermann §2.3.1: the discrete Fourier transform over a ring

The theoretical setting of the fast Fourier transform in *Modern Computer Arithmetic* (MCA),
§2.3.1, over an arbitrary commutative ring `R`.  The transform is defined with respect to a
**principal** `K`-th root of unity `ω`: `ω^K = 1` and `∑_{j<K} ω^{ij} = 0` for `0 < i < K`.  In a
domain that is the same as a primitive root, but the Schönhage–Strassen algorithm (§2.3.3) works
in `ℤ/(2^N + 1)`, which has zero divisors, and there the vanishing sums are exactly what makes
the transform invertible.

* `IsPrincipalRoot ω K` — the definition, with `IsPrincipalRoot.sum_pow_mul` (the geometric sums
  `∑_{j<K} ω^{mj}` are `K` when `K ∣ m` and `0` otherwise) and `IsPrincipalRoot.inv`
  (`ω^(K−1)`, the inverse of `ω`, is again principal).
* `dft ω a` — the forward transform (2.1), `â_i = ∑_j ω^{ij} a_j`, on vectors `Fin K → R`.
* `dft_dft` — transforming twice gives `K · [a_0, a_{K−1}, a_{K−2}, …, a_1]`.
* `dftInv ω a` — the backward transform, the forward transform at `ω^(K−1)`; `dftInv_dft` says
  that up to the factor `K` it inverts `dft`.

Mathlib's `ZMod.dft` is the complex-valued transform of `Mathlib.Analysis.Fourier.ZMod`; the
integer-multiplication algorithm needs the ring-generic one.
-/

namespace Azurite

namespace BZ

open Finset

variable {R : Type*} [CommRing R]

/-- `ω` is a principal `K`-th root of unity in `R` (MCA §2.3.1): `ω^K = 1` and
`∑_{j<K} ω^{ij} = 0` for every `0 < i < K`. -/
structure IsPrincipalRoot (ω : R) (K : ℕ) : Prop where
  pow_eq_one : ω ^ K = 1
  sum_pow_eq_zero : ∀ i, 0 < i → i < K → ∑ j ∈ range K, ω ^ (i * j) = 0

/-- `(K − 1)·i + i = K·i` for `0 < K`. -/
private lemma sub_one_mul_add (K i : ℕ) (hK : 0 < K) : (K - 1) * i + i = K * i := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_mul]

namespace IsPrincipalRoot

variable {ω : R} {K : ℕ}

/-- `ω^m` depends only on `m mod K`. -/
theorem pow_mod (h : IsPrincipalRoot ω K) (m : ℕ) : ω ^ m = ω ^ (m % K) :=
  pow_eq_pow_mod m h.pow_eq_one

/-- The geometric sums of a principal root: `∑_{j<K} ω^{mj}` is `K` when `K ∣ m` and `0`
otherwise. -/
theorem sum_pow_mul (h : IsPrincipalRoot ω K) (m : ℕ) :
    ∑ j ∈ range K, ω ^ (m * j) = if m % K = 0 then (K : R) else 0 := by
  have hterm : ∀ j, ω ^ (m * j) = ω ^ ((m % K) * j) := fun j => by
    rw [pow_mul, h.pow_mod m, ← pow_mul]
  simp_rw [hterm]
  split_ifs with h0
  · simp [h0]
  · rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · exact h.sum_pow_eq_zero (m % K) (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ hK)

/-- `ω^(K−1)`, the inverse of `ω`, is again a principal `K`-th root of unity. -/
theorem inv (h : IsPrincipalRoot ω K) : IsPrincipalRoot (ω ^ (K - 1)) K where
  pow_eq_one := by rw [← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]
  sum_pow_eq_zero := by
    intro i hi hiK
    have hterm : ∀ j, (ω ^ (K - 1)) ^ (i * j) = ω ^ (((K - 1) * i) * j) := fun j => by
      rw [← pow_mul, Nat.mul_assoc]
    simp_rw [hterm]
    rw [h.sum_pow_mul, ite_eq_right]
    intro h0
    have h1 : ((K - 1) * i + i) % K = i := by
      rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hiK]
    rw [sub_one_mul_add K i (by omega), Nat.mul_mod_right] at h1
    omega

end IsPrincipalRoot

/-- The discrete Fourier transform (MCA (2.1)) of `a = [a_0, …, a_{K−1}]` at `ω`:
`â_i = ∑_j ω^{ij} a_j`. -/
def dft (ω : R) {K : ℕ} (a : Fin K → R) : Fin K → R :=
  fun i => ∑ j : Fin K, ω ^ (i.val * j.val) * a j

/-- The backward transform: the forward transform at `ω⁻¹ = ω^(K−1)`. -/
def dftInv (ω : R) {K : ℕ} (a : Fin K → R) : Fin K → R :=
  dft (ω ^ (K - 1)) a

/-- Two forward transforms give `K` times the vector with indices negated (MCA §2.3.1). -/
theorem dft_dft_apply {ω : R} {K : ℕ} [NeZero K] (h : IsPrincipalRoot ω K) (a : Fin K → R)
    (i : Fin K) : dft ω (dft ω a) i = (K : R) * a (-i) := by
  unfold dft
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ (ℓ j : Fin K), ω ^ (i.val * j.val) * (ω ^ (j.val * ℓ.val) * a ℓ)
      = ω ^ ((i.val + ℓ.val) * j.val) * a ℓ := fun ℓ j => by
    rw [← mul_assoc, ← pow_add, Nat.add_mul, Nat.mul_comm j.val ℓ.val]
  simp_rw [hterm, ← Finset.sum_mul]
  have hsum : ∀ ℓ : Fin K, ∑ j : Fin K, ω ^ ((i.val + ℓ.val) * j.val)
      = if (i.val + ℓ.val) % K = 0 then (K : R) else 0 := fun ℓ => by
    rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ ((i.val + ℓ.val) * j)), h.sum_pow_mul]
  simp_rw [hsum]
  have key : ∀ b : Fin K, (i.val + b.val) % K = 0 ↔ b = -i := fun b => by
    rw [← Fin.val_add, eq_neg_iff_add_eq_zero, add_comm b i, Fin.ext_iff, Fin.val_zero]
  rw [Finset.sum_eq_single (-i)]
  · rw [ite_eq_left ((key _).mpr rfl)]
  · intro b _ hb
    rw [ite_eq_right (fun h0 => hb ((key b).mp h0)), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- `dft ω (dft ω a) = K · [a_0, a_{K−1}, a_{K−2}, …, a_1]`. -/
theorem dft_dft {ω : R} {K : ℕ} [NeZero K] (h : IsPrincipalRoot ω K) (a : Fin K → R) :
    dft ω (dft ω a) = fun i => (K : R) * a (-i) :=
  funext (dft_dft_apply h a)

/-- The backward transform inverts the forward one up to the factor `K` (MCA §2.3.1). -/
theorem dftInv_dft_apply {ω : R} {K : ℕ} [NeZero K] (h : IsPrincipalRoot ω K) (a : Fin K → R)
    (i : Fin K) : dftInv ω (dft ω a) i = (K : R) * a i := by
  unfold dftInv dft
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ (ℓ j : Fin K), (ω ^ (K - 1)) ^ (i.val * j.val) * (ω ^ (j.val * ℓ.val) * a ℓ)
      = ω ^ (((K - 1) * i.val + ℓ.val) * j.val) * a ℓ := fun ℓ j => by
    rw [← pow_mul, ← mul_assoc, ← pow_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm j.val ℓ.val]
  simp_rw [hterm, ← Finset.sum_mul]
  have hsum : ∀ ℓ : Fin K, ∑ j : Fin K, ω ^ (((K - 1) * i.val + ℓ.val) * j.val)
      = if ((K - 1) * i.val + ℓ.val) % K = 0 then (K : R) else 0 := fun ℓ => by
    rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ (((K - 1) * i.val + ℓ.val) * j)), h.sum_pow_mul]
  simp_rw [hsum]
  have hKi : (K - 1) * i.val + i.val = K * i.val := sub_one_mul_add K i.val (NeZero.pos K)
  have key : ∀ ℓ : Fin K, ((K - 1) * i.val + ℓ.val) % K = 0 ↔ ℓ = i := fun ℓ => by
    constructor
    · intro h0
      have h1 : ((K - 1) * i.val + ℓ.val + i.val) % K = i.val := by
        rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
      rw [Nat.add_right_comm, hKi, Nat.mul_add_mod, Nat.mod_eq_of_lt ℓ.isLt] at h1
      exact Fin.ext h1
    · rintro rfl
      rw [hKi, Nat.mul_mod_right]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left ((key i).mpr rfl)]
  · intro b _ hb
    rw [ite_eq_right (fun h0 => hb ((key b).mp h0)), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- `dftInv ω (dft ω a) = K • a`. -/
theorem dftInv_dft {ω : R} {K : ℕ} [NeZero K] (h : IsPrincipalRoot ω K) (a : Fin K → R) :
    dftInv ω (dft ω a) = fun i => (K : R) * a i :=
  funext (dftInv_dft_apply h a)

end BZ

end Azurite
