/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter2.FFT
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Brent–Zimmermann §2.3.3: the mathematics of Algorithm FFTMulMod

The Schönhage–Strassen multiplication modulo `2^n + 1` (MCA Algorithm 2.4, Theorem 2.3) rests
on four facts, stated here over an arbitrary commutative ring `R` and over `ℤ`, independently of
the limb-level implementation that will use them (`docs/fft_plan.md`):

* **Principal roots of two-power order.**  If `ω^{K/2} = −1` with `K = 2^(k+1)` then `ω` is a
  principal `K`-th root of unity (`IsPrincipalRoot.of_pow_two_pow_eq_neg_one`), the converse of
  `IsPrincipalRoot.pow_half_eq_neg_one`.  In `ℤ/(2^{n'}+1)` the algorithm's `ω = θ² = 2^{2n'/K}`
  satisfies `ω^{K/2} = 2^{n'} = −1`, so this is all that is needed there.
* **The Convolution Theorem** (MCA §2.9): `dft ω (cyclicConv a b) = dft ω a * dft ω b` pointwise
  (`dft_cyclicConv`), for any `ω` with `ω^K = 1`.
* **The weighted (negacyclic) convolution.**  With `θ^K = −1`, the cyclic convolution of
  `θ^ℓ a_ℓ` and `θ^m b_m` is `θ^i` times the negacyclic convolution (2.2),
  `c_i = ∑_{ℓ+m=i} a_ℓ b_m − ∑_{ℓ+m=K+i} a_ℓ b_m` (`cyclicConv_weight`).  Hence steps 4–11 of the
  algorithm compute `K θ^i c_i` (`dftInv_dft_weight_mul`), and so do Algorithms 2.2 and 2.3 with
  the pointwise products taken in bit-reversed order (`backwardFFT_forwardFFT_weight_mul`).
  Evaluating the same identity at `θ = 2^M` in `ℤ/(2^{MK}+1)` gives (2.2) itself,
  `A · B ≡ ∑_j c_j 2^{jM}` (`sum_weight_mul_sum_weight`, `two_pow_eq_neg_one_zmod`).
* **Size and recovery.**  For digits `0 ≤ a_ℓ, b_m < 2^M`, `−(K−1−j) 2^{2M} ≤ c_j < (j+1) 2^{2M}`
  (`negacyclicConv_bounds`), a window of length `K 2^{2M} = 2^{2M+k}`; with `n' ≥ 2M + k` the
  residue of `c_j` modulo `2^{n'} + 1` determines `c_j`, by the correction of steps 12–13
  (`int_recover_of_mem_window`).
-/

namespace Azurite

namespace BZ

open Finset

variable {R : Type*} [CommRing R]

/-! ### Principal roots of two-power order -/

/-- `∑_{j<2^k} τ^j = ∏_{t<k} (1 + τ^{2^t})`. -/
theorem geom_sum_two_pow (τ : R) (k : ℕ) :
    ∑ j ∈ range (2 ^ k), τ ^ j = ∏ t ∈ range k, (1 + τ ^ 2 ^ t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.prod_range_succ, ← ih]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    ring

/-- If `ω^{K/2} = −1` for `K = 2^(k+1)` then `ω` is a principal `K`-th root of unity: for
`0 < i < K`, some factor `1 + (ω^i)^{2^t}` of the geometric sum `∑_{j<K} ω^{ij}` vanishes. -/
theorem IsPrincipalRoot.of_pow_two_pow_eq_neg_one {ω : R} (k : ℕ) (h : ω ^ 2 ^ k = -1) :
    IsPrincipalRoot ω (2 ^ (k + 1)) where
  pow_eq_one := by rw [pow_succ, pow_mul, h]; norm_num
  sum_pow_eq_zero := by
    intro i hi hiK
    have hterm : ∀ j, ω ^ (i * j) = (ω ^ i) ^ j := fun j => pow_mul ω i j
    simp_rw [hterm]
    rw [geom_sum_two_pow]
    obtain ⟨s, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp hi)
    have hs : s < k + 1 := by
      rcases Nat.lt_or_ge s (k + 1) with hs | hs
      · exact hs
      · exact absurd hiK (Nat.not_lt.mpr ((Nat.pow_le_pow_right (by norm_num) hs).trans
          (Nat.le_mul_of_pos_right _ hu.pos)))
    apply Finset.prod_eq_zero (i := k - s) (Finset.mem_range.mpr (by omega))
    rw [← pow_mul, show 2 ^ s * u * 2 ^ (k - s) = 2 ^ k * u by
        rw [mul_comm (2 ^ s) u, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm],
      pow_mul, h, hu.neg_one_pow]
    norm_num

/-- `2^n = −1` in `ℤ/(2^n + 1)`. -/
theorem two_pow_eq_neg_one_zmod (n : ℕ) : (2 : ZMod (2 ^ n + 1)) ^ n = -1 := by
  have h := ZMod.natCast_self (2 ^ n + 1)
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

/-! ### Cyclic and negacyclic convolutions -/

/-- The cyclic convolution `c_i = ∑_{ℓ+m ≡ i (mod K)} a_ℓ b_m`. -/
def cyclicConv {K : ℕ} [NeZero K] (a b : Fin K → R) (i : Fin K) : R :=
  ∑ ℓ : Fin K, a ℓ * b (i - ℓ)

/-- The sum of the entries of a cyclic convolution is the product of the sums of the entries. -/
theorem sum_cyclicConv {K : ℕ} [NeZero K] (a b : Fin K → R) :
    ∑ i, cyclicConv a b i = (∑ ℓ, a ℓ) * (∑ m, b m) := by
  unfold cyclicConv
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight ℓ) b

/-- **The Convolution Theorem** (MCA §2.9): the transform of a cyclic convolution is the pointwise
product of the transforms, for any `ω` with `ω^K = 1`. -/
theorem dft_cyclicConv {K : ℕ} [NeZero K] {ω : R} (hω : ω ^ K = 1) (a b : Fin K → R)
    (j : Fin K) : dft ω (cyclicConv a b) j = dft ω a j * dft ω b j := by
  unfold dft cyclicConv
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft ℓ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [Fin.val_add, pow_mul', ← pow_eq_pow_mod (ℓ.val + m.val) hω, ← pow_mul', Nat.mul_add,
    pow_add]
  ring

/-- The weighting `a_ℓ ↦ θ^ℓ a_ℓ` of step 5 of Algorithm FFTMulMod. -/
def weight {K : ℕ} (θ : R) (a : Fin K → R) : Fin K → R := fun ℓ => θ ^ ℓ.val * a ℓ

/-- The negacyclic convolution (MCA (2.2)): `c_i = ∑_{ℓ+m=i} a_ℓ b_m − ∑_{ℓ+m=K+i} a_ℓ b_m`,
the terms with `ℓ ≤ i` (so `m = i − ℓ`) counted positively and those with `ℓ > i` (so
`m = K + i − ℓ`) negatively. -/
def negacyclicConv {K : ℕ} [NeZero K] (a b : Fin K → R) (i : Fin K) : R :=
  ∑ ℓ : Fin K, if ℓ ≤ i then a ℓ * b (i - ℓ) else -(a ℓ * b (i - ℓ))

/-- With `θ^K = −1`, the cyclic convolution of the weighted vectors is `θ^i` times the negacyclic
convolution: a wrapped-around index picks up the factor `θ^K = −1`. -/
theorem cyclicConv_weight {K : ℕ} [NeZero K] {θ : R} (hθ : θ ^ K = -1) (a b : Fin K → R)
    (i : Fin K) : cyclicConv (weight θ a) (weight θ b) i = θ ^ i.val * negacyclicConv a b i := by
  unfold cyclicConv negacyclicConv weight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs with hℓ
  · have hle : ℓ.val ≤ i.val := hℓ
    rw [Fin.sub_val_of_le hℓ, show θ ^ ℓ.val * a ℓ * (θ ^ (i.val - ℓ.val) * b (i - ℓ))
        = θ ^ (ℓ.val + (i.val - ℓ.val)) * (a ℓ * b (i - ℓ)) by rw [pow_add]; ring,
      Nat.add_sub_cancel' hle]
  · have hlt : i.val < ℓ.val := Fin.lt_def.mp (not_le.mp hℓ)
    rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega),
      show θ ^ ℓ.val * a ℓ * (θ ^ (K - ℓ.val + i.val) * b (i - ℓ))
        = θ ^ (ℓ.val + (K - ℓ.val + i.val)) * (a ℓ * b (i - ℓ)) by rw [pow_add]; ring,
      show ℓ.val + (K - ℓ.val + i.val) = K + i.val by omega, pow_add, hθ]
    ring

/-! ### The heart of Theorem 2.3 -/

/-- **Steps 4–11 of Algorithm FFTMulMod, in any commutative ring**: for `θ^K = −1` with
`ω = θ²` principal, transforming the weighted vectors, multiplying pointwise and transforming
back gives `K θ^i c_i`, `c` the negacyclic convolution.  Dividing by `K θ^i` (step 11) leaves
`c_i`. -/
theorem dftInv_dft_weight_mul {K : ℕ} [NeZero K] {θ : R} (hθ : θ ^ K = -1)
    (hω : IsPrincipalRoot (θ ^ 2) K) (a b : Fin K → R) (i : Fin K) :
    dftInv (θ ^ 2) (fun j => dft (θ ^ 2) (weight θ a) j * dft (θ ^ 2) (weight θ b) j) i
      = (K : R) * (θ ^ i.val * negacyclicConv a b i) := by
  have h : (fun j => dft (θ ^ 2) (weight θ a) j * dft (θ ^ 2) (weight θ b) j)
      = dft (θ ^ 2) (cyclicConv (weight θ a) (weight θ b)) := by
    funext j
    rw [dft_cyclicConv hω.pow_eq_one]
  rw [h, dftInv_dft_apply hω, cyclicConv_weight hθ]

/-- **Steps 6–9 with Algorithms 2.2 and 2.3**: the pointwise products are taken in bit-reversed
order and the backward transform returns the normal order, so no explicit bit reversal is
needed; only `θ^K = −1` is required (`K = 2^(k+1)`). -/
theorem backwardFFT_forwardFFT_weight_mul (k : ℕ) {θ : R} (hθ : θ ^ 2 ^ (k + 1) = -1)
    (a b : Fin (2 ^ (k + 1)) → R) (i : Fin (2 ^ (k + 1))) :
    backwardFFT (θ ^ 2) (k + 1) (fun r =>
        forwardFFT (θ ^ 2) (k + 1) (extendZero (weight θ a)) r
          * forwardFFT (θ ^ 2) (k + 1) (extendZero (weight θ b)) r) i
      = ((2 ^ (k + 1) : ℕ) : R) * (θ ^ i.val * negacyclicConv a b i) := by
  have hω : (θ ^ 2) ^ 2 ^ k = -1 := by rwa [← pow_mul, ← pow_succ']
  have hprin : IsPrincipalRoot (θ ^ 2) (2 ^ (k + 1)) :=
    IsPrincipalRoot.of_pow_two_pow_eq_neg_one k hω
  have : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  rw [backwardFFT_eq_dftNat k (θ ^ 2) _
      (extendZero (fun j => dft (θ ^ 2) (weight θ a) j * dft (θ ^ 2) (weight θ b) j)) i hω ?_
      i.isLt, ← dft_eq_dftNat]
  · exact dftInv_dft_weight_mul hθ hprin a b i
  · intro r hr
    rw [forwardFFT_eq_dftNat k _ _ r hω hr, forwardFFT_eq_dftNat k _ _ r hω hr, extendZero,
      dite_eq_left (bitrev_lt (k + 1) r), dft_eq_dftNat, dft_eq_dftNat]

/-- **Equation (2.2) at the ring level**: with `θ^K = −1`,
`(∑_ℓ θ^ℓ a_ℓ)(∑_m θ^m b_m) = ∑_j θ^j c_j`.  In `ℤ/(2^{MK}+1)` with `θ = 2^M`
(`two_pow_eq_neg_one_zmod`) this reads `A · B ≡ ∑_j c_j 2^{jM}`. -/
theorem sum_weight_mul_sum_weight {K : ℕ} [NeZero K] {θ : R} (hθ : θ ^ K = -1)
    (a b : Fin K → R) :
    (∑ ℓ, θ ^ ℓ.val * a ℓ) * (∑ m, θ ^ m.val * b m)
      = ∑ j, θ ^ j.val * negacyclicConv a b j := by
  rw [show (∑ ℓ, θ ^ ℓ.val * a ℓ) = ∑ ℓ, weight θ a ℓ from rfl,
    show (∑ m, θ ^ m.val * b m) = ∑ m, weight θ b m from rfl, ← sum_cyclicConv]
  exact Finset.sum_congr rfl fun j _ => cyclicConv_weight hθ a b j

/-! ### Size of the coefficients and their recovery from residues -/

/-- **MCA's bound on `c_j`**: for digits `0 ≤ a_ℓ, b_m < B`,
`−(K−1−j) B² ≤ c_j < (j+1) B²` (the first sum of (2.2) has `j+1` terms, the second `K−1−j`). -/
theorem negacyclicConv_bounds {K : ℕ} [NeZero K] (B : ℤ) (hB : 0 < B) (a b : Fin K → ℤ)
    (ha : ∀ ℓ, 0 ≤ a ℓ ∧ a ℓ < B) (hb : ∀ m, 0 ≤ b m ∧ b m < B) (j : Fin K) :
    -(((K - 1 - j.val : ℕ) : ℤ) * B ^ 2) ≤ negacyclicConv a b j
      ∧ negacyclicConv a b j < ((j.val + 1 : ℕ) : ℤ) * B ^ 2 := by
  unfold negacyclicConv
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ : Fin K => ℓ ≤ j)]
  set S₁ := Finset.univ.filter (fun ℓ : Fin K => ℓ ≤ j) with hS₁
  set S₂ := Finset.univ.filter (fun ℓ : Fin K => ¬ ℓ ≤ j) with hS₂
  have hcard₁ : S₁.card = j.val + 1 := by
    rw [hS₁, show Finset.univ.filter (fun ℓ : Fin K => ℓ ≤ j) = Finset.Iic j by ext ℓ; simp,
      Fin.card_Iic]
  have hcard₂ : S₂.card = K - 1 - j.val := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K)))
      (fun ℓ : Fin K => ℓ ≤ j)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [← hS₁, ← hS₂] at h
    omega
  have hprod : ∀ ℓ m, 0 ≤ a ℓ * b m ∧ a ℓ * b m ≤ (B - 1) ^ 2 := fun ℓ m =>
    ⟨mul_nonneg (ha ℓ).1 (hb m).1, by
      rw [sq]
      exact mul_le_mul (by linarith [(ha ℓ).2]) (by linarith [(hb m).2]) (hb m).1 (by linarith)⟩
  have h₁ : ∑ ℓ ∈ S₁, (if ℓ ≤ j then a ℓ * b (j - ℓ) else -(a ℓ * b (j - ℓ)))
      = ∑ ℓ ∈ S₁, a ℓ * b (j - ℓ) :=
    Finset.sum_congr rfl fun ℓ hℓ => by rw [ite_eq_left (Finset.mem_filter.mp hℓ).2]
  have h₂ : ∑ ℓ ∈ S₂, (if ℓ ≤ j then a ℓ * b (j - ℓ) else -(a ℓ * b (j - ℓ)))
      = ∑ ℓ ∈ S₂, -(a ℓ * b (j - ℓ)) :=
    Finset.sum_congr rfl fun ℓ hℓ => by rw [ite_eq_right (Finset.mem_filter.mp hℓ).2]
  rw [h₁, h₂]
  have hS₁_nonneg : 0 ≤ ∑ ℓ ∈ S₁, a ℓ * b (j - ℓ) :=
    Finset.sum_nonneg fun ℓ _ => (hprod ℓ _).1
  have hS₁_le : ∑ ℓ ∈ S₁, a ℓ * b (j - ℓ) ≤ ((j.val + 1 : ℕ) : ℤ) * (B - 1) ^ 2 := by
    have := Finset.sum_le_card_nsmul S₁ (fun ℓ => a ℓ * b (j - ℓ)) ((B - 1) ^ 2)
      fun ℓ _ => (hprod ℓ _).2
    rwa [hcard₁, nsmul_eq_mul] at this
  have hS₂_nonpos : ∑ ℓ ∈ S₂, -(a ℓ * b (j - ℓ)) ≤ 0 :=
    Finset.sum_nonpos fun ℓ _ => neg_nonpos.mpr (hprod ℓ _).1
  have hS₂_ge : -(((K - 1 - j.val : ℕ) : ℤ) * B ^ 2) ≤ ∑ ℓ ∈ S₂, -(a ℓ * b (j - ℓ)) := by
    have := Finset.card_nsmul_le_sum S₂ (fun ℓ => -(a ℓ * b (j - ℓ))) (-(B ^ 2))
      fun ℓ _ => by
        have h := (hprod ℓ (j - ℓ)).2
        have : (B - 1) ^ 2 ≤ B ^ 2 := by nlinarith
        linarith
    rwa [hcard₂, nsmul_eq_mul, mul_neg] at this
  have hsq : ((j.val + 1 : ℕ) : ℤ) * (B - 1) ^ 2 < ((j.val + 1 : ℕ) : ℤ) * B ^ 2 := by
    apply mul_lt_mul_of_pos_left _ (by positivity)
    nlinarith
  exact ⟨by linarith, by linarith⟩

/-- **Steps 12–13 of Algorithm FFTMulMod**: an integer in a window `[U − N, U)` of length `N`
is determined by its residue modulo `N`: it is the residue, minus `N` when the residue is at
least `U`. -/
theorem int_recover_of_mem_window {c U N : ℤ} (hU0 : 0 ≤ U) (hUN : U ≤ N) (hlo : U - N ≤ c)
    (hhi : c < U) : c = if U ≤ c % N then c % N - N else c % N := by
  by_cases hc : 0 ≤ c
  · rw [Int.emod_eq_of_lt hc (by omega), ite_eq_right (by omega)]
  · have h1 : c % N = c + N := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [h1, ite_eq_left (by omega)]
    ring

end BZ

end Azurite
