/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter2.DFT

/-!
# Brent–Zimmermann §2.3.2: the fast Fourier transform

The recursive evaluation of the transform (2.1) for `K = 2^k`, read off MCA's worked example for
`K = 8`.  Writing `m = K/2`, the first stage forms, for `j < m`,

  `s_j = a_j + a_{j+m}`                 (MCA's `a_{0,4}, a_{1,5}, …`)
  `d_j = ω^j · (a_j + ω^m · a_{j+m})`   (MCA's `a_{4,0}, ω a_{5,1}, ω² a_{6,2}, …`)

and then `â_{2i}` is the `i`-th entry of the transform of `s` at `ω²`, while `â_{2i+1}` is the
`i`-th entry of the transform of `d` at `ω²`; the example's second stage is this recursion applied
to both halves with root `ω²`.  This is "decimation in frequency"; MCA writes `ω^4 a_4` rather than
`−a_4`, and so do we: correctness (`fftRec_eq_sum`, `fft_eq_dft`) needs only `ω^K = 1`, not that
`ω^{K/2} = −1` (which can fail in a ring with zero divisors) nor that `ω` is principal (which is
needed for *inverting* the transform, `DFT.lean`).  The operation count `O(K log K)` is visible in
the recursion: two half-size transforms plus `O(K)` ring operations per level.

The recursion is stated on functions `ℕ → R` with an explicit length `2^k`, which keeps the index
arithmetic (`2i`, `2i+1`, `j + m`) out of `Fin`; `fft` packages it for `Fin (2^k) → R` and
`fft_eq_dft` connects it to `dft`.  The in-place, bit-reversed form used by an implementation is a
later concern.
-/

namespace Azurite

namespace BZ

open Finset

variable {R : Type*} [CommRing R]

/-- The recursive FFT on a vector of length `2^k` given as a function `ℕ → R` (entries beyond
`2^k` are ignored): `fftRec ω k a i = ∑_{j < 2^k} ω^{ij} a_j` for `i < 2^k` when `ω^(2^k) = 1`. -/
def fftRec (ω : R) : (k : ℕ) → (ℕ → R) → ℕ → R
  | 0, a => a
  | k + 1, a =>
    let m := 2 ^ k
    let s : ℕ → R := fun j => a j + a (j + m)
    let d : ℕ → R := fun j => ω ^ j * (a j + ω ^ m * a (j + m))
    let es := fftRec (ω ^ 2) k s
    let ds := fftRec (ω ^ 2) k d
    fun r => if r % 2 = 0 then es (r / 2) else ds (r / 2)

/-- The transform (2.1) on `ℕ → R` with an explicit length `K`. -/
def dftNat (ω : R) (K : ℕ) (a : ℕ → R) (i : ℕ) : R :=
  ∑ j ∈ range K, ω ^ (i * j) * a j

/-- The even entries of a length-`2m` transform are the transform at `ω²` of the sums
`a_j + a_{j+m}`. -/
private lemma dftNat_two_mul (ω : R) (m : ℕ) (hω : ω ^ (2 * m) = 1) (a : ℕ → R) (i : ℕ) :
    dftNat ω (2 * m) a (2 * i) = dftNat (ω ^ 2) m (fun j => a j + a (j + m)) i := by
  unfold dftNat
  rw [two_mul m, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * i * (m + j) = 2 * m * i + 2 * i * j by ring, pow_add, pow_mul ω (2 * m), hω,
    one_pow, one_mul, ← pow_mul, show 2 * (i * j) = 2 * i * j by ring, Nat.add_comm m j]
  dsimp only
  ring

/-- The odd entries of a length-`2m` transform are the transform at `ω²` of the twiddled
differences `ω^j (a_j + ω^m a_{j+m})`. -/
private lemma dftNat_two_mul_add_one (ω : R) (m : ℕ) (hω : ω ^ (2 * m) = 1) (a : ℕ → R)
    (i : ℕ) :
    dftNat ω (2 * m) a (2 * i + 1)
      = dftNat (ω ^ 2) m (fun j => ω ^ j * (a j + ω ^ m * a (j + m))) i := by
  unfold dftNat
  rw [two_mul m, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (2 * i + 1) * (m + j) = 2 * m * i + m + (2 * i + 1) * j by ring, pow_add, pow_add,
    pow_mul ω (2 * m), hω, one_pow, one_mul, ← pow_mul, show 2 * (i * j) = 2 * i * j by ring,
    show (2 * i + 1) * j = 2 * i * j + j by ring, pow_add, Nat.add_comm m j]
  dsimp only
  ring

/-- **Correctness of the FFT** (MCA §2.3.2): for `ω^(2^k) = 1` and `i < 2^k`,
`fftRec ω k a i = ∑_{j < 2^k} ω^{ij} a_j`. -/
theorem fftRec_eq_dftNat (k : ℕ) (ω : R) (hω : ω ^ (2 ^ k) = 1) (a : ℕ → R) (i : ℕ)
    (hi : i < 2 ^ k) : fftRec ω k a i = dftNat ω (2 ^ k) a i := by
  induction k generalizing ω a i with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [fftRec, dftNat]
  | succ k ih =>
    have h2m : ω ^ (2 * 2 ^ k) = 1 := by rwa [← pow_succ']
    have hω2 : (ω ^ 2) ^ (2 ^ k) = 1 := by rwa [← pow_mul]
    have hK : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    rw [hK] at hi ⊢
    show (if i % 2 = 0 then fftRec (ω ^ 2) k (fun j => a j + a (j + 2 ^ k)) (i / 2)
      else fftRec (ω ^ 2) k (fun j => ω ^ j * (a j + ω ^ 2 ^ k * a (j + 2 ^ k))) (i / 2)) = _
    have hi2 : i / 2 < 2 ^ k := by omega
    split_ifs with hpar
    · rw [ih _ hω2 _ _ hi2, ← dftNat_two_mul ω _ h2m a (i / 2), Nat.mul_div_cancel' (by omega)]
    · rw [ih _ hω2 _ _ hi2, ← dftNat_two_mul_add_one ω _ h2m a (i / 2)]
      congr 1
      omega

/-- A vector `Fin K → R` as a function `ℕ → R` (zero beyond `K`). -/
def extendZero {K : ℕ} (a : Fin K → R) : ℕ → R :=
  fun j => if h : j < K then a ⟨j, h⟩ else 0

/-- The FFT of a vector of length `2^k`. -/
def fft (k : ℕ) (ω : R) (a : Fin (2 ^ k) → R) : Fin (2 ^ k) → R :=
  fun i => fftRec ω k (extendZero a) i

theorem dft_eq_dftNat {K : ℕ} (ω : R) (a : Fin K → R) (i : Fin K) :
    dft ω a i = dftNat ω K (extendZero a) i := by
  unfold dft dftNat
  rw [← Fin.sum_univ_eq_sum_range (fun j => ω ^ (i.val * j) * extendZero a j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [extendZero, j.isLt]

/-- **The FFT computes the transform (2.1)** whenever `ω^(2^k) = 1`. -/
theorem fft_eq_dft (k : ℕ) (ω : R) (hω : ω ^ (2 ^ k) = 1) (a : Fin (2 ^ k) → R) :
    fft k ω a = dft ω a := by
  funext i
  rw [fft, dft_eq_dftNat, fftRec_eq_dftNat k ω hω _ i i.isLt]

/-! ### Butterflies (MCA §2.3.2, continued)

MCA pairs the two operations `a = b + ω^j c`, `a' = b + ω^{j+K/2} c` into one *butterfly*
`(b + ω^j c, b − ω^j c)`, "since `ω^{K/2} = −1`".  In a general ring a principal root only gives
`(K/2) · (1 + ω^{K/2}) = 0`; the sign flip follows once `K/2` is cancellable, which it is in the
rings of interest (`K/2` is a power of two and the modulus `2^N + 1` is odd).  `fftRecSub` is
`fftRec` with that butterfly; it is the shape the in-place algorithm takes. -/

namespace IsPrincipalRoot

/-- `∑_{j<2n} ω^{mj} = n · (1 + ω^m)` when `ω^{2m} = 1`: the terms alternate `1, ω^m, 1, …`. -/
private lemma sum_range_two_mul_pow_mul {ω : R} {m : ℕ} (hω : ω ^ (2 * m) = 1) (n : ℕ) :
    ∑ j ∈ range (2 * n), ω ^ (m * j) = (n : R) * (1 + ω ^ m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show m * (2 * n + 1) = 2 * m * n + m by ring, show m * (2 * n) = 2 * m * n by ring, pow_add,
      pow_mul, hω, one_pow, one_mul]
    push_cast
    ring

/-- For a principal `2m`-th root, `m · (1 + ω^m) = 0`. -/
theorem natCast_mul_one_add_pow_half {ω : R} {m : ℕ} (h : IsPrincipalRoot ω (2 * m)) (hm : 0 < m) :
    (m : R) * (1 + ω ^ m) = 0 := by
  rw [← sum_range_two_mul_pow_mul h.pow_eq_one m]
  exact h.sum_pow_eq_zero m hm (by omega)

/-- `ω^{K/2} = −1` for a principal `K`-th root when `K/2` is a unit of `R` (MCA's "since
`ω^4 = −1`"). -/
theorem pow_half_eq_neg_one {ω : R} {m : ℕ} (h : IsPrincipalRoot ω (2 * m)) (hm : 0 < m)
    (hu : IsUnit (m : R)) : ω ^ m = -1 := by
  have h0 := h.natCast_mul_one_add_pow_half hm
  rw [← mul_zero (m : R)] at h0
  exact eq_neg_of_add_eq_zero_right (hu.mul_left_cancel h0)

end IsPrincipalRoot

/-- `fftRec` with MCA's butterfly: the twiddled differences are `ω^j (a_j − a_{j+m})`, one
multiplication by `ω^j` serving both halves. -/
def fftRecSub (ω : R) : (k : ℕ) → (ℕ → R) → ℕ → R
  | 0, a => a
  | k + 1, a =>
    let m := 2 ^ k
    let s : ℕ → R := fun j => a j + a (j + m)
    let d : ℕ → R := fun j => ω ^ j * (a j - a (j + m))
    let es := fftRecSub (ω ^ 2) k s
    let ds := fftRecSub (ω ^ 2) k d
    fun r => if r % 2 = 0 then es (r / 2) else ds (r / 2)

/-- The butterfly form agrees with `fftRec` once `ω^{K/2} = −1` (`K = 2^(k+1)`). -/
theorem fftRecSub_eq_fftRec (k : ℕ) (ω : R) (hω : ω ^ (2 ^ k) = -1) (a : ℕ → R) :
    fftRecSub ω (k + 1) a = fftRec ω (k + 1) a := by
  induction k generalizing ω a with
  | zero =>
    funext r
    simp only [fftRecSub, fftRec, pow_zero, pow_one] at hω ⊢
    rw [hω]
    simp [sub_eq_add_neg]
  | succ k ih =>
    have hω2 : (ω ^ 2) ^ (2 ^ k) = -1 := by rwa [← pow_mul, ← pow_succ']
    funext r
    show (if r % 2 = 0 then fftRecSub (ω ^ 2) (k + 1) (fun j => a j + a (j + 2 ^ (k + 1))) (r / 2)
        else fftRecSub (ω ^ 2) (k + 1) (fun j => ω ^ j * (a j - a (j + 2 ^ (k + 1)))) (r / 2))
      = (if r % 2 = 0 then fftRec (ω ^ 2) (k + 1) (fun j => a j + a (j + 2 ^ (k + 1))) (r / 2)
        else fftRec (ω ^ 2) (k + 1) (fun j => ω ^ j * (a j + ω ^ 2 ^ (k + 1) * a (j + 2 ^ (k + 1))))
          (r / 2))
    rw [ih _ hω2, ih _ hω2, hω]
    simp [sub_eq_add_neg]

/-- **Correctness of the butterfly FFT**: for `ω^{K/2} = −1` with `K = 2^(k+1)` and `i < K`,
`fftRecSub ω (k+1) a i = ∑_{j<K} ω^{ij} a_j`. -/
theorem fftRecSub_eq_dftNat (k : ℕ) (ω : R) (hω : ω ^ (2 ^ k) = -1) (a : ℕ → R) (i : ℕ)
    (hi : i < 2 ^ (k + 1)) : fftRecSub ω (k + 1) a i = dftNat ω (2 ^ (k + 1)) a i := by
  rw [fftRecSub_eq_fftRec k ω hω a]
  exact fftRec_eq_dftNat (k + 1) ω (by rw [pow_succ, pow_mul, hω]; norm_num) a i hi

/-- The butterfly FFT computes the transform at any principal root of order `2^(k+1)` when
`2^k` is a unit of the ring. -/
theorem fftRecSub_eq_dftNat_of_principal (k : ℕ) {ω : R} (h : IsPrincipalRoot ω (2 ^ (k + 1)))
    (hu : IsUnit ((2 ^ k : ℕ) : R)) (a : ℕ → R) (i : ℕ) (hi : i < 2 ^ (k + 1)) :
    fftRecSub ω (k + 1) a i = dftNat ω (2 ^ (k + 1)) a i := by
  have h' : IsPrincipalRoot ω (2 * 2 ^ k) := by rwa [← pow_succ']
  exact fftRecSub_eq_dftNat k ω (h'.pow_half_eq_neg_one (Nat.two_pow_pos k) hu) a i hi

/-! ### Algorithm 2.2 ForwardFFT and Theorem 2.1

MCA's in-place algorithm is *decimation in time*: it transforms the even-indexed and the
odd-indexed entries separately (at `ω²`), then combines them with the butterfly
`(b_j + ω^{j'} c_j, b_j − ω^{j'} c_j)` where `j' = bitrev(j, K/2)`, and the result comes out in
bit-reversed order.  `forwardFFT` is the algorithm as a function on `ℕ → R` (position `r` of the
in-place result); Theorem 2.1 is `forwardFFT_eq_dftNat`: for `K = 2^(k+1)` and `ω^{K/2} = −1`,
`forwardFFT ω (k+1) a r = â_{bitrev(r, K)}`.  The `K = 1` case of the recursion (the identity)
is not in MCA; with it, MCA's base case `K = 2` is an instance of the general step, so the
definition has a single recursive clause. -/

/-- `bitrev k j`: the bit-reversal of `j` as a `k`-bit integer (MCA's `bitrev(j, 2^k)`). -/
def bitrev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, j => j % 2 * 2 ^ k + bitrev k (j / 2)

theorem bitrev_lt (k j : ℕ) : bitrev k j < 2 ^ k := by
  induction k generalizing j with
  | zero => simp [bitrev]
  | succ k ih =>
    have h := ih (j / 2)
    show j % 2 * 2 ^ k + bitrev k (j / 2) < 2 ^ (k + 1)
    rw [pow_succ]
    rcases Nat.mod_two_eq_zero_or_one j with h2 | h2 <;> rw [h2] <;> omega

theorem bitrev_two_mul (k j : ℕ) : bitrev (k + 1) (2 * j) = bitrev k j := by
  show 2 * j % 2 * 2 ^ k + bitrev k (2 * j / 2) = bitrev k j
  rw [Nat.mul_mod_right, Nat.zero_mul, Nat.zero_add, Nat.mul_div_cancel_left j (by norm_num)]

theorem bitrev_two_mul_add_one (k j : ℕ) : bitrev (k + 1) (2 * j + 1) = 2 ^ k + bitrev k j := by
  show (2 * j + 1) % 2 * 2 ^ k + bitrev k ((2 * j + 1) / 2) = 2 ^ k + bitrev k j
  rw [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega, Nat.one_mul]

/-- Reversing `k + 1` bits of a `k`-bit number appends a zero bit at the bottom. -/
theorem bitrev_succ_of_lt (k r : ℕ) (hr : r < 2 ^ k) : bitrev (k + 1) r = 2 * bitrev k r := by
  induction k generalizing r with
  | zero =>
    obtain rfl : r = 0 := (by omega)
    rfl
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    show r % 2 * 2 ^ (k + 1) + bitrev (k + 1) (r / 2) = 2 * (r % 2 * 2 ^ k + bitrev k (r / 2))
    rw [ih (r / 2) (by omega), h2]
    ring

/-- Reversing `k + 1` bits of `2^k + r` (`r < 2^k`) appends a one bit at the bottom. -/
theorem bitrev_succ_pow_add (k r : ℕ) (hr : r < 2 ^ k) :
    bitrev (k + 1) (2 ^ k + r) = 2 * bitrev k r + 1 := by
  induction k generalizing r with
  | zero =>
    obtain rfl : r = 0 := (by omega)
    rfl
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    show (2 ^ (k + 1) + r) % 2 * 2 ^ (k + 1) + bitrev (k + 1) ((2 ^ (k + 1) + r) / 2)
      = 2 * (r % 2 * 2 ^ k + bitrev k (r / 2)) + 1
    rw [show (2 ^ (k + 1) + r) % 2 = r % 2 by omega,
      show (2 ^ (k + 1) + r) / 2 = 2 ^ k + r / 2 by omega, ih (r / 2) (by omega), h2]
    ring

/-- Bit reversal is an involution on `k`-bit numbers. -/
theorem bitrev_bitrev (k j : ℕ) (hj : j < 2 ^ k) : bitrev k (bitrev k j) = j := by
  induction k generalizing j with
  | zero =>
    obtain rfl : j = 0 := (by omega)
    rfl
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have hj2 : j / 2 < 2 ^ k := by omega
    rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
    · obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' := ⟨j / 2, by omega⟩
      rw [bitrev_two_mul, bitrev_succ_of_lt k _ (bitrev_lt k j'),
        ih j' (by omega)]
    · obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' + 1 := ⟨j / 2, by omega⟩
      rw [bitrev_two_mul_add_one, bitrev_succ_pow_add k _ (bitrev_lt k j'),
        ih j' (by omega)]

/-- **Algorithm 2.2 ForwardFFT** as a function: `forwardFFT ω k a r` is the entry at position
`r` of the in-place result on `K = 2^k` entries.  The two recursive calls are the transforms of
the even- and odd-indexed entries at `ω²` (steps 4–5); the butterfly is step 7. -/
def forwardFFT (ω : R) : (k : ℕ) → (ℕ → R) → ℕ → R
  | 0, a => a
  | k + 1, a => fun r =>
    if r % 2 = 0 then
      forwardFFT (ω ^ 2) k (fun ℓ => a (2 * ℓ)) (r / 2)
        + ω ^ bitrev k (r / 2) * forwardFFT (ω ^ 2) k (fun ℓ => a (2 * ℓ + 1)) (r / 2)
    else
      forwardFFT (ω ^ 2) k (fun ℓ => a (2 * ℓ)) (r / 2)
        - ω ^ bitrev k (r / 2) * forwardFFT (ω ^ 2) k (fun ℓ => a (2 * ℓ + 1)) (r / 2)

/-- A range sum split into its even- and odd-indexed terms. -/
private lemma sum_range_two_mul_split (f : ℕ → R) (n : ℕ) :
    ∑ ℓ ∈ range (2 * n), f ℓ = ∑ ℓ ∈ range n, f (2 * ℓ) + ∑ ℓ ∈ range n, f (2 * ℓ + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **Theorem 2.1** (MCA): for `K = 2^(k+1)` and `ω^{K/2} = −1`, Algorithm ForwardFFT computes
the transform in bit-reversed order, `forwardFFT ω (k+1) a r = â_{bitrev(r, K)}` for `r < K`. -/
theorem forwardFFT_eq_dftNat (k : ℕ) :
    ∀ (ω : R) (a : ℕ → R) (r : ℕ), ω ^ 2 ^ k = -1 → r < 2 ^ (k + 1) →
      forwardFFT ω (k + 1) a r = dftNat ω (2 ^ (k + 1)) a (bitrev (k + 1) r) := by
  induction k with
  | zero =>
    intro ω a r hω hr
    simp only [pow_zero, pow_one] at hω
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · simp [forwardFFT, bitrev, dftNat, Finset.sum_range_succ]
    · simp [forwardFFT, bitrev, dftNat, Finset.sum_range_succ, hω, sub_eq_add_neg]
  | succ k ih =>
    intro ω a r hω hr
    have hω2 : (ω ^ 2) ^ 2 ^ k = -1 := by rwa [← pow_mul, ← pow_succ']
    have hK : ω ^ (2 * 2 ^ (k + 1)) = 1 := by rw [pow_mul', hω]; norm_num
    have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := pow_succ' 2 (k + 1)
    have hjlt : r / 2 < 2 ^ (k + 1) := by omega
    rw [forwardFFT]
    dsimp only
    rw [ih (ω ^ 2) _ (r / 2) hω2 hjlt, ih (ω ^ 2) _ (r / 2) hω2 hjlt]
    split_ifs with hpar
    · obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j := ⟨r / 2, by omega⟩
      rw [Nat.mul_div_cancel_left j (by norm_num), bitrev_two_mul]
      simp only [dftNat]
      rw [h2, sum_range_two_mul_split, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
      rw [show (2 * j + 1) / 2 = j by omega, bitrev_two_mul_add_one]
      simp only [dftNat]
      rw [h2, sum_range_two_mul_split, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      set K' := 2 ^ (k + 1) with hK'
      set j' := bitrev (k + 1) j with hj'
      rw [show (K' + j') * (2 * ℓ) = 2 * K' * ℓ + j' * (2 * ℓ) by ring,
        show (K' + j') * (2 * ℓ + 1) = 2 * K' * ℓ + K' + j' * (2 * ℓ + 1) by ring,
        pow_add ω (2 * K' * ℓ), pow_add ω (2 * K' * ℓ + K'), pow_add ω (2 * K' * ℓ) K',
        pow_mul ω (2 * K'), hK, one_pow, one_mul, one_mul, hω]
      ring

/-- Theorem 2.1 on `Fin`-indexed vectors: `forwardFFT` at position `r` is `dft` at
`bitrev(r, K)`. -/
theorem forwardFFT_eq_dft (k : ℕ) (ω : R) (hω : ω ^ 2 ^ k = -1) (a : Fin (2 ^ (k + 1)) → R)
    (r : Fin (2 ^ (k + 1))) :
    forwardFFT ω (k + 1) (extendZero a) r = dft ω a ⟨bitrev (k + 1) r, bitrev_lt _ _⟩ := by
  rw [forwardFFT_eq_dftNat k ω _ r hω r.isLt, dft_eq_dftNat]

/-! ### Algorithm 2.3 BackwardFFT and Theorem 2.2

The backward transform takes its input in bit-reversed order and returns the normal order: the
two halves of the (bit-reversed) input are the bit-reversed even- and odd-indexed entries, so
after transforming them in place (at `ω²`) the butterfly on `(a_j, a_{K/2+j})` with the twiddle
`ω^{−j} = ω^{K−j}` produces `ã_j` and `ã_{K/2+j}`.  `backwardFFT` is the algorithm as a function
and `backwardFFT_eq_dftNat` is Theorem 2.2: if `a_r = x_{bitrev(r,K)}` for `r < K`, the output at
`j < K` is `∑_ℓ (ω^{K−1})^{jℓ} x_ℓ`, the backward transform of `x` at `ω`.  Composed with
Algorithm 2.2, `backwardFFT_forwardFFT` recovers `K · x` in normal order with no explicit bit
reversal. -/

/-- **Algorithm 2.3 BackwardFFT** as a function: `backwardFFT ω k a r` is the entry at position
`r` of the in-place result on `K = 2^k` entries given in bit-reversed order.  Steps 4–5 are the
recursive calls on the two halves; step 7 is the butterfly with `ω^{−j} = ω^{K−j}`. -/
def backwardFFT (ω : R) : (k : ℕ) → (ℕ → R) → ℕ → R
  | 0, a => a
  | k + 1, a => fun r =>
    if r < 2 ^ k then
      backwardFFT (ω ^ 2) k a r
        + ω ^ (2 ^ (k + 1) - r) * backwardFFT (ω ^ 2) k (fun s => a (2 ^ k + s)) r
    else
      backwardFFT (ω ^ 2) k a (r - 2 ^ k)
        - ω ^ (2 ^ (k + 1) - (r - 2 ^ k)) * backwardFFT (ω ^ 2) k (fun s => a (2 ^ k + s)) (r - 2 ^ k)

/-- Inverses are unique in a commutative ring. -/
private lemma eq_of_mul_eq_one_of_mul_eq_one {u u' v : R} (h : u * v = 1) (h' : u' * v = 1) :
    u = u' := by
  calc u = u * (u' * v) := by rw [h', mul_one]
    _ = u' * (u * v) := by ring
    _ = u' := by rw [h, mul_one]

/-- **Theorem 2.2** (MCA): for `K = 2^(k+1)` and `ω^{K/2} = −1`, if `a` holds `x` in
bit-reversed order then Algorithm BackwardFFT returns the backward transform of `x` in normal
order: `backwardFFT ω (k+1) a j = ∑_{ℓ<K} (ω^{K−1})^{jℓ} x_ℓ` for `j < K`. -/
theorem backwardFFT_eq_dftNat (k : ℕ) :
    ∀ (ω : R) (a x : ℕ → R) (j : ℕ), ω ^ 2 ^ k = -1 →
      (∀ r, r < 2 ^ (k + 1) → a r = x (bitrev (k + 1) r)) → j < 2 ^ (k + 1) →
      backwardFFT ω (k + 1) a j = dftNat (ω ^ (2 ^ (k + 1) - 1)) (2 ^ (k + 1)) x j := by
  induction k with
  | zero =>
    intro ω a x j hω ha hj
    simp only [pow_zero, pow_one] at hω
    have ha0 : a 0 = x 0 := ha 0 (by norm_num)
    have ha1 : a 1 = x 1 := ha 1 (by norm_num)
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp [backwardFFT, dftNat, Finset.sum_range_succ, ha0, ha1, hω]
    · simp [backwardFFT, dftNat, Finset.sum_range_succ, ha0, ha1, hω, sub_eq_add_neg]
  | succ k ih =>
    intro ω a x j hω ha hj
    -- the half length `m`, the full length `2m`, and the inverse root `ν = ω^(2m−1)`
    set m := 2 ^ (k + 1) with hm
    have hK2 : 2 ^ (k + 1 + 1) = 2 * m := pow_succ' 2 (k + 1)
    rw [hK2] at ha hj ⊢
    have hm_pos : 0 < m := Nat.two_pow_pos _
    have hωK : ω ^ (2 * m) = 1 := by rw [pow_mul', hω]; norm_num
    set ν := ω ^ (2 * m - 1) with hν
    have hνω : ν * ω = 1 := by
      rw [hν, ← pow_succ, Nat.sub_add_cancel (by omega), hωK]
    have hνK : ν ^ (2 * m) = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, hωK, one_pow]
    have hνm : ν ^ m = -1 := by
      have : ν ^ m * ω ^ m = 1 := by rw [← mul_pow, hνω, one_pow]
      rw [hω, mul_neg_one, neg_eq_iff_eq_neg] at this
      exact this
    have htw : ∀ i, i ≤ 2 * m → ω ^ (2 * m - i) = ν ^ i := fun i hi => by
      calc ω ^ (2 * m - i) = ω ^ (2 * m - i) * (ν * ω) ^ i := by rw [hνω, one_pow, mul_one]
        _ = ν ^ i * ω ^ (2 * m - i + i) := by rw [mul_pow, pow_add]; ring
        _ = ν ^ i := by rw [Nat.sub_add_cancel hi, hωK, mul_one]
    have hν2 : (ω ^ 2) ^ (m - 1) = ν ^ 2 := by
      apply eq_of_mul_eq_one_of_mul_eq_one (v := ω ^ 2)
      · rw [← pow_succ, Nat.sub_add_cancel hm_pos, ← pow_mul, hωK]
      · rw [← mul_pow, hνω, one_pow]
    -- the induction hypotheses for the two halves
    have hω2 : (ω ^ 2) ^ 2 ^ k = -1 := by rwa [← pow_mul, ← pow_succ']
    have heven : ∀ r, r < m → a r = x (2 * bitrev (k + 1) r) := fun r hr => by
      rw [ha r (by omega), bitrev_succ_of_lt (k + 1) r hr]
    have hodd : ∀ r, r < m → a (m + r) = x (2 * bitrev (k + 1) r + 1) := fun r hr => by
      rw [ha (m + r) (by omega), bitrev_succ_pow_add (k + 1) r hr]
    rw [backwardFFT]
    dsimp only
    rw [← hm, hK2]
    -- (the recursive results, by induction)
    have hb : ∀ i, i < m → backwardFFT (ω ^ 2) (k + 1) a i
        = dftNat (ν ^ 2) m (fun ℓ => x (2 * ℓ)) i := fun i hi => by
      rw [ih (ω ^ 2) a (fun ℓ => x (2 * ℓ)) i hω2 heven hi, hν2]
    have hc : ∀ i, i < m → backwardFFT (ω ^ 2) (k + 1) (fun s => a (m + s)) i
        = dftNat (ν ^ 2) m (fun ℓ => x (2 * ℓ + 1)) i := fun i hi => by
      rw [ih (ω ^ 2) _ (fun ℓ => x (2 * ℓ + 1)) i hω2 hodd hi, hν2]
    split_ifs with hjm
    · rw [hb j hjm, hc j hjm, htw j (by omega)]
      simp only [dftNat]
      rw [sum_range_two_mul_split, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    · obtain ⟨j', rfl⟩ : ∃ j', j = m + j' := ⟨j - m, by omega⟩
      rw [Nat.add_sub_cancel_left, hb j' (by omega), hc j' (by omega), htw j' (by omega)]
      simp only [dftNat]
      rw [sum_range_two_mul_split, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [show (m + j') * (2 * ℓ) = 2 * m * ℓ + j' * (2 * ℓ) by ring,
        show (m + j') * (2 * ℓ + 1) = 2 * m * ℓ + m + j' * (2 * ℓ + 1) by ring,
        pow_add ν (2 * m * ℓ), pow_add ν (2 * m * ℓ + m), pow_add ν (2 * m * ℓ) m,
        pow_mul ν (2 * m), hνK, one_pow, one_mul, one_mul, hνm]
      ring

/-- `backwardFFT ω k a j` for `j < 2^k` depends only on `a` at positions below `2^k`. -/
theorem backwardFFT_congr (k : ℕ) (ω : R) : ∀ (a b : ℕ → R) (j : ℕ), j < 2 ^ k →
    (∀ s, s < 2 ^ k → a s = b s) → backwardFFT ω k a j = backwardFFT ω k b j := by
  induction k generalizing ω with
  | zero =>
    intro a b j hj hab
    exact hab j hj
  | succ k ih =>
    intro a b j hj hab
    have hK : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    rw [backwardFFT, backwardFFT]
    dsimp only
    split_ifs with hlt
    · rw [ih (ω ^ 2) a b j hlt (fun s hs => hab s (by omega)),
        ih (ω ^ 2) (fun s => a (2 ^ k + s)) (fun s => b (2 ^ k + s)) j hlt
          (fun s hs => hab _ (by omega))]
    · rw [ih (ω ^ 2) a b (j - 2 ^ k) (by omega) (fun s hs => hab s (by omega)),
        ih (ω ^ 2) (fun s => a (2 ^ k + s)) (fun s => b (2 ^ k + s)) (j - 2 ^ k) (by omega)
          (fun s hs => hab _ (by omega))]

/-- **Forward then backward recovers `K · x` in normal order** (Theorems 2.1 and 2.2 with the
inversion formula of §2.3.1), for a principal `K`-th root with `K/2` a unit of `R`. -/
theorem backwardFFT_forwardFFT (k : ℕ) {ω : R} (h : IsPrincipalRoot ω (2 ^ (k + 1)))
    (hu : IsUnit ((2 ^ k : ℕ) : R)) (x : Fin (2 ^ (k + 1)) → R) (j : Fin (2 ^ (k + 1))) :
    backwardFFT ω (k + 1) (forwardFFT ω (k + 1) (extendZero x)) j
      = ((2 ^ (k + 1) : ℕ) : R) * x j := by
  have h' : IsPrincipalRoot ω (2 * 2 ^ k) := by rwa [← pow_succ']
  have hω : ω ^ 2 ^ k = -1 := h'.pow_half_eq_neg_one (Nat.two_pow_pos k) hu
  have : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  rw [backwardFFT_eq_dftNat k ω _ (extendZero (dft ω x)) j hω ?_ j.isLt, ← dft_eq_dftNat]
  · exact dftInv_dft_apply h x j
  · intro r hr
    rw [forwardFFT_eq_dftNat k ω _ r hω hr, extendZero, dite_eq_left (bitrev_lt (k + 1) r),
      dft_eq_dftNat]

end BZ

end Azurite
