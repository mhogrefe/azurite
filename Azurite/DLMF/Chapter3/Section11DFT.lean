/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# DLMF §3.11(v): the discrete and the fast Fourier transform

Formalizations of the Example "The Discrete Fourier Transform" and of "The Fast Fourier
Transform" in <https://dlmf.nist.gov/3.11.v>.

* `dftPhi` (`φₖ(x) = e^{ikx}`), `dftNode` (`x_j = 2πj/n`), `omegaN` (`ωₙ = e^{2πi/n}`);
  `dftPhi_node`: `φₖ(x_j) = ωₙ^{jk}`.
* 3.11.37 (orthogonality): `dlmf_3_11_37`.
* 3.11.38–3.11.39: the coefficients 3.11.39 solve 3.11.38 (`dlmf_3_11_39`), and they are the only
  solution (`dlmf_3_11_39_unique`); "the corresponding sum (3.11.32) vanishes"
  (`dlmf_3_11_v_dft_residual`, read with `|·|²`, see `docs/dlmf_errata.md`).
* 3.11.41: `dlmf_3_11_41` (`f_j = ∑ aₖωₙ^{jk}` is 3.11.38).
* 3.11.42: `dlmf_3_11_42` (`ωₙ^{2(k − n/2)} = ω_{n/2}^k`, `n` even, integer powers).
* The FFT for `n = 2^m` (Cooley–Tukey radix-2 splitting, `fftL`): it computes 3.11.41
  (`dlmf_3_11_v_fft`) with exactly `m 2^{m−1} = ½ n log₂ n` complex multiplications and
  `m 2^m = n log₂ n` additions/subtractions (`dlmf_3_11_v_fft_ops`), the twiddle factors `ωₙ^j`
  being tabulated; the direct sum uses `n²` products `aₖωₙ^{jk}`, more than `n log₂ n` for every
  `n = 2^m` (`dlmf_3_11_v_fft_fewer`).

The DLMF's description of the factorization of `Ω` into `m` sparse matrices is the matrix form of
the recursion `fftL`; it is not formalized separately.
-/

open Complex Finset

namespace Azurite.DLMF

/-- `ωₙ = e^{2πi/n}` (3.11.41). -/
noncomputable def omegaN (n : ℕ) : ℂ := exp (2 * Real.pi * I / n)

/-- `φₖ(x) = e^{ikx}`. -/
noncomputable def dftPhi (k : ℕ) (x : ℝ) : ℂ := exp (I * k * x)

/-- `x_j = 2πj/n`. -/
noncomputable def dftNode (n j : ℕ) : ℝ := 2 * Real.pi * j / n

theorem omegaN_prim {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (omegaN n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem dftPhi_node (n k j : ℕ) : dftPhi k (dftNode n j) = omegaN n ^ (j * k) := by
  rw [dftPhi, dftNode, omegaN, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem conj_omegaN (n : ℕ) : (starRingEnd ℂ) (omegaN n) = (omegaN n)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

theorem geom_omegaN {n : ℕ} (hn : n ≠ 0) (k l : ℕ) (hk : k < n) (hl : l < n) :
    ∑ j ∈ range n, (omegaN n ^ k * (omegaN n ^ l)⁻¹) ^ j = if k = l then (n : ℂ) else 0 := by
  have hp := omegaN_prim hn
  have h0 : omegaN n ≠ 0 := hp.ne_zero hn
  split_ifs with hkl
  · subst hkl; simp [h0]
  · set ζ := omegaN n ^ k * (omegaN n ^ l)⁻¹
    have hζn : ζ ^ n = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hp.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      have : omegaN n ^ k = omegaN n ^ l := by
        have := congrArg (· * omegaN n ^ l) h1
        simpa [ζ, h0, pow_ne_zero] using this
      exact hkl (hp.pow_inj hk hl this)
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div]

/-- **DLMF 3.11.37**: `∑_{j<n} φₖ(x_j) conj φ_ℓ(x_j) = n δ_{kℓ}`, `0 ≤ k, ℓ ≤ n − 1`. -/
theorem dlmf_3_11_37 {n : ℕ} (hn : n ≠ 0) (k l : ℕ) (hk : k < n) (hl : l < n) :
    ∑ j ∈ range n, dftPhi k (dftNode n j) * (starRingEnd ℂ) (dftPhi l (dftNode n j)) =
      if k = l then (n : ℂ) else 0 := by
  rw [← geom_omegaN hn k l hk hl]
  refine sum_congr rfl fun j _ => ?_
  rw [dftPhi_node, dftPhi_node, map_pow, conj_omegaN, inv_pow, mul_pow, inv_pow, ← pow_mul,
    ← pow_mul, mul_comm k j, mul_comm l j]

/-- **DLMF 3.11.39**: `aₖ = (1/n) ∑_j f_j conj φₖ(x_j)`. -/
noncomputable def dftCoeff (n : ℕ) (f : ℕ → ℂ) (k : ℕ) : ℂ :=
  (1 / n) * ∑ j ∈ range n, f j * (starRingEnd ℂ) (dftPhi k (dftNode n j))

theorem dft_orth_dual {n : ℕ} (hn : n ≠ 0) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ range n, (starRingEnd ℂ) (dftPhi k (dftNode n i)) * dftPhi k (dftNode n j) =
      if j = i then (n : ℂ) else 0 := by
  rw [← dlmf_3_11_37 hn j i hj hi]
  refine sum_congr rfl fun k _ => ?_
  rw [dftPhi_node, dftPhi_node, dftPhi_node, dftPhi_node, mul_comm k i, mul_comm k j, mul_comm]

/-- **DLMF 3.11.38–3.11.39**: the coefficients 3.11.39 solve `f_j = ∑_{k<n} aₖφₖ(x_j)`. -/
theorem dlmf_3_11_39 {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℂ) {j : ℕ} (hj : j < n) :
    f j = ∑ k ∈ range n, dftCoeff n f k * dftPhi k (dftNode n j) := by
  have e : ∑ k ∈ range n, dftCoeff n f k * dftPhi k (dftNode n j) = 1 / n *
      ∑ i ∈ range n, f i * ∑ k ∈ range n,
        (starRingEnd ℂ) (dftPhi k (dftNode n i)) * dftPhi k (dftNode n j) := by
    simp only [dftCoeff, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [e, sum_congr rfl fun i hi => by rw [dft_orth_dual hn (mem_range.mp hi) hj],
    Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (mem_range.mpr hj) h)]
  simp
  field_simp

/-- **DLMF §3.11(v)**: the solution of 3.11.38 is unique, so it is given by 3.11.39. -/
theorem dlmf_3_11_39_unique {n : ℕ} (hn : n ≠ 0) (f a : ℕ → ℂ)
    (ha : ∀ j < n, f j = ∑ k ∈ range n, a k * dftPhi k (dftNode n j)) {k : ℕ} (hk : k < n) :
    a k = dftCoeff n f k := by
  rw [dftCoeff]
  have e : ∑ j ∈ range n, f j * (starRingEnd ℂ) (dftPhi k (dftNode n j)) =
      ∑ l ∈ range n, a l * ∑ j ∈ range n,
        dftPhi l (dftNode n j) * (starRingEnd ℂ) (dftPhi k (dftNode n j)) := by
    rw [sum_congr rfl fun j hj => by rw [ha j (mem_range.mp hj)]]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [e, sum_congr rfl fun l hl => by rw [dlmf_3_11_37 hn l k (mem_range.mp hl) hk],
    Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (fun h => absurd (mem_range.mpr hk) h)]
  simp
  field_simp

/-- **DLMF §3.11(v)**: "With this choice of `aₖ` and `f_j = f(x_j)`, the corresponding sum
(3.11.32) vanishes" (`w = 1`, `|·|²` for complex values). -/
theorem dlmf_3_11_v_dft_residual {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℂ) :
    ∑ j ∈ range n, ‖f (dftNode n j) - ∑ k ∈ range n,
      dftCoeff n (fun i => f (dftNode n i)) k * dftPhi k (dftNode n j)‖ ^ 2 = 0 :=
  sum_eq_zero fun j hj => by
    rw [← dlmf_3_11_39 hn (fun i => f (dftNode n i)) (mem_range.mp hj)]
    simp

/-- **DLMF 3.11.41**: 3.11.38 is `f_j = ∑_{k<n} aₖωₙ^{jk}`. -/
theorem dlmf_3_11_41 (n : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    ∑ k ∈ range n, a k * dftPhi k (dftNode n j) = ∑ k ∈ range n, a k * omegaN n ^ (j * k) :=
  sum_congr rfl fun k _ => by rw [dftPhi_node]

theorem omegaN_two_mul_sq (N : ℕ) : omegaN (2 * N) ^ 2 = omegaN N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [omegaN]
  rw [omegaN, omegaN, ← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem omegaN_two_mul_pow_half {N : ℕ} (hN : N ≠ 0) : omegaN (2 * N) ^ N = -1 := by
  rw [omegaN, ← Complex.exp_nat_mul]
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have e : (N : ℂ) * (2 * Real.pi * I / ((2 * N : ℕ) : ℂ)) = Real.pi * I := by
    push_cast; field_simp
  rw [e, Complex.exp_pi_mul_I]

/-- **DLMF 3.11.42**: `ωₙ^{2(k − n/2)} = ω_{n/2}^k` (`n = 2N` even, `k ∈ ℤ`). -/
theorem dlmf_3_11_42 {N : ℕ} (hN : N ≠ 0) (k : ℤ) :
    omegaN (2 * N) ^ (2 * (k - ((2 * N : ℕ) : ℤ) / 2)) = omegaN N ^ k := by
  have h0 : omegaN (2 * N) ≠ 0 := Complex.exp_ne_zero _
  have hdiv : ((2 * N : ℕ) : ℤ) / 2 = N := by push_cast; omega
  have A : omegaN (2 * N) ^ (2 * k) = omegaN N ^ k := by
    rw [zpow_mul, show omegaN (2 * N) ^ (2 : ℤ) = omegaN (2 * N) ^ 2 from zpow_ofNat _ 2,
      omegaN_two_mul_sq]
  have B : omegaN (2 * N) ^ (2 * (N : ℤ)) = 1 := by
    rw [show 2 * (N : ℤ) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      (omegaN_prim (by omega)).pow_eq_one]
  rw [hdiv, mul_sub, zpow_sub₀ h0, A, B, div_one]

/-! ### The fast Fourier transform -/

/-- The direct sums 3.11.41 for `n = 2^m`, as a list. -/
noncomputable def dftList (m : ℕ) (a : ℕ → ℂ) : List ℂ :=
  (List.range (2 ^ m)).map fun j => ∑ k ∈ range (2 ^ m), a k * omegaN (2 ^ m) ^ (j * k)

/-- The radix-2 (Cooley–Tukey) FFT for `n = 2^m`, instrumented: it returns the transform, the
number of complex multiplications and the number of complex additions/subtractions performed.
The transforms `E`, `O` of the even and odd coefficients are combined by the butterflies
`E_j ± ωₙ^j O_j`, `j < n/2`, with `ωₙ^j` tabulated. -/
noncomputable def fftL : ℕ → (ℕ → ℂ) → List ℂ × ℕ × ℕ
  | 0, a => ([a 0], 0, 0)
  | m + 1, a =>
    let E := fftL m fun k => a (2 * k)
    let O := fftL m fun k => a (2 * k + 1)
    let T := (List.range (2 ^ m)).map fun j => omegaN (2 ^ (m + 1)) ^ j * O.1.getD j 0
    ((List.range (2 ^ m)).map (fun j => E.1.getD j 0 + T.getD j 0) ++
        (List.range (2 ^ m)).map (fun j => E.1.getD j 0 - T.getD j 0),
      E.2.1 + O.2.1 + 2 ^ m, E.2.2 + O.2.2 + 2 * 2 ^ m)

theorem getD_map_range {N j : ℕ} (g : ℕ → ℂ) (hj : j < N) :
    ((List.range N).map g).getD j 0 = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem sum_range_two_mul_even_odd (g : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (2 * N), g k = ∑ k ∈ range N, (g (2 * k) + g (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

theorem omegaN_pow_mod {N : ℕ} (hN : N ≠ 0) (e : ℕ) : omegaN N ^ e = omegaN N ^ (e % N) := by
  conv_lhs => rw [← Nat.div_add_mod e N, pow_add, pow_mul, (omegaN_prim hN).pow_eq_one, one_pow,
    one_mul]

/-- The even/odd splitting of the direct sum. -/
theorem dft_split (N : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    ∑ k ∈ range (2 * N), a k * omegaN (2 * N) ^ (j * k) =
      ∑ k ∈ range N, a (2 * k) * omegaN N ^ (j * k) +
        omegaN (2 * N) ^ j * ∑ k ∈ range N, a (2 * k + 1) * omegaN N ^ (j * k) := by
  rw [sum_range_two_mul_even_odd, sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [show j * (2 * k) = 2 * (j * k) by ring, pow_mul, omegaN_two_mul_sq]
  · refine sum_congr rfl fun k _ => ?_
    rw [show j * (2 * k + 1) = 2 * (j * k) + j by ring, pow_add, pow_mul, omegaN_two_mul_sq]
    ring

theorem fftL_length (m : ℕ) (a : ℕ → ℂ) : (fftL m a).1.length = 2 ^ m := by
  induction m generalizing a with
  | zero => simp [fftL]
  | succ m _ => simp [fftL, pow_succ]; ring

/-- **DLMF §3.11(v)**: for `n = 2^m` the FFT computes the discrete Fourier transform 3.11.41. -/
theorem dlmf_3_11_v_fft (m : ℕ) (a : ℕ → ℂ) : (fftL m a).1 = dftList m a := by
  induction m generalizing a with
  | zero => simp [fftL, dftList]
  | succ m ih =>
    have hN : (2 : ℕ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
    have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    simp only [fftL, ih]
    apply List.ext_getElem
    · simp [dftList, e2]; ring
    intro j h1 h2
    simp only [dftList, List.length_map, List.length_range] at h2
    rw [List.getElem_append]
    simp only [dftList, List.getElem_map, List.getElem_range, e2]
    rw [dft_split]
    split_ifs with hj
    · simp only [List.length_map, List.length_range] at hj
      rw [getD_map_range _ hj, getD_map_range _ hj, getD_map_range _ hj]
    · simp only [List.length_map, List.length_range, not_lt] at hj
      have hj' : j - 2 ^ m < 2 ^ m := by omega
      simp only [List.length_map, List.length_range]
      rw [getD_map_range _ hj', getD_map_range _ hj', getD_map_range _ hj']
      have hw : omegaN (2 * 2 ^ m) ^ j = -omegaN (2 * 2 ^ m) ^ (j - 2 ^ m) := by
        conv_lhs => rw [show j = j - 2 ^ m + 2 ^ m by omega, pow_add,
          omegaN_two_mul_pow_half hN]
        ring
      have hp : ∀ k, omegaN (2 ^ m) ^ (j * k) = omegaN (2 ^ m) ^ ((j - 2 ^ m) * k) := by
        intro k
        rw [omegaN_pow_mod hN, omegaN_pow_mod hN ((j - 2 ^ m) * k), Nat.mul_mod,
          Nat.mul_mod (j - 2 ^ m)]
        congr 3
        conv_lhs => rw [show j = j - 2 ^ m + 2 ^ m by omega]
        simp
      simp only [hw, hp]
      ring

/-- **DLMF §3.11(v)**: the FFT for `n = 2^m` takes `½nm` multiplications and `nm` additions,
`nm = n log₂ n`. -/
theorem dlmf_3_11_v_fft_ops (m : ℕ) (a : ℕ → ℂ) :
    2 * (fftL m a).2.1 = 2 ^ m * m ∧ (fftL m a).2.2 = 2 ^ m * m := by
  induction m generalizing a with
  | zero => simp [fftL]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih fun k => a (2 * k)
    obtain ⟨h3, h4⟩ := ih fun k => a (2 * k + 1)
    simp only [fftL]
    constructor
    · rw [mul_add, mul_add, h1, h3]; ring
    · rw [h2, h4]; ring

/-- `n log₂ n < n²` for `n = 2^m`: the FFT count `nm` is below the `n²` products `aₖωₙ^{jk}` of
the direct computation. -/
theorem dlmf_3_11_v_fft_fewer (m : ℕ) : 2 ^ m * m < (2 ^ m) ^ 2 := by
  rw [sq]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self) (by positivity)

theorem fftL_two_pow_log (m : ℕ) : Nat.log 2 (2 ^ m) = m := Nat.log_pow (by norm_num) m

end Azurite.DLMF
