/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9Aitken
import Azurite.DLMF.Chapter3.Section9Hankel

/-!
# DLMF §3.9(iv): Shanks' transformation

* 3.9.9 (`shanks`): `t_{n,2k} = H_{k+1}(sₙ)/H_k(Δ²sₙ)`, with the Hankel determinants 3.9.10
  (`hankel`, in `Section9Hankel`).
* "Aitken's Δ²-process is the case `k = 1`" (`shanks_one`).
* 3.9.11 (`wynnEps`): Wynn's epsilon algorithm `ε_{−1}^{(n)} = 0`, `ε_0^{(n)} = sₙ`,
  `ε_{m+1}^{(n)} = ε_{m−1}^{(n+1)} + 1/(ε_m^{(n+1)} − ε_m^{(n)})`; here `ε_m^{(n)}` is
  `wynnEps s (m + 1) n`.
* "Then `t_{n,2k} = ε_{2k}^{(n)}`" (`dlmf_3_9_11`), together with the odd entries
  `ε_{2k+1}^{(n)} = H_k(Δ³sₙ)/H_{k+1}(Δsₙ)`, provided the Hankel determinants `H_k(Δ²sₙ)` and
  `H_k(Δsₙ)` that occur do not vanish (so that the ratios are defined). The proof uses the
  Hankel identities `hankel_J1`, `hankel_J2` (Desnanot–Jacobi). The case `k = 1` directly:
  `wynnEps_three`.
* "If `sₙ` is the `n`th partial sum of a power series `f`, then `t_{n,2k} = ε_{2k}^{(n)}` is the
  Padé approximant `[(n + k)/k]_f` (§3.11(iv))": not formalized (§3.11 is not yet available).
* Brezinski and Redivo Zaglia (1991) is not formalized.
-/

open Matrix

namespace Azurite.DLMF

variable {𝕜 : Type*} [Field 𝕜]

/-- **DLMF 3.9.9**: Shanks' transformation `t_{n,2k} = H_{k+1}(sₙ)/H_k(Δ²sₙ)`. -/
noncomputable def shanks (k : ℕ) : (ℕ → 𝕜) → (ℕ → 𝕜) := fun s n =>
  hankel s (k + 1) n / hankel (fwdDiff 1 (fwdDiff 1 s)) k n

theorem hankel_zero (u : ℕ → 𝕜) (n : ℕ) : hankel u 0 n = 1 := by
  simp [hankel]

theorem hankel_one (u : ℕ → 𝕜) (n : ℕ) : hankel u 1 n = u n := by
  simp [hankel]

theorem hankel_two (u : ℕ → 𝕜) (n : ℕ) :
    hankel u 2 n = u n * u (n + 2) - u (n + 1) ^ 2 := by
  simp [hankel, det_fin_two]
  ring_nf

section Aitken

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF §3.9(iv)**: "Aitken's Δ²-process is the case `k = 1`". -/
theorem shanks_one {s : ℕ → 𝕜} {n : ℕ} (h : s (n + 2) - 2 * s (n + 1) + s n ≠ 0) :
    shanks 1 s n = aitken s n := by
  have e : fwdDiff 1 (fwdDiff 1 s) n = s (n + 2) - 2 * s (n + 1) + s n := by
    simp only [fwdDiff]; ring_nf
  rw [shanks, hankel_two, hankel_one, e]
  simp only [aitken]
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff h]
  ring

end Aitken

/-- **DLMF 3.9.11**: Wynn's epsilon algorithm; `wynnEps s (m + 1) n = ε_m^{(n)}`
(`ε_{−1}^{(n)} = 0`, `ε_0^{(n)} = sₙ`). -/
def wynnEps (s : ℕ → 𝕜) : ℕ → ℕ → 𝕜
  | 0, _ => 0
  | 1, n => s n
  | m + 2, n => wynnEps s m (n + 1) + 1 / (wynnEps s (m + 1) (n + 1) - wynnEps s (m + 1) n)

theorem wynnEps_succ_succ (s : ℕ → 𝕜) (m n : ℕ) :
    wynnEps s (m + 2) n =
      wynnEps s m (n + 1) + 1 / (wynnEps s (m + 1) (n + 1) - wynnEps s (m + 1) n) := rfl

/-- `ε_2^{(n)}` is Aitken's `tₙ` (when the differences do not vanish). -/
theorem wynnEps_three {𝕜 : Type*} [NormedField 𝕜] {s : ℕ → 𝕜} {n : ℕ} (h0 : s (n + 1) - s n ≠ 0)
    (h1 : s (n + 2) - s (n + 1) ≠ 0) (h2 : s (n + 2) - 2 * s (n + 1) + s n ≠ 0) :
    wynnEps s 3 n = aitken s n := by
  simp only [wynnEps, zero_add]
  simp only [aitken]
  rw [show n + 1 + 1 = n + 2 from rfl, div_sub_div _ _ h1 h0, one_div_div,
    show (1 * (s (n + 1) - s n) - (s (n + 2) - s (n + 1)) * 1) =
      -(s (n + 2) - 2 * s (n + 1) + s n) by ring, div_neg]
  have key : (s (n + 2) - s (n + 1)) * (s (n + 1) - s n) / (s (n + 2) - 2 * s (n + 1) + s n) -
      (s (n + 1) - s n) ^ 2 / (s (n + 2) - 2 * s (n + 1) + s n) = s (n + 1) - s n := by
    rw [← sub_div, div_eq_iff h2]; ring
  linear_combination -key

/-- **DLMF 3.9.11**: "Then `t_{n,2k} = ε_{2k}^{(n)}`", and
`ε_{2k+1}^{(n)} = H_k(Δ³sₙ)/H_{k+1}(Δsₙ)`, for `k ≤ K`, provided `H_k(Δ²sₙ) ≠ 0` and
`H_k(Δsₙ) ≠ 0` for `k ≤ K` and all `n`. -/
theorem dlmf_3_9_11 (s : ℕ → 𝕜) (K : ℕ)
    (hD : ∀ k ≤ K, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 s)) k n ≠ 0)
    (hQ : ∀ k ≤ K, ∀ n, hankel (fwdDiff 1 s) k n ≠ 0) :
    ∀ k ≤ K, (∀ n, wynnEps s (2 * k + 1) n = shanks k s n) ∧
      (k < K → ∀ n, wynnEps s (2 * k + 2) n =
        hankel (fwdDiff 1 (fwdDiff 1 (fwdDiff 1 s))) k n / hankel (fwdDiff 1 s) (k + 1) n) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun n => ?_, fun hK n => ?_⟩
    · simp [wynnEps, shanks, hankel_zero, hankel_one]
    · have hq := hQ 1 hK n
      rw [hankel_one] at hq
      simp only [wynnEps, hankel_zero, hankel_one, zero_add]
      simp only [fwdDiff] at hq ⊢
  | succ k ih =>
    intro hk
    obtain ⟨hE, hO⟩ := ih (by omega)
    have hO' := hO (by omega)
    -- the even entry `ε_{2k+2}`
    have hE' : ∀ n, wynnEps s (2 * (k + 1) + 1) n = shanks (k + 1) s n := by
      intro n
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, wynnEps_succ_succ, hE,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring, hO', hO']
      have hDk1 := hD k (by omega) (n + 1)
      have hDk1' := hD (k + 1) hk n
      have hQn := hQ (k + 1) hk n
      have hQn1 := hQ (k + 1) hk (n + 1)
      -- `Q^{n+1} P^n − Q^n P^{n+1} = D_{k+1}^n D_k^{n+1}`
      have hI3 := hankel_J1 (fwdDiff 1 s) n k hDk1
      -- `N'^n D_k^{n+1} − N^{n+1} D_{k+1}^n = −Q^n Q^{n+1}`
      have hI4 := hankel_J2 s n k (hQ k (by omega) (n + 1))
      simp only [shanks, show k + 1 + 1 = k + 2 from rfl]
      have hdiff : hankel (fwdDiff 1 (fwdDiff 1 (fwdDiff 1 s))) k (n + 1) /
            hankel (fwdDiff 1 s) (k + 1) (n + 1) -
          hankel (fwdDiff 1 (fwdDiff 1 (fwdDiff 1 s))) k n / hankel (fwdDiff 1 s) (k + 1) n =
          -(hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) n *
            hankel (fwdDiff 1 (fwdDiff 1 s)) k (n + 1)) /
            (hankel (fwdDiff 1 s) (k + 1) n * hankel (fwdDiff 1 s) (k + 1) (n + 1)) := by
        rw [div_sub_div _ _ hQn1 hQn, div_eq_div_iff (mul_ne_zero hQn1 hQn)
          (mul_ne_zero hQn hQn1)]
        linear_combination (-(hankel (fwdDiff 1 s) (k + 1) n *
          hankel (fwdDiff 1 s) (k + 1) (n + 1))) * hI3
      rw [hdiff, one_div_div, div_neg, ← sub_eq_add_neg,
        div_sub_div _ _ hDk1 (mul_ne_zero hDk1' hDk1),
        div_eq_div_iff (mul_ne_zero hDk1 (mul_ne_zero hDk1' hDk1)) hDk1']
      linear_combination (-(hankel (fwdDiff 1 (fwdDiff 1 s)) k (n + 1) *
        hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) n)) * hI4
    refine ⟨hE', fun hK n => ?_⟩
    -- the odd entry `ε_{2k+3}`
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, wynnEps_succ_succ, hO',
      show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring, hE', hE']
    have hDk1 := hD k (by omega) (n + 1)
    have hD1n := hD (k + 1) hk n
    have hD1n1 := hD (k + 1) hk (n + 1)
    have hQ1n1 := hQ (k + 1) hk (n + 1)
    have hQ2n := hQ (k + 2) hK n
    have hQ1n := hQ (k + 1) hk n
    have hJ1 := hankel_J1 s n (k + 1) hQ1n1
    simp only [show k + 1 + 1 = k + 2 from rfl] at hJ1
    have hJ2 := hankel_J2 (fwdDiff 1 s) n k hDk1
    simp only [shanks, show k + 1 + 1 = k + 2 from rfl]
    have hdiff : hankel s (k + 2) (n + 1) / hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) (n + 1) -
        hankel s (k + 2) n / hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) n =
        hankel (fwdDiff 1 s) (k + 2) n * hankel (fwdDiff 1 s) (k + 1) (n + 1) /
          (hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) n *
            hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) (n + 1)) := by
      rw [div_sub_div _ _ hD1n1 hD1n, div_eq_div_iff (mul_ne_zero hD1n1 hD1n)
        (mul_ne_zero hD1n hD1n1)]
      linear_combination (hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) n *
        hankel (fwdDiff 1 (fwdDiff 1 s)) (k + 1) (n + 1)) * hJ1
    rw [hdiff, one_div_div, div_add_div _ _ hQ1n1 (mul_ne_zero hQ2n hQ1n1),
      div_eq_div_iff (mul_ne_zero hQ1n1 (mul_ne_zero hQ2n hQ1n1)) hQ2n]
    linear_combination (hankel (fwdDiff 1 s) (k + 1) (n + 1) * hankel (fwdDiff 1 s) (k + 2) n) * hJ2

end Azurite.DLMF
