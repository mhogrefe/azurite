/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ShortProduct
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ModPow2

/-!
# Correctness of the short products

* `mulLow_toNat`: the low short product is `A B mod β^n`, exactly (the recursion is an identity
  modulo `β^n`, `mulLow_step_mod`).
* `mulHigh_spec`: **MCA Theorem 3.5** — for `A, B < β^n`, `C' ≤ C ≤ C' + 3(n − 1)` with
  `C = ⌊A B/β^n⌋`, stated as `C' β^n ≤ A B < (C' + 3(n − 1) + 1) β^n`.  The step
  (`mulHigh_step_bounds`, any base `b`) accounts the four dropped or truncated pieces (the
  truncation of `C₁`, the two `ℓ × (k − ℓ)` strips below the recursive products, the `ℓ × ℓ`
  corner), each below `β^n`, plus the recursive errors: `ε(n) ≤ 2 ε(ℓ) + 3`, and `6ℓ ≤ 3n − 2`
  for Mulders' `ℓ = ⌊3n/10⌋`.
-/

namespace Azurite.AzNat

theorem toNat_shl_pow (a : AzNat) (sh : Nat) : (a <<< sh).toNat = a.toNat * 2 ^ sh := by
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq]

theorem toNat_shr_pow (a : AzNat) (sh : Nat) : (a >>> sh).toNat = a.toNat / 2 ^ sh := by
  rw [toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

theorem two_pow_64_mul (k : Nat) : (2 : Nat) ^ (64 * k) = (2 ^ 64) ^ k := pow_mul 2 64 k

theorem shortSplit_le (n : Nat) : 10 * shortSplit n ≤ 3 * n := by
  unfold shortSplit; omega

theorem shortSplit_pos {n : Nat} (h : 4 ≤ n) : 1 ≤ shortSplit n := by
  unfold shortSplit; omega

theorem shortSplit_lt {n : Nat} (h : 1 ≤ n) : shortSplit n < n := by
  unfold shortSplit; omega

/-! ### The low product -/

/-- The recursion of `mulLow` is an identity modulo `b^n` (`n = k + ℓ`, `ℓ ≤ k`). -/
theorem mulLow_step_mod {b n l k A B C2 C3 : ℕ} (hb : 0 < b) (hlk : l ≤ k) (hn : n = k + l)
    (hC2 : C2 % b ^ l = A / b ^ k * (B % b ^ l) % b ^ l)
    (hC3 : C3 % b ^ l = A % b ^ l * (B / b ^ k) % b ^ l) :
    (A % b ^ k * (B % b ^ k) % b ^ n + (C2 + C3) * b ^ k) % b ^ n = A * B % b ^ n := by
  have hK0 : 0 < b ^ k := pow_pos hb k
  have hL0 : 0 < b ^ l := pow_pos hb l
  have hN : b ^ n = b ^ k * b ^ l := by rw [hn, pow_add]
  have hLK : b ^ l ∣ b ^ k := pow_dvd_pow b hlk
  obtain ⟨m, hm⟩ := hLK
  -- `A B` modulo `b^n`
  have hA := Nat.div_add_mod A (b ^ k)
  have hB := Nat.div_add_mod B (b ^ k)
  have hAB : A * B = b ^ k * (A / b ^ k) * (b ^ k * (B / b ^ k))
      + b ^ k * (A / b ^ k * (B % b ^ k) + A % b ^ k * (B / b ^ k)) + A % b ^ k * (B % b ^ k) := by
    calc A * B = (b ^ k * (A / b ^ k) + A % b ^ k) * (b ^ k * (B / b ^ k) + B % b ^ k) := by
          rw [hA, hB]
      _ = _ := by ring
  have hsq : b ^ n ∣ b ^ k * (A / b ^ k) * (b ^ k * (B / b ^ k)) := by
    have h1 : b ^ n ∣ b ^ k * b ^ k := by rw [hN]; exact Nat.mul_dvd_mul_left _ ⟨m, hm⟩
    exact h1.trans ⟨A / b ^ k * (B / b ^ k), by ring⟩
  -- the cross terms modulo `b^l`
  have hBK : B % b ^ k % b ^ l = B % b ^ l := Nat.mod_mod_of_dvd B ⟨m, hm⟩
  have hAK : A % b ^ k % b ^ l = A % b ^ l := Nat.mod_mod_of_dvd A ⟨m, hm⟩
  have h2 : A / b ^ k * (B % b ^ k) ≡ C2 [MOD b ^ l] := by
    have : A / b ^ k * (B % b ^ k) ≡ A / b ^ k * (B % b ^ l) [MOD b ^ l] :=
      Nat.ModEq.mul_left _ (by unfold Nat.ModEq; rw [hBK]; exact Nat.mod_mod _ _ |>.symm ▸ rfl)
    exact this.trans (by unfold Nat.ModEq at *; rw [hC2])
  have h3 : A % b ^ k * (B / b ^ k) ≡ C3 [MOD b ^ l] := by
    have : A % b ^ k * (B / b ^ k) ≡ A % b ^ l * (B / b ^ k) [MOD b ^ l] :=
      Nat.ModEq.mul_right _ (by unfold Nat.ModEq; rw [hAK]; exact Nat.mod_mod _ _ |>.symm ▸ rfl)
    exact this.trans (by unfold Nat.ModEq at *; rw [hC3])
  have hcross : b ^ k * (A / b ^ k * (B % b ^ k) + A % b ^ k * (B / b ^ k))
      ≡ (C2 + C3) * b ^ k [MOD b ^ n] := by
    rw [hN, mul_comm (C2 + C3)]
    exact Nat.ModEq.mul_left' _ (h2.add h3)
  have hfull : A * B ≡ A % b ^ k * (B % b ^ k) + (C2 + C3) * b ^ k [MOD b ^ n] := by
    rw [hAB]
    have h0 : b ^ k * (A / b ^ k) * (b ^ k * (B / b ^ k)) ≡ 0 [MOD b ^ n] :=
      (Nat.modEq_zero_iff_dvd).mpr hsq
    have := (h0.add hcross).add (Nat.ModEq.refl (A % b ^ k * (B % b ^ k)))
    rw [zero_add] at this
    exact this.trans (by rw [add_comm])
  unfold Nat.ModEq at hfull
  rw [hfull, Nat.mod_add_mod]

theorem mulLowFuel_toNat (n₀ : Nat) :
    ∀ (fuel : Nat) (A B : AzNat) (n : Nat),
      (mulLowFuel n₀ fuel A B n).toNat = A.toNat * B.toNat % 2 ^ (64 * n)
  | 0, A, B, n => by simp only [mulLowFuel]; rw [toNat_modPow2, toNat_mul]
  | fuel + 1, A, B, n => by
    by_cases hn : n ≤ n₀
    · simp only [mulLowFuel, hn, ↓reduceIte]; rw [toNat_modPow2, toNat_mul]
    · simp only [mulLowFuel, hn, ↓reduceIte]
      set l := shortSplit n with hl
      set k := n - l with hk
      have hl10 := shortSplit_le n
      have hlk : l ≤ k := by omega
      have hnkl : n = k + l := by omega
      have h2 := mulLowFuel_toNat n₀ fuel (A >>> (64 * k)) (B.modPow2 (64 * l)) l
      have h3 := mulLowFuel_toNat n₀ fuel (A.modPow2 (64 * l)) (B >>> (64 * k)) l
      rw [toNat_shr_pow, toNat_modPow2] at h2 h3
      rw [toNat_modPow2, toNat_add, toNat_shl_pow, toNat_modPow2, toNat_mul, toNat_modPow2,
        toNat_modPow2, toNat_add]
      simp only [two_pow_64_mul] at h2 h3 ⊢
      exact mulLow_step_mod (b := 2 ^ 64) (by norm_num) hlk hnkl
        (by rw [Nat.mod_eq_of_lt (by rw [h2]; exact Nat.mod_lt _ (pow_pos (by norm_num) _)), h2])
        (by rw [Nat.mod_eq_of_lt (by rw [h3]; exact Nat.mod_lt _ (pow_pos (by norm_num) _)), h3])

/-- **The low short product is exact.** -/
theorem mulLow_toNat (n₀ : Nat) (A B : AzNat) (n : Nat) :
    (mulLow n₀ A B n).toNat = A.toNat * B.toNat % 2 ^ (64 * n) :=
  mulLowFuel_toNat n₀ n A B n

/-! ### The high product -/

/-- One step of MCA Algorithm 3.4 (any base `b`): the recursive errors and the three dropped
pieces give `ε(n) ≤ 2 ε(ℓ) + 3 ≤ 3(n − 1)`. -/
theorem mulHigh_step_bounds {b n l k A B C1 C2 C3 : ℕ} (hb : 0 < b) (hl1 : 1 ≤ l)
    (hln : 10 * l ≤ 3 * n) (hk : k = n - l)
    (hC1 : C1 = A / b ^ l * (B / b ^ l) / b ^ (k - l))
    (hC2 : C2 * b ^ l ≤ A % b ^ l * (B / b ^ k))
    (hC2' : A % b ^ l * (B / b ^ k) < (C2 + 3 * (l - 1) + 1) * b ^ l)
    (hC3 : C3 * b ^ l ≤ A / b ^ k * (B % b ^ l))
    (hC3' : A / b ^ k * (B % b ^ l) < (C3 + 3 * (l - 1) + 1) * b ^ l) :
    (C1 + C2 + C3) * b ^ n ≤ A * B ∧ A * B < (C1 + C2 + C3 + 3 * (n - 1) + 1) * b ^ n := by
  have hn4 : 4 ≤ n := by omega
  have hlk : l ≤ k := by omega
  set L := b ^ l with hL
  set K := b ^ k with hK
  set M := b ^ (k - l) with hM
  set N := b ^ n with hN
  have hL0 : 0 < L := pow_pos hb l
  have hK0 : 0 < K := pow_pos hb k
  have hM0 : 0 < M := pow_pos hb _
  have hKML : K = M * L := by rw [hK, hM, hL, ← pow_add]; congr 1; omega
  have hNLK : N = L * K := by rw [hN, hL, hK, ← pow_add]; congr 1; omega
  have hNMLL : N = M * L * L := by rw [hNLK, hKML]; ring
  have hLLN : L * L ≤ N := by
    rw [hN, hL, ← pow_add]; exact Nat.pow_le_pow_right hb (by omega)
  set Ah := A / L with hAh
  set Al := A % L with hAl
  set Bh := B / L with hBh
  set Bl := B % L with hBl
  set Ak := A / K with hAk
  set Bk := B / K with hBk
  have hAeq : A = L * Ah + Al := (Nat.div_add_mod A L).symm
  have hBeq : B = L * Bh + Bl := (Nat.div_add_mod B L).symm
  have hAl_lt : Al < L := Nat.mod_lt _ hL0
  have hBl_lt : Bl < L := Nat.mod_lt _ hL0
  have hAk_eq : Ak = Ah / M := by rw [hAk, hAh, Nat.div_div_eq_div_mul, hKML, mul_comm]
  have hBk_eq : Bk = Bh / M := by rw [hBk, hBh, Nat.div_div_eq_div_mul, hKML, mul_comm]
  have hAh_eq : Ah = M * Ak + Ah % M := by rw [hAk_eq]; exact (Nat.div_add_mod Ah M).symm
  have hBh_eq : Bh = M * Bk + Bh % M := by rw [hBk_eq]; exact (Nat.div_add_mod Bh M).symm
  have hAm_lt : Ah % M < M := Nat.mod_lt _ hM0
  have hBm_lt : Bh % M < M := Nat.mod_lt _ hM0
  have hAB : A * B = Ah * Bh * (L * L) + Ah * Bl * L + Al * Bh * L + Al * Bl := by
    rw [hAeq, hBeq]; ring
  -- `C₁`
  have hC1a : C1 * M ≤ Ah * Bh := by rw [hC1]; exact Nat.div_mul_le_self _ _
  have hC1b : Ah * Bh < M * (C1 + 1) := by rw [hC1]; exact Nat.lt_mul_div_succ _ hM0
  constructor
  · -- lower bound
    have e1 : C1 * N ≤ Ah * Bh * (L * L) := by
      calc C1 * N = C1 * M * (L * L) := by rw [hNMLL]; ring
        _ ≤ Ah * Bh * (L * L) := Nat.mul_le_mul_right _ hC1a
    have e2 : C2 * N ≤ Al * Bh * L := by
      calc C2 * N = C2 * L * K := by rw [hNLK]; ring
        _ ≤ Al * Bk * K := Nat.mul_le_mul_right _ hC2
        _ = Al * (M * Bk) * L := by rw [hKML]; ring
        _ ≤ Al * Bh * L := by
            have : M * Bk ≤ Bh := by rw [hBh_eq]; exact Nat.le_add_right _ _
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
    have e3 : C3 * N ≤ Ah * Bl * L := by
      calc C3 * N = C3 * L * K := by rw [hNLK]; ring
        _ ≤ Ak * Bl * K := Nat.mul_le_mul_right _ hC3
        _ = (M * Ak) * Bl * L := by rw [hKML]; ring
        _ ≤ Ah * Bl * L := by
            have : M * Ak ≤ Ah := by rw [hAh_eq]; exact Nat.le_add_right _ _
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    have : (C1 + C2 + C3) * N = C1 * N + C2 * N + C3 * N := by ring
    rw [this, hAB]
    omega
  · -- upper bound
    have u1 : Ah * Bh * (L * L) < (C1 + 1) * N := by
      calc Ah * Bh * (L * L) < M * (C1 + 1) * (L * L) := Nat.mul_lt_mul_of_pos_right hC1b (by positivity)
        _ = (C1 + 1) * N := by rw [hNMLL]; ring
    have u2 : Al * Bh * L < (C2 + 3 * (l - 1) + 1) * N + N := by
      have hsplit : Al * Bh * L = Al * Bk * K + Al * (Bh % M) * L := by
        calc Al * Bh * L = Al * (M * Bk + Bh % M) * L := by rw [← hBh_eq]
          _ = Al * Bk * K + Al * (Bh % M) * L := by rw [hKML]; ring
      have ha : Al * Bk * K < (C2 + 3 * (l - 1) + 1) * N := by
        calc Al * Bk * K < (C2 + 3 * (l - 1) + 1) * L * K := Nat.mul_lt_mul_of_pos_right hC2' hK0
          _ = (C2 + 3 * (l - 1) + 1) * N := by rw [hNLK]; ring
      have hb' : Al * (Bh % M) * L < N := by
        calc Al * (Bh % M) * L < L * M * L := by
              apply Nat.mul_lt_mul_of_pos_right _ hL0
              exact Nat.mul_lt_mul'' hAl_lt hBm_lt
          _ = N := by rw [hNMLL]; ring
      omega
    have u3 : Ah * Bl * L < (C3 + 3 * (l - 1) + 1) * N + N := by
      have hsplit : Ah * Bl * L = Ak * Bl * K + (Ah % M) * Bl * L := by
        calc Ah * Bl * L = (M * Ak + Ah % M) * Bl * L := by rw [← hAh_eq]
          _ = Ak * Bl * K + (Ah % M) * Bl * L := by rw [hKML]; ring
      have ha : Ak * Bl * K < (C3 + 3 * (l - 1) + 1) * N := by
        calc Ak * Bl * K < (C3 + 3 * (l - 1) + 1) * L * K := Nat.mul_lt_mul_of_pos_right hC3' hK0
          _ = (C3 + 3 * (l - 1) + 1) * N := by rw [hNLK]; ring
      have hb' : (Ah % M) * Bl * L < N := by
        calc (Ah % M) * Bl * L < M * L * L := by
              apply Nat.mul_lt_mul_of_pos_right _ hL0
              exact Nat.mul_lt_mul'' hAm_lt hBl_lt
          _ = N := hNMLL.symm
      omega
    have u4 : Al * Bl < N := lt_of_lt_of_le (Nat.mul_lt_mul'' hAl_lt hBl_lt) hLLN
    have hsum : (C1 + 1) * N + ((C2 + 3 * (l - 1) + 1) * N + N) + ((C3 + 3 * (l - 1) + 1) * N + N)
        + N = (C1 + C2 + C3 + 6 * l) * N := by
      have : 6 * (l - 1) + 6 = 6 * l := by omega
      calc _ = (C1 + C2 + C3 + (6 * (l - 1) + 6)) * N := by ring
        _ = _ := by rw [this]
    have hfin : (C1 + C2 + C3 + 6 * l) * N ≤ (C1 + C2 + C3 + 3 * (n - 1) + 1) * N :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hAB]
    omega

theorem mulHighFuel_spec (n₀ : Nat) (hn₀ : 3 ≤ n₀) :
    ∀ (fuel : Nat) (A B : AzNat) (n : Nat), n ≤ fuel + n₀ →
      A.toNat < 2 ^ (64 * n) → B.toNat < 2 ^ (64 * n) →
      (mulHighFuel n₀ fuel A B n).toNat * 2 ^ (64 * n) ≤ A.toNat * B.toNat ∧
        A.toNat * B.toNat < ((mulHighFuel n₀ fuel A B n).toNat + 3 * (n - 1) + 1) * 2 ^ (64 * n)
  | 0, A, B, n, _, _, _ => by
    simp only [mulHighFuel]
    rw [toNat_shr_pow, toNat_mul]
    have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
    refine ⟨Nat.div_mul_le_self _ _, ?_⟩
    have := Nat.lt_mul_div_succ (A.toNat * B.toNat) hb0
    calc A.toNat * B.toNat < 2 ^ (64 * n) * (A.toNat * B.toNat / 2 ^ (64 * n) + 1) := this
      _ ≤ (A.toNat * B.toNat / 2 ^ (64 * n) + 3 * (n - 1) + 1) * 2 ^ (64 * n) := by
          rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  | fuel + 1, A, B, n, hnf, hA, hB => by
    by_cases hn : n ≤ n₀
    · simp only [mulHighFuel, hn, ↓reduceIte]
      rw [toNat_shr_pow, toNat_mul]
      have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
      refine ⟨Nat.div_mul_le_self _ _, ?_⟩
      have := Nat.lt_mul_div_succ (A.toNat * B.toNat) hb0
      calc A.toNat * B.toNat < 2 ^ (64 * n) * (A.toNat * B.toNat / 2 ^ (64 * n) + 1) := this
        _ ≤ (A.toNat * B.toNat / 2 ^ (64 * n) + 3 * (n - 1) + 1) * 2 ^ (64 * n) := by
            rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    · simp only [mulHighFuel, hn, ↓reduceIte]
      set l := shortSplit n with hl
      set k := n - l with hk
      have hl10 := shortSplit_le n
      have hl1 : 1 ≤ l := shortSplit_pos (by omega)
      have hL0 : 0 < (2 : ℕ) ^ (64 * l) := Nat.two_pow_pos _
      have hK0 : 0 < (2 : ℕ) ^ (64 * k) := Nat.two_pow_pos _
      have hnkl : (2 : ℕ) ^ (64 * n) = 2 ^ (64 * k) * 2 ^ (64 * l) := by
        rw [← pow_add]; congr 1; omega
      have hBk : (B >>> (64 * k)).toNat < 2 ^ (64 * l) := by
        rw [toNat_shr_pow, Nat.div_lt_iff_lt_mul hK0, mul_comm, ← hnkl]; exact hB
      have hAk : (A >>> (64 * k)).toNat < 2 ^ (64 * l) := by
        rw [toNat_shr_pow, Nat.div_lt_iff_lt_mul hK0, mul_comm, ← hnkl]; exact hA
      have hAl : (A.modPow2 (64 * l)).toNat < 2 ^ (64 * l) := by
        rw [toNat_modPow2]; exact Nat.mod_lt _ hL0
      have hBl : (B.modPow2 (64 * l)).toNat < 2 ^ (64 * l) := by
        rw [toNat_modPow2]; exact Nat.mod_lt _ hL0
      obtain ⟨h2, h2'⟩ := mulHighFuel_spec n₀ hn₀ fuel (A.modPow2 (64 * l)) (B >>> (64 * k)) l
        (by omega) hAl hBk
      obtain ⟨h3, h3'⟩ := mulHighFuel_spec n₀ hn₀ fuel (A >>> (64 * k)) (B.modPow2 (64 * l)) l
        (by omega) hAk hBl
      rw [toNat_modPow2, toNat_shr_pow] at h2 h2' h3 h3'
      rw [toNat_add, toNat_add, toNat_shr_pow, toNat_mul, toNat_shr_pow, toNat_shr_pow]
      simp only [two_pow_64_mul] at h2 h2' h3 h3' hA hB ⊢
      exact mulHigh_step_bounds (b := 2 ^ 64) (by norm_num) hl1 hl10 hk rfl h2 h2' h3 h3'

/-- **MCA Theorem 3.5**: for `A, B < β^n`, `mulHigh n₀ A B n` is within `3(n − 1)` of
`⌊A B/β^n⌋` from below (`n₀ ≥ 3`). -/
theorem mulHigh_spec (n₀ : Nat) (hn₀ : 3 ≤ n₀) (A B : AzNat) (n : Nat)
    (hA : A.toNat < 2 ^ (64 * n)) (hB : B.toNat < 2 ^ (64 * n)) :
    (mulHigh n₀ A B n).toNat * 2 ^ (64 * n) ≤ A.toNat * B.toNat ∧
      A.toNat * B.toNat < ((mulHigh n₀ A B n).toNat + 3 * (n - 1) + 1) * 2 ^ (64 * n) :=
  mulHighFuel_spec n₀ hn₀ n A B n (by omega) hA hB

end Azurite.AzNat
