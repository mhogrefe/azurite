/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnSmooth
import Azurite.AzFloat.Equiv.EnclWidth

/-!
# The width of the logarithm of a smooth integer

* `atanhInvBracket_width`: the bracket of `atanh (1/q)` at `k` bits has width at most
  `20 · 2^(−k)`.
* `AEncl.natMul`: an enclosure with a nonnegative lower end times an exact natural number.
* **`lnSmoothBracket_width`**: the bracket of `a ln 2 + b ln 3 + c ln 5 + d ln 7` at `k` bits
  has width at most `2^(−k)`, whatever the exponents — the four series are bracketed at
  `k + ⌊lg (K₁ + K₂ + K₃ + K₄)⌋ + 8` bits, which pays for their coefficients.
* `divOut_spec`, `smoothExps_spec`, `isSmooth_spec`, `isSmooth_two_pow`, `isSmooth_nextSmooth`:
  `nextSmooth n` (`n ≥ 1`) has no prime factor above `7` — a power of two lies in `[n, 2n)` —
  and is the product of the powers that `smoothExps` reads off.
-/

namespace Azurite.AzFloat

open Finset BZ

/-- `atanh (1/q) ≤ 1` for `q ≥ 2`. -/
theorem atanhInv_le_one {q : ℝ} (hq : 2 ≤ q) : atanhInv q ≤ 1 := by
  rw [atanhInv_eq (by linarith)]
  have h3 : (q + 1) / (q - 1) ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hpos : 0 < (q + 1) / (q - 1) := div_pos (by linarith) (by linarith)
  have hlog : Real.log ((q + 1) / (q - 1)) ≤ 2 := by
    rw [Real.log_le_iff_le_exp hpos]
    have h1 := Real.add_one_le_exp (2 : ℝ)
    linarith
  linarith

/-- **The width of the bracket of `atanh (1/q)`**: at most `20 · 2^(−k)`, with a nonnegative
lower end. -/
theorem atanhInvBracket_width {q : ℕ} (hq : 2 ≤ q) {k : ℕ} (hk : 4 ≤ k) :
    ∃ lv hv : ℝ, (atanhInvBracket q k).1.toVal = some (lv : EReal) ∧
      (atanhInvBracket q k).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv ≤ atanhInv q ∧ atanhInv q ≤ hv ∧ hv - lv ≤ 20 * (1 / 2 : ℝ) ^ k := by
  have : NeZero k := ⟨by omega⟩
  have hq0 : q ≠ 0 := by omega
  have hb : 1 ≤ q.log2 := (Nat.le_log2 hq0).mpr (by simpa using hq)
  have hpow : 2 ^ q.log2 ≤ q := Nat.log2_self_le hq0
  set N := atanhInvTerms q.log2 k with hN
  have hN0 : 0 < N := Nat.succ_pos _
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨lv, hv, hl, hh, hl0, hlS, hlS', hSh, hSh'⟩ :=
    seriesBracket_spec (by omega : 0 < q) hN0 hk
  have ht := toVal_tail k
  obtain ⟨r, hr, hrge, hrle⟩ := addCeiling_abs hh ht k
  have hterm := atanhTerm_le_half_pow hpow (atanhInvTerms_spec hb k)
  rw [← hN] at hterm
  have htail := atanhInv_sub_sum_le hqr N
  have hSA := sum_le_atanhInv hqr N
  have hA1 := atanhInv_le_one hqr
  set u := (1 / 2 : ℝ) ^ k with hu
  have hu0 : 0 < u := by positivity
  have hu16 : u ≤ 1 / 16 := by
    rw [hu]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk).trans (by norm_num)
  have hp5 : (1 / 2 : ℝ) ^ (k + 5) = u / 32 := by rw [pow_add, hu]; ring
  have hp6 : (1 / 2 : ℝ) ^ (k + 6) = u / 64 := by rw [pow_add, hu]; ring
  rw [hp6] at hterm
  rw [hp5] at hrge hrle
  set Sn := ∑ i ∈ range N, atanhTerm (q : ℝ) i with hSn
  have hS0 : 0 ≤ Sn := hl0.trans hlS
  have hS1 : Sn ≤ 1 := hSA.trans hA1
  have hv0 : 0 ≤ hv + u / 32 := by linarith
  rw [abs_of_nonneg hv0] at hrle
  have hhv2 : hv ≤ 2 := by nlinarith
  refine ⟨lv, r, hl, hr, hl0, hlS.trans hSA, by linarith, ?_⟩
  have h1 : 2 * (hv + u / 32) * u ≤ 5 * u := by nlinarith
  have h2 : Sn * (8 * u) ≤ 8 * u := by nlinarith
  have h3 : Sn * (6 * u) ≤ 6 * u := by nlinarith
  nlinarith

/-- An enclosure with a nonnegative lower end times an exact natural number. -/
theorem AEncl.natMul {A : Encl} {x ε : ℝ} {w : ℕ} [NeZero w] (K : ℕ)
    (hA : AEncl A x ε) (h0 : ∀ l : ℝ, A.1.toVal = some (l : EReal) → 0 ≤ l) :
    AEncl (Encl.mul w (Encl.exact (ofAzNat (AzNat.ofNat K))) A) (K * x)
      (K * (ε + 4 * (x + ε) * (1 / 2 : ℝ) ^ w)) := by
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := hA
  have hl0 := h0 l hl
  have hF := toVal_ofAzNat_ofNat K
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  obtain ⟨p, hp, fp⟩ := mulFloor_err hF hl w (mul_nonneg hK hl0)
  obtain ⟨q, hq, cq⟩ := mulCeiling_err hF hh w (mul_nonneg hK (by linarith))
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  refine ⟨p, q, hp, hq, fp.le.trans (mul_le_mul_of_nonneg_left h1 hK),
    (mul_le_mul_of_nonneg_left h2 hK).trans cq.ge, ?_⟩
  have e1 := fp.ge
  have e2 := cq.le
  have hlx : l ≤ x + ε := by linarith
  have hhx : h ≤ x + ε := by linarith
  have a1 : (K : ℝ) * l * (1 / 2 : ℝ) ^ w ≤ K * (x + ε) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlx hK) hu0
  have a2 : (K : ℝ) * h * (1 / 2 : ℝ) ^ w ≤ K * (x + ε) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhx hK) hu0
  have a3 : (K : ℝ) * (h - l) ≤ K * ε := mul_le_mul_of_nonneg_left h3 hK
  nlinarith

set_option maxHeartbeats 800000 in
/-- **The width of the logarithm of a smooth integer**: `lnSmoothBracket a b c d k` encloses
`a ln 2 + b ln 3 + c ln 5 + d ln 7` with width at most `2^(−k)` (`k ≥ 4`). -/
theorem lnSmoothBracket_width (a b c d : ℕ) {k : ℕ} (hk : 4 ≤ k) :
    AEncl (lnSmoothBracket a b c d k)
      (a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7)
      ((1 / 2 : ℝ) ^ k) := by
  set K₁ := 2 * (72 * a + 114 * b + 167 * c + 202 * d) with hK₁
  set K₂ := 2 * (27 * a + 43 * b + 63 * c + 76 * d) with hK₂
  set K₃ := 2 * (19 * a + 30 * b + 44 * c + 53 * d) with hK₃
  set K₄ := 2 * (31 * a + 49 * b + 72 * c + 87 * d) with hK₄
  set T := K₁ + K₂ + K₃ + K₄ with hT
  set kk := k + T.log2 + 8 with hkk
  have hkk4 : 4 ≤ kk := by omega
  have : NeZero kk := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ kk with hu
  have hu0 : 0 < u := by positivity
  have hus : u ≤ 1 / 4096 := by
    rw [hu]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 12 ≤ kk)).trans
      (by norm_num)
  -- the four series
  have key : ∀ q : ℕ, 2 ≤ q → ∀ K : ℕ,
      AEncl (Encl.mul kk (Encl.exact (ofAzNat (AzNat.ofNat K))) (atanhInvBracket q kk))
        (K * atanhInv q) (28 * K * u) ∧ 0 ≤ (K : ℝ) * atanhInv q ∧
        (K : ℝ) * atanhInv q ≤ K := by
    intro q hq K
    obtain ⟨lv, hv, hl, hh, hl0, hlA, hAh, hw⟩ := atanhInvBracket_width hq hkk4
    have hA1 := atanhInv_le_one (q := (q : ℝ)) (by exact_mod_cast hq)
    have hA0 : 0 ≤ atanhInv (q : ℝ) := hl0.trans hlA
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hE : AEncl (atanhInvBracket q kk) (atanhInv q) (20 * u) :=
      ⟨lv, hv, hl, hh, hlA, hAh, hw⟩
    refine ⟨(hE.natMul (w := kk) K fun l hl' => ?_).mono ?_, mul_nonneg hK hA0,
      mul_le_of_le_one_right hK hA1⟩
    · rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
      rw [← hl']
      exact hl0
    · have : 20 * u + 4 * (atanhInv (q : ℝ) + 20 * u) * u ≤ 28 * u := by nlinarith
      have := mul_le_mul_of_nonneg_left this hK
      linarith
  obtain ⟨hP₁, n₁, m₁⟩ := key 251 (by norm_num) K₁
  obtain ⟨hP₂, n₂, m₂⟩ := key 449 (by norm_num) K₂
  obtain ⟨hP₃, n₃, m₃⟩ := key 4801 (by norm_num) K₃
  obtain ⟨hP₄, n₄, m₄⟩ := key 8749 (by norm_num) K₄
  have k₁ : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg _
  have k₂ : (0 : ℝ) ≤ K₂ := Nat.cast_nonneg _
  have k₃ : (0 : ℝ) ≤ K₃ := Nat.cast_nonneg _
  have k₄ : (0 : ℝ) ≤ K₄ := Nat.cast_nonneg _
  have hTr : (T : ℝ) = (K₁ : ℝ) + K₂ + K₃ + K₄ := by rw [hT]; push_cast; ring
  set B : ℝ := 2 * (T : ℝ) + 1 with hB
  have hTu : (T : ℝ) * u ≤ (T : ℝ) / 4096 := by
    have := mul_le_mul_of_nonneg_left hus (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    linarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have q₁ : (K₁ : ℝ) * u ≤ K₁ / 4096 := by nlinarith
  have q₂ : (K₂ : ℝ) * u ≤ K₂ / 4096 := by nlinarith
  have q₃ : (K₃ : ℝ) * u ≤ K₃ / 4096 := by nlinarith
  have q₄ : (K₄ : ℝ) * u ≤ K₄ / 4096 := by nlinarith
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hBu : B * u ≤ B / 4096 := by nlinarith
  -- the sums
  have hX₁ := hP₁.add (w := kk) hP₂ (B := B) (by
    rw [abs_of_nonneg (by linarith)]
    linarith)
  have hX₂ := hX₁.add (w := kk) hP₄ (B := B) (by
    rw [abs_of_nonneg (by linarith), ← hu]
    linarith)
  have hY := hX₂.sub (w := kk) hP₃ (B := B) (by
    have habs : |(K₁ : ℝ) * atanhInv ((251 : ℕ) : ℝ) + K₂ * atanhInv ((449 : ℕ) : ℝ)
        + K₄ * atanhInv ((8749 : ℕ) : ℝ) - K₃ * atanhInv ((4801 : ℕ) : ℝ)| ≤ T := by
      rw [abs_le, hTr]
      constructor <;> linarith
    rw [← hu]
    linarith)
  have hdef : lnSmoothBracket a b c d k
      = Encl.sub kk
        (Encl.add kk
          (Encl.add kk
            (Encl.mul kk (Encl.exact (ofAzNat (AzNat.ofNat K₁))) (atanhInvBracket 251 kk))
            (Encl.mul kk (Encl.exact (ofAzNat (AzNat.ofNat K₂))) (atanhInvBracket 449 kk)))
          (Encl.mul kk (Encl.exact (ofAzNat (AzNat.ofNat K₄))) (atanhInvBracket 8749 kk)))
        (Encl.mul kk (Encl.exact (ofAzNat (AzNat.ofNat K₃))) (atanhInvBracket 4801 kk)) :=
    rfl
  rw [hdef]
  have e := smooth_log_eq a b c d
  have e₁ : (K₁ : ℝ) = 2 * (72 * a + 114 * b + 167 * c + 202 * d) := by rw [hK₁]; push_cast; ring
  have e₂ : (K₂ : ℝ) = 2 * (27 * a + 43 * b + 63 * c + 76 * d) := by rw [hK₂]; push_cast; ring
  have e₃ : (K₃ : ℝ) = 2 * (19 * a + 30 * b + 44 * c + 53 * d) := by rw [hK₃]; push_cast; ring
  have e₄ : (K₄ : ℝ) = 2 * (31 * a + 49 * b + 72 * c + 87 * d) := by rw [hK₄]; push_cast; ring
  rw [← e₁, ← e₂, ← e₃, ← e₄] at e
  have hval : (a : ℝ) * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7
      = (K₁ : ℝ) * atanhInv ((251 : ℕ) : ℝ) + K₂ * atanhInv ((449 : ℕ) : ℝ)
        + K₄ * atanhInv ((8749 : ℕ) : ℝ) - K₃ * atanhInv ((4801 : ℕ) : ℝ) := by
    rw [e]
    push_cast
    ring
  rw [hval]
  refine hY.mono ?_
  -- `(52 T + 12) u ≤ 2^(−k)`
  have hTlt : (T : ℝ) < 2 * (2 : ℝ) ^ T.log2 := by
    have := Nat.lt_log2_self (n := T)
    rw [pow_succ] at this
    have h' : (T : ℝ) < (((2 ^ T.log2 * 2 : ℕ)) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  have hsplit : u = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ T.log2 * (1 / 256) := by
    rw [hu, hkk, pow_add, pow_add]
    norm_num
  have hpk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  have hpL : (0 : ℝ) < (1 / 2 : ℝ) ^ T.log2 := by positivity
  have hprod : (2 : ℝ) ^ T.log2 * (1 / 2 : ℝ) ^ T.log2 = 1 := by
    rw [← mul_pow]
    norm_num
  have hpL1 : (1 / 2 : ℝ) ^ T.log2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hTL : (T : ℝ) * (1 / 2 : ℝ) ^ T.log2 ≤ 2 := by nlinarith
  have hfin : (52 * (T : ℝ) + 12) * u ≤ (1 / 2 : ℝ) ^ k := by
    rw [hsplit]
    have : (52 * (T : ℝ) + 12) * ((1 / 2 : ℝ) ^ T.log2) ≤ 116 := by nlinarith
    nlinarith
  rw [← hu]
  have e' : 28 * (K₁ : ℝ) * u + 28 * K₂ * u + 4 * B * u + 28 * K₄ * u + 4 * B * u
      + 28 * K₃ * u + 4 * B * u = (52 * (T : ℝ) + 12) * u := by
    rw [hB, hTr]
    ring
  rw [e']
  exact hfin

/-! ### `nextSmooth` is smooth -/

/-- `divOut` splits off a power of `p`. -/
theorem divOut_spec (p : ℕ) : ∀ fuel n : ℕ, n = p ^ (divOut p fuel n).1 * (divOut p fuel n).2
  | 0, n => by simp [divOut]
  | fuel + 1, n => by
    rw [divOut]
    split_ifs with h
    · have ih := divOut_spec p fuel (n / p)
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h.2
      dsimp only
      rw [pow_succ, mul_assoc, mul_comm p, ← mul_assoc, ← ih]
      exact (Nat.div_mul_cancel hdvd).symm
    · simp

/-- `divOut` at `1`. -/
theorem divOut_one {p : ℕ} (hp : 2 ≤ p) (fuel : ℕ) : divOut p fuel 1 = (0, 1) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [divOut]
    have : ¬ (0 < 1 ∧ 1 % p = 0) := by
      rintro ⟨-, h⟩
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    rw [ite_eq_right this]

/-- `divOut 2` takes a power of two apart. -/
theorem divOut_two_pow : ∀ (j fuel : ℕ), j ≤ fuel → divOut 2 fuel (2 ^ j) = (j, 1)
  | 0, fuel, _ => by
    rw [pow_zero]
    exact divOut_one (by norm_num) fuel
  | j + 1, 0, h => by omega
  | j + 1, fuel + 1, h => by
    rw [divOut]
    have hc : 0 < 2 ^ (j + 1) ∧ 2 ^ (j + 1) % 2 = 0 :=
      ⟨by positivity, by rw [pow_succ]; exact Nat.mul_mod_left _ _⟩
    rw [ite_eq_left hc]
    have hdiv : 2 ^ (j + 1) / 2 = 2 ^ j := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [hdiv, divOut_two_pow j fuel (by omega)]

/-- `n` is the product of the powers and the cofactor of `smoothExps n`. -/
theorem smoothExps_spec (n : ℕ) :
    n = 2 ^ (smoothExps n).1 * 3 ^ (smoothExps n).2.1 * 5 ^ (smoothExps n).2.2.1
      * 7 ^ (smoothExps n).2.2.2.1 * (smoothExps n).2.2.2.2 := by
  unfold smoothExps
  dsimp only
  have h2 := divOut_spec 2 (n.log2 + 1) n
  have h3 := divOut_spec 3 (n.log2 + 1) (divOut 2 (n.log2 + 1) n).2
  have h5 := divOut_spec 5 (n.log2 + 1) (divOut 3 (n.log2 + 1) (divOut 2 (n.log2 + 1) n).2).2
  have h7 := divOut_spec 7 (n.log2 + 1)
    (divOut 5 (n.log2 + 1) (divOut 3 (n.log2 + 1) (divOut 2 (n.log2 + 1) n).2).2).2
  conv_lhs => rw [h2, h3, h5, h7]
  ring

/-- A smooth integer is the product of the powers of `smoothExps`. -/
theorem isSmooth_spec {n : ℕ} (h : isSmooth n = true) :
    n = 2 ^ (smoothExps n).1 * 3 ^ (smoothExps n).2.1 * 5 ^ (smoothExps n).2.2.1
      * 7 ^ (smoothExps n).2.2.2.1 := by
  have h1 : (smoothExps n).2.2.2.2 = 1 := by
    unfold isSmooth at h
    exact beq_iff_eq.mp h
  have := smoothExps_spec n
  rw [h1, mul_one] at this
  exact this

/-- A power of two is smooth. -/
theorem isSmooth_two_pow (j : ℕ) : isSmooth (2 ^ j) = true := by
  unfold isSmooth smoothExps
  dsimp only
  have hlog : (2 ^ j).log2 = j := Nat.log2_two_pow
  rw [hlog, divOut_two_pow j (j + 1) (by omega)]
  dsimp only
  rw [divOut_one (by norm_num), divOut_one (by norm_num), divOut_one (by norm_num)]
  rfl

/-- The search finds a smooth integer when there is one within its fuel. -/
theorem isSmooth_nextSmoothFuel : ∀ (fuel n m : ℕ), n ≤ m → m ≤ n + fuel →
    isSmooth m = true → isSmooth (nextSmoothFuel fuel n) = true
  | 0, n, m, h1, h2, hm => by
    have : m = n := by omega
    rw [nextSmoothFuel, ← this]
    exact hm
  | fuel + 1, n, m, h1, h2, hm => by
    rw [nextSmoothFuel]
    split_ifs with h
    · exact h
    · have hne : m ≠ n := fun e => h (e ▸ hm)
      exact isSmooth_nextSmoothFuel fuel (n + 1) m (by omega) (by omega) hm

/-- **`nextSmooth n` has no prime factor above `7`** (`n ≥ 1`): the power of two in `(n, 2n]`
is within the fuel. -/
theorem isSmooth_nextSmooth {n : ℕ} (hn : 1 ≤ n) : isSmooth (nextSmooth n) = true := by
  have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have h2 : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
  refine isSmooth_nextSmoothFuel n n (2 ^ (n.log2 + 1)) h1.le ?_ (isSmooth_two_pow _)
  rw [pow_succ]
  omega

end Azurite.AzFloat
