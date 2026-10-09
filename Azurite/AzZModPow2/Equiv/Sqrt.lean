/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZModPow2.Sqrt
import Azurite.AzZModPow2.Equiv.Basic
import Azurite.AzNat.Equiv.JacobiSym
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.Dispatch
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
## Correctness of `AzZModPow2.sqrt?`

* `sqrt?_some`: a returned root squares to the input (the candidate is verified).
* `sqrt?_isSome_iff`: a root is returned exactly when the input is a square.
* `sqrt?_le`: the returned root is the least one.

The Newton iteration is analysed over `ℤ` (`invSqrtStep_spec`: the error `1 − u y²` goes from
divisible by `2^j` to divisible by `2^min(k, 2j−2)`), the squares modulo `2^k` are described by
`sq_mod_pow2_structure` (a root of `2^v u` is `2^(v/2)` times a root of `u` modulo `2^(k−v)`) and
`int_roots_of_odd_sq` (the roots of an odd square modulo `2^n` are `±s`, `±s + 2^(n−1)`), and the
list search is `leastRoot_some`/`leastRoot_le`.
-/

namespace Azurite.AzZModPow2

variable {k : ℕ}

/-! ### Values -/

theorem toNat_val_mul (a b : AzZModPow2 k) :
    (a * b).val.toNat = a.val.toNat * b.val.toNat % 2 ^ k :=
  AzNat.toNat_mulDispatchModPow2 _ _ _

theorem toNat_val_ofAzNat (n : AzNat) : (ofAzNat k n).val.toNat = n.toNat % 2 ^ k :=
  AzNat.toNat_modPow2 _ _

theorem toNat_val_one : (1 : AzZModPow2 k).val.toNat = 1 % 2 ^ k := by
  show (ofAzNat k 1).val.toNat = _
  rw [toNat_val_ofAzNat, AzNat.toNat_one]

theorem toNat_val_zero : (0 : AzZModPow2 k).val.toNat = 0 := AzNat.toNat_zero

theorem eq_of_toNat_val {a b : AzZModPow2 k} (h : a.val.toNat = b.val.toNat) : a = b :=
  ext (AzNat.toNat_injective h)

theorem val_toZMod (a : AzZModPow2 k) : (toZMod a).val = a.val.toNat :=
  ZMod.val_natCast_of_lt a.isLt

/-- Being a square in `ZMod (2^k)` is having a root in `AzZModPow2 k`. -/
theorem isSquare_toZMod_iff (a : AzZModPow2 k) : IsSquare (toZMod a) ↔ ∃ r, r * r = a := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨ofZMod z, toZMod_injective ?_⟩
    rw [toZMod_mul, toZMod_ofZMod, hz]
  · rintro ⟨r, hr⟩
    exact ⟨toZMod r, by rw [← toZMod_mul, hr]⟩

/-! ### The Newton iteration -/

/-- If `U Y² = 1 − 2f` then `1 − U (Y (1 + f))² = f² (3 + 2f)`. -/
theorem newton_identity (U Y f : ℤ) (hE : U * Y ^ 2 = 1 - 2 * f) :
    1 - U * (Y * (1 + f)) ^ 2 = f ^ 2 * (3 + 2 * f) := by
  linear_combination (-(1 + f) ^ 2) * hE

/-- Perturbing the step by a multiple of `2 K₂` changes the error by a multiple of `4 K₂`. -/
theorem newton_perturb (U Y f K2 c : ℤ) :
    1 - U * (Y * (1 + (f + 2 * K2 * c))) ^ 2
      = (1 - U * (Y * (1 + f)) ^ 2)
        - 4 * K2 * (U * Y ^ 2 * (1 + f) * c + U * Y ^ 2 * c ^ 2 * K2) := by
  ring

/-- The canonical residue of `1 − u y²` differs from the integer `1 − U Y²` by a multiple of
`2^k`. -/
theorem err_val_eq (u y : AzZModPow2 k) :
    ∃ c : ℤ, ((1 - u * y * y).val.toNat : ℤ)
      = 1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2 - 2 ^ k * c := by
  have h1 : toZMod (1 - u * y * y)
      = ((1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2 : ℤ) : ZMod (2 ^ k)) := by
    rw [toZMod_sub, toZMod_mul, toZMod_mul, toZMod_one]
    unfold toZMod
    push_cast; ring
  have h2 : (((1 - u * y * y).val.toNat : ℤ) : ZMod (2 ^ k))
      = ((1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2 : ℤ) : ZMod (2 ^ k)) := by
    rw [Int.cast_natCast]; exact h1
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
  push_cast at hc
  exact ⟨c, by linarith⟩

/-- A step with an error divisible by `2^k` is the identity. -/
theorem invSqrtStep_of_dvd (u y : AzZModPow2 k)
    (h : (2 : ℤ) ^ k ∣ 1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2) :
    invSqrtStep u y = y := by
  have he : (1 - u * y * y) = 0 := by
    apply toZMod_injective
    rw [toZMod_sub, toZMod_mul, toZMod_mul, toZMod_one, toZMod_zero]
    have : (((1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2 : ℤ)) : ZMod (2 ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    push_cast at this
    unfold toZMod
    linear_combination this
  unfold invSqrtStep
  dsimp only
  rw [he]
  have h0 : ofAzNat k ((0 : AzZModPow2 k).val >>> 1) = 0 := by
    apply eq_of_toNat_val
    rw [toNat_val_ofAzNat, AzNat.toNat_hShiftRight, toNat_val_zero]
    simp
  rw [h0, mul_zero, add_zero]

/-- **The Newton step**: an error divisible by `2^j` (`3 ≤ j ≤ k`) becomes divisible by
`2^min(k, 2j−2)`. -/
theorem invSqrtStep_spec (u y : AzZModPow2 k) (j : ℕ) (hj3 : 3 ≤ j) (hjk : j ≤ k)
    (h : (2 : ℤ) ^ j ∣ 1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2) :
    (2 : ℤ) ^ min k (2 * j - 2) ∣
      1 - (u.val.toNat : ℤ) * ((invSqrtStep u y).val.toNat : ℤ) ^ 2 := by
  set U : ℤ := (u.val.toNat : ℤ) with hU
  set Y : ℤ := (y.val.toNat : ℤ) with hY
  obtain ⟨c, hc⟩ := err_val_eq u y
  rw [← hU, ← hY] at hc
  set N : ℕ := (1 - u * y * y).val.toNat with hN
  -- the error is even, so its halving is exact
  have h2E : (2 : ℤ) ∣ 1 - U * Y ^ 2 := (dvd_pow_self 2 (by omega : j ≠ 0)).trans h
  obtain ⟨f, hf⟩ := h2E
  have hjf : (2 : ℤ) ^ (j - 1) ∣ f := by
    have : (2 : ℤ) ^ (j - 1) * 2 ∣ f * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), mul_comm f, ← hf]; exact h
    exact (mul_dvd_mul_iff_right two_ne_zero).mp this
  set K2 : ℤ := 2 ^ (k - 2) with hK2
  have h4 : (2 : ℤ) ^ k = 4 * K2 := by
    rw [hK2, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_cancel' (by omega : 2 ≤ k)]
  -- the halved residue
  set H : ℕ := ((1 - u * y * y).val >>> 1).toNat with hHdef
  have hH2 : 2 * (H : ℤ) = N := by
    have h2N : 2 ∣ N := by
      have : (2 : ℤ) ∣ (N : ℤ) := by
        rw [hc, hf, h4]
        exact ⟨f - 2 * K2 * c, by ring⟩
      exact_mod_cast this
    rw [hHdef, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, pow_one]
    exact_mod_cast Nat.mul_div_cancel' h2N
  -- the new value
  have hY' : ∃ d : ℤ, ((invSqrtStep u y).val.toNat : ℤ) = Y * (1 + H) - 2 ^ k * d := by
    have h1 : toZMod (invSqrtStep u y) = ((Y * (1 + H) : ℤ) : ZMod (2 ^ k)) := by
      unfold invSqrtStep
      rw [toZMod_add, toZMod_mul, toZMod_ofAzNat, ← hHdef, hY]
      unfold toZMod
      push_cast; ring
    have h2 : (((invSqrtStep u y).val.toNat : ℤ) : ZMod (2 ^ k))
        = ((Y * (1 + H) : ℤ) : ZMod (2 ^ k)) := by
      rw [Int.cast_natCast]; exact h1
    obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
    push_cast at hd
    exact ⟨d, by linarith⟩
  obtain ⟨d, hd⟩ := hY'
  rw [hd]
  have hE' : U * Y ^ 2 = 1 - 2 * f := by linarith
  have hH' : (H : ℤ) = f + 2 * K2 * (-c) := by
    have : (2 : ℤ) * H = 2 * (f + 2 * K2 * (-c)) := by rw [hH2, hc, hf, h4]; ring
    exact mul_left_cancel₀ two_ne_zero this
  have hdiff : 1 - U * (Y * (1 + H) - 2 ^ k * d) ^ 2
      = (1 - U * (Y * (1 + H)) ^ 2) + 2 ^ k * (U * d * (2 * Y * (1 + H) - 2 ^ k * d)) := by
    ring
  rw [hdiff, hH', newton_perturb, newton_identity U Y f hE', h4]
  have hmin_k : (2 : ℤ) ^ min k (2 * j - 2) ∣ 4 * K2 := by
    rw [← h4]; exact pow_dvd_pow 2 (min_le_left _ _)
  have hmin_f : (2 : ℤ) ^ min k (2 * j - 2) ∣ f ^ 2 * (3 + 2 * f) := by
    apply Dvd.dvd.mul_right
    have : (2 : ℤ) ^ (2 * j - 2) ∣ f ^ 2 := by
      have := pow_dvd_pow_of_dvd hjf 2
      rwa [← pow_mul, show (j - 1) * 2 = 2 * j - 2 by omega] at this
    exact (pow_dvd_pow 2 (min_le_right _ _)).trans this
  exact dvd_add (dvd_sub hmin_f (dvd_mul_of_dvd_left hmin_k _)) (dvd_mul_of_dvd_left hmin_k _)

/-- The Newton invariant: after `n` steps the error is divisible by `2^min(k, 2^n + 2)`. -/
theorem invSqrtAux_spec (u : AzZModPow2 k) (hu : u.val.toNat % 8 = 1) : ∀ n : ℕ,
    (2 : ℤ) ^ min k (2 ^ n + 2) ∣
      1 - (u.val.toNat : ℤ) * ((invSqrtAux u n).val.toNat : ℤ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    show (2 : ℤ) ^ min k (2 ^ 0 + 2) ∣ 1 - _ * (((1 : AzZModPow2 k).val.toNat : ℕ) : ℤ) ^ 2
    rw [toNat_val_one]
    rcases Nat.lt_or_ge k 1 with hk | hk
    · have : k = 0 := by omega
      subst this; simp
    · rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      push_cast
      have h8 : (8 : ℤ) ∣ 1 - (u.val.toNat : ℤ) := by
        have : (u.val.toNat : ℤ) % 8 = 1 := by exact_mod_cast hu
        omega
      have h8' : (2 : ℤ) ^ min k 3 ∣ 8 := by
        have := pow_dvd_pow (2 : ℤ) (min_le_right k 3)
        norm_num at this
        exact this
      rw [mul_one]
      exact h8'.trans h8
  | succ n ih =>
    rw [invSqrtAux]
    by_cases hk : k ≤ 2 ^ n + 2
    · rw [min_eq_left hk] at ih
      rw [invSqrtStep_of_dvd _ _ ih, min_eq_left (by rw [pow_succ]; omega)]
      exact ih
    · have hk' := not_le.mp hk
      rw [min_eq_right hk'.le] at ih
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have := invSqrtStep_spec u (invSqrtAux u n) (2 ^ n + 2) (by omega) hk'.le ih
      rwa [show 2 * (2 ^ n + 2) - 2 = 2 ^ (n + 1) + 2 by rw [pow_succ]; omega] at this

/-- **`oddSqrt` is a square root** of a residue `≡ 1 (mod 8)`. -/
theorem oddSqrt_mul_self (u : AzZModPow2 k) (hu : u.val.toNat % 8 = 1) :
    oddSqrt u * oddSqrt u = u := by
  have h := invSqrtAux_spec u hu (Nat.clog 2 k)
  rw [min_eq_left ((Nat.le_pow_clog (by norm_num) k).trans (Nat.le_add_right _ _))] at h
  set y := invSqrtAux u (Nat.clog 2 k) with hy
  have hz : ((1 - (u.val.toNat : ℤ) * (y.val.toNat : ℤ) ^ 2 : ℤ) : ZMod (2 ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  have key : u * y * y = 1 := by
    apply toZMod_injective
    rw [toZMod_mul, toZMod_mul, toZMod_one]
    push_cast at hz
    unfold toZMod
    linear_combination (-1 : ZMod (2 ^ k)) * hz
  unfold oddSqrt
  rw [← hy]
  calc u * y * (u * y) = u * (u * y * y) := by ring
    _ = u := by rw [key, mul_one]

/-! ### Squares modulo a power of two -/

theorem odd_mul_self_mod_eight {t : ℕ} (ht : t % 2 = 1) : t * t % 8 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 * m + 1 := ⟨t / 2, by omega⟩
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
  have hmc : m * (m + 1) = 2 * c := by rw [two_mul]; exact hc
  have : (2 * m + 1) * (2 * m + 1) = 8 * c + 1 := by
    calc (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
      _ = 8 * c + 1 := by rw [hmc]; ring
  rw [this]; omega

/-- An odd `u < 2^n` that is a square modulo `2^n` (`n ≥ 1`) is `≡ 1 (mod 8)`. -/
theorem mod_eight_of_odd_sq (u t n : ℕ) (hn : 1 ≤ n) (ht : t % 2 = 1)
    (htt : t * t % 2 ^ n = u) : u % 8 = 1 := by
  have h8 := odd_mul_self_mod_eight ht
  have h8pow : (8 : ℕ) = 2 ^ 3 := by norm_num
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hdvd : 2 ^ n ∣ 8 := by rw [h8pow]; exact Nat.pow_dvd_pow 2 (by omega)
    have : u = 1 := by
      rw [← htt, ← Nat.mod_mod_of_dvd (t * t) hdvd, h8]
      exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    omega
  · have hdvd : 8 ∣ 2 ^ n := by rw [h8pow]; exact Nat.pow_dvd_pow 2 hn3
    rw [← htt, Nat.mod_mod_of_dvd (t * t) hdvd, h8]

/-- **Structure of a root**: if `r² ≡ a (mod 2^k)` with `a = 2^v u` nonzero, then `v` is even
and `r = 2^(v/2) t` with `t` odd and `t² ≡ u (mod 2^(k−v))`. -/
theorem sq_mod_pow2_structure (r a : ℕ) (ha0 : a ≠ 0) (hak : a < 2 ^ k)
    (hr : r * r % 2 ^ k = a) :
    padicValNat 2 a % 2 = 0 ∧ padicValNat 2 a < k ∧
      ∃ t, r = 2 ^ (padicValNat 2 a / 2) * t ∧ t % 2 = 1 ∧
        t * t % 2 ^ (k - padicValNat 2 a) = a / 2 ^ padicValNat 2 a := by
  set v := padicValNat 2 a with hv
  have hu := Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := a))
  set u := a / 2 ^ v with hudef
  have huodd : u % 2 = 1 := AzNat.odd_div_pow_padicValNat_two ha0
  have hvk : v < k := by
    by_contra hge
    have h1 : 2 ^ k ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hge)
    have h2 : 2 ^ v ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) pow_padicValNat_dvd
    omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
    exact ha0 hr.symm
  set q := r * r / 2 ^ k with hq
  have hrr : r * r = 2 ^ k * q + a := by rw [← hr, hq, Nat.div_add_mod]
  have hk : 2 ^ k = 2 ^ v * 2 ^ (k - v) := by rw [← pow_add, Nat.add_sub_cancel' hvk.le]
  set m := u + 2 ^ (k - v) * q with hm
  have hmodd : m % 2 = 1 := by
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ (k - v) := dvd_pow_self 2 (by omega)
    rw [hm, hc, mul_assoc]; omega
  have hrr' : r * r = 2 ^ v * m := by
    rw [hrr, hk, hm, ← hu]; ring
  have hval : padicValNat 2 (r * r) = v := by
    rw [hrr', padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega), add_zero]
  have hval2 : padicValNat 2 (r * r) = 2 * padicValNat 2 r := by
    rw [← sq, padicValNat.pow]
  set w := padicValNat 2 r with hw
  have hv2 : v = 2 * w := by rw [← hval, hval2]
  refine ⟨by omega, hvk, r / 2 ^ w, ?_, AzNat.odd_div_pow_padicValNat_two hr0, ?_⟩
  · rw [show v / 2 = w by omega]
    exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  · set t := r / 2 ^ w with ht
    have hrt : r = 2 ^ w * t := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have htt : t * t = m := by
      have h2v : 2 ^ v = 2 ^ w * 2 ^ w := by rw [← pow_add, hv2, two_mul]
      have h1 : 2 ^ v * (t * t) = 2 ^ v * m := by
        rw [← hrr', hrt, h2v]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [htt, hm, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have := hak
    rw [← hu, hk] at this
    exact Nat.lt_of_mul_lt_mul_left this

/-- **Roots of an odd square** modulo `2^n`: they are `±s` and `±s + 2^(n−1)`. -/
theorem int_roots_of_odd_sq (s t : ℤ) (n : ℕ) (hn : 1 ≤ n) (hs : s % 2 = 1) (ht : t % 2 = 1)
    (h : (2 : ℤ) ^ n ∣ t * t - s * s) :
    (2 : ℤ) ^ n ∣ t - s ∨ (2 : ℤ) ^ n ∣ t - (-s) ∨
      (2 : ℤ) ^ n ∣ t - (s + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ t - (-s + 2 ^ (n - 1)) := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    left; simp only [pow_one]; omega
  · obtain ⟨α, hα⟩ : ∃ α, t - s = 2 * α := ⟨(t - s) / 2, by omega⟩
    obtain ⟨β, hβ⟩ : ∃ β, t + s = 2 * β := ⟨(t + s) / 2, by omega⟩
    have hts : t * t - s * s = 2 ^ 2 * (α * β) := by
      have : t * t - s * s = (t - s) * (t + s) := by ring
      rw [this, hα, hβ]; ring
    have hn' : (2 : ℤ) ^ n = 2 ^ (n - 2) * 2 ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hn2]
    have hn1 : (2 : ℤ) ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have hαβ : (2 : ℤ) ^ (n - 2) ∣ α * β := by
      rw [hts, hn', mul_comm ((2 : ℤ) ^ (n - 2))] at h
      exact (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ 2 ≠ 0)).mp h
    have hsum : α + β = t := by omega
    have hcop : ∀ x : ℤ, x % 2 = 1 → IsCoprime ((2 : ℤ) ^ (n - 2)) x := fun x hx =>
      IsCoprime.pow_left ((Int.prime_two.irreducible.coprime_iff_not_dvd).mpr (by omega))
    rcases Int.emod_two_eq_zero_or_one α with hα2 | hα2
    · -- `α` even, `β` odd: `2^(n-2) ∣ α`, the conclusions about `t − s`
      have hβ2 : β % 2 = 1 := by omega
      obtain ⟨γ, hγ⟩ := (hcop β hβ2).dvd_of_dvd_mul_right hαβ
      rcases Int.emod_two_eq_zero_or_one γ with hγ2 | hγ2
      · left
        obtain ⟨δ, hδ⟩ : ∃ δ, γ = 2 * δ := ⟨γ / 2, by omega⟩
        exact ⟨δ, by rw [hα, hγ, hδ, hn']; ring⟩
      · right; right; left
        obtain ⟨δ, hδ⟩ : ∃ δ, γ = 2 * δ + 1 := ⟨γ / 2, by omega⟩
        exact ⟨δ, by rw [hn1, hn']; linear_combination hα + 2 * hγ + 2 * (2 : ℤ) ^ (n - 2) * hδ⟩
    · -- `α` odd, `β` even: `2^(n-2) ∣ β`, the conclusions about `t + s`
      obtain ⟨γ, hγ⟩ := (hcop α hα2).dvd_of_dvd_mul_left hαβ
      rcases Int.emod_two_eq_zero_or_one γ with hγ2 | hγ2
      · right; left
        obtain ⟨δ, hδ⟩ : ∃ δ, γ = 2 * δ := ⟨γ / 2, by omega⟩
        exact ⟨δ, by rw [sub_neg_eq_add, hβ, hγ, hδ, hn']; ring⟩
      · right; right; right
        obtain ⟨δ, hδ⟩ : ∃ δ, γ = 2 * δ + 1 := ⟨γ / 2, by omega⟩
        exact ⟨δ, by rw [hn1, hn']; linear_combination hβ + 2 * hγ + 2 * (2 : ℤ) ^ (n - 2) * hδ⟩

/-- A congruence `t ≡ c (mod 2^n)` with `c` the integer value of a residue `x` pins `t mod 2^n`
to the canonical representative of `x`. -/
theorem mod_eq_val_of_dvd {n : ℕ} (t : ℕ) (x : AzZModPow2 n) (c : ℤ)
    (hc : toZMod x = (c : ZMod (2 ^ n))) (h : (2 : ℤ) ^ n ∣ (t : ℤ) - c) :
    t % 2 ^ n = x.val.toNat := by
  have h1 : ((t : ℤ) : ZMod (2 ^ n)) = (c : ZMod (2 ^ n)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    exact dvd_sub_comm.mp h
  rw [← val_toZMod x, hc, ← h1, Int.cast_natCast, ZMod.val_natCast]

/-! ### The list search -/

theorem leastRoot_some (u : AzNat) (n : ℕ) : ∀ (l : List AzNat) (c : AzNat),
    leastRoot u n l = some c → c ∈ l ∧ (c * c).modPow2 n = u := by
  intro l
  induction l with
  | nil => intro c h; simp [leastRoot] at h
  | cons x xs ih =>
    intro c h
    unfold leastRoot at h
    dsimp only at h
    split_ifs at h with hx
    · obtain rfl := Option.some.inj h
      split
      · exact ⟨List.mem_cons_self .., hx⟩
      · rename_i m hm
        obtain ⟨hmem, hmroot⟩ := ih m hm
        rcases min_choice x m with hmin | hmin
        · rw [hmin]; exact ⟨List.mem_cons_self .., hx⟩
        · rw [hmin]; exact ⟨List.mem_cons_of_mem _ hmem, hmroot⟩
    · obtain ⟨hmem, hroot⟩ := ih c h
      exact ⟨List.mem_cons_of_mem _ hmem, hroot⟩

theorem leastRoot_le (u : AzNat) (n : ℕ) : ∀ (l : List AzNat) (c : AzNat),
    c ∈ l → (c * c).modPow2 n = u → ∃ m, leastRoot u n l = some m ∧ m ≤ c := by
  intro l
  induction l with
  | nil => intro c h; simp at h
  | cons x xs ih =>
    intro c hc hroot
    unfold leastRoot
    dsimp only
    rcases List.mem_cons.mp hc with rfl | hmem
    · rw [ite_eq_left hroot]
      split
      · exact ⟨c, rfl, le_rfl⟩
      · exact ⟨_, rfl, min_le_left _ _⟩
    · obtain ⟨m, hm, hle⟩ := ih c hmem hroot
      split_ifs with hx
      · rw [hm]
        exact ⟨_, rfl, (min_le_right _ _).trans hle⟩
      · exact ⟨m, hm, hle⟩

/-! ### The main theorems -/

/-- **Soundness**: a returned root squares to the input. -/
theorem sqrt?_some {a r : AzZModPow2 k} (h : sqrt? a = some r) : r * r = a := by
  unfold sqrt? at h
  split at h
  · rename_i hz
    obtain rfl := Option.some.inj h
    have : a = 0 := by
      apply ext
      by_contra hne
      rw [AzNat.trailingZeros_eq_padicValNat _ hne] at hz
      cases hz
    rw [this, mul_zero]
  · try dsimp only at h
    split_ifs at h with h1 h2
    split at h
    · cases h
    · try dsimp only at h
      split_ifs at h with h3
      obtain rfl := Option.some.inj h
      exact h3

/-- Among the four candidates one has the residue of any given root `t` of `u`. -/
theorem exists_candidate {n : ℕ} (hn : 1 ≤ n) (s t : ℕ) (hs : s % 2 = 1) (ht : t % 2 = 1)
    (hst : s * s % 2 ^ n = t * t % 2 ^ n) :
    let S : AzZModPow2 n := ofAzNat n (AzNat.ofNat s)
    let H : AzZModPow2 n := ofAzNat n ((1 : AzNat) <<< (n - 1))
    ∃ X ∈ [S.val, (-S).val, (S + H).val, (-S + H).val], t % 2 ^ n = X.toNat := by
  intro S H
  have hdvd : (2 : ℤ) ^ n ∣ (t : ℤ) * t - (s : ℤ) * s := by
    have := (Nat.modEq_iff_dvd.mp (hst : s * s ≡ t * t [MOD 2 ^ n]))
    push_cast at this
    exact this
  have hS : toZMod S = ((s : ℤ) : ZMod (2 ^ n)) := by
    rw [toZMod_ofAzNat, AzNat.toNat_ofNat, Int.cast_natCast]
  have hH : toZMod H = (((2 : ℤ) ^ (n - 1) : ℤ) : ZMod (2 ^ n)) := by
    rw [toZMod_ofAzNat, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_one, one_mul]
    push_cast; rfl
  rcases int_roots_of_odd_sq s t n hn (by exact_mod_cast hs) (by exact_mod_cast ht) hdvd
    with h | h | h | h
  · exact ⟨S.val, by simp, mod_eq_val_of_dvd t S _ hS h⟩
  · exact ⟨(-S).val, by simp, mod_eq_val_of_dvd t (-S) _ (by rw [toZMod_neg, hS]; push_cast; rfl) h⟩
  · exact ⟨(S + H).val, by simp,
      mod_eq_val_of_dvd t (S + H) _ (by rw [toZMod_add, hS, hH]; push_cast; rfl) h⟩
  · exact ⟨(-S + H).val, by simp,
      mod_eq_val_of_dvd t (-S + H) _ (by rw [toZMod_add, toZMod_neg, hS, hH]; push_cast; rfl) h⟩

/-- **Completeness and minimality**: every root `r'` of a nonzero `a` certifies that `sqrt?`
returns a root no larger than `r'`. -/
theorem sqrt?_of_root {a r' : AzZModPow2 k} (ha : a ≠ 0) (hr' : r' * r' = a) :
    ∃ r, sqrt? a = some r ∧ r.val.toNat ≤ r'.val.toNat := by
  have ha0 : a.val.toNat ≠ 0 := fun h => ha (eq_of_toNat_val (by rw [h, toNat_val_zero]))
  have hav : a.val ≠ 0 := fun h => ha0 (by rw [h, AzNat.toNat_zero])
  have hak : a.val.toNat < 2 ^ k := a.isLt
  have hrr : r'.val.toNat * r'.val.toNat % 2 ^ k = a.val.toNat := by
    rw [← toNat_val_mul, hr']
  obtain ⟨hveven, hvk, t, hrt, htodd, htt⟩ :=
    sq_mod_pow2_structure r'.val.toNat a.val.toNat ha0 hak hrr
  set v := padicValNat 2 a.val.toNat with hv
  set w := v / 2 with hw
  have hvw : v = 2 * w := by omega
  set n := k - v with hn
  set uN := a.val.toNat / 2 ^ v with huN
  have hn1 : 1 ≤ n := by omega
  have hu2 := Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := a.val.toNat))
  rw [← huN] at hu2
  have hk : 2 ^ k = 2 ^ v * 2 ^ n := by rw [← pow_add, hn, Nat.add_sub_cancel' hvk.le]
  have huN_lt : uN < 2 ^ n := by
    have := hak
    rw [← hu2, hk] at this
    exact Nat.lt_of_mul_lt_mul_left this
  have hu8 : uN % 8 = 1 := mod_eight_of_odd_sq uN t n hn1 htodd htt
  have hu_toNat : (a.val >>> v).toNat = uN := by
    rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hnk : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- unfold the algorithm along the non-failing branches
  unfold sqrt?
  rw [AzNat.trailingZeros_eq_padicValNat _ hav]
  try dsimp only
  rw [ite_eq_right (by omega : ¬ v % 2 = 1)]
  have hmod3 : (a.val >>> v).modPow2 3 = 1 := by
    apply AzNat.toNat_injective
    rw [AzNat.toNat_modPow2, hu_toNat, AzNat.toNat_one]
    exact hu8
  rw [ite_eq_right (not_not.mpr hmod3)]
  try dsimp only
  -- the Newton root is an odd root of `uN` modulo `2^n`
  set s := (oddSqrt (ofAzNat k (a.val >>> v))).val with hs
  have hs_sq : s.toNat * s.toNat % 2 ^ k = uN := by
    have h1 := oddSqrt_mul_self (ofAzNat k (a.val >>> v))
      (by rw [toNat_val_ofAzNat, hu_toNat, Nat.mod_eq_of_lt (lt_of_lt_of_le huN_lt hnk)]; exact hu8)
    have := congrArg (fun x : AzZModPow2 k => x.val.toNat) h1
    rwa [toNat_val_mul, toNat_val_ofAzNat, hu_toNat,
      Nat.mod_eq_of_lt (lt_of_lt_of_le huN_lt hnk)] at this
  have hs_sq_n : s.toNat * s.toNat % 2 ^ n = uN := by
    rw [← Nat.mod_mod_of_dvd (s.toNat * s.toNat) (Nat.pow_dvd_pow 2 (by omega : n ≤ k)), hs_sq,
      Nat.mod_eq_of_lt huN_lt]
  have hsodd : s.toNat % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one s.toNat with h0 | h1
    · exfalso
      have h2 : s.toNat * s.toNat % 2 = 0 := by rw [Nat.mul_mod, h0]
      have h3 : uN % 2 = s.toNat * s.toNat % 2 := by
        rw [← hs_sq_n, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : n ≠ 0))]
      omega
    · exact h1
  -- a candidate with the residue of `t`
  obtain ⟨X, hXmem, hXt⟩ := exists_candidate hn1 s.toNat t hsodd htodd (by rw [hs_sq_n, htt])
  have hX_root : (X * X).modPow2 n = a.val >>> v := by
    apply AzNat.toNat_injective
    rw [AzNat.toNat_modPow2, AzNat.toNat_mul, hu_toNat, ← hXt, ← Nat.mul_mod, htt]
  have hofNat : AzNat.ofNat s.toNat = s := AzNat.toNat_injective (AzNat.toNat_ofNat _)
  rw [hofNat] at hXmem
  obtain ⟨m, hm, hmle⟩ := leastRoot_le (a.val >>> v) n _ X hXmem hX_root
  rw [hm]
  dsimp only
  obtain ⟨_, hmroot⟩ := leastRoot_some _ _ _ _ hm
  have hm_sq : m.toNat * m.toNat % 2 ^ n = uN := by
    have := congrArg AzNat.toNat hmroot
    rwa [AzNat.toNat_modPow2, AzNat.toNat_mul, hu_toNat] at this
  -- the shifted candidate is a root of `a`
  have hm_lt : m.toNat < 2 ^ n := by
    have := (AzNat.le_iff_toNat_le _ _).mp hmle
    exact lt_of_le_of_lt this (by rw [← hXt]; exact Nat.mod_lt _ (by positivity))
  set r := ofAzNat k (m <<< w) with hr
  have hr_val : r.val.toNat = m.toNat * 2 ^ w := by
    rw [hr, toNat_val_ofAzNat, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    calc m.toNat * 2 ^ w < 2 ^ n * 2 ^ w := Nat.mul_lt_mul_of_pos_right hm_lt (by positivity)
      _ = 2 ^ (n + w) := by rw [pow_add]
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcheck : r * r = a := by
    apply eq_of_toNat_val
    rw [toNat_val_mul, hr_val]
    set q := m.toNat * m.toNat / 2 ^ n with hq
    have hmq : m.toNat * m.toNat = 2 ^ n * q + uN := by rw [← hm_sq, hq, Nat.div_add_mod]
    have : m.toNat * 2 ^ w * (m.toNat * 2 ^ w) = 2 ^ k * q + a.val.toNat := by
      calc m.toNat * 2 ^ w * (m.toNat * 2 ^ w) = (m.toNat * m.toNat) * (2 ^ w * 2 ^ w) := by ring
        _ = (2 ^ n * q + uN) * 2 ^ v := by rw [hmq, ← pow_add, hvw, two_mul]
        _ = 2 ^ k * q + a.val.toNat := by rw [hk, ← hu2]; ring
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hak]
  rw [ite_eq_left hcheck]
  refine ⟨r, rfl, ?_⟩
  rw [hr_val, hrt, mul_comm (2 ^ w)]
  apply Nat.mul_le_mul_right
  calc m.toNat ≤ X.toNat := (AzNat.le_iff_toNat_le _ _).mp hmle
    _ = t % 2 ^ n := hXt.symm
    _ ≤ t := Nat.mod_le _ _

/-- **Completeness**: a root is returned exactly when the input is a square. -/
theorem sqrt?_isSome_iff (a : AzZModPow2 k) : (sqrt? a).isSome ↔ IsSquare (toZMod a) := by
  rw [isSquare_toZMod_iff]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    exact ⟨r, sqrt?_some hr⟩
  · rintro ⟨r', hr'⟩
    by_cases ha : a = 0
    · subst ha
      unfold sqrt?
      rw [show (0 : AzZModPow2 k).val = 0 from rfl, AzNat.trailingZeros_zero]
      rfl
    · obtain ⟨r, hr, _⟩ := sqrt?_of_root ha hr'
      rw [hr]; rfl

/-- **Minimality**: the returned root is the least root. -/
theorem sqrt?_le {a r : AzZModPow2 k} (h : sqrt? a = some r) (r' : AzZModPow2 k)
    (hr' : r' * r' = a) : r.val ≤ r'.val := by
  by_cases ha : a = 0
  · subst ha
    unfold sqrt? at h
    rw [show (0 : AzZModPow2 k).val = 0 from rfl, AzNat.trailingZeros_zero] at h
    obtain rfl := Option.some.inj h
    rw [AzNat.le_iff_toNat_le, toNat_val_zero]
    exact Nat.zero_le _
  · obtain ⟨r₀, hr₀, hle⟩ := sqrt?_of_root ha hr'
    rw [h] at hr₀
    obtain rfl := Option.some.inj hr₀
    exact (AzNat.le_iff_toNat_le _ _).mpr hle

end Azurite.AzZModPow2
