/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.PerfectPower
import Azurite.Bernstein.PerfectPower
import Azurite.Algorithm.Equiv.PrimeSieve
import Azurite.AzNat.Equiv.IsSquare
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.MulModPow2.Dispatch
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.RootInt
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.SquareModPow2.Dispatch
import Azurite.AzNat.Equiv.TrailingZeros

/-!
# Correctness of the perfect-power functions

* **`isPerfectPower_eq_true_iff`**: `isPerfectPower n = true ↔ IsPerfectPower n.toNat`.
* **`expressAsPower_eq_some`**: `expressAsPower n = some (x, k)` gives `1 < k`,
  `x ^ k = n`, and for `n ≥ 2` that `x` is not a perfect power.
* **`expressAsPower_eq_none_iff`**: `none` exactly when `n` is not a perfect power.

The Newton iterations that propose a root are not part of the argument: `oddRoot?` tests the
candidate `r` (`r ^ k ≡ m (mod 2 ^ b)`), and `odd_root_unique` then makes `r` the only
possible root.
-/

namespace Azurite.AzNat

/-- What a root finder returns: a `k`-th root of `m` if there is one. -/
def RootSpec (o : Option AzNat) (m k : ℕ) : Prop :=
  (∀ x, o = some x → x.toNat ^ k = m) ∧ (o = none → ¬ ∃ y, y ^ k = m)

private theorem toNat_one' : (1 : AzNat).toNat = 1 := by decide

/-- `powModPow2` computes `r ^ k mod 2 ^ b`. -/
theorem toNat_powModPow2 (r : AzNat) (b k : ℕ) :
    (powModPow2 r b k).toNat = r.toNat ^ k % 2 ^ b := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [powModPow2, toNat_modPow2, toNat_one', pow_zero]
    · rw [powModPow2]
      have hh := ih ((k + 1) / 2) (by omega)
      have hsplit : r.toNat ^ (k + 1) =
          (r.toNat ^ ((k + 1) / 2)) ^ 2 * r.toNat ^ ((k + 1) % 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      split_ifs with hodd
      · rw [toNat_mulDispatchModPow2, toNat_squareDispatchModPow2, hh, hsplit, hodd, pow_one]
        rw [Nat.mul_mod, Nat.mod_mod, Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      · have h0 : (k + 1) % 2 = 0 := by omega
        rw [toNat_squareDispatchModPow2, hh, hsplit, h0, pow_zero, mul_one, ← Nat.pow_mod]

/-- `kthRoot?` finds a `k`-th root if there is one. -/
theorem kthRoot?_spec (m : AzNat) {k : ℕ} (hk : 1 ≤ k) : RootSpec (kthRoot? m k) m.toNat k := by
  unfold kthRoot?
  constructor
  · intro x hx
    split_ifs at hx with h
    cases hx
    rw [isPow, decide_eq_true_iff] at h
    rw [← toNat_pow, h]
  · intro hx
    split_ifs at hx with h
    rwa [isPow_eq_true_iff m k hk] at h

/-- The candidate of `oddRoot?` is the only possible root. -/
private theorem candidate_unique {m r : AzNat} {k y : ℕ} (hm : Odd m.toNat) (hk : Odd k)
    (hr : r.toNat < 2 ^ ((m.size + k - 1) / k))
    (h : r.toNat ^ k % 2 ^ ((m.size + k - 1) / k) = m.toNat % 2 ^ ((m.size + k - 1) / k))
    (hy : y ^ k = m.toNat) : r.toNat = y := by
  have hk0 : 0 < k := hk.pos
  have hyo : Odd y := by
    rw [← hy] at hm
    exact (Nat.odd_pow_iff (by omega)).1 hm
  have hyb : y < 2 ^ ((m.size + k - 1) / k) := by
    apply root_lt_two_pow hk0
    rw [hy, ← size_toNat]
    exact Nat.lt_size_self _
  exact odd_root_unique hk hyo hr hyb (by rw [h, hy])

/-- `oddRoot?` finds a `k`-th root of an odd `m` for odd `k`, if there is one. -/
theorem oddRoot?_spec (m y : AzNat) {k : ℕ} (hm : Odd m.toNat) (hk : Odd k) :
    RootSpec (oddRoot? m y k) m.toNat k := by
  unfold oddRoot?
  simp only []
  generalize hr : (rootHint y (invModPow2Hint (ofNat k) ((m.size + k - 1) / k)) k
    ((m.size + k - 1) / k)).modPow2 ((m.size + k - 1) / k) = r
  have hrlt : r.toNat < 2 ^ ((m.size + k - 1) / k) := by
    rw [← hr, toNat_modPow2]
    exact Nat.mod_lt _ (by positivity)
  split_ifs with h1 h2 h3
  · exact kthRoot?_spec m hk.pos
  all_goals
    have hlow : r.toNat ^ k % 2 ^ ((m.size + k - 1) / k) =
        m.toNat % 2 ^ ((m.size + k - 1) / k) := by
      push Not at h1
      have := congrArg toNat h1
      rw [toNat_modPow2, toNat_modPow2, toNat_powModPow2,
        Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))] at this
      exact this
  · refine ⟨fun x hx => (by cases hx), fun _ => ?_⟩
    rintro ⟨z, hz⟩
    have hrz := candidate_unique hm hk hrlt hlow hz
    apply h2
    apply toNat_injective
    rw [toNat_powModPow2, toNat_modPow2, hrz, hz]
  · refine ⟨fun x hx => ?_, fun hx => (by cases hx)⟩
    cases hx
    rw [← toNat_pow, h3]
  · refine ⟨fun x hx => (by cases hx), fun _ => ?_⟩
    rintro ⟨z, hz⟩
    have hrz := candidate_unique hm hk hrlt hlow hz
    apply h3
    apply toNat_injective
    rw [toNat_pow, hrz, hz]

/-- `primeRoot?` finds a `p`-th root of an odd `m`, if there is one. -/
theorem primeRoot?_spec (m y : AzNat) {p : ℕ} (hm : Odd m.toNat) (hp : 0 < p) :
    RootSpec (primeRoot? m y p) m.toNat p := by
  unfold primeRoot?
  split_ifs with h2 hsq hodd
  · subst h2
    rw [isSquare_eq_true_iff] at hsq
    obtain ⟨r, hr⟩ := hsq
    refine ⟨fun x hx => ?_, fun hx => (by cases hx)⟩
    cases hx
    rw [toNat_sqrt, hr, Nat.sqrt_eq, pow_two]
  · subst h2
    refine ⟨fun x hx => (by cases hx), fun _ => ?_⟩
    rintro ⟨z, hz⟩
    apply hsq
    rw [isSquare_eq_true_iff]
    exact ⟨z, by rw [← hz, pow_two]⟩
  · exact oddRoot?_spec m y hm (Nat.odd_iff.2 hodd)
  · exact kthRoot?_spec m hp

/-- The odd part: `n = 2 ^ e * (n / 2 ^ e)` with an odd cofactor, `e` the number of trailing
zeros. -/
private theorem odd_part {N : ℕ} (hN : N ≠ 0) :
    N = 2 ^ padicValNat 2 N * (N / 2 ^ padicValNat 2 N) ∧ Odd (N / 2 ^ padicValNat 2 N) := by
  have hdvd : 2 ^ padicValNat 2 N ∣ N := pow_padicValNat_dvd
  refine ⟨(Nat.mul_div_cancel' hdvd).symm, ?_⟩
  have := Nat.not_dvd_ordCompl Nat.prime_two hN
  rw [Nat.factorization_def N Nat.prime_two] at this
  rw [Nat.odd_iff]
  omega

/-- What `perfectPowerStep` computes with, for `n ≠ 0`. -/
private theorem step_eq {n : AzNat} (hn : n.toNat ≠ 0) :
    perfectPowerStep n =
      (let e := padicValNat 2 n.toNat
       let m := n >>> e
       let cands := if e = 0 then primesUpTo m.size else (primesUpTo e).filter (e % · = 0)
       cands.toList.findSome? fun p =>
        (primeRoot? m (invModPow2Hint m ((m.size + 2) / 3)) p).map
          fun (r : AzNat) => ((r <<< (e / p) : AzNat), p)) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by decide)
  unfold perfectPowerStep
  rw [trailingZeros_eq_padicValNat n hn0]

private theorem toNat_shr (a : AzNat) (k : ℕ) : (a >>> k).toNat = a.toNat / 2 ^ k :=
  toNat_shiftRight a k

private theorem toNat_shl (a : AzNat) (k : ℕ) : (a <<< k).toNat = a.toNat * 2 ^ k :=
  toNat_shiftLeft a k

/-- A step found is a prime exponent and a root. -/
theorem perfectPowerStep_eq_some {n x : AzNat} {p : ℕ} (h : perfectPowerStep n = some (x, p)) :
    p.Prime ∧ x.toNat ^ p = n.toNat := by
  have hn : n.toNat ≠ 0 := by
    intro h0
    have : n = 0 := toNat_injective (by rw [h0]; decide)
    rw [this, perfectPowerStep, trailingZeros_zero] at h
    cases h
  rw [step_eq hn] at h
  simp only [] at h
  obtain ⟨q, hq, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨r, hr, hxp⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨hx, rfl⟩ := Prod.mk.inj hxp
  obtain ⟨hN, hodd⟩ := odd_part hn
  rw [← toNat_shr] at hN hodd
  -- `q` is a prime dividing `e`
  have hq' : q.Prime ∧ q ∣ padicValNat 2 n.toNat := by
    rw [Array.mem_toList_iff] at hq
    split_ifs at hq with he
    · exact ⟨(mem_primesUpTo.1 hq).1, by rw [he]; exact dvd_zero q⟩
    · rw [Array.mem_filter] at hq
      exact ⟨(mem_primesUpTo.1 hq.1).1, Nat.dvd_of_mod_eq_zero (by simpa using hq.2)⟩
  refine ⟨hq'.1, ?_⟩
  have hroot := (primeRoot?_spec _ _ hodd hq'.1.pos).1 r hr
  rw [← hx, toNat_shl, mul_pow, hroot, ← pow_mul, Nat.div_mul_cancel hq'.2, mul_comm]
  exact hN.symm

/-- No step for `n ≥ 2`: `n` is not a perfect power. -/
theorem perfectPowerStep_eq_none {n : AzNat} (hn : 2 ≤ n.toNat)
    (h : perfectPowerStep n = none) : ¬ IsPerfectPower n.toNat := by
  intro hpp
  obtain ⟨p, hp, x, hx⟩ := hpp.exists_prime
  have hn0 : n.toNat ≠ 0 := by omega
  rw [step_eq hn0] at h
  simp only [] at h
  rw [List.findSome?_eq_none_iff] at h
  obtain ⟨hN, hodd⟩ := odd_part hn0
  rw [← toNat_shr] at hN hodd
  have hx' := hx
  rw [hN] at hx'
  obtain ⟨hpe, r, hr⟩ := (pow_eq_two_pow_mul_iff hodd hp.pos).1 ⟨x, hx'⟩
  have hmem : p ∈ (if padicValNat 2 n.toNat = 0 then
      primesUpTo (n >>> padicValNat 2 n.toNat).size
      else (primesUpTo (padicValNat 2 n.toNat)).filter
        (padicValNat 2 n.toNat % · = 0)).toList := by
    rw [Array.mem_toList_iff]
    split_ifs with he
    · rw [mem_primesUpTo]
      refine ⟨hp, ?_⟩
      have hlt := exponent_lt_size hn hx
      have : (n >>> padicValNat 2 n.toNat).toNat = n.toNat := by
        rw [toNat_shr, he, pow_zero, Nat.div_one]
      rw [← size_toNat, this]
      omega
    · rw [Array.mem_filter, mem_primesUpTo]
      exact ⟨⟨hp, Nat.le_of_dvd (by omega) hpe⟩, by simpa using Nat.mod_eq_zero_of_dvd hpe⟩
  have hnone := h p hmem
  rw [Option.map_eq_none_iff] at hnone
  exact (primeRoot?_spec _ _ hodd hp.pos).2 hnone ⟨r, hr⟩

/-- `size ≤ 1` means `n ≤ 1`. -/
private theorem size_le_one_iff (n : AzNat) : n.size ≤ 1 ↔ n.toNat ≤ 1 := by
  rw [← size_toNat]
  constructor
  · intro h
    have h1 := Nat.lt_size_self n.toNat
    have h2 : 2 ^ n.toNat.size ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
    omega
  · intro h
    have : n.toNat < 2 ^ 1 := by omega
    exact Nat.size_le.2 this

/-- The loop of `expressAsPower`: for `2 ≤ x < 2 ^ fuel` the result `(y, j)` has
`j = k t`, `y ^ t = x`, and `y ≥ 2` is not a perfect power. -/
private theorem go_spec (fuel : ℕ) : ∀ (x : AzNat) (k : ℕ), 2 ≤ x.toNat → x.toNat < 2 ^ fuel →
    ∃ t, 1 ≤ t ∧ (expressAsPower.go fuel x k).2 = k * t ∧
      (expressAsPower.go fuel x k).1.toNat ^ t = x.toNat ∧
      ¬ IsPerfectPower (expressAsPower.go fuel x k).1.toNat := by
  induction fuel with
  | zero => intro x k h2 hlt; simp at hlt; omega
  | succ fuel ih =>
    intro x k h2 hlt
    rw [expressAsPower.go]
    rcases hstep : perfectPowerStep x with _ | ⟨r, p⟩
    · exact ⟨1, Nat.le_refl 1, by simp, by simp, perfectPowerStep_eq_none h2 hstep⟩
    · obtain ⟨hp, hrp⟩ := perfectPowerStep_eq_some hstep
      have hp2 := hp.two_le
      have hr2 : 2 ≤ r.toNat := by
        by_contra hc
        have : r.toNat = 0 ∨ r.toNat = 1 := by omega
        rcases this with h0 | h0
        · rw [h0, zero_pow (by omega)] at hrp; omega
        · rw [h0, one_pow] at hrp; omega
      have hrlt : r.toNat < 2 ^ fuel := by
        by_contra hc
        push Not at hc
        have hsq : r.toNat ^ 2 ≤ r.toNat ^ p := Nat.pow_le_pow_right (by omega) hp2
        have h1 : (2 ^ fuel) ^ 2 ≤ r.toNat ^ 2 := Nat.pow_le_pow_left hc 2
        have hf : 1 ≤ fuel := by
          by_contra hf0
          have : fuel = 0 := by omega
          subst this
          omega
        have h3 : 2 ^ (fuel + 1) ≤ (2 ^ fuel) ^ 2 := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨t, ht1, hj, hy, hnp⟩ := ih r (k * p) hr2 hrlt
      refine ⟨p * t, by nlinarith, by rw [hj, mul_assoc], ?_, hnp⟩
      rw [mul_comm p t, pow_mul, hy, hrp]

/-- **`expressAsPower` returns a decomposition** `x ^ k = n` with `k > 1`, and for `n ≥ 2`
with `x` not a perfect power. -/
theorem expressAsPower_eq_some {n x : AzNat} {k : ℕ} (h : expressAsPower n = some (x, k)) :
    1 < k ∧ x.toNat ^ k = n.toNat ∧ (2 ≤ n.toNat → ¬ IsPerfectPower x.toNat) := by
  unfold expressAsPower at h
  split_ifs at h with hs
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [size_le_one_iff] at hs
    refine ⟨by norm_num, ?_, fun h2 => by omega⟩
    have : n.toNat = 0 ∨ n.toNat = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0] <;> norm_num
  · rw [size_le_one_iff] at hs
    rcases hstep : perfectPowerStep n with _ | ⟨r, p⟩
    · rw [hstep] at h
      cases h
    · rw [hstep] at h
      obtain ⟨hp, hrp⟩ := perfectPowerStep_eq_some hstep
      have hp2 := hp.two_le
      have hr2 : 2 ≤ r.toNat := by
        by_contra hc
        have : r.toNat = 0 ∨ r.toNat = 1 := by omega
        rcases this with h0 | h0
        · rw [h0, zero_pow (by omega)] at hrp; omega
        · rw [h0, one_pow] at hrp; omega
      have hrlt : r.toNat < 2 ^ n.size := by
        have h1 : r.toNat ^ 1 ≤ r.toNat ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_one] at h1
        have h2 := Nat.lt_size_self n.toNat
        rw [size_toNat] at h2
        omega
      obtain ⟨t, ht1, hj, hy, hnp⟩ := go_spec n.size r p hr2 hrlt
      have hxk := Option.some.inj h
      rw [hxk] at hj hy hnp
      simp only at hj hy hnp
      refine ⟨by rw [hj]; nlinarith, ?_, fun _ => hnp⟩
      rw [hj, mul_comm, pow_mul, hy, hrp]

/-- **`expressAsPower` fails exactly on the numbers that are not perfect powers.** -/
theorem expressAsPower_eq_none_iff (n : AzNat) :
    expressAsPower n = none ↔ ¬ IsPerfectPower n.toNat := by
  constructor
  · intro h
    unfold expressAsPower at h
    split_ifs at h with hs
    rw [size_le_one_iff] at hs
    rcases hstep : perfectPowerStep n with _ | ⟨r, p⟩
    · exact perfectPowerStep_eq_none (by omega) hstep
    · rw [hstep] at h
      cases h
  · intro h
    rcases hres : expressAsPower n with _ | ⟨x, k⟩
    · rfl
    · obtain ⟨hk, hxk, -⟩ := expressAsPower_eq_some hres
      exact absurd ⟨x.toNat, k, hk, hxk⟩ h

/-- **Correctness of the perfect-power test**: `true` exactly on the perfect powers. -/
theorem isPerfectPower_eq_true_iff (n : AzNat) :
    isPerfectPower n = true ↔ IsPerfectPower n.toNat := by
  unfold isPerfectPower
  rw [Bool.or_eq_true, decide_eq_true_iff, size_le_one_iff]
  constructor
  · rintro (h | h)
    · have : n.toNat = 0 ∨ n.toNat = 1 := by omega
      rcases this with h0 | h0 <;> rw [h0]
      · exact isPerfectPower_zero
      · exact isPerfectPower_one
    · obtain ⟨⟨r, p⟩, hstep⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨hp, hrp⟩ := perfectPowerStep_eq_some hstep
      exact ⟨r.toNat, p, hp.one_lt, hrp⟩
  · intro h
    by_cases h1 : n.toNat ≤ 1
    · exact Or.inl h1
    · right
      by_contra hc
      rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hc
      exact perfectPowerStep_eq_none (by omega) hc h

/-- `ofNat`-phrased correctness. -/
theorem isPerfectPower_ofNat_eq_true_iff (k : ℕ) :
    isPerfectPower (ofNat k) = true ↔ IsPerfectPower k := by
  rw [isPerfectPower_eq_true_iff, toNat_ofNat]

end Azurite.AzNat
