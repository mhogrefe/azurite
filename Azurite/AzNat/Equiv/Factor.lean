/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Factor
import Azurite.AzNat.Equiv.IsPrime
import Azurite.AzNat.Equiv.IsPrimeLucas
import Azurite.AzNat.Equiv.PerfectPower
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.Algorithm.Equiv.PrimeSieve
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.List.Sort

/-!
# Correctness of the integer factorization

**`factor_expand`**: `factor n`, written out with multiplicities, is Mathlib's
`Nat.primeFactorsList n.toNat`.  With it:

* `factor_prime`, `factor_pos`: every `(p, e)` has `p` prime and `e > 0`;
* `factor_sorted`: the primes are strictly increasing;
* `factor_exponent`: `e = n.toNat.factorization p.toNat`;
* `factor_prod`: `∏ p ^ e = n` for `n ≠ 0`.

The proof does not look at how divisors are found: `splitFactors_spec` holds for every
function `find`, because a divisor is used only after it has been checked, and primality is
`isPrime_eq_true_iff`.  Likewise a proposed list of factors (`factorHint`) is used only if it
passes `checkFactors` (`checkFactors_spec`, `hinted_spec`).  A list of primes with product `n` is a permutation of
`Nat.primeFactorsList n` (`Nat.primeFactorsList_unique`), and sorting makes it equal.
-/

namespace Azurite.AzNat

/-- `l` is a list of primes with product `n`. -/
def FactorsOf (l : List AzNat) (n : ℕ) : Prop :=
  (∀ p ∈ l, p.toNat.Prime) ∧ (l.map toNat).prod = n

private theorem toNat_one'' : (1 : AzNat).toNat = 1 := by decide

private theorem toNat_zero'' : (0 : AzNat).toNat = 0 := by decide

private theorem eq_iff_toNat {a b : AzNat} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, toNat_injective⟩

/-! ### Complete trial division -/

theorem trialFactor.go_spec (n d : AzNat) : 2 ≤ d.toNat → 2 ≤ n.toNat →
    (∀ p : ℕ, p.Prime → p ∣ n.toNat → d.toNat ≤ p) → FactorsOf (trialFactor.go n d) n.toNat := by
  induction n, d using trialFactor.go.induct with
  | case1 n d h1 =>
    intro hd hn hmin
    rw [trialFactor.go]
    simp only [h1, ↓reduceDIte]
    rw [lt_iff_toNat_lt, toNat_mul] at h1
    have hp : n.toNat.Prime := by
      by_contra hnp
      have h3 := Nat.minFac_sq_le_self (by omega) hnp
      have h4 := hmin _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
      nlinarith
    exact ⟨by simpa using hp, by simp⟩
  | case2 n d h1 h2 =>
    intro hd hn hmin
    rw [lt_iff_toNat_lt, toNat_ofNat] at h2
    omega
  | case3 n d h1 h2 hmod hq =>
    intro hd hn hmin
    rw [trialFactor.go]
    simp only [h1, h2, hmod, hq, ↓reduceDIte, ↓reduceIte]
    have hdvd : d.toNat ∣ n.toNat := by
      rw [eq_iff_toNat, toNat_mod, toNat_zero''] at hmod
      exact Nat.dvd_of_mod_eq_zero hmod
    have hdp : d.toNat.Prime := by
      rw [Nat.prime_def_minFac]
      refine ⟨hd, Nat.le_antisymm (Nat.minFac_le (by omega : 0 < d.toNat)) ?_⟩
      exact hmin _ (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd _).trans hdvd)
    rw [eq_iff_toNat, toNat_div, toNat_one''] at hq
    refine ⟨by simpa using hdp, ?_⟩
    have := Nat.div_mul_cancel hdvd
    rw [hq] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    omega
  | case4 n d h1 h2 hmod hq ih =>
    intro hd hn hmin
    rw [trialFactor.go]
    simp only [h1, h2, hmod, hq, ↓reduceDIte, ↓reduceIte]
    have hdvd : d.toNat ∣ n.toNat := by
      rw [eq_iff_toNat, toNat_mod, toNat_zero''] at hmod
      exact Nat.dvd_of_mod_eq_zero hmod
    have hdp : d.toNat.Prime := by
      rw [Nat.prime_def_minFac]
      refine ⟨hd, Nat.le_antisymm (Nat.minFac_le (by omega : 0 < d.toNat)) ?_⟩
      exact hmin _ (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd _).trans hdvd)
    have hq1 : (n / d).toNat ≠ 1 := by
      rw [eq_iff_toNat, toNat_one''] at hq
      exact hq
    have hmul : n.toNat / d.toNat * d.toNat = n.toNat := Nat.div_mul_cancel hdvd
    have hq2 : 2 ≤ (n / d).toNat := by
      rw [toNat_div] at hq1 ⊢
      obtain ⟨q, hq'⟩ : ∃ q, n.toNat / d.toNat = q := ⟨_, rfl⟩
      rw [hq'] at hq1 hmul ⊢
      have : q ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hmul
        omega
      omega
    obtain ⟨hpr, hprod⟩ := ih hd hq2 (fun p hp hpd => hmin p hp (by
      rw [toNat_div] at hpd
      exact hpd.trans (Nat.div_dvd_of_dvd hdvd)))
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hdp
      · exact hpr p hp
    · rw [List.map_cons, List.prod_cons, hprod, toNat_div, mul_comm]
      exact hmul
  | case5 n d h1 h2 hmod ih =>
    intro hd hn hmin
    rw [trialFactor.go]
    simp only [h1, h2, hmod, ↓reduceDIte, ↓reduceIte]
    have hnd : ¬ d.toNat ∣ n.toNat := by
      intro hdvd
      apply hmod
      rw [eq_iff_toNat, toNat_mod, toNat_zero'']
      exact Nat.mod_eq_zero_of_dvd hdvd
    refine ih (by rw [toNat_add, toNat_one'']; omega) hn (fun p hp hpd => ?_)
    rw [toNat_add, toNat_one'']
    have := hmin p hp hpd
    rcases Nat.lt_or_eq_of_le this with h | h
    · omega
    · exact absurd (h ▸ hpd) hnd

/-- Complete trial division gives the prime factors of `n ≥ 2`. -/
theorem trialFactor_spec {n : AzNat} (hn : 2 ≤ n.toNat) : FactorsOf (trialFactor n) n.toNat :=
  trialFactor.go_spec n (ofNat 2) (by rw [toNat_ofNat]) hn
    (fun p hp _ => by rw [toNat_ofNat]; exact hp.two_le)

/-! ### Trial division by a list of primes -/

/-- A cofactor and a list of primes whose product with it is `N`. -/
def SplitOf (r : AzNat × List AzNat) (N : ℕ) : Prop :=
  (∀ q ∈ r.2, q.toNat.Prime) ∧ (r.2.map toNat).prod * r.1.toNat = N

theorem pullOut_spec {p : AzNat} (hp : p.toNat.Prime) {N : ℕ} :
    ∀ (fuel : ℕ) (n : AzNat) (acc : List AzNat), SplitOf (n, acc) N →
      SplitOf (pullOut p fuel n acc) N := by
  intro fuel
  induction fuel with
  | zero => intro n acc h; exact h
  | succ fuel ih =>
    intro n acc h
    rw [pullOut]
    split_ifs with hmod
    · apply ih
      obtain ⟨h1, h2⟩ := h
      have hdvd : p.toNat ∣ n.toNat := by
        rw [eq_iff_toNat, toNat_mod, toNat_zero''] at hmod
        exact Nat.dvd_of_mod_eq_zero hmod
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact h1 q hq
      · simp only [List.map_cons, List.prod_cons, toNat_div]
        rw [← h2, mul_comm p.toNat, mul_assoc, Nat.mul_div_cancel' hdvd]
    · exact h

theorem trialDivideBy_spec {N : ℕ} : ∀ (ps : List ℕ), (∀ p ∈ ps, p.Prime) →
    ∀ (n : AzNat) (acc : List AzNat), SplitOf (n, acc) N →
      SplitOf (trialDivideBy ps n acc) N := by
  intro ps
  induction ps with
  | nil => intro _ n acc h; exact h
  | cons p ps ih =>
    intro hps n acc h
    rw [trialDivideBy]
    split_ifs with h1
    · exact h
    · exact ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ _
        (pullOut_spec (by rw [toNat_ofNat]; exact hps p List.mem_cons_self) _ _ _ h)

theorem trialDivide_spec (n : AzNat) : SplitOf (trialDivide n) n.toNat := by
  unfold trialDivide
  apply trialDivideBy_spec
  · intro p hp
    exact (mem_primesUpTo.1 (Array.mem_toList_iff.1 hp)).1
  · exact ⟨by simp, by simp⟩

/-! ### Splitting -/

private theorem prod_flatMap_replicate (l : List AzNat) (k : ℕ) :
    ((l.flatMap (List.replicate k)).map toNat).prod = (l.map toNat).prod ^ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons, mul_pow]

private theorem two_le_of_pow {x k n : ℕ} (hk : 1 < k) (hn : 2 ≤ n) (h : x ^ k = n) : 2 ≤ x := by
  by_contra hc
  have : x = 0 ∨ x = 1 := by omega
  rcases this with rfl | rfl
  · rw [zero_pow (by omega)] at h; omega
  · rw [one_pow] at h; omega

/-! ### Checked proposals -/

/-- A list that passes `checkFactors` is a list of primes with product `n`. -/
theorem checkFactors_spec {n : AzNat} {l : List AzNat} (h : checkFactors n l = true) :
    FactorsOf l n.toNat := by
  rw [checkFactors, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  refine ⟨fun p hp => (isPrime_eq_true_iff p).1 (h.2 p hp), ?_⟩
  rw [← h.1, toNat_listProd]

/-- `hinted` is as good as its slow path. -/
theorem hinted_spec {n : AzNat} {slow : Unit → List AzNat}
    (h : FactorsOf (slow ()) n.toNat) : FactorsOf (hinted n slow) n.toNat := by
  unfold hinted
  simp only []
  split_ifs with hc
  · exact checkFactors_spec hc
  · exact h

/-- **`splitFactors` gives the prime factors of `n ≥ 2`, whatever `find` is.** -/
theorem splitFactors_spec (find : AzNat → Option AzNat) :
    ∀ (fuel : ℕ) (n : AzNat), 2 ≤ n.toNat → FactorsOf (splitFactors find fuel n) n.toNat := by
  intro fuel
  induction fuel with
  | zero => intro n hn; exact trialFactor_spec hn
  | succ fuel ih =>
    intro n hn
    rw [splitFactors]
    apply hinted_spec
    split_ifs with hprime
    · rw [isPrime_eq_true_iff] at hprime
      exact ⟨by simpa using hprime, by simp⟩
    · rcases hpow : expressAsPower n with _ | ⟨x, k⟩
      · simp only []
        rcases hfind : find n with _ | d
        · exact trialFactor_spec hn
        · simp only []
          split_ifs with hd
          · obtain ⟨hd1, hd2, hd3⟩ := hd
            rw [lt_iff_toNat_lt, toNat_ofNat] at hd1
            rw [lt_iff_toNat_lt] at hd2
            have hdvd : d.toNat ∣ n.toNat := by
              rw [eq_iff_toNat, toNat_mod, toNat_zero''] at hd3
              exact Nat.dvd_of_mod_eq_zero hd3
            have hmul : d.toNat * (n.toNat / d.toNat) = n.toNat := Nat.mul_div_cancel' hdvd
            have hq2 : 2 ≤ (n / d).toNat := by
              rw [toNat_div]
              obtain ⟨q, hq'⟩ : ∃ q, n.toNat / d.toNat = q := ⟨_, rfl⟩
              rw [hq'] at hmul ⊢
              by_contra hc
              have : q = 0 ∨ q = 1 := by omega
              rcases this with rfl | rfl
              · rw [mul_zero] at hmul; omega
              · rw [mul_one] at hmul; omega
            obtain ⟨hp1, hq1⟩ := ih d (by omega)
            obtain ⟨hp2, hq2'⟩ := ih (n / d) hq2
            refine ⟨?_, ?_⟩
            · intro p hp
              rcases List.mem_append.1 hp with hp | hp
              · exact hp1 p hp
              · exact hp2 p hp
            · rw [List.map_append, List.prod_append, hq1, hq2', toNat_div]
              exact hmul
          · exact trialFactor_spec hn
      · simp only []
        obtain ⟨hk, hxk, -⟩ := expressAsPower_eq_some hpow
        obtain ⟨hp1, hq1⟩ := ih x (two_le_of_pow hk hn hxk)
        refine ⟨?_, ?_⟩
        · intro p hp
          obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.1 hp
          rw [(List.mem_replicate.1 hpq).2]
          exact hp1 q hq
        · rw [prod_flatMap_replicate, hq1, hxk]

private theorem size_le_one_iff' (n : AzNat) : n.size ≤ 1 ↔ n.toNat ≤ 1 := by
  rw [← size_toNat]
  constructor
  · intro h
    have h1 := Nat.lt_size_self n.toNat
    have h2 : 2 ^ n.toNat.size ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
    omega
  · intro h
    have : n.toNat < 2 ^ 1 := by omega
    exact Nat.size_le.2 this

/-- The unordered list of prime factors of `n ≥ 2` is a list of primes with product `n`. -/
theorem primeFactorList_spec {n : AzNat} (hn : 2 ≤ n.toNat) :
    FactorsOf (primeFactorList n) n.toNat := by
  unfold primeFactorList
  have hs : ¬ n.size ≤ 1 := by rw [size_le_one_iff']; omega
  simp only [hs, ↓reduceIte]
  apply hinted_spec
  obtain ⟨hp, hprod⟩ := trialDivide_spec n
  by_cases h1 : (trialDivide n).1 = 1
  · simp only [h1, ↓reduceIte]
    rw [h1, toNat_one'', mul_one] at hprod
    exact ⟨hp, hprod⟩
  · simp only [h1, ↓reduceIte]
    have hr2 : 2 ≤ (trialDivide n).1.toNat := by
      by_contra hc
      have : (trialDivide n).1.toNat = 0 ∨ (trialDivide n).1.toNat = 1 := by omega
      rcases this with h0 | h0
      · rw [h0, mul_zero] at hprod; omega
      · exact h1 (toNat_injective (by rw [h0, toNat_one'']))
    obtain ⟨hp2, hprod2⟩ := splitFactors_spec findDivisor (trialDivide n).1.size _ hr2
    refine ⟨?_, ?_⟩
    · intro p hp'
      rcases List.mem_append.1 hp' with h | h
      · exact hp p h
      · exact hp2 p h
    · rw [List.map_append, List.prod_append, hprod2, hprod]

/-- The unordered list of prime factors is a permutation of Mathlib's. -/
theorem primeFactorList_perm (n : AzNat) :
    ((primeFactorList n).map toNat).Perm (Nat.primeFactorsList n.toNat) := by
  by_cases hn : 2 ≤ n.toNat
  · obtain ⟨hp, hprod⟩ := primeFactorList_spec hn
    apply Nat.primeFactorsList_unique hprod
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
    exact hp q hq
  · have hs : n.size ≤ 1 := by rw [size_le_one_iff']; omega
    unfold primeFactorList
    simp only [hs, ↓reduceIte]
    have : n.toNat = 0 ∨ n.toNat = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0] <;> simp

/-- The sorted list of prime factors is Mathlib's. -/
theorem sorted_primeFactorList (n : AzNat) :
    ((primeFactorList n).mergeSort (· ≤ ·)).map toNat = Nat.primeFactorsList n.toNat := by
  apply List.Perm.eq_of_sortedLE
  · rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    have := (List.sortedLE_mergeSort (l := primeFactorList n)).pairwise
    exact this.imp fun h => (le_iff_toNat_le _ _).1 h
  · exact Nat.primeFactorsList_sorted _
  · exact ((List.mergeSort_perm _ _).map toNat).trans (primeFactorList_perm n)

/-! ### Runs -/

theorem groupRuns_expand (l : List AzNat) :
    (groupRuns l).flatMap (fun pe => List.replicate pe.2 pe.1) = l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [groupRuns]
    rcases h : groupRuns ps with _ | ⟨⟨q, e⟩, rest⟩
    · rw [h] at ih
      simp only [List.flatMap_nil] at ih
      simp [← ih]
    · rw [h] at ih
      simp only []
      split_ifs with hpq
      · subst hpq
        rw [← ih]
        simp [List.replicate_succ]
      · rw [← ih]
        simp

theorem groupRuns_pos (l : List AzNat) : ∀ pe ∈ groupRuns l, 0 < pe.2 := by
  induction l with
  | nil => intro pe h; simp [groupRuns] at h
  | cons p ps ih =>
    intro pe hpe
    rw [groupRuns] at hpe
    rcases h : groupRuns ps with _ | ⟨⟨q, e⟩, rest⟩
    · rw [h] at hpe
      simp only [List.mem_singleton] at hpe
      rw [hpe]
      exact Nat.one_pos
    · rw [h] at hpe ih
      simp only [] at hpe
      split_ifs at hpe with hpq
      · rcases List.mem_cons.1 hpe with rfl | hm
        · exact Nat.succ_pos _
        · exact ih pe (List.mem_cons_of_mem _ hm)
      · rcases List.mem_cons.1 hpe with rfl | hm
        · exact Nat.one_pos
        · exact ih pe hm

theorem groupRuns_key_mem (l : List AzNat) : ∀ pe ∈ groupRuns l, pe.1 ∈ l := by
  intro pe hpe
  have h := groupRuns_expand l
  have hpos := groupRuns_pos l pe hpe
  rw [← h, List.mem_flatMap]
  exact ⟨pe, hpe, List.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem groupRuns_sorted (l : List AzNat) (hl : l.Pairwise (· ≤ ·)) :
    ((groupRuns l).map (·.1)).Pairwise (· < ·) := by
  induction l with
  | nil => simp [groupRuns]
  | cons p ps ih =>
    obtain ⟨hp, hps⟩ := List.pairwise_cons.1 hl
    have ih' := ih hps
    rw [groupRuns]
    rcases h : groupRuns ps with _ | ⟨⟨q, e⟩, rest⟩
    · simp
    · rw [h] at ih'
      simp only []
      split_ifs with hpq
      · exact ih'
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨?_, ih'⟩
        have hq : q ∈ ps := groupRuns_key_mem ps (q, e) (by rw [h]; exact List.mem_cons_self)
        have hlt : p < q := lt_of_le_of_ne (hp q hq) hpq
        intro a ha
        rw [List.map_cons] at ha ih'
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hlt
        · exact lt_trans hlt ((List.pairwise_cons.1 ih').1 a ha)

/-! ### The factorization -/

/-- **The factorization written out with multiplicities is Mathlib's list of prime
factors.** -/
theorem factor_expand (n : AzNat) :
    (factor n).flatMap (fun pe => List.replicate pe.2 pe.1.toNat) =
      Nat.primeFactorsList n.toNat := by
  rw [← sorted_primeFactorList, factor]
  conv_rhs => rw [← groupRuns_expand ((primeFactorList n).mergeSort (· ≤ ·))]
  rw [List.map_flatMap]
  simp only [List.map_replicate]

/-- The exponents are positive. -/
theorem factor_pos {n : AzNat} {pe : AzNat × ℕ} (h : pe ∈ factor n) : 0 < pe.2 :=
  groupRuns_pos _ pe h

/-- The bases are primes. -/
theorem factor_prime {n : AzNat} {pe : AzNat × ℕ} (h : pe ∈ factor n) : pe.1.toNat.Prime := by
  apply Nat.prime_of_mem_primeFactorsList (n := n.toNat)
  rw [← factor_expand, List.mem_flatMap]
  exact ⟨pe, h, List.mem_replicate.2 ⟨by have := factor_pos h; omega, rfl⟩⟩

/-- The primes are strictly increasing. -/
theorem factor_sorted (n : AzNat) : ((factor n).map (·.1.toNat)).Pairwise (· < ·) := by
  have h := groupRuns_sorted ((primeFactorList n).mergeSort (· ≤ ·))
    (List.sortedLE_mergeSort (l := primeFactorList n)).pairwise
  rw [List.pairwise_map] at h ⊢
  exact h.imp fun h => (lt_iff_toNat_lt _ _).1 h

private theorem count_expand (L : List (ℕ × ℕ)) (hL : (L.map (·.1)).Pairwise (· < ·))
    {p e : ℕ} (h : (p, e) ∈ L) :
    (L.flatMap fun pe => List.replicate pe.2 pe.1).count p = e := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rw [List.map_cons, List.pairwise_cons] at hL
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.1 h with rfl | hm
    · have : (L.flatMap fun pe => List.replicate pe.2 pe.1).count p = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨b, hb, hpb⟩ := List.mem_flatMap.1 hmem
        have := hL.1 b.1 (List.mem_map_of_mem hb)
        rw [(List.mem_replicate.1 hpb).2] at this
        exact lt_irrefl _ this
      rw [this]
      simp
    · have hne : a.1 ≠ p := by
        have := hL.1 p (List.mem_map_of_mem (f := (·.1)) hm)
        exact ne_of_lt this
      rw [ih hL.2 hm, List.count_replicate]
      simp [hne]

/-- **The exponents are those of Mathlib's `Nat.factorization`.** -/
theorem factor_exponent {n : AzNat} {pe : AzNat × ℕ} (h : pe ∈ factor n) :
    pe.2 = n.toNat.factorization pe.1.toNat := by
  rw [← Nat.primeFactorsList_count_eq, ← factor_expand]
  have hL : (((factor n).map fun pe => (pe.1.toNat, pe.2)).map (·.1)).Pairwise (· < ·) := by
    rw [List.map_map]
    exact factor_sorted n
  have := count_expand _ hL (p := pe.1.toNat) (e := pe.2) (List.mem_map_of_mem h)
  rw [List.flatMap_map] at this
  exact this.symm

/-- **The product of the prime powers is `n`**, for `n ≠ 0`. -/
theorem factor_prod {n : AzNat} (hn : n.toNat ≠ 0) :
    ((factor n).map fun pe => pe.1.toNat ^ pe.2).prod = n.toNat := by
  have h := congrArg List.prod (factor_expand n)
  rw [Nat.prod_primeFactorsList hn] at h
  rw [← h]
  generalize factor n = L
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, List.flatMap_cons, List.prod_append,
      List.prod_replicate]

end Azurite.AzNat
