/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, (5.2)–(5.5): the moduli `s₁`, `s₂` and the
  selection of `t` and `s`.**

  Let `t'` be an even divisor of `t`, `F = f⁻·f⁺` the factored part
  of `n² − 1`, and

    **(5.2)**  `s₁ = ½ ∏_{p ∣ F} p^(v_p(t') + v_p(F))`

  (`s1`, defined per prime with the `½` absorbed as `−1` in the
  exponent of `2`; `two_mul_s1` recovers the paper's form).  Then

    **(5.3)**  for all `r ∣ n`: `r ≡ n^(l(r)) (mod s₁)`, where
               `l(r) ≡ l_p(r) (mod p^(v_p(t')))` for all `p ∣ t'`,

  "because `n` passed the Lucas–Lehmer test" (cf. (1.3)(e)); and
  (5.1) holds for the primes of `s₁` (Remark (4.5)).  If
  `s₁ > n^(1/2)`, (5.3) suffices for the final trial division (1.3)(l)
  with `(t', s₁)`.  Otherwise let `s̄₂` be a product of distinct
  `q`-primes with `q − 1 ∣ t'` and `q ∤ s₁` (found among the factors of
  `e(t)`); the Jacobi-sum tests with `t'` combined with (5.3) give
  `r ≡ n^(l(r)) (mod s₁·s₂)` with

    **(5.4)**  `s₂ = s̄₂ · ∏_{p ∣ t', p ∣ s̄₂} p^(v_p(n^(p−1)−1) + v_p(t') − 1)`

  (`s2`, defined per prime `q ∣ s̄₂` as the `q`-part `s2Part`:
  `q^(v_q(n^(q−1)−1) + v_q(t'))` if `q ∣ t'`, else `q` — the factor
  `q` of `s̄₂` supplies the `−1`), and one needs `s₁·s₂ > n^(1/2)`.

  **What is proved here.**  The exponents in `s₁` and `s₂` are
  exactly those for which `n^(t') ≡ 1 (mod s₁·s₂)`
  (`pow_modEq_one_s1`, `pow_modEq_one_s2`, `pow_modEq_one_s1_mul_s2`)
  — the fact that makes "`l(r)` modulo `t'`" meaningful and that
  feeds the exponent reduction of the final trial division.  The
  engine is lifting-the-exponent (`pow_prime_pow_modEq_one_lift`):
  `a ≡ 1 (mod p^m)` ⟹ `a^(p^k) ≡ 1 (mod p^(m+k))`.  For `p ∣ F`:
  `n² ≡ 1 (mod p^(v_p(F)))` lifts along `p^(v_p(t'))` and
  `2·p^(v_p(t')) ∣ t'` for odd `p` (this is where `t'` even is used);
  for `p = 2` only `2^(v_2(t')) ∣ t'`, whence the `−1`.  For
  `q ∣ s̄₂`: Fermat `n^(q−1) ≡ 1 (mod q^(v_q(n^(q−1)−1)))` lifts along
  `q^(v_q(t'))`, and `(q−1)·q^(v_q(t')) ∣ t'`.  Coprimality of `s₁`
  and `s₂` (`coprime_s1_s2`) follows from `q ∤ F` for `q ∣ s̄₂`.

  **What is deferred — the assembly theorem.**  (5.3) itself is the
  Lucas–Lehmer divisor confinement.  Its proof needs, per prime
  `r ∣ n`, an exponent *coherent across primes*: with
  `ε(r) ∈ {0, 1}` recording whether `T² − uT − a` is irreducible
  modulo `r`, Test (4.3) gives `r ≡ n^(ε(r)) (mod p^(v_p(F)))` for
  odd `p ∣ f⁺` (the norm-one group of `A ⊗ ℤ/r` has order `r − 1`
  when the polynomial splits and `r + 1` when it is irreducible),
  Test (4.2) gives `r ≡ 1 (mod p^(v_p(F)))` for `p ∣ f⁻`, and
  (4.4)(c1)/(c2) give the `2`-adic (6.4) exponents with parity
  `ε(r)` (`lemma_7_23`'s Legendre criterion, resp. the (10.8)
  argument: the same discriminant governs both).  The `p`-adic
  digits then come from (10.7).  Because the `s₁`-primes do not
  satisfy `p − 1 ∣ t'`, condition (2.3) fails for `s₁·s₂` and
  Theorem (6.3) does not apply as stated: the 1987 assembly is a
  generalized Theorem (6.3) in which the character hypotheses at the
  `s₁`-primes are replaced by this confinement.  Both are recorded as
  the next proof obligations of the arc.

  **(5.5) Selection of `t` and `s`** (spec level, over `ℕ`).  For every
  even divisor `t'` of `t`: `s₁ := s1 t' F`; if `n < s₁²` the
  `q`-primes are not needed; else start from `s̄₂ = ∏_{q−1 ∣ t', q ∤ s₁} q`
  (`s2barInit`) — if `s₁·s₂ ≤ n^(1/2)` this `t'` fails — and greedily
  remove, while some `q` can be removed keeping `s₁·s₂ > n^(1/2)`,
  the removable `q` with `w(q)/log(q^(v_q(s₂)))` largest (`prune`;
  the paper notes the exact problem is a knapsack problem, [2, §4]);
  the cost is `c(t') = t'·c_ftd + Σ_{q ∣ s̄₂} w(q)` (`totalCost`) and
  the `t'` of least cost is chosen (`selection_5_5`).  Our comparison
  of the ratios uses `Nat.log 2` of the `q`-parts; correctness never
  depends on the heuristic, only on the guard `n < (s₁·s₂)²`
  (`bigEnough`).  Guarded on a small example below.
-/
import Azurite.CohenLenstra.Impl_5_1
import Azurite.CohenLenstra.Theorem_6_3

namespace Azurite

namespace CL

/-! ### The moduli `s₁` and `s₂` -/

/-- The exponent of `p` in `s₁`: `v_p(t') + v_p(F)`, less one for
`p = 2` (the paper's `½`). -/
def s1Exp (t' F p : ℕ) : ℕ :=
  padicValNat p t' + padicValNat p F - if p = 2 then 1 else 0

/-- **(5.2)**: `s₁ = ½ ∏_{p ∣ F} p^(v_p(t') + v_p(F))`. -/
def s1 (t' F : ℕ) : ℕ := ∏ p ∈ F.primeFactors, p ^ s1Exp t' F p

/-- The paper's form of (5.2): `2·s₁ = ∏_{p ∣ F} p^(v_p(t') + v_p(F))`
for even `F`. -/
theorem two_mul_s1 (t' : ℕ) {F : ℕ} (hF0 : F ≠ 0) (hF : 2 ∣ F) :
    2 * s1 t' F
      = ∏ p ∈ F.primeFactors, p ^ (padicValNat p t' + padicValNat p F) := by
  have h2 : 2 ∈ F.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hF, hF0⟩
  rw [s1, ← Finset.mul_prod_erase _ _ h2, ← Finset.mul_prod_erase _ _ h2]
  have hrest : ∏ p ∈ F.primeFactors.erase 2, p ^ s1Exp t' F p
      = ∏ p ∈ F.primeFactors.erase 2,
          p ^ (padicValNat p t' + padicValNat p F) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [s1Exp, ite_eq_right (Finset.mem_erase.mp hp).1, Nat.sub_zero]
  rw [hrest, ← mul_assoc]
  congr 1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : 1 ≤ padicValNat 2 F := one_le_padicValNat_of_dvd hF0 hF
  rw [s1Exp, ite_eq_left rfl, ← pow_succ']
  congr 1
  omega

/-- The `q`-part of `s₂` for a `q`-prime `q ∣ s̄₂`:
`q^(v_q(n^(q−1)−1) + v_q(t'))` if `q ∣ t'`, else `q`. -/
def s2Part (t' n q : ℕ) : ℕ :=
  if q ∣ t' then q ^ (padicValNat q (n ^ (q - 1) - 1) + padicValNat q t') else q

/-- **(5.4)**: `s₂ = ∏_{q ∣ s̄₂} s2Part q`
`= s̄₂ · ∏_{p ∣ t', p ∣ s̄₂} p^(v_p(n^(p−1)−1) + v_p(t') − 1)`. -/
def s2 (t' n s2bar : ℕ) : ℕ := ∏ q ∈ s2bar.primeFactors, s2Part t' n q

/-! ### Lifting the exponent -/

/-- `a ≡ 1 (mod p^m)` with `m ≥ 1` ⟹ `a^p ≡ 1 (mod p^(m+1))`: since
`a^p − 1 = (Σ_{i<p} a^i)(a − 1)` and the geometric sum is `≡ p ≡ 0
(mod p)`. -/
theorem pow_prime_modEq_one_lift {p a m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (ha : a ≡ 1 [MOD p ^ m]) : a ^ p ≡ 1 [MOD p ^ (m + 1)] := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((p : ℤ) ^ m) ∣ (a : ℤ) - 1 := by
    have := Nat.modEq_iff_dvd.mp ha
    push_cast at this
    exact dvd_sub_comm.mp this
  have hap : ((a : ℕ) : ZMod p) = 1 := by
    have ha1 : a ≡ 1 [MOD p] := Nat.ModEq.of_dvd (dvd_pow_self p hm.ne') ha
    have := (ZMod.natCast_eq_natCast_iff a 1 p).mpr ha1
    simpa using this
  have h2 : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (a : ℤ) ^ i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hap]
    simp
  have h3 : ((p : ℤ) ^ (m + 1)) ∣ (a : ℤ) ^ p - 1 := by
    rw [← geom_sum_mul, pow_succ']
    exact mul_dvd_mul h2 h1
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp h3

/-- **Lifting the exponent**: `a ≡ 1 (mod p^m)` with `m ≥ 1` ⟹
`a^(p^k) ≡ 1 (mod p^(m+k))`. -/
theorem pow_prime_pow_modEq_one_lift {p a m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (ha : a ≡ 1 [MOD p ^ m]) (k : ℕ) : a ^ p ^ k ≡ 1 [MOD p ^ (m + k)] := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have := pow_prime_modEq_one_lift hp (by omega : 0 < m + k) ih
    rwa [← pow_mul, ← pow_succ, show m + k + 1 = m + (k + 1) by omega] at this

/-! ### `n^(t') ≡ 1` modulo `s₁`, `s₂`, `s₁·s₂` -/

/-- **`n^(t') ≡ 1 (mod s₁)`** for even `t'` and `F ∣ n² − 1`: the
exponents of (5.2) are exactly what lifting-the-exponent from
`n² ≡ 1 (mod p^(v_p(F)))` along `p^(v_p(t'))` supports (with the `−1`
at `p = 2`, where only `2^(v_2(t')) ∣ t'` is available). -/
theorem pow_modEq_one_s1 {n t' F : ℕ} (hn : 1 ≤ n) (ht2 : 2 ∣ t')
    (ht0 : t' ≠ 0) (hF0 : F ≠ 0) (hF : F ∣ n ^ 2 - 1) :
    n ^ t' ≡ 1 [MOD s1 t' F] := by
  rw [s1]
  refine modEq_prod_of_pairwise_coprime ?_ ?_
  · intro p hp q hq hne
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp))
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq))).mpr hne)
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have hpF : p ∣ F := Nat.dvd_of_mem_primeFactors hp
    rw [s1Exp]
    set v := padicValNat p F with hv
    set k := padicValNat p t' with hk
    have hv1 : 1 ≤ v := one_le_padicValNat_of_dvd hF0 hpF
    have hpv : p ^ v ∣ n ^ 2 - 1 := pow_padicValNat_dvd.trans hF
    have hsq : n ^ 2 ≡ 1 [MOD p ^ v] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hn)).mpr hpv).symm
    have hpk : p ^ k ∣ t' := pow_padicValNat_dvd
    by_cases h2 : p = 2
    · subst h2
      rw [ite_eq_left rfl]
      have hk1 : 1 ≤ k := one_le_padicValNat_of_dvd ht0 ht2
      have hlift := pow_prime_pow_modEq_one_lift Nat.prime_two hv1 hsq (k - 1)
      have h2k : 2 ^ (k - 1) * 2 = 2 ^ k := by
        rw [← pow_succ]
        congr 1
        omega
      obtain ⟨c, hc⟩ := hpk
      have hpow : n ^ t' = ((n ^ 2) ^ 2 ^ (k - 1)) ^ c := by
        rw [← pow_mul, ← pow_mul, hc, ← h2k]
        congr 1
        ring
      rw [hpow, show k + v - 1 = v + (k - 1) by omega]
      exact (hlift.pow c).trans (by rw [one_pow])
    · rw [ite_eq_right h2, Nat.sub_zero]
      have hlift := pow_prime_pow_modEq_one_lift hpp hv1 hsq k
      have hcop : Nat.Coprime 2 (p ^ k) :=
        Nat.Coprime.pow_right _
          ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm h2))
      obtain ⟨c, hc⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ht2 hpk
      have hpow : n ^ t' = ((n ^ 2) ^ p ^ k) ^ c := by
        rw [← pow_mul, ← pow_mul, hc, mul_assoc]
      rw [hpow, show k + v = v + k by omega]
      exact (hlift.pow c).trans (by rw [one_pow])

/-- **`n^(t') ≡ 1 (mod s₂)`** for `q`-primes `q ∣ s̄₂` (`q − 1 ∣ t'`,
`q ∤ n`): Fermat lifts along `q^(v_q(t'))`, and `(q−1)·q^(v_q(t')) ∣ t'`. -/
theorem pow_modEq_one_s2 {n t' s2bar : ℕ} (hn : 1 < n)
    (hq : ∀ q ∈ s2bar.primeFactors, (q - 1) ∣ t' ∧ ¬ q ∣ n) :
    n ^ t' ≡ 1 [MOD s2 t' n s2bar] := by
  rw [s2]
  have hpart : ∀ r, ∃ e, s2Part t' n r = r ^ e := fun r => by
    unfold s2Part
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨1, (pow_one r).symm⟩
  refine modEq_prod_of_pairwise_coprime ?_ ?_
  · intro p hp q hq' hne
    obtain ⟨e₁, h₁⟩ := hpart p
    obtain ⟨e₂, h₂⟩ := hpart q
    show Nat.Coprime (s2Part t' n p) (s2Part t' n q)
    rw [h₁, h₂]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp))
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq'))).mpr hne)
  · intro q hqmem
    have hqp := Nat.prime_of_mem_primeFactors hqmem
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨hq1, hqn⟩ := hq q hqmem
    have hferm : n ^ (q - 1) ≡ 1 [MOD q] :=
      Nat.ModEq.pow_card_sub_one_eq_one hqp
        ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqn).symm
    have hq2 := hqp.two_le
    unfold s2Part
    split_ifs with hqt
    · set v := padicValNat q (n ^ (q - 1) - 1) with hv
      set k := padicValNat q t' with hk
      have hN1 : 1 ≤ n ^ (q - 1) := Nat.one_le_pow _ _ (by omega)
      have hN0 : n ^ (q - 1) - 1 ≠ 0 := by
        have : 1 < n ^ (q - 1) := Nat.one_lt_pow (by omega) hn
        omega
      have hqN : q ∣ n ^ (q - 1) - 1 := (Nat.modEq_iff_dvd' hN1).mp hferm.symm
      have hv1 : 1 ≤ v := one_le_padicValNat_of_dvd hN0 hqN
      have hqv : n ^ (q - 1) ≡ 1 [MOD q ^ v] :=
        ((Nat.modEq_iff_dvd' hN1).mpr pow_padicValNat_dvd).symm
      have hlift := pow_prime_pow_modEq_one_lift hqp hv1 hqv k
      have hcop : Nat.Coprime (q - 1) (q ^ k) := by
        refine Nat.Coprime.pow_right _ ?_
        have hq' : q = 1 + (q - 1) := by omega
        conv_rhs => rw [hq']
        exact Nat.coprime_add_self_right.mpr (Nat.coprime_one_right _)
      obtain ⟨c, hc⟩ :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hq1 pow_padicValNat_dvd
      have hpow : n ^ t' = ((n ^ (q - 1)) ^ q ^ k) ^ c := by
        rw [← pow_mul, ← pow_mul, hc, mul_assoc]
      rw [hpow]
      exact (hlift.pow c).trans (by rw [one_pow])
    · obtain ⟨c, hc⟩ := hq1
      have hpow : n ^ t' = (n ^ (q - 1)) ^ c := by rw [← pow_mul, hc]
      rw [hpow]
      exact (hferm.pow c).trans (by rw [one_pow])

/-- A prime dividing `s₁` divides `F`. -/
theorem prime_dvd_F_of_dvd_s1 {t' F k : ℕ} (hk : k.Prime) (hk1 : k ∣ s1 t' F) :
    k ∣ F := by
  rw [s1] at hk1
  obtain ⟨p, hp, hkp⟩ := (Prime.dvd_finsetProd_iff hk.prime _).mp hk1
  have hkp' := hk.dvd_of_dvd_pow hkp
  rw [(Nat.prime_dvd_prime_iff_eq hk (Nat.prime_of_mem_primeFactors hp)).mp hkp']
  exact Nat.dvd_of_mem_primeFactors hp

/-- A prime dividing `s₂` divides `s̄₂`. -/
theorem prime_dvd_s2bar_of_dvd_s2 {t' n s2bar k : ℕ} (hk : k.Prime)
    (hk2 : k ∣ s2 t' n s2bar) : k ∣ s2bar := by
  rw [s2] at hk2
  obtain ⟨q, hq', hkq⟩ := (Prime.dvd_finsetProd_iff hk.prime _).mp hk2
  have hkq' : k ∣ q := by
    unfold s2Part at hkq
    split_ifs at hkq
    · exact hk.dvd_of_dvd_pow hkq
    · exact hkq
  rw [(Nat.prime_dvd_prime_iff_eq hk (Nat.prime_of_mem_primeFactors hq')).mp hkq']
  exact Nat.dvd_of_mem_primeFactors hq'

/-- `s₁` and `s₂` are coprime when the `q`-primes of `s̄₂` do not
divide `F`. -/
theorem coprime_s1_s2 {t' n F s2bar : ℕ}
    (hq : ∀ q ∈ s2bar.primeFactors, ¬ q ∣ F) :
    Nat.Coprime (s1 t' F) (s2 t' n s2bar) := by
  apply Nat.coprime_of_dvd
  intro k hk hk1 hk2
  have hkF : k ∣ F := prime_dvd_F_of_dvd_s1 hk hk1
  have hks : k ∣ s2bar := prime_dvd_s2bar_of_dvd_s2 hk hk2
  have hs0 : s2bar ≠ 0 := by
    rintro rfl
    simp [s2] at hk2
    exact hk.one_lt.ne' hk2
  exact hq k (Nat.mem_primeFactors.mpr ⟨hk, hks, hs0⟩) hkF

/-- **`n^(t') ≡ 1 (mod s₁·s₂)`** — the well-definedness of "`l(r)`
modulo `t'`" for the combined modulus of (5.3)/(5.4), and the input
of the exponent reduction in the final trial division. -/
theorem pow_modEq_one_s1_mul_s2 {n t' F s2bar : ℕ} (hn : 1 < n)
    (ht2 : 2 ∣ t') (ht0 : t' ≠ 0) (hF0 : F ≠ 0) (hF : F ∣ n ^ 2 - 1)
    (hq : ∀ q ∈ s2bar.primeFactors, (q - 1) ∣ t' ∧ ¬ q ∣ n ∧ ¬ q ∣ F) :
    n ^ t' ≡ 1 [MOD s1 t' F * s2 t' n s2bar] :=
  (Nat.modEq_and_modEq_iff_modEq_mul
    (coprime_s1_s2 fun q hq' => (hq q hq').2.2)).mp
    ⟨pow_modEq_one_s1 (by omega) ht2 ht0 hF0 hF,
     pow_modEq_one_s2 hn fun q hq' => ⟨(hq q hq').1, (hq q hq').2.1⟩⟩

/-! ### (5.5) Selection of `t` and `s` (spec level) -/

/-- The initial `s̄₂` of (5.2): the `q`-primes with `q − 1 ∣ t'` and
`q ∤ s₁`, as a list of distinct primes. -/
def s2barInit (t' s₁ : ℕ) (qprimes : List ℕ) : List ℕ :=
  qprimes.filter fun q => decide ((q - 1) ∣ t' ∧ ¬ q ∣ s₁)

/-- `s₂` from the list `s̄₂` of `q`-primes. -/
def s2OfList (t' n : ℕ) (qs : List ℕ) : ℕ := (qs.map (s2Part t' n)).prod

/-- The guard `s₁·s₂ > n^(1/2)`, i.e. `n < (s₁·s₂)²`. -/
def bigEnough (n s₁ s₂ : ℕ) : Bool := decide (n < (s₁ * s₂) ^ 2)

/-- One greedy step of (5.2): among the `q ∣ s̄₂` whose removal keeps
`s₁·s₂ > n^(1/2)`, the one with `w(q)/log(q^(v_q(s₂)))` largest
(logarithms approximated by `Nat.log 2`); `none` if no `q` is
removable. -/
def pruneStep (c : ℕ → ℕ → ℕ) (n s₁ t' : ℕ) (qs : List ℕ) : Option ℕ :=
  let s₂ := s2OfList t' n qs
  let cands := qs.filter fun q => bigEnough n s₁ (s₂ / s2Part t' n q)
  cands.foldl (fun best q =>
    match best with
    | none => some q
    | some q' =>
      if qCost c q * Nat.log 2 (s2Part t' n q')
          > qCost c q' * Nat.log 2 (s2Part t' n q)
      then some q else some q') none

/-- The greedy pruning loop of (5.2) (fuel = the list length). -/
def prune (c : ℕ → ℕ → ℕ) (n s₁ t' : ℕ) : List ℕ → ℕ → List ℕ
  | qs, 0 => qs
  | qs, fuel + 1 =>
    match pruneStep c n s₁ t' qs with
    | none => qs
    | some q => prune c n s₁ t' (qs.erase q) fuel

/-- **Procedure (5.2)** for one even divisor `t'`: returns
`(s₁, s̄₂)`, with `s̄₂ = []` if `s₁` alone suffices, or `none` if `t'`
is too small (fails). -/
def procedure_5_2 (c : ℕ → ℕ → ℕ) (n F t' : ℕ) (qprimes : List ℕ) :
    Option (ℕ × List ℕ) :=
  let s₁ := s1 t' F
  if n < s₁ ^ 2 then some (s₁, [])
  else
    let qs := s2barInit t' s₁ qprimes
    if bigEnough n s₁ (s2OfList t' n qs)
    then some (s₁, prune c n s₁ t' qs qs.length) else none

/-- The total cost `c(t') = t'·c_ftd + Σ_{q ∣ s̄₂} w(q)`. -/
def totalCost (c : ℕ → ℕ → ℕ) (cftd t' : ℕ) (qs : List ℕ) : ℕ :=
  t' * cftd + (qs.map (qCost c)).sum

/-- **(5.5) Selection of `t` and `s`**: over the even divisors `t'` of
`t`, apply (5.2) and keep the `t'` of least total cost; returns
`(t', s₁, s̄₂)`, with `s = s₁ · s2OfList t' n s̄₂`. -/
def selection_5_5 (c : ℕ → ℕ → ℕ) (cftd n F t : ℕ) (qprimes : List ℕ) :
    Option (ℕ × ℕ × List ℕ) :=
  let divs := (List.range (t + 1)).filter fun d => decide (d ≠ 0 ∧ d ∣ t ∧ 2 ∣ d)
  divs.foldl (fun best t' =>
    match procedure_5_2 c n F t' qprimes with
    | none => best
    | some (s₁, qs) =>
      match best with
      | none => some (t', s₁, qs)
      | some (t₀, s₀, qs₀) =>
        if totalCost c cftd t' qs < totalCost c cftd t₀ qs₀
        then some (t', s₁, qs) else some (t₀, s₀, qs₀)) none

/-! Sanity guards (interpreter): `n = 1000003`, `B = 11` (so `F = 24`,
the `11`-smooth part of `n² − 1 = 2³·3·…`), `t = 60` with its `q`-primes
`{2, 3, 5, 7, 11, 13, 31, 61}`, `c_{p^k} = p^k`, `c_ftd = 1`: the
selection picks `t' = 12`, `s₁ = 2^(2+3−1)·3^(1+1) = 144`, `s̄₂ = {13}`,
so `s = 144·13 = 1872 > n^(1/2) ≈ 1000`; for `t' = 60` alone the greedy
pruning leaves `s̄₂ = {5}`.  For `n = 10007` (`F = 144`, `t = 12`) the
`n ∓ 1` side suffices: `t' = 2`, `s₁ = 144 > 10007^(1/2)`. -/

#guard s1 12 24 = 144
#guard selection_5_5 (fun p k => p ^ k) 1 1000003 24 60 [2, 3, 5, 7, 11, 13, 31, 61]
  = some (12, 144, [13])
#guard procedure_5_2 (fun p k => p ^ k) 1000003 24 60 [2, 3, 5, 7, 11, 13, 31, 61]
  = some (144, [5])
#guard 1000003 < (144 * s2OfList 12 1000003 [13]) ^ 2
#guard selection_5_5 (fun p k => p ^ k) 1 10007 144 12 [2, 3, 5, 7, 13]
  = some (2, 144, [])

end CL

end Azurite
