/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Soundness of the APR-CL test** (`Azurite/APRCL/Test.lean`):
  `aprclCheck n cert = some true` implies `n` prime and `= some false` implies
  `n` composite.

  The primality half assembles the generalized Theorem (6.3) `theorem_6_3_LL`
  at `s₁ = F` (Lucas–Lehmer), `s₂ = ∏ q^e` (Jacobi sums), `t'`, with the
  character family `Yfam` (the common-ring characters transported into `ℂ`):
  the Lucas–Lehmer clauses as in `prime_of_ll`, the odd-`p` clauses from
  `clause_odd` (chains `chiR_eq_of_odd` + a (6.4) source), the `p = 2` clause
  from `clause_two` (chains `chiR_eq_of_k1/k2/k3` + the (c1)/(c2) two-adic
  source and parity); then the final trial division `step5_prime`.
-/
import Azurite.APRCL.Test
import Azurite.APRCL.Select
import Azurite.AzNat.Equiv.RootInt
import Azurite.APRCL.Equiv.LucasLehmer
import Azurite.APRCL.Equiv.Complete
import Azurite.APRCL.Equiv.JacobiAlign
import Azurite.CohenLenstra.Proposition_7_18

namespace Azurite

namespace APRCL

open AzZMod CL CP Polynomial

/-! ### Decoding the computable checks -/

section Decode

variable {n : AzNat}

theorem natCast_mod_azNat (m : ℕ) :
    (((n % AzNat.ofNat m).toNat : ℕ) : ZMod m) = (n.toNat : ZMod m) := by
  rw [AzNat.toNat_mod, AzNat.toNat_ofNat, ZMod.natCast_mod]

theorem powModEqOne_eq_true {t' m : ℕ} (h : powModEqOne n t' m = true) :
    n.toNat ^ t' ≡ 1 [MOD m] := by
  unfold powModEqOne at h
  rw [decide_eq_true_eq, natCast_mod_azNat] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast; exact h)

theorem notOneModSq_eq_true {p : ℕ} (h : notOneModSq n p = true) :
    ¬ n.toNat ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  unfold notOneModSq at h
  rw [decide_eq_true_eq, natCast_mod_azNat] at h
  intro hc
  apply h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
  push_cast at this
  exact this

theorem wieferichFree_eq_true {p : ℕ} (h : wieferichFree p = true) : ¬ 2 ^ p ≡ 2 [MOD p ^ 2] := by
  unfold wieferichFree at h
  rw [decide_eq_true_eq] at h
  intro hc
  apply h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
  push_cast at this
  exact this

theorem not_dvd_of_mod_ne_zero {m : ℕ} (h : ¬ n % AzNat.ofNat m = 0) : ¬ m ∣ n.toNat := fun hd =>
  h (AzNat.toNat_injective (by rw [AzNat.toNat_mod, AzNat.toNat_ofNat, Nat.mod_eq_zero_of_dvd hd]; rfl))

theorem lt_of_ofNat_lt {m : ℕ} (h : AzNat.ofNat m < n) : m < n.toNat := by
  rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat] at h
  exact h

theorem s2Of_eq (qs : List QCert) : s2Of qs = prodPow (qs.map fun d => (d.q, d.e)) := by
  simp [s2Of, prodPow, List.map_map, Function.comp_def]

variable [Fact (1 < n.toNat)]

/-- **The per-`q` check decoded.** -/
theorem qCheck_pass {F : AzNat} {t' : ℕ} {d : QCert} {hs : List (ℕ × ℕ)}
    (h : qCheck n F t' d = .pass hs) :
    d.q.Prime ∧ (d.q - 1) ∣ t' ∧ 1 ≤ d.e ∧ (2 ≤ d.e → d.q ∣ t') ∧
      n.toNat ^ t' ≡ 1 [MOD d.q ^ d.e] ∧ ¬ d.q ∣ n.toNat ∧ ¬ d.q ∣ F.toNat ∧
      CL.checkGenerator d.q d.g = true ∧
      CL.checkIndexTable d.q d.g (CL.indexTableOf (CL.indexTableArr d.q d.g)) = true ∧
      (∀ ph ∈ hs, ph.1 ∈ (d.q - 1).primeFactors ∧
        jTest n ph.1 (padicValNat ph.1 (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g)) = some ph.2) ∧
      (∀ p ∈ (d.q - 1).primeFactors, ∃ h, (p, h) ∈ hs) := by
  unfold qCheck at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain rfl := Outcome.pass.inj h
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
    not_or, Bool.not_eq_false] at h1 h5 h6
  obtain ⟨⟨⟨⟨hq, hqt⟩, he⟩, he2⟩, hpow⟩ := h1
  have hq' := isPrimeNat_eq_true_iff.mp hq
  have hq1 : d.q - 1 ≠ 0 := by have := hq'.two_le; omega
  refine ⟨hq', hqt, he, he2, powModEqOne_eq_true hpow, not_dvd_of_mod_ne_zero h2,
    not_dvd_of_mod_ne_zero h4, h5, h6, ?_, ?_⟩
  · intro ph hph
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hph
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hsome := List.all_eq_true.mp h9 _ hx
    simp only at hsome
    refine ⟨(Nat.mem_primeFactors_iff_mem_primeFactorsList).mpr hp, ?_⟩
    obtain ⟨hv, hhv⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hhv, Option.getD_some]
  · intro p hp
    refine ⟨(jTest n p (padicValNat p (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g))).getD 0, ?_⟩
    exact List.mem_map_of_mem (List.mem_map_of_mem
      ((Nat.mem_primeFactors_iff_mem_primeFactorsList).mp hp))

/-- **The per-`q` `composite` verdict is sound.** -/
theorem qCheck_composite {F : AzNat} {t' : ℕ} {d : QCert} (h : qCheck n F t' d = .composite) :
    ¬ n.toNat.Prime := by
  intro hN
  unfold qCheck at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · -- `q ∣ n`, `q < n`
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
      not_or, Bool.not_eq_false] at h1
    have hq := isPrimeNat_eq_true_iff.mp h1.1.1.1.1
    have hd : d.q ∣ n.toNat := dvd_of_mod_ofNat_eq_zero h2
    have hlt := lt_of_ofNat_lt h3
    rcases hN.eq_one_or_self_of_dvd _ hd with h | h
    · exact hq.one_lt.ne' h
    · omega
  · -- some `p ∣ q − 1` with `p ∣ n`, `p < n`
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h8
    obtain ⟨p, hp, hpd, hlt⟩ := h8
    have hp' := Nat.prime_of_mem_primeFactorsList hp
    have hd : p ∣ n.toNat := dvd_of_mod_ofNat_eq_zero hpd
    have hlt' := lt_of_ofNat_lt hlt
    rcases hN.eq_one_or_self_of_dvd _ hd with h | h
    · exact hp'.one_lt.ne' h
    · omega
  · -- a Jacobi test found no `h`: impossible for prime `n` (`jTest_isSome_of_checks`)
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
      not_or, Bool.not_eq_false] at h1 h5 h6
    have hq := isPrimeNat_eq_true_iff.mp h1.1.1.1.1
    simp only [Bool.not_eq_true, List.any_eq_false, decide_eq_true_eq] at h7
    simp only [Bool.not_eq_true, List.all_eq_false, List.mem_map] at h9
    obtain ⟨ph, ⟨p, hp, rfl⟩, hnone⟩ := h9
    have hsome := jTest_isSome_of_checks hq (Nat.prime_of_mem_primeFactorsList hp)
      (Nat.dvd_of_mem_primeFactorsList hp) h5 h6 hN (not_dvd_of_mod_ne_zero h2)
      (not_dvd_of_mod_ne_zero (h7 p hp))
    simp only at hnone
    rw [hsome] at hnone
    exact Bool.noConfusion hnone

/-- **The `q`-stage `pass` decoded.** -/
theorem qStage_pass {F : AzNat} {t' : ℕ} :
    ∀ {qs : List QCert} {res : List (ℕ × List (ℕ × ℕ))}, qStage n F t' qs = .pass res →
      (∀ d ∈ qs, ∃ hs, qCheck n F t' d = .pass hs ∧ (d.q, hs) ∈ res) ∧
      (∀ qh ∈ res, ∃ d ∈ qs, d.q = qh.1 ∧ qCheck n F t' d = .pass qh.2)
  | [], res, h => by
    simp only [qStage] at h
    obtain rfl := Outcome.pass.inj h
    exact ⟨fun d hd => absurd hd (List.not_mem_nil), fun qh hqh => absurd hqh (List.not_mem_nil)⟩
  | d :: ds, res, h => by
    simp only [qStage] at h
    split at h <;> try cases h
    rename_i hs hd
    split at h <;> try cases h
    rename_i rest hrest
    obtain ⟨ih1, ih2⟩ := qStage_pass hrest
    refine ⟨fun d' hd' => ?_, fun qh hqh => ?_⟩
    · rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨hs, hd, List.mem_cons_self ..⟩
      · obtain ⟨hs', h1, h2⟩ := ih1 d' hd'
        exact ⟨hs', h1, List.mem_cons_of_mem _ h2⟩
    · rcases List.mem_cons.mp hqh with rfl | hqh
      · exact ⟨d, List.mem_cons_self .., rfl, hd⟩
      · obtain ⟨d', h1, h2, h3⟩ := ih2 qh hqh
        exact ⟨d', List.mem_cons_of_mem _ h1, h2, h3⟩

/-- **The `q`-stage `composite` decoded.** -/
theorem qStage_composite {F : AzNat} {t' : ℕ} :
    ∀ {qs : List QCert}, qStage n F t' qs = .composite → ∃ d ∈ qs, qCheck n F t' d = .composite
  | [], h => by simp [qStage] at h
  | d :: ds, h => by
    simp only [qStage] at h
    split at h <;> try cases h
    · rename_i hd
      exact ⟨d, List.mem_cons_self .., hd⟩
    · rename_i hs hd
      split at h <;> try cases h
      rename_i hrest
      obtain ⟨d', h1, h2⟩ := qStage_composite hrest
      exact ⟨d', List.mem_cons_of_mem _ h1, h2⟩

/-- **The additional test (k) decoded.** -/
theorem auxOK_eq_true {p q' g' : ℕ} (h : auxOK n p q' g' = true) :
    q'.Prime ∧ p ∣ q' - 1 ∧ ¬ q' ∣ n.toNat ∧ CL.checkGenerator q' g' = true ∧
      CL.checkIndexTable q' g' (CL.indexTableOf (CL.indexTableArr q' g')) = true ∧
      ∃ h, jOdd n p 1 q' (CL.indexTableOf (CL.indexTableArr q' g')) = some h ∧ ¬ p ∣ h := by
  unfold auxOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hq, hpq⟩, hqn⟩, hchk⟩, hidx, hj⟩ := h
  refine ⟨isPrimeNat_eq_true_iff.mp hq, hpq, not_dvd_of_mod_ne_zero (by simpa using hqn), hchk,
    hidx, ?_⟩
  split at hj
  · rename_i h hh
    exact ⟨h, hh, decide_eq_true_eq.mp hj⟩
  · cases hj

/-- **The (6.4)-source check decoded.** -/
theorem sixFourOK_eq_true {llPrimes : List ℕ} {hs : List (ℕ × List (ℕ × ℕ))}
    {aux : List (ℕ × ℕ × ℕ)} {p : ℕ} (h : sixFourOK n llPrimes hs aux p = true) :
    p ∈ llPrimes ∨ ¬ n.toNat ^ (p - 1) ≡ 1 [MOD p ^ 2] ∨
      (∃ qh ∈ hs, p ∣ qh.1 - 1 ∧ ∃ ph ∈ qh.2, ph.1 = p ∧ ¬ p ∣ ph.2) ∨
      ∃ a ∈ aux, a.1 = p ∧ auxOK n p a.2.1 a.2.2 = true := by
  unfold sixFourOK at h
  simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with ((h | h) | ⟨qh, hqh, hpq, ph, hph, hp1, hp2⟩) | ⟨a, ha, hap, hok⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (notOneModSq_eq_true h))
  · exact Or.inr (Or.inr (Or.inl ⟨qh, hqh, hpq, ph, hph, hp1, hp2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, hap, hok⟩))

/-- **The odd-prime check `pass` decoded.** -/
theorem pCheck_pass {llPrimes : List ℕ} {hs : List (ℕ × List (ℕ × ℕ))} {aux : List (ℕ × ℕ × ℕ)}
    {p : ℕ} (hp2 : p ≠ 2) (h : pCheck n llPrimes hs aux p = .pass ()) :
    ¬ p ∣ n.toNat ∧ ¬ 2 ^ p ≡ 2 [MOD p ^ 2] ∧ sixFourOK n llPrimes hs aux p = true := by
  unfold pCheck at h
  rw [ite_eq_right hp2] at h
  split_ifs at h with h1 h2 h3 h4
  rw [Bool.and_eq_true] at h3
  exact ⟨not_dvd_of_mod_ne_zero h1, wieferichFree_eq_true h3.1, h3.2⟩

/-- **The odd-prime check `composite` decoded**: a prime `p ∣ t'` divides `n` properly, or
`n` is a `p`-th power. -/
theorem pCheck_composite (hn1 : 1 < n.toNat) {llPrimes : List ℕ} {hs : List (ℕ × List (ℕ × ℕ))}
    {aux : List (ℕ × ℕ × ℕ)} {p : ℕ} (hp : p.Prime)
    (h : pCheck n llPrimes hs aux p = .composite) : ¬ n.toNat.Prime := by
  unfold pCheck at h
  split_ifs at h with h0 h1 h2 h3 h4
  · have hd : p ∣ n.toNat := dvd_of_mod_ofNat_eq_zero h1
    have hlt := lt_of_ofNat_lt h2
    intro hN
    rcases hN.eq_one_or_self_of_dvd _ hd with h | h
    · exact hp.one_lt.ne' h
    · omega
  · obtain ⟨y, hy⟩ := (AzNat.isPow_eq_true_iff n p hp.one_lt.le).mp h4
    exact CL.not_prime_of_eq_pow hn1 hp.two_le hy.symm

omit [Fact (1 < n.toNat)] in
/-- **The final trial division, `some true`**: the loop found `n^i ≡ 1 (mod s)` with no
proper-divisor hit before. -/
theorem finalDiv_true {s : AzNat} (hN : 0 < n.toNat) (hs1 : 1 < s.toNat) :
    ∀ {fuel : ℕ} {r : AzNat} {i₀ : ℕ}, r.toNat = n.toNat ^ i₀ % s.toNat →
      (∀ j, 1 ≤ j → j ≤ i₀ →
        ¬ (n.toNat ^ j % s.toNat ∣ n.toNat ∧ n.toNat ^ j % s.toNat < n.toNat)) →
      finalDiv n s fuel r = some true →
      ∃ i, i₀ < i ∧ n.toNat ^ i % s.toNat = 1 ∧ ∀ j, 1 ≤ j → j < i →
        ¬ (n.toNat ^ j % s.toNat ∣ n.toNat ∧ n.toNat ^ j % s.toNat < n.toNat)
  | 0, r, i₀, _, _, h => by simp [finalDiv] at h
  | fuel + 1, r, i₀, hr, hloop, h => by
    simp only [finalDiv] at h
    have hr' : ((r * (n % s)) % s).toNat = n.toNat ^ (i₀ + 1) % s.toNat := by
      rw [AzNat.toNat_mod, AzNat.toNat_mul, hr, AzNat.toNat_mod, pow_succ]
      exact (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
    split_ifs at h with h1 h2
    · refine ⟨i₀ + 1, by omega, ?_, fun j hj hj' => hloop j hj (by omega)⟩
      have := congrArg AzNat.toNat h1
      rwa [hr'] at this
    · cases h
    · obtain ⟨i, hi, hi1, hi2⟩ := finalDiv_true hN hs1 (i₀ := i₀ + 1) hr' (fun j hj hj' => by
        rcases Nat.lt_or_ge j (i₀ + 1) with hlt | hge
        · exact hloop j hj (by omega)
        · obtain rfl : j = i₀ + 1 := by omega
          rintro ⟨hd, hlt⟩
          apply h2
          refine ⟨?_, ?_, ?_⟩
          · intro h0
            have := congrArg AzNat.toNat h0
            rw [hr'] at this
            rw [this] at hd
            exact hN.ne' (Nat.eq_zero_of_zero_dvd hd)
          · apply AzNat.toNat_injective
            rw [AzNat.toNat_mod, hr']
            exact Nat.mod_eq_zero_of_dvd hd
          · rw [AzNat.lt_iff_toNat_lt, hr']
            exact hlt) h
      exact ⟨i, by omega, hi1, hi2⟩

omit [Fact (1 < n.toNat)] in
/-- **The final trial division, `some false`**: a proper divisor was found. -/
theorem finalDiv_false {s : AzNat} :
    ∀ {fuel : ℕ} {r : AzNat}, finalDiv n s fuel r = some false →
      ∃ d, d ∣ n.toNat ∧ 1 < d ∧ d < n.toNat
  | 0, r, h => by simp [finalDiv] at h
  | fuel + 1, r, h => by
    simp only [finalDiv] at h
    split_ifs at h with h1 h2
    · cases h
    · obtain ⟨h0, hd, hlt⟩ := h2
      refine ⟨((r * (n % s)) % s).toNat, dvd_of_mod_ofNat_eq_zero (by rwa [AzNat.ofNat_toNat]), ?_,
        (AzNat.lt_iff_toNat_lt _ _).mp hlt⟩
      rcases Nat.lt_or_ge 1 ((r * (n % s)) % s).toNat with h | h
      · exact h
      · exfalso
        interval_cases hx : ((r * (n % s)) % s).toNat
        · exact h0 (AzNat.toNat_injective hx)
        · exact h1 (AzNat.toNat_injective hx)
    · exact finalDiv_false h

end Decode

/-! ### The assembled primality argument -/

/-- The lifting step of (5.2): `n² ≡ 1 (mod p^e)` gives `n^(2·p^v·w) ≡ 1 (mod p^(e+v))`. -/
theorem pow_modEq_one_of_sq {N p e v w : ℕ} (hp : p.Prime) (he : 0 < e)
    (h : N ^ 2 ≡ 1 [MOD p ^ e]) : N ^ (2 * p ^ v * w) ≡ 1 [MOD p ^ (e + v)] := by
  have h' := (CL.pow_prime_pow_modEq_one_lift hp he h v).pow w
  rw [one_pow] at h'
  calc N ^ (2 * p ^ v * w) = ((N ^ 2) ^ p ^ v) ^ w := by rw [← pow_mul, ← pow_mul, mul_assoc]
    _ ≡ 1 [MOD p ^ (e + v)] := h'

theorem toNat_liftedS1 (cert : LLCert) (t' : ℕ) :
    (liftedS1 cert t').toNat = 2 ^ (cert.e2 + padicValNat 2 t' - 1)
      * prodPow ((certPairs cert).map fun pe => (pe.1, pe.2 + padicValNat pe.1 t')) := by
  simp [liftedS1, AzNat.toNat_mul, toNat_listProd, List.map_map, Function.comp_def, AzNat.toNat_ofNat,
    prodPow, certPairs, mul_assoc]

open Classical in
/-- **APR-CL proves primality**: the Lucas–Lehmer data (`F`, the confinements `h42`/`h43`
with a coherent `ε`), the `q`-primes of `s₂` with the character family `Y` and the two
aligned Jacobi clauses, the bound `n < (s₁·s₂)²` for the (5.2)-lifted `s₁`, and a successful
final trial division. -/
theorem prime_of_aprcl {N : ℕ} (hN : 2 < N) (hodd : N % 2 = 1)
    {Lm Lp : List (ℕ × ℕ)} {e2 : ℕ}
    (hnd : ((Lm ++ Lp).map Prod.fst).Nodup)
    (hm : ∀ pe ∈ Lm, pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ N - 1)
    (hp : ∀ pe ∈ Lp, pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ N + 1)
    (he2 : 1 ≤ e2) (he2d : 2 ^ e2 ∣ N ^ 2 - 1)
    (ε : ℕ → ℕ) (hε : ∀ r, ε r < 2)
    (h42 : ∀ pe ∈ Lm, ∀ r, r.Prime → r ∣ N → r ≡ 1 [MOD pe.1 ^ pe.2])
    (h43 : ∀ pe ∈ Lp, ∀ r, r.Prime → r ∣ N → r ≡ N ^ ε r [MOD pe.1 ^ pe.2])
    {t' : ℕ} (ht0 : 0 < t') (ht2 : 2 ∣ t')
    {Qs : List (ℕ × ℕ)} (hQnd : (Qs.map Prod.fst).Nodup)
    (hQ : ∀ qe ∈ Qs, qe.1.Prime ∧ qe.1 ≠ 2 ∧ (qe.1 - 1) ∣ t' ∧ 1 ≤ qe.2 ∧
      (2 ≤ qe.2 → qe.1 ∣ t') ∧ ¬ qe.1 ∣ N ∧ N ^ t' ≡ 1 [MOD qe.1 ^ qe.2])
    {S₁ : ℕ} (hS₁ : S₁ = 2 ^ (e2 + padicValNat 2 t' - 1)
      * prodPow ((Lm ++ Lp).map fun pe => (pe.1, pe.2 + padicValNat pe.1 t')))
    (hQF : ∀ qe ∈ Qs, ¬ qe.1 ∣ S₁)
    (Y : (q : ℕ) → (p : ℕ) → MulChar (ZMod q) ℂ)
    (hY : ∀ qe ∈ Qs, ∀ p ∈ (qe.1 - 1).primeFactors,
      orderOf (Y qe.1 p) = p ^ (qe.1 - 1).factorization p)
    (hcl_odd : ∀ p ∈ t'.primeFactors, p ≠ 2 → ∀ r ∈ N.primeFactors, ∃ l,
      (∀ qe ∈ Qs, p ∣ qe.1 - 1 → Y qe.1 p r = Y qe.1 p N ^ l) ∧
      r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ (S₁ * prodPow Qs).factorization p])
    (hcl_two : ∀ r ∈ N.primeFactors, ∃ l, l % 2 = ε r ∧
      (∀ qe ∈ Qs, Y qe.1 2 r = Y qe.1 2 N ^ l) ∧
      r ≡ N ^ l [MOD 2 ^ (S₁ * prodPow Qs).factorization 2])
    (hsize : N < (S₁ * prodPow Qs) ^ 2)
    {i : ℕ} (hi1 : 1 ≤ i) (hri : N ^ i % (S₁ * prodPow Qs) = 1)
    (hloop : ∀ j, 1 ≤ j → j < i →
      ¬ (N ^ j % (S₁ * prodPow Qs) ∣ N ∧ N ^ j % (S₁ * prodPow Qs) < N)) :
    N.Prime := by
  have hN1 : 1 < N := by omega
  set L := Lm ++ Lp with hL
  set s₂ := prodPow Qs with hs₂
  set L' := L.map (fun pe => (pe.1, pe.2 + padicValNat pe.1 t')) with hL'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : 1 ≤ padicValNat 2 t' := one_le_padicValNat_of_dvd ht0.ne' ht2
  -- the Lucas–Lehmer list facts
  have hLp : ∀ pe ∈ L, pe.1.Prime := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).1
    · exact (hp pe h).1
  have hL2 : ∀ pe ∈ L, pe.1 ≠ 2 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.1
    · exact (hp pe h).2.1
  have hLe : ∀ pe ∈ L, 1 ≤ pe.2 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.2.1
    · exact (hp pe h).2.2.1
  have hLd : ∀ pe ∈ L, pe.1 ^ pe.2 ∣ N ^ 2 - 1 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.2.2.trans (sub_one_dvd_sq_sub_one hN1.le)
    · exact (hp pe h).2.2.2.trans (add_one_dvd_sq_sub_one N)
  have hLn : ∀ pe ∈ L, ¬ pe.1 ∣ N := fun pe hpe hd => by
    have hpp := hLp pe hpe
    have h1 : pe.1 ∣ pe.1 ^ pe.2 := dvd_pow_self _ (by have := hLe pe hpe; omega)
    rcases List.mem_append.mp hpe with h | h
    · have h2 : pe.1 ∣ N - 1 := h1.trans (hm pe h).2.2.2
      have h3 : pe.1 ∣ N - (N - 1) := Nat.dvd_sub hd h2
      rw [show N - (N - 1) = 1 by omega] at h3
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h3)
    · have h2 : pe.1 ∣ N + 1 := h1.trans (hp pe h).2.2.2
      have h3 : pe.1 ∣ N + 1 - N := Nat.dvd_sub h2 hd
      rw [show N + 1 - N = 1 by omega] at h3
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h3)
  -- the lifted list
  have hL'mem : ∀ pe' ∈ L', ∃ pe ∈ L, pe' = (pe.1, pe.2 + padicValNat pe.1 t') := fun pe' h => by
    obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp h
    exact ⟨pe, hpe, rfl⟩
  have hL'p : ∀ pe ∈ L', pe.1.Prime := fun pe' h => by
    obtain ⟨pe, hpe, rfl⟩ := hL'mem pe' h
    exact hLp pe hpe
  have hL'2 : ∀ pe ∈ L', pe.1 ≠ 2 := fun pe' h => by
    obtain ⟨pe, hpe, rfl⟩ := hL'mem pe' h
    exact hL2 pe hpe
  have hL'nd : (L'.map Prod.fst).Nodup := by
    rw [hL', List.map_map]
    exact hnd
  -- `S₁`
  have hP0 : 0 < prodPow L' := prodPow_pos fun pe hpe => (hL'p pe hpe).pos
  have hS0 : 0 < S₁ := by rw [hS₁]; exact Nat.mul_pos (pow_pos two_pos _) hP0
  have hS2 : 2 ∣ S₁ := by
    rw [hS₁]
    exact (dvd_pow_self 2 (by omega)).mul_right _
  have hcop2 : Nat.Coprime (2 ^ (e2 + padicValNat 2 t' - 1)) (prodPow L') :=
    Nat.Coprime.pow_left _ (coprime_prodPow Nat.prime_two fun pe hpe => ⟨hL'p pe hpe, hL'2 pe hpe⟩)
  -- `N^t' ≡ 1 (mod S₁)` by lifting
  have hpowS₁ : N ^ t' ≡ 1 [MOD S₁] := by
    have hsq : ∀ pe ∈ L, N ^ 2 ≡ 1 [MOD pe.1 ^ pe.2] := fun pe hpe =>
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr (hLd pe hpe)).symm
    have h2sq : N ^ 2 ≡ 1 [MOD 2 ^ e2] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr he2d).symm
    have hdvd : S₁ ∣ N ^ t' - 1 := by
      rw [hS₁]
      refine hcop2.mul_dvd_of_dvd_of_dvd ?_ (prodPow_dvd hL'p hL'nd fun pe' hpe' => ?_)
      · -- the `2`-part: `t' = 2 · 2^(v−1) · w`
        set v := padicValNat 2 t' with hv
        obtain ⟨w, hw⟩ : 2 ^ v ∣ t' := pow_padicValNat_dvd
        have ht'eq : t' = 2 * 2 ^ (v - 1) * w := by
          rw [hw]
          congr 1
          rw [← pow_succ', Nat.sub_add_cancel hv2]
        have := pow_modEq_one_of_sq Nat.prime_two (by omega) h2sq (v := v - 1) (w := w)
        rw [← ht'eq, show e2 + (v - 1) = e2 + v - 1 by omega] at this
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
      · obtain ⟨pe, hpe, rfl⟩ := hL'mem pe' hpe'
        have hpp := hLp pe hpe
        have hpv : pe.1 ^ padicValNat pe.1 t' ∣ t' := pow_padicValNat_dvd
        have hcop : Nat.Coprime 2 (pe.1 ^ padicValNat pe.1 t') :=
          Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hpp).mpr (hL2 pe hpe).symm)
        obtain ⟨w, hw⟩ := hcop.mul_dvd_of_dvd_of_dvd ht2 hpv
        have := pow_modEq_one_of_sq hpp (by have := hLe pe hpe; omega) (hsq pe hpe)
          (v := padicValNat pe.1 t') (w := w)
        rw [← hw] at this
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr hdvd).symm
  have hprimeS : ∀ q, q.Prime → q ∣ S₁ → q = 2 ∨ ∃ pe ∈ L, q = pe.1 := fun q hq hqF => by
    rw [hS₁] at hqF
    rcases (Nat.Prime.dvd_mul hq).mp hqF with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · obtain ⟨pe', hpe', hqe, -⟩ := prime_dvd_prodPow hL'p hq h
      obtain ⟨pe, hpe, rfl⟩ := hL'mem pe' hpe'
      exact Or.inr ⟨pe, hpe, hqe⟩
  have hnsS : N.Coprime S₁ := Nat.coprime_of_dvd fun k hk hkN hkF => by
    rcases hprimeS k hk hkF with rfl | ⟨pe, hpe, rfl⟩
    · omega
    · exact hLn pe hpe hkN
  have hfactp : ∀ pe ∈ L, S₁.factorization pe.1 = pe.2 + padicValNat pe.1 t' := fun pe hpe => by
    rw [hS₁, Nat.factorization_mul (pow_pos two_pos _).ne' hP0.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_apply, ite_eq_right (hL2 pe hpe).symm, zero_add]
    exact factorization_prodPow_of_mem hL'p hL'nd (List.mem_map_of_mem hpe :
      (pe.1, pe.2 + padicValNat pe.1 t') ∈ L')
  have hpdvd : ∀ pe ∈ L, pe.1 ∣ N ^ 2 - 1 := fun pe hpe =>
    (dvd_pow_self _ (by have := hLe pe hpe; omega)).trans (hLd pe hpe)
  -- `s₂`
  have hQp : ∀ qe ∈ Qs, qe.1.Prime := fun qe h => (hQ qe h).1
  have hs₂0 : 0 < s₂ := prodPow_pos fun qe h => (hQp qe h).pos
  have hprimes₂ : ∀ k, k.Prime → k ∣ s₂ → ∃ qe ∈ Qs, k = qe.1 := fun k hk hks => by
    obtain ⟨qe, hqe, hke, -⟩ := prime_dvd_prodPow hQp hk hks
    exact ⟨qe, hqe, hke⟩
  have hcopF : Nat.Coprime S₁ s₂ := Nat.coprime_of_dvd fun k hk hkF hks => by
    obtain ⟨qe, hqe, rfl⟩ := hprimes₂ k hk hks
    exact hQF qe hqe hkF
  have hnss₂ : N.Coprime s₂ := Nat.coprime_of_dvd fun k hk hkN hks => by
    obtain ⟨qe, hqe, rfl⟩ := hprimes₂ k hk hks
    exact (hQ qe hqe).2.2.2.2.2.1 hkN
  have hpowS : N ^ t' ≡ 1 [MOD S₁ * s₂] := by
    refine (Nat.modEq_and_modEq_iff_modEq_mul hcopF).mp ⟨hpowS₁, ?_⟩
    have hd : s₂ ∣ N ^ t' - 1 := prodPow_dvd hQp hQnd fun qe hqe =>
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp (hQ qe hqe).2.2.2.2.2.2.symm
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr hd).symm
  have hmemQs : ∀ q, q ∈ s₂.primeFactors → ∃ qe ∈ Qs, qe.1 = q := fun q hq => by
    obtain ⟨qe, hqe, rfl⟩ := hprimes₂ q (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq)
    exact ⟨qe, hqe, rfl⟩
  -- Theorem (6.3)
  have hconf : ∀ r, r ∣ N → ∃ i < t', r ≡ N ^ i [MOD S₁ * s₂] := by
    refine CL.theorem_6_3_LL hN1 hS0 hs₂0 ht0 ht2 (Nat.Coprime.mul_right hnsS hnss₂) hcopF hpowS
      ?_ ?_ ?_ Y ?_ ?_
    · intro q hq
      obtain ⟨qe, hqe, rfl⟩ := hmemQs q hq
      refine ⟨(hQ qe hqe).2.2.1, fun h2 => (hQ qe hqe).2.2.2.2.1 ?_⟩
      rwa [factorization_prodPow_of_mem hQp hQnd hqe] at h2
    · intro p hpF
      rcases hprimeS p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · exact (dvd_pow_self 2 (by omega)).trans he2d
      · exact hpdvd pe hpe
    · intro p hpF hpt
      rcases hprimeS p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · exact absurd ht2 hpt
      · rw [hfactp pe hpe, padicValNat.eq_zero_of_not_dvd hpt, add_zero]
        exact hLd pe hpe
    · intro q hq p hpq
      obtain ⟨qe, hqe, rfl⟩ := hmemQs q hq
      exact hY qe hqe p hpq
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrn : r ∣ N := Nat.dvd_of_mem_primeFactors hr
    have hrodd : r % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).of_dvd_nat hrn)
    have hoddp : ∀ pe ∈ L, r ≡ N ^ ε r [MOD pe.1 ^ pe.2] := fun pe hpe => by
      rcases List.mem_append.mp hpe with h | h
      · have h1 : N ≡ 1 [MOD pe.1 ^ pe.2] :=
          ((Nat.modEq_iff_dvd' hN1.le).mpr (hm pe h).2.2.2).symm
        exact (h42 pe h r hrp hrn).trans ((h1.pow (ε r)).trans (by rw [one_pow])).symm
      · exact h43 pe h r hrp hrn
    refine ⟨ε r, hε r, ?_, ?_, ?_⟩
    · intro p hpF
      rcases hprimeS p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · show r % 2 = N ^ ε r % 2
        rw [hrodd, Nat.pow_mod, hodd, one_pow, Nat.one_mod_eq_one.mpr (by norm_num)]
      · exact Nat.ModEq.of_dvd (dvd_pow_self _ (by have := hLe pe hpe; omega)) (hoddp pe hpe)
    · intro p hpF hp2
      rcases hprimeS p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · exact absurd ht2 hp2
      · rw [hfactp pe hpe, padicValNat.eq_zero_of_not_dvd hp2, add_zero]
        exact hoddp pe hpe
    · intro p hpt
      by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨l, hl2, hlY, hlc⟩ := hcl_two r hr
        refine ⟨l, fun _ => hl2, fun q hq _ => ?_, ?_⟩
        · obtain ⟨qe, hqe, rfl⟩ := hmemQs q hq
          exact hlY qe hqe
        · simpa using hlc
      · obtain ⟨l, hlY, hlc⟩ := hcl_odd p hpt hp2 r hr
        refine ⟨l, fun h => absurd h hp2, fun q hq hpq => ?_, hlc⟩
        obtain ⟨qe, hqe, rfl⟩ := hmemQs q hq
        exact hlY qe hqe hpq
  exact CL.step5_prime hN1 hsize hconf hi1 hri hloop

/-! ### The character family of a certificate -/

/-- `find?` on a list with distinct `q`'s returns the member itself. -/
theorem find?_eq_some_of_nodup {qs : List QCert} (hnd : (qs.map (·.q)).Nodup) {d : QCert}
    (hd : d ∈ qs) : qs.find? (fun d' => d'.q = d.q) = some d := by
  induction qs with
  | nil => simp at hd
  | cons d' rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · have hne : d'.q ≠ d.q := fun h => hnd.1 (h ▸ List.mem_map_of_mem hd)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 hd

/-- **The character family `Y_{q,p}` of a certificate**: for the certified generator `g_q`,
the common-ring character of order `p^(v_p(q−1))` transported into `ℂ`; `1` elsewhere. -/
noncomputable def Yfam (cert : Cert) (q p : ℕ) : MulChar (ZMod q) ℂ :=
  match cert.qs.find? (fun d => d.q = q) with
  | none => 1
  | some d =>
    if h : q.Prime ∧ p.Prime ∧ CL.checkGenerator q d.g = true then
      haveI : Fact q.Prime := ⟨h.1⟩
      Yc (q := q) (k := (q - 1).factorization p) h.2.1 (Nat.ordProj_dvd _ _)
        (Classical.choose_spec (CL.checkGenerator_spec h.2.2)).2
    else 1

theorem Yfam_eq {cert : Cert} (hnd : (cert.qs.map (·.q)).Nodup) {d : QCert} (hd : d ∈ cert.qs)
    (hq : d.q.Prime) {p : ℕ} (hp : p.Prime) (hchk : CL.checkGenerator d.q d.g = true) :
    Yfam cert d.q p = @Yc d.q p ((d.q - 1).factorization p) ⟨hq⟩ _ hp (Nat.ordProj_dvd _ _)
      (Classical.choose_spec (@CL.checkGenerator_spec d.q d.g ⟨hq⟩ hchk)).2 := by
  unfold Yfam
  rw [find?_eq_some_of_nodup hnd hd]
  simp only
  rw [dite_eq_left ⟨hq, hp, hchk⟩]

/-! ### The per-`(p, q)` chains, in `ℂ` -/

section Chains

variable {n : AzNat} [Fact (1 < n.toNat)] {d : QCert} (hq : d.q.Prime)
  (hchk : CL.checkGenerator d.q d.g = true)
  (hidx : CL.checkIndexTable d.q d.g (CL.indexTableOf (CL.indexTableArr d.q d.g)) = true)

include hq hchk hidx

/-- The certified generator's index table satisfies the table hypothesis. -/
theorem indexTable_spec_gen :
    haveI : Fact d.q.Prime := ⟨hq⟩
    ∀ x ∈ Finset.Icc 1 (d.q - 2),
      ((Classical.choose (CL.checkGenerator_spec hchk) : (ZMod d.q)ˣ) : ZMod d.q)
          ^ CL.indexTableOf (CL.indexTableArr d.q d.g) x
        = 1 - ((Classical.choose (CL.checkGenerator_spec hchk) : (ZMod d.q)ˣ) : ZMod d.q) ^ x := by
  have : Fact d.q.Prime := ⟨hq⟩
  have hval := (Classical.choose_spec (CL.checkGenerator_spec hchk)).1
  rw [hval]
  exact CL.checkIndexTable_spec hidx

/-- **The odd-`p` chain in `ℂ`.** -/
theorem chain_odd_complex {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (hW : ¬ 2 ^ p ≡ 2 [MOD p ^ 2])
    (hpn : ¬ p ∣ n.toNat) (hqn : ¬ d.q ∣ n.toNat) (hpq : p ∣ d.q - 1) {h : ℕ}
    (hh : jTest n p (padicValNat p (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g)) = some h) :
    haveI : Fact d.q.Prime := ⟨hq⟩
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ n.toNat → ∀ m : ℕ,
      ((p : ℤ) ^ ((n.toNat ^ ((p - 1) * p ^ (d.q - 1).factorization p) - 1).factorization p)
        ∣ (r : ℤ) ^ (p - 1) - (n.toNat : ℤ) ^ ((p - 1) * m)) →
      Yc hp (Nat.ordProj_dvd _ _) (Classical.choose_spec (CL.checkGenerator_spec hchk)).2 r
        = embC hp (zP d.q p ((d.q - 1).factorization p)) ^ (f₀ * m) := by
  have : Fact d.q.Prime := ⟨hq⟩
  have hq1 : d.q - 1 ≠ 0 := by have := hq.two_le; omega
  have hk : 0 < (d.q - 1).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hq1 hpq
  have hn1 : 1 < n.toNat := Fact.out
  rw [jTest, ite_eq_right hp3.ne', ← Nat.factorization_def _ hp] at hh
  have h88 := jOdd_spec hp hk (Nat.ordProj_dvd _ _) (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
    (indexTable_spec_gen hq hchk hidx) hh
  obtain ⟨f₀, hf₀⟩ := chiR_eq_of_odd hp hk (Nat.ordProj_dvd _ _)
    (Classical.choose_spec (CL.checkGenerator_spec hchk)).2 hpn hp3 hW hn1 hqn h88
  exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR hp _ _ (hf₀ r hr hrn m hm)⟩

end Chains

section AuxChains

variable {n : AzNat} [Fact (1 < n.toNat)] {q g : ℕ} (hq : q.Prime)
  (hchk : CL.checkGenerator q g = true)
  (hidx : CL.checkIndexTable q g (CL.indexTableOf (CL.indexTableArr q g)) = true)

include hq hchk hidx

/-- The certified generator's index table (plain `q`, `g` form). -/
theorem indexTable_spec_gen' :
    haveI : Fact q.Prime := ⟨hq⟩
    ∀ x ∈ Finset.Icc 1 (q - 2),
      ((Classical.choose (CL.checkGenerator_spec hchk) : (ZMod q)ˣ) : ZMod q) ^ CL.indexTableOf (CL.indexTableArr q g) x
        = 1 - ((Classical.choose (CL.checkGenerator_spec hchk) : (ZMod q)ˣ) : ZMod q) ^ x := by
  have : Fact q.Prime := ⟨hq⟩
  have hval := (Classical.choose_spec (CL.checkGenerator_spec hchk)).1
  rw [hval]
  exact CL.checkIndexTable_spec hidx

/-- **A passed odd-`p` test at level `k` with `p ∤ h` is a (6.4) source** (Theorem (7.19)),
for any certified `q`, `g`, `k` — used by the additional test (k) at `k = 1`. -/
theorem sixFour_of_jOdd {p k : ℕ} (hp : p.Prime) (hp3 : 2 < p) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)
    (hpn : ¬ p ∣ n.toNat) (hqn : ¬ q ∣ n.toNat) {h : ℕ}
    (hh : jOdd n p k q (CL.indexTableOf (CL.indexTableArr q g)) = some h) (hph : ¬ p ∣ h) :
    ∀ r, r.Prime → r ∣ n.toNat → ∀ D, ∃ l,
      r ^ (p - 1) ≡ (n.toNat ^ (p - 1)) ^ l [MOD p ^ D] := by
  have : Fact q.Prime := ⟨hq⟩
  have hn1 : 1 < n.toNat := Fact.out
  have h88 := jOdd_spec hp hk hpk (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
    (indexTable_spec_gen' hq hchk hidx) hh
  exact sixFour_of_odd hp hk hpk (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
    hpn hp3 hn1 hqn hph h88

end AuxChains

section Chains

variable {n : AzNat} [Fact (1 < n.toNat)] {d : QCert} (hq : d.q.Prime)
  (hchk : CL.checkGenerator d.q d.g = true)
  (hidx : CL.checkIndexTable d.q d.g (CL.indexTableOf (CL.indexTableArr d.q d.g)) = true)

include hq hchk hidx

/-- **The (1.3)(i3) source in `ℂ`-free form**: `p ∤ h` gives (6.4) for `p`. -/
theorem sixFour_odd_of_h {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (hpn : ¬ p ∣ n.toNat)
    (hqn : ¬ d.q ∣ n.toNat) (hpq : p ∣ d.q - 1) {h : ℕ}
    (hh : jTest n p (padicValNat p (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g)) = some h) (hph : ¬ p ∣ h) :
    ∀ r, r.Prime → r ∣ n.toNat → ∀ D, ∃ l,
      r ^ (p - 1) ≡ (n.toNat ^ (p - 1)) ^ l [MOD p ^ D] := by
  have : Fact d.q.Prime := ⟨hq⟩
  have hq1 : d.q - 1 ≠ 0 := by have := hq.two_le; omega
  have hk : 0 < (d.q - 1).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hq1 hpq
  have hn1 : 1 < n.toNat := Fact.out
  rw [jTest, ite_eq_right hp3.ne', ← Nat.factorization_def _ hp] at hh
  have h88 := jOdd_spec hp hk (Nat.ordProj_dvd _ _) (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
    (indexTable_spec_gen hq hchk hidx) hh
  exact sixFour_of_odd hp hk (Nat.ordProj_dvd _ _) (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
    hpn hp3 hn1 hqn hph h88

/-- **The `p = 2` chain in `ℂ`**, by cases on `k = v₂(q − 1)`. -/
theorem chain_two_complex (hodd : n.toNat % 2 = 1) (hqn : ¬ d.q ∣ n.toNat) (hq2 : d.q ≠ 2) {h : ℕ}
    (hh : jTest n 2 (padicValNat 2 (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g)) = some h) :
    haveI : Fact d.q.Prime := ⟨hq⟩
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ n.toNat → ∀ m : ℕ,
      ((2 : ℤ) ^ ((n.toNat ^ ((2 - 1) * 2 ^ (d.q - 1).factorization 2) - 1).factorization 2)
        ∣ (r : ℤ) ^ (2 - 1) - (n.toNat : ℤ) ^ ((2 - 1) * m)) →
      Yc Nat.prime_two (Nat.ordProj_dvd _ _) (Classical.choose_spec (CL.checkGenerator_spec hchk)).2 r
        = embC Nat.prime_two (zP d.q 2 ((d.q - 1).factorization 2)) ^ (f₀ * m) := by
  have : Fact d.q.Prime := ⟨hq⟩
  have hq1 : d.q - 1 ≠ 0 := by have := hq.two_le; omega
  have h2q : 2 ∣ d.q - 1 := by
    have := hq.eq_one_or_self_of_dvd 2
    have hodd' := hq.odd_of_ne_two hq2
    obtain ⟨w, hw⟩ := hodd'
    exact ⟨w, by omega⟩
  have hk : 0 < (d.q - 1).factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hq1 h2q
  have hn1 : 1 < n.toNat := Fact.out
  rw [jTest, ite_eq_left rfl, ← Nat.factorization_def _ Nat.prime_two] at hh
  have hf := indexTable_spec_gen hq hchk hidx
  set hg := (Classical.choose_spec (CL.checkGenerator_spec hchk)).2
  set hpk : 2 ^ (d.q - 1).factorization 2 ∣ d.q - 1 := Nat.ordProj_dvd _ _
  clear_value hpk
  generalize hkdef : (d.q - 1).factorization 2 = k at *
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    · -- `k = 1`
      rw [ite_eq_left rfl] at hh
      have h92 := j2k1_spec (n := n) (q := d.q) hh
      obtain ⟨f₀, hf₀⟩ := chiR_eq_of_k1 hg hn1 hodd hqn hpk h92
      exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR Nat.prime_two _ _ (hf₀ r hr hrn m hm)⟩
    · -- `k = 2`
      rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hh
      rcases Nat.lt_or_ge (n.toNat % 4) 2 with h4 | h4
      · have hn4 : n.toNat % 4 = 1 := by omega
        have h94 := j2k2_spec_one hg hf hpk hn4 hh
        obtain ⟨f₀, hf₀⟩ := chiR_eq_of_k2_one hg hn1 hodd hqn hpk hn4 h94
        exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR Nat.prime_two _ _ (hf₀ r hr hrn m hm)⟩
      · have hn4 : n.toNat % 4 = 3 := by omega
        have h96 := j2k2_spec_three hg hf hpk hn4 hh
        obtain ⟨f₀, hf₀⟩ := chiR_eq_of_k2_three hg hn1 hodd hqn hpk hn4 h96
        exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR Nat.prime_two _ _ (hf₀ r hr hrn m hm)⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hh
    rcases Nat.lt_or_ge (n.toNat % 8) 4 with h8 | h8
    · have hn8 : n.toNat % 8 = 1 ∨ n.toNat % 8 = 3 := by omega
      have h911 := j2k3_spec_low hg hf hpk hk3 hn8 hh
      obtain ⟨f₀, hf₀⟩ := chiR_eq_of_k3_low hg hn1 hodd hqn hk3 hpk hn8 h911
      exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR Nat.prime_two _ _ (hf₀ r hr hrn m hm)⟩
    · have hn8 : n.toNat % 8 = 5 ∨ n.toNat % 8 = 7 := by omega
      have h920 := j2k3_spec_high hg hf hpk hk3 hn8 hh
      obtain ⟨f₀, hf₀⟩ := chiR_eq_of_k3_high hg hn1 hodd hqn hk3 hpk hn8 h920
      exact ⟨f₀, fun r hr hrn m hm => Yc_eq_of_chiR Nat.prime_two _ _ (hf₀ r hr hrn m hm)⟩

end Chains

/-! ### The soundness theorems -/

/-- The list of certificate `q`'s with `p ∣ q − 1`. -/
def qsFor (cert : Cert) (p : ℕ) : List ℕ :=
  (cert.qs.filter fun d => decide (p ∣ d.q - 1)).map (·.q)

theorem mem_qsFor {cert : Cert} {p q : ℕ} :
    q ∈ qsFor cert p ↔ ∃ d ∈ cert.qs, d.q = q ∧ p ∣ d.q - 1 := by
  simp only [qsFor, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨d, ⟨hd, hpd⟩, rfl⟩
    exact ⟨d, hd, rfl, hpd⟩
  · rintro ⟨d, hd, rfl, hpd⟩
    exact ⟨d, ⟨hd, hpd⟩, rfl⟩

/-- **Soundness of `some true`**: APR-CL certifies primality. -/
theorem aprclCheck_true {n : AzNat} {cert : Cert} (h : aprclCheck n cert = some true) :
    n.toNat.Prime := by
  classical
  unfold aprclCheck at h
  split_ifs at h with h2 hodd hstruct hts
  · cases h
  · split at h <;> cases h
  · have : NeZero n.toNat := ⟨by omega⟩
    have : Fact (1 < n.toNat) := ⟨by omega⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hodd hstruct
    have hodd' : n.toNat % 2 = 1 := Nat.odd_iff.mp ((AzNat.isOdd_iff n).mp hodd)
    have hn1 : 1 < n.toNat := by omega
    have hn2 : ¬ 2 ∣ n.toNat := by omega
    obtain ⟨hnd, hm, hp, he2, he2d⟩ := structOK_eq_true hstruct
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hts
    obtain ⟨⟨ht2, ht0⟩, hQnd⟩ := hts
    split at h <;> try cases h
    rename_i ua hstage
    obtain ⟨hring, h42, h43⟩ := llStage_pass hstage
    try dsimp only at h
    split at h <;> try cases h
    rename_i hsl hqst
    obtain ⟨hq1, hq2⟩ := qStage_pass hqst
    try dsimp only at h
    split at h <;> try cases h
    rename_i hall
    have hall' := Outcome.all_pass hall
    try dsimp only at h
    split_ifs at h with hsize
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hsize
    -- notation
    set N := n.toNat with hNdef
    set U := toZMod ua.1 with hUdef
    set A := toZMod ua.2 with hAdef
    set Lm := cert.ll.minus.map (fun t => (t.1, t.2.1)) with hLm
    set Lp := cert.ll.plus.map (fun t => (t.1, t.2.1)) with hLp
    set Qs := cert.qs.map (fun d => (d.q, d.e)) with hQs
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set F := (liftedS1 cert.ll cert.t').toNat with hFdef
    have hF : F = 2 ^ (cert.ll.e2 + padicValNat 2 cert.t' - 1)
        * prodPow ((Lm ++ Lp).map fun pe => (pe.1, pe.2 + padicValNat pe.1 cert.t')) :=
      toNat_liftedS1 cert.ll cert.t'
    have hv2 : 1 ≤ padicValNat 2 cert.t' := one_le_padicValNat_of_dvd ht0.ne' ht2
    have hF2 : 2 ∣ F := by
      rw [hF]
      exact (dvd_pow_self 2 (by omega)).mul_right _
    -- the per-`q` data
    have hQd : ∀ d ∈ cert.qs, d.q.Prime ∧ (d.q - 1) ∣ cert.t' ∧ 1 ≤ d.e ∧ (2 ≤ d.e → d.q ∣ cert.t') ∧
        N ^ cert.t' ≡ 1 [MOD d.q ^ d.e] ∧ ¬ d.q ∣ N ∧ ¬ d.q ∣ F ∧
        CL.checkGenerator d.q d.g = true ∧
        CL.checkIndexTable d.q d.g (CL.indexTableOf (CL.indexTableArr d.q d.g)) = true ∧
        (∀ p ∈ (d.q - 1).primeFactors, ∃ h,
          jTest n p (padicValNat p (d.q - 1)) d.q (CL.indexTableOf (CL.indexTableArr d.q d.g)) = some h) := by
      intro d hd
      obtain ⟨hs, hchk, -⟩ := hq1 d hd
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := qCheck_pass hchk
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun p hp => ?_⟩
      obtain ⟨h, hh⟩ := a11 p hp
      exact ⟨h, (a10 _ hh).2⟩
    have hQ2 : ∀ d ∈ cert.qs, d.q ≠ 2 := fun d hd h2 => (hQd d hd).2.2.2.2.2.2.1 (h2 ▸ hF2)
    -- `ε(r)`
    let ε : ℕ → ℕ := fun r => if hr : r ∣ N then
      (if IsSquare ((ZMod.castHom hr (ZMod r) U) ^ 2 + 4 * ZMod.castHom hr (ZMod r) A) then 0 else 1)
      else 0
    have hε : ∀ r, ε r < 2 := fun r => by
      simp only [ε]
      split_ifs <;> omega
    -- the (6.4) source and parity at `p = 2`
    have hS2 : (∀ r, r.Prime → r ∣ N → ∀ D, ∃ l, r ≡ N ^ l [MOD 2 ^ D]) ∧
        ∃ v, ∀ r, r.Prime → r ∣ N → ∀ l, r ≡ N ^ l [MOD 2 ^ (v + 1)] → l % 2 = ε r := by
      rcases ringParams_pass hodd' hring with ⟨hn4, hU, hA, hw⟩ | ⟨hn3, hA, hU, hj, hα⟩
      · have ha : Int.ModEq (N : ℤ) ((cert.ll.w : ℤ) ^ ((N - 1) / 2)) (-1) :=
          (ZMod.intCast_eq_intCast_iff _ _ _).mp (by push_cast; exact hw)
        refine ⟨CL.cond_6_4_two_of_c1 hn1 hn4 (a := (cert.ll.w : ℤ)) (by push_cast; exact hw),
          (N - 1).factorization 2, fun r hr hrn l hl => ?_⟩
        have := CL.c1_parity (Nat.odd_iff.mpr hodd') hr hrn ha
          (Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) (by omega)) hl
        simp only [ε, dite_eq_left hrn]
        rw [this, hUdef, hAdef, hU, hA, Int.cast_natCast]
      · refine ⟨CL.cond_6_4_two_of_c2 hn3 hα, (N + 1).factorization 2, fun r hr hrn l hl => ?_⟩
        have hv : 2 ≤ (N + 1).factorization 2 :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp
            (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega)
        have := CL.c2_parity hn3 hr hrn hα hv (Nat.ordProj_dvd _ _) hl
        simp only [ε, dite_eq_left hrn]
        rw [this, hUdef, hAdef, hU, hA, map_one, mul_one]
    obtain ⟨hS64₂, v₂, hpar₂⟩ := hS2
    -- the Lucas–Lehmer confinements with the coherent `ε`
    have h42' : ∀ pe ∈ Lm, ∀ r, r.Prime → r ∣ N → r ≡ 1 [MOD pe.1 ^ pe.2] := by
      intro pe hpe r hr hrn
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
      obtain ⟨hx1, hunit⟩ := test42_pass (h42 t ht)
      exact pocklington_prime_pow hn1 (hm _ hpe).1 (hm _ hpe).2.2.2 hx1 hunit r hr hrn
    have h43' : ∀ pe ∈ Lp, ∀ r, r.Prime → r ∣ N → r ≡ N ^ ε r [MOD pe.1 ^ pe.2] := by
      intro pe hpe r hr hrn
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
      obtain ⟨x₀, x₁, hN, hx1, hunit⟩ := test43_pass (h43 t ht)
      have := CL.test_4_3_confinement hn2 hr hrn (hp _ hpe).1 (hp _ hpe).2.1
        (hp _ hpe).2.2.1 (hp _ hpe).2.2.2 hN hx1 hunit
      simpa only [ε, dite_eq_left hrn] using this
    -- the (6.4) sources at odd `p ∣ t'`
    have hS64 : ∀ p ∈ cert.t'.primeFactors, p ≠ 2 → ¬ p ∣ N ∧ ¬ 2 ^ p ≡ 2 [MOD p ^ 2] ∧
        ∀ r, r.Prime → r ∣ N → ∀ D, ∃ l, r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ D] := by
      intro p hpt hp2
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpt
      have hp3 : 2 < p := by have := hpp.two_le; omega
      have hpass := hall' _ (List.mem_map_of_mem
        ((Nat.mem_primeFactors_iff_mem_primeFactorsList).mp hpt))
      obtain ⟨hpn, hW, hsrc⟩ := pCheck_pass hp2 hpass
      refine ⟨hpn, hW, ?_⟩
      rcases sixFourOK_eq_true hsrc with hll | hwf | ⟨qh, hqh, hpq, ph, hph, rfl, hph2⟩ |
        ⟨a, ha, rfl, hok⟩
      · rcases List.mem_append.mp hll with hmm | hpp'
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmm
          have hpe : (t.1, t.2.1) ∈ Lm := List.mem_map_of_mem ht
          obtain ⟨hx1, hunit⟩ := test42_pass (h42 t ht)
          have hpd : t.1 ∣ N - 1 := (dvd_pow_self _ (by have := (hm _ hpe).2.2.1; omega)).trans
            (hm _ hpe).2.2.2
          intro r hr hrn D
          obtain ⟨l, hl⟩ := CL.cond_6_4_of_test_4_2 hn1 hpp hp2 hpd hx1 hunit r hr hrn D
          exact ⟨l, CL.pow_sub_one_modEq_of_modEq hl⟩
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpp'
          have hpe : (t.1, t.2.1) ∈ Lp := List.mem_map_of_mem ht
          obtain ⟨x₀, x₁, hN, hx1, hunit⟩ := test43_pass (h43 t ht)
          have hpd : t.1 ∣ N + 1 := (dvd_pow_self _ (by have := (hp _ hpe).2.2.1; omega)).trans
            (hp _ hpe).2.2.2
          intro r hr hrn D
          obtain ⟨l, hl⟩ := CL.cond_6_4_of_test_4_3 hn2 hn1 hr hrn hpp hp2 hpd hN hx1 hunit D
          exact ⟨l, CL.pow_sub_one_modEq_of_modEq hl⟩
      · intro r hr hrn
        have hpr : ¬ p ∣ r := fun hd =>
          hpn (((Nat.prime_dvd_prime_iff_eq hpp hr).mp hd) ▸ hrn)
        exact CL.proposition_7_18 hpp hp3 hpn hwf hpr
      · obtain ⟨d, hd, hdq, hchk⟩ := hq2 qh hqh
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := qCheck_pass hchk
        rw [← hdq] at hpq
        exact sixFour_odd_of_h a1 a8 a9 hpp hp3 hpn a6 hpq (a10 _ hph).2 hph2
      · obtain ⟨hq', hpq', hqn', hchk', hidx', h, hh, hph⟩ := auxOK_eq_true hok
        exact sixFour_of_jOdd hq' hchk' hidx' hpp hp3 one_pos (by rwa [pow_one]) hpn hqn' hh hph
    -- the odd clauses
    have hcl_odd : ∀ p ∈ cert.t'.primeFactors, p ≠ 2 → ∀ r ∈ N.primeFactors, ∃ l,
        (∀ qe ∈ Qs, p ∣ qe.1 - 1 → Yfam cert qe.1 p r = Yfam cert qe.1 p N ^ l) ∧
        r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ (F * prodPow Qs).factorization p] := by
      intro p hpt hp2
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpt
      have hp3 : 2 < p := by have := hpp.two_le; omega
      obtain ⟨hpn, hW, hS⟩ := hS64 p hpt hp2
      have hcl := clause_odd hpp hp2 hn1 hpn hS (qsFor cert p)
        (fun q hq => by
          obtain ⟨d, hd, rfl, -⟩ := mem_qsFor.mp hq
          exact (hQd d hd).1)
        (fun q => (q - 1).factorization p)
        (fun q hq => by
          obtain ⟨d, hd, rfl, hpq⟩ := mem_qsFor.mp hq
          exact Nat.Prime.factorization_pos_of_dvd hpp (by have := (hQd d hd).1.two_le; omega) hpq)
        (fun q => Yfam cert q p)
        (fun q => if hq : q.Prime then
          @embC q p ((q - 1).factorization p) ⟨hq⟩ hpp (zP q p ((q - 1).factorization p)) else 0)
        (fun q hq => by
          obtain ⟨d, hd, rfl, -⟩ := mem_qsFor.mp hq
          have hqp := (hQd d hd).1
          rw [dite_eq_left hqp]
          exact @isPrimitiveRoot_embC_zP d.q p _ ⟨hqp⟩ hpp)
        (fun q hq => by
          obtain ⟨d, hd, rfl, hpq⟩ := mem_qsFor.mp hq
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hQd d hd
          obtain ⟨hh, hjt⟩ := a10 p (Nat.mem_primeFactors.mpr ⟨hpp, hpq, by have := a1.two_le; omega⟩)
          obtain ⟨f₀, hf₀⟩ := chain_odd_complex a1 a8 a9 hpp hp3 hW hpn a6 hpq hjt
          refine ⟨f₀, fun r hr hrn m hm => ?_⟩
          rw [Yfam_eq hQnd hd a1 hpp a8, dite_eq_left a1]
          exact hf₀ r hr hrn m hm)
        ((F * prodPow Qs).factorization p)
      intro r hr
      obtain ⟨l, hlY, hlc⟩ := hcl r hr
      refine ⟨l, fun qe hqe hpq => ?_, hlc⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
      exact hlY d.q (mem_qsFor.mpr ⟨d, hd, rfl, hpq⟩)
    -- the `p = 2` clause
    have hcl_two : ∀ r ∈ N.primeFactors, ∃ l, l % 2 = ε r ∧
        (∀ qe ∈ Qs, Yfam cert qe.1 2 r = Yfam cert qe.1 2 N ^ l) ∧
        r ≡ N ^ l [MOD 2 ^ (F * prodPow Qs).factorization 2] := by
      have hcl := clause_two hn1 hodd' hS64₂ ε v₂ hpar₂ (cert.qs.map (·.q))
        (fun q hq => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
          exact (hQd d hd).1)
        (fun q => (q - 1).factorization 2)
        (fun q hq => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
          have hqp := (hQd d hd).1
          have h2q : 2 ∣ d.q - 1 := by
            obtain ⟨w, hw⟩ := hqp.odd_of_ne_two (hQ2 d hd)
            exact ⟨w, by omega⟩
          exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by have := hqp.two_le; omega) h2q)
        (fun q => Yfam cert q 2)
        (fun q => if hq : q.Prime then
          @embC q 2 ((q - 1).factorization 2) ⟨hq⟩ Nat.prime_two (zP q 2 ((q - 1).factorization 2))
          else 0)
        (fun q hq => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
          have hqp := (hQd d hd).1
          rw [dite_eq_left hqp]
          exact @isPrimitiveRoot_embC_zP d.q 2 _ ⟨hqp⟩ Nat.prime_two)
        (fun q hq => by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hQd d hd
          have h2q : 2 ∣ d.q - 1 := by
            obtain ⟨w, hw⟩ := a1.odd_of_ne_two (hQ2 d hd)
            exact ⟨w, by omega⟩
          obtain ⟨hh, hjt⟩ := a10 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2q, by have := a1.two_le; omega⟩)
          obtain ⟨f₀, hf₀⟩ := chain_two_complex a1 a8 a9 hodd' a6 (hQ2 d hd) hjt
          refine ⟨f₀, fun r hr hrn m hm => ?_⟩
          rw [Yfam_eq hQnd hd a1 Nat.prime_two a8, dite_eq_left a1]
          exact hf₀ r hr hrn m hm)
        ((F * prodPow Qs).factorization 2)
      intro r hr
      obtain ⟨l, hl2, hlY, hlc⟩ := hcl r hr
      refine ⟨l, hl2, fun qe hqe => ?_, by simpa using hlc⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
      exact hlY d.q (List.mem_map_of_mem hd)
    -- the final trial division
    have hS : (liftedS1 cert.ll cert.t' * AzNat.ofNat (s2Of cert.qs)).toNat = F * prodPow Qs := by
      rw [AzNat.toNat_mul, AzNat.toNat_ofNat, s2Of_eq]
    have hsize' : N < (F * prodPow Qs) ^ 2 := by
      have := (AzNat.lt_iff_toNat_lt _ _).mp hsize
      rwa [AzNat.toNat_square, hS] at this
    have hs1 : 1 < (liftedS1 cert.ll cert.t' * AzNat.ofNat (s2Of cert.qs)).toNat := by
      rw [hS]
      have hP : 0 < prodPow Qs := prodPow_pos fun qe hqe => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
        exact (hQd d hd).1.pos
      have hF0 : 0 < F := by
        rw [hF]
        refine Nat.mul_pos (pow_pos two_pos _) (prodPow_pos fun pe' hpe' => ?_)
        obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp hpe'
        rcases List.mem_append.mp hpe with h | h
        · exact (hm pe h).1.pos
        · exact (hp pe h).1.pos
      have hF1 : 2 ≤ F := Nat.le_of_dvd hF0 hF2
      calc 1 < 2 * 1 := by norm_num
        _ ≤ F * prodPow Qs := Nat.mul_le_mul hF1 hP
    obtain ⟨i, hi0, hri, hloop⟩ := finalDiv_true (by omega) hs1 (i₀ := 0) (r := 1)
      (by rw [pow_zero]; exact (Nat.mod_eq_of_lt hs1).symm) (fun j hj hj' => by omega) h
    rw [hS] at hri hloop
    exact prime_of_aprcl h2 hodd' hnd hm hp he2 he2d ε hε h42' h43' ht0 ht2
      (by simpa [hQs, List.map_map, Function.comp_def] using hQnd)
      (fun qe hqe => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hQd d hd
        exact ⟨a1, hQ2 d hd, a2, a3, a4, a6, a5⟩)
      hF (fun qe hqe => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
        exact (hQd d hd).2.2.2.2.2.2.1)
      (Yfam cert)
      (fun qe hqe p hpq => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hqe
        obtain ⟨a1, -, -, -, -, -, -, a8, -⟩ := hQd d hd
        rw [Yfam_eq hQnd hd a1 (Nat.prime_of_mem_primeFactors hpq) a8]
        exact @orderOf_Yc d.q p _ ⟨a1⟩ _ _ _ _)
      hcl_odd hcl_two hsize' (by omega) hri hloop
  · rename_i heq
    rw [heq]
    exact Nat.prime_two
  · cases h

/-- **Soundness of `some false`**: every compositeness verdict is correct. -/
theorem aprclCheck_false {n : AzNat} {cert : Cert} (h : aprclCheck n cert = some false) :
    ¬ n.toNat.Prime := by
  intro hN
  unfold aprclCheck at h
  split_ifs at h with h2 hodd hstruct hts
  · simp only [Bool.not_eq_true'] at hodd
    have hnodd : ¬ Odd n.toNat := fun ho => by
      have := (AzNat.isOdd_iff n).mpr ho
      rw [hodd] at this
      exact Bool.false_ne_true this
    have h2d : 2 ∣ n.toNat := Nat.dvd_of_mod_eq_zero (by have := Nat.odd_iff.not.mp hnodd; omega)
    have := hN.eq_one_or_self_of_dvd 2 h2d
    omega
  · have : NeZero n.toNat := ⟨by omega⟩
    have : Fact (1 < n.toNat) := ⟨by omega⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hodd hstruct
    have hodd' : n.toNat % 2 = 1 := Nat.odd_iff.mp ((AzNat.isOdd_iff n).mp hodd)
    split at h <;> try cases h
    rename_i hstage
    rcases llStage_composite hstage with hring | ⟨ua, hring, ⟨t, ht, h42⟩ | ⟨t, ht, h43⟩⟩
    · exact ringParams_composite hodd' hring hN
    · exact test42_composite h42 hN
    · exact test43_composite (not_isSquare_of_ringParams hN hodd' hring) h43 hN
  · have : NeZero n.toNat := ⟨by omega⟩
    have : Fact (1 < n.toNat) := ⟨by omega⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hodd hstruct
    have hodd' : n.toNat % 2 = 1 := Nat.odd_iff.mp ((AzNat.isOdd_iff n).mp hodd)
    split at h <;> try cases h
    · rename_i hstage
      rcases llStage_composite hstage with hring | ⟨ua, hring, ⟨t, ht, h42⟩ | ⟨t, ht, h43⟩⟩
      · exact ringParams_composite hodd' hring hN
      · exact test42_composite h42 hN
      · exact test43_composite (not_isSquare_of_ringParams hN hodd' hring) h43 hN
    · rename_i ua hstage
      try dsimp only at h
      split at h <;> try cases h
      · rename_i hqst
        obtain ⟨d, hd, hc⟩ := qStage_composite hqst
        exact qCheck_composite hc hN
      · rename_i hsl hqst
        try dsimp only at h
        split at h <;> try cases h
        · rename_i hall
          obtain ⟨o, ho, ho'⟩ := Outcome.all_composite hall
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
          exact pCheck_composite (by omega) (Nat.prime_of_mem_primeFactorsList hp) ho' hN
        · try dsimp only at h
          split_ifs at h with hsize
          obtain ⟨d, hd, hd1, hdn⟩ := finalDiv_false h
          rcases hN.eq_one_or_self_of_dvd d hd with h1 | h1 <;> omega
  · cases h
  · have : n.toNat ≤ 1 := by omega
    interval_cases hn : n.toNat
    · exact Nat.not_prime_zero hN
    · exact Nat.not_prime_one hN

/-- **The generated-certificate test is sound**: `some true` means prime. -/
theorem aprclTest_true {n : AzNat} {B : ℕ} (h : aprclTest n B = some true) : n.toNat.Prime :=
  aprclCheck_true h

/-- **The generated-certificate test is sound**: `some false` means composite. -/
theorem aprclTest_false {n : AzNat} {B : ℕ} (h : aprclTest n B = some false) : ¬ n.toNat.Prime :=
  aprclCheck_false h

/-- **The selected-certificate test is sound**: `some true` means prime. -/
theorem aprclTestSel_true {n : AzNat} {B : ℕ} (h : aprclTestSel n B = some true) : n.toNat.Prime :=
  aprclCheck_true h

/-- **The selected-certificate test is sound**: `some false` means composite. -/
theorem aprclTestSel_false {n : AzNat} {B : ℕ} (h : aprclTestSel n B = some false) :
    ¬ n.toNat.Prime :=
  aprclCheck_false h

end APRCL

end Azurite
