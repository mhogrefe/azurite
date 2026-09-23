/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra Theorem (6.3): the master reduction to divisor
  confinement.**

  This is the keystone of the whole test: if the auxiliary numbers
  `t, s` satisfy condition (2.3), and if for every prime `r ∣ n` and
  every prime `p ∣ t` there is an exponent `l` such that

  * **(6.5)** the chosen characters `χ_{p,q} ∈ Y_s` satisfy
    `χ_{p,q}(r) = χ_{p,q}(n)^l`, and
  * **(6.4)** `r^(p−1) ≡ (n^(p−1))^l  (mod p^(v_p(s)))`,

  then **(2.5)** holds: every divisor `r` of `n` is `≡ n^i (mod s)`
  for some `i < t`.

  The paper states (6.4)/(6.5) with a `p`-adic exponent
  `l_p(r) ∈ ℤ_p`; its proof immediately truncates `l_p(r)` to a
  sufficiently deep finite level and works with congruences.  We state
  the hypotheses at that finite level directly (one natural number `l`
  per pair `(r, p)`, constrained exactly as deep as the proof needs) —
  this is both what the proof consumes and what the Gauss/Jacobi-sum
  tests of the later sections actually establish.

  The proof follows the paper.  A CRT exponent `l(r)` is chosen with
  `l(r) ≡ l_p(r) mod p^(H_p)` for all `p ∣ t` (`H_p` large).  For a
  prime `q ∣ s`, the characters `χ_{p,q}` generate `X_q` (our (6.2)),
  so `χ(r) = χ(n^{l(r)})` for every character `χ` mod `q`, whence
  `r ≡ n^{l(r)} (mod q)` by separation (6.1).  If `v_q(s) ≥ 2` then
  `q ∣ t` (via Proposition (4.1) and the shape of `e(t)`), and (6.4)
  at `p = q` upgrades the congruence to modulus `q^(v_q(s))`: the
  element `a = r·n^{−l(r)}` satisfies `a ≡ 1 mod q` and
  `a^(q−1) ≡ 1 mod q^(v_q(s))`, so its multiplicative order divides
  both `q^(v_q(s)−1)` and `q − 1`, hence is `1`.  CRT over the primes
  `q ∣ s` gives `r ≡ n^{l(r)} (mod s)` for prime `r`; multiplicativity
  extends this to all divisors (the paper's Remark (6.7)), and `l(r)`
  is reduced mod `t` using `n^t ≡ 1 (mod s)`.
-/
import Azurite.CohenLenstra.Characters
import Azurite.CohenLenstra.Proposition_4_1
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Basic

namespace Azurite

namespace CL

open Finset

/-! ### Support lemmas -/

/-- Powers through a modulus-killing exponent: if `x^d = 1` and
`l ≡ l' (mod d)`, then `x^l = x^l'` — in any monoid. -/
theorem pow_eq_pow_of_modEq {M : Type _} [Monoid M] {x : M} {d l l' : ℕ}
    (hx : x ^ d = 1) (h : l ≡ l' [MOD d]) : x ^ l = x ^ l' := by
  have key : ∀ j : ℕ, x ^ j = x ^ (j % d) := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j d]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [key l, key l', h]

/-- One-units have prime-power order: if `a ≡ 1 (mod p)` then
`a^(p^k) ≡ 1 (mod p^(k+1))`. -/
theorem pow_pow_modEq_one {p a : ℕ} (ha : a ≡ 1 [MOD p]) (k : ℕ) :
    a ^ p ^ k ≡ 1 [MOD p ^ (k + 1)] := by
  have h1 : ((p : ℤ)) ∣ (a : ℤ) - 1 := by
    simpa using dvd_sub_comm.mp ha.dvd
  have h2 := dvd_sub_pow_of_dvd_sub h1 k
  rw [one_pow] at h2
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp (by exact_mod_cast h2)

/-- A unit of `ZMod (q^m)` that maps to `1` in `ZMod q` has order
dividing `q^(m−1)`. -/
theorem units_pow_prime_pow_eq_one {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0)
    (u : (ZMod (q ^ m))ˣ)
    (h1 : Units.map (ZMod.castHom (dvd_pow_self q hm) (ZMod q)).toMonoidHom
      u = 1) :
    u ^ q ^ (m - 1) = 1 := by
  have : NeZero (q ^ m) := ⟨pow_ne_zero _ hq.pos.ne'⟩
  have hval : (u : ZMod (q ^ m)).val ≡ 1 [MOD q] := by
    have hv := congrArg Units.val h1
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      ZMod.castHom_apply, Units.val_one] at hv
    rw [← ZMod.natCast_val] at hv
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hv, Nat.cast_one])
  have h2 := pow_pow_modEq_one hval (m - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h2
  have hcast : (((u : ZMod (q ^ m)).val : ℕ) : ZMod (q ^ m)) = ↑u := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  refine Units.ext ?_
  calc ((u ^ q ^ (m - 1) : (ZMod (q ^ m))ˣ) : ZMod (q ^ m))
      = ((((u : ZMod (q ^ m)).val ^ q ^ (m - 1) : ℕ)) : ZMod (q ^ m)) := by
        rw [Nat.cast_pow, hcast, Units.val_pow_eq_pow_val]
    _ = ((1 : ℕ) : ZMod (q ^ m)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    _ = ((1 : (ZMod (q ^ m))ˣ) : ZMod (q ^ m)) := by
        rw [Nat.cast_one, Units.val_one]

/-- Primes dividing `e t` have `q − 1 ∣ t` — the fact behind the
paper's remark that `χ_{p,q} ∈ Y_s` forces `p ∣ t`. -/
theorem sub_one_dvd_of_dvd_e {t q : ℕ} (ht : t ≠ 0) (hq : q.Prime)
    (h : q ∣ e t) : q - 1 ∣ t := by
  by_cases ht2 : Odd t
  · rw [e, ite_eq_left ht2] at h
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
    simp [hq2]
  · by_cases hq2 : q = 2
    · simp [hq2]
    · have hpos : (e t).factorization q ≠ 0 :=
        ((Nat.Prime.factorization_pos_of_dvd hq (e_ne_zero t) h).ne')
      rw [factorization_e_odd_prime ht2 ht hq hq2] at hpos
      by_contra hnd
      rw [ite_eq_right hnd] at hpos
      exact hpos rfl
/-- Primes appearing at least squared in `e t` divide `t` — the fact
behind the paper's step "`m(q) ≥ 2` implies `q ∣ t`". -/
theorem dvd_of_two_le_factorization_e {t q : ℕ} (ht : t ≠ 0)
    (hq : q.Prime) (h2 : 2 ≤ (e t).factorization q) : q ∣ t := by
  by_cases ht2 : Odd t
  · rw [e, ite_eq_left ht2] at h2
    have hle : (2 : ℕ).factorization q ≤ 1 := by
      rw [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply]
      split <;> omega
    omega
  · by_cases hq2 : q = 2
    · subst hq2
      exact (Nat.not_odd_iff_even.mp ht2).two_dvd
    · rw [factorization_e_odd_prime ht2 ht hq hq2] at h2
      by_cases hd : q - 1 ∣ t
      · rw [ite_eq_left hd] at h2
        exact Nat.dvd_of_factorization_pos (by omega)
      · rw [ite_eq_right hd] at h2
        omega

/-- A congruence holding modulo each member of a pairwise-coprime
family holds modulo the product. -/
theorem modEq_prod_of_pairwise_coprime {f : ℕ → ℕ} {a b : ℕ} :
    ∀ {S : Finset ℕ}, Set.Pairwise ↑S (Function.onFun Nat.Coprime f) →
      (∀ q ∈ S, a ≡ b [MOD f q]) → a ≡ b [MOD ∏ q ∈ S, f q] := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simpa using Nat.modEq_one
  | insert q S hqS ih =>
    intro hco h
    rw [Finset.prod_insert hqS]
    have hco' : Nat.Coprime (f q) (∏ x ∈ S, f x) :=
      Nat.Coprime.prod_right fun i hi =>
        hco (Finset.mem_coe.mpr (Finset.mem_insert_self q S))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi))
          (by rintro rfl; exact hqS hi)
    exact (Nat.modEq_and_modEq_iff_modEq_mul hco').mp
      ⟨h q (Finset.mem_insert_self q S),
        ih (hco.mono (by simp))
          fun q' hq' => h q' (Finset.mem_insert_of_mem hq')⟩

/-! ### Theorem (6.3) -/

/-- **Cohen–Lenstra Theorem (6.3), prime-divisor case**: the
congruence `r ≡ n^l (mod s)` for a single prime divisor `r` of `n`,
with an unbounded exponent. -/
private theorem theorem_6_3_prime {n s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hco : n.Coprime (s * t)) (h23 : ∀ u : (ZMod s)ˣ, u ^ t = 1)
    (Y : (q : ℕ) → (p : ℕ) → MulChar (ZMod q) ℂ)
    (hY : ∀ q ∈ s.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      orderOf (Y q p) = p ^ (q - 1).factorization p)
    {r : ℕ}
    (h : ∀ p ∈ t.primeFactors, ∃ l : ℕ,
      (∀ q ∈ s.primeFactors, p ∣ q - 1 →
        Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
      r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ s.factorization p])
    (hrn : r ∣ n) :
    ∃ i : ℕ, r ≡ n ^ i [MOD s] := by
  classical
  have hns : n.Coprime s := Nat.Coprime.coprime_dvd_right (dvd_mul_right s t) hco
  have hset : s ∣ e t := (proposition_4_1 hs ht).mp h23
  -- the CRT modulus data
  set P := s * ∏ q ∈ s.primeFactors, (q - 1) with hPdef
  have hP0 : P ≠ 0 := mul_ne_zero hs.ne'
    (Finset.prod_ne_zero_iff.mpr fun q hq =>
      Nat.sub_ne_zero_of_lt (Nat.prime_of_mem_primeFactors hq).one_lt)
  -- select the exponents from the hypothesis, totalized
  have h' : ∀ p : ℕ, ∃ l : ℕ, p ∈ t.primeFactors →
      ((∀ q ∈ s.primeFactors, p ∣ q - 1 →
        Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
       r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ s.factorization p]) := by
    intro p
    by_cases hp : p ∈ t.primeFactors
    · obtain ⟨l, hl⟩ := h p hp
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun hcon => (hp hcon).elim⟩
  choose lp hlp using h'
  -- the common exponent, by CRT over the primes dividing t
  obtain ⟨l, hl⟩ := Nat.chineseRemainderOfFinset lp
    (fun p => p ^ P.factorization p) t.primeFactors
    (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).pos.ne')
    (fun p hp p' hp' hne => Nat.Coprime.pow _ _
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hp')).mpr hne))
  -- the congruence modulo each maximal prime power of s
  have key : ∀ q ∈ s.primeFactors, r ≡ n ^ l [MOD q ^ s.factorization q] := by
    intro q hq
    have hq' : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hq'⟩
    have hqs : q ∣ s := Nat.dvd_of_mem_primeFactors hq
    have hq1t : q - 1 ∣ t := sub_one_dvd_of_dvd_e ht.ne' hq' (hqs.trans hset)
    have hcoqn : n.Coprime q := Nat.Coprime.coprime_dvd_right hqs hns
    have hcoqr : r.Coprime q :=
      Nat.Coprime.coprime_dvd_right hqs
        (Nat.Coprime.coprime_dvd_left hrn hns)
    -- Step A: χ(r) = χ(n^l) for every character mod q, via generation
    have hall : ∀ χ : MulChar (ZMod q) ℂ,
        χ ((r : ℕ) : ZMod q) = χ (((n : ℕ) : ZMod q) ^ l) := by
      have hgen : Subgroup.closure
          {χ : MulChar (ZMod q) ℂ | ∃ p ∈ (q - 1).primeFactors, χ = Y q p}
            = ⊤ :=
        closure_eq_top_of_forall_orderOf fun p hp =>
          ⟨Y q p, ⟨p, hp, rfl⟩, hY q hq p hp⟩
      intro χ
      have hχmem : χ ∈ Subgroup.closure
          {χ : MulChar (ZMod q) ℂ | ∃ p ∈ (q - 1).primeFactors, χ = Y q p} := by
        rw [hgen]; exact Subgroup.mem_top χ
      induction hχmem using Subgroup.closure_induction with
      | mem χ' hχ' =>
        obtain ⟨p, hpq1, rfl⟩ := hχ'
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hpq1
        have hpq1' : p ∣ q - 1 := Nat.dvd_of_mem_primeFactors hpq1
        have hpt : p ∈ t.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp', hpq1'.trans hq1t, ht.ne'⟩
        have hA := (hlp p hpt).1 q hq hpq1'
        -- kill the exponent difference: χ_{p,q}(n) has p-power order
        have hxord : (Y q p ((n : ℕ) : ZMod q)) ^ p ^ P.factorization p
            = 1 := by
          have hd : orderOf (Y q p) ∣ p ^ P.factorization p := by
            rw [hY q hq p hpq1]
            refine pow_dvd_pow p ?_
            have hq1P : (q - 1) ∣ P :=
              (Finset.dvd_prod_of_mem (fun q' => q' - 1) hq).trans
                (dvd_mul_left _ _)
            exact Finsupp.le_def.mp
              ((Nat.factorization_le_iff_dvd
                (Nat.sub_ne_zero_of_lt hq'.one_lt) hP0).mpr hq1P) p
          obtain ⟨c, hc⟩ := hd
          have hbase : (Y q p ((n : ℕ) : ZMod q)) ^ orderOf (Y q p)
              = 1 := by
            rw [show ((n : ℕ) : ZMod q)
                  = ((ZMod.unitOfCoprime n hcoqn : (ZMod q)ˣ) : ZMod q)
                from (ZMod.coe_unitOfCoprime n hcoqn).symm,
              ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
              MulChar.one_apply_coe]
          rw [hc, pow_mul, hbase, one_pow]
        rw [map_pow, hA,
          pow_eq_pow_of_modEq hxord ((hl p hpt).symm)]
      | one =>
        rw [show ((r : ℕ) : ZMod q)
              = ((ZMod.unitOfCoprime r hcoqr : (ZMod q)ˣ) : ZMod q)
            from (ZMod.coe_unitOfCoprime r hcoqr).symm,
          show (((n : ℕ) : ZMod q) ^ l)
              = ((ZMod.unitOfCoprime n hcoqn ^ l : (ZMod q)ˣ) : ZMod q)
            from by rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime],
          MulChar.one_apply_coe, MulChar.one_apply_coe]
      | mul χ₁ χ₂ _ _ h₁ h₂ =>
        rw [MulChar.mul_apply, MulChar.mul_apply, h₁, h₂]
      | inv χ' _ h' =>
        rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', h']
    -- Step B: separation gives the congruence mod q
    have hqmod : ((r : ℕ) : ZMod q) = ((n ^ l : ℕ) : ZMod q) := by
      have hu := eq_6_1 (x := ZMod.unitOfCoprime r hcoqr)
        (y := ZMod.unitOfCoprime n hcoqn ^ l) fun χ => by
          rw [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val,
            ZMod.coe_unitOfCoprime]
          exact hall χ
      have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hu
      simpa [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val,
        Nat.cast_pow] using this
    -- Step C: upgrade to the maximal power of q in s
    set m := s.factorization q with hmdef
    have hm1 : 1 ≤ m := (Nat.Prime.factorization_pos_of_dvd hq' hs.ne' hqs)
    rcases eq_or_lt_of_le hm1 with hm | hm
    · -- m = 1: nothing to upgrade
      rw [← hm, pow_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hqmod
    · -- m ≥ 2: q divides t, and (6.4) at p = q lifts the congruence
      have hm2 : 2 ≤ m := hm
      have hqt : q ∈ t.primeFactors := by
        refine Nat.mem_primeFactors.mpr ⟨hq', ?_, ht.ne'⟩
        refine dvd_of_two_le_factorization_e ht.ne' hq' ?_
        calc (2 : ℕ) ≤ m := hm2
          _ ≤ (e t).factorization q :=
            Finsupp.le_def.mp
              ((Nat.factorization_le_iff_dvd hs.ne' (e_ne_zero t)).mpr
                hset) q
      have hB := (hlp q hqt).2
      have hfermat : n ^ (q - 1) ≡ 1 [MOD q] := by
        have hz : ((n : ℕ) : ZMod q) ≠ 0 := fun h0 =>
          hq'.one_lt.ne' (hcoqn.symm.eq_one_of_dvd
            ((ZMod.natCast_eq_zero_iff n q).mp h0))
        refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
        rw [Nat.cast_pow, Nat.cast_one, ZMod.pow_card_sub_one_eq_one hz]
      -- transfer the exponent in (6.4) from lp q to l
      have hx1 : (((n ^ (q - 1) : ℕ)) : ZMod (q ^ m)) ^ q ^ (m - 1)
          = 1 := by
        have h2 := pow_pow_modEq_one hfermat (m - 1)
        rw [Nat.sub_add_cancel hm1] at h2
        rw [← Nat.cast_pow]
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h2, Nat.cast_one]
      have hxH : (((n ^ (q - 1) : ℕ)) : ZMod (q ^ m)) ^ q ^ P.factorization q
          = 1 := by
        have hle : m - 1 ≤ P.factorization q :=
          le_trans (Nat.sub_le m 1)
            (Finsupp.le_def.mp
              ((Nat.factorization_le_iff_dvd hs.ne' hP0).mpr
                (dvd_mul_right s _)) q)
        obtain ⟨c, hc⟩ := pow_dvd_pow q hle
        rw [hc, pow_mul, hx1, one_pow]
      have htr : (n ^ (q - 1)) ^ lp q ≡ (n ^ (q - 1)) ^ l
          [MOD q ^ m] := by
        refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
        rw [Nat.cast_pow (n ^ (q - 1)) (lp q), Nat.cast_pow (n ^ (q - 1)) l]
        exact (pow_eq_pow_of_modEq hxH (hl q hqt)).symm
      have hc : r ^ (q - 1) ≡ (n ^ l) ^ (q - 1) [MOD q ^ m] := by
        refine (hB.trans htr).trans ?_
        rw [← pow_mul, mul_comm (q - 1) l, pow_mul]
      -- the endgame: the unit r·(n^l)⁻¹ mod q^m has order dividing
      -- gcd(q−1, q^(m−1)) = 1
      have hrM : r.Coprime (q ^ m) := hcoqr.pow_right m
      have hnlM : (n ^ l).Coprime (q ^ m) := (hcoqn.pow_left l).pow_right m
      set RU := ZMod.unitOfCoprime r hrM with hRU
      set NU := ZMod.unitOfCoprime (n ^ l) hnlM with hNU
      have hA1 : (RU * NU⁻¹) ^ (q - 1) = 1 := by
        have hpow : RU ^ (q - 1) = NU ^ (q - 1) := by
          refine Units.ext ?_
          rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hRU, hNU,
            ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime,
            ← Nat.cast_pow, ← Nat.cast_pow]
          exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
        rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
      have hAq : (RU * NU⁻¹) ^ q ^ (m - 1) = 1 := by
        refine units_pow_prime_pow_eq_one hq'
          (by omega : m ≠ 0) _ ?_
        have hmapeq : Units.map
              (ZMod.castHom (dvd_pow_self q (by omega : m ≠ 0))
                (ZMod q)).toMonoidHom RU
            = Units.map (ZMod.castHom (dvd_pow_self q (by omega : m ≠ 0))
                (ZMod q)).toMonoidHom NU := by
          refine Units.ext ?_
          simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe,
            MonoidHom.coe_coe]
          rw [hRU, hNU, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime,
            map_natCast, map_natCast]
          exact hqmod
        rw [map_mul, map_inv, hmapeq, mul_inv_cancel]
      have hAone : RU * NU⁻¹ = 1 := by
        have hd1 : orderOf (RU * NU⁻¹) ∣ q - 1 :=
          orderOf_dvd_of_pow_eq_one hA1
        have hd2 : orderOf (RU * NU⁻¹) ∣ q ^ (m - 1) :=
          orderOf_dvd_of_pow_eq_one hAq
        have hcop : Nat.Coprime (q - 1) (q ^ (m - 1)) := by
          refine Nat.Coprime.pow_right _ ?_
          have h1 := Nat.gcd_dvd_left (q - 1) q
          have h2 := Nat.gcd_dvd_right (q - 1) q
          have h3 := Nat.dvd_sub h2 h1
          rw [show q - (q - 1) = 1 from by have := hq'.pos; omega,
            Nat.dvd_one] at h3
          exact h3
        rw [← orderOf_eq_one_iff]
        exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
      have hRUNU : RU = NU := mul_inv_eq_one.mp hAone
      have := congrArg (fun u : (ZMod (q ^ m))ˣ => (u : ZMod (q ^ m))) hRUNU
      rw [hRU, hNU] at this
      simp only [ZMod.coe_unitOfCoprime] at this
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  -- assemble over the primes dividing s
  refine ⟨l, ?_⟩
  have hsprod : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hs.ne'
  rw [← hsprod]
  refine modEq_prod_of_pairwise_coprime ?_ key
  intro q hq q' hq' hne
  exact Nat.Coprime.pow _ _
    ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq))
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq'))).mpr hne)

/-- **Cohen–Lenstra Theorem (6.3)**: let `t, s` satisfy condition
(2.3) (every unit of `ℤ/s` has `u^t = 1`), and let `n > 1` be coprime
to `st`.  Suppose the finite-level forms of (6.4)/(6.5) hold: for
every prime `r ∣ n` and every prime `p ∣ t` there is an exponent `l`
with `χ(r) = χ(n)^l` for the chosen characters `χ = Y q p` of `p`-power
order (over the primes `q ∣ s` with `p ∣ q − 1`), and
`r^(p−1) ≡ (n^(p−1))^l (mod p^(v_p(s)))`.  Then condition **(2.5)**
holds: every divisor `r` of `n` satisfies `r ≡ n^i (mod s)` for some
`i < t`. -/
theorem theorem_6_3 {n s t : ℕ} (hn : 1 < n) (hs : 0 < s) (ht : 0 < t)
    (hco : n.Coprime (s * t)) (h23 : ∀ u : (ZMod s)ˣ, u ^ t = 1)
    (Y : (q : ℕ) → (p : ℕ) → MulChar (ZMod q) ℂ)
    (hY : ∀ q ∈ s.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      orderOf (Y q p) = p ^ (q - 1).factorization p)
    (h : ∀ r ∈ n.primeFactors, ∀ p ∈ t.primeFactors, ∃ l : ℕ,
      (∀ q ∈ s.primeFactors, p ∣ q - 1 →
        Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
      r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ s.factorization p]) :
    ∀ r, r ∣ n → ∃ i < t, r ≡ n ^ i [MOD s] := by
  have hns : n.Coprime s := Nat.Coprime.coprime_dvd_right (dvd_mul_right s t) hco
  -- every divisor is congruent to SOME power of n mod s
  have hstep : ∀ r : ℕ, r ∣ n → ∃ i : ℕ, r ≡ n ^ i [MOD s] := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrn
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (by omega : n ≠ 0) (Nat.eq_zero_of_zero_dvd hrn)
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hr0) with h1 | h1
      · exact ⟨0, by rw [← h1, pow_zero]⟩
      · -- peel off the least prime factor
        have hrp : r.minFac.Prime := Nat.minFac_prime (by omega)
        obtain ⟨i₁, hi₁⟩ := theorem_6_3_prime hs ht hco h23 Y hY
          (h r.minFac (Nat.mem_primeFactors.mpr
            ⟨hrp, (Nat.minFac_dvd r).trans hrn, by omega⟩))
          ((Nat.minFac_dvd r).trans hrn)
        obtain ⟨i₂, hi₂⟩ := ih (r / r.minFac)
          (Nat.div_lt_self (by omega) hrp.one_lt)
          ((Nat.div_dvd_of_dvd (Nat.minFac_dvd r)).trans hrn)
        refine ⟨i₁ + i₂, ?_⟩
        calc r = r.minFac * (r / r.minFac) :=
              (Nat.mul_div_cancel' (Nat.minFac_dvd r)).symm
          _ ≡ n ^ i₁ * n ^ i₂ [MOD s] := hi₁.mul hi₂
          _ = n ^ (i₁ + i₂) := (pow_add n i₁ i₂).symm
  -- reduce the exponent modulo t, using n^t ≡ 1 (mod s)
  intro r hrn
  obtain ⟨i, hi⟩ := hstep r hrn
  refine ⟨i % t, Nat.mod_lt _ ht, ?_⟩
  refine hi.trans ?_
  have hx : ((n : ℕ) : ZMod s) ^ t = 1 := by
    have := congrArg (fun u : (ZMod s)ˣ => (u : ZMod s))
      (h23 (ZMod.unitOfCoprime n hns))
    simpa [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] using this
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [Nat.cast_pow, Nat.cast_pow]
  exact pow_eq_pow_of_modEq hx (Nat.mod_modEq i t).symm

end CL

end Azurite
