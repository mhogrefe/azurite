/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LengthAfterPoint
import Azurite.AzRat.Equiv.Basic
import Azurite.AzNat.Equiv.Div.DivModLimb
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Correctness of `AzRat.lengthAfterPoint`

`lengthAfterPoint b q = some L` iff `L` is the least `ℓ` with `q.den ∣ b^ℓ`, and `= none` iff
there is no such `ℓ` (`lengthAfterPoint_some_iff`, `lengthAfterPoint_none_iff`).  The proof
goes through `Nat.factorization`: with `b = ∏ pᵢ^mᵢ` (the table), `den ∣ b^L` iff every prime
of `den` is some `pᵢ` and `v_{pᵢ}(den) ≤ L · mᵢ`; `countFactor` computes `v_{pᵢ}(den)` and
strips `pᵢ`, so what is left at the end is `1` iff `den` has no other primes, and
`max ⌈v_{pᵢ}(den) / mᵢ⌉ ≤ L` iff all the inequalities hold.
-/

namespace Azurite.AzRat

/-! ### `countFactor` -/

/-- `countFactor p n = (c, m)` with `n = p^c · m`, `p ∤ m`, `m ≠ 0`, for `2 ≤ p` and `n ≠ 0`. -/
theorem countFactor_spec (p : UInt64) (hp : 2 ≤ p.toNat) (n : AzNat) (hn : n ≠ 0) :
    (countFactor p n).2 ≠ 0 ∧
    n.toNat = p.toNat ^ (countFactor p n).1 * (countFactor p n).2.toNat ∧
    ¬ p.toNat ∣ (countFactor p n).2.toNat := by
  suffices h : ∀ (N : ℕ) (n : AzNat), n.toNat = N → n ≠ 0 →
      (countFactor p n).2 ≠ 0 ∧
      n.toNat = p.toNat ^ (countFactor p n).1 * (countFactor p n).2.toNat ∧
      ¬ p.toNat ∣ (countFactor p n).2.toNat from h _ n rfl hn
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hN hn
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by decide)
  have hdm := AzNat.toNat_divModUInt64 n p hp0
  simp only at hdm
  set Q := (AzNat.divModUInt64 n p hp0).1 with hQ_def
  set r := (AzNat.divModUInt64 n p hp0).2 with hr_def
  have hnN : n.toNat ≠ 0 := fun hz => hn (AzNat.toNat_injective (by rw [hz]; rfl))
  rw [countFactor]
  simp only [hp, ↓reduceDIte, hn, ← hQ_def, ← hr_def]
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    have hr0 : r.toNat = 0 := by rw [hr]; rfl
    have hQ0 : Q ≠ 0 := by
      intro hz
      have : Q.toNat = 0 := by rw [hz]; rfl
      rw [this, hr0] at hdm
      omega
    have hQlt : Q.toNat < N := by
      have h2 : Q.toNat * 2 ≤ Q.toNat * p.toNat := Nat.mul_le_mul_left _ hp
      omega
    obtain ⟨h1, h2, h3⟩ := ih Q.toNat hQlt Q rfl hQ0
    refine ⟨h1, ?_, h3⟩
    rw [pow_succ, Nat.mul_assoc, Nat.mul_comm (p.toNat) _, ← Nat.mul_assoc, ← h2]
    omega
  · simp only [hr, ↓reduceIte]
    refine ⟨hn, by simp, ?_⟩
    intro hdvd
    have hrN : r.toNat ≠ 0 := fun hz => hr (UInt64.eq_of_toNat_eq hz)
    have hmod : n.toNat % p.toNat = r.toNat := by
      rw [← hdm.1, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hdm.2]
    rw [Nat.dvd_iff_mod_eq_zero, hmod] at hdvd
    exact hrN hdvd

/-- For a prime `p`, `countFactor` returns the `p`-adic valuation and erases `p` from the
factorization. -/
theorem countFactor_factorization (p : UInt64) (hp : Nat.Prime p.toNat) (n : AzNat)
    (hn : n ≠ 0) :
    (countFactor p n).1 = n.toNat.factorization p.toNat ∧
    (countFactor p n).2.toNat.factorization = n.toNat.factorization.erase p.toNat := by
  have hp2 : 2 ≤ p.toNat := hp.two_le
  obtain ⟨hm, hval, hndvd⟩ := countFactor_spec p hp2 n hn
  set c := (countFactor p n).1
  set m := (countFactor p n).2.toNat with hm_def
  have hmN : m ≠ 0 := fun hz => hm (AzNat.toNat_injective (by rw [← hm_def, hz]; rfl))
  have hfact : n.toNat.factorization = Finsupp.single p.toNat c + m.factorization := by
    rw [hval, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hmN, hp.factorization_pow]
  have hmp : m.factorization p.toNat = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
  constructor
  · rw [hfact, Finsupp.add_apply, Finsupp.single_eq_same, hmp, Nat.add_zero]
  · ext r
    by_cases hr : r = p.toNat
    · rw [hr, Finsupp.erase_same, hmp]
    · rw [Finsupp.erase_ne hr, hfact, Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_right (Ne.symm hr), Nat.zero_add]

/-! ### The table -/

/-- Every table entry is a prime power with positive exponent, the primes are distinct, and
the entries multiply to the base. -/
theorem basePrimeFactors_spec (B : ℕ) (h2 : 2 ≤ B) (h36 : B ≤ 36) :
    (∀ pm ∈ basePrimeFactors B, Nat.Prime pm.1.toNat ∧ 0 < pm.2) ∧
    ((basePrimeFactors B).map (fun pm : UInt64 × Nat => pm.1.toNat)).Nodup ∧
    ((basePrimeFactors B).map (fun pm : UInt64 × Nat => pm.1.toNat ^ pm.2)).prod = B := by
  interval_cases B <;> simp [basePrimeFactors] <;> norm_num

/-- The multiplicity of `r` recorded by the table (`m` if `(r, m)` is an entry, else `0`). -/
def tableMult : List (UInt64 × Nat) → ℕ → ℕ
  | [], _ => 0
  | (p, m) :: t, r => (if p.toNat = r then m else 0) + tableMult t r

/-- The factorization of a table product is `tableMult`. -/
theorem factorization_tableProd (T : List (UInt64 × Nat))
    (hT : ∀ pm ∈ T, Nat.Prime pm.1.toNat ∧ 0 < pm.2) (r : ℕ) :
    ((T.map (fun pm : UInt64 × Nat => pm.1.toNat ^ pm.2)).prod).factorization r = tableMult T r := by
  induction T with
  | nil => simp [tableMult]
  | cons pm t ih =>
    have hpm := hT pm (List.mem_cons_self ..)
    have ht : ∀ pm ∈ t, Nat.Prime pm.1.toNat ∧ 0 < pm.2 :=
      fun x hx => hT x (List.mem_cons_of_mem _ hx)
    have hprod_ne : (t.map (fun pm : UInt64 × Nat => pm.1.toNat ^ pm.2)).prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, hy0⟩ := hx
      exact pow_ne_zero _ (ht y hy).1.ne_zero hy0
    rw [List.map_cons, List.prod_cons,
      Nat.factorization_mul (pow_ne_zero _ hpm.1.ne_zero) hprod_ne, Finsupp.add_apply,
      hpm.1.factorization_pow, Finsupp.single_apply, ih ht, tableMult]

/-- `tableMult` vanishes off the table's primes. -/
theorem tableMult_of_not_mem (T : List (UInt64 × Nat)) (r : ℕ)
    (hr : ∀ pm ∈ T, pm.1.toNat ≠ r) : tableMult T r = 0 := by
  induction T with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨xp, xm⟩ := x
    rw [tableMult, ite_eq_right (hr (xp, xm) (List.mem_cons_self ..)), Nat.zero_add]
    exact ih fun pm hpm => hr pm (List.mem_cons_of_mem _ hpm)

/-- With distinct primes, `tableMult` reads off an entry's exponent. -/
theorem tableMult_of_mem (T : List (UInt64 × Nat)) (hnd : (T.map (fun pm : UInt64 × Nat => pm.1.toNat)).Nodup)
    (pm : UInt64 × Nat) (hpm : pm ∈ T) : tableMult T pm.1.toNat = pm.2 := by
  induction T with
  | nil => simp at hpm
  | cons x t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hpm with rfl | hmem
    · obtain ⟨xp, xm⟩ := pm
      rw [tableMult, ite_eq_left rfl, tableMult_of_not_mem t _ (fun y hy heq => hnd.1 (by
        rw [← heq]; exact List.mem_map_of_mem hy))]
      rfl
    · obtain ⟨xp, xm⟩ := x
      have hne : xp.toNat ≠ pm.1.toNat := by
        intro h; apply hnd.1; rw [h]; exact List.mem_map_of_mem hmem
      rw [tableMult, ite_eq_right hne, Nat.zero_add]
      exact ih hnd.2 hmem

/-! ### The fold -/

/-- The fold step of `lengthAfterPoint`. -/
def lapStep (acc : Nat × AzNat) (pm : UInt64 × Nat) : Nat × AzNat :=
  let s := countFactor pm.1 acc.2
  (max acc.1 ((s.1 + pm.2 - 1) / pm.2), s.2)

/-- `⌈c / m⌉ ≤ L ↔ c ≤ m · L` for `0 < m`. -/
private lemma ceilDiv_le_iff (c m L : ℕ) (hm : 0 < m) :
    (c + m - 1) / m ≤ L ↔ c ≤ m * L := by
  rw [Nat.div_le_iff_le_mul_add_pred hm]
  omega

/-- Invariant of the fold over a prefix `T'` of the table (whose primes are distinct and
disjoint from the remaining entries): the remainder has the processed primes erased from the
denominator's factorization, and the length bound is the conjunction of the per-prime
bounds. -/
theorem foldl_lapStep_spec (D : ℕ) :
    ∀ (T : List (UInt64 × Nat)) (T' : List (UInt64 × Nat)) (acc : Nat × AzNat),
      (∀ pm ∈ T' ++ T, Nat.Prime pm.1.toNat ∧ 0 < pm.2) →
      ((T' ++ T).map (fun pm : UInt64 × Nat => pm.1.toNat)).Nodup →
      acc.2 ≠ 0 →
      (∀ r, acc.2.toNat.factorization r =
        if ∃ pm ∈ T', pm.1.toNat = r then 0 else D.factorization r) →
      (∀ L, acc.1 ≤ L ↔ ∀ pm ∈ T', D.factorization pm.1.toNat ≤ pm.2 * L) →
      let res := T.foldl lapStep acc
      res.2 ≠ 0 ∧
      (∀ r, res.2.toNat.factorization r =
        if ∃ pm ∈ T' ++ T, pm.1.toNat = r then 0 else D.factorization r) ∧
      (∀ L, res.1 ≤ L ↔ ∀ pm ∈ T' ++ T, D.factorization pm.1.toNat ≤ pm.2 * L) := by
  intro T
  induction T with
  | nil =>
    intro T' acc _ _ h0 hfact hlen
    simp only [List.append_nil, List.foldl_nil]
    exact ⟨h0, hfact, hlen⟩
  | cons pm T ih =>
    intro T' acc hT hnd h0 hfact hlen
    have hpm := hT pm (by simp)
    have hT_shift : ∀ x ∈ (T' ++ [pm]) ++ T, Nat.Prime x.1.toNat ∧ 0 < x.2 := by
      intro x hx; apply hT; simpa [List.append_assoc] using hx
    have hnd_shift : (((T' ++ [pm]) ++ T).map (fun pm : UInt64 × Nat => pm.1.toNat)).Nodup := by
      simpa [List.append_assoc] using hnd
    -- `pm.1` has not been processed yet.
    have hnew : ∀ x ∈ T', x.1.toNat ≠ pm.1.toNat := by
      intro x hx heq
      rw [List.map_append, List.nodup_append] at hnd
      have h1 : x.1.toNat ∈ T'.map (fun pm : UInt64 × Nat => pm.1.toNat) := List.mem_map_of_mem hx
      have h2 : pm.1.toNat ∈ (pm :: T).map (fun pm : UInt64 × Nat => pm.1.toNat) := by simp
      exact hnd.2.2 _ h1 _ h2 heq
    obtain ⟨hc, hm⟩ := countFactor_factorization pm.1 hpm.1 acc.2 h0
    have hs0 : (countFactor pm.1 acc.2).2 ≠ 0 := (countFactor_spec pm.1 hpm.1.two_le acc.2 h0).1
    have hfact' : ∀ r, (lapStep acc pm).2.toNat.factorization r =
        if ∃ x ∈ T' ++ [pm], x.1.toNat = r then 0 else D.factorization r := by
      intro r
      show (countFactor pm.1 acc.2).2.toNat.factorization r = _
      rw [hm]
      by_cases hr : r = pm.1.toNat
      · rw [hr, Finsupp.erase_same]
        rw [ite_eq_left ⟨pm, by simp, rfl⟩]
      · rw [Finsupp.erase_ne hr, hfact r]
        by_cases hex : ∃ x ∈ T', x.1.toNat = r
        · rw [ite_eq_left hex, ite_eq_left]
          obtain ⟨x, hx, hxr⟩ := hex
          exact ⟨x, List.mem_append_left _ hx, hxr⟩
        · rw [ite_eq_right hex, ite_eq_right]
          rintro ⟨x, hx, hxr⟩
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hex ⟨x, hx', hxr⟩
          · rw [List.mem_singleton] at hx'
            subst hx'
            exact hr hxr.symm
    have hlen' : ∀ L, (lapStep acc pm).1 ≤ L ↔
        ∀ x ∈ T' ++ [pm], D.factorization x.1.toNat ≤ x.2 * L := by
      intro L
      show max acc.1 (((countFactor pm.1 acc.2).1 + pm.2 - 1) / pm.2) ≤ L ↔ _
      rw [max_le_iff, hlen L, ceilDiv_le_iff _ _ _ hpm.2, hc, hfact pm.1.toNat]
      rw [ite_eq_right (by rintro ⟨x, hx, hxr⟩; exact hnew x hx hxr)]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact h1 x hx'
        · rw [List.mem_singleton] at hx'; subst hx'; exact h2
      · intro h
        exact ⟨fun x hx => h x (List.mem_append_left _ hx), h pm (by simp)⟩
    have := ih (T' ++ [pm]) (lapStep acc pm) hT_shift hnd_shift hs0 hfact' hlen'
    simp only [List.append_assoc, List.singleton_append] at this
    rw [List.foldl_cons]
    exact this

/-! ### `lengthAfterPoint` -/

/-- Divisibility of the denominator by a power of the base, prime by prime. -/
theorem dvd_pow_iff (D B L : ℕ) (hD : D ≠ 0) (hB : B ≠ 0) :
    D ∣ B ^ L ↔ ∀ r, D.factorization r ≤ L * B.factorization r := by
  rw [← Nat.factorization_le_iff_dvd hD (pow_ne_zero _ hB), Nat.factorization_pow,
    Finsupp.le_def]
  simp only [Finsupp.smul_apply, smul_eq_mul]

/-- The core of both specifications: `lengthAfterPoint b q = some L` iff `L` is the least
exponent with `q.den ∣ b^L`, and `= none` iff there is none. -/
theorem lengthAfterPoint_spec (b : UInt64) (hb : 2 ≤ b.toNat ∧ b.toNat ≤ 36) (q : AzRat) :
    (∀ L, lengthAfterPoint b q = some L ↔
      q.den.toNat ∣ b.toNat ^ L ∧ ∀ L' < L, ¬ q.den.toNat ∣ b.toNat ^ L') ∧
    (lengthAfterPoint b q = none ↔ ∀ L, ¬ q.den.toNat ∣ b.toNat ^ L) := by
  obtain ⟨hT, hnd, hprod⟩ := basePrimeFactors_spec b.toNat hb.1 hb.2
  set T := basePrimeFactors b.toNat with hT_def
  set D := q.den.toNat with hD_def
  have hD : D ≠ 0 := fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hB : b.toNat ≠ 0 := by omega
  have hden0 : q.den ≠ 0 := q.den_nz
  have hfold := foldl_lapStep_spec D T [] (0, q.den) (by simpa using hT) (by simpa using hnd)
    hden0 (fun r => by rw [ite_eq_right (by simp)]) (fun L => by simp)
  simp only [List.nil_append] at hfold
  obtain ⟨hres0, hresfact, hreslen⟩ := hfold
  set res := T.foldl lapStep (0, q.den) with hres_def
  -- `b.factorization = tableMult T`.
  have hBfact : ∀ r, b.toNat.factorization r = tableMult T r := by
    intro r; rw [← hprod]; exact factorization_tableProd T hT r
  -- The two halves of divisibility.
  have hkey : ∀ L, D ∣ b.toNat ^ L ↔ (res.1 ≤ L ∧ res.2 = 1) := by
    intro L
    rw [dvd_pow_iff D _ L hD hB, hreslen L]
    have hres1 : res.2 = 1 ↔ ∀ r, (¬ ∃ pm ∈ T, pm.1.toNat = r) → D.factorization r = 0 := by
      constructor
      · intro h1 r hr
        have := hresfact r
        rw [ite_eq_right hr] at this
        rw [← this, h1]
        simp
      · intro h
        have hz : res.2.toNat.factorization = 0 := by
          ext r
          rw [hresfact r]
          split_ifs with hex
          · rfl
          · exact h r hex
        rcases (Nat.factorization_eq_zero_iff' _).mp hz with h0 | h1
        · exact absurd (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm)) hres0
        · exact AzNat.toNat_injective (h1.trans AzNat.toNat_one.symm)
    rw [hres1]
    constructor
    · intro h
      refine ⟨fun pm hpm => ?_, fun r hr => ?_⟩
      · have := h pm.1.toNat
        rwa [hBfact, tableMult_of_mem T hnd pm hpm, Nat.mul_comm] at this
      · have := h r
        rwa [hBfact, tableMult_of_not_mem T r (fun pm hpm heq => hr ⟨pm, hpm, heq⟩),
          Nat.mul_zero, Nat.le_zero] at this
    · rintro ⟨h1, h2⟩ r
      rw [hBfact]
      by_cases hex : ∃ pm ∈ T, pm.1.toNat = r
      · obtain ⟨pm, hpm, rfl⟩ := hex
        rw [tableMult_of_mem T hnd pm hpm, Nat.mul_comm]
        exact h1 pm hpm
      · rw [tableMult_of_not_mem T r (fun pm hpm heq => hex ⟨pm, hpm, heq⟩), Nat.mul_zero,
          h2 r hex]
  -- Unfold `lengthAfterPoint`.
  have hunfold : lengthAfterPoint b q = if res.2 = 1 then some res.1 else none := by
    unfold lengthAfterPoint
    rw [ite_eq_left hb]
    rfl
  rw [hunfold]
  constructor
  · intro L
    by_cases h1 : res.2 = 1
    · rw [ite_eq_left h1]
      constructor
      · intro hL
        have hL' : res.1 = L := Option.some.inj hL
        refine ⟨(hkey L).mpr ⟨hL' ▸ Nat.le_refl _, h1⟩, fun L' hL'' hdvd => ?_⟩
        have := ((hkey L').mp hdvd).1
        omega
      · rintro ⟨hdvd, hmin⟩
        have hle := ((hkey L).mp hdvd).1
        congr
        by_contra hne
        have hlt : res.1 < L := lt_of_le_of_ne hle hne
        exact hmin res.1 hlt ((hkey res.1).mpr ⟨Nat.le_refl _, h1⟩)
    · rw [ite_eq_right h1]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨hdvd, _⟩
        exact absurd ((hkey L).mp hdvd).2 h1
  · by_cases h1 : res.2 = 1
    · rw [ite_eq_left h1]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h
        exact absurd ((hkey res.1).mpr ⟨Nat.le_refl _, h1⟩) (h res.1)
    · rw [ite_eq_right h1]
      simp only [true_iff]
      intro L hdvd
      exact h1 ((hkey L).mp hdvd).2

/-- `lengthAfterPoint b q = some L` iff `L` is the least exponent with `q.den ∣ b^L`. -/
theorem lengthAfterPoint_some_iff (b : UInt64) (hb : 2 ≤ b.toNat ∧ b.toNat ≤ 36) (q : AzRat)
    (L : ℕ) :
    lengthAfterPoint b q = some L ↔
      q.den.toNat ∣ b.toNat ^ L ∧ ∀ L' < L, ¬ q.den.toNat ∣ b.toNat ^ L' :=
  (lengthAfterPoint_spec b hb q).1 L

/-- `lengthAfterPoint b q = none` iff no power of `b` is divisible by `q.den` (the base-`b`
expansion of `q` does not terminate). -/
theorem lengthAfterPoint_none_iff (b : UInt64) (hb : 2 ≤ b.toNat ∧ b.toNat ≤ 36) (q : AzRat) :
    lengthAfterPoint b q = none ↔ ∀ L, ¬ q.den.toNat ∣ b.toNat ^ L :=
  (lengthAfterPoint_spec b hb q).2

end Azurite.AzRat
