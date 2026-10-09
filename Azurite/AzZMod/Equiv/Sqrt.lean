/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Sqrt
import Azurite.AzZMod.Field
import Azurite.AzZMod.Equiv.Field
import Azurite.AzZMod.Equiv.Pow
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzNat.Equiv.JacobiSym
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
## Correctness of `AzZMod.sqrt?`

* `sqrt?_some`: a returned root squares to the input, for every modulus (the candidate is
  verified by a squaring), and `sqrt?_some_le`: it is the smaller of the two residues.
* `sqrt?_isSome_iff`: for a prime modulus a root is returned exactly when the input is a square.

Completeness works in the field `AzZMod p` (`instField`) with Euler's criterion imported through
`toZMod`.  The Tonelli–Shanks loop keeps `R² = a t`, `t^(2^(M−1)) = 1`, `c^(2^(M−1)) = −1`
(`tonelliShanksLoop_spec`); the least exponent search is `squareUntilOne_some`/`_none`; the
non-residue search terminates on an odd prime because a non-square exists
(`FiniteField.exists_nonsquare`) and the Jacobi symbol detects it (`jacobi_eq_neg_one_iff`).

The invariants are those stated in the Wikipedia article *Tonelli–Shanks algorithm*
(<https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm>); Atkin's identity
`i² = (2a)^((p−1)/2) = −1` follows the description in Rotaru and Iftene, *A complete
generalization of Atkin's square root algorithm* (Fundamenta Informaticae 125, 2013).  Full
references are in `AzZMod/Sqrt.lean`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- `toZMod` respects the monoid power (the `CommRing`'s `npow`). -/
theorem toZMod_npow [NeZero m.toNat] (a : AzZMod m) (n : ℕ) : toZMod (a ^ n) = toZMod a ^ n :=
  map_pow toZModRingHom a n

/-! ### Soundness -/

theorem canonicalRoot_mul_self [NeZero m.toNat] (r : AzZMod m) :
    canonicalRoot r * canonicalRoot r = r * r := by
  unfold canonicalRoot
  split_ifs
  · rfl
  · exact neg_mul_neg r r

theorem canonicalRoot_le [NeZero m.toNat] (r : AzZMod m) :
    (canonicalRoot r).val ≤ (-canonicalRoot r).val := by
  unfold canonicalRoot
  split_ifs with h
  · exact h
  · rw [neg_neg]; exact (not_le.mp h).le

/-- **Soundness**: a returned root squares to the input, for every modulus. -/
theorem sqrt?_some [NeZero m.toNat] {a r : AzZMod m} (h : sqrt? a = some r) : r * r = a := by
  unfold sqrt? at h
  split_ifs at h with ha
  · obtain rfl := Option.some.inj h
    rw [ha, mul_zero]
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨r', _, hr'⟩ := h
    split_ifs at hr' with hsq
    obtain rfl := Option.some.inj hr'
    rw [canonicalRoot_mul_self, ← Azurite.Square.square_eq, hsq]

/-- A returned root is the smaller of the two residues. -/
theorem sqrt?_some_le [NeZero m.toNat] {a r : AzZMod m} (h : sqrt? a = some r) :
    r.val ≤ (-r).val := by
  unfold sqrt? at h
  split_ifs at h with ha
  · obtain rfl := Option.some.inj h
    rw [neg_zero]
  · rw [Option.bind_eq_some_iff] at h
    obtain ⟨r', _, hr'⟩ := h
    split_ifs at hr'
    obtain rfl := Option.some.inj hr'
    exact canonicalRoot_le r'

/-! ### The Tonelli–Shanks loop -/

theorem squarePow2_eq [NeZero m.toNat] (c : AzZMod m) : ∀ k, squarePow2 c k = c ^ (2 ^ k) := by
  intro k
  induction k generalizing c with
  | zero => simp [squarePow2]
  | succ k ih =>
    rw [squarePow2, ih, Azurite.Square.square_eq, ← sq, ← pow_mul, pow_succ, mul_comm]

theorem squareUntilOne_some [NeZero m.toNat] : ∀ (fuel : ℕ) (t : AzZMod m) (i : ℕ),
    squareUntilOne fuel t = some i →
      1 ≤ i ∧ i ≤ fuel ∧ t ^ (2 ^ i) = 1 ∧ ∀ j, 1 ≤ j → j < i → t ^ (2 ^ j) ≠ 1 := by
  intro fuel
  induction fuel with
  | zero => intro t i h; simp [squareUntilOne] at h
  | succ fuel ih =>
    intro t i h
    unfold squareUntilOne at h
    dsimp only at h
    rw [Azurite.Square.square_eq] at h
    split_ifs at h with h1
    · obtain rfl := Option.some.inj h
      refine ⟨le_rfl, by omega, by rw [pow_one, sq]; exact h1, fun j hj hj' => by omega⟩
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨i', hi', rfl⟩ := h
      obtain ⟨h1', h2', h3', h4'⟩ := ih _ _ hi'
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [pow_succ, mul_comm, pow_mul, sq]; exact h3'
      · intro j hj hji
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [pow_succ, mul_comm, pow_mul, sq]
        by_cases hj0 : j' = 0
        · subst hj0; simpa using h1
        · exact h4' j' (by omega) (by omega)

theorem squareUntilOne_none [NeZero m.toNat] : ∀ (fuel : ℕ) (t : AzZMod m),
    squareUntilOne fuel t = none → ∀ j, 1 ≤ j → j ≤ fuel → t ^ (2 ^ j) ≠ 1 := by
  intro fuel
  induction fuel with
  | zero => intro t _ j hj hj'; omega
  | succ fuel ih =>
    intro t h j hj hjf
    unfold squareUntilOne at h
    dsimp only at h
    rw [Azurite.Square.square_eq] at h
    split_ifs at h with h1
    rw [Option.map_eq_none_iff] at h
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, mul_comm, pow_mul, sq]
    by_cases hj0 : j' = 0
    · subst hj0; simpa using h1
    · exact ih _ h j' (by omega) (by omega)

/-- In a field, a square root of one other than one is minus one. -/
theorem eq_neg_one_of_mul_self [Fact (Nat.Prime m.toNat)] {x : AzZMod m} (h : x * x = 1)
    (h1 : x ≠ 1) : x = -1 := by
  rcases mul_self_eq_one_iff.mp h with h | h
  · exact absurd h h1
  · exact h

theorem tonelliShanksLoop_spec [Fact (Nat.Prime m.toNat)] (a : AzZMod m) :
    ∀ (fuel M : ℕ) (c t R : AzZMod m), 1 ≤ M → M ≤ fuel → R * R = a * t →
      t ^ (2 ^ (M - 1)) = 1 → c ^ (2 ^ (M - 1)) = -1 →
      ∃ r, tonelliShanksLoop fuel M c t R = some r ∧ r * r = a := by
  intro fuel
  induction fuel with
  | zero => intro M c t R hM hMf; omega
  | succ fuel ih =>
    intro M c t R hM hMf hR ht hc
    rw [tonelliShanksLoop]
    dsimp only
    by_cases ht1 : t = 1
    · rw [ite_eq_left ht1]
      exact ⟨R, rfl, by rw [hR, ht1, mul_one]⟩
    rw [ite_eq_right ht1]
    have hM2 : 2 ≤ M := by
      by_contra hlt
      have hM1 : M = 1 := by omega
      rw [hM1] at ht
      simp at ht
      exact ht1 ht
    split
    · rename_i hnone
      exact absurd ht (squareUntilOne_none _ _ hnone (M - 1) (by omega) le_rfl)
    · rename_i i hi
      obtain ⟨hi1, hiM, hti, hmin⟩ := squareUntilOne_some _ _ _ hi
      -- `t^(2^(i-1)) = -1`
      have htm : t ^ (2 ^ (i - 1)) = -1 := by
        apply eq_neg_one_of_mul_self
        · rw [← sq, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hi1]; exact hti
        · by_cases hi1' : i = 1
          · subst hi1'; simpa using ht1
          · exact hmin (i - 1) (by omega) (by omega)
      -- `b² = c^(2^(M-i))` and `(b²)^(2^(i-1)) = c^(2^(M-1)) = -1`
      have hb2 : Azurite.Square.square (squarePow2 c (M - i - 1)) = c ^ (2 ^ (M - i)) := by
        rw [Azurite.Square.square_eq, squarePow2_eq, ← sq, ← pow_mul, ← pow_succ,
          Nat.sub_add_cancel (by omega)]
      have hcpow : (c ^ (2 ^ (M - i))) ^ (2 ^ (i - 1)) = -1 := by
        rw [← pow_mul, ← pow_add, show M - i + (i - 1) = M - 1 by omega]; exact hc
      rw [hb2]
      apply ih i (c ^ (2 ^ (M - i))) (t * c ^ (2 ^ (M - i))) (R * squarePow2 c (M - i - 1))
        hi1 (by omega)
      · rw [mul_mul_mul_comm, hR, ← Azurite.Square.square_eq, hb2, mul_assoc]
      · rw [mul_pow, hcpow, htm, neg_one_mul, neg_neg]
      · exact hcpow

/-! ### The non-residue search -/

theorem findNonResidue_some {p : AzNat} : ∀ (n : ℕ) (z w : AzNat), p.toNat - z.toNat = n →
    findNonResidue p z = some w → w < p ∧ AzNat.jacobi w p = -1 := by
  intro n
  induction n with
  | zero =>
    intro z w hn h
    rw [findNonResidue] at h
    have : ¬ z < p := by rw [AzNat.lt_iff_toNat_lt]; omega
    rw [dite_eq_right this] at h
    cases h
  | succ n ih =>
    intro z w hn h
    rw [findNonResidue] at h
    have hlt : z < p := by rw [AzNat.lt_iff_toNat_lt]; omega
    rw [dite_eq_left hlt] at h
    split_ifs at h with hj
    · obtain rfl := Option.some.inj h
      exact ⟨hlt, hj⟩
    · exact ih (z + 1) w (by rw [AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl]; omega) h

/-- For an odd prime `p`, the Jacobi symbol is `−1` exactly at the non-squares. -/
theorem jacobi_eq_neg_one_iff {p : AzNat} [Fact (Nat.Prime p.toNat)] (hp2 : p.toNat ≠ 2)
    (z : AzNat) : AzNat.jacobi z p = -1 ↔ ¬ IsSquare (z.toNat : ZMod p.toNat) := by
  have hodd : p.toNat % 2 = 1 := by
    rcases (Fact.out : Nat.Prime p.toNat).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  rw [AzNat.jacobi_eq z p hodd, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff,
    Int.cast_natCast]

theorem findNonResidue_isSome {p : AzNat} [Fact (Nat.Prime p.toNat)] (hp2 : p.toNat ≠ 2) :
    (findNonResidue p (AzNat.ofNat 2)).isSome := by
  obtain ⟨w, hw⟩ := FiniteField.exists_nonsquare (F := ZMod p.toNat)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hwlt : w.val < p.toNat := ZMod.val_lt w
  have key : ∀ (n : ℕ) (z : AzNat), p.toNat - z.toNat = n → z.toNat ≤ w.val →
      (findNonResidue p z).isSome := by
    intro n
    induction n with
    | zero => intro z hn hz; omega
    | succ n ih =>
      intro z hn hz
      rw [findNonResidue]
      have hlt : z < p := by rw [AzNat.lt_iff_toNat_lt]; omega
      rw [dite_eq_left hlt]
      split_ifs with hj
      · rfl
      · have hne : z.toNat ≠ w.val := by
          intro heq
          apply hj
          rw [jacobi_eq_neg_one_iff hp2, heq, ZMod.natCast_zmod_val]
          exact hw
        exact ih (z + 1) (by rw [AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl]; omega)
          (by rw [AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl]; omega)
  have hw2 : 2 ≤ w.val := by
    by_contra hlt
    have hw' : w = ((w.val : ℕ) : ZMod p.toNat) := (ZMod.natCast_zmod_val w).symm
    rcases (show w.val = 0 ∨ w.val = 1 by omega) with h0 | h1
    · rw [h0] at hw'; apply hw; rw [hw', Nat.cast_zero]; exact IsSquare.zero
    · rw [h1] at hw'; apply hw; rw [hw', Nat.cast_one]; exact IsSquare.one
  exact key _ _ rfl (by rw [AzNat.toNat_ofNat]; omega)

/-! ### Completeness -/

/-- Euler's criterion, transported: a nonzero square has `a^(p/2) = 1`. -/
theorem pow_half_eq_one [Fact (Nat.Prime m.toNat)] {a : AzZMod m} (ha : a ≠ 0)
    (hsq : IsSquare (toZMod a)) : a ^ (m.toNat / 2) = 1 := by
  apply toZMod_injective
  rw [toZMod_npow, toZMod_one]
  have ha' : toZMod a ≠ 0 := fun h => ha (toZMod_injective (by rw [h, toZMod_zero]))
  exact (ZMod.euler_criterion m.toNat ha').mp hsq

/-- Euler's criterion, transported: a nonzero non-square has `a^(p/2) = −1`. -/
theorem pow_half_eq_neg_one [Fact (Nat.Prime m.toNat)] {a : AzZMod m}
    (hsq : ¬ IsSquare (toZMod a)) : a ^ (m.toNat / 2) = -1 := by
  have hp := (Fact.out : Nat.Prime m.toNat)
  have ha' : toZMod a ≠ 0 := fun h => hsq (by rw [h]; exact IsSquare.zero)
  have ha : a ≠ 0 := fun h => ha' (by rw [h, toZMod_zero])
  apply eq_neg_one_of_mul_self
  · rw [← sq, ← pow_mul]
    have hodd : m.toNat % 2 = 1 ∨ m.toNat = 2 := by
      rcases hp.eq_two_or_odd with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hodd with hodd | h2
    · rw [show m.toNat / 2 * 2 = m.toNat - 1 by omega]
      apply toZMod_injective
      rw [toZMod_npow, toZMod_one]
      exact ZMod.pow_card_sub_one_eq_one ha'
    · -- modulo `2` every element is a square
      exfalso
      apply hsq
      exact ⟨toZMod a, by rw [← sq, show (2 : ℕ) = m.toNat from h2.symm, ZMod.pow_card]⟩
  · intro h1
    apply hsq
    apply (ZMod.euler_criterion m.toNat ha').mpr
    have := congrArg toZMod h1
    rwa [toZMod_npow, toZMod_one] at this

theorem atkin_spec [Fact (Nat.Prime m.toNat)] (a : AzZMod m) (ha : a ≠ 0)
    (hsq : IsSquare (toZMod a)) (h5 : m.toNat % 8 = 5) : atkin a * atkin a = a := by
  have hp := (Fact.out : Nat.Prime m.toNat)
  have hp2 : m.toNat ≠ 2 := by omega
  -- `2` is a non-residue, so `2^(p/2) = −1`
  have h2 : (2 : AzZMod m) ^ (m.toNat / 2) = -1 := by
    apply pow_half_eq_neg_one
    have : toZMod (2 : AzZMod m) = (2 : ZMod m.toNat) := by
      show toZMod ((2 : ℕ) : AzZMod m) = _
      rw [toZMod_natCast]; push_cast; rfl
    rw [this, ZMod.exists_sq_eq_two_iff hp2]
    omega
  have ha2 := pow_half_eq_one ha hsq
  unfold atkin
  dsimp only
  rw [Azurite.Square.square_eq, powAzNat_eq_pow, AzNat.toNat_hShiftRight,
    Nat.shiftRight_eq_div_pow, AzNat.toNat_sub, AzNat.toNat_ofNat]
  set e := (m.toNat - 5) / 2 ^ 3 with he
  set v := (a + a) ^ e with hv
  set i := (a + a) * (v * v) with hi
  have hI2 : i * i = -1 := by
    have : i * i = (a + a) ^ (2 + 4 * e) := by
      rw [hi, hv, ← two_mul]; ring
    rw [this, show 2 + 4 * e = m.toNat / 2 by omega, ← two_mul, mul_pow, h2, ha2, mul_one]
  linear_combination (a * a * v * v - a) * hI2 + (a * i) * hi

theorem sqrtCandidate_spec [Fact (Nat.Prime m.toNat)] (a : AzZMod m) (ha : a ≠ 0)
    (hsq : IsSquare (toZMod a)) : ∃ r, sqrtCandidate a = some r ∧ r * r = a := by
  have hp := (Fact.out : Nat.Prime m.toNat)
  have hp2 := hp.two_le
  have ha2 := pow_half_eq_one ha hsq
  unfold sqrtCandidate
  split_ifs with heven h3 h5
  · -- `p = 2`: every residue is its own root
    refine ⟨a, rfl, ?_⟩
    have h2 : m.toNat = 2 := hp.even_iff.mp ((AzNat.isEven_iff m).mp heven)
    apply toZMod_injective
    rw [toZMod_mul, ← sq, show (2 : ℕ) = m.toNat from h2.symm]
    exact ZMod.pow_card _
  · -- `p ≡ 3 (mod 4)`
    have h3' : m.toNat % 4 = 3 := by
      have := congrArg AzNat.toNat h3
      rwa [AzNat.toNat_modPow2, AzNat.toNat_ofNat] at this
    refine ⟨_, rfl, ?_⟩
    rw [powAzNat_eq_pow, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, AzNat.toNat_add,
      show (1 : AzNat).toNat = 1 from rfl, ← sq, ← pow_mul,
      show (m.toNat + 1) / 2 ^ 2 * 2 = m.toNat / 2 + 1 by omega, pow_succ, ha2, one_mul]
  · -- `p ≡ 5 (mod 8)`
    have h5' : m.toNat % 8 = 5 := by
      have := congrArg AzNat.toNat h5
      rwa [AzNat.toNat_modPow2, AzNat.toNat_ofNat] at this
    exact ⟨_, rfl, atkin_spec a ha hsq h5'⟩
  · -- Tonelli–Shanks
    have hodd : m.toNat % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd ((AzNat.isEven_iff m).mpr (by rw [h]; exact even_two)) heven
      · exact h
    have hp2' : m.toNat ≠ 2 := by omega
    unfold tonelliShanks
    dsimp only
    have hne : m - 1 ≠ 0 := fun h => by
      have := congrArg AzNat.toNat h
      rw [AzNat.toNat_sub, show (1 : AzNat).toNat = 1 from rfl, AzNat.toNat_zero] at this
      omega
    rw [AzNat.trailingZeros_eq_padicValNat _ hne]
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (findNonResidue_isSome (p := m) hp2')
    rw [hz]
    dsimp only
    obtain ⟨_, hzj⟩ := findNonResidue_some _ _ _ rfl hz
    have hzns : ¬ IsSquare (toZMod (ofAzNat m z)) := by
      rw [toZMod_ofAzNat]; exact (jacobi_eq_neg_one_iff hp2' z).mp hzj
    -- the arithmetic of `p − 1 = 2^s q`
    set s := padicValNat 2 (m - 1).toNat with hs
    have hpm1 : (m - 1).toNat = m.toNat - 1 := by
      rw [AzNat.toNat_sub]; rfl
    have hq : ((m - 1) >>> s).toNat = (m.toNat - 1) / 2 ^ s := by
      rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, hpm1]
    have hdvd : 2 ^ s ∣ m.toNat - 1 := by rw [hs, hpm1]; exact pow_padicValNat_dvd
    have hs1 : 1 ≤ s := by
      rw [hs]
      apply one_le_padicValNat_of_dvd
      · rw [hpm1]; omega
      · rw [hpm1]; exact ⟨m.toNat / 2, by omega⟩
    have hqodd : Odd ((m.toNat - 1) / 2 ^ s) := by
      rw [hs, hpm1]
      exact Nat.odd_iff.mpr (AzNat.odd_div_pow_padicValNat_two (by omega))
    have hhalf : (m.toNat - 1) / 2 ^ s * 2 ^ (s - 1) = m.toNat / 2 := by
      obtain ⟨k, hk⟩ := hdvd
      have h2s : 2 ^ s = 2 ^ (s - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hs1]
      rw [hk, Nat.mul_div_cancel_left k (by positivity)]
      rw [h2s] at hk
      generalize 2 ^ (s - 1) = T at hk ⊢
      have h2' : m.toNat - 1 = 2 * (k * T) := by rw [hk]; ring
      generalize k * T = KT at h2' ⊢
      omega
    have hq1 : ((m - 1) >>> s + 1).toNat = (m.toNat - 1) / 2 ^ s + 1 := by
      rw [AzNat.toNat_add, hq]; rfl
    apply tonelliShanksLoop_spec a (s + 1) s _ _ _ hs1 (by omega)
    · -- `R² = a t`
      rw [powAzNat_eq_pow, powAzNat_eq_pow, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow,
        hq1, hq, ← sq, ← pow_mul]
      obtain ⟨k, hk⟩ := hqodd
      rw [show ((m.toNat - 1) / 2 ^ s + 1) / 2 ^ 1 * 2 = (m.toNat - 1) / 2 ^ s + 1 by omega,
        pow_succ, mul_comm]
    · -- `t^(2^(s-1)) = 1`
      rw [powAzNat_eq_pow, hq, ← pow_mul, hhalf]; exact ha2
    · -- `c^(2^(s-1)) = -1`
      rw [powAzNat_eq_pow, hq, ← pow_mul, hhalf]; exact pow_half_eq_neg_one hzns

/-- **Completeness**: for a prime modulus, a root is returned exactly when the input is a
square. -/
theorem sqrt?_isSome_iff [Fact (Nat.Prime m.toNat)] (a : AzZMod m) :
    (sqrt? a).isSome ↔ IsSquare (toZMod a) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    have := sqrt?_some hr
    exact ⟨toZMod r, by rw [← toZMod_mul, this]⟩
  · intro hsq
    unfold sqrt?
    split_ifs with ha
    · rfl
    · obtain ⟨r, hr, hrr⟩ := sqrtCandidate_spec a ha hsq
      rw [hr, Option.bind_some, ite_eq_left (by rw [Azurite.Square.square_eq]; exact hrr)]
      rfl

/-- For a prime modulus, `none` means the input is a non-square. -/
theorem sqrt?_eq_none_iff [Fact (Nat.Prime m.toNat)] (a : AzZMod m) :
    sqrt? a = none ↔ ¬ IsSquare (toZMod a) := by
  rw [← sqrt?_isSome_iff]
  cases sqrt? a <;> simp

end Azurite.AzZMod
