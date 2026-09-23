/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Square.ToomCook3
import Azurite.UInt64.Equiv.SqrtRem
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt

namespace Azurite.AzNat

/-!
Correctness of `basecaseSqrtRem` (MCA Algorithm 1.13 on `AzNat`).

Strategy:
  1. Show `(basecaseSqrtRem.loop m s fuel).toNat = Nat.sqrt.iter m.toNat s.toNat`
     for any `fuel ≥ s.toNat`.  Mathlib's `Nat.sqrt.iter` is the same
     Newton loop on `Nat`; we just translate each step's UInt-level
     operations through the existing `toNat_` lemmas.
  2. Establish that the initial guess satisfies the precondition for
     Mathlib's `Nat.sqrt.lt_iter_succ_sq` (`m < (u₀ + 1)²`), using
     `AzNat.size_toNat` + `Nat.lt_size_self`.
  3. Use `SqrtCore.iter_sq_le` (unconditional `s² ≤ m`) and
     `SqrtCore.lt_iter_succ_sq` to conclude both characterizing
     bounds; `Nat.eq_sqrt` then identifies the result with
     `Nat.sqrt m.toNat`.
-/

/- Local copies of core's `Nat.sqrt.iter` correctness lemmas, which became
`private` in `Init.Data.Nat.Sqrt.Lemmas` and are therefore no longer
referenceable by name. Copied verbatim from the core source (with references
fully qualified to avoid `open Nat` ambiguity against Mathlib). -/
namespace SqrtCore

private theorem AM_GM : {a b : Nat} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact Nat.zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

theorem iter_sq_le (n guess : Nat) : Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n := by
  unfold Nat.sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [next, dite_eq_left h] using iter_sq_le n next
  else
    apply Nat.mul_le_of_le_div
    simp only
    split <;> omega

theorem lt_iter_succ_sq (n guess : Nat) (hn : n < (guess + 1) * (guess + 1)) :
    n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) := by
  unfold Nat.sqrt.iter
  let m := (guess + n / guess) / 2
  dsimp
  split <;> rename_i h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dite_eq_left h] using lt_iter_succ_sq n m this
    refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : Nat) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← Nat.add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_theorem {a : Nat} : a ≤ 2 * ((a + 1) / 2) := by omega
    refine Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_theorem)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (Nat.lt_mul_div_succ _ (Nat.lt_of_le_of_lt (Nat.zero_le m) h)) _
  · exact hn

end SqrtCore

-- ─────────────────────────────────────────────────────────────────────────
-- AzNat ↔ Nat translations for the operations used inside the loop
-- ─────────────────────────────────────────────────────────────────────────

/-- `(s + m / s) >>> 1` at AzNat level matches `(s + m / s) / 2` at Nat level. -/
private theorem toNat_newton_step (m s : AzNat) :
    ((s + m / s) >>> 1).toNat = (s.toNat + m.toNat / s.toNat) / 2 := by
  rw [toNat_hShiftRight, toNat_add, toNat_div, Nat.shiftRight_eq_div_pow, pow_one]

/-- AzNat `≤` agrees with `Nat` `≤` via `toNat`. -/
private theorem ge_iff_toNat_ge (a b : AzNat) : a ≥ b ↔ a.toNat ≥ b.toNat := by
  show compare b a ≠ Ordering.gt ↔ b.toNat ≤ a.toNat
  rw [compare_eq_compare_toNat]
  exact Nat.compare_ne_gt

/-- AzNat `s = 0` iff `s.toNat = 0`. -/
private theorem eq_zero_iff_toNat_zero (s : AzNat) : s = 0 ↔ s.toNat = 0 := by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  apply toNat_injective
  rw [h]; rfl

-- ─────────────────────────────────────────────────────────────────────────
-- Initial guess properties
-- ─────────────────────────────────────────────────────────────────────────

/-- `initialGuess.toNat = 2^⌈b/2⌉` where `b = AzNat.size m`. -/
private theorem toNat_initialGuess (m : AzNat) :
    (basecaseSqrtRem.initialGuess m).toNat = 2 ^ ((m.size + 1) / 2) := by
  show ((1 : AzNat) <<< ((m.size + 1) / 2)).toNat = _
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq]
  show (1 : AzNat).toNat * 2 ^ ((m.size + 1) / 2) = _
  rw [show ((1 : AzNat).toNat = 1) from rfl, Nat.one_mul]

/-- The initial guess is at least `1`. -/
private theorem initialGuess_pos (m : AzNat) :
    0 < (basecaseSqrtRem.initialGuess m).toNat := by
  rw [toNat_initialGuess]
  exact Nat.two_pow_pos _

/-- `m.toNat < initialGuess².toNat` (strict upper bound on `√m`). -/
private theorem m_lt_initialGuess_sq (m : AzNat) :
    m.toNat < (basecaseSqrtRem.initialGuess m).toNat *
              (basecaseSqrtRem.initialGuess m).toNat := by
  rw [toNat_initialGuess, ← Nat.pow_add]
  have h_m_lt : m.toNat < 2 ^ m.toNat.size := Nat.lt_size_self _
  have h_size_eq : m.toNat.size = m.size := size_toNat m
  rw [h_size_eq] at h_m_lt
  have h_double : m.size ≤ (m.size + 1) / 2 + (m.size + 1) / 2 := by omega
  exact lt_of_lt_of_le h_m_lt (Nat.pow_le_pow_right (by decide) h_double)

/-- `m.toNat < (initialGuess + 1)²` — the precondition for the loop's
    upper-bound invariant. -/
private theorem m_lt_initialGuess_succ_sq (m : AzNat) :
    m.toNat < ((basecaseSqrtRem.initialGuess m).toNat + 1) *
              ((basecaseSqrtRem.initialGuess m).toNat + 1) := by
  apply lt_of_lt_of_le (m_lt_initialGuess_sq m)
  apply Nat.mul_le_mul <;> exact Nat.le_succ _

-- ─────────────────────────────────────────────────────────────────────────
-- Loop ↔ Mathlib iter equivalence
-- ─────────────────────────────────────────────────────────────────────────

/-- `basecaseSqrtRem.loop` matches `Nat.sqrt.iter` at the `toNat` level
    whenever fuel is sufficient (`s.toNat ≤ fuel`). -/
private theorem toNat_loop_eq_iter (m : AzNat) :
    ∀ (fuel : Nat) (s : AzNat), s.toNat ≤ fuel →
    (basecaseSqrtRem.loop m s fuel).toNat = Nat.sqrt.iter m.toNat s.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hfuel
    have hs_zero : s.toNat = 0 := Nat.le_zero.mp hfuel
    rw [basecaseSqrtRem.loop, hs_zero, Nat.sqrt.iter.eq_1]
    simp
  | succ fuel' ih =>
    intro s hfuel
    rw [basecaseSqrtRem.loop]
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      rw [(eq_zero_iff_toNat_zero s).mp hs0, Nat.sqrt.iter.eq_1]
      simp
    · rw [ite_eq_right hs0]
      have hs_pos : 0 < s.toNat := by
        have : s.toNat ≠ 0 := fun h => hs0 ((eq_zero_iff_toNat_zero s).mpr h)
        omega
      have hu_toNat : ((s + m / s) >>> 1).toNat = (s.toNat + m.toNat / s.toNat) / 2 :=
        toNat_newton_step m s
      by_cases huge : (s + m / s) >>> 1 ≥ s
      · rw [ite_eq_left huge, Nat.sqrt.iter.eq_1]
        have h_ge_nat : (s.toNat + m.toNat / s.toNat) / 2 ≥ s.toNat := by
          rw [← hu_toNat]; exact (ge_iff_toNat_ge _ _).mp huge
        have h_nlt : ¬ (s.toNat + m.toNat / s.toNat) / 2 < s.toNat := by omega
        rw [dite_eq_right h_nlt]
      · rw [ite_eq_right huge]
        rw [Nat.sqrt.iter.eq_1]
        have h_nge_nat : ¬ (s.toNat + m.toNat / s.toNat) / 2 ≥ s.toNat := by
          rw [← hu_toNat]; exact mt (ge_iff_toNat_ge _ _).mpr huge
        have h_lt_nat : (s.toNat + m.toNat / s.toNat) / 2 < s.toNat := by omega
        rw [dite_eq_left h_lt_nat]
        have h_rec : (basecaseSqrtRem.loop m ((s + m / s) >>> 1) fuel').toNat
                   = Nat.sqrt.iter m.toNat ((s + m / s) >>> 1).toNat :=
          ih _ (by rw [hu_toNat]; omega)
        rw [h_rec, hu_toNat]

-- ─────────────────────────────────────────────────────────────────────────
-- Main correctness
-- ─────────────────────────────────────────────────────────────────────────

private theorem toNat_zero_of_size_zero (m : AzNat) (hm : m.limbs.size = 0) :
    m.toNat = 0 := by
  show toNatLimbsList _ = 0
  rw [List.length_eq_zero_iff.mp hm]; rfl

/-- `basecaseSqrt m = Nat.sqrt m.toNat`. -/
@[simp] theorem toNat_basecaseSqrt (m : AzNat) :
    (basecaseSqrt m).toNat = Nat.sqrt m.toNat := by
  unfold basecaseSqrt
  by_cases hm0 : m.limbs.size = 0
  · rw [ite_eq_left hm0, toNat_zero_of_size_zero m hm0]; rfl
  · rw [ite_eq_right hm0]
    by_cases hm1 : m.limbs.size = 1
    · -- Single-limb: delegated to UInt64.sqrt.
      rw [dite_eq_left hm1]
      show (Azurite.UInt64.sqrt _).toAzNat.toNat = _
      rw [_root_.UInt64.toNat_toAzNat, Azurite.UInt64.toNat_sqrt]
      rw [toNat_of_size_one m hm1]
    · -- Multi-limb: Newton iteration.
      rw [dite_eq_right hm1]
      set u₀ := basecaseSqrtRem.initialGuess m
      set fuel := (1 : Nat) <<< ((m.size + 1) / 2) + 1
      show (basecaseSqrtRem.loop m u₀ fuel).toNat = _
      have h_fuel : u₀.toNat ≤ fuel := by
        show u₀.toNat ≤ (1 : Nat) <<< ((m.size + 1) / 2) + 1
        rw [toNat_initialGuess, Nat.shiftLeft_eq, Nat.one_mul]
        omega
      rw [toNat_loop_eq_iter m fuel u₀ h_fuel]
      have h_sq_le : Nat.sqrt.iter m.toNat u₀.toNat *
                     Nat.sqrt.iter m.toNat u₀.toNat ≤ m.toNat :=
        SqrtCore.iter_sq_le _ _
      have h_succ_sq : m.toNat < (Nat.sqrt.iter m.toNat u₀.toNat + 1) *
                                 (Nat.sqrt.iter m.toNat u₀.toNat + 1) :=
        SqrtCore.lt_iter_succ_sq m.toNat u₀.toNat (m_lt_initialGuess_succ_sq m)
      exact Nat.eq_sqrt.mpr ⟨h_sq_le, h_succ_sq⟩

/-- The sqrt component of `basecaseSqrtRem m` equals `Nat.sqrt m.toNat`. -/
@[simp] theorem toNat_basecaseSqrtRem_fst (m : AzNat) :
    (basecaseSqrtRem m).1.toNat = Nat.sqrt m.toNat := toNat_basecaseSqrt m

/-- The remainder component of `basecaseSqrtRem m` equals `m − s²` where
    `s = ⌊√m⌋`. -/
@[simp] theorem toNat_basecaseSqrtRem_snd (m : AzNat) :
    (basecaseSqrtRem m).2.toNat = m.toNat - Nat.sqrt m.toNat * Nat.sqrt m.toNat := by
  show (m - (basecaseSqrt m).square).toNat = _
  rw [toNat_sub, toNat_square, Nat.pow_two, toNat_basecaseSqrt]

-- ─────────────────────────────────────────────────────────────────────────
-- D&C `sqrtRem` correctness
-- ─────────────────────────────────────────────────────────────────────────

/-- `(ofLimbs (a.extract lo (lo + len))).toNat = sliceVal a lo len`. -/
private theorem toNat_ofLimbs_extract (a : Array UInt64) (lo len : Nat) :
    (ofLimbs (a.extract lo (lo + len))).toNat = sliceVal a lo len := by
  rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop]
  show toNatLimbsList ((a.toList.drop lo).take (lo + len - lo)) = _
  rw [Nat.add_sub_cancel_left]

/-- Value of a single-limb slice is the limb's `toNat`. -/
private theorem sliceVal_one (a : Array UInt64) (lo : Nat) (h : lo < a.size) :
    sliceVal a lo 1 = (a[lo]'h).toNat := by
  unfold sliceVal
  have h_take : (a.toList.drop lo).take 1 = [a.toList[lo]'(by rw [Array.length_toList]; omega)] := by
    rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; omega)]
    simp
  rw [h_take, Array.getElem_toList]
  simp [toNatLimbsList]

/-- Lower bound on `sliceVal`, stated in the `len = m + 1` form to
    keep the index expression `lo + m` Nat-syntactically simple
    (avoiding the dependent-`getElem` headache of `lo + len − 1`). -/
private theorem sliceVal_lower_bound_succ (a : Array UInt64) (lo m : Nat)
    (hbound : lo + m + 1 ≤ a.size)
    (h_top : (a[lo + m]'(by omega)) ≠ 0) :
    2 ^ (64 * m) ≤ sliceVal a lo (m + 1) := by
  rw [sliceVal_split a lo (m + 1) m (by omega) hbound]
  rw [show m + 1 - m = 1 from by omega]
  rw [sliceVal_one a (lo + m) (by omega)]
  have h_top_pos : 1 ≤ (a[lo + m]'(by omega)).toNat := by
    rcases Nat.eq_zero_or_pos (a[lo + m]'(by omega)).toNat with hz | hp
    · exfalso; apply h_top
      exact _root_.UInt64.eq_of_toNat_eq (by rw [hz]; rfl)
    · exact hp
  have h_mul : 2 ^ (64 * m) ≤ (a[lo + m]'(by omega)).toNat * 2 ^ (64 * m) := by
    have := Nat.mul_le_mul_right (2 ^ (64 * m)) h_top_pos
    linarith
  omega

/-- The polynomial identity at the heart of MCA Algorithm 1.12.  Given
    the IH on the top half (`T = S'² + R'`) and the divmod step
    (`R' · B + A₁ = Q · (2 S') + U`), the input `m` decomposes as
    `m + Q² = S² + (U · B + A₀)`, where `B = β^ℓ` and `S = S' · B + Q`. -/
private theorem mca_1_12_eq (T R' Q U S' A₁ A₀ B : Nat)
    (h_top : T = S' * S' + R')
    (h_divmod : R' * B + A₁ = Q * (2 * S') + U) :
    T * B * B + A₁ * B + A₀ + Q * Q
      = (S' * B + Q) * (S' * B + Q) + (U * B + A₀) := by
  have hstep :
      (S' * S' + R') * B * B + A₁ * B + A₀ + Q * Q
        = S' * S' * B * B + (R' * B + A₁) * B + A₀ + Q * Q := by ring
  rw [h_top, hstep, h_divmod]; ring

/-- Case 1 (no adjustment) bound: when `Y ≥ Q²`, the residual
    `r = Y - Q²` satisfies `r ≤ 2 S` (= `2 (S' B + Q)`).

    Direct from `Y = U B + A₀` with `U < 2 S'` and `A₀ < B`. -/
private theorem mca_1_12_bound_no_adjust (S' Q U A₀ B : Nat)
    (h_U_lt : U < 2 * S') (h_A₀_lt : A₀ < B) :
    U * B + A₀ ≤ 2 * (S' * B + Q) := by
  have h_le : U + 1 ≤ 2 * S' := h_U_lt
  have h_mul : (U + 1) * B ≤ 2 * S' * B := Nat.mul_le_mul_right B h_le
  have h1 : U * B + B ≤ 2 * S' * B := by
    calc U * B + B = (U + 1) * B := by ring
      _ ≤ 2 * S' * B := h_mul
  have h2 : U * B + A₀ < 2 * S' * B := by
    calc U * B + A₀ < U * B + B := by omega
      _ ≤ 2 * S' * B := h1
  have h3 : 2 * S' * B + 2 * Q = 2 * (S' * B + Q) := by ring
  omega

/-- Bound on the quotient `Q` when `S' ≥ B`.  From divmod with
    `R' ≤ 2 S'` and `A₁ < B`, we get `Q · 2S' ≤ 2 S' B + (B − 1) < (B + 1) · 2 S'`
    (using `2 S' − 1 ≥ B − 1`, i.e., `S' ≥ B/2`, satisfied by `S' ≥ B`),
    hence `Q ≤ B`. -/
private theorem mca_1_12_Q_le_B (S' R' Q U A₁ B : Nat)
    (h_S'_ge_B : S' ≥ B)
    (h_R'_le : R' ≤ 2 * S') (h_A₁_lt : A₁ < B)
    (h_divmod : R' * B + A₁ = Q * (2 * S') + U) :
    Q ≤ B := by
  -- Q * (2 * S') ≤ R' * B + A₁ ≤ 2 * S' * B + (B - 1) < (B + 1) * (2 * S').
  have h1 : Q * (2 * S') ≤ R' * B + A₁ := by omega
  have h2 : R' * B ≤ 2 * S' * B := Nat.mul_le_mul_right B h_R'_le
  have h3 : Q * (2 * S') ≤ 2 * S' * B + (B - 1) := by omega
  -- (B + 1) * (2 * S') = 2 * S' * B + 2 * S' and 2 * S' ≥ 2 * B ≥ B (for B ≥ 0).
  have h4 : (B + 1) * (2 * S') = 2 * S' * B + 2 * S' := by ring
  have h5 : Q * (2 * S') < (B + 1) * (2 * S') := by
    rw [h4]
    have h_2S'_ge : 2 * S' ≥ 2 * B := by omega
    omega
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h5)

/-- The Spec_aux predicate: `(s, r)` is the correct sqrtRem pair for
    the slice `a[lo, lo + len)`. -/
private def Spec_aux (a : Array UInt64) (lo len : Nat) (s r : AzNat) : Prop :=
  s.toNat * s.toNat + r.toNat = sliceVal a lo len ∧ r.toNat ≤ 2 * s.toNat

/-- The "slice has nonzero top limb" invariant, stated at the list level
    (no dependent `getElem` proof to carry). -/
private def SliceTopNonzero (a : Array UInt64) (lo len : Nat) : Prop :=
  ((a.toList.drop lo).take len).getLast? ≠ some 0

/-- Preservation: dropping the bottom `2ℓ` limbs leaves the top limb
    unchanged, so the invariant is preserved. -/
private theorem SliceTopNonzero_recurse (a : Array UInt64) (lo len ℓ : Nat)
    (h2ℓ : 2 * ℓ < len) (hbound : lo + len ≤ a.size)
    (h_inv : SliceTopNonzero a lo len) :
    SliceTopNonzero a (lo + 2 * ℓ) (len - 2 * ℓ) := by
  unfold SliceTopNonzero at h_inv ⊢
  set P := (a.toList.drop lo).take len with hP_def
  have h_len_a : a.toList.length = a.size := Array.length_toList
  have hP_len : P.length = len := by
    rw [hP_def, List.length_take, List.length_drop, h_len_a]; omega
  have hP_ne : P ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hP_len] at this; simp at this; omega
  -- New slice = P.drop (2 * ℓ).
  have h_eq : (a.toList.drop (lo + 2 * ℓ)).take (len - 2 * ℓ) = P.drop (2 * ℓ) := by
    rw [hP_def, List.drop_take, List.drop_drop]
  rw [h_eq]
  -- P.drop (2 * ℓ) is non-empty since 2 * ℓ < len = P.length.
  have h_drop_ne : P.drop (2 * ℓ) ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [List.length_drop, hP_len] at this
    simp at this; omega
  have h_eq_last : (P.drop (2 * ℓ)).getLast h_drop_ne = P.getLast hP_ne :=
    List.getLast_drop h_drop_ne
  rw [List.getLast?_eq_some_getLast h_drop_ne, List.getLast?_eq_some_getLast hP_ne] at *
  rw [h_eq_last]
  exact h_inv

/-- The basecase delegation correctness: `basecaseSqrtRem (ofLimbs (a.extract …))`
    satisfies `Spec_aux`. -/
private theorem spec_aux_basecase (a : Array UInt64) (lo len : Nat)
    (_h : lo + len ≤ a.size) :
    Spec_aux a lo len
      (basecaseSqrtRem (ofLimbs (a.extract lo (lo + len)))).1
      (basecaseSqrtRem (ofLimbs (a.extract lo (lo + len)))).2 := by
  set m := ofLimbs (a.extract lo (lo + len))
  set s := (basecaseSqrtRem m).1
  set r := (basecaseSqrtRem m).2
  have h_s_eq : s.toNat = Nat.sqrt m.toNat := toNat_basecaseSqrtRem_fst m
  have h_r_eq : r.toNat = m.toNat - Nat.sqrt m.toNat * Nat.sqrt m.toNat :=
    toNat_basecaseSqrtRem_snd m
  have h_m_val : m.toNat = sliceVal a lo len := toNat_ofLimbs_extract a lo len
  have h_sq_le : Nat.sqrt m.toNat * Nat.sqrt m.toNat ≤ m.toNat := Nat.sqrt_le _
  have h_lt_succ : m.toNat < (Nat.sqrt m.toNat + 1) * (Nat.sqrt m.toNat + 1) :=
    Nat.lt_succ_sqrt _
  refine ⟨?_, ?_⟩
  · -- s² + r = sliceVal
    rw [h_s_eq, h_r_eq, ← h_m_val]
    omega
  · -- r ≤ 2s
    rw [h_s_eq, h_r_eq]
    -- m < (sqrt + 1)² = sqrt² + 2·sqrt + 1, so m - sqrt² ≤ 2·sqrt.
    have h_expand : (Nat.sqrt m.toNat + 1) * (Nat.sqrt m.toNat + 1)
                  = Nat.sqrt m.toNat * Nat.sqrt m.toNat + 2 * Nat.sqrt m.toNat + 1 := by ring
    omega

/-- Case 2 (adjustment) bound: when `Y < Q²`, the adjusted residual
    `r_new = (2 S − 1) − (Q² − Y)` is non-negative, i.e.,
    `Q² + 1 ≤ 2 S + Y`.

    Requires `S' ≥ B` (derived from the slice's top-element-nonzero
    invariant) and `Q ≤ B` (from `mca_1_12_Q_le_B`).  Then
    `Q² ≤ B² ≤ S' · B`, and `2 (S' B + Q) + Y ≥ S' B + 2 Q ≥ Q² + 2`
    (using `Q ≥ 1`, which follows from the case condition `Y < Q²`). -/
private theorem mca_1_12_bound_adjust (S' Q U A₀ B : Nat)
    (h_S'_ge_B : S' ≥ B)
    (h_Q_le_B : Q ≤ B)
    (h_case : U * B + A₀ < Q * Q) :
    Q * Q + 1 ≤ 2 * (S' * B + Q) + (U * B + A₀) := by
  have h_Q_pos : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · simp [h] at h_case
    · exact h
  have h_QQ : Q * Q ≤ B * B := Nat.mul_le_mul h_Q_le_B h_Q_le_B
  have h_S'B : B * B ≤ S' * B := Nat.mul_le_mul_right B h_S'_ge_B
  have h_QQ_le : Q * Q ≤ S' * B := Nat.le_trans h_QQ h_S'B
  have h_expand : 2 * (S' * B + Q) + (U * B + A₀)
                = S' * B + (S' * B + 2 * Q + U * B + A₀) := by ring
  omega

/-- Case 1 final spec equation: small Nat-only helper to keep `omega`'s
    search tractable (without it, `omega` sees too many nested products). -/
private theorem mca_1_12_case1_eq (S Q U A₀ T B A₁ : Nat)
    (h_mca : T * (B * B) + A₁ * B + A₀ + Q * Q = S * S + (U * B + A₀))
    (h_case : Q * Q ≤ U * B + A₀) :
    S * S + (U * B + A₀ - Q * Q) = T * (B * B) + A₁ * B + A₀ := by
  omega

/-- Case 2 final spec equation. -/
private theorem mca_1_12_case2_eq (S Q U A₀ T B A₁ : Nat)
    (h_s_pos : 1 ≤ S)
    (h_mca : T * (B * B) + A₁ * B + A₀ + Q * Q = S * S + (U * B + A₀))
    (h_case : U * B + A₀ < Q * Q)
    (h_bnd : Q * Q + 1 ≤ 2 * S + (U * B + A₀)) :
    (S - 1) * (S - 1) + (2 * S - 1 - (Q * Q - (U * B + A₀)))
      = T * (B * B) + A₁ * B + A₀ := by
  -- (S - 1)² + 2S = S² + 1 (no Nat-sub in conclusion).
  have h_sub_eq : (S - 1) * (S - 1) + 2 * S = S * S + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
    subst hk
    have : k + 1 - 1 = k := by omega
    rw [this]; ring
  omega

/-- Case 2 final bound `r_new ≤ 2 (s − 1)`. -/
private theorem mca_1_12_case2_bound (S Q U A₀ B : Nat)
    (h_s_pos : 1 ≤ S)
    (h_case : U * B + A₀ < Q * Q) :
    (2 * S - 1 - (Q * Q - (U * B + A₀))) ≤ 2 * (S - 1) := by
  omega

/-- Inductive correctness of `sqrtRem.aux`: under the slice-top-nonzero
    invariant, `sqrtRem.aux a lo len _` satisfies `Spec_aux`. -/
private theorem sqrtRem_aux_correct (a : Array UInt64) :
    ∀ (len : Nat) (lo : Nat) (h : lo + len ≤ a.size),
    SliceTopNonzero a lo len →
    Spec_aux a lo len (sqrtRem.aux a lo len h).1 (sqrtRem.aux a lo len h).2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro lo h h_inv
    rw [sqrtRem.aux]
    by_cases hℓ : (len - 1) / 4 = 0
    · -- Basecase: ℓ = 0 (i.e., len ≤ 4).
      simp only [hℓ, ↓reduceIte]
      exact spec_aux_basecase a lo len h
    · -- Recursive case: ℓ ≥ 1, so len ≥ 5.
      simp only [hℓ, ↓reduceIte]
      set ℓ := (len - 1) / 4 with hℓ_def
      have hℓ_pos : 1 ≤ ℓ := by
        rcases Nat.eq_zero_or_pos ℓ with h0 | hp
        · exact absurd h0 hℓ
        · exact hp
      have h_2ℓ_lt : 2 * ℓ < len := by omega
      have h_new_bound : (lo + 2 * ℓ) + (len - 2 * ℓ) ≤ a.size := by omega
      have h_new_inv : SliceTopNonzero a (lo + 2 * ℓ) (len - 2 * ℓ) :=
        SliceTopNonzero_recurse a lo len ℓ h_2ℓ_lt h h_inv
      have ih_top := ih (len - 2 * ℓ) (by omega) (lo + 2 * ℓ) h_new_bound h_new_inv
      -- Unpack IH spec.
      set bℓ : Nat := 64 * ℓ with hbℓ_def
      set B : Nat := 2 ^ bℓ with hB_def
      set sr' := sqrtRem.aux a (lo + 2 * ℓ) (len - 2 * ℓ) h_new_bound
      set s' := sr'.1 with hs'_def
      set r' := sr'.2 with hr'_def
      obtain ⟨ih_eq, ih_bnd⟩ := ih_top
      -- ih_eq : s'.toNat * s'.toNat + r'.toNat = sliceVal a (lo + 2 * ℓ) (len - 2 * ℓ)
      -- ih_bnd : r'.toNat ≤ 2 * s'.toNat
      -- Define abbreviations matching MCA's variable names.
      set T : Nat := sliceVal a (lo + 2 * ℓ) (len - 2 * ℓ) with hT_def
      have h_top_eq : T = s'.toNat * s'.toNat + r'.toNat := ih_eq.symm
      -- S' ≥ B: from the slice's top-element-nonzero invariant.
      -- top = sliceVal a (lo + 2ℓ) (len - 2ℓ). top.size = len - 2ℓ.
      -- top's last element = a[(lo + 2ℓ) + (len - 2ℓ) - 1] = a[lo + len - 1].
      -- By invariant, this is nonzero, so top ≥ 2^(64 * (len - 2ℓ - 1)).
      have h_top_lower : 2 ^ (64 * (len - 2 * ℓ - 1)) ≤ T := by
        rw [hT_def]
        have h_len_eq : len - 2 * ℓ = (len - 2 * ℓ - 1) + 1 := by omega
        rw [h_len_eq]
        refine sliceVal_lower_bound_succ a (lo + 2 * ℓ) (len - 2 * ℓ - 1) (by omega) ?_
        · -- Show: a[(lo + 2 * ℓ) + (len - 2 * ℓ - 1)] ≠ 0.
          -- This equals a[lo + len - 1] (Nat-wise).
          -- Use h_inv: SliceTopNonzero a lo len.
          unfold SliceTopNonzero at h_inv
          -- h_inv : ((a.toList.drop lo).take len).getLast? ≠ some 0
          intro h_zero
          apply h_inv
          have h_idx : (lo + 2 * ℓ) + (len - 2 * ℓ - 1) = lo + len - 1 := by omega
          -- Use the list-level connection.
          have h_p_len : ((a.toList.drop lo).take len).length = len := by
            rw [List.length_take, List.length_drop, Array.length_toList]; omega
          have h_p_ne : ((a.toList.drop lo).take len) ≠ [] := by
            intro h
            have := congrArg List.length h
            rw [h_p_len] at this; simp at this; omega
          rw [List.getLast?_eq_some_getLast h_p_ne]
          congr 1
          -- Need: ((a.toList.drop lo).take len).getLast _ = 0
          -- Have: a[(lo + 2 * ℓ) + (len - 2 * ℓ - 1)] = 0
          -- The last element of the slice list is a[lo + len - 1] = a[(lo + 2ℓ) + (len - 2ℓ - 1)].
          have h_last_idx : ((a.toList.drop lo).take len).length - 1 = len - 1 := by
            rw [h_p_len]
          have h_last : ((a.toList.drop lo).take len).getLast h_p_ne
                      = ((a.toList.drop lo).take len)[len - 1]'(by rw [h_p_len]; omega) := by
            rw [List.getLast_eq_getElem]
            congr 1
          rw [h_last]
          rw [List.getElem_take, List.getElem_drop, Array.getElem_toList]
          show (a[lo + (len - 1)]'(by omega)) = 0
          have h_idx_eq : lo + (len - 1) = lo + 2 * ℓ + (len - 2 * ℓ - 1) := by omega
          rw [getElem_congr rfl h_idx_eq (by omega)]
          exact h_zero
      -- S' ≥ B: from (S' + 1)² > T ≥ 2^(64·(len − 2ℓ − 1)) ≥ B².
      have h_s'_ge_B : s'.toNat ≥ B := by
        have h_T_lt : T < (s'.toNat + 1) * (s'.toNat + 1) := by
          rw [h_top_eq]
          have h_sq : (s'.toNat + 1) * (s'.toNat + 1)
                    = s'.toNat * s'.toNat + 2 * s'.toNat + 1 := by ring
          omega
        have h_pow_le : 2 ^ (128 * ℓ) ≤ 2 ^ (64 * (len - 2 * ℓ - 1)) := by
          apply Nat.pow_le_pow_right (by decide)
          have hℓ_bound : 4 * ℓ + 1 ≤ len := by
            have : ℓ ≤ (len - 1) / 4 := by omega
            omega
          omega
        have h_B_sq : B * B = 2 ^ (128 * ℓ) := by
          rw [hB_def, hbℓ_def, ← Nat.pow_add]
          congr 1; ring
        have h_T_ge_Bsq : T ≥ B * B := by
          rw [h_B_sq]; exact Nat.le_trans h_pow_le h_top_lower
        have h_sq_gt : (s'.toNat + 1) * (s'.toNat + 1) > B * B := by omega
        have h_s'_gt : s'.toNat + 1 > B := by
          by_contra hc
          push Not at hc
          exact absurd (Nat.mul_le_mul hc hc) (by omega)
        omega
      -- Set up the rest of the body.
      set a₀ := ofLimbs (a.extract lo (lo + ℓ))
      set a₁ := ofLimbs (a.extract (lo + ℓ) (lo + 2 * ℓ))
      set dividend := (r' <<< bℓ) + a₁
      set divisor := s' <<< 1
      set qu := dividend.divMod divisor
      set q := qu.1 with hq_def
      set u := qu.2 with hu_def
      set s := (s' <<< bℓ) + q
      set lhs := (u <<< bℓ) + a₀
      set rhs := q.square
      -- toNat computations.
      have h_a₀_eq : a₀.toNat = sliceVal a lo ℓ := by
        show (ofLimbs (a.extract lo (lo + ℓ))).toNat = _
        exact toNat_ofLimbs_extract a lo ℓ
      have h_a₁_eq : a₁.toNat = sliceVal a (lo + ℓ) ℓ := by
        show (ofLimbs (a.extract (lo + ℓ) (lo + 2 * ℓ))).toNat = _
        rw [show lo + 2 * ℓ = (lo + ℓ) + ℓ from by ring]
        exact toNat_ofLimbs_extract a (lo + ℓ) ℓ
      have h_dividend_eq : dividend.toNat = r'.toNat * B + a₁.toNat := by
        show ((r' <<< bℓ) + a₁).toNat = _
        rw [toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, hB_def]
      have h_divisor_eq : divisor.toNat = 2 * s'.toNat := by
        show (s' <<< 1).toNat = _
        rw [toNat_hShiftLeft, Nat.shiftLeft_eq]; ring
      -- divisor.toNat > 0 (since s' ≥ B ≥ 2).
      have h_s'_pos : 1 ≤ s'.toNat := by
        have h_B_ge_2 : 2 ≤ B := by
          rw [hB_def, hbℓ_def]
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (64 * ℓ) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have h_divisor_pos : 0 < divisor.toNat := by rw [h_divisor_eq]; omega
      -- divMod identity.
      have h_qu_spec := divMod_toNat dividend divisor
      have h_div_eq : q.toNat * divisor.toNat + u.toNat = dividend.toNat := h_qu_spec.1
      have h_u_lt : u.toNat < divisor.toNat := h_qu_spec.2 (by omega)
      have h_mca_divmod : r'.toNat * B + a₁.toNat = q.toNat * (2 * s'.toNat) + u.toNat := by
        rw [← h_dividend_eq, ← h_div_eq, h_divisor_eq]
      have h_u_lt' : u.toNat < 2 * s'.toNat := by rw [← h_divisor_eq]; exact h_u_lt
      -- Q ≤ B.
      have h_Q_le_B : q.toNat ≤ B := by
        have h_A₁_lt : a₁.toNat < B := by
          rw [h_a₁_eq, hB_def, hbℓ_def]
          rw [show 64 * ℓ = 64 * ℓ from rfl]
          -- sliceVal a (lo + ℓ) ℓ ≤ 2^(64*ℓ) - 1 < 2^(64*ℓ).
          unfold sliceVal
          have := toNatLimbsList_lt_pow ((a.toList.drop (lo + ℓ)).take ℓ)
          have h_len : ((a.toList.drop (lo + ℓ)).take ℓ).length ≤ ℓ := by
            rw [List.length_take]; omega
          have h_pow_le : 2 ^ (64 * ((a.toList.drop (lo + ℓ)).take ℓ).length)
                       ≤ 2 ^ (64 * ℓ) := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        exact mca_1_12_Q_le_B s'.toNat r'.toNat q.toNat u.toNat a₁.toNat B
                h_s'_ge_B ih_bnd h_A₁_lt h_mca_divmod
      -- toNat of s, lhs, rhs.
      have h_s_eq : s.toNat = s'.toNat * B + q.toNat := by
        show ((s' <<< bℓ) + q).toNat = _
        rw [toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, hB_def]
      have h_lhs_eq : lhs.toNat = u.toNat * B + a₀.toNat := by
        show ((u <<< bℓ) + a₀).toNat = _
        rw [toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, hB_def]
      have h_rhs_eq : rhs.toNat = q.toNat * q.toNat := by
        show q.square.toNat = _
        rw [toNat_square, Nat.pow_two]
      -- A₀ < B.
      have h_A₀_lt : a₀.toNat < B := by
        rw [h_a₀_eq, hB_def, hbℓ_def]
        unfold sliceVal
        have := toNatLimbsList_lt_pow ((a.toList.drop lo).take ℓ)
        have h_len : ((a.toList.drop lo).take ℓ).length ≤ ℓ := by
          rw [List.length_take]; omega
        have h_pow_le : 2 ^ (64 * ((a.toList.drop lo).take ℓ).length)
                     ≤ 2 ^ (64 * ℓ) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      -- Decompose sliceVal.
      have h_B : B = 2 ^ (64 * ℓ) := by rw [hB_def, hbℓ_def]
      have h_BB : B * B = 2 ^ (64 * (2 * ℓ)) := by
        rw [hB_def, hbℓ_def, ← Nat.pow_add]; congr 1; ring
      have h_sliceVal_eq : sliceVal a lo len
                        = T * (B * B) + a₁.toNat * B + a₀.toNat := by
        rw [sliceVal_split a lo len (2 * ℓ) (by omega) h]
        rw [sliceVal_split a lo (2 * ℓ) ℓ (by omega) (by omega)]
        rw [show 2 * ℓ - ℓ = ℓ from by omega]
        rw [← h_a₀_eq, ← h_a₁_eq, ← hT_def, ← h_B, ← h_BB]
        ring
      -- MCA equation.
      have h_mca_eq : T * (B * B) + a₁.toNat * B + a₀.toNat + q.toNat * q.toNat
                    = s.toNat * s.toNat + (u.toNat * B + a₀.toNat) := by
        have key := mca_1_12_eq T r'.toNat q.toNat u.toNat s'.toNat a₁.toNat a₀.toNat B
                      h_top_eq h_mca_divmod
        rw [h_s_eq]
        have h_assoc : T * B * B = T * (B * B) := by ring
        omega
      -- s.toNat ≥ 1 (used in both cases).
      have h_s_pos : 1 ≤ s.toNat := by
        rw [h_s_eq]
        have hB1 : 1 ≤ B := by rw [hB_def]; exact Nat.one_le_two_pow
        have : 1 ≤ s'.toNat * B := Nat.mul_le_mul h_s'_pos hB1
        omega
      -- Case split.
      by_cases h_case : lhs ≥ rhs
      · -- Case 1: no adjust. Result is (s, lhs - rhs).
        simp only [h_case, ↓reduceIte]
        have h_case_toNat : rhs.toNat ≤ lhs.toNat := (ge_iff_toNat_ge lhs rhs).mp h_case
        rw [h_lhs_eq, h_rhs_eq] at h_case_toNat
        refine ⟨?_, ?_⟩
        · -- Spec equation.
          show s.toNat * s.toNat + (lhs - rhs).toNat = sliceVal a lo len
          rw [toNat_sub, h_sliceVal_eq, h_lhs_eq, h_rhs_eq]
          exact mca_1_12_case1_eq s.toNat q.toNat u.toNat a₀.toNat T B a₁.toNat
                  h_mca_eq h_case_toNat
        · -- r ≤ 2s.
          show (lhs - rhs).toNat ≤ 2 * s.toNat
          rw [toNat_sub, h_lhs_eq, h_rhs_eq, h_s_eq]
          have h_bnd := mca_1_12_bound_no_adjust s'.toNat q.toNat u.toNat a₀.toNat B
                          h_u_lt' h_A₀_lt
          omega
      · -- Case 2: adjust. Result is (s - 1, (s <<< 1) - 1 - (rhs - lhs)).
        simp only [h_case, ↓reduceIte]
        have h_case_toNat : lhs.toNat < rhs.toNat := by
          have hnle : ¬ (rhs.toNat ≤ lhs.toNat) := fun h =>
            h_case ((ge_iff_toNat_ge lhs rhs).mpr h)
          omega
        rw [h_lhs_eq, h_rhs_eq] at h_case_toNat
        -- toNat of shifts and subs.
        have h_2s_eq : (s <<< 1).toNat = 2 * s.toNat := by
          rw [toNat_hShiftLeft, Nat.shiftLeft_eq]; ring
        have h_s_minus_eq : (s - 1).toNat = s.toNat - 1 := by
          rw [toNat_sub]; rfl
        have h_inner_eq : ((s <<< 1) - 1 - (rhs - lhs)).toNat
                        = 2 * s.toNat - 1 - (q.toNat * q.toNat - (u.toNat * B + a₀.toNat)) := by
          rw [toNat_sub, toNat_sub, toNat_sub]
          rw [h_2s_eq, h_rhs_eq, h_lhs_eq]
          rfl
        -- Case 2 bound: Q² + 1 ≤ 2*(S'*B + Q) + (U*B + A₀).
        have h_bnd_adj := mca_1_12_bound_adjust s'.toNat q.toNat u.toNat a₀.toNat B
                            h_s'_ge_B h_Q_le_B h_case_toNat
        have h_bnd : q.toNat * q.toNat + 1 ≤ 2 * s.toNat + (u.toNat * B + a₀.toNat) := by
          rw [h_s_eq]; exact h_bnd_adj
        refine ⟨?_, ?_⟩
        · -- Spec equation.
          show (s - 1).toNat * (s - 1).toNat
              + ((s <<< 1) - 1 - (rhs - lhs)).toNat = sliceVal a lo len
          rw [h_s_minus_eq, h_inner_eq, h_sliceVal_eq]
          exact mca_1_12_case2_eq s.toNat q.toNat u.toNat a₀.toNat T B a₁.toNat
                  h_s_pos h_mca_eq h_case_toNat h_bnd
        · -- r ≤ 2(s-1).
          show ((s <<< 1) - 1 - (rhs - lhs)).toNat ≤ 2 * (s - 1).toNat
          rw [h_inner_eq, h_s_minus_eq]
          exact mca_1_12_case2_bound s.toNat q.toNat u.toNat a₀.toNat B h_s_pos h_case_toNat

/-- At the top-level invocation, the slice covers all of `m.limbs`, so
    `sliceVal = m.toNat`. -/
private theorem sliceVal_full (m : AzNat) :
    sliceVal m.limbs 0 m.limbs.size = m.toNat := by
  unfold sliceVal
  show toNatLimbsList ((m.limbs.toList.drop 0).take m.limbs.size) = m.toNat
  rw [List.drop_zero]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rfl

/-- The slice-top-nonzero invariant holds at the top-level (from the
    AzNat invariant that `m.limbs.back? ≠ some 0`). -/
private theorem sliceTopNonzero_full (m : AzNat) :
    SliceTopNonzero m.limbs 0 m.limbs.size := by
  unfold SliceTopNonzero
  show ((m.limbs.toList.drop 0).take m.limbs.size).getLast? ≠ some 0
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rw [Array.getLast?_toList]
  exact m.last_ne_zero

-- ─────────────────────────────────────────────────────────────────────────
-- Top-level theorems
-- ─────────────────────────────────────────────────────────────────────────

/-- `sqrtRem.fst` gives `Nat.sqrt m.toNat`. -/
@[simp] theorem toNat_sqrtRem_fst (m : AzNat) :
    (sqrtRem m).1.toNat = Nat.sqrt m.toNat := by
  have h_spec := sqrtRem_aux_correct m.limbs m.limbs.size 0 (by omega)
                   (sliceTopNonzero_full m)
  obtain ⟨h_eq, h_bnd⟩ := h_spec
  rw [sliceVal_full] at h_eq
  -- h_eq: s² + r = m.toNat; h_bnd: r ≤ 2s. Conclude s = Nat.sqrt m.toNat.
  set s := (sqrtRem.aux m.limbs 0 m.limbs.size _).1 with hs_def
  set r := (sqrtRem.aux m.limbs 0 m.limbs.size _).2 with hr_def
  have h_sq_le : s.toNat * s.toNat ≤ m.toNat := by omega
  have h_lt_succ : m.toNat < (s.toNat + 1) * (s.toNat + 1) := by
    have h_expand : (s.toNat + 1) * (s.toNat + 1)
                  = s.toNat * s.toNat + 2 * s.toNat + 1 := by ring
    omega
  show s.toNat = _
  exact Nat.eq_sqrt.mpr ⟨h_sq_le, h_lt_succ⟩

/-- `sqrt m = Nat.sqrt m.toNat`. -/
@[simp] theorem toNat_sqrt (m : AzNat) : (sqrt m).toNat = Nat.sqrt m.toNat :=
  toNat_sqrtRem_fst m

/-- `sqrtRem.snd` gives `m − ⌊√m⌋²`. -/
@[simp] theorem toNat_sqrtRem_snd (m : AzNat) :
    (sqrtRem m).2.toNat = m.toNat - Nat.sqrt m.toNat * Nat.sqrt m.toNat := by
  have h_spec := sqrtRem_aux_correct m.limbs m.limbs.size 0 (by omega)
                   (sliceTopNonzero_full m)
  obtain ⟨h_eq, _⟩ := h_spec
  rw [sliceVal_full] at h_eq
  have h_s := toNat_sqrtRem_fst m
  show (sqrtRem.aux m.limbs 0 m.limbs.size _).2.toNat = _
  rw [show (sqrtRem.aux m.limbs 0 m.limbs.size _).1.toNat = Nat.sqrt m.toNat from h_s] at h_eq
  omega

end Azurite.AzNat
