/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Div.DivModLimb
import Azurite.AzNat.Equiv.DivMod10p19
import Azurite.AzNat.Equiv.LimbDigitsPow2
import Azurite.AzNat.LimbDigits
import Azurite.UInt64.Equiv.Digits
import Azurite.UInt64.Equiv.MaxPow
import Mathlib.Data.Nat.Digits.Lemmas

namespace Azurite.AzNat

/-! ### Equivalence of the base-`10^19` aux to the generic one -/

/-- The constant-folded `toBase10p19DigitsAux` agrees with the generic
    `toBaseUInt64DigitsAux` at `d = divMod10p19_d`. -/
theorem toBase10p19DigitsAux_eq_toBaseUInt64DigitsAux :
    ∀ (f : Nat) (U : AzNat) (acc : Array UInt64),
      toBase10p19DigitsAux f U acc =
        toBaseUInt64DigitsAux divMod10p19_d divMod10p19_d_ne f U acc := by
  intro f
  induction f with
  | zero =>
    intro U acc; rfl
  | succ n ih =>
    intro U acc
    unfold toBase10p19DigitsAux toBaseUInt64DigitsAux
    by_cases h : U.limbs.size = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [divMod10p19_eq_divModUInt64]
      exact ih _ _

/-! ### Helpers: `digitsPaddedTo` and `toBaseUInt64DigitsAux` -/

/-- `UInt64.digitsPaddedTo b u E`, when `u.toNat < b.toNat ^ E` and `b ≥ 2`,
    represents `u.toNat` in base `b`. -/
private theorem ofDigits_digitsPaddedTo (b u : UInt64) (E : Nat) (hb : 2 ≤ b.toNat)
    (_h_u : u.toNat < b.toNat ^ E) :
    Nat.ofDigits b.toNat ((UInt64.digitsPaddedTo b u E).toList.map UInt64.toNat) =
      u.toNat := by
  unfold UInt64.digitsPaddedTo
  have h_dig_val : Nat.ofDigits b.toNat ((UInt64.digits b u).toList.map UInt64.toNat) = u.toNat := by
    rw [UInt64.digits_eq b u hb, Nat.ofDigits_digits]
  by_cases h_lt : (UInt64.digits b u).size < E
  · rw [ite_eq_left h_lt, Array.toList_append, Array.toList_replicate,
        List.map_append, List.map_replicate]
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0, Nat.ofDigits_append_replicate_zero]
    exact h_dig_val
  · rw [ite_eq_right h_lt]
    exact h_dig_val

/-- Each entry of `digitsPaddedTo b u E` is `< b.toNat`. -/
private theorem digit_lt_of_digitsPaddedTo (b u : UInt64) (E : Nat) (hb : 2 ≤ b.toNat) :
    ∀ x ∈ (UInt64.digitsPaddedTo b u E).toList.map UInt64.toNat, x < b.toNat := by
  intro x hx
  unfold UInt64.digitsPaddedTo at hx
  have h_dig_eq : (UInt64.digits b u).toList.map UInt64.toNat =
      Nat.digits b.toNat u.toNat := UInt64.digits_eq b u hb
  by_cases h_lt : (UInt64.digits b u).size < E
  · rw [ite_eq_left h_lt] at hx
    rw [Array.toList_append, Array.toList_replicate, List.map_append,
        List.map_replicate, List.mem_append] at hx
    cases hx with
    | inl hx => rw [h_dig_eq] at hx; exact Nat.digits_lt_base hb hx
    | inr hx =>
      rw [List.mem_replicate] at hx
      have : x = (0 : UInt64).toNat := hx.2
      rw [this]; show 0 < b.toNat; omega
  · rw [ite_eq_right h_lt] at hx; rw [h_dig_eq] at hx; exact Nat.digits_lt_base hb hx

/-- Length of `digitsPaddedTo b u E` is `max E (UInt64.digits b u).size`. In
    the typical case `(UInt64.digits b u).size ≤ E`, it equals `E`. -/
private theorem digitsPaddedTo_size_eq_of_le (b u : UInt64) (E : Nat)
    (h_le : (UInt64.digits b u).size ≤ E) :
    (UInt64.digitsPaddedTo b u E).size = E := by
  unfold UInt64.digitsPaddedTo
  by_cases h_lt : (UInt64.digits b u).size < E
  · rw [ite_eq_left h_lt, Array.size_append, Array.size_replicate]; omega
  · rw [ite_eq_right h_lt]; omega

/-! ### `toBaseUInt64DigitsAux` — base-`P` digit extraction by repeated division -/

/-- Loop invariant for `toBaseUInt64DigitsAux`: at any partial state
    `(acc, U)`, the value `ofDigits P acc + P^|acc| * U` is invariant, so when
    the loop terminates at `U = 0` we get `ofDigits P acc = original U.toNat`. -/
private theorem ofDigits_toBaseUInt64DigitsAux (d : UInt64) (hd : d ≠ 0)
    (hd_pos : 2 ≤ d.toNat) :
    ∀ (fuel : Nat) (U : AzNat) (acc : Array UInt64),
      U.toNat < d.toNat ^ fuel →
      Nat.ofDigits d.toNat
          ((toBaseUInt64DigitsAux d hd fuel U acc).toList.map UInt64.toNat) =
        Nat.ofDigits d.toNat (acc.toList.map UInt64.toNat) +
          d.toNat ^ acc.size * U.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro U acc h_fuel
    show Nat.ofDigits d.toNat (acc.toList.map UInt64.toNat) =
        Nat.ofDigits d.toNat (acc.toList.map UInt64.toNat) + d.toNat ^ acc.size * U.toNat
    have h_u : U.toNat = 0 := by
      have : U.toNat < 1 := by simpa using h_fuel
      omega
    rw [h_u]; ring
  | succ f ih =>
    intro U acc h_fuel
    show Nat.ofDigits d.toNat
        ((if U.limbs.size = 0 then acc
          else toBaseUInt64DigitsAux d hd f (U.divModUInt64 d hd).1
            (acc.push (U.divModUInt64 d hd).2)).toList.map UInt64.toNat) =
      Nat.ofDigits d.toNat (acc.toList.map UInt64.toNat) +
        d.toNat ^ acc.size * U.toNat
    by_cases h_size : U.limbs.size = 0
    · rw [ite_eq_left h_size]
      have h_u : U.toNat = 0 := by
        show toNatLimbsList U.limbs.toList = 0
        rw [show U.limbs.toList = [] from by
          have : U.limbs.toList.length = 0 := by rw [Array.length_toList, h_size]
          exact List.length_eq_zero_iff.mp this]
        rfl
      rw [h_u]; ring
    · rw [ite_eq_right h_size]
      have h_u_pos : 0 < U.toNat := by
        show 0 < toNatLimbsList U.limbs.toList
        by_contra h
        push Not at h
        have h_zero : toNatLimbsList U.limbs.toList = 0 := by omega
        have h_back := U.last_ne_zero
        have h_nil : U.limbs.toList = [] := by
          apply toNatLimbsList_eq_zero_of_getLast_ne_zero
          · rw [Array.getLast?_toList]; exact h_back
          · exact h_zero
        apply h_size
        rw [← Array.length_toList, h_nil]; rfl
      set qr := U.divModUInt64 d hd
      have h_qr := toNat_divModUInt64 U d hd
      have h_q_lt : qr.1.toNat < d.toNat ^ f := by
        have h_d_pos : 0 < d.toNat := by omega
        have h_pow_succ : d.toNat ^ (f + 1) = d.toNat * d.toNat ^ f := by
          rw [pow_succ]; ring
        have : qr.1.toNat * d.toNat + qr.2.toNat = U.toNat := h_qr.1
        have h_q_bound : qr.1.toNat * d.toNat < d.toNat * d.toNat ^ f := by
          calc qr.1.toNat * d.toNat
              ≤ qr.1.toNat * d.toNat + qr.2.toNat := Nat.le_add_right _ _
            _ = U.toNat := this
            _ < d.toNat ^ (f + 1) := h_fuel
            _ = d.toNat * d.toNat ^ f := h_pow_succ
        exact Nat.lt_of_mul_lt_mul_left (by rw [Nat.mul_comm] at h_q_bound; exact h_q_bound)
      rw [ih qr.1 (acc.push qr.2) h_q_lt]
      rw [Array.toList_push, List.map_append, List.map_singleton,
          Nat.ofDigits_append, List.length_map, Array.length_toList,
          Array.size_push, Nat.ofDigits_singleton]
      have h_val : qr.1.toNat * d.toNat + qr.2.toNat = U.toNat := h_qr.1
      have h_pow_succ : d.toNat ^ (acc.size + 1) = d.toNat ^ acc.size * d.toNat := by
        rw [pow_succ]
      rw [h_pow_succ]
      have h_arith : d.toNat ^ acc.size * d.toNat * qr.1.toNat
          + d.toNat ^ acc.size * qr.2.toNat = d.toNat ^ acc.size * U.toNat := by
        rw [← h_val]; ring
      linarith

/-- Each digit produced by `toBaseUInt64DigitsAux` is `< d.toNat`. -/
private theorem digit_lt_of_toBaseUInt64DigitsAux (d : UInt64) (hd : d ≠ 0) :
    ∀ (fuel : Nat) (U : AzNat) (acc : Array UInt64),
      (∀ x ∈ acc.toList.map UInt64.toNat, x < d.toNat) →
      ∀ x ∈ (toBaseUInt64DigitsAux d hd fuel U acc).toList.map UInt64.toNat,
        x < d.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro U acc h_acc x hx
    -- toBaseUInt64DigitsAux d hd 0 U acc = acc
    show x < d.toNat
    apply h_acc x
    exact hx
  | succ f ih =>
    intro U acc h_acc x hx
    by_cases h_size : U.limbs.size = 0
    · rw [show toBaseUInt64DigitsAux d hd (f + 1) U acc = acc from by
        show (if U.limbs.size = 0 then acc else _) = acc
        rw [ite_eq_left h_size]] at hx
      exact h_acc x hx
    · rw [show toBaseUInt64DigitsAux d hd (f + 1) U acc =
            toBaseUInt64DigitsAux d hd f (U.divModUInt64 d hd).1
              (acc.push (U.divModUInt64 d hd).2) from by
        show (if U.limbs.size = 0 then acc else _) = _
        rw [ite_eq_right h_size]] at hx
      apply ih (U.divModUInt64 d hd).1 (acc.push (U.divModUInt64 d hd).2) ?_ x hx
      intro y hy
      rw [Array.toList_push, List.map_append, List.map_singleton, List.mem_append] at hy
      cases hy with
      | inl h => exact h_acc y h
      | inr h =>
        rw [List.mem_singleton] at h
        rw [h]
        have h_qr := toNat_divModUInt64 U d hd
        exact h_qr.2

/-! ### Foldl over base-`P` digits with `digitsPaddedTo` -/

/-- Helper recurrence: a foldl that concatenates `digitsPaddedTo b · E` over
    a list, with each input digit `< b.toNat ^ E`, has `Nat.ofDigits` equal to
    the base-`b^E` reconstruction of the list. -/
private theorem ofDigits_foldl_digitsPaddedTo (b : UInt64) (hb : 2 ≤ b.toNat) (E : Nat) :
    ∀ (acc : Array UInt64) (L : List UInt64),
      (∀ d ∈ L, d.toNat < b.toNat ^ E) →
      Nat.ofDigits b.toNat
          ((L.foldl (fun a d => a ++ UInt64.digitsPaddedTo b d E) acc).toList.map
            UInt64.toNat) =
        Nat.ofDigits b.toNat (acc.toList.map UInt64.toNat) +
          b.toNat ^ acc.size * Nat.ofDigits (b.toNat ^ E) (L.map UInt64.toNat) := by
  intro acc L
  induction L generalizing acc with
  | nil =>
    intro _
    show Nat.ofDigits b.toNat (acc.toList.map UInt64.toNat) =
        Nat.ofDigits b.toNat (acc.toList.map UInt64.toNat) +
          b.toNat ^ acc.size * Nat.ofDigits (b.toNat ^ E) []
    rw [show Nat.ofDigits (b.toNat ^ E) ([] : List Nat) = 0 from rfl]; ring
  | cons d L ih =>
    intro h_bound
    rw [List.foldl_cons]
    have h_d_bound : d.toNat < b.toNat ^ E := h_bound d List.mem_cons_self
    have h_d_digits_le : (UInt64.digits b d).size ≤ E := by
      have h_2_lt : 1 < b.toNat := by omega
      have h_len : (UInt64.digits b d).size = (Nat.digits b.toNat d.toNat).length := by
        rw [Array.size_eq_length_toList, ← List.length_map (f := UInt64.toNat),
            UInt64.digits_eq b d hb]
      rw [h_len, Nat.digits_length_le_iff h_2_lt]
      exact h_d_bound
    have h_tail_bound : ∀ x ∈ L, x.toNat < b.toNat ^ E := fun x hx =>
      h_bound x (List.mem_cons_of_mem _ hx)
    rw [ih (acc ++ UInt64.digitsPaddedTo b d E) h_tail_bound]
    rw [Array.toList_append, List.map_append, Nat.ofDigits_append]
    rw [Array.size_append, digitsPaddedTo_size_eq_of_le b d E h_d_digits_le]
    rw [List.length_map, Array.length_toList,
        ofDigits_digitsPaddedTo b d E hb h_d_bound]
    rw [List.map_cons, Nat.ofDigits_cons]
    rw [Nat.pow_add]
    ring

/-- Each digit produced by the foldl over `digitsPaddedTo` is `< b.toNat`. -/
private theorem digit_lt_of_foldl_digitsPaddedTo (b : UInt64) (hb : 2 ≤ b.toNat) (E : Nat) :
    ∀ (acc : Array UInt64) (L : List UInt64),
      (∀ x ∈ acc.toList.map UInt64.toNat, x < b.toNat) →
      ∀ x ∈ (L.foldl (fun a d => a ++ UInt64.digitsPaddedTo b d E) acc).toList.map
              UInt64.toNat, x < b.toNat := by
  intro acc L
  induction L generalizing acc with
  | nil => intros h_acc x hx; exact h_acc x hx
  | cons d L ih =>
    intro h_acc x hx
    rw [List.foldl_cons] at hx
    apply ih (acc ++ UInt64.digitsPaddedTo b d E) ?_ x hx
    intro y hy
    rw [Array.toList_append, List.map_append, List.mem_append] at hy
    cases hy with
    | inl h => exact h_acc y h
    | inr h => exact digit_lt_of_digitsPaddedTo b d E hb y h

/-! ### Trim preservation (generic, mirroring `LimbDigitsPow2.lean`) -/

/-- Generic helper duplicated from `LimbDigitsPow2.lean` for use here. -/
private theorem ofDigits_trimTrailingZeros (b : Nat) (a : Array UInt64) :
    Nat.ofDigits b ((trimTrailingZeros a).toList.map UInt64.toNat) =
    Nat.ofDigits b (a.toList.map UInt64.toNat) := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp [h]
  · have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1]'h_idx = 0
    · simp only [h, ↓reduceDIte, h_last, ite_true]
      rw [ofDigits_trimTrailingZeros b a.pop]
      have h_ne : a.toList ≠ [] := by
        intro he
        apply h
        have h_len : a.toList.length = 0 := by rw [he]; rfl
        rwa [Array.length_toList] at h_len
      have h_pop_eq : a.toList = a.pop.toList ++ [a.toList.getLast h_ne] := by
        rw [Array.toList_pop]
        exact (List.dropLast_append_getLast h_ne).symm
      have h_getLast : a.toList.getLast h_ne = a[a.size - 1]'h_idx := by
        rw [List.getLast_eq_getElem]; simp
      rw [h_pop_eq, h_getLast, h_last, List.map_append, List.map_singleton]
      have : (0 : UInt64).toNat = 0 := rfl
      rw [this, Nat.ofDigits_append_zero]
    · simp [h, h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

private theorem mem_of_mem_trimTrailingZeros (a : Array UInt64) :
    ∀ y ∈ (trimTrailingZeros a).toList, y ∈ a.toList := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp [h]
  · have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1]'h_idx = 0
    · simp only [h, ↓reduceDIte, h_last, ite_true]
      intro y hy
      have := mem_of_mem_trimTrailingZeros a.pop y hy
      rw [Array.toList_pop] at this
      exact List.mem_of_mem_dropLast this
    · simp [h, h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

private theorem getLast_map_toNat_ne_zero_of_back?_ne_some_zero
    {b : Array UInt64} (h_back : b.back? ≠ some 0)
    (h_ne : b.toList.map UInt64.toNat ≠ []) :
    (b.toList.map UInt64.toNat).getLast h_ne ≠ 0 := by
  have h_ne_b : b.toList ≠ [] := fun he => h_ne (by rw [he]; rfl)
  rw [List.getLast_map]
  intro h_eq
  apply h_back
  rw [← Array.getLast?_toList, List.getLast?_eq_some_getLast h_ne_b]
  congr 1
  apply UInt64.toNat.inj
  rw [h_eq]; rfl

/-! ### Main correctness theorem. -/

/-- **Correctness of `AzNat.limbDigits`.** For `b.toNat ≥ 2`, the function
    produces the base-`b` digits of `n`, LSB-first, matching `Nat.digits`. -/
theorem limbDigits_eq (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat) :
    (n.limbDigits b).toList.map UInt64.toNat = Nat.digits b.toNat n.toNat := by
  have hb_uint : ¬ b < 2 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt_toNat] at h
    have h2 : (2 : UInt64).toNat = 2 := rfl
    omega
  have h_b_pos : 1 < b.toNat := by omega
  unfold AzNat.limbDigits
  rw [ite_eq_right hb_uint]
  -- Follow the function's match on `n.limbs.size`.
  split
  · -- size = 0 branch
    rename_i h_size
    have h_n : n.toNat = 0 := by
      show toNatLimbsList n.limbs.toList = 0
      have : n.limbs.toList = [] := by
        have h_len : n.limbs.toList.length = 0 := by rw [Array.length_toList, h_size]
        exact List.length_eq_zero_iff.mp h_len
      rw [this]; rfl
    rw [h_n]
    show ([] : List UInt64).map UInt64.toNat = Nat.digits b.toNat 0
    simp
  · -- size = 1 branch
    rename_i h_size
    have h_n : n.toNat = (n.limbs[0]'(by simp [h_size])).toNat := by
      show toNatLimbsList n.limbs.toList = _
      have h_list : n.limbs.toList = [n.limbs[0]'(by simp [h_size])] := by
        have h_len : n.limbs.toList.length = 1 := by rw [Array.length_toList, h_size]
        have h0 : n.limbs.toList[0]? = some (n.limbs[0]'(by simp [h_size])) := by
          rw [Array.getElem?_toList]; simp
        match h_eq : n.limbs.toList with
        | [] => exfalso; rw [h_eq] at h_len; simp at h_len
        | [x] =>
          rw [h_eq] at h0
          simp at h0
          rw [h0]
        | _ :: _ :: _ =>
          exfalso
          rw [h_eq] at h_len
          simp at h_len
      rw [h_list]
      show toNatLimbsList [n.limbs[0]'(by simp [h_size])] = _
      simp [toNatLimbsList]
    rw [h_n]; exact UInt64.digits_eq b _ hb
  · -- size = _ + 2 branch
    rename_i size h_size
    -- ≥ 2-limb case; dispatch on isPowerOfTwo.
    by_cases hpow : b.isPowerOfTwo
    · rw [ite_eq_left hpow]
      exact limbDigitsPow2_eq b.toBitVec.ctz.toNat
        (by
          have h_ne : b ≠ 0 := by
            intro he
            unfold UInt64.isPowerOfTwo at hpow
            rw [he] at hpow; simp at hpow
          have h_bv_ne : b.toBitVec ≠ 0#64 := fun hb' =>
            h_ne (UInt64.eq_of_toBitVec_eq hb')
          have h_bv_lt := BitVec.ctz_lt_iff_ne_zero.mpr h_bv_ne
          rw [BitVec.lt_def] at h_bv_lt
          have h_64 : ((↑(64 : Nat) : BitVec 64)).toNat = 64 := by decide
          have h_b_eq : b.toNat = 2 ^ b.toBitVec.ctz.toNat :=
            UInt64.toNat_eq_two_pow_ctz b hpow
          have h_2_le : 2 ≤ 2 ^ b.toBitVec.ctz.toNat := by omega
          have h_pow_le_iff : 2 ^ 1 ≤ 2 ^ b.toBitVec.ctz.toNat → 1 ≤ b.toBitVec.ctz.toNat := by
            intro h
            by_contra hc
            push Not at hc
            have : b.toBitVec.ctz.toNat = 0 := by omega
            rw [this] at h
            simp at h
          exact h_pow_le_iff (by simpa using h_2_le))
        (by
          have h_ne : b ≠ 0 := by
            intro he
            unfold UInt64.isPowerOfTwo at hpow
            rw [he] at hpow; simp at hpow
          have h_bv_ne : b.toBitVec ≠ 0#64 := fun hb' =>
            h_ne (UInt64.eq_of_toBitVec_eq hb')
          have h_bv_lt := BitVec.ctz_lt_iff_ne_zero.mpr h_bv_ne
          rw [BitVec.lt_def] at h_bv_lt
          have h_64 : ((↑(64 : Nat) : BitVec 64)).toNat = 64 := by decide
          omega)
        n
      |>.trans (by rw [← UInt64.toNat_eq_two_pow_ctz b hpow])
    · rw [ite_eq_right hpow]
      -- Two sub-branches: `b = 10` (specialized via `toBase10p19DigitsAux`)
      -- and `b ≠ 10` (generic via `toBaseUInt64DigitsAux`). They produce
      -- the same array because `toBase10p19DigitsAux _ n #[]` equals
      -- `toBaseUInt64DigitsAux divMod10p19_d _ _ n #[]` (by
      -- `toBase10p19DigitsAux_eq_toBaseUInt64DigitsAux`), and
      -- `divMod10p19_d = (UInt64.maxPow 10).1` / `UInt64.maxPow10Exp = (UInt64.maxPow 10).2`
      -- (by `UInt64.maxPow_ten`). We use a `suffices` to prove the
      -- generic-case correctness once, then convert the specialized
      -- branch into the generic form.
      suffices h_gen : ∀ (P_arg : UInt64) (E_arg : Nat)
          (h_P_eq : P_arg = (UInt64.maxPow b).1)
          (h_E_eq : E_arg = (UInt64.maxPow b).2)
          (hP : P_arg ≠ 0),
          List.map UInt64.toNat (AzNat.trimTrailingZeros
            (Array.foldl (fun acc d => acc ++ UInt64.digitsPaddedTo b d E_arg) #[]
              (AzNat.toBaseUInt64DigitsAux P_arg hP (64 * n.limbs.size) n #[]))).toList
          = Nat.digits b.toNat n.toNat by
        by_cases hb10 : b = 10
        · rw [ite_eq_left hb10]
          subst hb10
          -- Convert specialized to generic
          have h_aux := toBase10p19DigitsAux_eq_toBaseUInt64DigitsAux
            (64 * n.limbs.size) n #[]
          have h_d_eq : divMod10p19_d = (UInt64.maxPow 10).1 := by
            show UInt64.maxPow10 = (UInt64.maxPow 10).1
            rw [UInt64.maxPow_ten]
          have h_E_eq : UInt64.maxPow10Exp = (UInt64.maxPow 10).2 := by
            rw [show UInt64.maxPow10Exp = (UInt64.maxPow10, UInt64.maxPow10Exp).2 from rfl,
                ← UInt64.maxPow_ten]
          show List.map UInt64.toNat
              (AzNat.trimTrailingZeros (Array.foldl
                (fun acc d => acc ++ UInt64.digitsPaddedTo 10 d UInt64.maxPow10Exp) #[]
                (AzNat.toBase10p19DigitsAux (64 * n.limbs.size) n #[]))).toList
            = Nat.digits ((10 : UInt64).toNat) n.toNat
          rw [h_aux]
          exact h_gen divMod10p19_d UInt64.maxPow10Exp h_d_eq h_E_eq divMod10p19_d_ne
        · rw [ite_eq_right hb10]
          have h_correct := UInt64.maxPow_correct b hb
          have h_P_ne : (UInt64.maxPow b).1 ≠ 0 := by
            intro he
            have : (UInt64.maxPow b).1.toNat = 0 := by rw [he]; rfl
            rw [h_correct.1] at this
            have : 0 < b.toNat ^ (UInt64.maxPow b).2 := by positivity
            omega
          show List.map UInt64.toNat
              (if hP : (UInt64.maxPow b).1 = 0 then #[]
               else AzNat.trimTrailingZeros (Array.foldl
                 (fun acc d => acc ++ UInt64.digitsPaddedTo b d (UInt64.maxPow b).2) #[]
                 (AzNat.toBaseUInt64DigitsAux (UInt64.maxPow b).1 hP
                   (64 * n.limbs.size) n #[]))).toList
            = Nat.digits b.toNat n.toNat
          rw [dite_eq_right h_P_ne]
          exact h_gen (UInt64.maxPow b).1 (UInt64.maxPow b).2 rfl rfl h_P_ne
      -- Now prove the generic-case correctness.
      intro P_arg E_arg h_P_eq h_E_eq hP
      subst h_P_eq
      subst h_E_eq
      have h_correct := UInt64.maxPow_correct b hb
      have h_P_val : (UInt64.maxPow b).1.toNat = b.toNat ^ (UInt64.maxPow b).2 := h_correct.1
      have h_overflow : 2 ^ 64 ≤ b.toNat ^ ((UInt64.maxPow b).2 + 1) := h_correct.2
      have h_E_pos : 1 ≤ (UInt64.maxPow b).2 := by
        by_contra h
        push Not at h
        have : (UInt64.maxPow b).2 = 0 := by omega
        rw [this] at h_overflow
        simp at h_overflow
        have : b.toNat < 2 ^ 64 := UInt64.toNat_lt b
        omega
      have h_2_le_P : 2 ≤ (UInt64.maxPow b).1.toNat := by
        rw [h_P_val]
        calc 2 ≤ b.toNat := hb
          _ = b.toNat ^ 1 := (pow_one _).symm
          _ ≤ b.toNat ^ (UInt64.maxPow b).2 :=
            Nat.pow_le_pow_right (by omega) h_E_pos
      have h_n_fuel : n.toNat < (UInt64.maxPow b).1.toNat ^ (64 * n.limbs.size) := by
        have h_n_lt : n.toNat < 2 ^ (64 * n.limbs.size) := by
          have h_eq : n.toNat = toNatLimbsList n.limbs.toList := rfl
          rw [h_eq]
          have := toNatLimbsList_lt_pow n.limbs.toList
          rw [Array.length_toList] at this
          exact this
        have h_pow_le : 2 ^ (64 * n.limbs.size) ≤
            (UInt64.maxPow b).1.toNat ^ (64 * n.limbs.size) :=
          Nat.pow_le_pow_left (by omega) _
        omega
      set raw := toBaseUInt64DigitsAux (UInt64.maxPow b).1 hP (64 * n.limbs.size) n #[]
        with hraw
      set flat := Array.foldl
        (fun acc d => acc ++ UInt64.digitsPaddedTo b d (UInt64.maxPow b).2) #[] raw with hflat
      set L := (trimTrailingZeros flat).toList.map UInt64.toNat with hL
      -- (a) value: ofDigits b L = n.toNat
      have h_raw_val : Nat.ofDigits (UInt64.maxPow b).1.toNat
          (raw.toList.map UInt64.toNat) = n.toNat := by
        have := ofDigits_toBaseUInt64DigitsAux (UInt64.maxPow b).1 hP h_2_le_P
          (64 * n.limbs.size) n #[] h_n_fuel
        simpa using this
      have h_raw_digit_lt : ∀ x ∈ raw.toList.map UInt64.toNat,
          x < (UInt64.maxPow b).1.toNat := by
        intro x hx
        exact digit_lt_of_toBaseUInt64DigitsAux (UInt64.maxPow b).1 hP
          (64 * n.limbs.size) n #[] (fun y hy => by simp at hy) x hx
      have h_raw_to_list_bound : ∀ d ∈ raw.toList,
          d.toNat < b.toNat ^ (UInt64.maxPow b).2 := by
        intro d hd
        have h_d_mem : d.toNat ∈ raw.toList.map UInt64.toNat := List.mem_map_of_mem hd
        have := h_raw_digit_lt d.toNat h_d_mem
        rw [h_P_val] at this
        exact this
      have h_flat_val : Nat.ofDigits b.toNat (flat.toList.map UInt64.toNat) = n.toNat := by
        rw [hflat, ← Array.foldl_toList]
        rw [ofDigits_foldl_digitsPaddedTo b hb (UInt64.maxPow b).2 #[] raw.toList
          h_raw_to_list_bound]
        show 0 + b.toNat ^ 0 * Nat.ofDigits (b.toNat ^ (UInt64.maxPow b).2)
            (raw.toList.map UInt64.toNat) = n.toNat
        rw [pow_zero, one_mul, Nat.zero_add]
        rw [show Nat.ofDigits (b.toNat ^ (UInt64.maxPow b).2) (raw.toList.map UInt64.toNat)
              = Nat.ofDigits (UInt64.maxPow b).1.toNat (raw.toList.map UInt64.toNat)
              from by rw [h_P_val]]
        exact h_raw_val
      have h_val : Nat.ofDigits b.toNat L = n.toNat := by
        rw [hL, ofDigits_trimTrailingZeros]; exact h_flat_val
      -- (b) bound: each element < b
      have h_flat_lt : ∀ x ∈ flat.toList.map UInt64.toNat, x < b.toNat := by
        rw [hflat, ← Array.foldl_toList]
        exact digit_lt_of_foldl_digitsPaddedTo b hb (UInt64.maxPow b).2 #[] raw.toList
          (fun x hx => by simp at hx)
      have h_lt : ∀ x ∈ L, x < b.toNat := by
        intro x hx
        rw [hL, List.mem_map] at hx
        obtain ⟨u, hu_mem, hu_eq⟩ := hx
        apply h_flat_lt
        rw [List.mem_map]
        exact ⟨u, mem_of_mem_trimTrailingZeros flat u hu_mem, hu_eq⟩
      -- (c) last ≠ 0
      have h_last : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
        rw [hL]
        exact getLast_map_toNat_ne_zero_of_back?_ne_some_zero
          (back?_trimTrailingZeros flat)
      rw [← h_val, Nat.digits_ofDigits b.toNat h_b_pos L h_lt h_last]

end Azurite.AzNat
