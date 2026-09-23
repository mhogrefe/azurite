/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Div.Addback
import Azurite.UInt64.Equiv.Div2By1

namespace Azurite.AzNat

/-! ### Helper lemmas for one body iteration of `schoolbookDivModLimbs.go` -/

/-- Setting a position outside the slice `[loA, loA + n)` does not affect
    `toNatLimbsList ((a.toList.drop loA).take n)`. -/
private lemma toNatLimbsList_set_outside (a : Array UInt64) (loA n i : Nat) (v : UInt64)
    (h_idx : i < a.size) (h_out : i < loA ∨ loA + n ≤ i) :
    toNatLimbsList (((a.set i v).toList.drop loA).take n)
      = toNatLimbsList ((a.toList.drop loA).take n) := by
  congr 1
  rw [Array.toList_set, List.drop_set]
  by_cases hlt : i < loA
  · simp only [hlt, ↓reduceIte]
  · simp only [hlt, ↓reduceIte]
    have hge : loA + n ≤ i := by omega
    rw [List.take_set_of_le (by omega : n ≤ i - loA)]

/-- The single-iteration body of `schoolbookDivModLimbs.go` (extracted as a helper
    function for proof modularity). Given the same trial digit `q_init` that
    `go` would compute, this performs the `subMulLimbs` + `addback` + `set`
    sequence that mutates `a` before the recursive call.

    Returns the post-body array, which equals `a'` in the body of
    `schoolbookDivModLimbs.go` (recursive case). -/
noncomputable def schoolbookDivModLimbs.bodyStep
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 :=
  let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
  let fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2
                 (by rw [subMulLimbs_size]; omega) hB
  fixup.1.set (loA + n + j) fixup.2
    (by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivModLimbs.addback_size _ _ _ _ _ _ _ _ _ _,
          subMulLimbs_size]
      omega)

/-- Size preservation of `bodyStep`. -/
theorem schoolbookDivModLimbs.bodyStep_size
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).size = a.size := by
  unfold schoolbookDivModLimbs.bodyStep
  rw [Array.size_set, schoolbookDivModLimbs.addback_size, subMulLimbs_size]

/-- `bodyStep` preserves any prefix up to `loA + j`. The body mutates the slice
    `[loA + j, loA + j + n + 1)` (via `subMulLimbs`/`addback`) and stores at
    position `loA + n + j` — both lie at index `≥ loA + j`, so the prefix is
    untouched. -/
theorem schoolbookDivModLimbs.bodyStep_toList_take_le
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : m0 ≤ loA + j) :
    (schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.take m0
      = a.toList.take m0 := by
  unfold schoolbookDivModLimbs.bodyStep
  rw [Array.toList_set, List.take_set_of_le (by omega : m0 ≤ loA + n + j),
    schoolbookDivModLimbs.addback_toList_take_le _ _ _ _ _ _ _ _ _ _ m0 hm]
  exact subMulLimbs_toList_take_le a b (loA + j) loB n q_init hSub hB m0 hm

/-- `bodyStep` preserves the suffix from any `m0 ≥ loA + j + n + 1`.  All
    mutations (subMulLimbs over `[loA+j, loA+j+n)`, addback over the same range
    + final-borrow handling at `loA+j+n`, and the set at position `loA+n+j`)
    fall within indices `< loA + j + n + 1`. -/
theorem schoolbookDivModLimbs.bodyStep_toList_drop_ge
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : (loA + j) + n + 1 ≤ m0) :
    (schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop m0
      = a.toList.drop m0 := by
  unfold schoolbookDivModLimbs.bodyStep
  rw [Array.toList_set, List.drop_set, ite_eq_left (by omega : loA + n + j < m0),
    schoolbookDivModLimbs.addback_toList_drop_ge _ _ _ _ _ _ _ _ _ _ m0 (by omega)]
  -- Lift `subMulLimbs_toList_drop` (exact offset `(loA+j)+n+1`) to general `m0`.
  have h_split : ∀ (l : List UInt64),
      l.drop m0 = (l.drop ((loA + j) + n + 1)).drop (m0 - ((loA + j) + n + 1)) :=
    fun l => by rw [List.drop_drop, Nat.add_sub_cancel' hm]
  rw [h_split, subMulLimbs_toList_drop, ← h_split]

/-- The high slot of the post-`bodyStep` array (at index `loA + n + j`) holds
    the corrected quotient digit `fixup.2`. -/
theorem schoolbookDivModLimbs.bodyStep_high_slot
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    let fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2
                   (by rw [subMulLimbs_size]; omega) hB
    have h_idx : loA + n + j <
        (schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).size := by
      rw [schoolbookDivModLimbs.bodyStep_size]; omega
    (schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB)[loA + n + j]'h_idx
      = fixup.2 := by
  unfold schoolbookDivModLimbs.bodyStep
  exact Array.getElem_set_self ..

/-- **Body identity**: composing `subMulLimbs`, `addback`, and the storage
    `set` into `bodyStep`, the `(n+1)`-limb slice value at offset `loA + j`
    transforms with the identity

    `A_top + r.2 * β^(n+1) + b_out * β^n
       = (a' low n limbs) + fixup.2 * B + (topR + r.2) * β^n`

    where `r := subMulLimbs ...`, `fixup := addback r.1 ...`,
    `topR := r.1[loA+j+n]`, `a' := bodyStep ...`, and `b_out` is the final
    addback borrow flag (existential).

    The hypothesis `h_q_safe` is the safety condition that prevents UInt64
    wraparound: when `subMulLimbs` borrows, the trial digit `q_init` has
    `2 ≤ q_init.toNat` (the addback fuel). -/
theorem schoolbookDivModLimbs.bodyStep_toNat
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (h_q_safe : (subMulLimbs a b (loA + j) loB n q_init hSub hB).2 = true →
                  2 ≤ q_init.toNat) :
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    let fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2
                   (by rw [subMulLimbs_size]; omega) hB
    ∃ b_out : Bool,
      toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
          + r.2.toNat * 2 ^ (64 * (n + 1))
          + b_out.toNat * 2 ^ (64 * n)
        = toNatLimbsList
            (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop
              (loA + j)).take n)
          + fixup.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
          + ((r.1[(loA + j) + n]'(by rw [subMulLimbs_size]; omega)).toNat
              + r.2.toNat) * 2 ^ (64 * n) := by
  intro r fixup
  have h_r_size : r.1.size = a.size := subMulLimbs_size _ _ _ _ _ _ _ _
  have h_addback_hyp : (loA + j) + n ≤ r.1.size := by rw [h_r_size]; omega
  -- Step 1: subMulLimbs identity.
  have h_subMul := subMulLimbs_toNat a b (loA + j) loB n q_init hSub hB
  -- Step 2: addback identity.
  have h_addback_eq :=
    schoolbookDivModLimbs.addback_toNat r.1 b (loA + j) loB n q_init r.2 2
      h_addback_hyp hB h_q_safe
  obtain ⟨b_out, h_addback_eq⟩ := h_addback_eq
  refine ⟨b_out, ?_⟩
  -- Unfold bodyStep and identify a' = fixup.1.set (loA + n + j) fixup.2.
  have h_bodyStep_low :
      toNatLimbsList
        (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop
          (loA + j)).take n)
      = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) := by
    unfold schoolbookDivModLimbs.bodyStep
    -- The `set` is at position `loA + n + j`, which is outside `[loA + j, loA + j + n)`.
    have h_fixup_size : fixup.1.size = a.size := by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivModLimbs.addback_size _ _ _ _ _ _ _ _ _ _, h_r_size]
    have h_idx : loA + n + j < fixup.1.size := by rw [h_fixup_size]; omega
    have h_out : loA + n + j < loA + j ∨ (loA + j) + n ≤ loA + n + j := by omega
    exact toNatLimbsList_set_outside fixup.1 (loA + j) n (loA + n + j) fixup.2
      h_idx h_out
  rw [h_bodyStep_low]
  -- Decompose r.1's (n+1)-limb slice as low-n + topR * β^n.
  have h_topR_idx : (loA + j) + n < r.1.size := by rw [h_r_size]; omega
  have h_R1_decomp :
      toNatLimbsList ((r.1.toList.drop (loA + j)).take (n + 1))
        = toNatLimbsList ((r.1.toList.drop (loA + j)).take n)
          + (r.1[(loA + j) + n]'h_topR_idx).toNat * 2 ^ (64 * n) :=
    toNatLimbsList_drop_take_succ r.1 (loA + j) n h_topR_idx
  -- Now combine subMul + addback + decomposition.
  set X := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) with hX_def
  set R1lo := toNatLimbsList ((r.1.toList.drop (loA + j)).take n) with hR1lo_def
  set R1full := toNatLimbsList ((r.1.toList.drop (loA + j)).take (n + 1)) with hR1full_def
  set Flo := toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) with hFlo_def
  set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
  set topR := (r.1[(loA + j) + n]'h_topR_idx).toNat with htopR_def
  -- Rewrite hypotheses.
  change X + r.2.toNat * 2 ^ (64 * (n + 1)) = R1full + q_init.toNat * Z at h_subMul
  change Flo + (1 - b_out.toNat) * 2 ^ (64 * n) + fixup.2.toNat * Z
    = R1lo + (1 - r.2.toNat) * 2 ^ (64 * n) + q_init.toNat * Z at h_addback_eq
  change R1full = R1lo + topR * 2 ^ (64 * n) at h_R1_decomp
  -- Goal in renamed form.
  show X + r.2.toNat * 2 ^ (64 * (n + 1)) + b_out.toNat * 2 ^ (64 * n)
     = Flo + fixup.2.toNat * Z + (topR + r.2.toNat) * 2 ^ (64 * n)
  -- Substitute h_R1_decomp into h_subMul.
  rw [h_R1_decomp] at h_subMul
  -- Power identity: β^(n+1) = β^n * 2^64.
  have h_pow_succ : (2 : Nat) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * (n + 1) = 64 * n + 64 from by ring, Nat.pow_add]
  rw [h_pow_succ] at h_subMul ⊢
  -- Bool indicators: case-split to resolve `(1 - _.toNat)` Nat subtractions.
  cases hr2 : r.2 <;> cases hb_out : b_out <;> simp only [hr2, hb_out,
    Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
    Nat.zero_mul, Nat.one_mul] at h_subMul h_addback_eq ⊢ <;>
  linarith [h_subMul, h_addback_eq]

/-- Variant of `bodyStep_toNat` with the two-correction (Knuth/M-G) safety
    hypotheses, allowing the boundary case `q_init.toNat = 1` (where the
    standard `bodyStep_toNat` would require `2 ≤ q_init.toNat` and fail).
    Identical conclusion to `bodyStep_toNat`, just weaker preconditions. -/
theorem schoolbookDivModLimbs.bodyStep_toNat_two
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (h_safe1 : (subMulLimbs a b (loA + j) loB n q_init hSub hB).2 = true →
                  1 ≤ q_init.toNat)
    (h_safe2 : (subMulLimbs a b (loA + j) loB n q_init hSub hB).2 = true →
                  toNatLimbsList
                    (((subMulLimbs a b (loA + j) loB n q_init hSub hB).1.toList.drop
                      (loA + j)).take n)
                    + toNatLimbsList ((b.toList.drop loB).take n) < 2 ^ (64 * n) →
                  2 ≤ q_init.toNat) :
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    let fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2
                   (by rw [subMulLimbs_size]; omega) hB
    ∃ b_out : Bool,
      toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
          + r.2.toNat * 2 ^ (64 * (n + 1))
          + b_out.toNat * 2 ^ (64 * n)
        = toNatLimbsList
            (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop
              (loA + j)).take n)
          + fixup.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
          + ((r.1[(loA + j) + n]'(by rw [subMulLimbs_size]; omega)).toNat
              + r.2.toNat) * 2 ^ (64 * n) := by
  intro r fixup
  have h_r_size : r.1.size = a.size := subMulLimbs_size _ _ _ _ _ _ _ _
  have h_addback_hyp : (loA + j) + n ≤ r.1.size := by rw [h_r_size]; omega
  have h_subMul := subMulLimbs_toNat a b (loA + j) loB n q_init hSub hB
  have h_addback_eq :=
    schoolbookDivModLimbs.addback_toNat_two r.1 b (loA + j) loB n q_init r.2
      h_addback_hyp hB h_safe1 h_safe2
  obtain ⟨b_out, h_addback_eq⟩ := h_addback_eq
  refine ⟨b_out, ?_⟩
  have h_bodyStep_low :
      toNatLimbsList
        (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop
          (loA + j)).take n)
      = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) := by
    unfold schoolbookDivModLimbs.bodyStep
    have h_fixup_size : fixup.1.size = a.size := by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivModLimbs.addback_size _ _ _ _ _ _ _ _ _ _, h_r_size]
    have h_idx : loA + n + j < fixup.1.size := by rw [h_fixup_size]; omega
    have h_out : loA + n + j < loA + j ∨ (loA + j) + n ≤ loA + n + j := by omega
    exact toNatLimbsList_set_outside fixup.1 (loA + j) n (loA + n + j) fixup.2
      h_idx h_out
  rw [h_bodyStep_low]
  have h_topR_idx : (loA + j) + n < r.1.size := by rw [h_r_size]; omega
  have h_R1_decomp :
      toNatLimbsList ((r.1.toList.drop (loA + j)).take (n + 1))
        = toNatLimbsList ((r.1.toList.drop (loA + j)).take n)
          + (r.1[(loA + j) + n]'h_topR_idx).toNat * 2 ^ (64 * n) :=
    toNatLimbsList_drop_take_succ r.1 (loA + j) n h_topR_idx
  set X := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) with hX_def
  set R1lo := toNatLimbsList ((r.1.toList.drop (loA + j)).take n) with hR1lo_def
  set R1full := toNatLimbsList ((r.1.toList.drop (loA + j)).take (n + 1)) with hR1full_def
  set Flo := toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) with hFlo_def
  set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
  set topR := (r.1[(loA + j) + n]'h_topR_idx).toNat with htopR_def
  change X + r.2.toNat * 2 ^ (64 * (n + 1)) = R1full + q_init.toNat * Z at h_subMul
  change Flo + (1 - b_out.toNat) * 2 ^ (64 * n) + fixup.2.toNat * Z
    = R1lo + (1 - r.2.toNat) * 2 ^ (64 * n) + q_init.toNat * Z at h_addback_eq
  change R1full = R1lo + topR * 2 ^ (64 * n) at h_R1_decomp
  show X + r.2.toNat * 2 ^ (64 * (n + 1)) + b_out.toNat * 2 ^ (64 * n)
     = Flo + fixup.2.toNat * Z + (topR + r.2.toNat) * 2 ^ (64 * n)
  rw [h_R1_decomp] at h_subMul
  have h_pow_succ : (2 : Nat) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * (n + 1) = 64 * n + 64 from by ring, Nat.pow_add]
  rw [h_pow_succ] at h_subMul ⊢
  cases hr2 : r.2 <;> cases hb_out : b_out <;> simp only [hr2, hb_out,
    Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
    Nat.zero_mul, Nat.one_mul] at h_subMul h_addback_eq ⊢ <;>
  linarith [h_subMul, h_addback_eq]

/-! ### Trial-digit (`q_init`) bounds — Knuth/Möller–Granlund analysis

The `schoolbookDivModLimbs.go` body computes a trial quotient digit

  `q_init := if bn1 ≤ A_top then β-1
             else (div2By1 A_top A_next bn1 inv).1`

where `bn1 = b[loB + n - 1]` (normalized: `2^63 ≤ bn1`), `A_top = a[loA + n + j]`,
`A_next = a[loA + (n-1) + j]`, and `inv = reciprocal bn1`. The BZ correctness
proof needs the bound `q_true ≤ q_init.toNat ≤ q_true + 2`, where

  `q_true := ⌊A_local / B⌋` with `A_local := toNatLimbsList ((a.drop (loA+j)).take (n+1))`
  and       `B := toNatLimbsList ((b.drop loB).take n)`.

This is the Knuth/Möller–Granlund "two-correction" bound: under normalization
plus the BZ invariant `A_local < β · B`, the 2-by-1 trial digit (or its cap at
`β-1`) overestimates the true digit by at most 2, which is why the addback
fixup uses fuel = 2.

The proof is a substantial multi-step argument:
  1. Decompose `A_local = A_top · β^n + A_next · β^(n-1) + A_rest` and
     `B = bn1 · β^(n-1) + B_rest`.
  2. The BZ invariant `A_local < β · B` plus normalization gives `A_top ≤ bn1`.
  3. **Cap branch** (`bn1 ≤ A_top`, hence `A_top = bn1`): show `β - 3 ≤ q_true`
     using `A_local ≥ bn1 · β^n` and `B < (bn1 + 1) · β^(n-1)`. Always
     `q_true < β`, so `q_init = β - 1 ∈ [q_true, q_true + 2]`.
  4. **div2By1 branch** (`A_top < bn1`): apply `toNat_div2By1` to get the exact
     2-by-1 quotient `q_init` of `(A_top · β + A_next) / bn1`. Show
     `q_init ≥ q_true` and `q_init - q_true ≤ 2` via the standard
     Knuth-style inequality argument relating the partial quotient to the
     true quotient, leveraging `A_rest < β^(n-1)` and `B_rest < β^(n-1)`.

Pending: actual proof. Statement is sufficient for `bodyStep_BZ` to consume. -/
set_option maxHeartbeats 1000000 in
theorem schoolbookDivModLimbs.q_init_bounds
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (h_n_pos : 0 < n)
    (hbn1_eq : ∃ h_idx : loB + n - 1 < b.size, bn1 = b[loB + n - 1]'h_idx)
    (hbn1_norm : 2 ^ 63 ≤ bn1.toNat)
    (hinv : ∃ h, inv = UInt64.reciprocal bn1 h)
    (h_BZ_local : toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
                    < 2 ^ 64 * toNatLimbsList ((b.toList.drop loB).take n))
    (h_B_pos : 0 < toNatLimbsList ((b.toList.drop loB).take n)) :
    let A_top : UInt64 := a[loA + n + j]'(by omega)
    let A_next : UInt64 := a[loA + (n - 1) + j]'(by omega)
    let q_init : UInt64 :=
      if bn1 ≤ A_top then (0 : UInt64) - 1
      else (UInt64.div2By1 A_top A_next bn1 inv).1
    let A_local : Nat := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
    let B : Nat := toNatLimbsList ((b.toList.drop loB).take n)
    let q_true : Nat := A_local / B
    q_true ≤ q_init.toNat ∧ q_init.toNat ≤ q_true + 2
      ∧ q_init.toNat * B < A_local + 2 ^ (64 * n) := by
  -- Setup: introduce the let-bindings and abbreviate key quantities.
  intro A_top A_next q_init A_local B q_true
  -- Index bounds for A_top and A_next.
  have h_A_top_idx : loA + n + j < a.size := by omega
  have h_A_next_idx : loA + (n - 1) + j < a.size := by omega
  -- β^n decomposition: β^n = β^(n-1) * 2^64.
  have h_n_succ : (n - 1) + 1 = n := by omega
  have h_pow_n : (2 : Nat) ^ (64 * n) = 2 ^ (64 * (n - 1)) * 2 ^ 64 := by
    conv_lhs => rw [show n = (n - 1) + 1 from h_n_succ.symm]
    rw [show 64 * ((n - 1) + 1) = 64 * (n - 1) + 64 from by ring, Nat.pow_add]
  have h_pow_succ : (2 : Nat) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * (n + 1) = 64 * n + 64 from by ring, Nat.pow_add]
  -- Step 1: Decompose A_local = A_top·β^n + A_next·β^(n-1) + A_rest.
  have h_idx_top_eq : loA + n + j = (loA + j) + n := by omega
  have h_idx_next_eq : loA + (n - 1) + j = (loA + j) + (n - 1) := by omega
  -- Decomposition lemma instances with the index equality baked in.
  have h_A_top_eq : (a[loA + n + j]'h_A_top_idx)
      = a[(loA + j) + n]'(h_idx_top_eq ▸ h_A_top_idx) := getElem_congr_idx h_idx_top_eq
  have h_A_next_eq : (a[loA + (n - 1) + j]'h_A_next_idx)
      = a[(loA + j) + (n - 1)]'(h_idx_next_eq ▸ h_A_next_idx) :=
    getElem_congr_idx h_idx_next_eq
  have h_A_decomp1 : A_local
      = toNatLimbsList ((a.toList.drop (loA + j)).take n) + A_top.toNat * 2 ^ (64 * n) := by
    show toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) = _
    have h := toNatLimbsList_drop_take_succ a (loA + j) n (h_idx_top_eq ▸ h_A_top_idx)
    show _ = _ + (a[loA + n + j]'h_A_top_idx).toNat * 2 ^ (64 * n)
    rw [h_A_top_eq]; exact h
  -- Lower n-limb of A: split off A_next at position (n-1).
  set A_lo := toNatLimbsList ((a.toList.drop (loA + j)).take n) with hA_lo_def
  have h_take_eq : ((a.toList.drop (loA + j)).take n)
      = ((a.toList.drop (loA + j)).take ((n - 1) + 1)) := by rw [h_n_succ]
  have h_A_decomp2 : A_lo
      = toNatLimbsList ((a.toList.drop (loA + j)).take (n - 1))
          + A_next.toNat * 2 ^ (64 * (n - 1)) := by
    rw [hA_lo_def, h_take_eq]
    have h := toNatLimbsList_drop_take_succ a (loA + j) (n - 1) (h_idx_next_eq ▸ h_A_next_idx)
    show _ = _ + (a[loA + (n - 1) + j]'h_A_next_idx).toNat * 2 ^ (64 * (n - 1))
    rw [h_A_next_eq]; exact h
  set A_rest := toNatLimbsList ((a.toList.drop (loA + j)).take (n - 1)) with hA_rest_def
  -- Bound A_rest < β^(n-1).
  have h_A_rest_lt : A_rest < 2 ^ (64 * (n - 1)) := by
    have h_pow := toNatLimbsList_lt_pow ((a.toList.drop (loA + j)).take (n - 1))
    have h_len : ((a.toList.drop (loA + j)).take (n - 1)).length ≤ n - 1 :=
      List.length_take_le _ _
    calc A_rest < 2 ^ (64 * ((a.toList.drop (loA + j)).take (n - 1)).length) := h_pow
      _ ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  -- Bound A_lo < β^n.
  have h_A_lo_lt : A_lo < 2 ^ (64 * n) := by
    have h_pow := toNatLimbsList_lt_pow ((a.toList.drop (loA + j)).take n)
    have h_len : ((a.toList.drop (loA + j)).take n).length ≤ n :=
      List.length_take_le _ _
    calc A_lo < 2 ^ (64 * ((a.toList.drop (loA + j)).take n).length) := h_pow
      _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  -- A_top.toNat < 2^64.
  have h_A_top_lt : A_top.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have h_A_next_lt : A_next.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have h_bn1_lt : bn1.toNat < 2 ^ 64 := UInt64.toNat_lt _
  -- Step 2: Decompose B = bn1·β^(n-1) + B_rest.
  have h_B_decomp : B = toNatLimbsList ((b.toList.drop loB).take (n - 1))
                       + bn1.toNat * 2 ^ (64 * (n - 1)) := by
    show toNatLimbsList ((b.toList.drop loB).take n) = _
    obtain ⟨h_bn1_idx, h_bn1_val⟩ := hbn1_eq
    have h_eq_idx : loB + (n - 1) = loB + n - 1 := by omega
    have h := toNatLimbsList_drop_take_succ b loB (n - 1) (h_eq_idx ▸ h_bn1_idx)
    have h_arr : b[loB + (n - 1)]'(h_eq_idx ▸ h_bn1_idx) = b[loB + n - 1]'h_bn1_idx :=
      getElem_congr_idx h_eq_idx
    rw [h_arr, ← h_bn1_val] at h
    have h_take_eq : ((b.toList.drop loB).take n) = ((b.toList.drop loB).take ((n - 1) + 1)) := by
      rw [h_n_succ]
    rw [h_take_eq]
    exact h
  set B_rest := toNatLimbsList ((b.toList.drop loB).take (n - 1)) with hB_rest_def
  -- Bound B_rest < β^(n-1).
  have h_B_rest_lt : B_rest < 2 ^ (64 * (n - 1)) := by
    have h_pow := toNatLimbsList_lt_pow ((b.toList.drop loB).take (n - 1))
    have h_len : ((b.toList.drop loB).take (n - 1)).length ≤ n - 1 :=
      List.length_take_le _ _
    calc B_rest < 2 ^ (64 * ((b.toList.drop loB).take (n - 1)).length) := h_pow
      _ ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  -- Bound B < β^n.
  have h_B_lt : B < 2 ^ (64 * n) := by
    have h_pow := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
    have h_len : ((b.toList.drop loB).take n).length ≤ n :=
      List.length_take_le _ _
    calc B < 2 ^ (64 * ((b.toList.drop loB).take n).length) := h_pow
      _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  -- A_local < 2^(64*(n+1)).
  have h_A_local_lt : A_local < 2 ^ (64 * (n + 1)) := by
    show toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) < _
    have h_pow := toNatLimbsList_lt_pow ((a.toList.drop (loA + j)).take (n + 1))
    have h_len : ((a.toList.drop (loA + j)).take (n + 1)).length ≤ n + 1 :=
      List.length_take_le _ _
    calc toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
        < 2 ^ (64 * ((a.toList.drop (loA + j)).take (n + 1)).length) := h_pow
      _ ≤ 2 ^ (64 * (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  -- Lower bound on B: B ≥ bn1·β^(n-1) ≥ β^n / 2.
  have h_B_ge : bn1.toNat * 2 ^ (64 * (n - 1)) ≤ B := by
    rw [h_B_decomp]; omega
  have h_B_ge_half : 2 ^ (64 * n) ≤ 2 * B := by
    have : 2 ^ 63 * 2 ^ (64 * (n - 1)) ≤ bn1.toNat * 2 ^ (64 * (n - 1)) :=
      Nat.mul_le_mul_right _ hbn1_norm
    have h2 : 2 ^ (64 * n) = 2 * (2 ^ 63 * 2 ^ (64 * (n - 1))) := by
      rw [h_pow_n]
      have : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by norm_num
      rw [this]; ring
    linarith [h_B_ge, this, h2]
  -- BZ invariant: A_local < 2^64 * B, so q_true < 2^64.
  have h_q_true_lt : q_true < 2 ^ 64 := by
    show A_local / B < 2 ^ 64
    rw [Nat.div_lt_iff_lt_mul h_B_pos]
    linarith [h_BZ_local]
  -- A_local ≥ A_top · β^n.
  have h_A_local_ge : A_top.toNat * 2 ^ (64 * n) ≤ A_local := by
    rw [h_A_decomp1]; omega
  -- A_local ≥ A_top · β^n + A_next · β^(n-1).
  have h_A_local_ge2 : A_top.toNat * 2 ^ (64 * n) + A_next.toNat * 2 ^ (64 * (n - 1)) ≤ A_local := by
    rw [h_A_decomp1, h_A_decomp2]; omega
  -- Setup q_init.
  show q_true ≤ q_init.toNat ∧ q_init.toNat ≤ q_true + 2
       ∧ q_init.toNat * B < A_local + 2 ^ (64 * n)
  -- Case split on bn1 ≤ A_top.
  by_cases h_cap : bn1 ≤ A_top
  · -- Cap branch: q_init = β - 1.
    have h_q_init_eq : q_init = (0 : UInt64) - 1 := by
      show (if bn1 ≤ A_top then (0 : UInt64) - 1
            else (UInt64.div2By1 A_top A_next bn1 inv).1) = _
      simp [h_cap]
    have h_q_init_toNat : q_init.toNat = 2 ^ 64 - 1 := by
      rw [h_q_init_eq]; decide
    -- bn1 ≤ A_top in Nat.
    have h_cap_nat : bn1.toNat ≤ A_top.toNat := _root_.UInt64.le_iff_toNat_le.mp h_cap
    -- q_true ≤ q_init = β - 1 since q_true < 2^64.
    have h_q_true_le : q_true ≤ q_init.toNat := by
      rw [h_q_init_toNat]; omega
    -- Third clause: q_init * B < A_local + β^n.
    -- q_init * B = (β-1) * B = β * B - B
    -- We have: A_local ≥ A_top · β^n + A_next · β^(n-1) ≥ bn1 · β^n.
    -- Compute (β-1)*B = (β-1) * (B_rest + bn1·β^(n-1))
    --   = (β-1)*B_rest + (β-1)*bn1·β^(n-1)
    -- Want: (β-1)*B < A_local + β^n
    -- (β-1)*B_rest + (β-1)*bn1·β^(n-1) < A_top·β^n + A_next·β^(n-1) + β^n
    -- A_top·β^n ≥ bn1·β^n = β·bn1·β^(n-1)
    -- So suffices: (β-1)*B_rest + (β-1)*bn1·β^(n-1) < β·bn1·β^(n-1) + β^n
    -- i.e. (β-1)*B_rest < bn1·β^(n-1) + β^n.
    -- (β-1)*B_rest < β · β^(n-1) = β^n. ✓
    have h_third : q_init.toNat * B < A_local + 2 ^ (64 * n) := by
      rw [h_q_init_toNat]
      -- (2^64 - 1) * B = 2^64 * B - B (with 2^64 ≥ 1)
      -- B ≤ B_rest + bn1·β^(n-1)
      -- bn1·β^n = bn1 · β · β^(n-1) ≥ A_top · β^n? No, bn1 ≤ A_top.
      -- So A_top · β^n ≥ bn1 · β^n.
      have h_bn1_pow : bn1.toNat * 2 ^ (64 * n) ≤ A_top.toNat * 2 ^ (64 * n) :=
        Nat.mul_le_mul_right _ h_cap_nat
      -- A_local ≥ A_top * β^n ≥ bn1 * β^n.
      have h_A_local_ge_bn1 : bn1.toNat * 2 ^ (64 * n) ≤ A_local :=
        le_trans h_bn1_pow h_A_local_ge
      -- B ≤ bn1·β^(n-1) + β^(n-1) - 1 < (bn1+1) · β^(n-1).
      have h_B_ub : B < (bn1.toNat + 1) * 2 ^ (64 * (n - 1)) := by
        rw [h_B_decomp]
        calc B_rest + bn1.toNat * 2 ^ (64 * (n - 1))
            < 2 ^ (64 * (n - 1)) + bn1.toNat * 2 ^ (64 * (n - 1)) := by omega
          _ = (bn1.toNat + 1) * 2 ^ (64 * (n - 1)) := by ring
      -- (2^64 - 1) * B < (2^64 - 1) * (bn1 + 1) · β^(n-1)
      -- We claim: (2^64 - 1) * B < bn1 · β^n + β^n
      -- (2^64 - 1) * (bn1 + 1) · β^(n-1) ≤ bn1 · β^n + β^n
      -- Expand: (2^64 - 1) * (bn1 + 1) ≤ bn1 · 2^64 + 2^64 - bn1 - 1 + 2^64 ?
      -- Actually: (2^64 - 1)(bn1+1) = 2^64·bn1 + 2^64 - bn1 - 1.
      -- And bn1·2^64 + 2^64 = 2^64·bn1 + 2^64.
      -- So (2^64 - 1)(bn1+1) ≤ bn1·2^64 + 2^64 iff -bn1 - 1 ≤ 0. ✓
      -- Then (2^64-1)(bn1+1)·β^(n-1) ≤ (bn1·2^64 + 2^64)·β^(n-1) = bn1·β^n + β^n.
      have h_expand : (2^64 - 1) * (bn1.toNat + 1) ≤ bn1.toNat * 2^64 + 2^64 := by
        have hexp : (2^64 - 1) * (bn1.toNat + 1)
            = (2^64 - 1) * bn1.toNat + (2^64 - 1) := by ring
        have h1 : (2^64 - 1) * bn1.toNat = bn1.toNat * 2^64 - bn1.toNat := by
          have hh : (2^64 - 1) * bn1.toNat = 2^64 * bn1.toNat - 1 * bn1.toNat :=
            by rw [Nat.sub_mul]
          rw [hh]; ring_nf
        have h_bn1_le : bn1.toNat ≤ 2^64 := by omega
        rw [hexp, h1]
        have h_mul_ge : bn1.toNat ≤ bn1.toNat * 2^64 := by
          have := Nat.le_mul_of_pos_right bn1.toNat (show 0 < 2^64 by norm_num)
          linarith
        omega
      have h_calc : (2^64 - 1) * ((bn1.toNat + 1) * 2 ^ (64 * (n - 1)))
                      ≤ bn1.toNat * 2 ^ (64 * n) + 2 ^ (64 * n) := by
        calc (2^64 - 1) * ((bn1.toNat + 1) * 2 ^ (64 * (n - 1)))
            = ((2^64 - 1) * (bn1.toNat + 1)) * 2 ^ (64 * (n - 1)) := by ring
          _ ≤ (bn1.toNat * 2^64 + 2^64) * 2 ^ (64 * (n - 1)) :=
              Nat.mul_le_mul_right _ h_expand
          _ = bn1.toNat * (2 ^ (64 * (n - 1)) * 2^64) + 2 ^ (64 * (n - 1)) * 2^64 := by ring
          _ = bn1.toNat * 2 ^ (64 * n) + 2 ^ (64 * n) := by rw [← h_pow_n]
      have h_q_init_mul : (2^64 - 1) * B < (2^64 - 1) * ((bn1.toNat + 1) * 2 ^ (64 * (n - 1))) := by
        have h_pos : 0 < (2^64 - 1 : Nat) := by norm_num
        exact Nat.mul_lt_mul_of_pos_left h_B_ub h_pos
      linarith [h_q_init_mul, h_calc, h_A_local_ge_bn1]
    -- Second clause: q_init ≤ q_true + 2.
    -- q_init = 2^64 - 1. Need: 2^64 - 1 ≤ q_true + 2, i.e., q_true ≥ 2^64 - 3.
    -- Standard argument: q_true · B ≤ A_local, (q_true + 1) · B > A_local.
    -- We'll use a contradiction-style argument:
    -- Suppose q_true + 2 < q_init = 2^64 - 1, i.e., q_true ≤ 2^64 - 4.
    -- Then (q_true + 3) ≤ 2^64 - 1. And (q_true + 1) · B > A_local, so
    -- (q_true + 3) · B > A_local + 2B. Combined with (q_init) * B < A_local + β^n
    -- (which is the third clause we just proved): (q_true + 3) · B ≤ q_init · B
    -- (since q_true + 3 ≤ q_init), so (q_true+3) · B < A_local + β^n.
    -- Combining: 2B < β^n. But 2B ≥ β^n by normalization. Contradiction.
    have h_q_true_div : q_true * B ≤ A_local := Nat.div_mul_le_self _ _
    have h_q_true_succ : A_local < (q_true + 1) * B := by
      show A_local < (A_local / B + 1) * B
      have h := Nat.lt_mul_div_succ A_local h_B_pos
      linarith [h, show B * (A_local / B + 1) = (A_local / B + 1) * B from by ring]
    have h_q_init_le : q_init.toNat ≤ q_true + 2 := by
      by_contra h_contra
      push Not at h_contra
      -- h_contra : q_true + 2 < q_init.toNat, so q_true + 3 ≤ q_init.toNat.
      have h_q3_le_qi : q_true + 3 ≤ q_init.toNat := by omega
      -- (q_true + 3) * B ≤ q_init.toNat * B.
      have h_mul3 : (q_true + 3) * B ≤ q_init.toNat * B :=
        Nat.mul_le_mul_right _ h_q3_le_qi
      -- (q_true + 3) * B = (q_true + 1) * B + 2 * B > A_local + 2 * B.
      have h_q3_gt : A_local + 2 * B < (q_true + 3) * B := by
        have h_expand : (q_true + 3) * B = (q_true + 1) * B + 2 * B := by ring
        linarith [h_q_true_succ, h_expand]
      -- q_init.toNat * B < A_local + 2 ^ (64 * n).
      have h_qi_lt : q_init.toNat * B < A_local + 2 ^ (64 * n) := h_third
      -- Combined: A_local + 2 * B < A_local + β^n, so 2 * B < β^n. Contradicts 2B ≥ β^n.
      have h_2B_lt : 2 * B < 2 ^ (64 * n) := by linarith [h_q3_gt, h_mul3, h_qi_lt]
      linarith [h_B_ge_half, h_2B_lt]
    exact ⟨h_q_true_le, h_q_init_le, h_third⟩
  · -- div2By1 branch: A_top < bn1.
    have h_top_lt : A_top.toNat < bn1.toNat := by
      have : ¬ bn1.toNat ≤ A_top.toNat := fun h => h_cap (_root_.UInt64.le_iff_toNat_le.mpr h)
      omega
    have h_q_init_eq : q_init = (UInt64.div2By1 A_top A_next bn1 inv).1 := by
      show (if bn1 ≤ A_top then (0 : UInt64) - 1
            else (UInt64.div2By1 A_top A_next bn1 inv).1) = _
      simp [h_cap]
    -- Apply toNat_div2By1.
    obtain ⟨h_inv_h, h_inv_eq⟩ := hinv
    have h_div2 := _root_.UInt64.toNat_div2By1 A_top A_next bn1 inv hbn1_norm h_top_lt h_inv_eq
    obtain ⟨h_div2_eq, h_div2_lt⟩ := h_div2
    -- Let q := (div2By1 ...).1.toNat, r := (div2By1 ...).2.toNat.
    -- h_div2_eq: q * bn1 + r = A_top * β + A_next.
    -- h_div2_lt: r < bn1.
    set q := (UInt64.div2By1 A_top A_next bn1 inv).1.toNat with hq_def
    set r := (UInt64.div2By1 A_top A_next bn1 inv).2.toNat with hr_def
    have h_q_init_toNat : q_init.toNat = q := by rw [h_q_init_eq]
    have h_q_lt : q < 2 ^ 64 := UInt64.toNat_lt _
    -- Key: q * bn1 ≤ A_top * 2^64 + A_next < (q+1) * bn1.
    have h_q_mul_le : q * bn1.toNat ≤ A_top.toNat * 2 ^ 64 + A_next.toNat := by
      omega
    have h_q_succ_mul_gt : A_top.toNat * 2 ^ 64 + A_next.toNat < (q + 1) * bn1.toNat := by
      have : (q + 1) * bn1.toNat = q * bn1.toNat + bn1.toNat := by ring
      omega
    -- Step: q * B ≤ A_local + q * B_rest.
    -- q * B = q * (bn1 · β^(n-1) + B_rest) = q * bn1 · β^(n-1) + q * B_rest
    -- ≤ (A_top · β + A_next) · β^(n-1) + q * B_rest
    -- = A_top · β^n + A_next · β^(n-1) + q * B_rest
    -- ≤ A_local + q * B_rest. ✓
    have h_q_B_le : q * B ≤ A_local + q * B_rest := by
      rw [h_B_decomp]
      have h_expand : q * (B_rest + bn1.toNat * 2 ^ (64 * (n - 1)))
                      = q * B_rest + q * bn1.toNat * 2 ^ (64 * (n - 1)) := by ring
      rw [h_expand]
      have h_step1 : q * bn1.toNat * 2 ^ (64 * (n - 1))
                       ≤ (A_top.toNat * 2 ^ 64 + A_next.toNat) * 2 ^ (64 * (n - 1)) :=
        Nat.mul_le_mul_right _ h_q_mul_le
      have h_step2 : (A_top.toNat * 2 ^ 64 + A_next.toNat) * 2 ^ (64 * (n - 1))
                       = A_top.toNat * 2 ^ (64 * n) + A_next.toNat * 2 ^ (64 * (n - 1)) := by
        rw [h_pow_n]; ring
      linarith [h_step1, h_step2, h_A_local_ge2]
    -- Third clause: q * B < A_local + β^n.
    -- q * B_rest < q * β^(n-1) ≤ (β - 1) * β^(n-1) ≤ β^n.
    have h_third : q_init.toNat * B < A_local + 2 ^ (64 * n) := by
      rw [h_q_init_toNat]
      -- q * B_rest ≤ q * (β^(n-1) - 1) < q * β^(n-1) ≤ (2^64 - 1) * β^(n-1) ≤ β^n.
      have h_qBr_lt : q * B_rest < 2 ^ (64 * n) := by
        -- q * B_rest ≤ (2^64 - 1) * (β^(n-1) - 1) < 2^64 * β^(n-1) = β^n.
        have h_q_le : q ≤ 2^64 - 1 := by omega
        have h_Br_le : B_rest ≤ 2 ^ (64 * (n - 1)) - 1 := by omega
        have h_pow_pos : 0 < 2 ^ (64 * (n - 1)) := Nat.two_pow_pos _
        calc q * B_rest ≤ (2^64 - 1) * (2 ^ (64 * (n - 1)) - 1) :=
              Nat.mul_le_mul h_q_le h_Br_le
          _ < 2^64 * 2 ^ (64 * (n - 1)) := by
              have : (2^64 - 1) * (2 ^ (64 * (n - 1)) - 1)
                  ≤ 2^64 * 2 ^ (64 * (n - 1)) - 2^64 := by
                have h1 : (2^64 - 1) * (2 ^ (64 * (n - 1)) - 1)
                    ≤ (2^64 - 1) * 2 ^ (64 * (n - 1)) := by
                  exact Nat.mul_le_mul_left _ (by omega)
                have h2 : (2^64 - 1) * 2 ^ (64 * (n - 1))
                    = 2^64 * 2 ^ (64 * (n - 1)) - 2 ^ (64 * (n - 1)) := by
                  rw [Nat.sub_mul, Nat.one_mul]
                have h3 : 2^64 ≤ 2^64 * 2 ^ (64 * (n - 1)) :=
                  Nat.le_mul_of_pos_right _ h_pow_pos
                omega
              have h_pos_bound : (2^64 : Nat) > 0 := by norm_num
              omega
          _ = 2 ^ (64 * (n - 1)) * 2 ^ 64 := by ring
          _ = 2 ^ (64 * n) := by rw [← h_pow_n]
      linarith [h_q_B_le, h_qBr_lt]
    -- Lower bound: q_init ≥ q_true.
    -- From q * bn1 + r = A_top * β + A_next, with r ≥ 0:
    -- q * bn1 ≥ A_top * β + A_next - (bn1 - 1) = A_top * β + A_next - bn1 + 1
    -- Need: (q + 1) * B > A_local.
    -- (q + 1) * B ≥ (q + 1) * bn1·β^(n-1) = (q · bn1 + bn1)·β^(n-1)
    -- ≥ (A_top·β + A_next - bn1 + 1 + bn1)·β^(n-1)
    -- = (A_top·β + A_next + 1)·β^(n-1)
    -- = A_top·β^n + A_next·β^(n-1) + β^(n-1)
    -- > A_top·β^n + A_next·β^(n-1) + A_rest = A_local. ✓
    have h_q_lower : q_true ≤ q_init.toNat := by
      rw [h_q_init_toNat]
      -- Show A_local < (q + 1) * B, then q_true = A_local / B < q + 1, so q_true ≤ q.
      have h_qbn1_ge : A_top.toNat * 2 ^ 64 + A_next.toNat - bn1.toNat + 1 ≤ q * bn1.toNat + 1 := by
        have h_r_lt_bn1 : r < bn1.toNat := h_div2_lt
        omega
      -- (q + 1) * B ≥ (q + 1) * (bn1 · β^(n-1)) = (q*bn1 + bn1) · β^(n-1).
      have h_qB_lower : (q + 1) * B ≥ (q * bn1.toNat + bn1.toNat) * 2 ^ (64 * (n - 1)) := by
        rw [h_B_decomp]
        have h_expand : (q + 1) * (B_rest + bn1.toNat * 2 ^ (64 * (n - 1)))
            = (q + 1) * B_rest + (q * bn1.toNat + bn1.toNat) * 2 ^ (64 * (n - 1)) := by ring
        rw [h_expand]; omega
      -- q*bn1 + bn1 ≥ A_top·β + A_next + 1.
      have h_step : q * bn1.toNat + bn1.toNat ≥ A_top.toNat * 2 ^ 64 + A_next.toNat + 1 := by
        omega
      -- (q + 1) * B ≥ (A_top·β + A_next + 1) · β^(n-1)
      --             = A_top·β^n + A_next·β^(n-1) + β^(n-1).
      have h_step2 : (A_top.toNat * 2 ^ 64 + A_next.toNat + 1) * 2 ^ (64 * (n - 1))
            ≤ (q * bn1.toNat + bn1.toNat) * 2 ^ (64 * (n - 1)) :=
        Nat.mul_le_mul_right _ h_step
      have h_step3 : (A_top.toNat * 2 ^ 64 + A_next.toNat + 1) * 2 ^ (64 * (n - 1))
          = A_top.toNat * 2 ^ (64 * n) + A_next.toNat * 2 ^ (64 * (n - 1))
              + 2 ^ (64 * (n - 1)) := by
        rw [h_pow_n]; ring
      -- A_local = A_top·β^n + A_next·β^(n-1) + A_rest, A_rest < β^(n-1).
      have h_A_full : A_local = A_top.toNat * 2 ^ (64 * n)
                                + A_next.toNat * 2 ^ (64 * (n - 1)) + A_rest := by
        rw [h_A_decomp1, h_A_decomp2]; ring
      have h_A_local_lt_qB : A_local < (q + 1) * B := by
        calc A_local = A_top.toNat * 2 ^ (64 * n) + A_next.toNat * 2 ^ (64 * (n - 1))
                        + A_rest := h_A_full
          _ < A_top.toNat * 2 ^ (64 * n) + A_next.toNat * 2 ^ (64 * (n - 1))
                + 2 ^ (64 * (n - 1)) := by omega
          _ = (A_top.toNat * 2 ^ 64 + A_next.toNat + 1) * 2 ^ (64 * (n - 1)) := by
                rw [h_step3]
          _ ≤ (q * bn1.toNat + bn1.toNat) * 2 ^ (64 * (n - 1)) := h_step2
          _ ≤ (q + 1) * B := h_qB_lower
      -- q_true = A_local / B < q + 1.
      show A_local / B ≤ q
      have h_div_lt : A_local / B < q + 1 := by
        rw [Nat.div_lt_iff_lt_mul h_B_pos]
        linarith [h_A_local_lt_qB,
                   show (q + 1) * B = B * (q + 1) from by ring]
      omega
    -- Upper bound: q_init ≤ q_true + 2.
    -- From third clause: q * B < A_local + β^n.
    -- (q_true + 1) * B > A_local, so q * B - q_true * B < A_local + β^n - A_local = β^n.
    -- (q - q_true) * B < β^n + B (more carefully).
    -- Actually: if q ≥ q_true + 3, then (q_true + 3) * B ≤ q * B < A_local + β^n.
    -- (q_true + 3) * B = (q_true + 1) * B + 2 * B > A_local + 2 * B.
    -- So A_local + 2 * B < A_local + β^n, i.e., 2 * B < β^n. Contradicts 2B ≥ β^n.
    have h_q_true_div : q_true * B ≤ A_local := Nat.div_mul_le_self _ _
    have h_q_true_succ : A_local < (q_true + 1) * B := by
      show A_local < (A_local / B + 1) * B
      have h := Nat.lt_mul_div_succ A_local h_B_pos
      linarith [h, show B * (A_local / B + 1) = (A_local / B + 1) * B from by ring]
    have h_q_init_le : q_init.toNat ≤ q_true + 2 := by
      rw [h_q_init_toNat]
      by_contra h_contra
      push Not at h_contra
      have h_q3_le_qi : q_true + 3 ≤ q := by omega
      have h_mul3 : (q_true + 3) * B ≤ q * B :=
        Nat.mul_le_mul_right _ h_q3_le_qi
      have h_q3_gt : A_local + 2 * B < (q_true + 3) * B := by
        have h_expand : (q_true + 3) * B = (q_true + 1) * B + 2 * B := by ring
        linarith [h_q_true_succ, h_expand]
      have h_qi_lt : q * B < A_local + 2 ^ (64 * n) := by
        have := h_third; rw [h_q_init_toNat] at this; exact this
      have h_2B_lt : 2 * B < 2 ^ (64 * n) := by linarith [h_q3_gt, h_mul3, h_qi_lt]
      linarith [h_B_ge_half, h_2B_lt]
    exact ⟨h_q_lower, h_q_init_le, h_third⟩

/-! ### `bodyStep_BZ` — one-step BZ invariant preservation -/

/-- **BZ invariant preserved by one body iteration**.

    Pre: BZ invariant on the `(n+1)`-limb dividend slice at offset `loA + j`
    (i.e., `A_local < β · B`).

    Post (using the trial digit `q_init` that `schoolbookDivModLimbs.go` would compute):
      - The post-bodyStep slice's low `n` limbs hold the new remainder `R < B`.
      - The high slot at `loA + n + j` holds the corrected quotient digit.
      - The value identity
          `A_local = digit_stored.toNat · B + R`
        holds, witnessing the standard division identity at this step.

    Combined with prefix/suffix preservation (`bodyStep_toList_take_le`,
    `bodyStep_toList_drop_ge`), this is exactly the inductive hypothesis the
    `j+1` case of `go_toNat` needs.

    Proof sketch:
      1. Let `q_init` be the trial digit. By `q_init_bounds`,
         `q_true ≤ q_init.toNat ≤ q_true + 2` where `q_true = A_local / B`.
      2. The `subMulLimbs ... q_init` step computes `A_local - q_init · B`
         (interpreted as signed); the borrow flag `r.2` records whether the
         result is negative.
      3. `addback ... fuel = 2` adds back `B` up to twice, producing the
         corrected `(R, fixup.2)` with `0 ≤ R < B` and
         `fixup.2.toNat = q_init.toNat - (number of addbacks) = q_true`.
      4. `bodyStep_toNat` then gives the value identity.
      5. The `q_init.toNat ≤ q_true + 2` bound ensures the addback fuel is
         sufficient (the safety hypothesis `h_q_safe` of `bodyStep_toNat`
         demands `r.2 = true → 2 ≤ q_init.toNat`, automatic from
         `q_true ≥ 1` only when there's an actual borrow and `q_true ≥ 0`;
         care needed at `q_true = 0`).

    Pending: full proof tying together `q_init_bounds`, `subMulLimbs_toNat`,
    `addback_toNat`, and the bodyStep identity. -/
theorem schoolbookDivModLimbs.bodyStep_BZ
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n)
    (hbn1_eq : ∃ h_idx : loB + n - 1 < b.size, bn1 = b[loB + n - 1]'h_idx)
    (hbn1_norm : 2 ^ 63 ≤ bn1.toNat)
    (hinv : ∃ h, inv = UInt64.reciprocal bn1 h)
    (h_BZ_local : toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
                    < 2 ^ 64 * toNatLimbsList ((b.toList.drop loB).take n))
    (h_B_pos : 0 < toNatLimbsList ((b.toList.drop loB).take n)) :
    let A_top : UInt64 := a[loA + n + j]'(by omega)
    let A_next : UInt64 := a[loA + (n - 1) + j]'(by omega)
    let q_init : UInt64 :=
      if bn1 ≤ A_top then (0 : UInt64) - 1
      else (UInt64.div2By1 A_top A_next bn1 inv).1
    let a' := schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB
    have h_idx : loA + n + j < a'.size := by
      rw [schoolbookDivModLimbs.bodyStep_size]; omega
    -- Post-bodyStep array satisfies:
    -- (1) low n limbs at offset (loA + j) form the remainder R < B,
    -- (2) high slot at (loA + n + j) is the true quotient digit,
    -- (3) value identity A_local = digit · B + R.
    toNatLimbsList ((a'.toList.drop (loA + j)).take n)
        < toNatLimbsList ((b.toList.drop loB).take n)
      ∧ toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
          = (a'[loA + n + j]'h_idx).toNat
              * toNatLimbsList ((b.toList.drop loB).take n)
            + toNatLimbsList ((a'.toList.drop (loA + j)).take n) := by
  -- Combine q_init_bounds + subMulLimbs_toNat + addback_toNat_two +
  -- bodyStep_toNat_two (see proof sketch above).
  intro A_top A_next q_init a' h_idx
  -- Set up named values.
  set X := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) with hX_def
  set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
  set q_true := X / Z with hq_true_def
  -- Apply q_init_bounds.
  have h_q_bounds := schoolbookDivModLimbs.q_init_bounds a b loA loB n j bn1 inv hSub
    h_n_pos hbn1_eq hbn1_norm hinv h_BZ_local h_B_pos
  simp only at h_q_bounds
  -- The let-bindings in q_init_bounds should match q_init.
  change q_true ≤ q_init.toNat ∧ q_init.toNat ≤ q_true + 2
    ∧ q_init.toNat * Z < X + 2 ^ (64 * n) at h_q_bounds
  obtain ⟨hq_lo, hq_hi, hq_delta⟩ := h_q_bounds
  -- subMulLimbs result.
  set r := subMulLimbs a b (loA + j) loB n q_init hSub hB with hr_def
  have h_r_size : r.1.size = a.size := subMulLimbs_size _ _ _ _ _ _ _ _
  have h_topR_idx : (loA + j) + n < r.1.size := by rw [h_r_size]; omega
  set R1lo := toNatLimbsList ((r.1.toList.drop (loA + j)).take n) with hR1lo_def
  set R1full := toNatLimbsList ((r.1.toList.drop (loA + j)).take (n + 1)) with hR1full_def
  set topR := (r.1[(loA + j) + n]'h_topR_idx).toNat with htopR_def
  have h_subMul := subMulLimbs_toNat a b (loA + j) loB n q_init hSub hB
  rw [← hr_def] at h_subMul
  change X + r.2.toNat * 2 ^ (64 * (n + 1)) = R1full + q_init.toNat * Z at h_subMul
  -- Decompose R1full = R1lo + topR * β^n.
  have h_R1_decomp : R1full = R1lo + topR * 2 ^ (64 * n) :=
    toNatLimbsList_drop_take_succ r.1 (loA + j) n h_topR_idx
  -- Power identity: β^(n+1) = β^n * 2^64.
  have h_pow_succ : (2 : Nat) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * (n + 1) = 64 * n + 64 from by ring, Nat.pow_add]
  -- Useful bounds on slices.
  have h_R1lo_lt : R1lo < 2 ^ (64 * n) := by
    have h_pow := toNatLimbsList_lt_pow ((r.1.toList.drop (loA + j)).take n)
    have h_len : ((r.1.toList.drop (loA + j)).take n).length = n := by
      rw [List.length_take, List.length_drop, Array.length_toList, h_r_size]
      omega
    rw [h_len] at h_pow; exact h_pow
  have h_Z_lt : Z < 2 ^ (64 * n) := by
    have h_pow := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
    have h_len : ((b.toList.drop loB).take n).length = n := by
      rw [List.length_take, List.length_drop, Array.length_toList]
      omega
    rw [h_len] at h_pow; exact h_pow
  have h_X_lt : X < 2 ^ (64 * (n + 1)) := by
    have h_pow := toNatLimbsList_lt_pow ((a.toList.drop (loA + j)).take (n + 1))
    have h_len : ((a.toList.drop (loA + j)).take (n + 1)).length = n + 1 := by
      rw [List.length_take, List.length_drop, Array.length_toList]
      omega
    rw [h_len] at h_pow; exact h_pow
  have h_R1full_lt : R1full < 2 ^ (64 * (n + 1)) := by
    have h_pow := toNatLimbsList_lt_pow ((r.1.toList.drop (loA + j)).take (n + 1))
    have h_len : ((r.1.toList.drop (loA + j)).take (n + 1)).length = n + 1 := by
      rw [List.length_take, List.length_drop, Array.length_toList, h_r_size]
      omega
    rw [h_len] at h_pow; exact h_pow
  -- Standard divmod: q_true * Z ≤ X < (q_true + 1) * Z, and X = q_true * Z + (X mod Z).
  have h_qtrue_mul : q_true * Z + X % Z = X := by
    rw [hq_true_def]
    have := Nat.div_add_mod X Z
    linarith [Nat.div_add_mod X Z, Nat.mul_comm Z (X / Z)]
  have h_X_mod_lt : X % Z < Z := Nat.mod_lt _ h_B_pos
  -- Prove h_safe1: r.2 = true → 1 ≤ q_init.toNat.
  have h_safe1 : r.2 = true → 1 ≤ q_init.toNat := by
    intro h_borrow
    -- r.2 = true: subMul gives X + 1 * β^(n+1) = R1full + q_init * Z.
    -- So q_init * Z = X + β^(n+1) - R1full ≥ β^(n+1) - R1full ≥ 1 (since R1full < β^(n+1)).
    -- Combined with Z > 0, q_init ≥ 1.
    rw [h_borrow] at h_subMul
    simp only [Bool.toNat_true, Nat.one_mul] at h_subMul
    have h_qZ_pos : 0 < q_init.toNat * Z := by
      have : R1full + q_init.toNat * Z = X + 2 ^ (64 * (n + 1)) := by linarith
      have : q_init.toNat * Z = X + 2 ^ (64 * (n + 1)) - R1full := by omega
      rw [this]
      have : R1full < X + 2 ^ (64 * (n + 1)) := by
        have := Nat.zero_le X; linarith
      omega
    by_contra h_not
    push Not at h_not
    have h_q_zero : q_init.toNat = 0 := by omega
    rw [h_q_zero, Nat.zero_mul] at h_qZ_pos
    exact Nat.lt_irrefl _ h_qZ_pos
  -- Prove h_safe2: r.2 = true → R1lo + Z < β^n → 2 ≤ q_init.toNat.
  have h_safe2 : r.2 = true →
      R1lo + Z < 2 ^ (64 * n) → 2 ≤ q_init.toNat := by
    intro h_borrow h_lo_lt
    -- Suppose q_init = 1. Get contradiction.
    have h_q1 := h_safe1 h_borrow
    by_contra h_q_lt
    push Not at h_q_lt
    have hq_eq1 : q_init.toNat = 1 := by omega
    -- From q_init_bounds with q_init = 1: q_true ≤ 1.
    have h_qtrue_le1 : q_true ≤ 1 := by rw [hq_eq1] at hq_lo; exact hq_lo
    -- From subMul (r.2 = true, q_init = 1): X + β^(n+1) = R1full + Z.
    rw [h_borrow] at h_subMul
    simp only [Bool.toNat_true, Nat.one_mul, hq_eq1, Nat.one_mul] at h_subMul
    -- So R1full = X + β^(n+1) - Z.
    -- Z > X means q_true = 0. Actually from r.2 = true with q_init = 1 we have Z > X
    -- (since X + β^(n+1) = R1full + Z < β^(n+1) + Z, so X < Z).
    have h_X_lt_Z : X < Z := by
      have h1 : R1full + Z = X + 2 ^ (64 * (n + 1)) := by linarith
      -- R1full < β^(n+1), so Z > X.
      omega
    have h_qtrue_zero : q_true = 0 := by
      rw [hq_true_def]; exact Nat.div_eq_of_lt h_X_lt_Z
    -- R1full = X + β^(n+1) - Z. Now decompose.
    rw [h_R1_decomp] at h_subMul
    -- X + β^(n+1) = R1lo + topR * β^n + Z.
    -- So R1lo + topR * β^n = X + β^(n+1) - Z.
    -- Since Z < β^n, β^(n+1) - Z > β^(n+1) - β^n = (β-1) * β^n.
    -- Hence R1lo + topR * β^n > (β-1) * β^n, and since R1lo < β^n,
    -- topR ≥ β - 1, so topR = β - 1 (topR < β = 2^64 since it's a UInt64).
    have h_topR_lt : topR < 2 ^ 64 := by
      rw [htopR_def]
      exact (r.1[(loA + j) + n]'h_topR_idx).toNat_lt
    -- Compute: R1lo + topR * β^n = X + β^(n+1) - Z.
    have h_eq1 : R1lo + topR * 2 ^ (64 * n) = X + 2 ^ (64 * (n + 1)) - Z := by
      have : X + 2 ^ (64 * (n + 1)) = R1lo + topR * 2 ^ (64 * n) + Z := by linarith
      omega
    -- (β-1) * β^n ≤ R1lo + topR * β^n.
    have h_lower : (2 ^ 64 - 1) * 2 ^ (64 * n) ≤ R1lo + topR * 2 ^ (64 * n) := by
      rw [h_eq1, h_pow_succ]
      have h_Z_le_pow_n : Z ≤ 2 ^ (64 * n) := le_of_lt h_Z_lt
      have hX_nn : 0 ≤ X := Nat.zero_le _
      have h_pow_nn : 1 ≤ (2 : Nat) ^ 64 := Nat.two_pow_pos 64
      have h_eq_calc : (2 ^ 64 - 1) * 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * n) - 2 ^ (64 * n) := by
        rw [Nat.sub_mul, Nat.one_mul]
      rw [h_eq_calc]
      have h_pow_n_le : 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
        Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 64)
      omega
    -- So topR ≥ 2^64 - 1, hence topR = 2^64 - 1.
    have h_topR_ge : 2 ^ 64 - 1 ≤ topR := by
      by_contra h
      push Not at h
      -- topR ≤ 2^64 - 2.
      have h_topR_le : topR ≤ 2 ^ 64 - 2 := by omega
      have : R1lo + topR * 2 ^ (64 * n) < (2 ^ 64 - 1) * 2 ^ (64 * n) := by
        have h1 : topR * 2 ^ (64 * n) ≤ (2 ^ 64 - 2) * 2 ^ (64 * n) :=
          Nat.mul_le_mul_right _ h_topR_le
        have h2 : (2 ^ 64 - 2) * 2 ^ (64 * n) + 2 ^ (64 * n) ≤ (2 ^ 64 - 1) * 2 ^ (64 * n) := by
          have : (2 ^ 64 - 1) * 2 ^ (64 * n) = (2 ^ 64 - 2) * 2 ^ (64 * n) + 2 ^ (64 * n) := by
            have h_two_le : (2 : Nat) ≤ 2 ^ 64 := by norm_num
            rw [show (2 ^ 64 - 1) = (2 ^ 64 - 2) + 1 from by omega]
            rw [Nat.add_mul, Nat.one_mul]
          linarith
        linarith
      linarith
    have h_topR_eq : topR = 2 ^ 64 - 1 := by omega
    -- Then R1lo = X + β^(n+1) - Z - (2^64 - 1) * β^n = X + β^n - Z.
    have h_R1lo_eq : R1lo = X + 2 ^ (64 * n) - Z := by
      have h_two_le : (2 : Nat) ≤ 2 ^ 64 := by norm_num
      have h_pow_n_pos : 0 < (2 : Nat) ^ (64 * n) := Nat.two_pow_pos _
      have h_pow_64_pos : 0 < (2 : Nat) ^ 64 := Nat.two_pow_pos _
      -- (2^64 - 1) * β^n = β^(n+1) - β^n.
      have h_calc : (2 ^ 64 - 1) * 2 ^ (64 * n) = 2 ^ (64 * (n + 1)) - 2 ^ (64 * n) := by
        rw [h_pow_succ, Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
      rw [h_topR_eq, h_calc] at h_eq1
      -- Need to handle Nat subtraction carefully.
      have h_pow_n_le_pow_succ : 2 ^ (64 * n) ≤ 2 ^ (64 * (n + 1)) := by
        rw [h_pow_succ]; exact Nat.le_mul_of_pos_right _ h_pow_64_pos
      have h_Z_le_X_plus : Z ≤ X + 2 ^ (64 * (n + 1)) := by
        have hZ : Z < 2 ^ (64 * (n + 1)) := lt_of_lt_of_le h_Z_lt h_pow_n_le_pow_succ
        omega
      omega
    -- R1lo + Z = X + β^n ≥ β^n. Contradicts h_lo_lt.
    have h_R1lo_plus_Z : R1lo + Z = X + 2 ^ (64 * n) := by
      have h_Z_le_X_plus_pow : Z ≤ X + 2 ^ (64 * n) := by
        have : Z < 2 ^ (64 * n) := h_Z_lt
        omega
      omega
    have h_pow_le_sum : 2 ^ (64 * n) ≤ R1lo + Z := by
      rw [h_R1lo_plus_Z]; exact Nat.le_add_left _ _
    omega
  -- Apply bodyStep_toNat_two.
  have h_bodyStep := schoolbookDivModLimbs.bodyStep_toNat_two a b loA loB n j q_init hSub hB
    h_safe1 (by
      intro h_borrow h_lt
      change R1lo + Z < 2 ^ (64 * n) at h_lt
      exact h_safe2 h_borrow h_lt)
  simp only at h_bodyStep
  obtain ⟨b_out, h_eq⟩ := h_bodyStep
  -- Set up names matching bodyStep_toNat_two output.
  set fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2
    (by rw [h_r_size]; omega) hB with hfixup_def
  set Flo := toNatLimbsList ((a'.toList.drop (loA + j)).take n) with hFlo_def
  change X + r.2.toNat * 2 ^ (64 * (n + 1)) + b_out.toNat * 2 ^ (64 * n)
       = Flo + fixup.2.toNat * Z + (topR + r.2.toNat) * 2 ^ (64 * n) at h_eq
  -- The high slot of a' = fixup.2.
  have h_hi_slot : (a'[loA + n + j]'h_idx).toNat = fixup.2.toNat := by
    have h := schoolbookDivModLimbs.bodyStep_high_slot a b loA loB n j q_init hSub hB
    simp only at h
    rw [h]
  -- Goal: Flo < Z ∧ X = (a'[..]).toNat * Z + Flo.
  rw [h_hi_slot]
  show Flo < Z ∧ X = fixup.2.toNat * Z + Flo
  -- Case analysis on r.2 (borrow flag).
  cases hr2 : r.2
  · -- Case r.2 = false: addback is a no-op. fixup = (r.1, q_init).
    have h_fixup_noop : fixup = (r.1, q_init) := by
      rw [hfixup_def, hr2]
      exact schoolbookDivModLimbs.addback_borrow_false r.1 b (loA + j) loB n q_init 2 _ hB
    have h_fixup_2 : fixup.2 = q_init := by rw [h_fixup_noop]
    -- Flo = R1lo since fixup.1 = r.1 (low n limbs unchanged).
    have h_Flo_eq_fixup_low :
        Flo = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) := by
      show toNatLimbsList ((a'.toList.drop (loA + j)).take n)
        = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n)
      change toNatLimbsList (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop (loA + j)).take n)
        = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n)
      unfold schoolbookDivModLimbs.bodyStep
      have h_fixup_size : fixup.1.size = a.size := by
        rw [hfixup_def, schoolbookDivModLimbs.addback_size, h_r_size]
      have h_idx2 : loA + n + j < fixup.1.size := by rw [h_fixup_size]; omega
      have h_out : loA + n + j < loA + j ∨ (loA + j) + n ≤ loA + n + j := by omega
      have h_fixup_eq : (schoolbookDivModLimbs.addback
            (subMulLimbs a b (loA + j) loB n q_init hSub hB).1 b (loA + j) loB n q_init
            (subMulLimbs a b (loA + j) loB n q_init hSub hB).2 2 _ hB) = fixup := rfl
      simp only [h_fixup_eq]
      exact toNatLimbsList_set_outside fixup.1 (loA + j) n (loA + n + j) fixup.2 h_idx2 h_out
    have h_Flo_eq_R1lo : Flo = R1lo := by
      rw [h_Flo_eq_fixup_low, h_fixup_noop, hR1lo_def]
    -- Substitute into h_eq.
    rw [hr2, h_fixup_2, h_Flo_eq_R1lo] at h_eq
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h_eq
    -- Now h_eq : X + b_out.toNat * β^n = R1lo + q_init * Z + topR * β^n.
    -- From subMul (r.2 = false): X = R1full + q_init * Z = R1lo + topR * β^n + q_init * Z.
    rw [hr2] at h_subMul
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h_subMul
    rw [h_R1_decomp] at h_subMul
    -- h_subMul : X = R1lo + topR * β^n + q_init * Z.
    -- So b_out = false (consistent only).
    have h_bout_zero : b_out.toNat * 2 ^ (64 * n) = 0 := by
      have h_combined : X + b_out.toNat * 2 ^ (64 * n) = X := by linarith
      omega
    -- From q_init_bounds: r.2 = false ⟹ q_init * Z ≤ X (since R1full ≥ 0).
    -- And q_true * Z ≤ X. We have q_true ≤ q_init.
    -- We want to show q_init = q_true.
    -- From X = R1lo + topR * β^n + q_init * Z:
    --   q_init * Z = X - R1lo - topR * β^n ≤ X.
    -- And X = q_true * Z + (X mod Z), X mod Z < Z.
    -- So q_init * Z ≤ q_true * Z + (X mod Z) < (q_true + 1) * Z.
    -- Hence q_init < q_true + 1, q_init ≤ q_true. Combined with q_true ≤ q_init: q_init = q_true.
    have h_qinit_Z_le : q_init.toNat * Z ≤ X := by
      have : R1lo + topR * 2 ^ (64 * n) + q_init.toNat * Z = X := by linarith
      omega
    have h_qinit_le_qtrue : q_init.toNat ≤ q_true := by
      by_contra h
      push Not at h
      -- q_init ≥ q_true + 1, so q_init * Z ≥ (q_true + 1) * Z > X. Contradiction.
      have h_step : (q_true + 1) * Z ≤ q_init.toNat * Z := Nat.mul_le_mul_right _ h
      have h_qtrue_succ : (q_true + 1) * Z = q_true * Z + Z := by rw [Nat.add_mul, Nat.one_mul]
      have h_X_lt_succ : X < (q_true + 1) * Z := by
        rw [h_qtrue_succ]
        have h1 : X = q_true * Z + X % Z := by linarith
        omega
      omega
    have h_qinit_eq_qtrue : q_init.toNat = q_true := le_antisymm h_qinit_le_qtrue hq_lo
    -- Now: X = R1lo + topR * β^n + q_true * Z. And X = q_true * Z + X mod Z.
    -- So R1lo + topR * β^n = X mod Z < Z ≤ β^n. Hence topR = 0 and R1lo = X mod Z < Z.
    have h_decomp : R1lo + topR * 2 ^ (64 * n) = X % Z := by
      have h1 : X = q_true * Z + X % Z := by linarith
      have h2 : R1lo + topR * 2 ^ (64 * n) + q_init.toNat * Z = X := by linarith
      rw [h_qinit_eq_qtrue] at h2
      omega
    have h_decomp_lt : R1lo + topR * 2 ^ (64 * n) < Z := by
      rw [h_decomp]; exact h_X_mod_lt
    have h_topR_zero : topR = 0 := by
      by_contra h_topR_ne
      have h_topR_pos : 1 ≤ topR := Nat.one_le_iff_ne_zero.mpr h_topR_ne
      have h_pow_le : 2 ^ (64 * n) ≤ topR * 2 ^ (64 * n) :=
        Nat.le_mul_of_pos_left _ h_topR_pos
      have h_Z_lt_pow : Z < 2 ^ (64 * n) := h_Z_lt
      omega
    have h_R1lo_eq_mod : R1lo = X % Z := by
      rw [h_topR_zero] at h_decomp; simpa using h_decomp
    refine ⟨?_, ?_⟩
    · -- Flo = R1lo = X mod Z < Z.
      rw [h_Flo_eq_R1lo, h_R1lo_eq_mod]; exact h_X_mod_lt
    · -- X = q_true * Z + X mod Z = fixup.2 * Z + R1lo = fixup.2 * Z + Flo.
      rw [h_Flo_eq_R1lo, h_R1lo_eq_mod, h_fixup_2, h_qinit_eq_qtrue]
      omega
  · -- Case r.2 = true: addback fires.
    rw [hr2] at h_eq
    simp only [Bool.toNat_true, Nat.one_mul] at h_eq
    -- h_eq : X + β^(n+1) + b_out.toNat * β^n = Flo + fixup.2 * Z + (topR + 1) * β^n.
    -- From subMul: X + β^(n+1) = R1full + q_init * Z = R1lo + topR * β^n + q_init * Z.
    rw [hr2] at h_subMul
    simp only [Bool.toNat_true, Nat.one_mul] at h_subMul
    rw [h_R1_decomp] at h_subMul
    -- h_subMul : X + β^(n+1) = R1lo + topR * β^n + q_init * Z.
    have hq_init_ge_1 : 1 ≤ q_init.toNat := h_safe1 hr2
    -- We need to determine fixup.2 and Flo.
    -- The addback iterates up to 2 times. The number of iterations that fire equals
    -- q_init - fixup.2. From q_init_bounds, q_init ≤ q_true + 2.
    -- We use the addback equation directly.
    have h_addback_eq :=
      schoolbookDivModLimbs.addback_toNat_two_strong r.1 b (loA + j) loB n q_init r.2
        (by rw [h_r_size]; omega) hB h_safe1 (by
          intro h_borrow h_lt
          change R1lo + Z < 2 ^ (64 * n) at h_lt
          exact h_safe2 h_borrow h_lt)
    rw [← hfixup_def] at h_addback_eq
    obtain ⟨b_out', h_addback_eq, h_bout_true_imp, h_bout_false_imp⟩ := h_addback_eq
    -- We know from bodyStep_toNat_two that the b_out from there matches.
    -- We extract: Flo + (1 - b_out'.toNat) * β^n + fixup.2 * Z
    --           = R1lo + (1 - r.2.toNat) * β^n + q_init * Z.
    -- With r.2 = true: ... = R1lo + 0 + q_init * Z = R1lo + q_init * Z.
    -- The Flo here is the (loA+j)-take-n of fixup.1 (before set). But our Flo is
    -- of a' = fixup.1.set (loA + n + j) fixup.2, which has the same low-n slice.
    -- Need to relate them.
    have h_Flo_alt : Flo = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) := by
      show toNatLimbsList ((a'.toList.drop (loA + j)).take n)
        = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n)
      show toNatLimbsList (((schoolbookDivModLimbs.bodyStep a b loA loB n j q_init hSub hB).toList.drop (loA + j)).take n)
        = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n)
      unfold schoolbookDivModLimbs.bodyStep
      have h_fixup_size : fixup.1.size = a.size := by
        rw [hfixup_def, schoolbookDivModLimbs.addback_size, h_r_size]
      have h_idx2 : loA + n + j < fixup.1.size := by rw [h_fixup_size]; omega
      have h_out : loA + n + j < loA + j ∨ (loA + j) + n ≤ loA + n + j := by omega
      exact toNatLimbsList_set_outside fixup.1 (loA + j) n (loA + n + j) fixup.2 h_idx2 h_out
    rw [← h_Flo_alt] at h_addback_eq
    rw [hr2] at h_addback_eq
    simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_addback_eq
    -- h_addback_eq : Flo + (1 - b_out'.toNat) * β^n + fixup.2 * Z = R1lo + q_init * Z.
    -- From this and X + β^(n+1) = R1lo + topR * β^n + q_init * Z:
    -- Flo + (1 - b_out'.toNat) * β^n + fixup.2 * Z = X + β^(n+1) - topR * β^n.
    -- The number of addback iterations (k) satisfies: q_init - fixup.2 = k ∈ {1, 2}.
    -- From q_init ≥ q_true and q_init ≤ q_true + 2:
    -- - If k = 1: fixup.2 = q_init - 1 ∈ [q_true - 1, q_true + 1].
    -- - If k = 2: fixup.2 = q_init - 2 ∈ [q_true - 2, q_true].
    -- We claim fixup.2 = q_true and Flo < Z, which gives both parts of the goal.
    -- Strategy: use h_addback_eq combined with X = q_true * Z + X mod Z.
    -- Let m := X mod Z.
    -- X + β^(n+1) - topR * β^n = q_true * Z + m + β^(n+1) - topR * β^n.
    -- And we want this = Flo + (1 - b_out'.toNat) * β^n + fixup.2 * Z.
    --
    -- Key fact: Flo < β^n (slice bound).
    have h_Flo_lt : Flo < 2 ^ (64 * n) := by
      have h_pow := toNatLimbsList_lt_pow ((a'.toList.drop (loA + j)).take n)
      have ha'_size : a'.size = a.size := schoolbookDivModLimbs.bodyStep_size _ _ _ _ _ _ _ _ _
      have h_len : ((a'.toList.drop (loA + j)).take n).length = n := by
        rw [List.length_take, List.length_drop, Array.length_toList, ha'_size]
        omega
      rw [h_len] at h_pow; exact h_pow
    -- From h_eq (with r.2 = true, h_pow_succ applied):
    -- X + 2^(64n) * 2^64 + b_out * 2^(64n) = Flo + fixup.2 * Z + (topR + 1) * 2^(64n).
    -- Rearranged: X + (2^64 + b_out) * 2^(64n) = Flo + fixup.2 * Z + (topR + 1) * 2^(64n).
    rw [h_pow_succ] at h_eq
    -- bodyStep_toNat_two's b_out should equal addback_toNat_two's b_out' since fixup is the same.
    -- We'll work with h_eq directly.
    -- First show that q_init ≥ q_true + 1 (since r.2 = true means q_init * Z > X).
    have h_qinit_gt : q_true < q_init.toNat := by
      -- From h_subMul: X + β^(n+1) = R1lo + topR * β^n + q_init * Z.
      -- R1lo + topR * β^n = R1full < β^(n+1).
      -- So q_init * Z > X, hence q_init > X / Z = q_true.
      have h_qinit_Z_gt : q_init.toNat * Z > X := by
        have h_R1full_lt' : R1lo + topR * 2 ^ (64 * n) < 2 ^ (64 * (n + 1)) := by
          rw [← h_R1_decomp]; exact h_R1full_lt
        omega
      -- q_init * Z > X means q_init ≥ q_true + 1.
      by_contra h
      push Not at h
      -- q_init ≤ q_true. Then q_init * Z ≤ q_true * Z ≤ X. Contradiction.
      have h1 : q_init.toNat * Z ≤ q_true * Z := Nat.mul_le_mul_right _ h
      have h2 : q_true * Z ≤ X := by
        have := h_qtrue_mul; omega
      omega
    -- Case split on b_out' = true/false to use the strong implications.
    cases hb_out' : b_out'
    · -- b_out' = false: from h_bout_false_imp, Flo < Z. Need to derive
      -- X = fixup.2 * Z + Flo. From h_addback_eq and h_subMul:
      --   Flo + 2^(64*n) + fixup.2 * Z = R1lo + q_init * Z         (1)
      --   X + 2^(64*n) * 2^64 = R1lo + topR * 2^(64*n) + q_init * Z (2)
      -- Subtracting (1) from (2):
      --   X + 2^(64*n) * 2^64 - 2^(64*n) - fixup.2 * Z = topR * 2^(64*n)
      --   X + (2^64 - topR - 1) * 2^(64*n) = fixup.2 * Z + Flo
      -- For X = fixup.2 * Z + Flo, need topR = 2^64 - 1.
      have h_Flo_lt_Z : Flo < Z := by
        have := h_bout_false_imp hb_out' hr2
        rw [← h_Flo_alt] at this
        exact this
      rw [hb_out'] at h_addback_eq
      simp only [Bool.toNat_false, Nat.sub_zero, Nat.one_mul] at h_addback_eq
      -- h_addback_eq : Flo + 2^(64*n) + fixup.2 * Z = R1lo + q_init * Z.
      -- From h_subMul (with h_R1_decomp + h_pow_succ already applied):
      --   X + 2^(64*n) * 2^64 = R1lo + topR * 2^(64*n) + q_init * Z.
      -- We need topR = 2^64 - 1 to conclude X = fixup.2 * Z + Flo.
      -- Bound topR < 2^64 (UInt64).
      have h_topR_lt : topR < 2 ^ 64 := by
        rw [htopR_def]
        exact (r.1[(loA + j) + n]'h_topR_idx).toNat_lt
      -- The strengthened `q_init_bounds` gives `q_init * Z < X + β^n` (i.e.,
      -- `δ = q_init * Z - X < β^n` when r.2 = true). This pins down topR.
      -- From h_subMul: R1lo + topR * β^n + q_init * Z = X + β^(n+1).
      -- So R1lo + topR * β^n = X + β^(n+1) - q_init * Z > β^(n+1) - X - β^n - X
      --                       = β^(n+1) - β^n  (using q_init * Z < X + β^n).
      -- Hence R1lo + topR * β^n > (β - 1) * β^n. Since R1lo < β^n, topR ≥ β - 1.
      -- Combined with topR < β: topR = β - 1.
      have h_topR_eq : topR = 2 ^ 64 - 1 := by
        have h_lower : (2 ^ 64 - 1) * 2 ^ (64 * n) < R1lo + topR * 2 ^ (64 * n) := by
          have h_calc : (2 ^ 64 - 1) * 2 ^ (64 * n) = 2 ^ (64 * n) * 2 ^ 64 - 2 ^ (64 * n) := by
            rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
          have h_pow_n_le : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 :=
            Nat.le_mul_of_pos_right _ (Nat.two_pow_pos 64)
          rw [h_calc]
          -- Goal: 2^(64*n) * 2^64 - 2^(64*n) < R1lo + topR * 2^(64*n).
          -- From h_subMul: R1lo + topR * 2^(64*n) = X + 2^(64*n) * 2^64 - q_init * Z.
          -- From hq_delta: q_init * Z < X + 2^(64*n).
          -- So R1lo + topR * 2^(64*n) > X + 2^(64*n) * 2^64 - X - 2^(64*n) =
          -- 2^(64*n) * 2^64 - 2^(64*n).
          omega
        -- topR ≥ β - 1.
        have h_topR_ge : 2 ^ 64 - 1 ≤ topR := by
          by_contra h_lt
          push Not at h_lt
          -- topR ≤ 2^64 - 2.
          have h_topR_le : topR ≤ 2 ^ 64 - 2 := by omega
          have h_mul : topR * 2 ^ (64 * n) ≤ (2 ^ 64 - 2) * 2 ^ (64 * n) :=
            Nat.mul_le_mul_right _ h_topR_le
          have h_calc2 : (2 ^ 64 - 1) * 2 ^ (64 * n)
              = (2 ^ 64 - 2) * 2 ^ (64 * n) + 2 ^ (64 * n) := by
            have h_sub : (2 ^ 64 - 1) = (2 ^ 64 - 2) + 1 := by
              have : (2 : Nat) ^ 1 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
              simp at this; omega
            rw [h_sub, Nat.add_mul, Nat.one_mul]
          omega
        omega
      -- Now derive X = fixup.2 * Z + Flo using topR = 2^64 - 1.
      -- h_addback_eq : Flo + 2^(64*n) + fixup.2 * Z = R1lo + q_init * Z.
      -- h_subMul (with h_R1_decomp + h_pow_succ): X + 2^(64*n) * 2^64
      --   = R1lo + topR * 2^(64*n) + q_init * Z
      --   = R1lo + (2^64 - 1) * 2^(64*n) + q_init * Z
      --   = R1lo + q_init * Z + 2^(64*n) * 2^64 - 2^(64*n).
      -- So X = R1lo + q_init * Z - 2^(64*n).
      -- And from h_addback_eq: R1lo + q_init * Z = Flo + 2^(64*n) + fixup.2 * Z.
      -- So X = Flo + 2^(64*n) + fixup.2 * Z - 2^(64*n) = Flo + fixup.2 * Z.
      refine ⟨h_Flo_lt_Z, ?_⟩
      have h_pow_n_le : (2 : Nat) ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos 64)
      -- topR * 2^(64*n) = 2^(64*n) * 2^64 - 2^(64*n), expressed additively.
      have h_topR_add : topR * 2 ^ (64 * n) + 2 ^ (64 * n) = 2 ^ (64 * n) * 2 ^ 64 := by
        rw [h_topR_eq, Nat.sub_mul, Nat.one_mul]
        rw [Nat.mul_comm (2 ^ 64) (2 ^ (64 * n))]
        rw [Nat.sub_add_cancel h_pow_n_le]
      -- h_subMul : X + 2^(64*n) * 2^64 = R1lo + topR * 2^(64*n) + q_init * Z.
      -- h_addback_eq : Flo + 2^(64*n) + fixup.2 * Z = R1lo + q_init * Z.
      linarith [h_subMul, h_addback_eq, h_topR_add]
    · -- b_out' = true: from h_bout_true_imp, R1lo + 2*Z < 2^(64*n).
      -- We derive a contradiction.
      exfalso
      have h_lt : R1lo + 2 * Z < 2 ^ (64 * n) := h_bout_true_imp hb_out' hr2
      -- From h_subMul: X + 2^(64*n) * 2^64 = R1lo + topR * 2^(64*n) + q_init * Z.
      -- q_init * Z ≤ X + 2*Z (from q_init ≤ q_true + 2, q_true * Z ≤ X).
      have h_qinit_Z_bound : q_init.toNat * Z ≤ X + 2 * Z := by
        have h1 : q_init.toNat * Z ≤ (q_true + 2) * Z := Nat.mul_le_mul_right _ hq_hi
        have h2 : (q_true + 2) * Z = q_true * Z + 2 * Z := by ring
        have h3 : q_true * Z ≤ X := by have := h_qtrue_mul; omega
        omega
      have h_topR_lt : topR < 2 ^ 64 := by
        rw [htopR_def]
        exact (r.1[(loA + j) + n]'h_topR_idx).toNat_lt
      -- From h_subMul: R1lo + topR * 2^(64*n) ≥ X + 2^(64*n) * 2^64 - (X + 2*Z)
      --                                       = 2^(64*n) * 2^64 - 2*Z.
      -- Combined with R1lo < 2^(64*n) - 2*Z (from h_lt, taking R1lo < 2^(64*n) - 2*Z
      -- when R1lo + 2*Z < 2^(64*n)):
      --   topR * 2^(64*n) > 2^(64*n) * 2^64 - 2^(64*n) = (2^64 - 1) * 2^(64*n)
      -- So topR ≥ 2^64. Contradicts topR < 2^64.
      have h_R1lo_bound : R1lo + 2 * Z < 2 ^ (64 * n) := h_lt
      have h_step : R1lo + topR * 2 ^ (64 * n) + q_init.toNat * Z
                      = X + 2 ^ (64 * n) * 2 ^ 64 := by linarith [h_subMul]
      -- Compute lower bound on topR * 2^(64*n).
      have h_lower : 2 ^ (64 * n) * 2 ^ 64 ≤ R1lo + topR * 2 ^ (64 * n) + X + 2 * Z := by
        have h_pos : 0 ≤ X := Nat.zero_le _
        omega
      -- But R1lo + 2*Z < 2^(64*n), so R1lo + 2*Z ≤ 2^(64*n) - 1.
      -- Hence topR * 2^(64*n) + 2^(64*n) - 1 + X ≥ 2^(64*n) * 2^64 + X.
      -- (topR + 1) * 2^(64*n) > 2^(64*n) * 2^64.
      -- topR + 1 > 2^64, topR ≥ 2^64. Contradicts h_topR_lt.
      have h_pow_pos : 0 < (2 : Nat) ^ (64 * n) := Nat.two_pow_pos _
      have h_topR_ge : 2 ^ 64 ≤ topR := by
        by_contra h
        push Not at h
        -- topR ≤ 2^64 - 1, so (topR + 1) * 2^(64*n) ≤ 2^64 * 2^(64*n).
        -- But we need (topR + 1) * 2^(64*n) > 2^64 * 2^(64*n).
        have h_topR_le : topR ≤ 2 ^ 64 - 1 := by omega
        have h_mul : (topR + 1) * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) := by
          have : topR + 1 ≤ 2 ^ 64 := by omega
          exact Nat.mul_le_mul_right _ this
        -- From h_step: topR * 2^(64*n) = X + 2^(64*n) * 2^64 - R1lo - q_init * Z.
        -- So topR * 2^(64*n) ≥ X + 2^(64*n) * 2^64 - R1lo - X - 2*Z
        --                    = 2^(64*n) * 2^64 - R1lo - 2*Z
        --                    > 2^(64*n) * 2^64 - 2^(64*n)
        --                    = (2^64 - 1) * 2^(64*n)
        have h_topR_gt : (2 ^ 64 - 1) * 2 ^ (64 * n) < topR * 2 ^ (64 * n) := by
          have h1 : R1lo + 2 * Z + 1 ≤ 2 ^ (64 * n) := by omega
          -- From h_step: topR * 2^(64*n) = X + 2^(64*n) * 2^64 - R1lo - q_init * Z.
          -- We need: topR * 2^(64*n) > (2^64 - 1) * 2^(64*n).
          -- (2^64 - 1) * 2^(64*n) = 2^64 * 2^(64*n) - 2^(64*n).
          -- topR * 2^(64*n) > 2^64 * 2^(64*n) - 2^(64*n).
          -- 2^(64*n) > 2^64 * 2^(64*n) - topR * 2^(64*n) = (2^64 - topR) * 2^(64*n).
          -- (2^64 - topR) < 1, so 2^64 = topR. Contradicts topR < 2^64.
          have h_calc : (2 ^ 64 - 1) * 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * n) - 2 ^ (64 * n) := by
            rw [Nat.sub_mul, Nat.one_mul]
          have h_le2 : (2 : Nat) ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) := by
            have h_pow_64 : 1 ≤ (2 : Nat) ^ 64 := Nat.two_pow_pos 64
            exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 64)
          rw [h_calc]
          -- Goal: 2^64 * 2^(64*n) - 2^(64*n) < topR * 2^(64*n).
          -- From h_step: topR * 2^(64*n) = X + 2^64 * 2^(64*n) - R1lo - q_init * Z.
          -- topR * 2^(64*n) ≥ X + 2^64 * 2^(64*n) - R1lo - (X + 2*Z)
          --                = 2^64 * 2^(64*n) - R1lo - 2*Z.
          -- And R1lo + 2*Z < 2^(64*n), so 2^(64*n) > R1lo + 2*Z, i.e.,
          -- 2^64 * 2^(64*n) - R1lo - 2*Z > 2^64 * 2^(64*n) - 2^(64*n).
          omega
        have : 2 ^ 64 ≤ topR := by
          have h_pow_pos' : 0 < (2 : Nat) ^ (64 * n) := h_pow_pos
          have h_calc : (2 ^ 64 - 1) * 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * n) - 2 ^ (64 * n) := by
            rw [Nat.sub_mul, Nat.one_mul]
          rw [h_calc] at h_topR_gt
          -- topR * 2^(64*n) > 2^64 * 2^(64*n) - 2^(64*n).
          -- I.e., topR ≥ 2^64 (using positivity of 2^(64*n)).
          have h_pow_64 : 1 ≤ (2 : Nat) ^ 64 := Nat.two_pow_pos 64
          have h_pow_n_le : (2 : Nat) ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
            Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 64)
          -- From: topR * 2^(64*n) > 2^64 * 2^(64*n) - 2^(64*n) =
          -- (2^64 - 1) * 2^(64*n). Hence topR > 2^64 - 1, i.e., topR ≥ 2^64.
          by_contra h_topR_lt'
          push Not at h_topR_lt'
          have h_topR_le' : topR ≤ 2 ^ 64 - 1 := by omega
          have h_mul' : topR * 2 ^ (64 * n) ≤ (2 ^ 64 - 1) * 2 ^ (64 * n) :=
            Nat.mul_le_mul_right _ h_topR_le'
          rw [h_calc] at h_mul'
          omega
        omega
      omega

end Azurite.AzNat
