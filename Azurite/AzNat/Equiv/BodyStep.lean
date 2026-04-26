import Azurite.AzNat.Equiv.Addback

namespace Azurite.AzNat

/-! ### Helper lemmas for one body iteration of `schoolbookDivMod.go` -/

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

/-- The single-iteration body of `schoolbookDivMod.go` (extracted as a helper
    function for proof modularity). Given the same trial digit `q_init` that
    `go` would compute, this performs the `subMulLimbs` + `addback` + `set`
    sequence that mutates `a` before the recursive call.

    Returns the post-body array, which equals `a'` in the body of
    `schoolbookDivMod.go` (recursive case). -/
noncomputable def schoolbookDivMod.bodyStep
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 :=
  let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
  let fixup := schoolbookDivMod.addback r.1 b (loA + j) loB n q_init r.2 2
                 (by rw [subMulLimbs_size]; omega) hB
  fixup.1.set (loA + n + j) fixup.2
    (by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivMod.addback_size _ _ _ _ _ _ _ _ _ _,
          subMulLimbs_size]
      omega)

/-- Size preservation of `bodyStep`. -/
theorem schoolbookDivMod.bodyStep_size
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).size = a.size := by
  unfold schoolbookDivMod.bodyStep
  rw [Array.size_set, schoolbookDivMod.addback_size, subMulLimbs_size]

/-- `bodyStep` preserves any prefix up to `loA + j`. The body mutates the slice
    `[loA + j, loA + j + n + 1)` (via `subMulLimbs`/`addback`) and stores at
    position `loA + n + j` — both lie at index `≥ loA + j`, so the prefix is
    untouched. -/
theorem schoolbookDivMod.bodyStep_toList_take_le
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : m0 ≤ loA + j) :
    (schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).toList.take m0
      = a.toList.take m0 := by
  unfold schoolbookDivMod.bodyStep
  rw [Array.toList_set, List.take_set_of_le (by omega : m0 ≤ loA + n + j),
    schoolbookDivMod.addback_toList_take_le _ _ _ _ _ _ _ _ _ _ m0 hm]
  exact subMulLimbs_toList_take_le a b (loA + j) loB n q_init hSub hB m0 hm

/-- `bodyStep` preserves the suffix from any `m0 ≥ loA + j + n + 1`.  All
    mutations (subMulLimbs over `[loA+j, loA+j+n)`, addback over the same range
    + final-borrow handling at `loA+j+n`, and the set at position `loA+n+j`)
    fall within indices `< loA + j + n + 1`. -/
theorem schoolbookDivMod.bodyStep_toList_drop_ge
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : (loA + j) + n + 1 ≤ m0) :
    (schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).toList.drop m0
      = a.toList.drop m0 := by
  unfold schoolbookDivMod.bodyStep
  rw [Array.toList_set, List.drop_set, if_pos (by omega : loA + n + j < m0),
    schoolbookDivMod.addback_toList_drop_ge _ _ _ _ _ _ _ _ _ _ m0 (by omega)]
  -- Lift `subMulLimbs_toList_drop` (exact offset `(loA+j)+n+1`) to general `m0`.
  have h_split : ∀ (l : List UInt64),
      l.drop m0 = (l.drop ((loA + j) + n + 1)).drop (m0 - ((loA + j) + n + 1)) :=
    fun l => by rw [List.drop_drop, Nat.add_sub_cancel' hm]
  rw [h_split, subMulLimbs_toList_drop, ← h_split]

/-- The high slot of the post-`bodyStep` array (at index `loA + n + j`) holds
    the corrected quotient digit `fixup.2`. -/
theorem schoolbookDivMod.bodyStep_high_slot
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    let fixup := schoolbookDivMod.addback r.1 b (loA + j) loB n q_init r.2 2
                   (by rw [subMulLimbs_size]; omega) hB
    have h_idx : loA + n + j <
        (schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).size := by
      rw [schoolbookDivMod.bodyStep_size]; omega
    (schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB)[loA + n + j]'h_idx
      = fixup.2 := by
  unfold schoolbookDivMod.bodyStep
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
theorem schoolbookDivMod.bodyStep_toNat
    (a b : Array UInt64) (loA loB n j : Nat) (q_init : UInt64)
    (hSub : (loA + j) + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (h_q_safe : (subMulLimbs a b (loA + j) loB n q_init hSub hB).2 = true →
                  2 ≤ q_init.toNat) :
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    let fixup := schoolbookDivMod.addback r.1 b (loA + j) loB n q_init r.2 2
                   (by rw [subMulLimbs_size]; omega) hB
    ∃ b_out : Bool,
      toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
          + r.2.toNat * 2 ^ (64 * (n + 1))
          + b_out.toNat * 2 ^ (64 * n)
        = toNatLimbsList
            (((schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).toList.drop
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
    schoolbookDivMod.addback_toNat r.1 b (loA + j) loB n q_init r.2 2
      h_addback_hyp hB h_q_safe
  obtain ⟨b_out, h_addback_eq⟩ := h_addback_eq
  refine ⟨b_out, ?_⟩
  -- Unfold bodyStep and identify a' = fixup.1.set (loA + n + j) fixup.2.
  have h_bodyStep_low :
      toNatLimbsList
        (((schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB).toList.drop
          (loA + j)).take n)
      = toNatLimbsList ((fixup.1.toList.drop (loA + j)).take n) := by
    unfold schoolbookDivMod.bodyStep
    -- The `set` is at position `loA + n + j`, which is outside `[loA + j, loA + j + n)`.
    have h_fixup_size : fixup.1.size = a.size := by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivMod.addback_size _ _ _ _ _ _ _ _ _ _, h_r_size]
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

end Azurite.AzNat
