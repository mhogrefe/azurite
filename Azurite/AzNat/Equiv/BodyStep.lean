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

/-! ### Trial-digit (`q_init`) bounds — Knuth/Möller–Granlund analysis

The `schoolbookDivMod.go` body computes a trial quotient digit

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
theorem schoolbookDivMod.q_init_bounds
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
    let A_local : Nat := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
    let B : Nat := toNatLimbsList ((b.toList.drop loB).take n)
    let q_true : Nat := A_local / B
    q_true ≤ q_init.toNat ∧ q_init.toNat ≤ q_true + 2 := by
  -- Pending: Knuth/Möller–Granlund bound (see comment block above).
  sorry

/-! ### `bodyStep_BZ` — one-step BZ invariant preservation -/

/-- **BZ invariant preserved by one body iteration**.

    Pre: BZ invariant on the `(n+1)`-limb dividend slice at offset `loA + j`
    (i.e., `A_local < β · B`).

    Post (using the trial digit `q_init` that `schoolbookDivMod.go` would compute):
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
theorem schoolbookDivMod.bodyStep_BZ
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
    let a' := schoolbookDivMod.bodyStep a b loA loB n j q_init hSub hB
    have h_idx : loA + n + j < a'.size := by
      rw [schoolbookDivMod.bodyStep_size]; omega
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
  -- Pending: combine q_init_bounds + subMulLimbs_toNat + addback_toNat +
  -- bodyStep_toNat (see proof sketch above).
  sorry

end Azurite.AzNat
