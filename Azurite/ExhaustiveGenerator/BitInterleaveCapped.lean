/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `BitInterleaveCapped` — the CAPPED sibling of `BitInterleave`'s
  `BitAssignment`: slots may own only finitely many counter-bit positions.

  A `CappedBitAssignment m` distributes counter-bit positions among `m`
  slots, where slot `j` owns exactly `b` positions when `cap j = some b` and
  infinitely many when `cap j = none`. `slotOf` is `Option`-valued: a
  position is unowned (`none`) only when every slot is capped and the
  position lies past all owned ones. The four `BitAssignment` laws return
  with their rank arguments guarded by validity
  (`∀ b, cap j = some b → r < b`).

  `deinterleave`/`interleave` are the same bounded `Finset.range` bit sums
  as the uncapped file, with the validity guard folded into the summand
  (resp. the summation range). The uncapped bijection `ℕ ≃ (Fin m → ℕ)`
  becomes a guarded pair of round-trips:
  * `deinterleave_interleave` under the per-slot bounds `f j < 2 ^ b`, and
  * `interleave_deinterleave` under `Valid k` (all set bits of `k` owned),
  together with `interleave_valid` and the unconditional output bound
  `deinterleave_lt_two_pow : cap j = some b → deinterleave j k < 2 ^ b`.

  The instance `cappedRoundRobin cap` is Malachite `update_bit_map`'s
  weight-1 drop-out rotation (`bit_distributor.rs`): positions are assigned
  in rounds; in each round the still-active slots (used-count below their
  cap) receive one position each in DECREASING slot order (slot `m - 1`
  first, matching `roundRobin`), and a slot drops out of the rotation once
  its cap is exhausted. Slot `j` is active in round `t` exactly when its cap
  exceeds `t`, which turns the position-by-position scan into per-round
  `Finset` counting: `pos j r = roundStart r + offsetIn r j`, where
  `roundStart` sums the sizes of the earlier rounds and `offsetIn` counts
  the active slots above `j`. With no caps this degenerates to `roundRobin`
  (`cappedRoundRobin_pos_none`/`cappedRoundRobin_slotOf_none`).

  Ownership: with at least one uncapped slot every position is owned
  (`cappedRoundRobin_owned_of_none`); when all slots are capped by `b j`,
  position `i` is owned iff `i < ∑ j, b j` (`cappedRoundRobin_owned_iff`)
  and `Valid k ↔ k < 2 ^ ∑ j, b j` (`cappedRoundRobin_valid_iff`).

  NOTE (cap placement): with `cap = ![some 2, none]` it is slot 0 that owns
  exactly two positions (`{1, 3}` — its `pos_rank` law caps it) while slot 1
  owns the rest; this matches `update_bit_map`, whose `set_max_bits` doctest
  pins the cap to the OUTPUT INDEX, not to the rotation order. The mirrored
  vector `![none, some 2]` produces the table `[1, 0, 1, 0, 0, 0, …]`.
-/
import Azurite.ExhaustiveGenerator.BitInterleave
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Fin

namespace Azurite

/-! ### `Nat.testBit` helper -/

/-- A number with all bits at or above `b` clear is below `2 ^ b`: the
converse of `Nat.testBit_lt_two_pow`, via the most-significant set bit. -/
theorem lt_two_pow_of_testBit_eq_false {n b : ℕ}
    (h : ∀ i, b ≤ i → n.testBit i = false) : n < 2 ^ b := by
  by_contra hge
  obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (Nat.le_of_not_lt hge)
  rw [h i hi] at hbit
  exact Bool.false_ne_true hbit

/-! ### Decidability of the validity guard -/

/-- The validity guard `∀ b, o = some b → r < b` (rank `r` lies under an
optional cap `o`) is decidable by cases on `o`. -/
instance decidableCapGuard : (o : Option ℕ) → (r : ℕ) → Decidable (∀ b, o = some b → r < b)
  | none, _ => isTrue fun _ h => nomatch h
  | some b, r =>
    decidable_of_iff (r < b) ⟨fun h _ hb' => Option.some.inj hb' ▸ h, fun h => h b rfl⟩

/-! ### The abstract capped slot assignment -/

/-- A **capped bit assignment**: a distribution of counter-bit positions `ℕ`
among `m` slots where slot `j` owns exactly `b` positions when
`cap j = some b` and an infinite ascending sequence when `cap j = none`.
The rank `r` is VALID for slot `j` when `∀ b, cap j = some b → r < b`; the
four `BitAssignment` laws hold guarded by validity, and `slotOf` returns
`none` exactly on the unowned positions (possible only when all slots are
capped). Uncapped everywhere, this is `BitAssignment` with a total
`slotOf`. -/
structure CappedBitAssignment (m : ℕ) where
  /-- `some b`: slot `j` owns exactly `b` positions; `none`: infinitely many. -/
  cap : Fin m → Option ℕ
  /-- The slot owning counter-bit position `i`, or `none` if `i` is unowned. -/
  slotOf : ℕ → Option (Fin m)
  /-- The index of position `i` within its slot's ascending positions
  (junk when `i` is unowned). -/
  rank : ℕ → ℕ
  /-- The `r`-th (0-based, ascending) counter position owned by slot `j`,
  meaningful only at valid ranks `r`. -/
  pos : Fin m → ℕ → ℕ
  /-- Slot `j` owns all the positions `pos j r`, at valid ranks. -/
  pos_slotOf : ∀ j r, (∀ b, cap j = some b → r < b) → slotOf (pos j r) = some j
  /-- `pos j r` is the `r`-th position of its slot, at valid ranks. -/
  rank_pos : ∀ j r, (∀ b, cap j = some b → r < b) → rank (pos j r) = r
  /-- Every owned position is reached by `pos` at a valid rank. -/
  pos_rank : ∀ i j, slotOf i = some j →
    pos j (rank i) = i ∧ (∀ b, cap j = some b → rank i < b)
  /-- Each slot's positions ascend strictly in the rank, on the valid range. -/
  pos_lt_pos : ∀ j r r', (∀ b, cap j = some b → r' < b) → r < r' → pos j r < pos j r'

namespace CappedBitAssignment

variable {m : ℕ} (A : CappedBitAssignment m)

/-- Validity of ranks is downward closed. -/
theorem valid_of_le {j : Fin m} {r r' : ℕ} (hr : r ≤ r')
    (h : ∀ b, A.cap j = some b → r' < b) : ∀ b, A.cap j = some b → r < b :=
  fun b hb => Nat.lt_of_le_of_lt hr (h b hb)

/-- The `r`-th position of a slot is at least `r` (strict monotonicity from
`0`, on the valid range). This is what bounds `deinterleave` by `k.size`
bits. -/
theorem le_pos (j : Fin m) (r : ℕ) : (∀ b, A.cap j = some b → r < b) → r ≤ A.pos j r := by
  induction r with
  | zero => exact fun _ => Nat.zero_le _
  | succ n ih =>
    intro h
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih (A.valid_of_le (Nat.le_succ n) h))
      (A.pos_lt_pos j n (n + 1) h (Nat.lt_succ_self n)))

/-- `(j, r) ↦ pos j r` is injective on valid pairs: `slotOf` recovers `j` and
`rank` recovers `r`. -/
theorem pos_inj {j j' : Fin m} {r r' : ℕ} (h : ∀ b, A.cap j = some b → r < b)
    (h' : ∀ b, A.cap j' = some b → r' < b) (heq : A.pos j r = A.pos j' r') :
    j = j' ∧ r = r' := by
  have hj : j = j' := Option.some.inj (by rw [← A.pos_slotOf j r h, heq, A.pos_slotOf j' r' h'])
  refine ⟨hj, ?_⟩
  subst hj
  rw [← A.rank_pos j r h, heq, A.rank_pos j r' h']

/-- Position `i` is **owned** when some slot owns it. -/
def Owned (i : ℕ) : Prop := (A.slotOf i).isSome

instance (i : ℕ) : Decidable (A.Owned i) :=
  inferInstanceAs (Decidable (_ = true))

/-! ### Deinterleave and interleave

Both maps are bounded bit sums over `Finset.range`, exactly as in the
uncapped file; the validity guard is folded into the summand
(`deinterleave`) resp. the summation range (`interleave`), so invalid ranks
contribute nothing. -/

/-- `A.deinterleave j k` extracts slot `j`'s component of the counter `k`:
the number whose bit `r` is bit `A.pos j r` of `k` for valid `r`, and `0`
for invalid `r`. Only ranks `r < k.size` can contribute (`le_pos`), so the
sum is finite and computable. -/
def deinterleave (j : Fin m) (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k.size,
    if decide (∀ b, A.cap j = some b → r < b) && k.testBit (A.pos j r) then 2 ^ r else 0

/-- `A.interleave f` assembles a counter from the components: bit `r` of
`f j` lands at counter position `A.pos j r`, for valid ranks `r`. The double
sum ranges over pairwise distinct positions (`pos_inj`), so there are no
carries. Bits of `f j` at invalid ranks are DROPPED; the round-trip
`deinterleave_interleave` therefore assumes `f j < 2 ^ b` for capped
slots. -/
def interleave (f : Fin m → ℕ) : ℕ :=
  ∑ j, ∑ r ∈ (Finset.range (f j).size).filter (fun r => ∀ b, A.cap j = some b → r < b),
    if (f j).testBit r then 2 ^ (A.pos j r) else 0

/-- The full deinterleave map `ℕ → (Fin m → ℕ)`: distribute the bits of `k`
into `m` component numbers according to the assignment. -/
def deinterleaveTuple (k : ℕ) : Fin m → ℕ := fun j => A.deinterleave j k

/-- A counter `k` is **valid** when every set bit sits at an owned position.
Interleaving hits exactly the valid counters (`interleave_valid`,
`interleave_deinterleave`). -/
def Valid (k : ℕ) : Prop := ∀ i, k.testBit i = true → A.Owned i

instance (k : ℕ) : Decidable (A.Valid k) :=
  decidable_of_iff (∀ i < k.size, k.testBit i = true → A.Owned i) <| by
    constructor
    · intro h i hbit
      exact h i (Nat.lt_size.mpr (Nat.ge_two_pow_of_testBit hbit)) hbit
    · intro h i _ hbit
      exact h i hbit

/-- **The defining `testBit` characterization of `deinterleave`.** Bit `r` of
`A.deinterleave j k` is bit `A.pos j r` of `k` guarded by validity of `r` —
with no bound on `r`: above `k.size` both sides are false, since a valid `r`
has `pos j r ≥ r ≥ k.size` and `k < 2 ^ k.size`. -/
theorem testBit_deinterleave (j : Fin m) (k r : ℕ) :
    (A.deinterleave j k).testBit r
      = (decide (∀ b, A.cap j = some b → r < b) && k.testBit (A.pos j r)) := by
  unfold deinterleave
  rw [testBit_sum_pow (Finset.range k.size) (fun x => x)
    (fun x => decide (∀ b, A.cap j = some b → x < b) && k.testBit (A.pos j x))
    (Set.injOn_id _) r]
  by_cases hr : r < k.size
  · -- In range: the unique possible witness is `a = r`.
    by_cases hb : (decide (∀ b, A.cap j = some b → r < b) && k.testBit (A.pos j r)) = true
    · rw [hb, decide_eq_true_eq]
      exact ⟨r, Finset.mem_range.mpr hr, rfl, hb⟩
    · simp only [Bool.not_eq_true] at hb
      rw [hb]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro a _ rfl hba
      rw [hb] at hba
      exact Bool.false_ne_true hba
  · -- Above the bound: no witness is in range, and the right side is false.
    have hL : decide (∃ a ∈ Finset.range k.size, a = r
        ∧ (decide (∀ b, A.cap j = some b → a < b) && k.testBit (A.pos j a)) = true) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro a ha rfl
      exact absurd (Finset.mem_range.mp ha) hr
    rw [hL]
    symm
    by_cases hv : ∀ b, A.cap j = some b → r < b
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_size_self k)
        (Nat.pow_le_pow_right (by norm_num) ((by omega : k.size ≤ r).trans (A.le_pos j r hv))))]
      simp
    · simp [hv]

/-- **`testBit` of `interleave` at an owned position.** Bit `i` of
`A.interleave f` is bit `A.rank i` of the component owning position `i`.
Position `i` appears in the double sum only as `pos j (rank i)` (`pos_inj` +
`pos_rank`); when `rank i` is at or above `(f j).size` both sides are
false. -/
theorem testBit_interleave_owned (f : Fin m → ℕ) {i : ℕ} {j : Fin m}
    (h : A.slotOf i = some j) :
    (A.interleave f).testBit i = (f j).testBit (A.rank i) := by
  obtain ⟨hpos, hvalid⟩ := A.pos_rank i j h
  unfold interleave
  rw [Finset.sum_sigma' Finset.univ
    (fun j' => (Finset.range (f j').size).filter (fun r => ∀ b, A.cap j' = some b → r < b))
    (fun j' r => if (f j').testBit r then 2 ^ (A.pos j' r) else 0)]
  rw [testBit_sum_pow (Finset.univ.sigma fun j' =>
      (Finset.range (f j').size).filter (fun r => ∀ b, A.cap j' = some b → r < b))
    (fun p => A.pos p.1 p.2) (fun p => (f p.1).testBit p.2) ?hinj i]
  case hinj =>
    rintro ⟨pj, pr⟩ hp ⟨qj, qr⟩ hq hpq
    have hp' := Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hp)).2
    have hq' := Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hq)).2
    obtain ⟨h1, h2⟩ := A.pos_inj hp'.2 hq'.2 hpq
    subst h1; subst h2; rfl
  by_cases hb : (f j).testBit (A.rank i) = true
  · rw [hb, decide_eq_true_eq]
    -- The bit is set, so the rank is below the size.
    have hrank : A.rank i < (f j).size := by
      by_contra hge
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_size_self _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hb
      exact Bool.false_ne_true hb
    exact ⟨⟨j, A.rank i⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrank, hvalid⟩⟩, hpos, hb⟩
  · simp only [Bool.not_eq_true] at hb
    rw [hb]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    rintro ⟨pj, pr⟩ hmem hposeq
    have hp' := Finset.mem_filter.mp (Finset.mem_sigma.mp hmem).2
    have hslot : A.slotOf i = some pj := by rw [← hposeq, A.pos_slotOf pj pr hp'.2]
    have hj : pj = j := Option.some.inj (hslot.symm.trans h)
    have hrank : A.rank i = pr := by rw [← hposeq, A.rank_pos pj pr hp'.2]
    subst hj
    rw [← hrank, hb]
    simp

/-- **`testBit` of `interleave` at an unowned position** is false: every
summand sits at an owned position (`pos_slotOf`). -/
theorem testBit_interleave_unowned (f : Fin m → ℕ) {i : ℕ}
    (h : A.slotOf i = none) : (A.interleave f).testBit i = false := by
  unfold interleave
  rw [Finset.sum_sigma' Finset.univ
    (fun j' => (Finset.range (f j').size).filter (fun r => ∀ b, A.cap j' = some b → r < b))
    (fun j' r => if (f j').testBit r then 2 ^ (A.pos j' r) else 0)]
  rw [testBit_sum_pow (Finset.univ.sigma fun j' =>
      (Finset.range (f j').size).filter (fun r => ∀ b, A.cap j' = some b → r < b))
    (fun p => A.pos p.1 p.2) (fun p => (f p.1).testBit p.2) ?hinj i]
  case hinj =>
    rintro ⟨pj, pr⟩ hp ⟨qj, qr⟩ hq hpq
    have hp' := Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hp)).2
    have hq' := Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hq)).2
    obtain ⟨h1, h2⟩ := A.pos_inj hp'.2 hq'.2 hpq
    subst h1; subst h2; rfl
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  rintro ⟨pj, pr⟩ hmem hposeq
  have hp' := Finset.mem_filter.mp (Finset.mem_sigma.mp hmem).2
  have hslot : A.slotOf i = some pj := by rw [← hposeq, A.pos_slotOf pj pr hp'.2]
  rw [h] at hslot
  exact fun _ => absurd hslot (by simp)

/-! ### The output bound and the round-trips -/

/-- **Unconditional capped-output bound.** A slot capped at `b` reads only
`b` bit positions, so its `deinterleave` output is below `2 ^ b` — for EVERY
counter `k`, valid or not. -/
theorem deinterleave_lt_two_pow {j : Fin m} {b : ℕ} (hb : A.cap j = some b) (k : ℕ) :
    A.deinterleave j k < 2 ^ b := by
  apply lt_two_pow_of_testBit_eq_false
  intro r hr
  rw [A.testBit_deinterleave]
  have hv : ¬∀ b', A.cap j = some b' → r < b' := fun h => absurd (h b hb) (by omega)
  simp [hv]

/-- **Left inverse.** Deinterleaving the interleaving of `f` recovers `f`,
provided each capped component is within its cap (`f j < 2 ^ b`): those are
exactly the bits the interleave can carry. -/
theorem deinterleave_interleave (f : Fin m → ℕ)
    (hf : ∀ j b, A.cap j = some b → f j < 2 ^ b) (j : Fin m) :
    A.deinterleave j (A.interleave f) = f j := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [A.testBit_deinterleave]
  by_cases hv : ∀ b, A.cap j = some b → r < b
  · rw [A.testBit_interleave_owned f (A.pos_slotOf j r hv), A.rank_pos j r hv,
      decide_eq_true hv, Bool.true_and]
  · -- Invalid rank: the guard is false, and bit `r` of `f j` is above the cap.
    have hbit : (f j).testBit r = false := by
      cases hcap : A.cap j with
      | none => exact absurd (fun b hb => absurd (hcap.symm.trans hb) (by simp)) hv
      | some b =>
        have hrb : ¬r < b :=
          fun hrb => hv fun b' hb' => Option.some.inj ((hcap.symm.trans hb')) ▸ hrb
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j b hcap)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hv, hbit]

/-- Interleaving only sets bits at owned positions. -/
theorem interleave_valid (f : Fin m → ℕ) : A.Valid (A.interleave f) := by
  intro i hbit
  show (A.slotOf i).isSome = true
  cases h : A.slotOf i with
  | none => rw [A.testBit_interleave_unowned f h] at hbit; exact absurd hbit (by simp)
  | some j => rfl

/-- **Right inverse.** Interleaving the deinterleaved components of a VALID
counter `k` recovers `k`: validity says no set bit of `k` sits at an unowned
position, and the owned bits round-trip through `pos_rank`. -/
theorem interleave_deinterleave (k : ℕ) (hk : A.Valid k) :
    A.interleave (A.deinterleaveTuple k) = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases h : A.slotOf i with
  | some j =>
    obtain ⟨hpos, hvalid⟩ := A.pos_rank i j h
    rw [A.testBit_interleave_owned _ h]
    show (A.deinterleave j k).testBit (A.rank i) = k.testBit i
    rw [A.testBit_deinterleave, hpos, decide_eq_true hvalid, Bool.true_and]
  | none =>
    rw [A.testBit_interleave_unowned _ h]
    cases hb : k.testBit i with
    | false => rfl
    | true =>
      have hown := hk i hb
      rw [Owned, h] at hown
      exact absurd hown (by simp)

end CappedBitAssignment

/-! ### The weight-1 drop-out rotation (Malachite's `update_bit_map`)

`update_bit_map` scans positions `0, 1, 2, …`, keeping a pointer that moves
through the ACTIVE slots in decreasing cyclic order (slot `m - 1` first);
each position goes to the pointed-at slot, and a slot leaves the active list
the moment its cap is used up. Because every active slot receives exactly
one position per sweep, the scan aggregates into ROUNDS: slot `j` is active
in round `t` iff its cap exceeds `t`, and round `t` emits its active slots
in decreasing order. All the maps below are `Finset` counts over that round
structure — no closed-form phase arithmetic. -/

namespace CappedRoundRobin

variable {m : ℕ}

/-- Slot `j` is still **active** in round `t`: its cap (if any) exceeds `t`.
This is precisely the validity guard for rank `t` at slot `j`. -/
def ActiveIn (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : Prop :=
  ∀ b, cap j = some b → t < b

instance (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : Decidable (ActiveIn cap t j) :=
  decidableCapGuard (cap j) t

/-- Activity is antitone in the round: active later means active earlier. -/
theorem ActiveIn.mono {cap : Fin m → Option ℕ} {t t' : ℕ} (h : t ≤ t') {j : Fin m}
    (ha : ActiveIn cap t' j) : ActiveIn cap t j :=
  fun b hb => Nat.lt_of_le_of_lt h (ha b hb)

/-- The number of active slots in round `t` — the number of positions the
round emits. -/
def roundSize (cap : Fin m → Option ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (ActiveIn cap t)).card

/-- The first position of round `t`: the total size of the earlier rounds. -/
def roundStart (cap : Fin m → Option ℕ) (t : ℕ) : ℕ :=
  ∑ t' ∈ Finset.range t, roundSize cap t'

/-- Slot `j`'s offset within round `t`: rounds emit active slots in
DECREASING order, so `j` comes after the active slots above it. -/
def offsetIn (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun j' => ActiveIn cap t j' ∧ j < j')).card

/-- The `r`-th position of slot `j`: its slot in round `r` (meaningful when
`j` is active in round `r`, i.e. at valid ranks). -/
def posFun (cap : Fin m → Option ℕ) (j : Fin m) (r : ℕ) : ℕ :=
  roundStart cap r + offsetIn cap r j

/-- The round containing position `i` (junk past the last round): the number
of rounds that finish at or before `i`. Rounds containing a position start
within `i + 1` rounds because every earlier round is nonempty. -/
def rankFun (cap : Fin m → Option ℕ) (i : ℕ) : ℕ :=
  ((Finset.range (i + 1)).filter (fun t => roundStart cap (t + 1) ≤ i)).card

/-- The slot owning position `i`: the active slot of round `rankFun i` whose
position lands on `i`, if any. -/
def slotOfFun (cap : Fin m → Option ℕ) (i : ℕ) : Option (Fin m) :=
  (List.finRange m).find? fun j =>
    decide (ActiveIn cap (rankFun cap i) j) && (posFun cap j (rankFun cap i) == i)

/-- `roundStart` unfolds one round at a time. -/
theorem roundStart_succ (cap : Fin m → Option ℕ) (t : ℕ) :
    roundStart cap (t + 1) = roundStart cap t + roundSize cap t :=
  Finset.sum_range_succ _ t

/-- `roundStart` is monotone. -/
theorem roundStart_le_roundStart (cap : Fin m → Option ℕ) {t t' : ℕ} (h : t ≤ t') :
    roundStart cap t ≤ roundStart cap t' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- A round with an active slot is nonempty. -/
theorem one_le_roundSize {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (h : ActiveIn cap t j) : 1 ≤ roundSize cap t :=
  Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩

/-- If round `t` still has an active slot, all earlier rounds are nonempty,
so round `t` starts at position `t` or later. -/
theorem le_roundStart {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (h : ActiveIn cap t j) : t ≤ roundStart cap t := by
  calc t = ∑ _t' ∈ Finset.range t, 1 := by simp
    _ ≤ roundStart cap t := Finset.sum_le_sum fun t' ht' =>
        one_le_roundSize (h.mono (Nat.le_of_lt (Finset.mem_range.mp ht')))

/-- An active slot's offset is within its round. -/
theorem offsetIn_lt_roundSize {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (h : ActiveIn cap t j) : offsetIn cap t j < roundSize cap t := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩, by simp⟩)
  intro j' hj'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
  exact hj'.1

/-- Offsets strictly DECREASE up the active slots: the active slots above
`j` are a strict superset of those above a larger active `j'`. -/
theorem offsetIn_lt_offsetIn {cap : Fin m → Option ℕ} {t : ℕ} {j j' : Fin m}
    (hact : ActiveIn cap t j') (hlt : j < j') :
    offsetIn cap t j' < offsetIn cap t j := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨j', ?_, ?_⟩)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, lt_trans hlt hx.2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hact, hlt⟩
  · simp

/-- A valid position of a slot lies before the end of its round. -/
theorem posFun_lt_roundStart_succ {cap : Fin m → Option ℕ} {j : Fin m} {r : ℕ}
    (h : ActiveIn cap r j) : posFun cap j r < roundStart cap (r + 1) := by
  rw [roundStart_succ]
  exact Nat.add_lt_add_left (offsetIn_lt_roundSize h) _

/-- `rankFun` recovers the round: a position between `roundStart t` and
`roundStart (t + 1)` has rank `t`. -/
theorem rankFun_eq {cap : Fin m → Option ℕ} {t i : ℕ}
    (h1 : roundStart cap t ≤ i) (h2 : i < roundStart cap (t + 1)) :
    rankFun cap i = t := by
  have hsize : 1 ≤ roundSize cap t := by
    rw [roundStart_succ] at h2; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hsize
  have hts : t ≤ roundStart cap t := le_roundStart (Finset.mem_filter.mp hj).2
  have hset : (Finset.range (i + 1)).filter (fun t' => roundStart cap (t' + 1) ≤ i)
      = Finset.range t := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hle⟩
      by_contra hge
      have := Nat.le_trans (roundStart_le_roundStart cap (by omega : t + 1 ≤ t' + 1)) hle
      omega
    · intro hlt
      exact ⟨by omega, Nat.le_trans (roundStart_le_roundStart cap (by omega : t' + 1 ≤ t)) h1⟩
  rw [rankFun, hset, Finset.card_range]

/-- Every offset below the round size is attained by an active slot: the
offset map is injective from the active set into `range (roundSize t)`, and
the two sets have equal cardinality. -/
theorem exists_active_offsetIn_eq {cap : Fin m → Option ℕ} {t d : ℕ}
    (hd : d < roundSize cap t) : ∃ j, ActiveIn cap t j ∧ offsetIn cap t j = d := by
  have hmaps : Set.MapsTo (offsetIn cap t) ↑(Finset.univ.filter (ActiveIn cap t))
      ↑(Finset.range (roundSize cap t)) := by
    intro j hj
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr
      (offsetIn_lt_roundSize (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2))
  have hinj : Set.InjOn (offsetIn cap t) ↑(Finset.univ.filter (ActiveIn cap t)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have := offsetIn_lt_offsetIn hb' hlt; omega
    · exact heq
    · have := offsetIn_lt_offsetIn ha' hgt; omega
  have hcard : (Finset.range (roundSize cap t)).card
      ≤ (Finset.univ.filter (ActiveIn cap t)).card := by
    rw [Finset.card_range]; exact Nat.le_refl _
  obtain ⟨j, hj, hjd⟩ := Finset.surjOn_of_injOn_of_card_le (offsetIn cap t) hmaps hinj hcard
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hd))
  exact ⟨j, (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2, hjd⟩

/-- Every position within a round is some active slot's position. -/
theorem exists_posFun_eq {cap : Fin m → Option ℕ} {t i : ℕ}
    (h1 : roundStart cap t ≤ i) (h2 : i < roundStart cap (t + 1)) :
    ∃ j, ActiveIn cap t j ∧ posFun cap j t = i := by
  have hd : i - roundStart cap t < roundSize cap t := by
    rw [roundStart_succ] at h2; omega
  obtain ⟨j, hact, hoff⟩ := exists_active_offsetIn_eq hd
  refine ⟨j, hact, ?_⟩
  rw [posFun, hoff]
  omega

end CappedRoundRobin

open CappedRoundRobin in
/-- **Malachite's weight-1 drop-out rotation** (`update_bit_map` with all
weights 1): among the slots still below their caps, positions are assigned
in decreasing cyclic slot order, slot `m - 1` first; a slot drops out of the
rotation once it has received its `cap`-many positions. With `cap ≡ none`
this is exactly `roundRobin` (`cappedRoundRobin_pos_none`). -/
def cappedRoundRobin (cap : Fin m → Option ℕ) : CappedBitAssignment m where
  cap := cap
  slotOf := slotOfFun cap
  rank := rankFun cap
  pos := posFun cap
  pos_slotOf := fun j r h => by
    have hrank : rankFun cap (posFun cap j r) = r :=
      rankFun_eq (Nat.le_add_right _ _) (posFun_lt_roundStart_succ h)
    unfold slotOfFun
    rw [hrank]
    have hjpred : (decide (ActiveIn cap r j) && (posFun cap j r == posFun cap j r)) = true := by
      simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
      exact h
    obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp
      ((List.find?_isSome (xs := List.finRange m) (p := fun j' =>
          decide (ActiveIn cap r j') && (posFun cap j' r == posFun cap j r))).mpr
        ⟨j, List.mem_finRange j, hjpred⟩)
    have hj'pred := List.find?_some hj'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hj'pred
    have hoff : offsetIn cap r j' = offsetIn cap r j := by
      have := hj'pred.2
      unfold posFun at this
      omega
    have hjj' : j' = j := by
      rcases lt_trichotomy j' j with hlt | heq | hgt
      · have := offsetIn_lt_offsetIn (t := r) h hlt; omega
      · exact heq
      · have := offsetIn_lt_offsetIn (t := r) hj'pred.1 hgt; omega
    rw [hj', hjj']
  rank_pos := fun j r h =>
    rankFun_eq (Nat.le_add_right _ _) (posFun_lt_roundStart_succ h)
  pos_rank := fun i j h => by
    unfold slotOfFun at h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨hp.2, hp.1⟩
  pos_lt_pos := fun j r r' h hlt =>
    Nat.lt_of_lt_of_le (posFun_lt_roundStart_succ (ActiveIn.mono (Nat.le_of_lt hlt) h))
      (Nat.le_trans (roundStart_le_roundStart cap hlt) (Nat.le_add_right _ _))

namespace CappedRoundRobin

variable {m : ℕ}

/-- Positions within a round are owned. -/
theorem owned_of_round {cap : Fin m → Option ℕ} {t i : ℕ}
    (h1 : roundStart cap t ≤ i) (h2 : i < roundStart cap (t + 1)) :
    (cappedRoundRobin cap).Owned i := by
  obtain ⟨j, hact, hpos⟩ := exists_posFun_eq h1 h2
  have hpos' : (cappedRoundRobin cap).pos j t = i := hpos
  have hslot : (cappedRoundRobin cap).slotOf i = some j := by
    rw [← hpos']
    exact (cappedRoundRobin cap).pos_slotOf j t hact
  show ((cappedRoundRobin cap).slotOf i).isSome = true
  rw [hslot]
  rfl

/-- Positions below some `roundStart` are owned: locate the containing round
with `Nat.find`. -/
theorem owned_of_exists_lt_roundStart {cap : Fin m → Option ℕ} {i : ℕ}
    (h : ∃ t, i < roundStart cap t) : (cappedRoundRobin cap).Owned i := by
  have hspec := Nat.find_spec h
  have hne : Nat.find h ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp [roundStart] at hspec
  obtain ⟨t, ht⟩ : ∃ t, Nat.find h = t + 1 := ⟨Nat.find h - 1, by omega⟩
  have h1 : ¬i < roundStart cap t := Nat.find_min h (by omega)
  rw [ht] at hspec
  exact owned_of_round (Nat.le_of_not_lt h1) hspec

/-- With every slot capped, activity in round `t` says the cap exceeds `t`. -/
theorem activeIn_allCapped (b : Fin m → ℕ) (t : ℕ) (j : Fin m) :
    ActiveIn (fun j' => some (b j')) t j ↔ t < b j := by
  constructor
  · intro h
    exact h (b j) rfl
  · intro h b' hb'
    exact Option.some.inj hb' ▸ h

/-- With every slot capped by `b`, round `t` starts at `∑ j, min t (b j)`:
slot `j` contributes one position to each of its first `b j` rounds. -/
theorem roundStart_allCapped (b : Fin m → ℕ) (t : ℕ) :
    roundStart (fun j => some (b j)) t = ∑ j, min t (b j) := by
  calc roundStart (fun j => some (b j)) t
      = ∑ t' ∈ Finset.range t, ∑ j : Fin m, if t' < b j then 1 else 0 := by
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [roundSize, Finset.card_filter]
        exact Finset.sum_congr rfl fun j _ => by simp [activeIn_allCapped]
    _ = ∑ j : Fin m, ∑ t' ∈ Finset.range t, if t' < b j then 1 else 0 := Finset.sum_comm
    _ = ∑ j : Fin m, min t (b j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.card_filter]
        have h : (Finset.range t).filter (fun t' => t' < b j) = Finset.range (min t (b j)) := by
          ext x
          simp
        rw [h, Finset.card_range]

end CappedRoundRobin

/-! ### Ownership characterizations for `cappedRoundRobin` -/

/-- **An uncapped slot keeps every round alive**, so every position is
owned: `slotOf` never returns `none`. -/
theorem cappedRoundRobin_owned_of_none {m : ℕ} {cap : Fin m → Option ℕ} {j₀ : Fin m}
    (h : cap j₀ = none) (i : ℕ) : (cappedRoundRobin cap).Owned i := by
  apply CappedRoundRobin.owned_of_exists_lt_roundStart
  have hact : CappedRoundRobin.ActiveIn cap (i + 1) j₀ := by
    intro b hb
    rw [h] at hb
    exact absurd hb (by simp)
  exact ⟨i + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (CappedRoundRobin.le_roundStart hact)⟩

/-- With an uncapped slot present, every counter is valid. -/
theorem cappedRoundRobin_valid_of_none {m : ℕ} {cap : Fin m → Option ℕ} {j₀ : Fin m}
    (h : cap j₀ = none) (k : ℕ) : (cappedRoundRobin cap).Valid k :=
  fun i _ => cappedRoundRobin_owned_of_none h i

/-- **All-capped ownership**: with every slot capped by `b`, exactly the
first `∑ j, b j` positions are owned. -/
theorem cappedRoundRobin_owned_iff {m : ℕ} (b : Fin m → ℕ) (i : ℕ) :
    (cappedRoundRobin (fun j => some (b j))).Owned i ↔ i < ∑ j, b j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hpos, hvalid⟩ := (cappedRoundRobin (fun j' => some (b j'))).pos_rank i j hj
    have hlt : (cappedRoundRobin (fun j' => some (b j'))).pos j
          ((cappedRoundRobin (fun j' => some (b j'))).rank i)
        < CappedRoundRobin.roundStart (fun j' => some (b j'))
          ((cappedRoundRobin (fun j' => some (b j'))).rank i + 1) :=
      CappedRoundRobin.posFun_lt_roundStart_succ hvalid
    rw [hpos] at hlt
    refine Nat.lt_of_lt_of_le hlt ?_
    rw [CappedRoundRobin.roundStart_allCapped]
    exact Finset.sum_le_sum fun j' _ => Nat.min_le_right _ _
  · intro h
    apply CappedRoundRobin.owned_of_exists_lt_roundStart
    refine ⟨∑ j, b j, ?_⟩
    rw [CappedRoundRobin.roundStart_allCapped]
    calc i < ∑ j, b j := h
      _ = ∑ j, min (∑ j', b j') (b j) := Finset.sum_congr rfl fun j _ =>
          (min_eq_right (Finset.single_le_sum (fun j' _ => Nat.zero_le (b j'))
            (Finset.mem_univ j))).symm

/-- **All-capped validity**: with every slot capped by `b`, the valid
counters are exactly `k < 2 ^ ∑ j, b j`. -/
theorem cappedRoundRobin_valid_iff {m : ℕ} (b : Fin m → ℕ) (k : ℕ) :
    (cappedRoundRobin (fun j => some (b j))).Valid k ↔ k < 2 ^ ∑ j, b j := by
  constructor
  · intro h
    apply lt_two_pow_of_testBit_eq_false
    intro i hi
    by_contra hbit
    simp only [Bool.not_eq_false] at hbit
    have := (cappedRoundRobin_owned_iff b i).mp (h i hbit)
    omega
  · intro h i hbit
    rw [cappedRoundRobin_owned_iff]
    have h2 : 2 ^ i ≤ k := Nat.ge_two_pow_of_testBit hbit
    by_contra hge
    have : (2 : ℕ) ^ ∑ j, b j ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-! ### Degeneration to `roundRobin` -/

/-- With no caps, every slot is active in every round, so round `r` starts at
`r * m`, slot `j` sits at offset `m - 1 - j`, and `pos` is exactly the
uncapped `roundRobin` assignment. -/
theorem cappedRoundRobin_pos_none {m : ℕ} (hm : 0 < m) (j : Fin m) (r : ℕ) :
    (cappedRoundRobin (fun _ : Fin m => none)).pos j r = (roundRobin m hm).pos j r := by
  have hact : ∀ t (j' : Fin m), CappedRoundRobin.ActiveIn (fun _ : Fin m => none) t j' :=
    fun _ _ _ hb => nomatch hb
  have hsize : ∀ t, CappedRoundRobin.roundSize (fun _ : Fin m => none) t = m := by
    intro t
    rw [CappedRoundRobin.roundSize, Finset.filter_true_of_mem fun j' _ => hact t j',
      Finset.card_univ, Fintype.card_fin]
  have hstart : CappedRoundRobin.roundStart (fun _ : Fin m => none) r = r * m := by
    rw [CappedRoundRobin.roundStart, Finset.sum_congr rfl fun t _ => hsize t,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hoff : CappedRoundRobin.offsetIn (fun _ : Fin m => none) r j = m - 1 - j.val := by
    rw [CappedRoundRobin.offsetIn]
    have hfilter : (Finset.univ.filter
          (fun j' => CappedRoundRobin.ActiveIn (fun _ : Fin m => none) r j' ∧ j < j'))
        = Finset.Ioi j := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
      exact ⟨fun h => h.2, fun h => ⟨hact r j', h⟩⟩
    rw [hfilter, Fin.card_Ioi]
  show CappedRoundRobin.posFun (fun _ : Fin m => none) j r = r * m + (m - 1 - j.val)
  rw [CappedRoundRobin.posFun, hstart, hoff]

/-- With no caps, `slotOf` is `some` of the `roundRobin` slot. -/
theorem cappedRoundRobin_slotOf_none {m : ℕ} (hm : 0 < m) (i : ℕ) :
    (cappedRoundRobin (fun _ : Fin m => none)).slotOf i = some ((roundRobin m hm).slotOf i) := by
  have hpos : (cappedRoundRobin (fun _ : Fin m => none)).pos ((roundRobin m hm).slotOf i)
      ((roundRobin m hm).rank i) = i := by
    rw [cappedRoundRobin_pos_none hm]
    exact (roundRobin m hm).pos_rank i
  have hslot := (cappedRoundRobin (fun _ : Fin m => none)).pos_slotOf
    ((roundRobin m hm).slotOf i) ((roundRobin m hm).rank i) fun _ hb => nomatch hb
  rw [hpos] at hslot
  exact hslot

/-! ### Guards (pin `update_bit_map`'s drop-out rotation)

Weight-1 `update_bit_map` trace for `cap = ![some 2, none]` (slot 0 capped
at 2): rounds emit active slots in decreasing order, so round 0 emits
`1, 0`, round 1 emits `1, 0` — exhausting slot 0's cap — and every later
round emits `1` alone: positions `1, 3` belong to slot 0, all others to
slot 1. (The task-description table `[1, 0, 1, 0, 0, 0, …]` is realized by
the MIRRORED vector `![none, some 2]`; with `![some 2, none]` it would let
slot 0 own infinitely many positions despite `cap 0 = some 2`, contradicting
`pos_rank`. `update_bit_map`'s `set_max_bits` doctest pins the cap to the
output index, as here.) -/

#guard (let A := cappedRoundRobin ![some 2, none];
  (List.range 8).map A.slotOf)
  = [some 1, some 0, some 1, some 0, some 1, some 1, some 1, some 1]
#guard (let A := cappedRoundRobin ![none, some 2];
  (List.range 8).map A.slotOf)
  = [some 1, some 0, some 1, some 0, some 0, some 0, some 0, some 0]

-- Symmetric caps `![some 3, some 3]`: pure alternation for 6 positions, then
-- unowned; `Owned i ↔ i < 6` and `Valid k ↔ k < 64`.
#guard (let A := cappedRoundRobin ![some 3, some 3];
  (List.range 8).map A.slotOf)
  = [some 1, some 0, some 1, some 0, some 1, some 0, none, none]
#guard (let A := cappedRoundRobin ![some 3, some 3];
  (List.range 10).map (fun i => decide (A.Owned i)))
  = [true, true, true, true, true, true, false, false, false, false]
#guard (let A := cappedRoundRobin ![some 3, some 3];
  (List.range 80).all fun k => decide (A.Valid k) == decide (k < 64))

-- No caps: `slotOf` matches `roundRobin 2`.
#guard (let A := cappedRoundRobin (fun _ : Fin 2 => none);
  let B := roundRobin 2 (by norm_num);
  (List.range 6).map A.slotOf = (List.range 6).map (fun i => some (B.slotOf i)))

-- 3-slot mixed `![some 1, none, some 2]`, hand-computed from
-- `update_bit_map`: round 0 emits `2, 1, 0` (slot 0 exhausted, cap 1);
-- round 1 emits `2, 1` (slot 2 exhausted, cap 2); rounds ≥ 2 emit `1` alone.
--   positions:  0  1  2  3  4  5  6  7
--   slots:      2  1  0  2  1  1  1  1
#guard (let A := cappedRoundRobin ![some 1, none, some 2];
  (List.range 8).map A.slotOf)
  = [some 2, some 1, some 0, some 2, some 1, some 1, some 1, some 1]

-- A cap of 0 means the slot owns nothing at all (`card = 1` components).
#guard (let A := cappedRoundRobin ![some 0, none];
  (List.range 4).map A.slotOf) = [some 1, some 1, some 1, some 1]

-- Round-trips. `![some 2, none]` has an uncapped slot, so every `k` is
-- valid; `f 0 = 3 < 2 ^ 2` respects slot 0's cap.
#guard (let A := cappedRoundRobin ![some 2, none];
  (A.deinterleave 0 (A.interleave ![3, 11]), A.deinterleave 1 (A.interleave ![3, 11]))) == (3, 11)
#guard (let A := cappedRoundRobin ![some 2, none];
  (List.range 40).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
#guard (let A := cappedRoundRobin ![some 3, some 3];
  (List.range 64).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
#guard (let A := cappedRoundRobin ![some 1, none, some 2];
  (List.range 32).all fun k =>
    A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k, A.deinterleave 2 k] == k)

-- The unconditional capped-output bound, at arbitrary (even invalid) `k`.
#guard (let A := cappedRoundRobin ![some 2, none];
  (List.range 200).all fun k => A.deinterleave 0 k < 4)

end Azurite
