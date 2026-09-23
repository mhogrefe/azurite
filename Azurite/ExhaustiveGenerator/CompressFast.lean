/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `CompressFast` — fast rank/unrank for capped-product compression.

  `Compress.lean`'s `rankSpec`/`unrank` are linear scans of the raw counters,
  infeasible for compressing products with large non-power-of-two cards (the
  polynomial-coefficient case, e.g. an `AzZMod p` component). This file builds
  the closed-form counting route for the capped fair products of
  `FairCapped.lean` (which imports this file), whose live counters are exactly

    `Live cap cards k  :=  Valid k ∧ ∀ capped slot j, deinterleave j k < cards j`

  (the liveness bridges `fair*GenCapped_gen_isSome_iff`, proved next to the
  raw builders in `FairCapped.lean` — the guard shape of those builders).

  * `countBelow cap cards n` computes `#{k < n | Live k}` WITHOUT scanning, by
    the **first-differing-bit partition**: `k < n` iff `k` agrees with `n` at
    all positions above some set bit `i` of `n` and has bit `i` clear
    (`lt_iff_exists_diff_bit`). Within the class of a set bit `i` the live
    counters factor as a PRODUCT over slots of per-slot completion counts: a
    slot's high bits are pinned by `n`'s prefix (`deinterleave` of
    `(n >>> (i+1)) <<< (i+1)`, which also absorbs the forced 0 at position
    `i`), its low bits are free, and for a capped slot the in-range choices
    are counted by the clamp formula `min 2^f (c - p·2^f)`
    (`card_filter_range_add_lt`). Validity is folded in by clipping `n` to
    `2 ^ ∑ bits` when every slot is capped (`totalBits`); after the clip every
    class prefix is automatically `Valid`, and the class bijection
    (`card_class`) needs no ownership side conditions at all.
  * `countBelow_eq_card` is the counting correctness (`= Finset`-filter card),
    and `countBelow_eq_rankSpec` bridges to `rankSpec g` for ANY generator
    whose liveness is `Live cap cards` (the raw capped builders).
  * `fastUnrank` finds the `i`-th live counter as the least `k` with
    `i < countBelow (k + 1)`, by a doubling upper bound (`Nat.find` over
    `countBelow (2 ^ t)` — the existence witness is the SLOW `unrank`, erased
    at runtime) plus monotone binary search (`binSearch`).
    `fastUnrank_eq_unrank` pins it to the spec `unrank` via the order-iso
    uniqueness (`rankSpec_unrank`/`eq_of_rankSpec_eq`).
  * `compressFast` is the drop-in the `FairCapped.lean` instances are built
    on: gen-pointwise IDENTICAL to `compress` (`compressFast_gen_eq_compress`)
    with `unrank` replaced by `fastUnrank`; `compressFast_contiguous` and
    `FiniteGenerator.ofCompressFast` transport the companion instances.

  The position arithmetic is made cheap first: `roundStart` has the closed
  form `∑ j, min t (cap j)` (`roundStart_eq_sum`, generalizing
  `roundStart_allCapped` to mixed caps), so `posFast`/`deiFast` avoid the
  quadratic per-round rescan of `posFun`/`deinterleave` — `countBelow` runs in
  `O(bits² · m)` overall and `fastUnrank` in `O(bits³ · m)`, instant at any
  depth (see the `10^12 + 39`-card scale guards in `FairCapped.lean`, where
  the spec path would scan ~`1.3 × 10^9` raw counters).
-/
import Azurite.ExhaustiveGenerator.BitInterleaveCapped
import Azurite.ExhaustiveGenerator.Compress
import Mathlib.Data.Fintype.BigOperators

namespace Azurite

/-! ### ℕ bit toolkit -/

/-- **The first-differing-bit partition of `k < n`.** `k` is below `n` exactly
when, at some SET bit `i` of `n`, `k` has bit `i` clear and agrees with `n`
everywhere above `i`. The witness `i` (the highest differing bit) is unique —
see `diff_bit_unique` — so the classes over the set bits of `n` partition
`[0, n)`. -/
theorem lt_iff_exists_diff_bit {k n : ℕ} :
    k < n ↔ ∃ i, n.testBit i = true ∧ k.testBit i = false ∧
      ∀ i', i < i' → k.testBit i' = n.testBit i' := by
  constructor
  · intro hkn
    have hne : k ^^^ n ≠ 0 := by
      intro h0
      have hkeq : k = n := Nat.eq_of_testBit_eq fun i => by
        have h := congrArg (fun x => x.testBit i) h0
        simp only [Nat.testBit_xor, Nat.zero_testBit] at h
        revert h
        cases k.testBit i <;> cases n.testBit i <;> simp
      omega
    obtain ⟨i, hbit, hhigh⟩ := Nat.exists_most_significant_bit hne
    have hagree : ∀ i', i < i' → k.testBit i' = n.testBit i' := by
      intro i' hi'
      have h := hhigh i' hi'
      rw [Nat.testBit_xor] at h
      revert h
      cases k.testBit i' <;> cases n.testBit i' <;> simp
    rw [Nat.testBit_xor] at hbit
    rcases hk : k.testBit i with _ | _ <;> rcases hn : n.testBit i with _ | _
    · rw [hk, hn] at hbit; exact absurd hbit (by simp)
    · exact ⟨i, hn, hk, hagree⟩
    · -- `k` set, `n` clear above-agreeing: forces `n < k`, contradicting `k < n`.
      exact absurd (Nat.lt_of_testBit i hn hk fun j hj => (hagree j hj).symm) (by omega)
    · rw [hk, hn] at hbit; exact absurd hbit (by simp)
  · rintro ⟨i, hn, hk, hagree⟩
    exact Nat.lt_of_testBit i hk hn hagree

/-- The first-differing-bit witness is unique (this makes the classes
disjoint). -/
theorem diff_bit_unique {k n i i' : ℕ}
    (h : k.testBit i = false ∧ ∀ p, i < p → k.testBit p = n.testBit p)
    (h' : k.testBit i' = false ∧ ∀ p, i' < p → k.testBit p = n.testBit p)
    (hn : n.testBit i = true) (hn' : n.testBit i' = true) : i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := h.2 i' hlt
    rw [h'.1, hn'] at this
    exact absurd this (by simp)
  · exact heq
  · have := h'.2 i hgt
    rw [h.1, hn] at this
    exact absurd this (by simp)

/-- `testBit` of a sum whose left addend is a multiple of `2 ^ f` and whose
right addend is below `2 ^ f`: the bits simply concatenate. -/
theorem testBit_add_of_mod_eq_zero {a b f : ℕ} (ha : a % 2 ^ f = 0) (hb : b < 2 ^ f)
    (p : ℕ) : (a + b).testBit p = if p < f then b.testBit p else a.testBit p := by
  obtain ⟨q, hq⟩ : 2 ^ f ∣ a := Nat.dvd_of_mod_eq_zero ha
  subst hq
  rw [Nat.testBit_two_pow_mul_add q hb p]
  by_cases hp : p < f
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp,
      show 2 ^ f * q = q <<< f by rw [Nat.shiftLeft_eq, Nat.mul_comm],
      Nat.testBit_shiftLeft]
    simp [Nat.le_of_not_lt hp]

/-- **The clamp formula**: among the `2 ^ f`-many free completions `x` of a
fixed prefix contribution `D`, exactly `min (2 ^ f) (c - D)` land below the
card `c` (`0` when the prefix alone is already out of range — ℕ-truncation). -/
theorem card_filter_range_add_lt (F D c : ℕ) :
    ((Finset.range F).filter fun x => D + x < c).card = min F (c - D) := by
  rw [show (Finset.range F).filter (fun x => D + x < c) = Finset.range (min F (c - D)) by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
    omega]
  exact Finset.card_range _

/-! ### Fast round-robin position arithmetic

`posFun`'s `roundStart` re-scans every earlier round; the closed form below
(each slot contributes one position to each of its first `cap j` rounds)
makes a single position `O(m)` and a full `deiFast` `O(bits · m)`. -/

namespace CappedRoundRobin

variable {m : ℕ}

/-- Closed form for `roundStart` with MIXED caps: slot `j` contributes one
position to each of its first `min t (cap j)` rounds (all `t` when uncapped).
Generalizes `roundStart_allCapped`. -/
theorem roundStart_eq_sum (cap : Fin m → Option ℕ) (t : ℕ) :
    roundStart cap t = ∑ j, (cap j).elim t (min t) := by
  calc roundStart cap t
      = ∑ t' ∈ Finset.range t, ∑ j : Fin m, if ActiveIn cap t' j then 1 else 0 := by
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [roundSize, Finset.card_filter]
    _ = ∑ j : Fin m, ∑ t' ∈ Finset.range t, if ActiveIn cap t' j then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ j : Fin m, (cap j).elim t (min t) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases hc : cap j with _ | b
        · -- Uncapped: active in every round.
          have hone : ∀ t' ∈ Finset.range t, (if ActiveIn cap t' j then 1 else 0) = 1 :=
            fun t' _ => ite_eq_left fun b hb => nomatch hc.symm.trans hb
          rw [Finset.sum_congr rfl hone]
          simp
        · -- Capped at `b`: active in exactly the first `b` rounds.
          have hiff : ∀ t' ∈ Finset.range t, (if ActiveIn cap t' j then 1 else 0)
              = if t' < b then 1 else 0 := by
            intro t' _
            by_cases h : t' < b
            · have ha : ActiveIn cap t' j := fun b' hb' =>
                Option.some.inj (hc.symm.trans hb') ▸ h
              rw [ite_eq_left h, ite_eq_left ha]
            · have hna : ¬ActiveIn cap t' j := fun ha => h (ha b hc)
              rw [ite_eq_right hna, ite_eq_right h]
          rw [Finset.sum_congr rfl hiff, ← Finset.card_filter,
            show (Finset.range t).filter (fun t' => t' < b) = Finset.range (min t b) by
              ext x; simp]
          simp [Finset.card_range]

/-- `posFun` through the closed-form `roundStart`: a single position in
`O(m)`. -/
def posFast (cap : Fin m → Option ℕ) (j : Fin m) (r : ℕ) : ℕ :=
  (∑ j', (cap j').elim r (min r)) + offsetIn cap r j

theorem posFast_eq (cap : Fin m → Option ℕ) (j : Fin m) (r : ℕ) :
    posFast cap j r = posFun cap j r := by
  rw [posFast, posFun, roundStart_eq_sum]

end CappedRoundRobin

/-! ### The capped-product liveness predicate and `countBelow` -/

namespace CompressFast

open CappedRoundRobin

variable {m : ℕ}

/-- `deinterleave` of `cappedRoundRobin cap` through the fast position
arithmetic (`posFast`): `O(bits · m)` per call. -/
def deiFast (cap : Fin m → Option ℕ) (j : Fin m) (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k.size,
    if decide (∀ b, cap j = some b → r < b) && k.testBit (posFast cap j r) then 2 ^ r else 0

theorem deiFast_eq (cap : Fin m → Option ℕ) (j : Fin m) (k : ℕ) :
    deiFast cap j k = (cappedRoundRobin cap).deinterleave j k :=
  Finset.sum_congr rfl fun r _ => by rw [posFast_eq]; rfl

/-- The total counter-bit budget: `some (∑ j, b j)` when EVERY slot is capped
(no counter at or above `2 ^ ∑ b` is valid), `none` when some slot is
uncapped (every counter is valid). -/
def totalBits (cap : Fin m → Option ℕ) : Option ℕ :=
  if h : ∀ j, (cap j).isSome then some (∑ j, (cap j).get (h j)) else none

/-- **The capped-product liveness predicate**: counter `k` is live when it is
valid for the assignment and every CAPPED slot's decoded index is below that
slot's card (infinite slots are unconstrained). This is exactly when the raw
capped fair builders produce a value at `k`
(`fairPairGenCapped_gen_isSome_iff` and friends). -/
def Live (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) (k : ℕ) : Prop :=
  (cappedRoundRobin cap).Valid k ∧
    ∀ j b, cap j = some b → (cappedRoundRobin cap).deinterleave j k < cards j

instance (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) (k : ℕ) :
    Decidable (Live cap cards k) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- The per-slot factor of a `countBelow` class: with `2 ^ f - 1 =
deiFast … (2 ^ i - 1)` counting the slot's FREE low bits below position `i`
and `D = deiFast … hi` its FIXED high-bit contribution from the class prefix
`hi`, an uncapped slot admits all `2 ^ f` completions and a capped one the
clamped `min (2 ^ f) (cards j - D)`. -/
def slotCount (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) (j : Fin m) (i : ℕ)
    (hi : ℕ) : ℕ :=
  match cap j with
  | none => deiFast cap j (2 ^ i - 1) + 1
  | some _ => min (deiFast cap j (2 ^ i - 1) + 1) (cards j - deiFast cap j hi)

/-- **The digit DP**: `countBelow cap cards n = #{k < n | Live k}`, computed
in `O(bits² · m)` — clip `n` to the valid-counter budget (`totalBits`), then
sum over the SET bits `i` of the clipped `n'` the product over slots of the
per-slot completion counts of the class prefix `(n' >>> (i+1)) <<< (i+1)`
(which pins the high bits AND the forced 0 at position `i`). Correctness is
`countBelow_eq_card`; the bridge to generator ranks is
`countBelow_eq_rankSpec`. -/
def countBelow (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) (n : ℕ) : ℕ :=
  let n' := match totalBits cap with
    | some B => min n (2 ^ B)
    | none => n
  ∑ i ∈ Finset.range n'.size,
    if n'.testBit i then ∏ j, slotCount cap cards j i ((n' >>> (i + 1)) <<< (i + 1))
    else 0

/-! ### Ownership through `totalBits` -/

/-- `cappedRoundRobin`'s two ownership regimes in a single guard: position `p`
is owned exactly when it lies under the `totalBits` budget (vacuous with an
uncapped slot present). -/
theorem owned_iff_totalBits (cap : Fin m → Option ℕ) (p : ℕ) :
    (cappedRoundRobin cap).Owned p ↔ Under (totalBits cap) p := by
  rw [totalBits]
  split
  · next h =>
    obtain ⟨b, hb⟩ : ∃ b : Fin m → ℕ, ∀ j, cap j = some (b j) :=
      ⟨fun j => (cap j).get (h j), fun j => (Option.some_get (h j)).symm⟩
    have hcap : cap = fun j => some (b j) := funext hb
    subst hcap
    rw [cappedRoundRobin_owned_iff b p, under_some_iff]
    simp
  · next h =>
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hjn : cap j = none := Option.not_isSome_iff_eq_none.mp hj
    exact ⟨fun _ => under_none p, fun _ => cappedRoundRobin_owned_of_none hjn p⟩

/-- With every slot capped, a valid counter lies below `2 ^ totalBits`. -/
theorem valid_lt_two_pow_of_totalBits {cap : Fin m → Option ℕ} {B k : ℕ}
    (htb : totalBits cap = some B) (hv : (cappedRoundRobin cap).Valid k) : k < 2 ^ B := by
  apply lt_two_pow_of_testBit_eq_false
  intro p hp
  by_contra hbit
  simp only [Bool.not_eq_false] at hbit
  have hown := (owned_iff_totalBits cap p).mp (hv p hbit)
  rw [htb] at hown
  exact absurd (under_some_iff.mp hown) (by omega)

/-! ### The per-slot bit split at a class boundary

Fix a boundary position `i`. Each slot `j` reads a slot-local INITIAL SEGMENT
of ranks below the boundary (its positions ascend): `f` many, with
`deinterleave j (2 ^ i - 1) = 2 ^ f - 1` (the free-bit count of the digit DP)
— and any counter that splits as `prefix + low` at the boundary has its
`deinterleave` split accordingly. -/

/-- Slot `j`'s ranks with positions below `i` form an initial segment
`[0, f)`, `2 ^ f - 1 = deinterleave j (2 ^ i - 1)` (so `f` is computable),
and `f` is at most the slot's cap. -/
theorem exists_freeCount (A : CappedBitAssignment m) (j : Fin m) (i : ℕ) :
    ∃ f, A.deinterleave j (2 ^ i - 1) + 1 = 2 ^ f
      ∧ (∀ r, ((∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) ↔ r < f)
      ∧ (∀ b, A.cap j = some b → f ≤ b) := by
  set S := (Finset.range i).filter
    (fun r => (∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) with hS
  have hmem : ∀ r, r ∈ S ↔ ((∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) := by
    intro r
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_of_le_of_lt (A.le_pos j r h.1) h.2, h⟩⟩
  have hchar : ∀ r, ((∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) ↔ r < S.card := by
    intro r
    constructor
    · intro h
      have hsub : Finset.range (r + 1) ⊆ S := by
        intro r' hr'
        have hr'r : r' ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr')
        refine (hmem r').mpr ⟨A.valid_of_le hr'r h.1, ?_⟩
        rcases Nat.lt_or_eq_of_le hr'r with hlt | heq
        · exact Nat.lt_trans (A.pos_lt_pos j r' r h.1 hlt) h.2
        · exact heq ▸ h.2
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
    · intro hr
      by_contra hno
      have hsub : S ⊆ Finset.range r := by
        intro s hs
        rw [Finset.mem_range]
        by_contra hge
        have hs' := (hmem s).mp hs
        have hrs : r ≤ s := Nat.le_of_not_lt hge
        refine hno ⟨A.valid_of_le hrs hs'.1, ?_⟩
        rcases Nat.lt_or_eq_of_le hrs with hlt | heq
        · exact Nat.lt_trans (A.pos_lt_pos j r s hs'.1 hlt) hs'.2
        · exact heq ▸ hs'.2
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
  refine ⟨S.card, ?_, hchar, ?_⟩
  · have hdei : A.deinterleave j (2 ^ i - 1) = 2 ^ S.card - 1 := by
      apply Nat.eq_of_testBit_eq
      intro r
      rw [A.testBit_deinterleave, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
      by_cases hv : ∀ b, A.cap j = some b → r < b
      · rw [decide_eq_true hv, Bool.true_and]
        by_cases hp : A.pos j r < i
        · rw [decide_eq_true hp, decide_eq_true ((hchar r).mp ⟨hv, hp⟩)]
        · rw [decide_eq_false hp, eq_comm, decide_eq_false
            fun hrf => hp ((hchar r).mpr hrf).2]
      · rw [decide_eq_false hv, Bool.false_and, eq_comm, decide_eq_false
          fun hrf => hv ((hchar r).mpr hrf).1]
    rw [hdei]
    have : 1 ≤ 2 ^ S.card := Nat.one_le_two_pow
    omega
  · intro b hb
    by_contra hgt
    have := ((hchar b).mpr (Nat.lt_of_not_le hgt)).1 b hb
    omega

/-- A counter below `2 ^ i` deinterleaves below `2 ^ f` at slot `j` (its set
bits reach only the slot's sub-`i` ranks). -/
theorem deinterleave_lt_of_lt_two_pow (A : CappedBitAssignment m) {i lo : ℕ}
    (hlo : lo < 2 ^ i) {j : Fin m} {f : ℕ}
    (hf : ∀ r, ((∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) ↔ r < f) :
    A.deinterleave j lo < 2 ^ f := by
  apply lt_two_pow_of_testBit_eq_false
  intro r hr
  rw [A.testBit_deinterleave]
  by_cases hv : ∀ b, A.cap j = some b → r < b
  · rw [decide_eq_true hv, Bool.true_and]
    have hpos : ¬A.pos j r < i := fun hp => absurd ((hf r).mp ⟨hv, hp⟩) (by omega)
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlo
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hpos)))
  · simp [hv]

/-- **The split law**: on a counter that decomposes at boundary `i` as a
high `prefix` (no bits at or below `i`) plus a `low` part (below `2 ^ i`),
each slot's `deinterleave` decomposes as the sum of the parts' — the prefix
contributing only ranks at or above the slot's free-bit count `f`, the low
part only ranks below it. -/
theorem deinterleave_add_of_prefix (A : CappedBitAssignment m) {i hi lo : ℕ}
    (hhi : ∀ p, p ≤ i → hi.testBit p = false) (hlo : lo < 2 ^ i) {j : Fin m} {f : ℕ}
    (hf : ∀ r, ((∀ b, A.cap j = some b → r < b) ∧ A.pos j r < i) ↔ r < f) :
    A.deinterleave j (hi + lo) = A.deinterleave j hi + A.deinterleave j lo := by
  have hhimod : hi % 2 ^ (i + 1) = 0 := Nat.eq_of_testBit_eq fun p => by
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hp : p < i + 1
    · rw [hhi p (by omega)]
      simp
    · simp [hp]
  have hlo' : lo < 2 ^ (i + 1) :=
    lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsum := testBit_add_of_mod_eq_zero hhimod hlo'
  have hdlo : A.deinterleave j lo < 2 ^ f := deinterleave_lt_of_lt_two_pow A hlo hf
  have hdhimod : A.deinterleave j hi % 2 ^ f = 0 := Nat.eq_of_testBit_eq fun r => by
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hrf : r < f
    · obtain ⟨hv, hp⟩ := (hf r).mpr hrf
      rw [A.testBit_deinterleave, hhi (A.pos j r) (by omega)]
      simp
    · simp [hrf]
  apply Nat.eq_of_testBit_eq
  intro r
  rw [A.testBit_deinterleave, testBit_add_of_mod_eq_zero hdhimod hdlo r]
  by_cases hrf : r < f
  · obtain ⟨hv, hp⟩ := (hf r).mpr hrf
    rw [ite_eq_left hrf, A.testBit_deinterleave, hsum (A.pos j r), ite_eq_left (by omega)]
  · rw [ite_eq_right hrf, A.testBit_deinterleave]
    by_cases hv : ∀ b, A.cap j = some b → r < b
    · have hpos : ¬A.pos j r < i := fun hp => hrf ((hf r).mp ⟨hv, hp⟩)
      rw [hsum (A.pos j r)]
      by_cases hpi : A.pos j r < i + 1
      · have hpe : A.pos j r = i := by omega
        rw [ite_eq_left hpi, hpe, hhi i (le_refl i), Nat.testBit_lt_two_pow (hpe ▸ hlo)]
      · rw [ite_eq_right hpi]
    · simp [hv]

/-! ### The class card -/

/-- Agreement at all positions above `i` is the (decidable) equality of the
`(i + 1)`-shifts. -/
theorem shiftRight_eq_iff_agree {k n i : ℕ} :
    k >>> (i + 1) = n >>> (i + 1) ↔ ∀ p, i < p → k.testBit p = n.testBit p := by
  constructor
  · intro h p hp
    have := congrArg (fun x => x.testBit (p - (i + 1))) h
    simp only [Nat.testBit_shiftRight] at this
    rwa [show i + 1 + (p - (i + 1)) = p by omega] at this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    exact h (i + 1 + p) (by omega)

/-- **The class card is the slot-count product.** Fix a set bit `i` of `n'`
whose class prefix `(n' >>> (i+1)) <<< (i+1)` is a valid counter. The live
counters below `n'` that agree with `n'` above `i` and have bit `i` clear
biject with the tuples of per-slot free-bit completions — `k` maps to its
low part's deinterleave tuple, a tuple maps to `prefix + interleave` — so the
class has exactly `∏ j, slotCount j` elements. No ownership hypotheses: a
class member's low bits at unowned positions are forced to `0` on both sides
(`Valid` on the left, `interleave` only setting owned bits on the right). -/
theorem card_class (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) {n' i : ℕ}
    (hbit : n'.testBit i = true)
    (hval : (cappedRoundRobin cap).Valid ((n' >>> (i + 1)) <<< (i + 1))) :
    ((Finset.range n').filter fun k => Live cap cards k ∧ k.testBit i = false ∧
        k >>> (i + 1) = n' >>> (i + 1)).card
      = ∏ j, slotCount cap cards j i ((n' >>> (i + 1)) <<< (i + 1)) := by
  set A := cappedRoundRobin cap with hA
  set hi' := (n' >>> (i + 1)) <<< (i + 1) with hhi'def
  -- Prefix bit anatomy: clear at and below `i`, `n'`'s bits above.
  have hhibit : ∀ p, p ≤ i → hi'.testBit p = false := by
    intro p hp
    rw [hhi'def, Nat.testBit_shiftLeft]
    simp [Nat.not_le_of_lt (Nat.lt_succ_of_le hp)]
  have hhibit' : ∀ p, i < p → hi'.testBit p = n'.testBit p := by
    intro p hp
    rw [hhi'def, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      show i + 1 + (p - (i + 1)) = p by omega]
    simp [Nat.succ_le_of_lt hp]
  have hhimul : hi' = 2 ^ (i + 1) * (n' >>> (i + 1)) := by
    rw [hhi'def, Nat.shiftLeft_eq, Nat.mul_comm]
  have hhimod : hi' % 2 ^ (i + 1) = 0 := by
    rw [hhimul]
    exact Nat.mul_mod_right _ _
  -- Per-slot free-bit counts.
  choose f hF hfr hfb using fun j => exists_freeCount A j i
  -- The slot counts through `f`.
  have hslot : ∀ j, slotCount cap cards j i hi' = match cap j with
      | none => 2 ^ f j
      | some _ => min (2 ^ f j) (cards j - A.deinterleave j hi') := by
    intro j
    rcases hc : cap j with _ | b <;>
      simp only [slotCount, hc, deiFast_eq, ← hA, hF j]
  have hx2f : ∀ (x : Fin m → ℕ), (∀ j, x j < slotCount cap cards j i hi') →
      ∀ j, x j < 2 ^ f j := by
    intro x hx j
    have := hx j
    rw [hslot j] at this
    rcases hc : cap j with _ | b
    · rwa [hc] at this
    · rw [hc] at this
      exact lt_of_lt_of_le this (min_le_left _ _)
  -- The pi-set of per-slot completions.
  rw [show (∏ j, slotCount cap cards j i hi')
      = (Fintype.piFinset fun j => Finset.range (slotCount cap cards j i hi')).card by
    rw [Fintype.card_piFinset]
    exact (Finset.prod_congr rfl fun j _ => (Finset.card_range _).symm)]
  -- The bijection.
  refine Finset.card_bij' (fun k _ j => A.deinterleave j (k % 2 ^ (i + 1)))
    (fun x _ => hi' + A.interleave x) ?_ ?_ ?_ ?_
  · -- Forward membership: a class member's low tuple is a completion tuple.
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, hlive, hkbit, hkagree⟩ := hk
    -- Split `k` at the boundary.
    have hlo_lt : k % 2 ^ (i + 1) < 2 ^ i := by
      apply lt_two_pow_of_testBit_eq_false
      intro p hp
      rw [Nat.testBit_mod_two_pow]
      by_cases hpi : p < i + 1
      · rw [show p = i by omega, hkbit]
        simp
      · simp [hpi]
    have hksplit : k = hi' + k % 2 ^ (i + 1) := by
      conv_lhs => rw [← Nat.div_add_mod k (2 ^ (i + 1))]
      rw [hhimul, ← Nat.shiftRight_eq_div_pow, hkagree]
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, hslot j]
    have hdlo : A.deinterleave j (k % 2 ^ (i + 1)) < 2 ^ f j :=
      deinterleave_lt_of_lt_two_pow A hlo_lt (hfr j)
    rcases hc : cap j with _ | b
    · exact hdlo
    · refine Nat.lt_min.mpr ⟨hdlo, ?_⟩
      have hsplit := deinterleave_add_of_prefix A hhibit hlo_lt (hfr j)
      rw [← hksplit] at hsplit
      have hcapped := hlive.2 j b hc
      rw [← hA] at hcapped
      omega
  · -- Backward membership: a completion tuple's counter is a class member.
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    have hx' : ∀ j, x j < slotCount cap cards j i hi' := fun j =>
      Finset.mem_range.mp (hx j)
    have hxf := hx2f x hx'
    -- The interleaved low part sits below the boundary.
    have hlox : A.interleave x < 2 ^ i := by
      apply lt_two_pow_of_testBit_eq_false
      intro p hp
      cases hsl : A.slotOf p with
      | none => exact A.testBit_interleave_unowned x hsl
      | some j =>
        rw [A.testBit_interleave_owned x hsl]
        obtain ⟨hpos, hvalid⟩ := A.pos_rank p j hsl
        by_contra hbitp
        simp only [Bool.not_eq_false] at hbitp
        have hrank : A.rank p < f j := by
          have h2 : 2 ^ A.rank p ≤ x j := Nat.ge_two_pow_of_testBit hbitp
          have := hxf j
          by_contra hge
          exact absurd (lt_of_le_of_lt h2 this)
            (Nat.not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hge)))
        have hlt := ((hfr j) (A.rank p)).mpr hrank
        rw [hpos] at hlt
        omega
    have hlox' : A.interleave x < 2 ^ (i + 1) :=
      lt_of_lt_of_le hlox (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hsum := testBit_add_of_mod_eq_zero hhimod hlox'
    -- The per-slot cap bounds for the interleave round-trip.
    have hcapb : ∀ j b, A.cap j = some b → x j < 2 ^ b := by
      intro j b hb
      exact lt_of_lt_of_le (hxf j)
        (Nat.pow_le_pow_right (by norm_num) (hfb j b hb))
    have hdix : ∀ j, A.deinterleave j (A.interleave x) = x j :=
      A.deinterleave_interleave x hcapb
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · -- `hi' + interleave x < n'`, by the first-differing-bit criterion at `i`.
      refine Nat.lt_of_testBit i ?_ hbit ?_
      · rw [hsum i, ite_eq_left (by omega)]
        exact Nat.testBit_lt_two_pow hlox
      · intro p hp
        rw [hsum p, ite_eq_right (by omega), hhibit' p hp]
    · -- Valid: low bits are owned by `interleave_valid`, high bits by `hval`.
      intro p hbitp
      rw [hsum p] at hbitp
      by_cases hpi : p < i + 1
      · rw [ite_eq_left hpi] at hbitp
        exact A.interleave_valid x p hbitp
      · rw [ite_eq_right hpi] at hbitp
        exact hval p hbitp
    · -- Capped slots stay below their cards.
      intro j b hc
      rw [← hA, deinterleave_add_of_prefix A hhibit hlox (hfr j), hdix j]
      have := hx' j
      rw [hslot j, hc] at this
      have hDx := Nat.lt_min.mp this
      omega
    · -- Bit `i` is clear.
      rw [hsum i, ite_eq_left (by omega)]
      exact Nat.testBit_lt_two_pow hlox
    · -- Agreement above `i`.
      rw [shiftRight_eq_iff_agree]
      intro p hp
      rw [hsum p, ite_eq_right (by omega), hhibit' p hp]
  · -- Left inverse: `prefix + interleave (deinterleaveTuple low) = k`.
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, hlive, hkbit, hkagree⟩ := hk
    have hlo_lt : k % 2 ^ (i + 1) < 2 ^ i := by
      apply lt_two_pow_of_testBit_eq_false
      intro p hp
      rw [Nat.testBit_mod_two_pow]
      by_cases hpi : p < i + 1
      · rw [show p = i by omega, hkbit]
        simp
      · simp [hpi]
    have hksplit : k = hi' + k % 2 ^ (i + 1) := by
      conv_lhs => rw [← Nat.div_add_mod k (2 ^ (i + 1))]
      rw [hhimul, ← Nat.shiftRight_eq_div_pow, hkagree]
    have hlov : A.Valid (k % 2 ^ (i + 1)) := by
      intro p hbitp
      rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbitp
      exact hlive.1 p hbitp.2
    have hid := A.interleave_deinterleave (k % 2 ^ (i + 1)) hlov
    calc hi' + A.interleave (fun j => A.deinterleave j (k % 2 ^ (i + 1)))
        = hi' + A.interleave (A.deinterleaveTuple (k % 2 ^ (i + 1))) := rfl
      _ = hi' + k % 2 ^ (i + 1) := by rw [hid]
      _ = k := hksplit.symm
  · -- Right inverse: the low part of `prefix + interleave x` is `x`.
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    have hxf := hx2f x fun j => Finset.mem_range.mp (hx j)
    have hlox : A.interleave x < 2 ^ i := by
      apply lt_two_pow_of_testBit_eq_false
      intro p hp
      cases hsl : A.slotOf p with
      | none => exact A.testBit_interleave_unowned x hsl
      | some j =>
        rw [A.testBit_interleave_owned x hsl]
        obtain ⟨hpos, hvalid⟩ := A.pos_rank p j hsl
        by_contra hbitp
        simp only [Bool.not_eq_false] at hbitp
        have hrank : A.rank p < f j := by
          have h2 : 2 ^ A.rank p ≤ x j := Nat.ge_two_pow_of_testBit hbitp
          have := hxf j
          by_contra hge
          exact absurd (lt_of_le_of_lt h2 this)
            (Nat.not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hge)))
        have hlt := ((hfr j) (A.rank p)).mpr hrank
        rw [hpos] at hlt
        omega
    have hmod : (hi' + A.interleave x) % 2 ^ (i + 1) = A.interleave x := by
      rw [hhimul, Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hlox
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hcapb : ∀ j b, A.cap j = some b → x j < 2 ^ b := fun j b hb =>
      lt_of_lt_of_le (hxf j) (Nat.pow_le_pow_right (by norm_num) (hfb j b hb))
    funext j
    rw [hmod]
    exact A.deinterleave_interleave x hcapb j

/-! ### The counting correctness -/

/-- The class sum counts the live counters below `n'`, provided every set
bit's class prefix is a valid counter: partition `[0, n')` by the highest
differing bit (`lt_iff_exists_diff_bit`, disjointness by `diff_bit_unique`)
and apply `card_class` per class. -/
theorem sum_classes_eq_card (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) {n' : ℕ}
    (hval : ∀ i, n'.testBit i = true →
      (cappedRoundRobin cap).Valid ((n' >>> (i + 1)) <<< (i + 1))) :
    (∑ i ∈ Finset.range n'.size,
      if n'.testBit i then ∏ j, slotCount cap cards j i ((n' >>> (i + 1)) <<< (i + 1))
      else 0)
      = ((Finset.range n').filter fun k => Live cap cards k).card := by
  rw [← Finset.sum_filter]
  have hpart : (Finset.range n').filter (fun k => Live cap cards k)
      = ((Finset.range n'.size).filter fun i => n'.testBit i).biUnion
          fun i => (Finset.range n').filter fun k => Live cap cards k ∧
            k.testBit i = false ∧ k >>> (i + 1) = n' >>> (i + 1) := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hkn, hlive⟩
      obtain ⟨i, hni, hki, hagree⟩ := lt_iff_exists_diff_bit.mp hkn
      exact ⟨i, ⟨Nat.lt_size.mpr (Nat.ge_two_pow_of_testBit hni), hni⟩,
        hkn, hlive, hki, shiftRight_eq_iff_agree.mpr hagree⟩
    · rintro ⟨i, -, hkn, hlive, -, -⟩
      exact ⟨hkn, hlive⟩
  have hdisj : (↑((Finset.range n'.size).filter fun i => n'.testBit i) :
      Set ℕ).PairwiseDisjoint
      (fun i => (Finset.range n').filter fun k => Live cap cards k ∧
        k.testBit i = false ∧ k >>> (i + 1) = n' >>> (i + 1)) := by
    intro i hi i' hi' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_filter] at hk hk'
    have hi_bit := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
    have hi'_bit := (Finset.mem_filter.mp (Finset.mem_coe.mp hi')).2
    exact hne (diff_bit_unique ⟨hk.2.2.1, shiftRight_eq_iff_agree.mp hk.2.2.2⟩
      ⟨hk'.2.2.1, shiftRight_eq_iff_agree.mp hk'.2.2.2⟩ hi_bit hi'_bit)
  rw [hpart, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hbit := (Finset.mem_filter.mp hi).2
  exact (card_class cap cards hbit (hval i hbit)).symm

/-- **`countBelow` counts the live counters** — the SPEC equality against the
linear `Finset` filter count. -/
theorem countBelow_eq_card (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) (n : ℕ) :
    countBelow cap cards n = ((Finset.range n).filter fun k => Live cap cards k).card := by
  rcases htb : totalBits cap with _ | B
  · -- An uncapped slot: every position is owned, every prefix valid.
    rw [countBelow]
    simp only [htb]
    refine sum_classes_eq_card cap cards fun i _ => ?_
    intro p _
    rw [owned_iff_totalBits cap p, htb]
    exact under_none p
  · -- All capped: clip `n` to the `2 ^ B` budget, past which nothing is valid.
    have hclip : (Finset.range n).filter (fun k => Live cap cards k)
        = (Finset.range (min n (2 ^ B))).filter (fun k => Live cap cards k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
      constructor
      · rintro ⟨hkn, hlive⟩
        exact ⟨⟨hkn, valid_lt_two_pow_of_totalBits htb hlive.1⟩, hlive⟩
      · rintro ⟨⟨hkn, -⟩, hlive⟩
        exact ⟨hkn, hlive⟩
    rw [countBelow]
    simp only [htb]
    rw [hclip]
    refine sum_classes_eq_card cap cards fun i hbit => ?_
    intro p hbitp
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
      Nat.testBit_shiftRight, show i + 1 + (p - (i + 1)) = p from by omega] at hbitp
    obtain ⟨hip, hNp⟩ := hbitp
    have h2p : 2 ^ p ≤ min n (2 ^ B) := Nat.ge_two_pow_of_testBit hNp
    rw [owned_iff_totalBits cap p, htb]
    rw [under_some_iff]
    have hpB : p ≤ B := by
      by_contra hgt
      have h1 : 2 ^ (B + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ p ≤ 2 ^ B := le_trans h2p (min_le_right _ _)
      have h3 : (1 : ℕ) ≤ 2 ^ B := Nat.one_le_two_pow
      have h4 : 2 ^ (B + 1) = 2 * 2 ^ B := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rcases Nat.lt_or_eq_of_le hpB with h | h
    · exact h
    · -- `p = B` would force `min n (2 ^ B) = 2 ^ B`, whose only set bit is `B` — but
      -- bit `i < p = B` of it is set too.
      subst h
      have hNe : min n (2 ^ p) = 2 ^ p := le_antisymm (min_le_right _ _) h2p
      rw [hNe, Nat.testBit_two_pow_of_ne (show p ≠ i by omega)] at hbit
      exact absurd hbit (by simp)

open ExhaustiveGenerator

/-! ### The generator-rank bridge -/

/-- `countBelow` computes `rankSpec` for ANY generator whose liveness
predicate is `Live cap cards` — the digit DP replaces the linear scan. -/
theorem countBelow_eq_rankSpec {T : Type*} (g : ExhaustiveGenerator T)
    {cap : Fin m → Option ℕ} {cards : Fin m → ℕ}
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) (n : ℕ) :
    countBelow cap cards n = rankSpec g n := by
  rw [countBelow_eq_card, rankSpec]
  congr 1
  apply Finset.filter_congr
  intro k _
  simp [hbr k]

/-! ### Monotone binary search -/

/-- Binary search for the least witness of a (least-witness-closed) predicate
in `[lo, hi]`: halve toward the side containing the boundary. -/
def binSearch (P : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : hi ≤ lo then lo
  else if P ((lo + hi) / 2) then binSearch P lo ((lo + hi) / 2)
  else binSearch P ((lo + hi) / 2 + 1) hi
termination_by hi - lo
decreasing_by all_goals omega

/-- `binSearch` finds THE least witness: on a monotone predicate with
`P hi = true`, the result satisfies `P`, everything before it (from `lo`)
does not, and it stays in `[lo, hi]`. -/
theorem binSearch_spec {P : ℕ → Bool} (hmono : ∀ x y, x ≤ y → P x = true → P y = true)
    {lo hi : ℕ} (hlh : lo ≤ hi) (hhi : P hi = true) :
    P (binSearch P lo hi) = true
      ∧ (∀ x, lo ≤ x → x < binSearch P lo hi → P x = false)
      ∧ lo ≤ binSearch P lo hi ∧ binSearch P lo hi ≤ hi := by
  suffices h : ∀ d lo hi, hi - lo ≤ d → lo ≤ hi → P hi = true →
      P (binSearch P lo hi) = true
        ∧ (∀ x, lo ≤ x → x < binSearch P lo hi → P x = false)
        ∧ lo ≤ binSearch P lo hi ∧ binSearch P lo hi ≤ hi from
    h (hi - lo) lo hi (le_refl _) hlh hhi
  intro d
  induction d with
  | zero =>
    intro lo hi hd hlh hhi
    have heq : hi = lo := by omega
    subst heq
    rw [binSearch, dite_eq_left (le_refl _)]
    exact ⟨hhi, fun x hx hx' => absurd hx' (by omega), le_refl _, le_refl _⟩
  | succ d ih =>
    intro lo hi hd hlh hhi
    rw [binSearch]
    split
    · next h =>
      have heq : lo = hi := by omega
      subst heq
      exact ⟨hhi, fun x hx hx' => absurd hx' (by omega), le_refl _, le_refl _⟩
    · next h =>
      have hlt : lo < hi := by omega
      split
      · next hm =>
        obtain ⟨h1, h2, h3, h4⟩ := ih lo ((lo + hi) / 2) (by omega) (by omega) hm
        exact ⟨h1, h2, h3, by omega⟩
      · next hm =>
        obtain ⟨h1, h2, h3, h4⟩ := ih ((lo + hi) / 2 + 1) hi (by omega) (by omega) hhi
        refine ⟨h1, ?_, by omega, h4⟩
        intro x hx hx'
        by_cases hxm : (lo + hi) / 2 + 1 ≤ x
        · exact h2 x hxm hx'
        · -- `x ≤ mid`: monotonicity would push a witness up to `mid`.
          rcases hPx : P x with _ | _
          · rfl
          · exact absurd (hmono x ((lo + hi) / 2) (by omega) hPx) hm

/-! ### Fast unrank -/

/-- **Fast unrank**: the `i`-th live counter of a capped-product generator,
WITHOUT the linear scan — the least `k` with `i < countBelow (k + 1)`, found
by binary search under a doubling upper bound (`Nat.find` on
`i < countBelow (2 ^ t)`; the existence witness is the SLOW `unrank`, erased
at runtime). Same hypothesis interface as `unrank` plus the liveness bridge
`hbr`; `fastUnrank_eq_unrank` proves it IS `unrank`. -/
def fastUnrank (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) {T : Type*}
    (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) (i : ℕ) : ℕ :=
  if hi : Under N i then
    have hex : ∃ t, i < countBelow cap cards (2 ^ t) := by
      refine ⟨(unrank g N h i + 1).size, ?_⟩
      rw [countBelow_eq_rankSpec g hbr]
      have h1 : rankSpec g (unrank g N h i + 1) = i + 1 := by
        rw [rankSpec_succ_of_isSome (gen_unrank_isSome hi), rankSpec_unrank hi]
      have h2 : rankSpec g (unrank g N h i + 1)
          ≤ rankSpec g (2 ^ (unrank g N h i + 1).size) :=
        rankSpec_le_rankSpec g (Nat.le_of_lt (Nat.lt_size_self _))
      omega
    binSearch (fun k => decide (i < countBelow cap cards (k + 1))) 0 (2 ^ Nat.find hex)
  else 0

/-- **`fastUnrank` is `unrank`** — the core case, on indices under the live
count: both are the unique least `k` whose successor-rank exceeds `i`
(order-iso uniqueness via `rankSpec_unrank`/`rankSpec_succ_of_isSome`). -/
theorem fastUnrank_eq_unrank_of_under {T : Type*} {g : ExhaustiveGenerator T} {N : Option ℕ}
    {h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome}
    {cap : Fin m → Option ℕ} {cards : Fin m → ℕ}
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) {i : ℕ} (hi : Under N i) :
    fastUnrank cap cards g N h hbr i = unrank g N h i := by
  rw [fastUnrank, dite_eq_left hi]
  have hlive : (g.gen (unrank g N h i)).isSome := gen_unrank_isSome hi
  have hrank : rankSpec g (unrank g N h i) = i := rankSpec_unrank hi
  have hcb : ∀ x, countBelow cap cards x = rankSpec g x :=
    countBelow_eq_rankSpec g hbr
  set P := fun k => decide (i < countBelow cap cards (k + 1)) with hP
  have hmono : ∀ x y, x ≤ y → P x = true → P y = true := by
    intro x y hxy hx
    rw [hP, decide_eq_true_eq] at hx ⊢
    have := rankSpec_le_rankSpec g (show x + 1 ≤ y + 1 by omega)
    rw [hcb] at hx ⊢
    omega
  have hPu : P (unrank g N h i) = true := by
    rw [hP, decide_eq_true_eq, hcb, rankSpec_succ_of_isSome hlive, hrank]
    omega
  have hPbelow : ∀ x, x < unrank g N h i → P x = false := by
    intro x hx
    rw [hP, decide_eq_false_iff_not, Nat.not_lt, hcb]
    have := rankSpec_le_rankSpec g (show x + 1 ≤ unrank g N h i by omega)
    omega
  -- The doubling bound satisfies `P`.
  have hex : ∃ t, i < countBelow cap cards (2 ^ t) := by
    refine ⟨(unrank g N h i + 1).size, ?_⟩
    rw [countBelow_eq_rankSpec g hbr]
    have h1 : rankSpec g (unrank g N h i + 1) = i + 1 := by
      rw [rankSpec_succ_of_isSome hlive, hrank]
    have h2 : rankSpec g (unrank g N h i + 1)
        ≤ rankSpec g (2 ^ (unrank g N h i + 1).size) :=
      rankSpec_le_rankSpec g (Nat.le_of_lt (Nat.lt_size_self _))
    omega
  have hPhi : P (2 ^ Nat.find hex) = true := by
    have hspec := Nat.find_spec hex
    rw [hP, decide_eq_true_eq]
    have := rankSpec_le_rankSpec g (show 2 ^ Nat.find hex ≤ 2 ^ Nat.find hex + 1 by omega)
    rw [hcb] at hspec ⊢
    omega
  obtain ⟨h1, h2, -, -⟩ := binSearch_spec hmono (Nat.zero_le _) hPhi
  -- Two least witnesses coincide.
  rcases Nat.lt_trichotomy (binSearch P 0 (2 ^ Nat.find hex)) (unrank g N h i)
    with hlt | heq | hgt
  · rw [hPbelow _ hlt] at h1
    exact absurd h1 (by simp)
  · exact heq
  · rw [h2 (unrank g N h i) (Nat.zero_le _) hgt] at hPu
    exact absurd hPu (by simp)

/-- **`fastUnrank` is `unrank`, unconditionally**: past the live count both
return the junk value `0`. -/
theorem fastUnrank_eq_unrank {T : Type*} {g : ExhaustiveGenerator T} {N : Option ℕ}
    {h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome}
    {cap : Fin m → Option ℕ} {cards : Fin m → ℕ}
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) (i : ℕ) :
    fastUnrank cap cards g N h hbr i = unrank g N h i := by
  by_cases hi : Under N i
  · exact fastUnrank_eq_unrank_of_under hbr hi
  · rw [fastUnrank, dite_eq_right hi, unrank, dite_eq_right hi]

/-! ### The re-pointed compression -/

/-- **`compress` through the fast path**: gen-pointwise IDENTICAL to
`compress g N h h'` (`compressFast_gen_eq_compress`), with `unrank`'s linear
scan replaced by `fastUnrank`'s digit DP. The extra hypothesis `hbr` is the
liveness bridge of the capped-product builders
(`fairPairGenCapped_gen_isSome_iff` and friends, proved next to the raw
builders in `FairCapped.lean`) — the public capped instances there are all
built on this. -/
@[reducible] def compressFast (cap : Fin m → Option ℕ) (cards : Fin m → ℕ) {T : Type*}
    (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k))
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) : ExhaustiveGenerator T where
  gen i := if Under N i then g.gen (fastUnrank cap cards g N h hbr i) else none
  occurs_exactly_once t := by
    have hgen : ∀ i, (if Under N i then g.gen (fastUnrank cap cards g N h hbr i) else none)
        = (compress g N h h').gen i := by
      intro i
      show _ = (if Under N i then g.gen (unrank g N h i) else none)
      rw [fastUnrank_eq_unrank hbr i]
    obtain ⟨n, hn, hun⟩ := (compress g N h h').occurs_exactly_once t
    refine ⟨n, ?_, ?_⟩
    · show (if Under N n then g.gen (fastUnrank cap cards g N h hbr n) else none) = some t
      rw [hgen n]
      exact hn
    · intro j hj
      refine hun j ?_
      show (compress g N h h').gen j = some t
      rw [← hgen j]
      exact hj

/-- The fast compression is gen-pointwise the spec compression — the
zero-observable-change re-pointing lemma. -/
theorem compressFast_gen_eq_compress {T : Type*} (cap : Fin m → Option ℕ)
    (cards : Fin m → ℕ) (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k))
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) (i : ℕ) :
    (compressFast cap cards g N h h' hbr).gen i = (compress g N h h').gen i := by
  show (if Under N i then g.gen (fastUnrank cap cards g N h hbr i) else none)
    = (if Under N i then g.gen (unrank g N h i) else none)
  rw [fastUnrank_eq_unrank hbr i]

/-- The fast compression is contiguous — `compress_contiguous` transported
along the gen-pointwise equality, so the `Contiguous` companions of the
capped instances re-point together with the generators. -/
theorem compressFast_contiguous {T : Type*} (cap : Fin m → Option ℕ)
    (cards : Fin m → ℕ) (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k))
    (hbr : ∀ k, (g.gen k).isSome ↔ Live cap cards k) :
    @Contiguous T (compressFast cap cards g N h h' hbr) :=
  @Contiguous.mk T (compressFast cap cards g N h h' hbr) fun n hnone => by
    rw [compressFast_gen_eq_compress] at hnone ⊢
    exact @Contiguous.contig T (compress g N h h') (compress_contiguous g N h h') n hnone

/-! ### Guards

Small cross-checks of `countBelow` against the brute-force filter count. The
generator-level guards — `countBelow` = `rankSpec` on the raw capped
builders, `fastUnrank` = spec `unrank`, and the `10^12 + 39`-card scale
demonstration — live with the builders and bridges in `FairCapped.lean`. -/

-- `Ordering × Ordering`-shaped caps (all-capped, cards `3 × 3` on `2 + 2`
-- bits, 9 live among 16 valid counters): `countBelow` = brute-force filter
-- count.
#guard (List.range 64).all fun n =>
  countBelow ![some 2, some 2] ![3, 3] n
    == ((List.range n).filter fun k => decide (Live ![some 2, some 2] ![3, 3] k)).length

-- `Ordering × AzNat`-shaped caps (mixed): same sweep on the mixed regime.
#guard (List.range 64).all fun n =>
  countBelow ![some 2, none] ![3, 0] n
    == ((List.range n).filter fun k => decide (Live ![some 2, none] ![3, 0] k)).length

end CompressFast

/-! ### `FiniteGenerator` data for a fast-compressed generator -/

open ExhaustiveGenerator in
/-- `FiniteGenerator` data for `compressFast … (some n) …`: the fast-path
counterpart of `FiniteGenerator.ofCompress`, with the gen bounds transported
along `compressFast_gen_eq_compress`. -/
@[reducible] def FiniteGenerator.ofCompressFast {m : ℕ} (cap : Fin m → Option ℕ)
    (cards : Fin m → ℕ) {T : Type*} (g : ExhaustiveGenerator T) (n : ℕ)
    (h : ∀ i, Under (some n) (rankSpec g i) → ∃ k, i ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under (some n) (rankSpec g k))
    (hbr : ∀ k, (g.gen k).isSome ↔ CompressFast.Live cap cards k) :
    @FiniteGenerator T (CompressFast.compressFast cap cards g (some n) h h' hbr) :=
  @FiniteGenerator.mk T (CompressFast.compressFast cap cards g (some n) h h' hbr) n
    (fun i hi => by
      rw [CompressFast.compressFast_gen_eq_compress]
      exact compress_gen_none g (some n) h h'
        fun hu => absurd (under_some_iff.mp hu) (by omega))
    (fun i hi => by
      rw [CompressFast.compressFast_gen_eq_compress]
      exact Option.isSome_iff_ne_none.mp
        (compress_gen_isSome g (some n) h h' (under_some_iff.mpr hi)))

end Azurite
