/-
  `BitInterleaveWeightedCapped` — the WEIGHTED + CAPPED `CappedBitAssignment`
  (Malachite `BitDistributorOutputType::normal(w)` with `max_bits`): the last
  flagged extension of the `BitDistributor` port, combining
  `BitInterleaveWeighted`'s weight blocks with `BitInterleaveCapped`'s
  drop-out rotation.

  Rust semantics (`update_bit_map` in `bit_distributor.rs`): the scan keeps a
  per-slot `weight_counter` that counts down one per emitted position, moving
  to the next active slot (decreasing cyclic order, slot `m - 1` first) when
  it hits `0`; a slot's `bits_used` counter is checked against `max_bits`
  AFTER every position, and when the cap is hit MID-BLOCK the slot is removed
  immediately (`weight_counter` forced to `0`), cutting its block short.

  ROUNDS aggregation: a slot still active at the start of sweep `t` has
  received full blocks so far, so its bits used before round `t` is
  `min (t * w j) (cap j)` (uncapped: `t * w j`) — proved as the telescoping
  closed form `sum_range_contrib`. Hence
  * slot `j` is ACTIVE in round `t` iff `t * w j < cap j`
    (`ActiveIn w cap t j`, vacuous when uncapped), and
  * an active slot contributes `contrib j t = min (w j) (cap j − t * w j)`
    CONSECUTIVE positions to round `t` (`ℕ`-truncation makes this `0` exactly
    when inactive; uncapped slots contribute `w j`),
  with the active slots emitted in decreasing index order. The maps are all
  closed `Finset` counts over that round structure:
  * `roundSize t = ∑ j, contrib j t`, `roundStart t = ∑ t' < t, roundSize t'`
    with the performance form
    `roundStart t = ∑ j, (cap j).elim (t * w j) (min (t * w j))`
    (`roundStart_eq_sum`, the mixed-cap generalization of `CompressFast`'s
    weight-1 form);
  * `offsetIn t j = ∑ j' > j, contrib j' t` (reusing `weightBlockStart` at
    the per-round weights `contrib · t`);
  * `pos j r = roundStart (r / w j) + offsetIn (r / w j) j + r % w j` — for a
    VALID rank `r < cap j` the containing round is still `r / w j`: blocks
    before saturation have full width `w j`, and the last partial block is
    still consecutive in round `t = r / w j` because
    `contrib j t = min (w j) (cap j − t * w j) > r − t * w j ⟺ r < cap j`;
  * `rank`/`slotOf` by interval location within the round (`roundOf` counts
    the finished rounds; `slotOf` is a `List.find?` over the slots).

  Hand simulation of the Rust `set_max_bits` doctest (`[normal(2); 3]`, caps
  `5` on slots `{0, 2}`, i.e. `w = ![2, 2, 2]`, `cap = ![some 5, none, some 5]`
  — a 3-slot mixed example; per round, contributions in emission order
  `slot 2, slot 1, slot 0`):

    round 0: used 0 0 0, contribs 2 2 2 → emits 2 2 1 1 0 0   (positions 0–5)
    round 1: used 2 2 2, contribs 2 2 2 → emits 2 2 1 1 0 0   (positions 6–11)
    round 2: used 4 4 4, contribs min(2,5−4)=1, 2, 1
                                        → emits 2 1 1 0       (positions 12–15)
    round 3+: slots 0 and 2 exhausted (used 5 = cap)
                                        → emits 1 1 per round (positions 16–…)

  giving the doctest bit map `[2,2,1,1,0,0,2,2,1,1,0,0,2,1,1,0,1,1,…]` —
  round 2 shows both caps cutting blocks short mid-round (guarded below).

  Mid-block cut, minimal (`w = ![3, 1]`, `cap = ![some 4, none]`): slot 0 has
  weight 3 but cap 4, so it gets a block of 3 and then a block of 1:

    round 0: contribs 1, min(3,4)=3   → emits 1 0 0 0   (positions 0–3)
    round 1: contribs 1, min(3,4−3)=1 → emits 1 0       (positions 4–5)
    round 2+: slot 0 exhausted        → emits 1         (positions 6, 7, …)

  Degenerations: all weights `1` recovers `cappedRoundRobin cap` pointwise
  (`weightedCappedRoundRobin_one_slotOf`/`_one_pos`), and no caps recovers
  `weightedRoundRobin w` via `some ∘`
  (`weightedCappedRoundRobin_none_slotOf`/`_none_pos`). Deinterleave /
  interleave / round-trips / validity machinery all come free from
  `CappedBitAssignment`. NOTE: `FairCapped`'s builders
  (`fairPairCappedAssignment` etc.) currently hardcode `cappedRoundRobin`;
  threading an arbitrary `CappedBitAssignment` (to use this one in fair
  products) is a follow-up factoring, not done here.
-/
import Azurite.ExhaustiveGenerator.BitInterleaveCapped
import Azurite.ExhaustiveGenerator.BitInterleaveWeighted

namespace Azurite

namespace WeightedCappedRoundRobin

variable {m : ℕ}

/-! ### Activity and per-round contributions -/

/-- Slot `j` is still **active** in round `t`: the `t * w j` bits it used in
the earlier (full-block) rounds lie below its cap. This is the validity guard
for rank `t * w j` at slot `j`; with all weights `1` it is
`CappedRoundRobin.ActiveIn`. -/
def ActiveIn (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : Prop :=
  ∀ b, cap j = some b → t * w j < b

instance (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    Decidable (ActiveIn w cap t j) :=
  decidableCapGuard (cap j) (t * w j)

/-- Activity is antitone in the round: active later means active earlier. -/
theorem ActiveIn.mono {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t t' : ℕ} (h : t ≤ t')
    {j : Fin m} (ha : ActiveIn w cap t' j) : ActiveIn w cap t j :=
  fun b hb => Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (w j) h) (ha b hb)

/-- The number of consecutive positions slot `j` receives in round `t`:
`min (w j) (cap j − t * w j)` when capped (a cap can cut the block short —
`ℕ`-truncation makes this `0` once the slot is exhausted), `w j` when
uncapped. -/
def contrib (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : ℕ :=
  min (w j) ((cap j).elim (w j) fun b => b - t * w j)

theorem contrib_none {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (h : cap j = none) : contrib w cap t j = w j := by
  rw [contrib, h, Option.elim_none, Nat.min_self]

theorem contrib_some {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m} {b : ℕ}
    (h : cap j = some b) : contrib w cap t j = min (w j) (b - t * w j) := by
  rw [contrib, h, Option.elim_some]

/-- An active slot's block is nonempty (for positive weights). -/
theorem contrib_pos {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (hwj : 0 < w j) (h : ActiveIn w cap t j) : 0 < contrib w cap t j := by
  rcases hc : cap j with _ | b
  · rw [contrib_none hc]; exact hwj
  · rw [contrib_some hc]
    have := h b hc
    omega

/-- An exhausted slot contributes nothing. -/
theorem contrib_eq_zero {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t : ℕ} {j : Fin m}
    (h : ¬ActiveIn w cap t j) : contrib w cap t j = 0 := by
  rcases hc : cap j with _ | b
  · exact absurd (fun b hb => nomatch hc.symm.trans hb) h
  · rw [contrib_some hc]
    have hnb : ¬t * w j < b :=
      fun hlt => h fun b' hb' => Option.some.inj (hc.symm.trans hb') ▸ hlt
    omega

/-- Contributions shrink over time (blocks only get cut, never regrow). -/
theorem contrib_antitone (w : Fin m → ℕ) (cap : Fin m → Option ℕ) {t t' : ℕ} (h : t ≤ t')
    (j : Fin m) : contrib w cap t' j ≤ contrib w cap t j := by
  rcases hc : cap j with _ | b
  · rw [contrib_none hc, contrib_none hc]
  · rw [contrib_some hc, contrib_some hc]
    have := Nat.mul_le_mul_right (w j) h
    omega

theorem contrib_le_weight (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    contrib w cap t j ≤ w j :=
  Nat.min_le_left _ _

/-! ### Round sizes and round starts -/

/-- The number of positions round `t` emits. -/
def roundSize (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) : ℕ :=
  ∑ j, contrib w cap t j

/-- The first position of round `t`: the total size of the earlier rounds. -/
def roundStart (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) : ℕ :=
  ∑ t' ∈ Finset.range t, roundSize w cap t'

theorem roundStart_succ (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) :
    roundStart w cap (t + 1) = roundStart w cap t + roundSize w cap t :=
  Finset.sum_range_succ _ t

theorem roundStart_le_roundStart (w : Fin m → ℕ) (cap : Fin m → Option ℕ) {t t' : ℕ}
    (h : t ≤ t') : roundStart w cap t ≤ roundStart w cap t' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem roundSize_antitone (w : Fin m → ℕ) (cap : Fin m → Option ℕ) {t t' : ℕ}
    (h : t ≤ t') : roundSize w cap t' ≤ roundSize w cap t :=
  Finset.sum_le_sum fun j _ => contrib_antitone w cap h j

/-- **The bits-used closed form.** The contributions of slot `j` to the first
`t` rounds telescope to `min (t * w j) (cap j)` (uncapped: `t * w j`) — the
per-slot used-count of the Rust scan at the start of sweep `t`. -/
theorem sum_range_contrib (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    ∑ t' ∈ Finset.range t, contrib w cap t' j
      = (cap j).elim (t * w j) (min (t * w j)) := by
  induction t with
  | zero => rcases hc : cap j with _ | b <;> simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases hc : cap j with _ | b
    · rw [Option.elim_none, Option.elim_none, contrib_none hc, Nat.succ_mul]
    · rw [Option.elim_some, Option.elim_some, contrib_some hc]
      have hmul : (n + 1) * w j = n * w j + w j := Nat.succ_mul n (w j)
      omega

/-- **The `roundStart` closed form** (the performance form, mirroring
`CompressFast.roundStart_eq_sum`): round `t` starts at the total bits used by
all slots, `∑ j, min (t * w j) (cap j)` with uncapped slots contributing
`t * w j`. -/
theorem roundStart_eq_sum (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) :
    roundStart w cap t = ∑ j, (cap j).elim (t * w j) (min (t * w j)) := by
  unfold roundStart roundSize
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => sum_range_contrib w cap t j

/-! ### In-round offsets -/

/-- Slot `j`'s offset within round `t`: rounds emit active slots' blocks in
DECREASING order, so `j`'s block comes after the blocks of the slots above it
— `∑ j' > j, contrib j' t` (`offsetIn_eq_sum_Ioi`). Definitionally the
`weightBlockStart` of the per-round weights `contrib · t`, which makes
`BitInterleaveWeighted`'s block-decomposition machinery reusable. -/
def offsetIn (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) : ℕ :=
  weightBlockStart (contrib w cap t) j

theorem offsetIn_eq_sum_Ioi (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    offsetIn w cap t j = ∑ j' ∈ Finset.Ioi j, contrib w cap t j' :=
  weightBlockStart_eq_sum_Ioi _ j

/-- A slot's block fits inside its round. -/
theorem offsetIn_add_contrib_le_roundSize (w : Fin m → ℕ) (cap : Fin m → Option ℕ)
    (t : ℕ) (j : Fin m) :
    offsetIn w cap t j + contrib w cap t j ≤ roundSize w cap t :=
  weightBlockStart_add_weight_le (contrib w cap t) j

/-- Blocks of distinct slots are disjoint: the whole block of a HIGHER slot
`j'` sits below the offset of a lower slot `j`. -/
theorem contrib_add_offsetIn_le (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (t : ℕ)
    {j j' : Fin m} (h : j < j') :
    contrib w cap t j' + offsetIn w cap t j' ≤ offsetIn w cap t j := by
  rw [offsetIn_eq_sum_Ioi, offsetIn_eq_sum_Ioi,
    ← Finset.sum_insert (fun hmem => absurd (Finset.mem_Ioi.mp hmem) (lt_irrefl j'))]
  refine Finset.sum_le_sum_of_subset fun x hx => ?_
  rw [Finset.mem_insert] at hx
  rw [Finset.mem_Ioi]
  rcases hx with rfl | hx
  · exact h
  · exact lt_trans h (Finset.mem_Ioi.mp hx)

/-! ### The four maps -/

/-- The `r`-th position of slot `j`. For a VALID rank (`r < cap j`) the
containing round is still `r / w j` — full-width blocks before saturation,
and the final partial block is consecutive in its round — at in-block offset
`r % w j`. -/
def posFun (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (j : Fin m) (r : ℕ) : ℕ :=
  roundStart w cap (r / w j) + offsetIn w cap (r / w j) j + r % w j

/-- The round containing position `i` (junk past the last round): the number
of rounds that finish at or before `i`. -/
def roundOf (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (i : ℕ) : ℕ :=
  ((Finset.range (i + 1)).filter fun t => roundStart w cap (t + 1) ≤ i).card

/-- The rank position `i` would have inside slot `j`: full blocks in the
earlier rounds plus the in-block offset (junk when `i` is not owned by
`j`). -/
def rankInSlot (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (i : ℕ) (j : Fin m) : ℕ :=
  roundOf w cap i * w j
    + (i - (roundStart w cap (roundOf w cap i) + offsetIn w cap (roundOf w cap i) j))

/-- The slot owning position `i`: the slot whose candidate rank is valid and
lands back on `i`, if any. -/
def slotOfFun (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (i : ℕ) : Option (Fin m) :=
  (List.finRange m).find? fun j =>
    decide (∀ b, cap j = some b → rankInSlot w cap i j < b)
      && (posFun w cap j (rankInSlot w cap i j) == i)

/-- The rank of position `i` within its owning slot (junk when unowned). -/
def rankFun (w : Fin m → ℕ) (cap : Fin m → Option ℕ) (i : ℕ) : ℕ :=
  (slotOfFun w cap i).elim 0 (rankInSlot w cap i)

/-! ### Round location of a valid position -/

/-- Validity of rank `r` at slot `j` makes the slot active in round
`r / w j`: `(r / w j) * w j ≤ r < cap j`. -/
theorem activeIn_div_of_valid {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {j : Fin m} {r : ℕ}
    (h : ∀ b, cap j = some b → r < b) : ActiveIn w cap (r / w j) j :=
  fun b hb => Nat.lt_of_le_of_lt (Nat.div_mul_le_self r (w j)) (h b hb)

/-- **The partial-block analysis.** At a valid rank, the in-block offset
`r % w j` lies inside round `r / w j`'s (possibly cut-short) block:
`contrib j t = min (w j) (cap j − t * w j) > r − t * w j ⟺ r < cap j`. -/
theorem mod_lt_contrib {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {j : Fin m} {r : ℕ}
    (hwj : 0 < w j) (h : ∀ b, cap j = some b → r < b) :
    r % w j < contrib w cap (r / w j) j := by
  rcases hc : cap j with _ | b
  · rw [contrib_none hc]
    exact Nat.mod_lt r hwj
  · rw [contrib_some hc]
    have hb := h b hc
    have hd := Nat.div_add_mod' r (w j)
    have hm := Nat.mod_lt r hwj
    omega

/-- A valid position of a slot lies before the end of its round. -/
theorem posFun_lt_roundStart_succ {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {j : Fin m}
    {r : ℕ} (hwj : 0 < w j) (h : ∀ b, cap j = some b → r < b) :
    posFun w cap j r < roundStart w cap (r / w j + 1) := by
  have h1 := mod_lt_contrib hwj h
  have h2 := offsetIn_add_contrib_le_roundSize w cap (r / w j) j
  rw [roundStart_succ]
  unfold posFun
  omega

/-- A round with positive size keeps all earlier rounds nonempty
(`roundSize` is antitone), so it starts at position `t` or later. -/
theorem le_roundStart_of_pos {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t : ℕ}
    (h : 0 < roundSize w cap t) : t ≤ roundStart w cap t := by
  calc t = ∑ _t' ∈ Finset.range t, 1 := by simp
    _ ≤ roundStart w cap t := Finset.sum_le_sum fun t' ht' =>
        Nat.lt_of_lt_of_le h
          (roundSize_antitone w cap (Nat.le_of_lt (Finset.mem_range.mp ht')))

/-- `roundOf` recovers the round: a position between `roundStart t` and
`roundStart (t + 1)` has round `t`. -/
theorem roundOf_eq {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {t i : ℕ}
    (h1 : roundStart w cap t ≤ i) (h2 : i < roundStart w cap (t + 1)) :
    roundOf w cap i = t := by
  have hsize : 0 < roundSize w cap t := by
    rw [roundStart_succ] at h2
    omega
  have hts : t ≤ roundStart w cap t := le_roundStart_of_pos hsize
  have hset : (Finset.range (i + 1)).filter (fun t' => roundStart w cap (t' + 1) ≤ i)
      = Finset.range t := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hle⟩
      by_contra hge
      have := Nat.le_trans (roundStart_le_roundStart w cap (by omega : t + 1 ≤ t' + 1)) hle
      omega
    · intro hlt
      exact ⟨by omega,
        Nat.le_trans (roundStart_le_roundStart w cap (by omega : t' + 1 ≤ t)) h1⟩
  rw [roundOf, hset, Finset.card_range]

/-- The round of a valid position is `r / w j`. -/
theorem roundOf_posFun {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {j : Fin m} {r : ℕ}
    (hwj : 0 < w j) (h : ∀ b, cap j = some b → r < b) :
    roundOf w cap (posFun w cap j r) = r / w j := by
  refine roundOf_eq ?_ (posFun_lt_roundStart_succ hwj h)
  unfold posFun
  omega

/-- `rankInSlot` inverts `posFun` at valid ranks. -/
theorem rankInSlot_posFun {w : Fin m → ℕ} {cap : Fin m → Option ℕ} {j : Fin m} {r : ℕ}
    (hwj : 0 < w j) (h : ∀ b, cap j = some b → r < b) :
    rankInSlot w cap (posFun w cap j r) j = r := by
  unfold rankInSlot
  rw [roundOf_posFun hwj h]
  have hd := Nat.div_add_mod' r (w j)
  unfold posFun
  omega

/-- **Injectivity on valid pairs**: positions determine their slot and rank —
the common round is `roundOf`, and within a round the blocks are disjoint. -/
theorem posFun_inj {w : Fin m → ℕ} {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j)
    {j j' : Fin m} {r r' : ℕ} (h : ∀ b, cap j = some b → r < b)
    (h' : ∀ b, cap j' = some b → r' < b)
    (heq : posFun w cap j r = posFun w cap j' r') : j = j' ∧ r = r' := by
  have e1 := roundOf_posFun (hw j) h
  have e2 := roundOf_posFun (hw j') h'
  rw [heq] at e1
  have ht : r / w j = r' / w j' := e1.symm.trans e2
  have hoff : offsetIn w cap (r / w j) j + r % w j
      = offsetIn w cap (r / w j) j' + r' % w j' := by
    have heq' := heq
    unfold posFun at heq'
    rw [← ht] at heq'
    omega
  have hmj := mod_lt_contrib (hw j) h
  have hmj' := mod_lt_contrib (hw j') h'
  rw [← ht] at hmj'
  have hj : j = j' := by
    rcases lt_trichotomy j j' with hlt | hEq | hgt
    · have hb := contrib_add_offsetIn_le w cap (r / w j) hlt
      omega
    · exact hEq
    · have hb := contrib_add_offsetIn_le w cap (r / w j) hgt
      omega
  subst hj
  refine ⟨rfl, ?_⟩
  have hAB : r / w j * w j = r' / w j * w j := by rw [ht]
  have d1 := Nat.div_add_mod' r (w j)
  have d2 := Nat.div_add_mod' r' (w j)
  omega

/-- `slotOfFun` finds exactly the owning slot of a valid position. -/
theorem slotOfFun_posFun {w : Fin m → ℕ} {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j)
    (j : Fin m) (r : ℕ) (h : ∀ b, cap j = some b → r < b) :
    slotOfFun w cap (posFun w cap j r) = some j := by
  have hrank : rankInSlot w cap (posFun w cap j r) j = r := rankInSlot_posFun (hw j) h
  have hjpred : (decide (∀ b, cap j = some b → rankInSlot w cap (posFun w cap j r) j < b)
      && (posFun w cap j (rankInSlot w cap (posFun w cap j r) j) == posFun w cap j r))
        = true := by
    rw [hrank]
    simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
    exact h
  unfold slotOfFun
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (xs := List.finRange m) (p := fun j' =>
        decide (∀ b, cap j' = some b → rankInSlot w cap (posFun w cap j r) j' < b)
          && (posFun w cap j' (rankInSlot w cap (posFun w cap j r) j')
            == posFun w cap j r))).mpr
      ⟨j, List.mem_finRange j, hjpred⟩)
  have hj'pred := List.find?_some hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hj'pred
  obtain ⟨hjj, -⟩ := posFun_inj hw hj'pred.1 h hj'pred.2
  rw [hj', hjj]

end WeightedCappedRoundRobin

open WeightedCappedRoundRobin in
/-- **Malachite's weighted drop-out rotation** (`update_bit_map` with weights
`w j` and optional `max_bits` caps): rounds emit each still-active slot's
block of `min (w j) (cap j − t * w j)` consecutive positions in decreasing
slot order; a slot leaves the rotation the moment its cap is used up, cutting
its final block short. With all weights `1` this is `cappedRoundRobin capBits`
(`weightedCappedRoundRobin_one_slotOf`); with no caps it is
`weightedRoundRobin w` (`weightedCappedRoundRobin_none_slotOf`). -/
def weightedCappedRoundRobin (w : Fin m → ℕ) (capBits : Fin m → Option ℕ)
    (hw : ∀ j, 0 < w j) : CappedBitAssignment m where
  cap := capBits
  slotOf := slotOfFun w capBits
  rank := rankFun w capBits
  pos := posFun w capBits
  pos_slotOf := fun j r h => slotOfFun_posFun hw j r h
  rank_pos := fun j r h => by
    show (slotOfFun w capBits (posFun w capBits j r)).elim 0
      (rankInSlot w capBits (posFun w capBits j r)) = r
    rw [slotOfFun_posFun hw j r h]
    exact rankInSlot_posFun (hw j) h
  pos_rank := fun i j h => by
    have hrank : rankFun w capBits i = rankInSlot w capBits i j := by
      show (slotOfFun w capBits i).elim 0 (rankInSlot w capBits i)
        = rankInSlot w capBits i j
      rw [h, Option.elim_some]
    unfold slotOfFun at h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    rw [hrank]
    exact ⟨hp.2, hp.1⟩
  pos_lt_pos := fun j r r' h' hlt => by
    have h : ∀ b, capBits j = some b → r < b := fun b hb => Nat.lt_trans hlt (h' b hb)
    show posFun w capBits j r < posFun w capBits j r'
    have hq : r / w j ≤ r' / w j := Nat.div_le_div_right (Nat.le_of_lt hlt)
    rcases Nat.lt_or_ge (r / w j) (r' / w j) with hqlt | hqge
    · calc posFun w capBits j r
          < roundStart w capBits (r / w j + 1) := posFun_lt_roundStart_succ (hw j) h
        _ ≤ roundStart w capBits (r' / w j) := roundStart_le_roundStart w capBits hqlt
        _ ≤ posFun w capBits j r' := by unfold posFun; omega
    · have hqeq : r / w j = r' / w j := Nat.le_antisymm hq hqge
      have hAB : r / w j * w j = r' / w j * w j := by rw [hqeq]
      have d1 := Nat.div_add_mod' r (w j)
      have d2 := Nat.div_add_mod' r' (w j)
      unfold posFun
      rw [hqeq]
      omega

namespace WeightedCappedRoundRobin

variable {m : ℕ}

/-- Every position within a round is some slot's position at a valid rank:
decompose the in-round offset into blocks with
`exists_weightBlock_decomp` at the per-round weights `contrib w cap t`. -/
theorem exists_posFun_eq {w : Fin m → ℕ} {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j)
    {t i : ℕ} (h1 : roundStart w cap t ≤ i) (h2 : i < roundStart w cap (t + 1)) :
    ∃ (j : Fin m) (r : ℕ), (∀ b, cap j = some b → r < b) ∧ posFun w cap j r = i := by
  have hd : i - roundStart w cap t < ∑ j, contrib w cap t j := by
    rw [roundStart_succ] at h2
    have : roundSize w cap t = ∑ j, contrib w cap t j := rfl
    omega
  have hm : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hd
    omega
  obtain ⟨j, s, hs, hts, -⟩ := exists_weightBlock_decomp (contrib w cap t) hm hd
  have hsw : s < w j := Nat.lt_of_lt_of_le hs (contrib_le_weight w cap t j)
  have hdiv : (t * w j + s) / w j = t := by
    rw [Nat.mul_comm, Nat.mul_add_div (hw j), Nat.div_eq_of_lt hsw, Nat.add_zero]
  have hmod : (t * w j + s) % w j = s := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hsw]
  refine ⟨j, t * w j + s, ?_, ?_⟩
  · intro b hb
    rw [contrib_some hb] at hs
    omega
  · unfold posFun
    rw [hdiv, hmod]
    have hoff : offsetIn w cap t j = weightBlockStart (contrib w cap t) j := rfl
    omega

/-- Positions within a round are owned. -/
theorem owned_of_round {w : Fin m → ℕ} {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j)
    {t i : ℕ} (h1 : roundStart w cap t ≤ i) (h2 : i < roundStart w cap (t + 1)) :
    (weightedCappedRoundRobin w cap hw).Owned i := by
  obtain ⟨j, r, hvalid, hpos⟩ := exists_posFun_eq hw h1 h2
  have hslot : (weightedCappedRoundRobin w cap hw).slotOf i = some j := by
    rw [← hpos]
    exact (weightedCappedRoundRobin w cap hw).pos_slotOf j r hvalid
  show ((weightedCappedRoundRobin w cap hw).slotOf i).isSome = true
  rw [hslot]
  rfl

/-- Positions below some `roundStart` are owned: locate the containing round
with `Nat.find`. -/
theorem owned_of_exists_lt_roundStart {w : Fin m → ℕ} {cap : Fin m → Option ℕ}
    (hw : ∀ j, 0 < w j) {i : ℕ} (h : ∃ t, i < roundStart w cap t) :
    (weightedCappedRoundRobin w cap hw).Owned i := by
  have hspec := Nat.find_spec h
  have hne : Nat.find h ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp [roundStart] at hspec
  obtain ⟨t, ht⟩ : ∃ t, Nat.find h = t + 1 := ⟨Nat.find h - 1, by omega⟩
  have h1 : ¬i < roundStart w cap t := Nat.find_min h (by omega)
  rw [ht] at hspec
  exact owned_of_round hw (Nat.le_of_not_lt h1) hspec

end WeightedCappedRoundRobin

/-! ### Ownership characterizations -/

/-- **An uncapped slot keeps every round alive**, so every position is
owned. -/
theorem weightedCappedRoundRobin_owned_of_none {m : ℕ} {w : Fin m → ℕ}
    {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j) {j₀ : Fin m} (h : cap j₀ = none)
    (i : ℕ) : (weightedCappedRoundRobin w cap hw).Owned i := by
  apply WeightedCappedRoundRobin.owned_of_exists_lt_roundStart hw
  refine ⟨i + 1, ?_⟩
  have hsize : ∀ t, 1 ≤ WeightedCappedRoundRobin.roundSize w cap t := by
    intro t
    calc 1 ≤ w j₀ := hw j₀
      _ = WeightedCappedRoundRobin.contrib w cap t j₀ :=
          (WeightedCappedRoundRobin.contrib_none h).symm
      _ ≤ WeightedCappedRoundRobin.roundSize w cap t :=
          Finset.single_le_sum (fun j' _ => Nat.zero_le _) (Finset.mem_univ j₀)
  calc i < i + 1 := Nat.lt_succ_self i
    _ = ∑ _t ∈ Finset.range (i + 1), 1 := by simp
    _ ≤ WeightedCappedRoundRobin.roundStart w cap (i + 1) :=
        Finset.sum_le_sum fun t _ => hsize t

/-- With an uncapped slot present, every counter is valid. -/
theorem weightedCappedRoundRobin_valid_of_none {m : ℕ} {w : Fin m → ℕ}
    {cap : Fin m → Option ℕ} (hw : ∀ j, 0 < w j) {j₀ : Fin m} (h : cap j₀ = none)
    (k : ℕ) : (weightedCappedRoundRobin w cap hw).Valid k :=
  fun i _ => weightedCappedRoundRobin_owned_of_none hw h i

/-- **All-capped ownership**: with every slot capped by `b`, exactly the
first `∑ j, b j` positions are owned — regardless of the weights. -/
theorem weightedCappedRoundRobin_owned_iff {m : ℕ} (w : Fin m → ℕ) (b : Fin m → ℕ)
    (hw : ∀ j, 0 < w j) (i : ℕ) :
    (weightedCappedRoundRobin w (fun j => some (b j)) hw).Owned i ↔ i < ∑ j, b j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hpos, hvalid⟩ :=
      (weightedCappedRoundRobin w (fun j' => some (b j')) hw).pos_rank i j hj
    have hlt : (weightedCappedRoundRobin w (fun j' => some (b j')) hw).pos j
          ((weightedCappedRoundRobin w (fun j' => some (b j')) hw).rank i)
        < WeightedCappedRoundRobin.roundStart w (fun j' => some (b j'))
          ((weightedCappedRoundRobin w (fun j' => some (b j')) hw).rank i / w j + 1) :=
      WeightedCappedRoundRobin.posFun_lt_roundStart_succ (hw j) hvalid
    rw [hpos] at hlt
    refine Nat.lt_of_lt_of_le hlt ?_
    rw [WeightedCappedRoundRobin.roundStart_eq_sum]
    refine Finset.sum_le_sum fun j' _ => ?_
    simp only [Option.elim_some]
    exact Nat.min_le_right _ _
  · intro h
    apply WeightedCappedRoundRobin.owned_of_exists_lt_roundStart hw
    refine ⟨∑ j, b j, ?_⟩
    rw [WeightedCappedRoundRobin.roundStart_eq_sum]
    refine Nat.lt_of_lt_of_le h (Finset.sum_le_sum fun j _ => ?_)
    simp only [Option.elim_some]
    exact Nat.le_min.mpr ⟨Nat.le_trans (Finset.single_le_sum
        (fun j' _ => Nat.zero_le (b j')) (Finset.mem_univ j))
      (Nat.le_mul_of_pos_right _ (hw j)), Nat.le_refl _⟩

/-- **All-capped validity**: with every slot capped by `b`, the valid
counters are exactly `k < 2 ^ ∑ j, b j`. -/
theorem weightedCappedRoundRobin_valid_iff {m : ℕ} (w : Fin m → ℕ) (b : Fin m → ℕ)
    (hw : ∀ j, 0 < w j) (k : ℕ) :
    (weightedCappedRoundRobin w (fun j => some (b j)) hw).Valid k ↔ k < 2 ^ ∑ j, b j := by
  constructor
  · intro h
    apply lt_two_pow_of_testBit_eq_false
    intro i hi
    by_contra hbit
    simp only [Bool.not_eq_false] at hbit
    have := (weightedCappedRoundRobin_owned_iff w b hw i).mp (h i hbit)
    omega
  · intro h i hbit
    rw [weightedCappedRoundRobin_owned_iff]
    have h2 : 2 ^ i ≤ k := Nat.ge_two_pow_of_testBit hbit
    by_contra hge
    have : (2 : ℕ) ^ ∑ j, b j ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-! ### Degeneration to `cappedRoundRobin` (all weights `1`) -/

namespace WeightedCappedRoundRobin

variable {m : ℕ}

theorem contrib_one (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    contrib (fun _ => 1) cap t j
      = if CappedRoundRobin.ActiveIn cap t j then 1 else 0 := by
  rcases hc : cap j with _ | b
  · rw [contrib_none hc,
      if_pos (show CappedRoundRobin.ActiveIn cap t j from fun b hb => nomatch hc.symm.trans hb)]
  · rw [contrib_some hc]
    show min 1 (b - t * 1) = _
    split_ifs with h
    · have := h b hc; omega
    · have hnb : ¬ t < b := fun hlt => h fun b' hb' => Option.some.inj (hc.symm.trans hb') ▸ hlt
      omega

theorem roundSize_one (cap : Fin m → Option ℕ) (t : ℕ) :
    roundSize (fun _ => 1) cap t = CappedRoundRobin.roundSize cap t := by
  unfold roundSize CappedRoundRobin.roundSize
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun j _ => contrib_one cap t j

theorem roundStart_one (cap : Fin m → Option ℕ) (t : ℕ) :
    roundStart (fun _ => 1) cap t = CappedRoundRobin.roundStart cap t :=
  Finset.sum_congr rfl fun t' _ => roundSize_one cap t'

theorem offsetIn_one (cap : Fin m → Option ℕ) (t : ℕ) (j : Fin m) :
    offsetIn (fun _ => 1) cap t j = CappedRoundRobin.offsetIn cap t j := by
  rw [offsetIn_eq_sum_Ioi, CappedRoundRobin.offsetIn]
  have hset : Finset.univ.filter (fun j' => CappedRoundRobin.ActiveIn cap t j' ∧ j < j')
      = (Finset.Ioi j).filter (CappedRoundRobin.ActiveIn cap t) := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  rw [hset, Finset.card_filter]
  exact Finset.sum_congr rfl fun j' _ => contrib_one cap t j'

theorem posFun_one (cap : Fin m → Option ℕ) (j : Fin m) (r : ℕ) :
    posFun (fun _ => 1) cap j r = CappedRoundRobin.posFun cap j r := by
  show roundStart (fun _ => 1) cap (r / 1) + offsetIn (fun _ => 1) cap (r / 1) j + r % 1
      = CappedRoundRobin.roundStart cap r + CappedRoundRobin.offsetIn cap r j
  rw [Nat.div_one, Nat.mod_one, Nat.add_zero, roundStart_one, offsetIn_one]

end WeightedCappedRoundRobin

/-- With all weights `1`, `weightedCappedRoundRobin` has `cappedRoundRobin`'s
`pos`. -/
theorem weightedCappedRoundRobin_one_pos {m : ℕ} (cap : Fin m → Option ℕ) (j : Fin m)
    (r : ℕ) :
    (weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).pos j r
      = (cappedRoundRobin cap).pos j r :=
  WeightedCappedRoundRobin.posFun_one cap j r

/-- **All-weights-`1` degeneration**: `weightedCappedRoundRobin (fun _ => 1) cap`
agrees with `cappedRoundRobin cap` pointwise on `slotOf`. -/
theorem weightedCappedRoundRobin_one_slotOf {m : ℕ} (cap : Fin m → Option ℕ) (i : ℕ) :
    (weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).slotOf i
      = (cappedRoundRobin cap).slotOf i := by
  cases h : (cappedRoundRobin cap).slotOf i with
  | some j =>
    obtain ⟨hpos, hvalid⟩ := (cappedRoundRobin cap).pos_rank i j h
    have hpos' : WeightedCappedRoundRobin.posFun (fun _ => 1) cap j
        ((cappedRoundRobin cap).rank i) = i := by
      rw [WeightedCappedRoundRobin.posFun_one]
      exact hpos
    rw [← hpos']
    exact (weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).pos_slotOf j
      ((cappedRoundRobin cap).rank i) hvalid
  | none =>
    cases hwc : (weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).slotOf i with
    | none => rfl
    | some j =>
      obtain ⟨hpos, hvalid⟩ :=
        (weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).pos_rank i j hwc
      have hpos' : (cappedRoundRobin cap).pos j
          ((weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).rank i) = i := by
        rw [← weightedCappedRoundRobin_one_pos]
        exact hpos
      have hslot := (cappedRoundRobin cap).pos_slotOf j
        ((weightedCappedRoundRobin (fun _ => 1) cap fun _ => Nat.one_pos).rank i) hvalid
      rw [hpos', h] at hslot
      exact absurd hslot (by simp)

/-! ### Degeneration to `weightedRoundRobin` (no caps) -/

namespace WeightedCappedRoundRobin

variable {m : ℕ}

theorem contrib_noneCap (w : Fin m → ℕ) (t : ℕ) (j : Fin m) :
    contrib w (fun _ => none) t j = w j :=
  contrib_none rfl

theorem roundStart_noneCap (w : Fin m → ℕ) (t : ℕ) :
    roundStart w (fun _ => none) t = t * ∑ j, w j := by
  unfold roundStart roundSize
  rw [Finset.sum_congr rfl fun t' _ =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => contrib_noneCap w t' j]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem offsetIn_noneCap (w : Fin m → ℕ) (t : ℕ) (j : Fin m) :
    offsetIn w (fun _ => none) t j = weightBlockStart w j := by
  rw [offsetIn]
  congr 1
  funext j'
  exact contrib_noneCap w t j'

theorem posFun_noneCap (w : Fin m → ℕ) (j : Fin m) (r : ℕ) :
    posFun w (fun _ => none) j r = weightedPos w j r := by
  unfold posFun weightedPos
  rw [roundStart_noneCap, offsetIn_noneCap]

end WeightedCappedRoundRobin

/-- With no caps, `weightedCappedRoundRobin` has `weightedRoundRobin`'s
`pos`. -/
theorem weightedCappedRoundRobin_none_pos {m : ℕ} (w : Fin m → ℕ) (hm : 0 < m)
    (hw : ∀ j, 0 < w j) (j : Fin m) (r : ℕ) :
    (weightedCappedRoundRobin w (fun _ => none) hw).pos j r
      = (weightedRoundRobin w hm hw).pos j r :=
  WeightedCappedRoundRobin.posFun_noneCap w j r

/-- **No-caps degeneration**: `weightedCappedRoundRobin w (fun _ => none)` is
`weightedRoundRobin w` with a totalized `slotOf` (`some ∘`). -/
theorem weightedCappedRoundRobin_none_slotOf {m : ℕ} (w : Fin m → ℕ) (hm : 0 < m)
    (hw : ∀ j, 0 < w j) (i : ℕ) :
    (weightedCappedRoundRobin w (fun _ => none) hw).slotOf i
      = some ((weightedRoundRobin w hm hw).slotOf i) := by
  have hpos : (weightedCappedRoundRobin w (fun _ => none) hw).pos
      ((weightedRoundRobin w hm hw).slotOf i) ((weightedRoundRobin w hm hw).rank i) = i := by
    rw [weightedCappedRoundRobin_none_pos w hm hw]
    exact (weightedRoundRobin w hm hw).pos_rank i
  have hslot := (weightedCappedRoundRobin w (fun _ => none) hw).pos_slotOf
    ((weightedRoundRobin w hm hw).slotOf i) ((weightedRoundRobin w hm hw).rank i)
    fun b hb => nomatch hb
  rw [hpos] at hslot
  exact hslot

/-! ### Guards (pin `update_bit_map`'s weighted drop-out rotation)

The Rust `set_max_bits` doctest is EXACTLY this configuration:
`[normal(2); 3]` with caps `5` on slots `{0, 2}` — bit map
`[2,2,1,1,0,0,2,2,1,1,0,0,2,1,1,0,1,1,1,…]` (slot 2 emits its last position
at 12 and slot 0 at 15, both blocks cut short mid-round; from position 16 on
everything belongs to the uncapped slot 1). -/

#guard (let A := weightedCappedRoundRobin ![2, 2, 2] ![some 5, none, some 5] (by decide);
  (List.range 20).map A.slotOf)
  = [some 2, some 2, some 1, some 1, some 0, some 0,
     some 2, some 2, some 1, some 1, some 0, some 0,
     some 2, some 1, some 1, some 0,
     some 1, some 1, some 1, some 1]

-- Mid-block cut, minimal: slot 0 has weight 3 but cap 4 — a block of 3
-- (round 0), then a block of 1 (round 1, cut short), then nothing:
--   positions:  0  1  2  3  4  5  6  7
--   slots:      1  0  0  0  1  0  1  1
#guard (let A := weightedCappedRoundRobin ![3, 1] ![some 4, none] (by decide);
  (List.range 8).map A.slotOf)
  = [some 1, some 0, some 0, some 0, some 1, some 0, some 1, some 1]

-- All slots capped (`w = ![2, 2]`, caps 3): round 0 emits `1 1 0 0`, round 1
-- cuts both blocks to width 1 (`1 0`), then every position is unowned;
-- `Owned i ↔ i < 6` and `Valid k ↔ k < 2^6`.
#guard (let A := weightedCappedRoundRobin ![2, 2] ![some 3, some 3] (by decide);
  (List.range 8).map A.slotOf)
  = [some 1, some 1, some 0, some 0, some 1, some 0, none, none]
#guard (let A := weightedCappedRoundRobin ![2, 2] ![some 3, some 3] (by decide);
  (List.range 10).map (fun i => decide (A.Owned i)))
  = [true, true, true, true, true, true, false, false, false, false]
#guard (let A := weightedCappedRoundRobin ![2, 2] ![some 3, some 3] (by decide);
  (List.range 80).all fun k => decide (A.Valid k) == decide (k < 64))

-- All-weights-1 degeneration vs `cappedRoundRobin` on a mixed-cap config.
#guard (let A := weightedCappedRoundRobin ![1, 1, 1] ![some 1, none, some 2] (by decide);
  let B := cappedRoundRobin ![some 1, none, some 2];
  (List.range 12).map A.slotOf == (List.range 12).map B.slotOf)

-- No-caps degeneration vs `weightedRoundRobin` (via `some ∘`).
#guard (let A := weightedCappedRoundRobin ![2, 1] (fun _ => none) (by decide);
  let B := weightedRoundRobin ![2, 1] (by omega) (by decide);
  (List.range 12).map A.slotOf == (List.range 12).map (fun i => some (B.slotOf i)))

-- Round-trips on a 2-slot weighted+capped config (slot 0: weight 2, cap 3;
-- slot 1: weight 3, uncapped — every `k` is valid, and `f 0 = 5 < 2^3`
-- respects slot 0's cap).
#guard (let A := weightedCappedRoundRobin ![2, 3] ![some 3, none] (by decide);
  (A.deinterleave 0 (A.interleave ![5, 20]), A.deinterleave 1 (A.interleave ![5, 20])))
  == (5, 20)
#guard (let A := weightedCappedRoundRobin ![2, 3] ![some 3, none] (by decide);
  (List.range 64).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
-- All-capped round-trip on the full valid range.
#guard (let A := weightedCappedRoundRobin ![2, 2] ![some 3, some 3] (by decide);
  (List.range 64).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
-- The unconditional capped-output bound, at arbitrary (even invalid) `k`.
#guard (let A := weightedCappedRoundRobin ![2, 3] ![some 3, none] (by decide);
  (List.range 200).all fun k => A.deinterleave 0 k < 8)

end Azurite
