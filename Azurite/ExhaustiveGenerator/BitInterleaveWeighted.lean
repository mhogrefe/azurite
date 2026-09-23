/-
  `BitInterleaveWeighted` — the WEIGHTED round-robin `BitAssignment`
  (Malachite `BitDistributorOutputType::normal(w)` with per-slot weights).

  `weightedRoundRobin w hm hw` assigns the counter-bit positions to the `m`
  slots periodically with period `W = ∑ j, w j`: within each period the slots
  take CONSECUTIVE blocks of their weight in DECREASING slot order (slot
  `m - 1` first, owning the least-significant bits — Malachite's
  `update_bit_map`). The `[normal(2); 3]` bit-map doctest is the oracle:

    `[2, 2, 1, 1, 0, 0, 2, 2, 1, 1, 0, 0, …]`

  Closed forms (`t = i % W`, `b = weightBlockIdx w t` the reversed block
  index, `weightBlockStart w j = ∑ j' > j, w j'` the offset of slot `j`'s
  block within a period):
  - `slotOf i = m - 1 - b` — the unique `j` with
    `weightBlockStart w j ≤ t < weightBlockStart w j + w j`;
  - `rank i = (i / W) * w j + (t - weightBlockStart w j)`;
  - `pos j r = (r / w j) * W + weightBlockStart w j + (r % w j)`.
  The four `BitAssignment` laws are `Finset`-sum/div/mod arithmetic, so the
  `ℕ ≃ (Fin m → ℕ)` bijection is inherited FREE from `BitInterleave`. With all
  weights `1` this degenerates pointwise to `roundRobin`
  (`weightedRoundRobin_one_slotOf`/`_rank`/`_pos`).

  Weight intuition: giving slot `j` weight `w j` makes its deinterleaved
  component grow like `k ^ (w j / W)` in the counter `k`.

  NOT built here (flagged extensions of the port):
  - TINY output types (`BitDistributorOutputType::tiny()`): tiny slots own the
    logarithmically-sparse ruler positions `i` with `i + 1` a power of two, and
    the normal slots' closed forms shift around them. NOW BUILT in
    `BitInterleaveTiny` (`tinyAssignment`) — the bijection was indeed free.
  - WEIGHTED + CAPPED combined (`normal(w)` with `max_bits`): a future
    `CappedBitAssignment` instance with weighted rounds, following the same
    pattern as `cappedRoundRobin` in `BitInterleaveCapped`.
-/
import Azurite.ExhaustiveGenerator.BitInterleave

namespace Azurite

variable {m : ℕ}

/-! ### Reversed weight prefix sums

Malachite hands the least-significant bits to the LAST slot, so the natural
prefix sums read the weights from slot `m - 1` DOWN: `revWeightSum w r` is the
total weight of the `r` lowest blocks (slots `m - 1, m - 2, …, m - r`). It is
`ℕ`-total (summands beyond `m` are `0`) so all the arithmetic below is
unconditional. -/

/-- The total weight of the `r` lowest blocks: `∑_{i < r} w (m - 1 - i)`
(slot `m - 1` first). Terms with `i ≥ m` are `0`, making the function total;
on `r ≤ m` it is the reversed prefix-sum of the weights. -/
def revWeightSum (w : Fin m → ℕ) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, if h : i < m then w ⟨m - 1 - i, by omega⟩ else 0

theorem revWeightSum_zero (w : Fin m → ℕ) : revWeightSum w 0 = 0 :=
  Finset.sum_range_zero _

theorem revWeightSum_succ (w : Fin m → ℕ) (r : ℕ) :
    revWeightSum w (r + 1)
      = revWeightSum w r + if h : r < m then w ⟨m - 1 - r, by omega⟩ else 0 :=
  Finset.sum_range_succ _ r

/-- `ℕ`-indexed step form: below `m`, extending the sum by one block adds the
weight of slot `m - 1 - b`. -/
theorem revWeightSum_succ_of_lt (w : Fin m → ℕ) {b : ℕ} (hb : b < m) :
    revWeightSum w (b + 1) = revWeightSum w b + w ⟨m - 1 - b, by omega⟩ := by
  rw [revWeightSum_succ, dite_eq_left hb]

theorem revWeightSum_mono (w : Fin m → ℕ) : Monotone (revWeightSum w) :=
  fun _ _ hab => Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hab)

/-- On `r ≤ m`, `revWeightSum w r` is the weight of the `r` TOPMOST-value
slots: the sum over the slots `j` with `m - r ≤ j`. (Reindex `i ↦ m - 1 - i`.) -/
theorem revWeightSum_eq_sum_filter (w : Fin m → ℕ) {r : ℕ} (hr : r ≤ m) :
    revWeightSum w r = ∑ j ∈ Finset.univ.filter (fun j : Fin m => m - r ≤ j.val), w j := by
  refine Finset.sum_bij'
    (fun a ha => ⟨m - 1 - a, by have := Finset.mem_range.mp ha; omega⟩)
    (fun b _ => m - 1 - b.val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show m - r ≤ m - 1 - a
    omega
  · intro b hb
    have hbv := b.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Finset.mem_range.mpr (by omega)
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    show m - 1 - (m - 1 - a) = a
    omega
  · intro b hb
    have hbv := b.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Fin.ext (show m - 1 - (m - 1 - b.val) = b.val by omega)
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [dite_eq_left (show a < m by omega)]

/-- The whole period: `revWeightSum w m = ∑ j, w j = W`. -/
theorem revWeightSum_total (w : Fin m → ℕ) : revWeightSum w m = ∑ j, w j := by
  rw [revWeightSum_eq_sum_filter w le_rfl]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_true_of_mem fun j _ => ?_
  omega

/-- The period `W = ∑ j, w j` is positive when there is a slot and all weights
are positive. -/
theorem weightSum_pos (hm : 0 < m) {w : Fin m → ℕ} (hw : ∀ j, 0 < w j) :
    0 < ∑ j, w j :=
  Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- A single weight is at most the period. -/
theorem weight_le_sum (w : Fin m → ℕ) (j : Fin m) : w j ≤ ∑ j', w j' :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) (Finset.mem_univ j)

/-! ### Block starts and block lookup -/

/-- The offset of slot `j`'s block within a period: the total weight of all
LOWER blocks, i.e. of the slots `j' > j` (`weightBlockStart_eq_sum_Ioi`).
Definitionally `revWeightSum w (m - 1 - j)`. -/
def weightBlockStart (w : Fin m → ℕ) (j : Fin m) : ℕ :=
  revWeightSum w (m - 1 - j.val)

/-- `weightBlockStart w j = ∑ j' > j, w j'` — the spec form. -/
theorem weightBlockStart_eq_sum_Ioi (w : Fin m → ℕ) (j : Fin m) :
    weightBlockStart w j = ∑ j' ∈ Finset.Ioi j, w j' := by
  have hj := j.isLt
  rw [weightBlockStart, revWeightSum_eq_sum_filter w (by omega)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j'
  have hj' := j'.isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi, Fin.lt_def]
  omega

/-- Extending slot `j`'s block: `revWeightSum` one step past `m - 1 - j` adds
exactly `w j`. -/
theorem revWeightSum_reflect_succ (w : Fin m → ℕ) (j : Fin m) :
    revWeightSum w (m - 1 - j.val + 1) = weightBlockStart w j + w j := by
  have hj := j.isLt
  rw [revWeightSum_succ, dite_eq_left (show m - 1 - j.val < m by omega)]
  congr 1
  exact congrArg w (Fin.ext (show m - 1 - (m - 1 - j.val) = j.val by omega))

/-- Slot `j`'s block fits in the period: `weightBlockStart w j + w j ≤ W`. -/
theorem weightBlockStart_add_weight_le (w : Fin m → ℕ) (j : Fin m) :
    weightBlockStart w j + w j ≤ ∑ j', w j' := by
  have hj := j.isLt
  rw [← revWeightSum_reflect_succ, ← revWeightSum_total]
  exact revWeightSum_mono w (by omega)

/-- The REVERSED block index of an in-period offset `t`: the number of full
low blocks below `t`, computed as a `Finset` count. For `t` in slot `j`'s
block this is `m - 1 - j` (`weightBlockIdx_eq`); the count formulation makes
the function total and computable with the uniqueness proof built in. -/
def weightBlockIdx (w : Fin m → ℕ) (t : ℕ) : ℕ :=
  ((Finset.range m).filter fun r => revWeightSum w (r + 1) ≤ t).card

/-- **Uniqueness.** If `t` lies in the `r`-th reversed block
(`revWeightSum w r ≤ t < revWeightSum w (r + 1)` with `r < m`), then
`weightBlockIdx w t = r`. -/
theorem weightBlockIdx_eq (w : Fin m → ℕ) {t r : ℕ} (hr : r < m)
    (h1 : revWeightSum w r ≤ t) (h2 : t < revWeightSum w (r + 1)) :
    weightBlockIdx w t = r := by
  have hfil : (Finset.range m).filter (fun r' => revWeightSum w (r' + 1) ≤ t)
      = Finset.range r := by
    ext r'
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hle⟩
      by_contra hnot
      have := revWeightSum_mono w (show r + 1 ≤ r' + 1 by omega)
      omega
    · intro hlt
      have h3 : revWeightSum w (r' + 1) ≤ revWeightSum w r := revWeightSum_mono w (by omega)
      exact ⟨by omega, le_trans h3 h1⟩
  rw [weightBlockIdx, hfil, Finset.card_range]

/-- **Existence.** Every in-period offset `t < W` lies in SOME slot's block:
`t` decomposes as `weightBlockStart w j + s` with `s < w j`, and
`weightBlockIdx w t` is that block's reversed index `m - 1 - j`. -/
theorem exists_weightBlock_decomp (w : Fin m → ℕ) (hm : 0 < m)
    {t : ℕ} (ht : t < ∑ j, w j) :
    ∃ (j : Fin m) (s : ℕ), s < w j ∧ t = weightBlockStart w j + s
      ∧ weightBlockIdx w t = m - 1 - j.val := by
  have ht' : t < revWeightSum w m := by rwa [revWeightSum_total]
  have hex : ∃ r, t < revWeightSum w (r + 1) :=
    ⟨m - 1, by rwa [Nat.sub_add_cancel hm]⟩
  -- Locate the block: least `b` whose block ends past `t`.
  obtain ⟨b, hbm, hlow, hspec⟩ :
      ∃ b, b < m ∧ revWeightSum w b ≤ t ∧ t < revWeightSum w (b + 1) := by
    refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
    · have : Nat.find hex ≤ m - 1 :=
        Nat.find_min' hex (by rwa [Nat.sub_add_cancel hm])
      omega
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0, revWeightSum_zero]; exact Nat.zero_le t
      · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
        omega
  have hltb : m - 1 - b < m := by omega
  have hsucc : revWeightSum w (b + 1) = revWeightSum w b + w ⟨m - 1 - b, hltb⟩ :=
    revWeightSum_succ_of_lt w hbm
  have hbs : weightBlockStart w ⟨m - 1 - b, hltb⟩ = revWeightSum w b :=
    congrArg (revWeightSum w) (show m - 1 - (m - 1 - b) = b by omega)
  refine ⟨⟨m - 1 - b, hltb⟩, t - revWeightSum w b, by omega, by rw [hbs]; omega, ?_⟩
  show weightBlockIdx w t = m - 1 - (m - 1 - b)
  rw [weightBlockIdx_eq w hbm hlow hspec]
  omega

/-- Offsets inside slot `j`'s block have reversed block index `m - 1 - j`. -/
theorem weightBlockIdx_blockStart_add (w : Fin m → ℕ) (j : Fin m) {s : ℕ}
    (hs : s < w j) : weightBlockIdx w (weightBlockStart w j + s) = m - 1 - j.val := by
  have hj := j.isLt
  refine weightBlockIdx_eq w (show m - 1 - j.val < m by omega)
    (Nat.le_add_right _ _) ?_
  rw [revWeightSum_reflect_succ]
  omega

/-! ### The three maps and their laws -/

/-- Weighted `slotOf`: reflect the reversed block index of `i % W`. -/
def weightedSlotOf (w : Fin m → ℕ) (hm : 0 < m) (i : ℕ) : Fin m :=
  ⟨m - 1 - weightBlockIdx w (i % ∑ j, w j), by omega⟩

/-- Weighted `rank`: `w j` bits per period plus the offset inside the current
block, `(i / W) * w j + (i % W − weightBlockStart w j)`. -/
def weightedRank (w : Fin m → ℕ) (hm : 0 < m) (i : ℕ) : ℕ :=
  i / (∑ j, w j) * w (weightedSlotOf w hm i)
    + (i % (∑ j, w j) - revWeightSum w (weightBlockIdx w (i % ∑ j, w j)))

/-- Weighted `pos`: rank `r` of slot `j` sits in period `r / w j` at in-block
offset `r % w j`, i.e. `(r / w j) * W + weightBlockStart w j + (r % w j)`. -/
def weightedPos (w : Fin m → ℕ) (j : Fin m) (r : ℕ) : ℕ :=
  r / w j * (∑ j', w j') + weightBlockStart w j + r % w j

theorem weightedPos_mod (w : Fin m → ℕ) (hw : ∀ j, 0 < w j) (j : Fin m) (r : ℕ) :
    weightedPos w j r % (∑ j', w j') = weightBlockStart w j + r % w j := by
  have hlt : weightBlockStart w j + r % w j < ∑ j', w j' :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt r (hw j)) _)
      (weightBlockStart_add_weight_le w j)
  rw [weightedPos, Nat.add_assoc, Nat.mul_add_mod', Nat.mod_eq_of_lt hlt]

theorem weightedPos_div (w : Fin m → ℕ) (hm : 0 < m) (hw : ∀ j, 0 < w j)
    (j : Fin m) (r : ℕ) : weightedPos w j r / (∑ j', w j') = r / w j := by
  have hlt : weightBlockStart w j + r % w j < ∑ j', w j' :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt r (hw j)) _)
      (weightBlockStart_add_weight_le w j)
  rw [weightedPos, Nat.add_assoc, Nat.mul_comm,
    Nat.mul_add_div (weightSum_pos hm hw), Nat.div_eq_of_lt hlt, Nat.add_zero]

/-- Law 1: slot `j` owns all its positions. -/
theorem weightedPos_slotOf (w : Fin m → ℕ) (hm : 0 < m) (hw : ∀ j, 0 < w j)
    (j : Fin m) (r : ℕ) : weightedSlotOf w hm (weightedPos w j r) = j := by
  have hj := j.isLt
  apply Fin.ext
  show m - 1 - weightBlockIdx w (weightedPos w j r % ∑ j', w j') = j.val
  rw [weightedPos_mod w hw, weightBlockIdx_blockStart_add w j (Nat.mod_lt r (hw j))]
  omega

/-- Law 2: `pos j r` is the `r`-th position of its slot. -/
theorem weightedRank_pos (w : Fin m → ℕ) (hm : 0 < m) (hw : ∀ j, 0 < w j)
    (j : Fin m) (r : ℕ) : weightedRank w hm (weightedPos w j r) = r := by
  rw [weightedRank, weightedPos_slotOf w hm hw, weightedPos_mod w hw,
    weightBlockIdx_blockStart_add w j (Nat.mod_lt r (hw j)),
    weightedPos_div w hm hw]
  have hbs : revWeightSum w (m - 1 - j.val) = weightBlockStart w j := rfl
  rw [hbs, Nat.add_sub_cancel_left, Nat.mul_comm]
  exact Nat.div_add_mod r (w j)

/-- Law 3: every position is reached — `pos` inverts `(slotOf, rank)`. -/
theorem weightedPos_rank (w : Fin m → ℕ) (hm : 0 < m) (hw : ∀ j, 0 < w j) (i : ℕ) :
    weightedPos w (weightedSlotOf w hm i) (weightedRank w hm i) = i := by
  have hW : 0 < ∑ j', w j' := weightSum_pos hm hw
  obtain ⟨j, s, hs, ht, -⟩ :=
    exists_weightBlock_decomp w hm (Nat.mod_lt i hW)
  have hdiv : (i / (∑ j', w j') * w j + s) / w j = i / (∑ j', w j') := by
    rw [Nat.mul_comm, Nat.mul_add_div (hw j), Nat.div_eq_of_lt hs, Nat.add_zero]
  have hmod : (i / (∑ j', w j') * w j + s) % w j = s := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hs]
  have hkey : weightedPos w j (i / (∑ j', w j') * w j + s) = i := by
    rw [weightedPos, hdiv, hmod, Nat.add_assoc, ← ht, Nat.mul_comm]
    exact Nat.div_add_mod i _
  rw [← hkey, weightedPos_slotOf w hm hw, weightedRank_pos w hm hw]

/-- Law 4 (generic core): `r ↦ (r / d) * W + c + r % d` is strictly monotone
when `0 < d ≤ W` — mixed-radix reading of `r` with the low digit kept and the
high part rescaled to a wider base. -/
theorem weightedPos_strictMono_aux {d W c : ℕ} (hd : 0 < d) (hdW : d ≤ W) :
    StrictMono fun r => r / d * W + c + r % d := by
  intro r r' h
  simp only
  have hle : r / d ≤ r' / d := Nat.div_le_div_right h.le
  rcases Nat.lt_or_ge (r / d) (r' / d) with hq | hq
  · calc r / d * W + c + r % d < r / d * W + c + d :=
          Nat.add_lt_add_left (Nat.mod_lt r hd) _
      _ ≤ r / d * W + c + W := Nat.add_le_add_left hdW _
      _ = (r / d + 1) * W + c := by ring
      _ ≤ r' / d * W + c :=
          Nat.add_le_add_right (Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq)) c
      _ ≤ r' / d * W + c + r' % d := Nat.le_add_right _ _
  · have heq : r / d = r' / d := le_antisymm hle hq
    have e1 := Nat.div_add_mod r d
    have e2 := Nat.div_add_mod r' d
    rw [← heq] at e2
    have hs : r % d < r' % d := by
      have hlt : d * (r / d) + r % d < d * (r / d) + r' % d := by
        rw [e1, e2]; exact h
      exact Nat.lt_of_add_lt_add_left hlt
    rw [heq]
    exact Nat.add_lt_add_left hs _

/-- **The weighted round-robin assignment** (Malachite
`[normal(w 0), …, normal(w (m-1))]`): period `W = ∑ j, w j`; within each
period the slots own consecutive blocks of their weight in DECREASING slot
order (slot `m - 1` owns the `w (m-1)` least-significant positions — the
`[normal(2); 3]` bit-map doctest `[2, 2, 1, 1, 0, 0, …]`). The bijection
`ℕ ≃ (Fin m → ℕ)` and all of `deinterleave`/`interleave` come free from
`BitInterleave`. Slot `j`'s deinterleaved component grows like
`k ^ (w j / W)`. -/
def weightedRoundRobin (w : Fin m → ℕ) (hm : 0 < m) (hw : ∀ j, 0 < w j) :
    BitAssignment m where
  slotOf := weightedSlotOf w hm
  rank := weightedRank w hm
  pos := weightedPos w
  pos_slotOf := weightedPos_slotOf w hm hw
  rank_pos := weightedRank_pos w hm hw
  pos_rank := weightedPos_rank w hm hw
  pos_strictMono j :=
    weightedPos_strictMono_aux (hw j) (weight_le_sum w j)

@[simp] theorem weightedRoundRobin_slotOf (w : Fin m → ℕ) (hm : 0 < m)
    (hw : ∀ j, 0 < w j) : (weightedRoundRobin w hm hw).slotOf = weightedSlotOf w hm := rfl

@[simp] theorem weightedRoundRobin_rank (w : Fin m → ℕ) (hm : 0 < m)
    (hw : ∀ j, 0 < w j) : (weightedRoundRobin w hm hw).rank = weightedRank w hm := rfl

@[simp] theorem weightedRoundRobin_pos (w : Fin m → ℕ) (hm : 0 < m)
    (hw : ∀ j, 0 < w j) : (weightedRoundRobin w hm hw).pos = weightedPos w := rfl

/-! ### Degeneration: all weights `1` is `roundRobin` -/

theorem sum_const_one (m : ℕ) : (∑ _j : Fin m, (1 : ℕ)) = m := by simp

theorem revWeightSum_one {r : ℕ} (hr : r ≤ m) :
    revWeightSum (fun _ : Fin m => 1) r = r := by
  calc revWeightSum (fun _ : Fin m => 1) r
      = ∑ _i ∈ Finset.range r, 1 :=
        Finset.sum_congr rfl fun i hi =>
          dite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hr)
    _ = r := by simp

theorem weightBlockIdx_one {t : ℕ} (ht : t < m) :
    weightBlockIdx (fun _ : Fin m => 1) t = t :=
  weightBlockIdx_eq _ ht (by rw [revWeightSum_one ht.le])
    (by rw [revWeightSum_one (by omega)]; omega)

/-- With all weights `1`, `weightedRoundRobin` has `roundRobin`'s `slotOf`. -/
theorem weightedRoundRobin_one_slotOf (hm : 0 < m) (i : ℕ) :
    (weightedRoundRobin (fun _ => 1) hm (fun _ => Nat.one_pos)).slotOf i
      = (roundRobin m hm).slotOf i := by
  apply Fin.ext
  show m - 1 - weightBlockIdx (fun _ : Fin m => 1) (i % ∑ _j : Fin m, (1 : ℕ))
    = m - 1 - i % m
  rw [sum_const_one, weightBlockIdx_one (Nat.mod_lt i hm)]

/-- With all weights `1`, `weightedRoundRobin` has `roundRobin`'s `rank`. -/
theorem weightedRoundRobin_one_rank (hm : 0 < m) (i : ℕ) :
    (weightedRoundRobin (fun _ => 1) hm (fun _ => Nat.one_pos)).rank i
      = (roundRobin m hm).rank i := by
  show weightedRank (fun _ : Fin m => 1) hm i = i / m
  rw [weightedRank, sum_const_one, weightBlockIdx_one (Nat.mod_lt i hm),
    revWeightSum_one (Nat.mod_lt i hm).le]
  omega

/-- With all weights `1`, `weightedRoundRobin` has `roundRobin`'s `pos`. -/
theorem weightedRoundRobin_one_pos (hm : 0 < m) (j : Fin m) (r : ℕ) :
    (weightedRoundRobin (fun _ => 1) hm (fun _ => Nat.one_pos)).pos j r
      = (roundRobin m hm).pos j r := by
  have hj := j.isLt
  show weightedPos (fun _ : Fin m => 1) j r = r * m + (m - 1 - j.val)
  rw [weightedPos, weightBlockStart, sum_const_one, revWeightSum_one (by omega),
    Nat.div_one, Nat.mod_one, Nat.add_zero]

/-! ### Guards (pin Malachite's weighted semantics)

The `[normal(2); 3]` `bit_map_as_slice` doctest: consecutive weight-2 blocks
in decreasing slot order, `[2, 2, 1, 1, 0, 0]` repeating. -/

#guard (List.range 12).map
    (fun i => ((weightedRoundRobin ![2, 2, 2] (by omega) (by decide)).slotOf i).val)
  == [2, 2, 1, 1, 0, 0, 2, 2, 1, 1, 0, 0]

-- Rust `bit_distributor_sequence(normal(1), normal(2))`: the constructor
-- SWAPS the arguments — `BitDistributor::new(&[y_output_type, x_output_type])`
-- with `x = normal(1)`, `y = normal(2)` — and streams `get_output(1)`. So the
-- doctest sequence is slot 1 of the WEIGHTS-`![2, 1]` distributor:
-- `[0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, …]` (grows like `n^(1/3)`).
#guard (List.range 50).map ((weightedRoundRobin ![2, 1] (by omega) (by decide)).deinterleave 1)
  == [0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3,
      2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1]

-- Rust `bit_distributor_sequence(normal(2), normal(1))`: slot 1 of the
-- weights-`![1, 2]` distributor: `[0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, …]`
-- (grows like `n^(2/3)`).
#guard (List.range 50).map ((weightedRoundRobin ![1, 2] (by omega) (by decide)).deinterleave 1)
  == [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 8, 9, 10, 11, 8, 9, 10, 11, 12,
      13, 14, 15, 12, 13, 14, 15, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 8, 9]

-- Round-trips both ways under weighted assignments.
#guard (let A := weightedRoundRobin ![1, 2] (by omega) (by decide);
  (List.range 40).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
#guard (let A := weightedRoundRobin ![3, 1, 2] (by omega) (by decide);
  (List.range 40).all fun k =>
    A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k, A.deinterleave 2 k] == k)
#guard (let A := weightedRoundRobin ![1, 2] (by omega) (by decide);
  let k := A.interleave ![5, 11];
  (A.deinterleave 0 k, A.deinterleave 1 k)) == (5, 11)

end Azurite
