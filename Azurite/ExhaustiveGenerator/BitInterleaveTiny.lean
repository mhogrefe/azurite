/-
  `BitInterleaveTiny` — TINY output types: the RULER `BitAssignment`
  (Malachite `BitDistributorOutputType::tiny()`).

  Tiny slots own the RULER positions — the counter-bit positions `i` such that
  `i + 1` is a power of two (`i ∈ {0, 1, 3, 7, 15, 31, …}`; NB `i = 0` AND
  `i = 1` are both ruler positions, since `i + 1 ∈ {1, 2}`) — rotating among
  multiple tiny slots in DECREASING slot order starting from the LAST tiny slot
  (Malachite's `update_bit_map`: `ti` starts at the last tiny index and
  decrements with wraparound). Normal slots own all OTHER positions, rotating
  per their weights exactly as in `weightedRoundRobin` (the weight counter only
  advances when a normal position is consumed). The `[normal(2), tiny()]`
  `bit_map_as_slice` doctest is the oracle:

    `[1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, …]`

  (slot 1, the tiny, at `i = 0, 1, 3, 7, 15, …`). With `t` tiny slots a tiny
  component grows as `O((log k)^(1/t))` in the counter `k`; the normal slots'
  growth is unaffected.

  Closed forms. The `r`-th ruler position (0-based, ascending) is `2 ^ r - 1`,
  and the ruler rank of a ruler position `i` is `i.size` (`(2 ^ r - 1).size =
  r`), so the tiny side is exactly `roundRobin t` composed with `r ↦ 2 ^ r - 1`
  and the tiny-slot order embedding. On the normal side, the number of ruler
  positions `≤ i` is `(i + 1).size`, so the NON-ruler rank of a non-ruler `i`
  is `i - (i + 1).size`; the inverse is `nonRulerPos n = n + rulerBlockIdx n +
  1`, where `rulerBlockIdx n` — the index `s ≥ 1` of the inter-ruler block
  `(2 ^ s - 1, 2 ^ (s + 1) - 1)` holding the `n`-th non-ruler position, unique
  `s` with `2 ^ s - s - 1 ≤ n < 2 ^ (s + 1) - s - 2` — is a `Finset` count
  (the `weightBlockIdx` house trick: totality and computability with the
  uniqueness proof built in, instead of chasing a closed inverse). The normal
  side is then `weightedRoundRobin` over the normal slots conjugated by
  `nonRulerPos`/the non-ruler rank and the normal-slot order embedding.

  The slot partition is given as `isTiny : Fin m → Bool` plus weights
  `w : Fin m → ℕ` (only read on normal slots — Malachite stores weight `0` on
  tiny slots); the order embeddings `Fin (tinyCount) ↪o Fin m` /
  `Fin (normalCount) ↪o Fin m` are `Finset.orderEmbOfFin` of the filtered slot
  sets. Hypotheses: at least one NORMAL slot (`0 < normalCount` — Malachite
  panics on all-tiny) and at least one TINY slot (`0 < tinyCount` — the
  all-normal case has DIFFERENT semantics, no reserved ruler positions; use
  `weightedRoundRobin`), plus positive weights on the normal slots. The four
  `BitAssignment` laws reduce to the `roundRobin`/`weightedRoundRobin` laws
  through the ruler/non-ruler characterizations, so the bijection
  `ℕ ≃ (Fin m → ℕ)` and `deinterleave`/`interleave` come FREE from
  `BitInterleave`.
-/
import Mathlib.Data.Finset.Sort
import Azurite.ExhaustiveGenerator.BitInterleaveWeighted
import Azurite.ExhaustiveGenerator.FairPairs

namespace Azurite

/-! ### Ruler positions

The positions reserved for tiny slots: `i` with `i + 1` a power of two. The
`r`-th ruler position is `2 ^ r - 1`, and `Nat.size` reads the rank back off. -/

/-- **The ruler-position test**: `i + 1` is a power of two, i.e. `i ∈ {0, 1,
3, 7, 15, …}`. The computable test compares `i + 1` with `2 ^ i.size` (for
`i = 2 ^ s - 1` the size is exactly `s`); `isRulerPos_iff` is the spec. -/
def isRulerPos (i : ℕ) : Bool := decide (i + 1 = 2 ^ i.size)

/-- `2 ^ e - 1` has bit-length `e`: the ruler rank of a ruler position is its
`Nat.size`. -/
theorem size_two_pow_sub_one (e : ℕ) : (2 ^ e - 1).size = e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · have h2 : 2 ^ (e - 1) * 2 = 2 ^ e := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have h1 : (0 : ℕ) < 2 ^ (e - 1) := by positivity
    have hle : (2 ^ e - 1).size ≤ e := Nat.size_le.mpr (by omega)
    have hlt : e - 1 < (2 ^ e - 1).size := Nat.lt_size.mpr (by omega)
    omega

/-- The spec of the computable test: `i` is a ruler position iff `i + 1` is a
power of two. -/
theorem isRulerPos_iff {i : ℕ} : isRulerPos i = true ↔ ∃ s, i + 1 = 2 ^ s := by
  rw [isRulerPos, decide_eq_true_iff]
  refine ⟨fun h => ⟨i.size, h⟩, ?_⟩
  rintro ⟨s, hs⟩
  have hpow : (0 : ℕ) < 2 ^ s := by positivity
  have hi : i = 2 ^ s - 1 := by omega
  rw [hi, size_two_pow_sub_one]
  omega

/-- The `r`-th ruler position `2 ^ r - 1` passes the test. -/
theorem isRulerPos_two_pow_sub_one (e : ℕ) : isRulerPos (2 ^ e - 1) = true :=
  isRulerPos_iff.mpr ⟨e, by
    have : (0 : ℕ) < 2 ^ e := by positivity
    omega⟩

/-- Negative spec: `i` is a non-ruler position iff `i + 1` misses EVERY power
of two (not just `2 ^ i.size`). -/
theorem isRulerPos_eq_false_iff {i : ℕ} :
    isRulerPos i = false ↔ ∀ s, i + 1 ≠ 2 ^ s := by
  constructor
  · intro h s hs
    have h2 := isRulerPos_iff.mpr ⟨s, hs⟩
    rw [h] at h2
    exact Bool.false_ne_true h2
  · intro h
    cases hb : isRulerPos i with
    | false => rfl
    | true =>
      obtain ⟨s, hs⟩ := isRulerPos_iff.mp hb
      exact absurd hs (h s)

/-! ### The non-ruler rank and its inverse

The count of ruler positions `≤ i` is `(i + 1).size` (`2 ^ s - 1 ≤ i` iff
`s < (i + 1).size`), so a non-ruler `i` has non-ruler rank `i - (i + 1).size`.
The inverse adds the rank's inter-ruler block index back:
`nonRulerPos n = n + rulerBlockIdx n + 1`. -/

/-- Generic bit lemma powering the block-index arithmetic: `2 ^ a` grows at
least linearly, `2 ^ a + b ≤ 2 ^ b + a` for `a ≤ b`. -/
theorem two_pow_add_le {a b : ℕ} (h : a ≤ b) : 2 ^ a + b ≤ 2 ^ b + a := by
  induction b, h using Nat.le_induction with
  | base => omega
  | succ b _ ih =>
    have h1 : (0 : ℕ) < 2 ^ b := by positivity
    have h2 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ ..
    omega

/-- **The inter-ruler block index** of a non-ruler rank `n`: the unique
`s ≥ 1` with `2 ^ s - s - 1 ≤ n < 2 ^ (s + 1) - s - 2`, i.e. the `n`-th
non-ruler position lies strictly between the rulers `2 ^ s - 1` and
`2 ^ (s + 1) - 1`. Computed as a `Finset` count (the `weightBlockIdx` house
trick — total and computable, uniqueness in `rulerBlockIdx_eq`); the filter
condition `2 ^ (u + 1) ≤ n + u + 2` is the subtraction-free form of
`2 ^ (u + 1) - (u + 1) - 1 ≤ n`. -/
def rulerBlockIdx (n : ℕ) : ℕ :=
  ((Finset.range (n + 2)).filter fun u => 2 ^ (u + 1) ≤ n + u + 2).card

/-- **Uniqueness.** If `n` lies in block `s` (subtraction-free bounds), then
`rulerBlockIdx n = s`: the filter is exactly `Finset.range s`. -/
theorem rulerBlockIdx_eq {n s : ℕ} (hs : 1 ≤ s) (h1 : 2 ^ s ≤ n + s + 1)
    (h2 : n + s + 2 < 2 ^ (s + 1)) : rulerBlockIdx n = s := by
  have hs2 : s ≤ n + 1 := by
    have ha := Nat.lt_two_pow_self (n := s - 1)
    have hb : 2 ^ (s - 1) * 2 = 2 ^ s := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    omega
  have hfil : (Finset.range (n + 2)).filter (fun u => 2 ^ (u + 1) ≤ n + u + 2)
      = Finset.range s := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hcond⟩
      by_contra hnot
      have hle := two_pow_add_le (show s + 1 ≤ u + 1 by omega)
      omega
    · intro hu
      have hle := two_pow_add_le (show u + 1 ≤ s by omega)
      exact ⟨by omega, by omega⟩
  rw [rulerBlockIdx, hfil, Finset.card_range]

/-- **Existence/spec.** Every rank `n` lies in some block: `rulerBlockIdx n`
satisfies the block bounds (least `s` with `n + s + 2 < 2 ^ (s + 1)` via
`Nat.find`, then pinned by uniqueness). -/
theorem rulerBlockIdx_spec (n : ℕ) :
    1 ≤ rulerBlockIdx n ∧ 2 ^ rulerBlockIdx n ≤ n + rulerBlockIdx n + 1
      ∧ n + rulerBlockIdx n + 2 < 2 ^ (rulerBlockIdx n + 1) := by
  have hex : ∃ s, n + s + 2 < 2 ^ (s + 1) := by
    refine ⟨n + 1, ?_⟩
    have h0 := Nat.lt_two_pow_self (n := n)
    have h4 : 2 ^ (n + 2) = 2 ^ n * 4 := by
      rw [Nat.pow_succ, Nat.pow_succ]
      ring
    omega
  have hspec : n + Nat.find hex + 2 < 2 ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hs1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have hz : Nat.find hex = 0 := by omega
    rw [hz] at hspec
    norm_num at hspec
  have h1 : 2 ^ Nat.find hex ≤ n + Nat.find hex + 1 := by
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
    omega
  rw [rulerBlockIdx_eq hs1 h1 hspec]
  exact ⟨hs1, h1, hspec⟩

/-- The block index is monotone in the rank (filter grows with `n`). -/
theorem rulerBlockIdx_mono : Monotone rulerBlockIdx := by
  intro a b hab
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
  omega

/-- **The `n`-th non-ruler position** (0-based, ascending): the rank plus the
number of rulers below it, which is `rulerBlockIdx n + 1`. This is the
`pos`-side inverse of the non-ruler rank `i - (i + 1).size`. -/
def nonRulerPos (n : ℕ) : ℕ := n + rulerBlockIdx n + 1

/-- Non-ruler positions are strictly ascending in the rank. -/
theorem nonRulerPos_strictMono : StrictMono nonRulerPos := by
  intro a b hab
  have := rulerBlockIdx_mono hab.le
  unfold nonRulerPos
  omega

/-- `nonRulerPos n + 1` has bit-length `rulerBlockIdx n + 1`: the count of
ruler positions `≤ nonRulerPos n`. -/
theorem size_nonRulerPos_succ (n : ℕ) :
    (nonRulerPos n + 1).size = rulerBlockIdx n + 1 := by
  obtain ⟨hs1, h1, h2⟩ := rulerBlockIdx_spec n
  have hle : (nonRulerPos n + 1).size ≤ rulerBlockIdx n + 1 :=
    Nat.size_le.mpr (by unfold nonRulerPos; omega)
  have hlt : rulerBlockIdx n < (nonRulerPos n + 1).size :=
    Nat.lt_size.mpr (by unfold nonRulerPos; omega)
  omega

/-- `nonRulerPos` lands strictly between consecutive rulers. -/
theorem isRulerPos_nonRulerPos (n : ℕ) : isRulerPos (nonRulerPos n) = false := by
  obtain ⟨hs1, h1, h2⟩ := rulerBlockIdx_spec n
  rw [isRulerPos_eq_false_iff]
  intro s hs
  have hlo : 2 ^ rulerBlockIdx n < nonRulerPos n + 1 := by unfold nonRulerPos; omega
  have hhi : nonRulerPos n + 1 < 2 ^ (rulerBlockIdx n + 1) := by unfold nonRulerPos; omega
  rw [hs] at hlo hhi
  have h3 : rulerBlockIdx n < s := by
    by_contra hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show s ≤ rulerBlockIdx n by omega)
    omega
  have h4 : s ≤ rulerBlockIdx n := by
    by_contra hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show rulerBlockIdx n + 1 ≤ s by omega)
    omega
  omega

/-- Rank round-trip, `pos` then rank: the non-ruler rank of `nonRulerPos n`
is `n`. -/
theorem nonRulerPos_rank (n : ℕ) : nonRulerPos n - (nonRulerPos n + 1).size = n := by
  rw [size_nonRulerPos_succ]
  unfold nonRulerPos
  omega

/-- Rank round-trip, rank then `pos`: every non-ruler position is
`nonRulerPos` of its non-ruler rank. The block index of the rank is
`(i + 1).size - 1` (the position sits strictly between the rulers
`2 ^ ((i+1).size - 1) - 1` and `2 ^ (i+1).size - 1`). -/
theorem nonRulerPos_nonRulerRank {i : ℕ} (h : isRulerPos i = false) :
    nonRulerPos (i - (i + 1).size) = i := by
  have hne := isRulerPos_eq_false_iff.mp h
  set σ := (i + 1).size with hσ
  have hσpos : 0 < σ := by
    have := Nat.size_pos.mpr (show 0 < i + 1 by omega)
    omega
  have hup : i + 1 < 2 ^ σ := Nat.lt_size_self (i + 1)
  have hlow : 2 ^ (σ - 1) ≤ i + 1 := Nat.lt_size.mp (by omega)
  have hne' : i + 1 ≠ 2 ^ (σ - 1) := hne (σ - 1)
  have hσ2 : 2 ≤ σ := by
    by_contra hc
    have h1 : σ = 1 := by omega
    rw [h1] at hup hlow hne'
    norm_num at hup hlow hne'
    omega
  have hsz : σ ≤ 2 ^ (σ - 1) := by
    have := Nat.lt_two_pow_self (n := σ - 1)
    omega
  have hiσ : σ ≤ i := by omega
  have heq : rulerBlockIdx (i - σ) = σ - 1 := by
    apply rulerBlockIdx_eq
    · omega
    · have he : i - σ + (σ - 1) + 1 = i := by omega
      rw [he]
      omega
    · have he : i - σ + (σ - 1) + 2 = i + 1 := by omega
      have he2 : σ - 1 + 1 = σ := by omega
      rw [he, he2]
      exact hup
  unfold nonRulerPos
  rw [heq]
  omega

/-! ### The tiny/normal slot partition

The `isTiny` mask splits `Fin m` into the tiny and normal slot sets; the
order embeddings `Finset.orderEmbOfFin` enumerate each set ascending, and
`tinyIdx`/`normalIdx` invert them (via `Finset.orderIsoOfFin`). -/

variable {m : ℕ}

/-- The tiny slots: the filter of the `isTiny` mask. -/
def tinySlots (isTiny : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun j => isTiny j = true

/-- The normal slots: the complement filter. -/
def normalSlots (isTiny : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun j => isTiny j = false

/-- The number `t` of tiny slots. -/
def tinyCount (isTiny : Fin m → Bool) : ℕ := (tinySlots isTiny).card

/-- The number of normal slots. -/
def normalCount (isTiny : Fin m → Bool) : ℕ := (normalSlots isTiny).card

theorem card_tinySlots (isTiny : Fin m → Bool) :
    (tinySlots isTiny).card = tinyCount isTiny := rfl

theorem card_normalSlots (isTiny : Fin m → Bool) :
    (normalSlots isTiny).card = normalCount isTiny := rfl

/-- The ascending enumeration of the tiny slots. -/
def tinyEmb (isTiny : Fin m → Bool) : Fin (tinyCount isTiny) ↪o Fin m :=
  (tinySlots isTiny).orderEmbOfFin (card_tinySlots isTiny)

/-- The ascending enumeration of the normal slots. -/
def normalEmb (isTiny : Fin m → Bool) : Fin (normalCount isTiny) ↪o Fin m :=
  (normalSlots isTiny).orderEmbOfFin (card_normalSlots isTiny)

theorem isTiny_tinyEmb (isTiny : Fin m → Bool) (c : Fin (tinyCount isTiny)) :
    isTiny (tinyEmb isTiny c) = true :=
  (Finset.mem_filter.mp
    ((tinySlots isTiny).orderEmbOfFin_mem (card_tinySlots isTiny) c)).2

theorem isTiny_normalEmb (isTiny : Fin m → Bool) (c : Fin (normalCount isTiny)) :
    isTiny (normalEmb isTiny c) = false :=
  (Finset.mem_filter.mp
    ((normalSlots isTiny).orderEmbOfFin_mem (card_normalSlots isTiny) c)).2

/-- The tiny-order index of a tiny slot: the inverse of `tinyEmb`. -/
def tinyIdx (isTiny : Fin m → Bool) (j : Fin m) (hj : isTiny j = true) :
    Fin (tinyCount isTiny) :=
  ((tinySlots isTiny).orderIsoOfFin (card_tinySlots isTiny)).symm
    ⟨j, by simp [tinySlots, hj]⟩

/-- The normal-order index of a normal slot: the inverse of `normalEmb`. -/
def normalIdx (isTiny : Fin m → Bool) (j : Fin m) (hj : isTiny j = false) :
    Fin (normalCount isTiny) :=
  ((normalSlots isTiny).orderIsoOfFin (card_normalSlots isTiny)).symm
    ⟨j, by simp [normalSlots, hj]⟩

theorem tinyEmb_tinyIdx (isTiny : Fin m → Bool) {j : Fin m} (hj : isTiny j = true) :
    tinyEmb isTiny (tinyIdx isTiny j hj) = j := by
  show (tinySlots isTiny).orderEmbOfFin (card_tinySlots isTiny)
    (tinyIdx isTiny j hj) = j
  rw [← Finset.coe_orderIsoOfFin_apply, tinyIdx, OrderIso.apply_symm_apply]

theorem normalEmb_normalIdx (isTiny : Fin m → Bool) {j : Fin m}
    (hj : isTiny j = false) : normalEmb isTiny (normalIdx isTiny j hj) = j := by
  show (normalSlots isTiny).orderEmbOfFin (card_normalSlots isTiny)
    (normalIdx isTiny j hj) = j
  rw [← Finset.coe_orderIsoOfFin_apply, normalIdx, OrderIso.apply_symm_apply]

theorem tinyIdx_tinyEmb (isTiny : Fin m → Bool) (c : Fin (tinyCount isTiny))
    (h : isTiny (tinyEmb isTiny c) = true) :
    tinyIdx isTiny (tinyEmb isTiny c) h = c :=
  (tinyEmb isTiny).injective (tinyEmb_tinyIdx isTiny h)

theorem normalIdx_normalEmb (isTiny : Fin m → Bool) (c : Fin (normalCount isTiny))
    (h : isTiny (normalEmb isTiny c) = false) :
    normalIdx isTiny (normalEmb isTiny c) h = c :=
  (normalEmb isTiny).injective (normalEmb_normalIdx isTiny h)

/-- The weights of the normal slots, in normal order — the weight function the
inner `weightedRoundRobin` runs on. -/
def normalWeights (isTiny : Fin m → Bool) (w : Fin m → ℕ) :
    Fin (normalCount isTiny) → ℕ :=
  fun c => w (normalEmb isTiny c)

theorem normalWeights_pos (isTiny : Fin m → Bool) {w : Fin m → ℕ}
    (hw : ∀ j, isTiny j = false → 0 < w j) (c : Fin (normalCount isTiny)) :
    0 < normalWeights isTiny w c :=
  hw _ (isTiny_normalEmb isTiny c)

/-! ### The three maps and their laws

Each map is the two-branch composite: on ruler positions, `roundRobin
(tinyCount)` on the ruler rank `i.size` behind `tinyEmb`; on non-ruler
positions, `weightedRoundRobin (normalWeights)` on the non-ruler rank
`i - (i + 1).size` behind `normalEmb`. -/

/-- Tiny `slotOf`: ruler positions go to the tiny slots by decreasing-order
round-robin on the ruler rank (`i = 0` to the LAST tiny slot); non-ruler
positions to the normal slots by the weighted rotation on the non-ruler
rank. -/
def tinySlotOf (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny) (i : ℕ) : Fin m :=
  if isRulerPos i then
    tinyEmb isTiny ((roundRobin (tinyCount isTiny) ht).slotOf i.size)
  else
    normalEmb isTiny (weightedSlotOf (normalWeights isTiny w) hn (i - (i + 1).size))

/-- Tiny `rank`: the round-robin rank of the ruler rank, resp. the weighted
rank of the non-ruler rank. -/
def tinyRank (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny) (i : ℕ) : ℕ :=
  if isRulerPos i then (roundRobin (tinyCount isTiny) ht).rank i.size
  else weightedRank (normalWeights isTiny w) hn (i - (i + 1).size)

/-- Tiny `pos`: the `r`-th position of tiny slot `j` (tiny-order index `c`)
is the ruler position `2 ^ (r * t + (t - 1 - c)) - 1`; the `r`-th position of
a normal slot is `nonRulerPos` of its weighted position among the non-ruler
ranks. -/
def tinyPos (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (j : Fin m) (r : ℕ) : ℕ :=
  if hj : isTiny j = true then
    2 ^ ((roundRobin (tinyCount isTiny) ht).pos (tinyIdx isTiny j hj) r) - 1
  else
    nonRulerPos (weightedPos (normalWeights isTiny w)
      (normalIdx isTiny j (by simpa using hj)) r)

/-- Law 1: slot `j` owns all its positions. -/
theorem tinyPos_slotOf (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) (j : Fin m) (r : ℕ) :
    tinySlotOf isTiny w ht hn (tinyPos isTiny w ht j r) = j := by
  unfold tinyPos tinySlotOf
  by_cases hj : isTiny j = true
  · rw [dite_eq_left hj, ite_eq_left (isRulerPos_two_pow_sub_one _), size_two_pow_sub_one,
      (roundRobin (tinyCount isTiny) ht).pos_slotOf]
    exact tinyEmb_tinyIdx isTiny hj
  · rw [dite_eq_right hj, ite_eq_right (by simp [isRulerPos_nonRulerPos]), nonRulerPos_rank,
      weightedPos_slotOf _ hn (normalWeights_pos isTiny hw)]
    exact normalEmb_normalIdx isTiny (by simpa using hj)

/-- Law 2: `pos j r` is the `r`-th position of its slot. -/
theorem tinyRank_pos (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) (j : Fin m) (r : ℕ) :
    tinyRank isTiny w ht hn (tinyPos isTiny w ht j r) = r := by
  unfold tinyPos tinyRank
  by_cases hj : isTiny j = true
  · rw [dite_eq_left hj, ite_eq_left (isRulerPos_two_pow_sub_one _), size_two_pow_sub_one,
      (roundRobin (tinyCount isTiny) ht).rank_pos]
  · rw [dite_eq_right hj, ite_eq_right (by simp [isRulerPos_nonRulerPos]), nonRulerPos_rank,
      weightedRank_pos _ hn (normalWeights_pos isTiny hw)]

/-- Law 3: every position is reached — `pos` inverts `(slotOf, rank)`. -/
theorem tinyPos_rank (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) (i : ℕ) :
    tinyPos isTiny w ht (tinySlotOf isTiny w ht hn i) (tinyRank isTiny w ht hn i)
      = i := by
  unfold tinySlotOf tinyRank tinyPos
  by_cases hi : isRulerPos i = true
  · rw [ite_eq_left hi, ite_eq_left hi, dite_eq_left (isTiny_tinyEmb isTiny _), tinyIdx_tinyEmb,
      (roundRobin (tinyCount isTiny) ht).pos_rank]
    have h2 : i + 1 = 2 ^ i.size := of_decide_eq_true hi
    omega
  · have hi' : isRulerPos i = false := by simpa using hi
    rw [ite_eq_right hi, ite_eq_right hi, dite_eq_right (by simp [isTiny_normalEmb]),
      normalIdx_normalEmb, weightedPos_rank _ hn (normalWeights_pos isTiny hw)]
    exact nonRulerPos_nonRulerRank hi'

/-- Law 4: each slot's positions are strictly ascending — `2 ^ ·` on the
strictly monotone round-robin positions, resp. `nonRulerPos` on the strictly
monotone weighted positions. -/
theorem tinyPos_strictMono (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hw : ∀ j, isTiny j = false → 0 < w j)
    (j : Fin m) : StrictMono (tinyPos isTiny w ht j) := by
  intro r r' hr
  unfold tinyPos
  by_cases hj : isTiny j = true
  · rw [dite_eq_left hj, dite_eq_left hj]
    have hlt := (roundRobin (tinyCount isTiny) ht).pos_strictMono
      (tinyIdx isTiny j hj) hr
    have h1 : (0 : ℕ)
        < 2 ^ ((roundRobin (tinyCount isTiny) ht).pos (tinyIdx isTiny j hj) r) := by
      positivity
    have h2 := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) hlt
    omega
  · rw [dite_eq_right hj, dite_eq_right hj]
    exact nonRulerPos_strictMono
      (weightedPos_strictMono_aux (normalWeights_pos isTiny hw _)
        (weight_le_sum (normalWeights isTiny w) _) hr)

/-- **The tiny/ruler assignment** (Malachite `BitDistributorOutputType::tiny()`
mixed with `normal(w)`): the tiny slots own the ruler positions
`{0, 1, 3, 7, 15, …}` in decreasing-order rotation (`i = 0` goes to the LAST
tiny slot); the normal slots own the other positions in the weighted rotation.
Hypotheses: at least one tiny slot (all-normal is `weightedRoundRobin` — its
semantics differ, no positions are reserved), at least one normal slot
(Malachite panics on all-tiny), and positive weights on the normal slots
(`w` is not read on tiny slots). A tiny component grows like
`(log k)^(1/tinyCount)`; the bijection `ℕ ≃ (Fin m → ℕ)` and
`deinterleave`/`interleave` come free from `BitInterleave`. -/
def tinyAssignment (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) : BitAssignment m where
  slotOf := tinySlotOf isTiny w ht hn
  rank := tinyRank isTiny w ht hn
  pos := tinyPos isTiny w ht
  pos_slotOf := tinyPos_slotOf isTiny w ht hn hw
  rank_pos := tinyRank_pos isTiny w ht hn hw
  pos_rank := tinyPos_rank isTiny w ht hn hw
  pos_strictMono := tinyPos_strictMono isTiny w ht hw

@[simp] theorem tinyAssignment_slotOf (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) :
    (tinyAssignment isTiny w ht hn hw).slotOf = tinySlotOf isTiny w ht hn := rfl

@[simp] theorem tinyAssignment_rank (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) :
    (tinyAssignment isTiny w ht hn hw).rank = tinyRank isTiny w ht hn := rfl

@[simp] theorem tinyAssignment_pos (isTiny : Fin m → Bool) (w : Fin m → ℕ)
    (ht : 0 < tinyCount isTiny) (hn : 0 < normalCount isTiny)
    (hw : ∀ j, isTiny j = false → 0 < w j) :
    (tinyAssignment isTiny w ht hn hw).pos = tinyPos isTiny w ht := rfl

/-! ### Convenience pair assignments and builders -/

/-- The `[tiny(), normal(1)]` 2-slot assignment: the FIRST component is tiny
(grows like `log k`), the second normal. -/
def fairPairAssignmentTinyFirst : BitAssignment 2 :=
  tinyAssignment ![true, false] ![0, 1] (by decide) (by decide) (by decide)

/-- The `[normal(1), tiny()]` 2-slot assignment: the SECOND component is tiny
(grows like `log k`), the first normal. -/
def fairPairAssignmentTinySecond : BitAssignment 2 :=
  tinyAssignment ![false, true] ![1, 0] (by decide) (by decide) (by decide)

namespace ExhaustiveGenerator

/-- **The tiny-first fair pair generator**: `fairPairGenWith` at
`fairPairAssignmentTinyFirst` — the first component grows like `log k`, the
second like `k / log-factor` (Malachite `exhaustive_pairs_custom_output` with
`[tiny(), normal(1)]`). -/
@[reducible] def fairPairGenTinyFirst {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (hA : ∀ n, gA.gen n ≠ none)
    (hB : ∀ n, gB.gen n ≠ none) : ExhaustiveGenerator (A × B) :=
  fairPairGenWith fairPairAssignmentTinyFirst gA gB hA hB

/-- **The tiny-second fair pair generator**: `fairPairGenWith` at
`fairPairAssignmentTinySecond` — the second component grows like `log k`. -/
@[reducible] def fairPairGenTinySecond {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (hA : ∀ n, gA.gen n ≠ none)
    (hB : ∀ n, gB.gen n ≠ none) : ExhaustiveGenerator (A × B) :=
  fairPairGenWith fairPairAssignmentTinySecond gA gB hA hB

end ExhaustiveGenerator

/-! ### Guards (pin Malachite's tiny semantics)

The ruler positions and the two rank maps. -/

#guard ((List.range 20).filter (fun i => isRulerPos i)) == [0, 1, 3, 7, 15]
#guard (List.range 8).map rulerBlockIdx == [1, 2, 2, 2, 3, 3, 3, 3]
#guard (List.range 8).map nonRulerPos == [2, 4, 5, 6, 8, 9, 10, 11]

/-! The exact `[normal(2), tiny()]` `bit_map_as_slice` doctest (first 32 of the
64 entries): slot 1 (the tiny) at the ruler positions `0, 1, 3, 7, 15, 31`.
The tiny slot's weight entry is `0`, mirroring Malachite's internal
representation — it is never read. -/

#guard (List.range 32).map (fun i =>
    ((tinyAssignment ![false, true] ![2, 0] (by decide) (by decide)
      (by decide)).slotOf i).val)
  == [1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-! TWO tiny slots (`m = 3`, tinys `{0, 2}`, one normal of weight 2): the
decreasing-index rotation gives ruler rank `r` to tiny-order index
`1 - (r % 2)`, so `i = 0` goes to slot 2 (the LAST tiny — where the Rust
`update_bit_map` starts), `i = 1` to slot 0, `i = 3` to slot 2, `i = 7` to
slot 0, `i = 15` to slot 2. -/

/-- Guard exemplar: two tiny slots (`{0, 2}`) around one weight-2 normal. -/
def twoTinyDemoAssignment : BitAssignment 3 :=
  tinyAssignment ![true, false, true] ![0, 2, 0] (by decide) (by decide) (by decide)

#guard (List.range 16).map (fun i => (twoTinyDemoAssignment.slotOf i).val)
  == [2, 0, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2]

/-! Tiny + WEIGHTED normals (`m = 3`, tiny `{2}`, normals `{0, 1}` with
weights `(1, 2)`): the non-ruler positions carry the weighted rotation
`[1, 1, 0]` per period — hand-transcribed from `update_bit_map`. -/

#guard (List.range 17).map (fun i =>
    ((tinyAssignment ![false, false, true] ![1, 2, 0] (by decide) (by decide)
      (by decide)).slotOf i).val)
  == [2, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 1, 1, 2, 0]

/-! The tiny component's LOGARITHMIC growth (the `bit_distributor_sequence
(tiny(), normal(1))` stream, which Rust documents as `O(log n)`): the first 34
values of the tiny slot's deinterleave, hand-derived from the bit map — the
tiny slot reads counter bits `0, 1, 3, 7, 15, …`, so the value stays `≤ 7`
through `k = 127` and first reaches `8` at `k = 128 = 2 ^ 7 + 1 - 1`'s bit 7. -/

#guard (List.range 34).map (fairPairAssignmentTinyFirst.deinterleave 0)
  == [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7,
      0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 0, 1]
#guard ((List.range 128).map (fairPairAssignmentTinyFirst.deinterleave 0)).all (· ≤ 7)
#guard fairPairAssignmentTinyFirst.deinterleave 0 128 == 8

/-! A fair pair over `AzNat × AzNat` with `[tiny, normal]`: the first
component cycles through a logarithmically-growing range while the second
grows nearly linearly. Prefix hand-derived from the bit map. -/

open ExhaustiveGenerator

#guard ((List.range 30).filterMap
    (fairPairGenTinyFirst naturalsGen naturalsGen
      gen_ne_none_of_infinite gen_ne_none_of_infinite).gen).map
    (fun p => (p.1.toNat, p.2.toNat))
  == [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (3, 1),
      (4, 0), (5, 0), (6, 0), (7, 0), (4, 1), (5, 1), (6, 1), (7, 1),
      (0, 2), (1, 2), (2, 2), (3, 2), (0, 3), (1, 3), (2, 3), (3, 3),
      (4, 2), (5, 2), (6, 2), (7, 2), (4, 3), (5, 3)]

-- Deep spot check: `k = 100 = 0b1100100` has no ruler bits set (`x = 0`) and
-- non-ruler bits at positions 2, 5, 6 = non-ruler ranks 0, 2, 3 (`y = 13`).
#guard ((fairPairGenTinyFirst naturalsGen naturalsGen
    gen_ne_none_of_infinite gen_ne_none_of_infinite).gen 100).map
    (fun p => (p.1.toNat, p.2.toNat)) = some (0, 13)

/-! Round-trips both ways under tiny assignments. -/

#guard (let A := fairPairAssignmentTinyFirst;
  (List.range 40).all fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k)
#guard (let A := twoTinyDemoAssignment;
  (List.range 40).all fun k =>
    A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k, A.deinterleave 2 k] == k)
#guard (let A := fairPairAssignmentTinyFirst;
  let k := A.interleave ![5, 11];
  (A.deinterleave 0 k, A.deinterleave 1 k)) == (5, 11)
-- The index of `(2, 1)` computed via `interleave`: tiny value 2 = bit at ruler
-- rank 1 = counter bit 1; normal value 1 = counter bit 2; so `k = 2 + 4 = 6` —
-- exactly where the pair prefix above shows `(2, 1)`.
#guard fairPairAssignmentTinyFirst.interleave ![2, 1] == 6

end Azurite
