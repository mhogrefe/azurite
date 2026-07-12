/-
  `shortlex_vecs_length_range` / `exhaustive_vecs_length_range` — all vecs
  with lengths in the half-open range `[a, b)` (Malachite normalizes `a > b`
  to the empty range; here that is automatic, `card = b - a = 0`).

  Both are their all-length counterparts with the lengths generator swapped
  for a RANGE generator (Malachite: `_from_length_iterator` with
  `primitive_int_increasing_range(a, b)`): `natRangeGen a b` enumerates the
  subtype `{n : ℕ // a ≤ n ∧ n < b}` in increasing order, and the vecs land
  on the corresponding list subtype `{l : List T // a ≤ l.length ∧ l.length
  < b}` — the flattening `⟨n, v⟩ ↦ v.toList` remains a bijection fiber-wise.

  `shortlexVecsLengthRange` is the lexicographic dependent pair over the
  range: length `a` fully, then `a + 1`, …, then done — a FINITE generator
  (for finite `T`) with the exact Malachite count `∑_{k=a}^{b-1} cT^k`
  (the ragged block sum), and its stream matches the Rust verbatim.

  `exhaustiveVecsLengthRange` is the fair dependent pair over the range —
  the bounded-degree polynomial shape: coefficient lists of length `< b`
  are exactly the polynomials of degree `< b - 1`, enumerated fairly with
  every fiber advancing. ORDER NOTE: with a FINITE length iterator the Rust
  machine exhausts it and re-targets the scheduler modulo the live count
  (`i %= len`), so its interleaving differs from the clean absolute-slot
  order (which leaves holes at out-of-range slots); the guards pin our
  order AND replay Malachite's doctest verbatim through the Rust-exact
  simulator — same values, both provably-or-checkably exhaustive-once.
-/
import Azurite.ExhaustiveGenerator.ShortlexVecs
import Azurite.ExhaustiveGenerator.ExhaustiveVecs
import Azurite.ExhaustiveGenerator.ExhaustiveDepPairsSimGen
import Azurite.ExhaustiveGenerator.ZMods

namespace Azurite

/-! ### The length-range generator -/

/-- The increasing range generator on `{n : ℕ // a ≤ n ∧ n < b}` (Malachite
`primitive_int_increasing_range` as a length iterator): `a, a + 1, …, b - 1`,
then exhausted; `a ≥ b` gives the empty generator. -/
@[reducible] def natRangeGen (a b : ℕ) : ExhaustiveGenerator {n : ℕ // a ≤ n ∧ n < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b - a)
    (fun i h => ⟨a + i, Nat.le_add_right a i, by omega⟩)
    (fun i j _ _ hij => by
      have h2 : a + i = a + j := congrArg Subtype.val hij
      omega)
    (fun t => ⟨t.val - a, by have := t.property; omega, by
      apply Subtype.ext
      have := t.property
      show a + (t.val - a) = t.val
      omega⟩)

/-- `natRangeGen` is finite with `card = b - a`. -/
@[reducible] def natRangeGen_finiteGenerator (a b : ℕ) :
    @FiniteGenerator _ (natRangeGen a b) :=
  .ofBoundedBijOn (natRangeGen a b) (b - a) rfl

theorem natRangeGen_contigStep (a b : ℕ) :
    ∀ n, (natRangeGen a b).gen n = none → (natRangeGen a b).gen (n + 1) = none := by
  intro n h
  by_cases hn : n < b - a
  · rw [show (natRangeGen a b).gen n
        = some ⟨a + n, Nat.le_add_right a n, by omega⟩ from dif_pos hn] at h
    exact absurd h (Option.some_ne_none _)
  · exact dif_neg (by omega)

/-! ### Shortlex, lengths in `[a, b)` -/

namespace ExhaustiveGenerator

/-- Flatten a range-tagged lex vec to the list subtype. -/
@[reducible] def flattenShortlexRange {T : Type*} {a b : ℕ} :
    LexDepPair {n : ℕ // a ≤ n ∧ n < b} (fun n => LexVec T n.val)
      → {l : List T // a ≤ l.length ∧ l.length < b} :=
  fun p => ⟨p.snd.val.toList, by rw [List.Vector.toList_length]; exact p.fst.property⟩

theorem flattenShortlexRange_bijective {T : Type*} {a b : ℕ} :
    Function.Bijective (flattenShortlexRange (T := T) (a := a) (b := b)) := by
  constructor
  · rintro ⟨⟨n, hn⟩, ⟨v⟩⟩ ⟨⟨m, hm⟩, ⟨w⟩⟩ h
    have hl : v.toList = w.toList := congrArg Subtype.val h
    have hnm : n = m := by
      have := congrArg List.length hl
      rwa [v.toList_length, w.toList_length] at this
    subst hnm
    rw [List.Vector.eq v w hl]
  · rintro ⟨l, hl⟩
    exact ⟨⟨⟨l.length, hl⟩, ⟨⟨l, rfl⟩⟩⟩, rfl⟩

/-- **Shortlex vecs with lengths in `[a, b)`** (Malachite
`shortlex_vecs_length_range`): every length-`a` vec lexicographically, then
length `a + 1`, …, through `b - 1`, then exhausted. -/
@[reducible] def shortlexVecsLengthRange {T : Type*} (a b : ℕ)
    (g : ExhaustiveGenerator T) {cT : ℕ} (hpos : 0 < cT)
    (hnone : ∀ k, cT ≤ k → g.gen k = none)
    (hsome : ∀ k, k < cT → g.gen k ≠ none) :
    ExhaustiveGenerator {l : List T // a ≤ l.length ∧ l.length < b} :=
  mapGen flattenShortlexRange flattenShortlexRange_bijective
    (lexDepPairGen (natRangeGen a b)
      (fun n => DepFinGen.ofBounded (lexVecData g hnone hsome n.val).gen
        (pow_pos hpos n.val)
        (lexVecData g hnone hsome n.val).hnone
        (lexVecData g hnone hsome n.val).hsome)
      (natRangeGen_contigStep a b))

/-! ### Fair, lengths in `[a, b)` -/

/-- Flatten a range-tagged vec to the list subtype (Σ form). -/
@[reducible] def flattenVecRange {T : Type*} {a b : ℕ} :
    ((n : {n : ℕ // a ≤ n ∧ n < b}) × List.Vector T n.val)
      → {l : List T // a ≤ l.length ∧ l.length < b} :=
  fun p => ⟨p.2.toList, by rw [List.Vector.toList_length]; exact p.1.property⟩

theorem flattenVecRange_bijective {T : Type*} {a b : ℕ} :
    Function.Bijective (flattenVecRange (T := T) (a := a) (b := b)) := by
  constructor
  · rintro ⟨⟨n, hn⟩, v⟩ ⟨⟨m, hm⟩, w⟩ h
    have hl : v.toList = w.toList := congrArg Subtype.val h
    have hnm : n = m := by
      have := congrArg List.length hl
      rwa [v.toList_length, w.toList_length] at this
    subst hnm
    rw [List.Vector.eq v w hl]
  · rintro ⟨l, hl⟩
    exact ⟨⟨⟨l.length, hl⟩, ⟨l, rfl⟩⟩, rfl⟩

/-- **Fair vecs with lengths in `[a, b)`** (Malachite
`exhaustive_vecs_length_range`): the fair dependent pair of the length range
and the fair fixed-length vecs — the bounded-degree polynomial shape
(coefficient lists of length `< b` are the polynomials of degree
`< b - 1`). -/
@[reducible] def exhaustiveVecsLengthRange {T : Type*} (a b : ℕ)
    (gV : (n : ℕ) → ExhaustiveGenerator (List.Vector T n)) :
    ExhaustiveGenerator {l : List T // a ≤ l.length ∧ l.length < b} :=
  mapGen flattenVecRange flattenVecRange_bijective
    (exhaustiveDepPairGen rulerSequence exists_le_and_rulerSequence_eq
      (natRangeGen a b) (fun n => gV n.val))

end ExhaustiveGenerator

/-! ### Guards

The shortlex doctest replays VERBATIM (a finite first component is native to
the lexicographic dependent pair — no order divergence). For the fair one we
pin OUR order and replay Malachite's doctest VERBATIM through the Rust-exact
simulator (the finite length iterator makes the Rust machine wrap its
scheduler modulo the live count — the `remove`/`%=` semantics the clean port
renders as holes). The last guards are the requested use: bounded-degree
polynomial coefficient streams over `AzZMod 3`. -/

open ExhaustiveGenerator

-- Malachite's `shortlex_vecs_length_range(2, 4, exhaustive_bools())`
-- doctest, verbatim — 12 values (`2^2 + 2^3`), then exhausted.
#guard (@firstN _ (shortlexVecsLengthRange 2 4 boolsGen FiniteGenerator.card_pos
      FiniteGenerator.gen_none FiniteGenerator.gen_some) 20).map (·.val)
  = [[false, false], [false, true], [true, false], [true, true],
     [false, false, false], [false, false, true], [false, true, false], [false, true, true],
     [true, false, false], [true, false, true], [true, true, false], [true, true, true]]
#guard (@firstN _ (shortlexVecsLengthRange 2 4 boolsGen FiniteGenerator.card_pos
      FiniteGenerator.gen_none FiniteGenerator.gen_some) 20).length == 12

-- The empty range (`a ≥ b`) produces nothing (Malachite's `a > b` clamp).
#guard (@firstN _ (shortlexVecsLengthRange 3 3 boolsGen FiniteGenerator.card_pos
      FiniteGenerator.gen_none FiniteGenerator.gen_some) 5).length == 0

-- Our fair order over `AzNat` elements, lengths in `[2, 4)`: absolute
-- slots — scheduler values `≥ 2` are holes past the exhausted range.
#guard ((List.range 40).filterMap
    ((exhaustiveVecsLengthRange 2 4 (fun n =>
      (inferInstance : ExhaustiveGenerator (List.Vector AzNat n)))).gen)).map
    (fun l => l.val.map (·.toNat))
  = [[0, 0], [0, 0, 0], [0, 1], [1, 0], [0, 0, 1], [1, 1], [0, 2], [0, 1, 0],
     [0, 3], [1, 2], [0, 1, 1], [1, 3], [2, 0], [1, 0, 0], [2, 1], [3, 0],
     [1, 0, 1], [3, 1], [2, 2], [1, 1, 0], [2, 3], [3, 2], [1, 1, 1], [3, 3],
     [0, 4], [0, 0, 2], [0, 5], [1, 4], [0, 0, 3], [1, 5]]

-- Malachite's `exhaustive_vecs_length_range(2, 4, exhaustive_unsigneds())`
-- doctest, VERBATIM through the Rust-exact simulator: the length iterator
-- `[2, 4)` exhausts after two pulls, and the scheduler wraps (`i %= 2`).
#guard (DepPairsSim.firstN (fun i => if i < 2 then some (2 + i) else none)
      (fun n j => (gen (T := List.Vector AzNat n) j).map (fun v => v.toList.map (·.toNat)))
      rulerSequence 0 20).map (·.2)
  = [[0, 0], [0, 0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 2], [0, 1, 0],
     [0, 3], [0, 1, 1], [1, 2], [1, 3], [2, 0], [1, 0, 0], [2, 1], [3, 0],
     [3, 1], [1, 0, 1], [2, 2], [2, 3]]

-- THE REQUESTED SHAPE: bounded-degree polynomials over `AzZMod 3` — all
-- coefficient lists of length `< 3` (degree `< 2`), enumerated fairly
-- through the finite rail; exactly `1 + 3 + 9 = 13` values, then exhausted.
#guard ((List.range 200).filterMap
    ((exhaustiveVecsLengthRange 0 3 (fun n =>
      (inferInstance : ExhaustiveGenerator (List.Vector (AzZMod (AzNat.ofNat 3)) n)))).gen)).map
    (fun l => l.val.map (·.val.toNat))
  = [[], [0], [0, 0], [1], [2], [0, 1], [1, 0], [1, 1], [0, 2], [1, 2],
     [2, 0], [2, 1], [2, 2]]
#guard ((List.range 200).filterMap
    ((exhaustiveVecsLengthRange 0 3 (fun n =>
      (inferInstance : ExhaustiveGenerator (List.Vector (AzZMod (AzNat.ofNat 3)) n)))).gen)).length
  == 13

end Azurite
