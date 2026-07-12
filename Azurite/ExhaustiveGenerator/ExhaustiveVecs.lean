/-
  `exhaustive_vecs` — all vecs of every length, fairly (Malachite
  `exhaustive_vecs` / `exhaustive_vecs_from_length_iterator`).

  Malachite's `ExhaustiveVecs` IS `ExhaustiveDependentPairs<u64, Vec<T>,
  RulerSequence, …>` projected to the second coordinate: lengths
  `0, 1, 2, …` as the first component, the FAIR fixed-length vecs of each
  length as the fibers, ruler-scheduled. The port is that composition
  verbatim: `exhaustiveDepPairGen` over `lengthsGen` with fibers the fair
  `List.Vector T n` instances, flattened along the bijection
  `⟨n, v⟩ ↦ v.toList` onto the bare `List T` — which the fair enumeration
  OWNS (shortlex order lives on the `ShortlexVec` newtype).

  **The length-`0` fiber is FINITE** — the single empty vec, then `none` —
  so this is the first composition exercising `exhaustiveDepPairGen`'s
  finite-fiber (hole) case: the ruler scheduler revisits slot `0` at every
  even step, and every visit past the first is a hole (counters
  `2, 4, 6, …` are `none`). For finite `T`, EVERY fiber is finite (`cT ^ n`
  values) and the stream is hole-dense; the fiber instances then come from
  the capped rail. Both rails enter through the single instance gate
  `[∀ n, ExhaustiveGenerator (List.Vector T n)]`.

  FIDELITY: per-fiber subsequences match the Rust stream exactly — both
  pull each length's fair enumeration sequentially, and the guards pin our
  per-length subsequences against the Rust doctest's. The INTERLEAVING
  differs from step `2` on: when the length-`0` iterator exhausts, the Rust
  REMOVES it and every scheduler index shifts down (its third output is
  `[1]`, the shifted slot; ours is a hole, then `[0, 0]`) — the stateful
  re-targeting already documented in `ExhaustiveDepPairs.lean`. Same
  every-vec-exactly-once guarantee, provably (`occurs_exactly_once`) rather
  than dynamically.

  `exhaustiveVecsFromLengthGen` keeps the length generator (and scheduler)
  generic — Malachite's `exhaustive_vecs_from_length_iterator`, restricted
  to honest length GENERATORS (the Rust accepts arbitrary, possibly
  repeating, length iterators and then repeats vecs; an
  `ExhaustiveGenerator ℕ` first component rules that out, and flattening
  stays a bijection for any choice). `exhaustiveVecs` pins Malachite's
  defaults: lengths `0, 1, 2, …`, ruler-scheduled.
-/
import Azurite.ExhaustiveGenerator.ExhaustiveDepPairs
import Azurite.ExhaustiveGenerator.ShortlexVecs
import Azurite.ExhaustiveGenerator.FairVecs
import Azurite.ExhaustiveGenerator.FairCapped

namespace Azurite

namespace ExhaustiveGenerator

/-- Flatten a length-tagged vec to its underlying list: the computable
bijection `((n : ℕ) × List.Vector T n) → List T` (a list determines its
length, so dropping the tag loses nothing). -/
@[reducible] def flattenVec {T : Type*} : ((n : ℕ) × List.Vector T n) → List T :=
  fun p => p.2.toList

theorem flattenVec_bijective {T : Type*} :
    Function.Bijective (flattenVec (T := T)) := by
  constructor
  · -- Injective: the list determines the length, then the vec.
    rintro ⟨n, v⟩ ⟨m, w⟩ h
    have hl : v.toList = w.toList := h
    have hnm : n = m := by
      have := congrArg List.length hl
      rwa [v.toList_length, w.toList_length] at this
    subst hnm
    rw [List.Vector.eq v w hl]
  · -- Surjective: a list `l` is the flattening of `⟨l.length, ⟨l⟩⟩`.
    intro l
    exact ⟨⟨l.length, ⟨l, rfl⟩⟩, rfl⟩

/-- **All vecs from a length generator** (Malachite
`exhaustive_vecs_from_length_iterator`): the fair dependent pair of a length
generator and per-length vec generators, flattened onto `List T`. Generic
over the scheduler and the length generator (see the module header). -/
@[reducible] def exhaustiveVecsFromLengthGen {T : Type*}
    (s : ℕ → ℕ) (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i)
    (gLen : ExhaustiveGenerator ℕ)
    (gV : (n : ℕ) → ExhaustiveGenerator (List.Vector T n)) :
    ExhaustiveGenerator (List T) :=
  mapGen flattenVec flattenVec_bijective
    (exhaustiveDepPairGen s hs gLen gV)

/-- **The fair all-length vec generator** (Malachite `exhaustive_vecs`):
lengths `0, 1, 2, …`, ruler-scheduled, fibers the fair fixed-length vecs. -/
@[reducible] def exhaustiveVecs {T : Type*}
    (gV : (n : ℕ) → ExhaustiveGenerator (List.Vector T n)) :
    ExhaustiveGenerator (List T) :=
  exhaustiveVecsFromLengthGen rulerSequence exists_le_and_rulerSequence_eq
    lengthsGen gV

end ExhaustiveGenerator

open ExhaustiveGenerator

/-- Fair `ExhaustiveGenerator` on the bare `List T` (Malachite
`exhaustive_vecs`): shortest-biased fair enumeration of ALL lists. The fiber
gate resolves through either rail — the infinite-`T` fair vec instance or
the finite-`T` capped one. -/
instance instExhaustiveGeneratorList {T : Type*}
    [gV : ∀ n, ExhaustiveGenerator (List.Vector T n)] :
    ExhaustiveGenerator (List T) :=
  exhaustiveVecs fun n => gV n

/-! ### Guards

The interleaving is OURS (absolute slots with holes; the Rust re-targets its
scheduler after the length-`0` fiber exhausts — see the module header), so
the stream table pins our order. The per-length SUBSEQUENCES are where the
two agree step for step, and those guards are Malachite's `exhaustive_vecs`
doctest values verbatim. -/

-- Our stream over `AzNat`: 40 counters, 21 values (odd counters plus
-- counter `0`; every even counter past `0` revisits the exhausted
-- length-`0` fiber).
#guard ((List.range 40).filterMap (gen (T := List AzNat))).map (·.map (·.toNat))
  = [[], [0], [0, 0], [1], [0, 0, 0], [2], [0, 1], [3], [0, 0, 0, 0], [4], [1, 0], [5],
     [0, 0, 1], [6], [1, 1], [7], [0, 0, 0, 0, 0], [8], [0, 2], [9], [0, 1, 0]]

-- THE FINITE-FIBER HOLES (the length-`0` generator is finite): the single
-- empty vec arrives at counter `0`; every later visit to slot `0` is dead.
#guard (gen (T := List AzNat) 0) == some []
#guard (gen (T := List AzNat) 2).isNone
#guard (gen (T := List AzNat) 4).isNone
#guard (gen (T := List AzNat) 6).isNone
#guard ((List.range 40).filter fun n => (gen (T := List AzNat) n).isNone).length == 19

-- Per-length subsequences: the Rust doctest's fiber orders, verbatim
-- (its length-1 values in order, its length-2 values, its length-3 values).
#guard ((((List.range 120).filterMap (gen (T := List AzNat))).filter
      fun l => l.length == 1).map (·.map (·.toNat))).take 10
  = [[0], [1], [2], [3], [4], [5], [6], [7], [8], [9]]
#guard ((((List.range 120).filterMap (gen (T := List AzNat))).filter
      fun l => l.length == 2).map (·.map (·.toNat))).take 4
  = [[0, 0], [0, 1], [1, 0], [1, 1]]
#guard ((((List.range 120).filterMap (gen (T := List AzNat))).filter
      fun l => l.length == 3).map (·.map (·.toNat))).take 3
  = [[0, 0, 0], [0, 0, 1], [0, 1, 0]]

-- Occurs-once, concrete: a long prefix has no duplicates.
#guard ((List.range 200).filterMap (gen (T := List AzNat))).Nodup

-- The finite-`T` rail (`Ordering`, every fiber finite — capped instances):
-- all lengths keep arriving through the hole-dense stream.
#guard ((List.range 48).filterMap (gen (T := List Ordering)))
  = [[], [.lt], [.lt, .lt], [.eq], [.lt, .lt, .lt], [.gt], [.lt, .eq],
     [.lt, .lt, .lt, .lt], [.eq, .lt], [.lt, .lt, .eq], [.eq, .eq],
     [.lt, .lt, .lt, .lt, .lt], [.lt, .gt], [.lt, .eq, .lt], [.eq, .gt],
     [.lt, .lt, .lt, .eq]]

end Azurite
