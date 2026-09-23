/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `FairWeighted` — WEIGHTED fair pair/triple/quadruple builders on the plain
  products (Malachite `exhaustive_pairs_custom_output` etc.: a `BitDistributor`
  with `normal(w)` output types).

  The weights are USE-SITE parameters — a caller picks how fast each component
  should grow — so these are BUILDERS, not instances (the default instances
  stay the balanced weight-1 `FairPairs`/`FairTuples` ones). Each builder is
  the assignment-generic `fairPairGenWith`/`fairTripleGenWith`/
  `fairQuadrupleGenWith` applied to a `weightedRoundRobin` assignment: weights
  `(p, q)` make the components of a pair grow like `k^(p/(p+q))` and
  `k^(q/(p+q))` in the position `k` (weight-1 everywhere recovers the plain
  fair builders — `weightedRoundRobin_one_*`).

  This completes the planned BitDistributor port surface (chunks 1–5: the
  abstract assignment + weight-1 round-robin, the fair pair/tuple/vec
  instances, the capped assignment + finite components, hole compression, and
  the weighted assignment + these builders). TINY output types have since
  landed as the `tinyAssignment` instance in `BitInterleaveTiny` (with
  `fairPairGenTinyFirst`/`fairPairGenTinySecond` builders there). Flagged
  extensions that remain: the fast rank/unrank for deep compressed positions
  (4d) and WEIGHTED + CAPPED combined (a future `CappedBitAssignment` instance
  with weighted rounds) — see the scope notes in `BitInterleaveWeighted`.
-/
import Azurite.ExhaustiveGenerator.BitInterleaveWeighted
import Azurite.ExhaustiveGenerator.FairTuples

namespace Azurite

/-- The weighted 2-slot assignment `weightedRoundRobin ![wA, wB]`: within each
period of `wA + wB` counter bits, the SECOND component takes the `wB`
least-significant bits, then the first takes `wA`. -/
def fairPairAssignmentWeighted (wA wB : ℕ) (hA : 0 < wA) (hB : 0 < wB) :
    BitAssignment 2 :=
  weightedRoundRobin ![wA, wB] (by omega) (fun j => match j with
    | ⟨0, _⟩ => hA
    | ⟨1, _⟩ => hB)

/-- The weighted 3-slot assignment `weightedRoundRobin ![wA, wB, wC]`. -/
def fairTripleAssignmentWeighted (wA wB wC : ℕ)
    (hA : 0 < wA) (hB : 0 < wB) (hC : 0 < wC) : BitAssignment 3 :=
  weightedRoundRobin ![wA, wB, wC] (by omega) (fun j => match j with
    | ⟨0, _⟩ => hA
    | ⟨1, _⟩ => hB
    | ⟨2, _⟩ => hC)

/-- The weighted 4-slot assignment `weightedRoundRobin ![wA, wB, wC, wD]`. -/
def fairQuadrupleAssignmentWeighted (wA wB wC wD : ℕ)
    (hA : 0 < wA) (hB : 0 < wB) (hC : 0 < wC) (hD : 0 < wD) : BitAssignment 4 :=
  weightedRoundRobin ![wA, wB, wC, wD] (by omega) (fun j => match j with
    | ⟨0, _⟩ => hA
    | ⟨1, _⟩ => hB
    | ⟨2, _⟩ => hC
    | ⟨3, _⟩ => hD)

namespace ExhaustiveGenerator

/-- **The weighted fair pair generator.** `fairPairGenWith` at
`weightedRoundRobin ![wA, wB]`: the first component's index grows like
`k^(wA/(wA+wB))` and the second's like `k^(wB/(wA+wB))` — e.g. weights
`(1, 2)` give a `~k^⅓`/`~k^⅔` split. Exactly-once and computability are
inherited from the generic builder; the weights only choose the
`BitAssignment`. -/
@[reducible] def fairPairGenWeighted {A B : Type*} (wA wB : ℕ)
    (hwA : 0 < wA) (hwB : 0 < wB)
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) :
    ExhaustiveGenerator (A × B) :=
  fairPairGenWith (fairPairAssignmentWeighted wA wB hwA hwB) gA gB hA hB

/-- **The weighted fair triple generator.** `fairTripleGenWith` at
`weightedRoundRobin ![wA, wB, wC]`: component `j` grows like
`k^(w j / (wA+wB+wC))`. -/
@[reducible] def fairTripleGenWeighted {A B C : Type*} (wA wB wC : ℕ)
    (hwA : 0 < wA) (hwB : 0 < wB) (hwC : 0 < wC)
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C) :=
  fairTripleGenWith (fairTripleAssignmentWeighted wA wB wC hwA hwB hwC) gA gB gC hA hB hC

/-- **The weighted fair quadruple generator.** `fairQuadrupleGenWith` at
`weightedRoundRobin ![wA, wB, wC, wD]`: component `j` grows like
`k^(w j / (wA+wB+wC+wD))`. -/
@[reducible] def fairQuadrupleGenWeighted {A B C D : Type*} (wA wB wC wD : ℕ)
    (hwA : 0 < wA) (hwB : 0 < wB) (hwC : 0 < wC) (hwD : 0 < wD)
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (gC : ExhaustiveGenerator C) (gD : ExhaustiveGenerator D)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C × D) :=
  fairQuadrupleGenWith (fairQuadrupleAssignmentWeighted wA wB wC wD hwA hwB hwC hwD)
    gA gB gC gD hA hB hC hD

end ExhaustiveGenerator

/-! ### Guards (Malachite fidelity)

Weights `(1, 2)` over `AzNat × AzNat`: slot 0 owns one of every 3 counter
bits (positions `≡ 2 mod 3`), slot 1 the other two — the second component
gets 2 bits per period and grows like `k^⅔`, the first like `k^⅓`. The
12-pair prefix is hand-derived from the bit map: `y` counts through `0..3`
(2 bits) before `x` gets its first bit at counter bit 2. -/

open ExhaustiveGenerator

#guard ((List.range 12).filterMap
    (fairPairGenWeighted 1 2 (by omega) (by omega) naturalsGen naturalsGen
      gen_ne_none_of_infinite gen_ne_none_of_infinite).gen).map
    (fun p => (p.1.toNat, p.2.toNat))
  == [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
      (0, 4), (0, 5), (0, 6), (0, 7)]

-- Swapped weights `(2, 1)`: the FIRST component now takes 2 of every 3 bits.
#guard ((List.range 12).filterMap
    (fairPairGenWeighted 2 1 (by omega) (by omega) naturalsGen naturalsGen
      gen_ne_none_of_infinite gen_ne_none_of_infinite).gen).map
    (fun p => (p.1.toNat, p.2.toNat))
  == [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1),
      (0, 2), (0, 3), (1, 2), (1, 3)]

-- Deep imbalance spot checks for weights `(1, 2)`: `k = 63 = 0b111111` has
-- slot 0 owning bits 2, 5 (`x = 3 ≈ 63^⅓`) and slot 1 owning bits 0, 1, 3, 4
-- (`y = 15 ≈ 63^⅔`); `k = 100 = 0b1100100` has slot-0 bits 2, 5 set (`x = 3`)
-- and slot-1 bit 6 set at rank 4 (`y = 16`).
#guard ((fairPairGenWeighted 1 2 (by omega) (by omega) naturalsGen naturalsGen
    gen_ne_none_of_infinite gen_ne_none_of_infinite).gen 63).map
    (fun p => (p.1.toNat, p.2.toNat)) = some (3, 15)
#guard ((fairPairGenWeighted 1 2 (by omega) (by omega) naturalsGen naturalsGen
    gen_ne_none_of_infinite gen_ne_none_of_infinite).gen 100).map
    (fun p => (p.1.toNat, p.2.toNat)) = some (3, 16)

-- Weighted triple `(1, 1, 2)`: the LAST slot owns the 2 low bits of each
-- 4-bit period, so the third component counts through `0..3` first.
#guard ((List.range 12).filterMap
    (fairTripleGenWeighted 1 1 2 (by omega) (by omega) (by omega)
      naturalsGen naturalsGen naturalsGen
      gen_ne_none_of_infinite gen_ne_none_of_infinite gen_ne_none_of_infinite).gen).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat))
  == [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3),
      (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 3)]
#guard ((fairTripleGenWeighted 1 1 2 (by omega) (by omega) (by omega)
    naturalsGen naturalsGen naturalsGen
    gen_ne_none_of_infinite gen_ne_none_of_infinite gen_ne_none_of_infinite).gen 63).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (1, 1, 15)

-- Round-trip: the `interleave`-computed index of `(1, 4)` under weights
-- `(1, 2)` is `12`, matching the prefix continuation `gen 12 = (1, 4)`.
#guard (fairPairAssignmentWeighted 1 2 (by omega) (by omega)).interleave ![1, 4] == 12
#guard ((fairPairGenWeighted 1 2 (by omega) (by omega) naturalsGen naturalsGen
    gen_ne_none_of_infinite gen_ne_none_of_infinite).gen 12).map
    (fun p => (p.1.toNat, p.2.toNat)) = some (1, 4)

end Azurite
