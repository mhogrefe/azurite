/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `FairVecs` — the FAIR fixed-length vec generator on the PLAIN vector type
  `List.Vector T n` (Malachite `exhaustive_vecs_fixed_length_from_single`, all
  output types `normal(1)`).

  This is the polynomial-coefficients carrier: all length-`n` vecs over a
  single INFINITE component type `T`, every coordinate advancing at the same
  balanced `k^(1/n)` rate via the flat `n`-slot round-robin `BitAssignment`
  (slot `j` = coordinate `j`; slot 0 = the FIRST coordinate owns the highest
  bit offset, matching Malachite's Z-order doctests). The plain type carries
  the FAIR enumeration; the lexicographic enumeration lives on the `LexVec`
  newtype (`LexVecs.lean`), which also requires `T` finite — the two never
  clash.

  By cases on `n`: length `0` is the singleton generator (just the empty vec),
  and length `m + 1` is the flat `(m+1)`-way interleave, exactly-once via
  `deinterleaveTuple_bijective`'s round-trips + the component's uniqueness per
  coordinate. The component must currently be infinite
  (`[Contiguous] + [Infinite]`, never-runs-out via `gen_ne_none_of_infinite`);
  finite components arrive with the capped assignment sibling in a later chunk.
-/
import Azurite.ExhaustiveGenerator.FairPairs
import Mathlib.Data.Vector.Basic

namespace Azurite

/-- The `(m+1)`-slot weight-1 round-robin bit assignment underlying the fair
fixed-length vec generator: slot `j` (coordinate `j`) owns the counter bits at
offset `m - j`, so the FIRST coordinate owns the highest offset and the LAST
the least-significant bit — Malachite's `BitDistributor` `[normal(1); m+1]`. -/
def fairVecAssignment (m : ℕ) : BitAssignment (m + 1) := roundRobin (m + 1) (Nat.succ_pos m)

namespace ExhaustiveGenerator

/-- **The fair fixed-length vec generator (builder form, positive length).**
Given a component generator that never runs out (`h` — `Prop`-level, so
computability is unaffected), enumerate all length-`(m+1)` vecs over `T`
fairly: position `k`'s bits are deinterleaved by `fairVecAssignment m` into
the `m + 1` coordinate indices, so every coordinate grows like `k^(1/(m+1))`.
Exactly-once composes `deinterleaveTuple_bijective`'s round-trips with the
component's `occurs_exactly_once` per coordinate: the unique index of `v` is
`(fairVecAssignment m).interleave (fun j => idx (v.get j))`. -/
@[reducible] def fairVecGen {T : Type*} (g : ExhaustiveGenerator T)
    (h : ∀ n, g.gen n ≠ none) (m : ℕ) : ExhaustiveGenerator (List.Vector T (m + 1)) where
  gen k := some (List.Vector.ofFn fun j =>
    (g.gen ((fairVecAssignment m).deinterleave j k)).get
      (Option.isSome_iff_ne_none.mpr (h _)))
  occurs_exactly_once v := by
    -- One unique component index per coordinate.
    choose idx hidx huniq using fun j : Fin (m + 1) => g.occurs_exactly_once (v.get j)
    refine ⟨(fairVecAssignment m).interleave idx, ?_, ?_⟩
    · -- Existence: `deinterleave_interleave` decodes the witness back to `idx j`
      -- in every coordinate.
      beta_reduce
      rw [Option.some.injEq]
      apply List.Vector.ext
      intro j
      rw [List.Vector.get_ofFn]
      apply Option.some.inj
      rw [Option.some_get, (fairVecAssignment m).deinterleave_interleave idx j]
      exact hidx j
    · -- Uniqueness: any producing position `k` has every deinterleaved coordinate
      -- pinned by the component's uniqueness, so `interleave_deinterleave` pins `k`.
      intro k hk
      have hg : ∀ j, g.gen ((fairVecAssignment m).deinterleave j k) = some (v.get j) := by
        intro j
        have hj := congrArg (fun w => List.Vector.get w j) (Option.some.inj hk)
        simp only [List.Vector.get_ofFn] at hj
        rw [← hj, Option.some_get]
      have htup : (fairVecAssignment m).deinterleaveTuple k = idx :=
        funext fun j => huniq j _ (hg j)
      calc k = (fairVecAssignment m).interleave ((fairVecAssignment m).deinterleaveTuple k) :=
            ((fairVecAssignment m).interleave_deinterleave k).symm
        _ = (fairVecAssignment m).interleave idx := by rw [htup]

/-- The length-`0` vec generator: the single empty vec (`List.Vector.eq_nil`
supplies completeness). The degenerate base case of the fair fixed-length vec
instance; no component constraints are needed. -/
@[reducible] def fairVecGenZero (T : Type*) : ExhaustiveGenerator (List.Vector T 0) :=
  ofListNodup [List.Vector.nil] (by simp)
    (fun t => by rw [t.eq_nil]; exact List.mem_singleton_self _)

end ExhaustiveGenerator

open ExhaustiveGenerator in
/-- **The fair `ExhaustiveGenerator (List.Vector T n)` instance** for an
infinite contiguous component: by cases on `n`, the singleton empty-vec
generator at length `0` and the flat `n`-way `fairVecGen` (never-`none`
witness from `gen_ne_none_of_infinite`) at positive length. Lives on the PLAIN
vector type; the lexicographic enumeration stays on the `LexVec` newtype. -/
instance instExhaustiveGeneratorVector {T : Type*} [inst : ExhaustiveGenerator T]
    [Contiguous T] [Infinite T] : {n : ℕ} → ExhaustiveGenerator (List.Vector T n)
  | 0 => fairVecGenZero T
  | m + 1 => fairVecGen inst gen_ne_none_of_infinite m

open ExhaustiveGenerator in
/-- The fair fixed-length vec generator is contiguous: at length `0` it is
list-backed (`contiguous_of_getElem?`), at positive length always-`some`
(`contiguous_of_gen_some`). -/
instance instContiguousVector {T : Type*} [ExhaustiveGenerator T] [Contiguous T]
    [Infinite T] {n : ℕ} : Contiguous (List.Vector T n) := by
  match n with
  | 0 => exact contiguous_of_getElem? (instExhaustiveGeneratorVector (n := 0)) rfl
  | m + 1 => exact contiguous_of_gen_some (instExhaustiveGeneratorVector (n := m + 1)) rfl

open ExhaustiveGenerator in
/-- The length-`0` vec generator is finite with `card = 1` (the empty vec). -/
instance instFiniteGeneratorVectorZero {T : Type*} [ExhaustiveGenerator T] [Contiguous T]
    [Infinite T] : FiniteGenerator (List.Vector T 0) :=
  FiniteGenerator.ofListNodup (instExhaustiveGeneratorVector (n := 0)) 1 rfl rfl

/-- Positive-length vecs over an infinite type are infinite (the constant
vecs embed the element type), so vec components resolve through the
infinite rail in further compositions. -/
instance instInfiniteVector {T : Type*} [Infinite T] {n : ℕ} :
    Infinite (List.Vector T (n + 1)) :=
  Infinite.of_injective
    (fun t => (⟨List.replicate (n + 1) t, List.length_replicate⟩ : List.Vector T (n + 1)))
    (fun a b h => by
      have h2 : List.replicate (n + 1) a = List.replicate (n + 1) b :=
        congrArg Subtype.val h
      have h3 := congrArg List.head? h2
      rw [List.head?_replicate, List.head?_replicate] at h3
      simpa using h3)

/-! ### Guards

The exact Malachite `exhaustive_vecs_fixed_length_from_single` sequences,
rendered by `.toList`: length 2 replays the pairs table as lists, length 3 the
20-term fixed-length-vecs test sequence, length 0 the single empty vec, and
length 1 the component order. -/

open ExhaustiveGenerator

-- Length 2: the fair pairs table as lists (Malachite
-- `exhaustive_vecs_fixed_length_from_single(2, …)` doctest prefix).
#guard (firstN (List.Vector AzNat 2) 10).map (fun v => v.toList.map (·.toNat))
  = [[0, 0], [0, 1], [1, 0], [1, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1]]

-- Length 3: Malachite `exhaustive_vecs_fixed_length_from_single(3, …)` test
-- sequence (20 terms) — identical to the flat triples order.
#guard (firstN (List.Vector AzNat 3) 20).map (fun v => v.toList.map (·.toNat))
  = [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1],
     [0, 0, 2], [0, 0, 3], [0, 1, 2], [0, 1, 3], [1, 0, 2], [1, 0, 3], [1, 1, 2], [1, 1, 3],
     [0, 2, 0], [0, 2, 1], [0, 3, 0], [0, 3, 1]]

-- Length 0: the single empty vec (and the enumeration caps at 1).
#guard (firstN (List.Vector AzNat 0) 10).map (fun v => v.toList.map (·.toNat)) = [[]]
#guard (firstN (List.Vector AzNat 0) 10).length == 1

-- Length 1: the component order (`roundRobin 1` deinterleave is the identity).
#guard (firstN (List.Vector AzNat 1) 5).map (fun v => v.toList.map (·.toNat))
  = [[0], [1], [2], [3], [4]]

-- Balance spot check: `k = 511 = 0b111111111` (9 set bits) at length 3 splits
-- as 3 bits per coordinate, so all three coordinates are `7 ≈ 511^⅓`.
#guard (gen (T := List.Vector AzNat 3) 511).map (fun v => v.toList.map (·.toNat))
  = some [7, 7, 7]

end Azurite
