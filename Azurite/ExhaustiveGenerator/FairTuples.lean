/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `FairTuples` — FLAT fair triple and quadruple generators on the plain
  products `A × B × C` and `A × B × C × D` (Malachite
  `exhaustive_triples_from_single` / `exhaustive_quadruples_from_single`,
  generalized to heterogeneous components).

  WHY FLAT: resolving a bare `A × B × C` through the fair PAIR instance twice
  (`A × (B × C)`) gives component growth `O(√n), O(n^¼), O(n^¼)` — the first
  component takes every other counter bit and the inner pair splits the rest. A
  flat 3-slot round-robin interleave gives all three components balanced
  `O(n^⅓)` growth (and 4 slots all `O(n^¼)`), which is the fairness the
  enumeration exists to provide. These instances therefore OVERRIDE the
  nested-pair resolution on bare right-nested products, by instance priority:
  quadruple (1200) > triple (1100) > pair (default 1000). A bare right-nested
  product resolves at MAXIMAL flat width — e.g. a 5-tuple `A × B × C × D × E`
  resolves as the flat quadruple over `A, B, C, (D × E)` with the last slot a
  fair pair. Extending to flat arity 5+ later is mechanical (a `roundRobin 5`
  assignment and an instance at priority 1300, and so on).

  All components must currently be INFINITE (`[Contiguous] + [Infinite]`, the
  never-runs-out witnesses coming from `gen_ne_none_of_infinite`); finite
  components arrive with the capped assignment sibling in a later chunk.

  Slot `j` = the `j`-th component: slot 0 is the FIRST component (highest bit
  offset `m - 1`), the LAST slot owns the least-significant counter bit —
  matching Malachite's Z-order tuple doctests.
-/
import Azurite.ExhaustiveGenerator.FairPairs

namespace Azurite

/-- The 3-slot weight-1 round-robin bit assignment underlying the fair triple
generator: slot 0 (the FIRST component) owns the counter bits at offset 2
(`≡ 2 mod 3`), slot 2 (the LAST) the bits at offset 0 — Malachite's
`BitDistributor` `[normal(1); 3]`. -/
def fairTripleAssignment : BitAssignment 3 := roundRobin 3 (by omega)

/-- The 4-slot weight-1 round-robin bit assignment underlying the fair
quadruple generator: slot `j` owns the counter bits at offset `3 - j` —
Malachite's `BitDistributor` `[normal(1); 4]`. -/
def fairQuadrupleAssignment : BitAssignment 4 := roundRobin 4 (by omega)

namespace ExhaustiveGenerator

/-- **The assignment-generic fair triple generator.** Given ANY 3-slot
`BitAssignment P` and three generators that never run out (`hA`/`hB`/`hC` —
`Prop`-level, so computability is unaffected), enumerate the PLAIN product
`A × B × C`: position `k`'s bits are deinterleaved by `P` into the three
component indices. Exactly-once composes `deinterleaveTuple_bijective`'s
round-trips with the components' `occurs_exactly_once`: the unique index of
`(a, b, c)` is `P.interleave ![idx a, idx b, idx c]`. Specialized by
`fairTripleGen` (weight-1, all components `~k^⅓`) and
`fairTripleGenWeighted` in `FairWeighted` (component `j` grows
`~k^(w j / ∑ w)`). -/
@[reducible] def fairTripleGenWith {A B C : Type*} (P : BitAssignment 3)
    (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C) where
  gen k := some
    ((gA.gen (P.deinterleave 0 k)).get
        (Option.isSome_iff_ne_none.mpr (hA _)),
     (gB.gen (P.deinterleave 1 k)).get
        (Option.isSome_iff_ne_none.mpr (hB _)),
     (gC.gen (P.deinterleave 2 k)).get
        (Option.isSome_iff_ne_none.mpr (hC _)))
  occurs_exactly_once := by
    rintro ⟨a, b, c⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    obtain ⟨iC, hiC, huC⟩ := gC.occurs_exactly_once c
    refine ⟨P.interleave ![iA, iB, iC], ?_, ?_⟩
    · -- Existence: `deinterleave_interleave` decodes the witness back to the indices.
      have hga : gA.gen (P.deinterleave 0
          (P.interleave ![iA, iB, iC])) = some a := by
        rw [P.deinterleave_interleave ![iA, iB, iC] 0]
        exact hiA
      have hgb : gB.gen (P.deinterleave 1
          (P.interleave ![iA, iB, iC])) = some b := by
        rw [P.deinterleave_interleave ![iA, iB, iC] 1]
        exact hiB
      have hgc : gC.gen (P.deinterleave 2
          (P.interleave ![iA, iB, iC])) = some c := by
        rw [P.deinterleave_interleave ![iA, iB, iC] 2]
        exact hiC
      beta_reduce
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨Option.some.inj ((Option.some_get _).trans hga),
        Option.some.inj ((Option.some_get _).trans hgb),
        Option.some.inj ((Option.some_get _).trans hgc)⟩
    · -- Uniqueness: any producing position `m` has its deinterleaved components
      -- pinned by the components' uniqueness, so `interleave_deinterleave` pins `m`.
      intro m hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨hma, hmb, hmc⟩ := hm
      have hga : gA.gen (P.deinterleave 0 m) = some a := by
        rw [← hma]
        exact (Option.some_get _).symm
      have hgb : gB.gen (P.deinterleave 1 m) = some b := by
        rw [← hmb]
        exact (Option.some_get _).symm
      have hgc : gC.gen (P.deinterleave 2 m) = some c := by
        rw [← hmc]
        exact (Option.some_get _).symm
      have htup : P.deinterleaveTuple m = ![iA, iB, iC] := by
        funext j
        match j with
        | ⟨0, _⟩ => exact huA _ hga
        | ⟨1, _⟩ => exact huB _ hgb
        | ⟨2, _⟩ => exact huC _ hgc
      calc m = P.interleave (P.deinterleaveTuple m) :=
            (P.interleave_deinterleave m).symm
        _ = P.interleave ![iA, iB, iC] := by rw [htup]

/-- **The fair triple generator (builder form).** `fairTripleGenWith` at the
weight-1 round-robin `fairTripleAssignment`: all three components grow like
`k^⅓` (a FLAT 3-way split, not the unbalanced pair-of-pair nesting) —
Malachite's `exhaustive_triples`. -/
@[reducible] def fairTripleGen {A B C : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C) :=
  fairTripleGenWith fairTripleAssignment gA gB gC hA hB hC

/-- **The assignment-generic fair quadruple generator.** The 4-slot analogue
of `fairTripleGenWith`: position `k`'s bits are deinterleaved by an arbitrary
`BitAssignment 4` into the four component indices. The unique index of
`(a, b, c, d)` is `P.interleave ![idx a, idx b, idx c, idx d]`. Specialized by
`fairQuadrupleGen` (weight-1, all components `~k^¼`) and
`fairQuadrupleGenWeighted` in `FairWeighted`. -/
@[reducible] def fairQuadrupleGenWith {A B C D : Type*} (P : BitAssignment 4)
    (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C) (gD : ExhaustiveGenerator D)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C × D) where
  gen k := some
    ((gA.gen (P.deinterleave 0 k)).get
        (Option.isSome_iff_ne_none.mpr (hA _)),
     (gB.gen (P.deinterleave 1 k)).get
        (Option.isSome_iff_ne_none.mpr (hB _)),
     (gC.gen (P.deinterleave 2 k)).get
        (Option.isSome_iff_ne_none.mpr (hC _)),
     (gD.gen (P.deinterleave 3 k)).get
        (Option.isSome_iff_ne_none.mpr (hD _)))
  occurs_exactly_once := by
    rintro ⟨a, b, c, d⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    obtain ⟨iC, hiC, huC⟩ := gC.occurs_exactly_once c
    obtain ⟨iD, hiD, huD⟩ := gD.occurs_exactly_once d
    refine ⟨P.interleave ![iA, iB, iC, iD], ?_, ?_⟩
    · -- Existence: `deinterleave_interleave` decodes the witness back to the indices.
      have hga : gA.gen (P.deinterleave 0
          (P.interleave ![iA, iB, iC, iD])) = some a := by
        rw [P.deinterleave_interleave ![iA, iB, iC, iD] 0]
        exact hiA
      have hgb : gB.gen (P.deinterleave 1
          (P.interleave ![iA, iB, iC, iD])) = some b := by
        rw [P.deinterleave_interleave ![iA, iB, iC, iD] 1]
        exact hiB
      have hgc : gC.gen (P.deinterleave 2
          (P.interleave ![iA, iB, iC, iD])) = some c := by
        rw [P.deinterleave_interleave ![iA, iB, iC, iD] 2]
        exact hiC
      have hgd : gD.gen (P.deinterleave 3
          (P.interleave ![iA, iB, iC, iD])) = some d := by
        rw [P.deinterleave_interleave ![iA, iB, iC, iD] 3]
        exact hiD
      beta_reduce
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨Option.some.inj ((Option.some_get _).trans hga),
        Option.some.inj ((Option.some_get _).trans hgb),
        Option.some.inj ((Option.some_get _).trans hgc),
        Option.some.inj ((Option.some_get _).trans hgd)⟩
    · -- Uniqueness: pin each deinterleaved component, then `interleave_deinterleave`.
      intro m hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨hma, hmb, hmc, hmd⟩ := hm
      have hga : gA.gen (P.deinterleave 0 m) = some a := by
        rw [← hma]
        exact (Option.some_get _).symm
      have hgb : gB.gen (P.deinterleave 1 m) = some b := by
        rw [← hmb]
        exact (Option.some_get _).symm
      have hgc : gC.gen (P.deinterleave 2 m) = some c := by
        rw [← hmc]
        exact (Option.some_get _).symm
      have hgd : gD.gen (P.deinterleave 3 m) = some d := by
        rw [← hmd]
        exact (Option.some_get _).symm
      have htup : P.deinterleaveTuple m = ![iA, iB, iC, iD] := by
        funext j
        match j with
        | ⟨0, _⟩ => exact huA _ hga
        | ⟨1, _⟩ => exact huB _ hgb
        | ⟨2, _⟩ => exact huC _ hgc
        | ⟨3, _⟩ => exact huD _ hgd
      calc m = P.interleave
              (P.deinterleaveTuple m) :=
            (P.interleave_deinterleave m).symm
        _ = P.interleave ![iA, iB, iC, iD] := by rw [htup]

/-- **The fair quadruple generator (builder form).** `fairQuadrupleGenWith` at
the weight-1 round-robin `fairQuadrupleAssignment`: all four components grow
like `k^¼` — Malachite's `exhaustive_quadruples`. -/
@[reducible] def fairQuadrupleGen {A B C D : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C) (gD : ExhaustiveGenerator D)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none) :
    ExhaustiveGenerator (A × B × C × D) :=
  fairQuadrupleGenWith fairQuadrupleAssignment gA gB gC gD hA hB hC hD

end ExhaustiveGenerator

/-! ### The flat instances (priorities: quadruple 1200 > triple 1100 > pair 1000)

Higher-priority instances are tried first, so a bare right-nested product
resolves at MAXIMAL flat width: `A × B × C × D` hits the flat quadruple (not
the triple with `C × D` fused, nor the pair twice), `A × B × C` hits the flat
triple, and only a genuine 2-product falls through to the fair pair. A 5-tuple
`A × B × C × D × E` resolves as the flat quadruple over `A, B, C, (D × E)`
(its last slot a fair pair) — flat arity 5+ is a mechanical later extension.
The matching `Contiguous` instances carry the same priorities so they resolve
against the same `ExhaustiveGenerator` instance. -/

open ExhaustiveGenerator in
/-- **The flat fair `ExhaustiveGenerator (A × B × C)` instance** for three
infinite contiguous components: `fairTripleGen` with the never-`none` witnesses
supplied by `gen_ne_none_of_infinite`. Priority 1100 beats the fair pair
(default 1000), so a bare `A × B × C` gets the balanced flat 3-way interleave
rather than the unbalanced pair-of-pair nesting. -/
instance (priority := 1100) instExhaustiveGeneratorProd3 {A B C : Type*}
    [ExhaustiveGenerator A] [Contiguous A] [Infinite A]
    [ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [ExhaustiveGenerator C] [Contiguous C] [Infinite C] :
    ExhaustiveGenerator (A × B × C) :=
  fairTripleGen inferInstance inferInstance inferInstance
    gen_ne_none_of_infinite gen_ne_none_of_infinite gen_ne_none_of_infinite

open ExhaustiveGenerator in
/-- The fair triple generator is always-`some`, hence vacuously contiguous. -/
instance (priority := 1100) instContiguousProd3 {A B C : Type*}
    [ExhaustiveGenerator A] [Contiguous A] [Infinite A]
    [ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [ExhaustiveGenerator C] [Contiguous C] [Infinite C] :
    Contiguous (A × B × C) :=
  contiguous_of_gen_some instExhaustiveGeneratorProd3 rfl

open ExhaustiveGenerator in
/-- **The flat fair `ExhaustiveGenerator (A × B × C × D)` instance** for four
infinite contiguous components. Priority 1200 beats the flat triple (1100) and
the fair pair (1000), so a bare `A × B × C × D` gets the balanced flat 4-way
interleave. -/
instance (priority := 1200) instExhaustiveGeneratorProd4 {A B C D : Type*}
    [ExhaustiveGenerator A] [Contiguous A] [Infinite A]
    [ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [ExhaustiveGenerator C] [Contiguous C] [Infinite C]
    [ExhaustiveGenerator D] [Contiguous D] [Infinite D] :
    ExhaustiveGenerator (A × B × C × D) :=
  fairQuadrupleGen inferInstance inferInstance inferInstance inferInstance
    gen_ne_none_of_infinite gen_ne_none_of_infinite
    gen_ne_none_of_infinite gen_ne_none_of_infinite

open ExhaustiveGenerator in
/-- The fair quadruple generator is always-`some`, hence vacuously contiguous. -/
instance (priority := 1200) instContiguousProd4 {A B C D : Type*}
    [ExhaustiveGenerator A] [Contiguous A] [Infinite A]
    [ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [ExhaustiveGenerator C] [Contiguous C] [Infinite C]
    [ExhaustiveGenerator D] [Contiguous D] [Infinite D] :
    Contiguous (A × B × C × D) :=
  contiguous_of_gen_some instExhaustiveGeneratorProd4 rfl

/-! ### Guards

The exact Malachite `exhaustive_triples_from_single` test sequence (20 terms),
now at the PLAIN-product level (instance-resolved). The 3-way Z-order is
visible: the first 8 terms count in binary with one bit per component (slot 0
= FIRST component owns the highest offset). -/

open ExhaustiveGenerator

-- Malachite `exhaustive_triples_from_single` (test sequence, 20 terms). This
-- guard is ALSO the priority check: nested pair-of-pair resolution of
-- `A × (B × C)` would give `(1, 0, 0)` at index 2 and `(0, 1, 0)` at index 4
-- (swapped relative to the flat order below), and `(0, 0, 2)`/`(0, 2, 0)`
-- would trade places at indices 8 and 16.
#guard (firstN (AzNat × AzNat × AzNat) 20).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat))
  = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
     (0, 0, 2), (0, 0, 3), (0, 1, 2), (0, 1, 3), (1, 0, 2), (1, 0, 3), (1, 1, 2), (1, 1, 3),
     (0, 2, 0), (0, 2, 1), (0, 3, 0), (0, 3, 1)]

-- Explicit priority check: forcing the nested pair-of-pair instance on the
-- SAME type gives a DIFFERENT order — `(1, 0, 0)` at index 2, where the flat
-- instance (above) has `(0, 1, 0)`.
#guard ((instExhaustiveGeneratorProd (A := AzNat) (B := AzNat × AzNat)).gen 2).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (1, 0, 0)
#guard (gen (T := AzNat × AzNat × AzNat) 2).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (0, 1, 0)

-- Balance spot check: `k = 511 = 0b111111111` (9 set bits) splits as 3 bits
-- per slot, so all three components are `7 ≈ 511^⅓`.
#guard (gen (T := AzNat × AzNat × AzNat) 511).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (7, 7, 7)

-- Heterogeneous: `AzNat × AzInt × AzNat`, middle component in `integersGen`
-- order `0, 1, -1, 2, …`.
#guard (firstN (AzNat × AzInt × AzNat) 10).map
    (fun t => (t.1.toNat, t.2.1.toInt, t.2.2.toNat))
  = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
     (0, 0, 2), (0, 0, 3)]

-- Round-trip: the index of `(0, 2, 0)` computed via `interleave` is `16`,
-- exactly where the test sequence above finds it.
#guard fairTripleAssignment.interleave ![0, 2, 0] == 16

-- Quadruples: the first 16 terms count in binary with one bit per component
-- (4-way Z-order, first component slowest).
#guard (firstN (AzNat × AzNat × AzNat × AzNat) 16).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.1.toNat, t.2.2.2.toNat))
  = [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1),
     (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 1, 0), (0, 1, 1, 1),
     (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 0), (1, 0, 1, 1),
     (1, 1, 0, 0), (1, 1, 0, 1), (1, 1, 1, 0), (1, 1, 1, 1)]

-- Quadruple balance spot check: `k = 65535 = 0b1111111111111111` (16 set bits)
-- splits as 4 bits per slot, so all four components are `15 ≈ 65535^¼`.
#guard (gen (T := AzNat × AzNat × AzNat × AzNat) 65535).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.1.toNat, t.2.2.2.toNat)) = some (15, 15, 15, 15)

end Azurite
