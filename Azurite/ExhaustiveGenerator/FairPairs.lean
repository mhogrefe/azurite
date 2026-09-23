/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `FairPairs` — the FAIR pair generator on the plain product `A × B`
  (Malachite `exhaustive_pairs`, the 2-way `BitDistributor` composition).

  Both components may be INFINITE: position `k`'s bits are split between the
  two components by the weight-1 round-robin `BitAssignment` (`BitInterleave`),
  so each component's index grows like `√k` — the enumeration is FAIR, unlike
  the lexicographic `LexPair` (which must cycle a finite last component). Slot
  0 is the FIRST component (bit offset 1), slot 1 the SECOND (bit offset 0),
  matching Malachite's Z-order pairs doctest.

  This is the DEFAULT `ExhaustiveGenerator (A × B)` instance for two infinite
  contiguous components; the lex generator deliberately lives on the newtype
  `LexPair A B` so the two never clash. The new lemma of substance is the
  infiniteness bridge `gen_ne_none_of_infinite`: a `Contiguous` generator on an
  `Infinite` type never runs out (pigeonhole via the unique index `Count.idx`),
  which is what lets `gen` return `some` unconditionally (`Option.get` on
  `Prop`-level witnesses — computability unaffected).

  NB bare triples and quadruples do NOT resolve through this instance twice:
  `FairTuples.lean` registers flat 3-way and 4-way instances at higher priority
  (1100/1200 vs this instance's default 1000), so `A × B × C` gets the
  balanced flat interleave; only a genuine 2-product falls through to here.
-/
import Azurite.ExhaustiveGenerator.Count
import Azurite.ExhaustiveGenerator.BitInterleave
import Mathlib.Data.Fintype.EquivFin

namespace Azurite

namespace ExhaustiveGenerator

variable {T : Type*}

/-- **The infiniteness bridge.** A `Contiguous` generator on an `Infinite` type
never runs out. Pigeonhole: a `none` at `n` propagates to every later position
(`gen_none_of_le`), so every value's unique index (`idx`) lies below `n`,
giving an injection `T ↪ Fin n` — contradicting `Infinite T`. This is the
witness that lets fair product generators `Option.get` their components'
outputs unconditionally. -/
theorem gen_ne_none_of_infinite [ExhaustiveGenerator T] [Contiguous T] [Infinite T] :
    ∀ n, gen (T := T) n ≠ none := by
  intro n h
  -- A `none` at `n` propagates to every later position.
  have hnone_ge : ∀ m, n ≤ m → gen (T := T) m = none := fun m hm => gen_none_of_le hm h
  -- Hence every value's index is `< n`, giving an injection `T ↪ Fin n`.
  let G : T → Fin n := fun t => ⟨idx t, by
    by_contra hge
    rw [Nat.not_lt] at hge
    exact Option.some_ne_none _ ((gen_idx t).symm.trans (hnone_ge (idx t) hge))⟩
  have hG : Function.Injective G := by
    intro a b hab
    have hidx : idx a = idx b := congrArg Fin.val hab
    have h1 := gen_idx a
    rw [hidx, gen_idx b] at h1
    exact (Option.some.inj h1).symm
  have : Finite T := Finite.of_injective G hG
  exact not_finite T

/-- `Option.get`-ready form of `gen_ne_none_of_infinite`: every position of a
contiguous generator on an infinite type `isSome`. -/
theorem gen_isSome_of_infinite [ExhaustiveGenerator T] [Contiguous T] [Infinite T] (n : ℕ) :
    (gen (T := T) n).isSome :=
  Option.isSome_iff_ne_none.mpr (gen_ne_none_of_infinite n)

end ExhaustiveGenerator

/-- The 2-slot weight-1 round-robin bit assignment underlying the fair pair
generator: slot 0 (the FIRST component) owns the odd counter bits (offset 1),
slot 1 (the SECOND) the even bits (offset 0) — Malachite's `BitDistributor`
`[normal(1); 2]`. -/
def fairPairAssignment : BitAssignment 2 := roundRobin 2 (by omega)

namespace ExhaustiveGenerator

/-- **The assignment-generic fair pair generator.** Given ANY 2-slot
`BitAssignment P` and two generators that never run out (`hA`/`hB` —
`Prop`-level, so computability is unaffected), enumerate the PLAIN product
`A × B`: position `k`'s bits are deinterleaved by `P` into the two component
indices. Exactly-once is the composition of `deinterleaveTuple_bijective`'s
round-trips with the two components' `occurs_exactly_once`: the unique index
of `(a, b)` is `P.interleave ![idx a, idx b]`. Specialized by `fairPairGen`
(weight-1 `fairPairAssignment`, both components `~√k`) and
`fairPairGenWeighted` in `FairWeighted` (weights `(p, q)`, components
`~k^(p/(p+q))` and `~k^(q/(p+q))`). -/
@[reducible] def fairPairGenWith {A B : Type*} (P : BitAssignment 2)
    (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) :
    ExhaustiveGenerator (A × B) where
  gen k := some
    ((gA.gen (P.deinterleave 0 k)).get
        (Option.isSome_iff_ne_none.mpr (hA _)),
     (gB.gen (P.deinterleave 1 k)).get
        (Option.isSome_iff_ne_none.mpr (hB _)))
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    refine ⟨P.interleave ![iA, iB], ?_, ?_⟩
    · -- Existence: `deinterleave_interleave` decodes the witness back to `(iA, iB)`.
      have hga : gA.gen (P.deinterleave 0
          (P.interleave ![iA, iB])) = some a := by
        rw [P.deinterleave_interleave ![iA, iB] 0]
        exact hiA
      have hgb : gB.gen (P.deinterleave 1
          (P.interleave ![iA, iB])) = some b := by
        rw [P.deinterleave_interleave ![iA, iB] 1]
        exact hiB
      beta_reduce
      rw [Option.some.injEq, Prod.mk.injEq]
      exact ⟨Option.some.inj ((Option.some_get _).trans hga),
        Option.some.inj ((Option.some_get _).trans hgb)⟩
    · -- Uniqueness: any producing position `m` has its deinterleaved components
      -- pinned by the components' uniqueness, so `interleave_deinterleave` pins `m`.
      intro m hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨hma, hmb⟩ := hm
      have hga : gA.gen (P.deinterleave 0 m) = some a := by
        rw [← hma]
        exact (Option.some_get _).symm
      have hgb : gB.gen (P.deinterleave 1 m) = some b := by
        rw [← hmb]
        exact (Option.some_get _).symm
      have htup : P.deinterleaveTuple m = ![iA, iB] := by
        funext j
        match j with
        | ⟨0, _⟩ => exact huA _ hga
        | ⟨1, _⟩ => exact huB _ hgb
      calc m = P.interleave (P.deinterleaveTuple m) :=
            (P.interleave_deinterleave m).symm
        _ = P.interleave ![iA, iB] := by rw [htup]

/-- **The fair pair generator (builder form).** `fairPairGenWith` at the
weight-1 round-robin `fairPairAssignment`: both components grow like `√k` —
Malachite's `exhaustive_pairs`. -/
@[reducible] def fairPairGen {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) :
    ExhaustiveGenerator (A × B) :=
  fairPairGenWith fairPairAssignment gA gB hA hB

end ExhaustiveGenerator

open ExhaustiveGenerator in
/-- **The default fair `ExhaustiveGenerator (A × B)` instance** for two
infinite contiguous components: `fairPairGen` with the never-`none` witnesses
supplied by the infiniteness bridge `gen_ne_none_of_infinite`. -/
instance instExhaustiveGeneratorProd {A B : Type*} [ExhaustiveGenerator A] [Contiguous A]
    [Infinite A] [ExhaustiveGenerator B] [Contiguous B] [Infinite B] :
    ExhaustiveGenerator (A × B) :=
  fairPairGen inferInstance inferInstance gen_ne_none_of_infinite gen_ne_none_of_infinite

open ExhaustiveGenerator in
/-- The fair pair generator is always-`some`, hence vacuously contiguous. -/
instance instContiguousProd {A B : Type*} [ExhaustiveGenerator A] [Contiguous A]
    [Infinite A] [ExhaustiveGenerator B] [Contiguous B] [Infinite B] :
    Contiguous (A × B) :=
  contiguous_of_gen_some instExhaustiveGeneratorProd rfl

/-! `Infinite (A × B)` is already ambient from Mathlib (`Prod.infinite_of_left`
with `Nonempty B` from `Infinite B`), so the fair pair can itself feed further
fair compositions. -/
example {A B : Type*} [Infinite A] [Infinite B] : Infinite (A × B) := inferInstance

/-! ### Guards

The exact Malachite `BitDistributor` pairs doctest, now at the PRODUCT level
(instance-resolved, no explicit builder arguments). Fairness is visible: over
the 10-pair prefix both components stay `≤ 3` (each grows like `√n`). -/

open ExhaustiveGenerator

#guard (firstN (AzNat × AzNat) 10).map (fun p => (p.1.toNat, p.2.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1)]

-- Heterogeneous: `AzNat × AzInt`, second component in `integersGen` order
-- `0, 1, -1, 2, -2, …`.
#guard (firstN (AzNat × AzInt) 8).map (fun p => (p.1.toNat, p.2.toInt))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, -1), (0, 2), (1, -1), (1, 2)]

-- Deeper fairness spot check: `k = 100 = 0b1100100`; fst reads the odd bits
-- (`0b100 = 4`), snd the even bits (`0b1010 = 10`) — both `≈ √100`.
#guard (gen (T := AzNat × AzNat) 100).map (fun p => (p.1.toNat, p.2.toNat)) = some (4, 10)

-- Round-trip: the index of `(2, 1)` computed via `interleave` is `9`, exactly
-- where the doctest prefix above found it.
#guard fairPairAssignment.interleave ![2, 1] == 9
#guard ((firstN (AzNat × AzNat) 10)[fairPairAssignment.interleave ![2, 1]]?).map
    (fun p => (p.1.toNat, p.2.toNat)) = some (2, 1)

end Azurite
