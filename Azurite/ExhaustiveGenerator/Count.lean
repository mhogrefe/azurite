/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Element counts for every `ExhaustiveGenerator`.

  Since a generator covers its type `T` exactly once (`occurs_exactly_once`),
  the number of elements it produces is exactly `|T|`:
    * `Infinite T`               for the 7 infinite (always-`some`) generators,
    * `Fintype.card T = N`       for the 28 finite (eventually-`none`) ones.

  Mathlib DOES provide computable `Fintype` instances for the fixed-width
  base types: `Mathlib.Data.FinEnum` has `FinEnum UInt8 … Int64` instances,
  and `[FinEnum α] → Fintype α`. The order subtypes get computable instances
  from `Subtype.fintype` (the predicates are decidable). So this file derives
  no `Fintype` instances; the `<gen>_card` theorems below hold for ANY ambient
  instance (`Fintype.card` is instance-independent), each reading its bound off
  the generator's own `FiniteGenerator` data via `fintypeCard_eq_finiteCard`.

  NB even a computable `Fintype.card` is INFEASIBLE at runtime for these types
  (evaluating `Fintype.card UInt64` materializes a `2^64`-element `univ`); that
  is why the COMPOSITION path (`LexPair` etc.) consumes the bound as the
  `FiniteGenerator.card` literal, never as `Fintype.card`.
-/
import Azurite.ExhaustiveGenerator.PositiveNaturals
import Azurite.ExhaustiveGenerator.Integers
import Azurite.ExhaustiveGenerator.Signeds
import Azurite.ExhaustiveGenerator.Unsigneds
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FinEnum

namespace Azurite.ExhaustiveGenerator

variable {T : Type*}

/-- The "covers every element" half of `occurs_exactly_once`: every `t : T` is
produced at some position. So the counts below really are counts of *generated*
elements. -/
theorem generates [ExhaustiveGenerator T] (t : T) : ∃ n, gen (T := T) n = some t :=
  ⟨_, (occurs_exactly_once t).choose_spec.1⟩

/-- The unique position at which `t` is generated. -/
noncomputable def idx [ExhaustiveGenerator T] (t : T) : ℕ := (occurs_exactly_once t).choose

theorem gen_idx [ExhaustiveGenerator T] (t : T) : gen (idx t) = some t :=
  (occurs_exactly_once t).choose_spec.1

theorem idx_unique [ExhaustiveGenerator T] {t : T} {m : ℕ} (h : gen m = some t) : m = idx t :=
  (occurs_exactly_once t).choose_spec.2 m h

/-- A finite generator that produces values exactly at positions `0, …, bound-1`
(`hsome`) and `none` afterwards (`hnone`) yields a bijection `T ≃ Fin bound`:
`t ↦` its unique index (`< bound`), with inverse `i ↦ (gen i).get`. -/
noncomputable def equivFin [ExhaustiveGenerator T] (bound : ℕ)
    (hnone : ∀ n, bound ≤ n → gen (T := T) n = none)
    (hsome : ∀ n, n < bound → gen (T := T) n ≠ none) : T ≃ Fin bound where
  toFun t := ⟨idx t, by
    by_contra hlt
    rw [Nat.not_lt] at hlt
    have h1 := gen_idx t
    rw [hnone (idx t) hlt] at h1
    simp at h1⟩
  invFun i := (gen i.val).get (Option.isSome_iff_ne_none.mpr (hsome i.val i.2))
  left_inv t := Option.some.inj (by rw [Option.some_get]; exact gen_idx t)
  right_inv i := Fin.ext (idx_unique (Option.some_get _).symm).symm

/-- The crux count lemma: a generator with the finite `hnone`/`hsome` shape has
`Fintype.card T = bound`. Works for ANY ambient `Fintype T` instance since
`Fintype.card` is instance-independent. -/
theorem fintypeCard_eq [ExhaustiveGenerator T] [Fintype T] (bound : ℕ)
    (hnone : ∀ n, bound ≤ n → gen (T := T) n = none)
    (hsome : ∀ n, n < bound → gen (T := T) n ≠ none) : Fintype.card T = bound :=
  (Fintype.card_congr (equivFin bound hnone hsome)).trans (Fintype.card_fin bound)

/-- Derive a `Fintype T` instance from the finite generator's `T ≃ Fin bound`.
Noncomputable (`equivFin`'s inverse goes through `idx`/choice); used only by the
parametrized range subtypes (`Ranges.lean`/`AzRanges.lean`), which have no
ambient computable instance. -/
@[reducible] noncomputable def fintypeOfBounded [ExhaustiveGenerator T] (bound : ℕ)
    (hnone : ∀ n, bound ≤ n → gen (T := T) n = none)
    (hsome : ∀ n, n < bound → gen (T := T) n ≠ none) : Fintype T :=
  Fintype.ofEquiv _ (equivFin bound hnone hsome).symm

/-- **The `Fintype`/`FiniteGenerator` bridge.** For a finite generator, the
ambient `Fintype` cardinality (any instance) equals the generator's literal
`FiniteGenerator.card`. This is what makes every `<gen>_card` theorem a
one-liner, and it rewrites the odometer radix between the instance path
(literal `card`) and the `Fintype`-stated theorem layer. -/
theorem fintypeCard_eq_finiteCard [ExhaustiveGenerator T] [FiniteGenerator T] [Fintype T] :
    Fintype.card T = FiniteGenerator.card (T := T) :=
  fintypeCard_eq _ FiniteGenerator.gen_none FiniteGenerator.gen_some

/-- **`finiteBound` bridge, `none` half.** For a FINITE `[Contiguous]` generator,
positions at or beyond `Fintype.card T` are `none`. Proof: if some position
`n ≥ card` were `some`, then by contiguity every position `0, …, n` is `some`,
giving an injection `Fin (n+1) ↪ T` (each position's value is distinct — a
shared value would force equal indices via `idx_unique`), so `n + 1 ≤ card T`,
contradicting `card T ≤ n`. This is the `hnone` witness `lexPairGenOfFinite`
needs, synthesized from `[Fintype T] + [Contiguous T]` alone. -/
theorem finiteBound_none [ExhaustiveGenerator T] [Fintype T] [Contiguous T] :
    ∀ n, Fintype.card T ≤ n → gen (T := T) n = none := by
  intro n hn
  by_contra hne
  -- Every position `≤ n` is `some` (contiguity: a `none` at `i ≤ n` would
  -- propagate to `n`, contradicting `hne`).
  have hsome_le : ∀ i, i ≤ n → gen (T := T) i ≠ none := fun i hi h0 => hne (gen_none_of_le hi h0)
  -- The distinct values at positions `0, …, n` inject `Fin (n+1)` into `T`.
  let F : Fin (n + 1) → T := fun i =>
    (gen (T := T) i.val).get (Option.isSome_iff_ne_none.mpr (hsome_le i.val (Nat.lt_succ_iff.mp i.isLt)))
  have hF : Function.Injective F := by
    intro i j hij
    have hgi : gen (T := T) i.val = some (F i) := (Option.some_get _).symm
    have hgj : gen (T := T) j.val = some (F j) := (Option.some_get _).symm
    rw [hij] at hgi
    exact Fin.ext ((idx_unique hgi).trans (idx_unique hgj).symm)
  have := Fintype.card_le_of_injective F hF
  rw [Fintype.card_fin] at this
  omega

/-- **`finiteBound` bridge, `some` half.** For a FINITE `[Contiguous]` generator,
positions below `Fintype.card T` are `some`. Proof: if some position `n < card`
were `none`, then by contiguity every position `≥ n` is `none`, so the index map
`idx : T ↪ Fin n` is well-defined and injective, giving `card T ≤ n < card T`, a
contradiction. This is the `hsome` witness `lexPairGenOfFinite` needs. -/
theorem finiteBound_some [ExhaustiveGenerator T] [Fintype T] [Contiguous T] :
    ∀ n, n < Fintype.card T → gen (T := T) n ≠ none := by
  intro n hn h0
  -- A `none` at `n` propagates to every later position.
  have hnone_ge : ∀ m, n ≤ m → gen (T := T) m = none := fun m hm => gen_none_of_le hm h0
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
  have := Fintype.card_le_of_injective G hG
  rw [Fintype.card_fin] at this
  omega

/-- An always-`some` generator built from a bijection `f : ℕ → T` makes `T`
infinite. -/
theorem infinite_of_bijective (f : ℕ → T) (hf : Function.Bijective f) : Infinite T :=
  Infinite.of_injective f hf.injective

end Azurite.ExhaustiveGenerator

namespace Azurite

open ExhaustiveGenerator

/-! ### Infinite generators: `Infinite T`

Each result is REGISTERED as an instance (the types/subtypes are Azurite's own,
so there is no Mathlib instance to clash with); the named theorem form is kept
for the blueprint/discoverability. -/

theorem naturalsGen_infinite : Infinite AzNat :=
  infinite_of_bijective AzNat.ofNat naturals_bijective

instance : Infinite AzNat := naturalsGen_infinite

theorem positiveNaturalsGen_infinite : Infinite {n : AzNat // 0 < n} :=
  infinite_of_bijective positiveNaturalsFun positiveNaturalsFun_bijective

instance : Infinite {n : AzNat // 0 < n} := positiveNaturalsGen_infinite

theorem positiveIntegersGen_infinite : Infinite {z : AzInt // 0 < z} :=
  infinite_of_bijective positiveIntegersFun positiveIntegersFun_bijective

instance : Infinite {z : AzInt // 0 < z} := positiveIntegersGen_infinite

theorem nonnegativeIntegersGen_infinite : Infinite {z : AzInt // 0 ≤ z} :=
  infinite_of_bijective nonnegativeIntegersFun nonnegativeIntegersFun_bijective

instance : Infinite {z : AzInt // 0 ≤ z} := nonnegativeIntegersGen_infinite

theorem negativeIntegersGen_infinite : Infinite {z : AzInt // z < 0} :=
  infinite_of_bijective negativeIntegersFun negativeIntegersFun_bijective

instance : Infinite {z : AzInt // z < 0} := negativeIntegersGen_infinite

theorem integersGen_infinite : Infinite AzInt :=
  infinite_of_bijective integers integers_bijective

instance : Infinite AzInt := integersGen_infinite

theorem nonzeroIntegersGen_infinite : Infinite {z : AzInt // z ≠ 0} :=
  infinite_of_bijective nonzeroIntegersFun nonzeroIntegersFun_bijective

instance : Infinite {z : AzInt // z ≠ 0} := nonzeroIntegersGen_infinite

/-! ### Finite generators: `Fintype.card T = N`

Every count is `fintypeCard_eq_finiteCard` verbatim: the ambient `Fintype`
instance (Mathlib's computable `FinEnum`-derived one for the base types,
`Subtype.fintype` for the order subtypes) has the cardinality carried by the
generator's `FiniteGenerator` instance, whose literal `card` is definitionally
the stated bound. -/

/-- `uint8Gen` produces `2 ^ 8` elements. -/
theorem uint8Gen_card : Fintype.card UInt8 = 2 ^ 8 := fintypeCard_eq_finiteCard

/-- `uint16Gen` produces `2 ^ 16` elements. -/
theorem uint16Gen_card : Fintype.card UInt16 = 2 ^ 16 := fintypeCard_eq_finiteCard

/-- `uint32Gen` produces `2 ^ 32` elements. -/
theorem uint32Gen_card : Fintype.card UInt32 = 2 ^ 32 := fintypeCard_eq_finiteCard

/-- `uint64Gen` produces `2 ^ 64` elements. -/
theorem uint64Gen_card : Fintype.card UInt64 = 2 ^ 64 := fintypeCard_eq_finiteCard

/-- `int8Gen` produces `2 ^ 8` elements. -/
theorem int8Gen_card : Fintype.card Int8 = 2 ^ 8 := fintypeCard_eq_finiteCard

/-- `int16Gen` produces `2 ^ 16` elements. -/
theorem int16Gen_card : Fintype.card Int16 = 2 ^ 16 := fintypeCard_eq_finiteCard

/-- `int32Gen` produces `2 ^ 32` elements. -/
theorem int32Gen_card : Fintype.card Int32 = 2 ^ 32 := fintypeCard_eq_finiteCard

/-- `int64Gen` produces `2 ^ 64` elements. -/
theorem int64Gen_card : Fintype.card Int64 = 2 ^ 64 := fintypeCard_eq_finiteCard

/-- `positiveUInt8Gen` produces `2 ^ 8 - 1` elements. -/
theorem positiveUInt8Gen_card : Fintype.card {x : UInt8 // 0 < x} = 2 ^ 8 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveUInt16Gen` produces `2 ^ 16 - 1` elements. -/
theorem positiveUInt16Gen_card : Fintype.card {x : UInt16 // 0 < x} = 2 ^ 16 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveUInt32Gen` produces `2 ^ 32 - 1` elements. -/
theorem positiveUInt32Gen_card : Fintype.card {x : UInt32 // 0 < x} = 2 ^ 32 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveUInt64Gen` produces `2 ^ 64 - 1` elements. -/
theorem positiveUInt64Gen_card : Fintype.card {x : UInt64 // 0 < x} = 2 ^ 64 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveInt8Gen` produces `2 ^ 7 - 1` elements. -/
theorem positiveInt8Gen_card : Fintype.card {x : Int8 // 0 < x} = 2 ^ 7 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveInt16Gen` produces `2 ^ 15 - 1` elements. -/
theorem positiveInt16Gen_card : Fintype.card {x : Int16 // 0 < x} = 2 ^ 15 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveInt32Gen` produces `2 ^ 31 - 1` elements. -/
theorem positiveInt32Gen_card : Fintype.card {x : Int32 // 0 < x} = 2 ^ 31 - 1 :=
  fintypeCard_eq_finiteCard

/-- `positiveInt64Gen` produces `2 ^ 63 - 1` elements. -/
theorem positiveInt64Gen_card : Fintype.card {x : Int64 // 0 < x} = 2 ^ 63 - 1 :=
  fintypeCard_eq_finiteCard

/-- `nonnegativeInt8Gen` produces `2 ^ 7` elements. -/
theorem nonnegativeInt8Gen_card : Fintype.card {x : Int8 // 0 ≤ x} = 2 ^ 7 :=
  fintypeCard_eq_finiteCard

/-- `nonnegativeInt16Gen` produces `2 ^ 15` elements. -/
theorem nonnegativeInt16Gen_card : Fintype.card {x : Int16 // 0 ≤ x} = 2 ^ 15 :=
  fintypeCard_eq_finiteCard

/-- `nonnegativeInt32Gen` produces `2 ^ 31` elements. -/
theorem nonnegativeInt32Gen_card : Fintype.card {x : Int32 // 0 ≤ x} = 2 ^ 31 :=
  fintypeCard_eq_finiteCard

/-- `nonnegativeInt64Gen` produces `2 ^ 63` elements. -/
theorem nonnegativeInt64Gen_card : Fintype.card {x : Int64 // 0 ≤ x} = 2 ^ 63 :=
  fintypeCard_eq_finiteCard

/-- `negativeInt8Gen` produces `2 ^ 7` elements. -/
theorem negativeInt8Gen_card : Fintype.card {x : Int8 // x < 0} = 2 ^ 7 :=
  fintypeCard_eq_finiteCard

/-- `negativeInt16Gen` produces `2 ^ 15` elements. -/
theorem negativeInt16Gen_card : Fintype.card {x : Int16 // x < 0} = 2 ^ 15 :=
  fintypeCard_eq_finiteCard

/-- `negativeInt32Gen` produces `2 ^ 31` elements. -/
theorem negativeInt32Gen_card : Fintype.card {x : Int32 // x < 0} = 2 ^ 31 :=
  fintypeCard_eq_finiteCard

/-- `negativeInt64Gen` produces `2 ^ 63` elements. -/
theorem negativeInt64Gen_card : Fintype.card {x : Int64 // x < 0} = 2 ^ 63 :=
  fintypeCard_eq_finiteCard

/-- `nonzeroInt8Gen` produces `2 ^ 8 - 1` elements. -/
theorem nonzeroInt8Gen_card : Fintype.card {x : Int8 // x ≠ 0} = 2 ^ 8 - 1 :=
  fintypeCard_eq_finiteCard

/-- `nonzeroInt16Gen` produces `2 ^ 16 - 1` elements. -/
theorem nonzeroInt16Gen_card : Fintype.card {x : Int16 // x ≠ 0} = 2 ^ 16 - 1 :=
  fintypeCard_eq_finiteCard

/-- `nonzeroInt32Gen` produces `2 ^ 32 - 1` elements. -/
theorem nonzeroInt32Gen_card : Fintype.card {x : Int32 // x ≠ 0} = 2 ^ 32 - 1 :=
  fintypeCard_eq_finiteCard

/-- `nonzeroInt64Gen` produces `2 ^ 64 - 1` elements. -/
theorem nonzeroInt64Gen_card : Fintype.card {x : Int64 // x ≠ 0} = 2 ^ 64 - 1 :=
  fintypeCard_eq_finiteCard

end Azurite
