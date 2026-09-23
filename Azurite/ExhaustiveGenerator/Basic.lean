/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ExhaustiveGenerator` — a typeclass packaging a generator `ℕ → Option T`
  together with a proof that every value of `T` occurs EXACTLY ONCE.

  The `Option` codomain lets a generator be either infinite (always `some`,
  e.g. every `AzNat`) or finite (eventually `none`, e.g. every `UInt8`, which
  stops after `2^8` values). This is the foundation for exhaustive value
  enumeration (the eventual basis for enumerating all polynomials over a
  coefficient ring). It corresponds to Malachite's `exhaustive_*` iterators.
-/
import Azurite.AzNat.Basic
import Azurite.AzNat.Equiv.Basic
import Mathlib.Logic.Equiv.Basic

namespace Azurite

/-- An exhaustive generator for a type `T`: a function `gen : ℕ → Option T`
enumerating every value of `T` exactly once. The index `n : ℕ` is the abstract
position. A `some t` output at position `n` means `t` is the `n`-th produced
value; `none` marks a position past the end of a finite enumeration. The
`occurs_exactly_once` field says each `t : T` is produced at a unique position
(injective = at most once, surjective = at least once), with the `Option`
wrapper allowing finite generators to run out. -/
class ExhaustiveGenerator (T : Type*) where
  /-- `gen n` is the `n`-th generated value, or `none` past the end. -/
  gen : ℕ → Option T
  /-- Every value of `T` is produced at exactly one position. -/
  occurs_exactly_once : ∀ t : T, ∃! n : ℕ, gen n = some t

/-- A `Contiguous` generator is one whose `some`-outputs form an INITIAL SEGMENT
of `ℕ`: once the generator yields `none` it yields `none` forever (`contig`).
Equivalently, the produced values occupy positions `0, 1, …` with no gaps. All
of Azurite's base generators have this shape (`ofBijective` is always `some`;
the finite builders are `if n < card then some … else none`). This mixin is
what upgrades a `[Fintype B] + [Contiguous B]` finite component into the
`hnone`/`hsome` contiguity witnesses that `lexPairGenOfFinite` consumes (see
`finiteBound_none`/`finiteBound_some` in `Count.lean`). -/
class Contiguous (T : Type*) [inst : ExhaustiveGenerator T] : Prop where
  /-- Once `none`, always `none`: a `none` at position `n` forces `none` at `n+1`. -/
  contig : ∀ n, inst.gen n = none → inst.gen (n + 1) = none

/-- A `FiniteGenerator` carries a finite generator's bound as **data**: `card`
is the number of values produced (positions `0, …, card-1` are `some`, the rest
`none`). Azurite's finite instances supply `card` as a cheap literal (e.g.
`2 ^ 8`), which is what keeps the compositional generators (`LexPair` etc.)
COMPUTABLE: the mixed-radix odometer consumes the bound as its runtime radix.
Even a computable `Fintype.card` would not do — evaluating
`Fintype.card UInt64` materializes a `2^64`-element `univ`. The bound proofs
`gen_none`/`gen_some` are `Prop`s; they are exactly the finiteness witnesses
the `lexPair*` builders consume. NB the named `[inst : …]` binding (same gotcha
as `Contiguous`): the fields must refer to THIS instance's `gen`
(`ExhaustiveGenerator.gen (T := T)` inside the class would re-synthesize). -/
class FiniteGenerator (T : Type*) [inst : ExhaustiveGenerator T] where
  /-- The number of values the generator produces (a cheap literal in instances). -/
  card : ℕ
  /-- Positions at or beyond `card` are `none`. -/
  gen_none : ∀ n, card ≤ n → inst.gen n = none
  /-- Positions below `card` produce a value. -/
  gen_some : ∀ n, n < card → inst.gen n ≠ none

/-- Every finite generator is contiguous: a `none` at `n` puts `n` at or past
`card` (else `gen_some` would contradict it), so `n + 1` is past `card` too.
This lets `[FiniteGenerator T]` alone supply the `Contiguous` mixin everywhere
downstream. -/
instance (priority := 100) FiniteGenerator.toContiguous {T : Type*}
    [ExhaustiveGenerator T] [FiniteGenerator T] : Contiguous T where
  contig n h := by
    by_cases hc : FiniteGenerator.card (T := T) ≤ n + 1
    · exact FiniteGenerator.gen_none (n + 1) hc
    · exact absurd h (FiniteGenerator.gen_some n (by omega))

namespace ExhaustiveGenerator

/-- Build an (infinite) generator from a bijection `f : ℕ → T`: every position
produces a value (`gen n = some (f n)`) and bijectivity gives the
exactly-once property. Reuses existing `Function.Bijective` proofs. -/
@[reducible] def ofBijective {T : Type*} (f : ℕ → T) (hf : Function.Bijective f) :
    ExhaustiveGenerator T where
  gen := fun n => some (f n)
  occurs_exactly_once t := by
    obtain ⟨n, hn⟩ := hf.surjective t
    refine ⟨n, ?_, ?_⟩
    · show some (f n) = some t
      rw [hn]
    · intro m hm
      have hm' : some (f m) = some t := hm
      exact hf.injective (by rw [Option.some.inj hm', hn])

/-- Build a finite generator from a function `f : ℕ → T` that bijects the
initial segment `{0, …, card-1}` onto `T`: positions below `card` produce
values, the rest are `none`. -/
@[reducible] def ofBoundedBij {T : Type*} (card : ℕ) (f : ℕ → T)
    (hinj : ∀ i j, i < card → j < card → f i = f j → i = j)
    (hsurj : ∀ t, ∃ i, i < card ∧ f i = t) : ExhaustiveGenerator T where
  gen := fun n => if n < card then some (f n) else none
  occurs_exactly_once t := by
    obtain ⟨i, hi, hfi⟩ := hsurj t
    refine ⟨i, ?_, ?_⟩
    · show (if i < card then some (f i) else none) = some t
      rw [ite_eq_left hi, hfi]
    · intro m hm
      have hm' : (if m < card then some (f m) else none) = some t := hm
      by_cases hmc : m < card
      · rw [ite_eq_left hmc] at hm'
        exact hinj m i hmc hi (by rw [Option.some.inj hm', hfi])
      · rw [ite_eq_right hmc] at hm'
        exact absurd hm' (by simp)

/-- Like `ofBoundedBij`, but the value function `f` may depend on the proof
`n < card` that the position is in range. This is what subtype generators need:
`f n h` can package a value together with a proof (e.g. positivity) that only
holds within the bounded range. -/
@[reducible] def ofBoundedBijOn {T : Type*} (card : ℕ) (f : (n : ℕ) → n < card → T)
    (hinj : ∀ i j (hi : i < card) (hj : j < card), f i hi = f j hj → i = j)
    (hsurj : ∀ t, ∃ i, ∃ hi : i < card, f i hi = t) : ExhaustiveGenerator T where
  gen := fun n => if h : n < card then some (f n h) else none
  occurs_exactly_once t := by
    obtain ⟨i, hi, hfi⟩ := hsurj t
    refine ⟨i, ?_, ?_⟩
    · show (if h : i < card then some (f i h) else none) = some t
      rw [dite_eq_left hi, hfi]
    · intro m hm
      have hm' : (if h : m < card then some (f m h) else none) = some t := hm
      by_cases hmc : m < card
      · rw [dite_eq_left hmc] at hm'
        exact hinj m i hmc hi (by rw [Option.some.inj hm', hfi])
      · rw [dite_eq_right hmc] at hm'
        exact absurd hm' (by simp)

/-- Build a (finite) generator from an explicit duplicate-free list that
contains every value of `T`: `gen n = l[n]?`. Existence of the index comes from
completeness (`hcomp`), uniqueness from `hnd` (`List.Nodup.getElem?_inj`). Since
`l[n]?` is `some` below `l.length` and `none` above, this matches the finite
`fintypeCard_eq` shape with `bound = l.length`. -/
@[reducible] def ofListNodup {T : Type*} (l : List T) (hnd : l.Nodup)
    (hcomp : ∀ t : T, t ∈ l) : ExhaustiveGenerator T where
  gen n := l[n]?
  occurs_exactly_once t := by
    obtain ⟨n, hn, hget⟩ := List.getElem_of_mem (hcomp t)
    refine ⟨n, ?_, ?_⟩
    · show l[n]? = some t
      rw [List.getElem?_eq_getElem hn, hget]
    · intro m hm
      have hmn : l[n]? = l[m]? := by rw [hm, List.getElem?_eq_getElem hn, hget]
      exact ((List.Nodup.getElem?_inj hn hnd).mp hmn).symm

/-- **Relabel a generator along a computable bijection.** Given a generator for
`S` and a bijection `f : S → T` (the map is DATA, its bijectivity a `Prop`),
produce a generator for `T` that emits `f`-images: `gen k := (g.gen k).map f`.
Positions, finiteness, and enumeration order are inherited verbatim from `g`;
only the emitted values are relabeled. Because `f` is a plain function (not a
`noncomputable` bundled `Equiv`), the result stays computable — usable in
`#eval`/`#guard`. This is the reusable transport combinator underlying the
nested tuple generators. -/
@[reducible] def mapGen {S T : Type*} (f : S → T) (hf : Function.Bijective f)
    (g : ExhaustiveGenerator S) : ExhaustiveGenerator T where
  gen k := (g.gen k).map f
  occurs_exactly_once t := by
    obtain ⟨s, hs⟩ := hf.surjective t
    obtain ⟨n, hn, hun⟩ := g.occurs_exactly_once s
    refine ⟨n, ?_, ?_⟩
    · -- Existence: `g` produces `s` at `n`, so `mapGen` produces `f s = t` there.
      show (g.gen n).map f = some t
      rw [hn, Option.map_some, hs]
    · -- Uniqueness: a producing position for `t` gives (via `f` injective) one for `s`.
      intro m hm
      have hm : (g.gen m).map f = some t := hm
      rcases hgm : g.gen m with _ | s'
      · rw [hgm] at hm; simp at hm
      · rw [hgm, Option.map_some] at hm
        exact hun m (hgm.trans (by rw [hf.injective ((Option.some.inj hm).trans hs.symm)]))

/-! ### Builder contiguity lemmas

Each builder produces a `Contiguous` generator. These lemmas are keyed on the
`gen`-FUNCTION SHAPE (not on the specific proof arguments of the builder, which
live only in the proof-irrelevant `occurs_exactly_once` field and so cannot be
recovered by unification). The generator is passed explicitly and the shape
hypothesis is discharged by `rfl` (the builders are `@[reducible]`, so their
`gen` field is definitionally the stated shape). Typical use:
`instance : Contiguous UInt8 := contiguous_of_boundedBij uint8Gen rfl`. -/

/-- An always-`some` generator (shape `fun n => some (f n)`, as from
`ofBijective`) is vacuously contiguous. -/
theorem contiguous_of_gen_some {T : Type*} (g : ExhaustiveGenerator T) {f : ℕ → T}
    (hg : g.gen = fun n => some (f n)) : @Contiguous T g :=
  ⟨fun n h => by rw [hg] at h; exact absurd h (Option.some_ne_none _)⟩

/-- A bounded generator of shape `fun n => if n < card then some (f n) else none`
(as from `ofBoundedBij`) is contiguous: a `none` means `n ≥ card`, so `n + 1 ≥
card` is `none` too. -/
theorem contiguous_of_boundedBij {T : Type*} (g : ExhaustiveGenerator T) {card : ℕ}
    {f : ℕ → T} (hg : g.gen = fun n => if n < card then some (f n) else none) :
    @Contiguous T g := by
  refine ⟨fun n h => ?_⟩
  rw [hg] at h ⊢
  simp only at h ⊢
  by_cases hn : n < card
  · rw [ite_eq_left hn] at h; exact absurd h (Option.some_ne_none _)
  · rw [ite_eq_right (by omega)]

/-- A bounded generator of shape `fun n => if h : n < card then some (f n h) else
none` (as from `ofBoundedBijOn`) is contiguous. -/
theorem contiguous_of_boundedBijOn {T : Type*} (g : ExhaustiveGenerator T) {card : ℕ}
    {f : (n : ℕ) → n < card → T}
    (hg : g.gen = fun n => if h : n < card then some (f n h) else none) :
    @Contiguous T g := by
  refine ⟨fun n h => ?_⟩
  rw [hg] at h ⊢
  simp only at h ⊢
  by_cases hn : n < card
  · rw [dite_eq_left hn] at h; exact absurd h (Option.some_ne_none _)
  · rw [dite_eq_right (by omega)]

/-- A list-backed generator of shape `fun n => l[n]?` (as from `ofListNodup`) is
contiguous: `l[n]? = none` means `l.length ≤ n`, so `l[n+1]? = none` too. -/
theorem contiguous_of_getElem? {T : Type*} (g : ExhaustiveGenerator T) {l : List T}
    (hg : g.gen = fun n => l[n]?) : @Contiguous T g := by
  refine ⟨fun n h => ?_⟩
  rw [hg] at h ⊢
  simp only at h ⊢
  rw [List.getElem?_eq_none_iff] at h ⊢
  omega

/-- `mapGen` preserves contiguity: relabeling along `f` does not change which
positions are `some` (`Option.map` sends `none ↔ none`). Stated as a raw
`contig`-step over the underlying generator `g` (with `hstep` its step) since
`mapGen` takes `g` as explicit data. -/
theorem mapGen_contig_step {S T : Type*} (f : S → T) (hf : Function.Bijective f)
    (g : ExhaustiveGenerator S) (hstep : ∀ n, g.gen n = none → g.gen (n + 1) = none) :
    ∀ n, (mapGen f hf g).gen n = none → (mapGen f hf g).gen (n + 1) = none := by
  intro n h
  have h : (g.gen n).map f = none := h
  show (g.gen (n + 1)).map f = none
  rw [Option.map_eq_none_iff] at h ⊢
  exact hstep n h

/-- `mapGen` preserves `Contiguous` (packaged form): relabeling a contiguous
generator along `f` yields a contiguous generator. `f` is passed explicitly so
the produced `@Contiguous T (mapGen f hf g)` matches a `mapGen`-defined instance
definitionally. -/
theorem mapGen_contiguous {S T : Type*} (f : S → T) (hf : Function.Bijective f)
    (g : ExhaustiveGenerator S) (hg : @Contiguous S g) : @Contiguous T (mapGen f hf g) :=
  @Contiguous.mk T (mapGen f hf g) (mapGen_contig_step f hf g (fun n => hg.contig n))

variable {T : Type*} [ExhaustiveGenerator T]

/-- **Monotone `none`-propagation.** From the `contig` step, a `none` output at
position `m` forces `none` at every later position `n ≥ m`. This is the
initial-segment property in its usable form. -/
theorem gen_none_of_le [Contiguous T] {m n : ℕ} (hmn : m ≤ n)
    (h : gen (T := T) m = none) : gen (T := T) n = none := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact Contiguous.contig _ ih

/-- Step-form of `gen_none_of_le` for a generator `g` supplied as explicit data
(not resolved as the ambient instance): a `none` at `m ≤ n` propagates to `n`. -/
theorem gen_none_of_le_step {S : Type*} (g : ExhaustiveGenerator S)
    (hstep : ∀ n, g.gen n = none → g.gen (n + 1) = none) {m n : ℕ} (hmn : m ≤ n)
    (h : g.gen m = none) : g.gen n = none := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact hstep _ ih

/-- The first `n` generated values, dropping any `none`s. A pure inspection
helper for previewing what a generator produces; for a finite generator with
`card ≤ n`, this yields the whole (finite) enumeration. -/
def firstN (T : Type*) [ExhaustiveGenerator T] (n : ℕ) : List T :=
  (List.range n).filterMap (gen (T := T))

end ExhaustiveGenerator

namespace FiniteGenerator

/-! ### Builder `FiniteGenerator` data

Like the builder contiguity lemmas above, these are keyed on the `gen`-function
SHAPE, with the shape hypothesis discharged by `rfl` (the builders are
`@[reducible]`). `card` is passed EXPLICITLY so instances carry the intended
literal (which need only be *definitionally* equal to the shape's bound — e.g.
`2 ^ 8` for a builder bound spelled `2 * 2 ^ 7`). Typical use:
`instance : FiniteGenerator UInt8 := .ofBoundedBij uint8Gen (2 ^ 8) rfl`. -/

/-- `FiniteGenerator` data for a bounded generator of shape
`fun n => if n < card then some (f n) else none` (as from `ofBoundedBij`). -/
@[reducible] def ofBoundedBij {T : Type*} (g : ExhaustiveGenerator T) (card : ℕ)
    {f : ℕ → T} (hg : g.gen = fun n => if n < card then some (f n) else none) :
    @FiniteGenerator T g where
  card := card
  gen_none n hn := by simp only [hg]; exact ite_eq_right (by omega)
  gen_some n hn := by simp only [hg]; rw [ite_eq_left hn]; exact Option.some_ne_none _

/-- `FiniteGenerator` data for a bounded generator of shape
`fun n => if h : n < card then some (f n h) else none` (as from `ofBoundedBijOn`). -/
@[reducible] def ofBoundedBijOn {T : Type*} (g : ExhaustiveGenerator T) (card : ℕ)
    {f : (n : ℕ) → n < card → T}
    (hg : g.gen = fun n => if h : n < card then some (f n h) else none) :
    @FiniteGenerator T g where
  card := card
  gen_none n hn := by simp only [hg]; exact dite_eq_right (by omega)
  gen_some n hn := by simp only [hg]; rw [dite_eq_left hn]; exact Option.some_ne_none _

/-- `FiniteGenerator` data for a list-backed generator of shape `fun n => l[n]?`
(as from `ofListNodup`); `card` is the list length, passed as a literal with the
`hlen` obligation discharged by `rfl`. -/
@[reducible] def ofListNodup {T : Type*} (g : ExhaustiveGenerator T) (card : ℕ)
    {l : List T} (hg : g.gen = fun n => l[n]?) (hlen : l.length = card) :
    @FiniteGenerator T g where
  card := card
  gen_none n hn := by simp only [hg]; exact List.getElem?_eq_none (by omega)
  gen_some n hn := by
    simp only [hg]
    rw [List.getElem?_eq_getElem (by omega)]
    exact Option.some_ne_none _

/-- A finite generator over a NONEMPTY type produces at least one value:
`occurs_exactly_once` puts a witness at some position, which `gen_none` forces
below `card`. This is what discharges nonemptiness side conditions (e.g.
`lexDepPairGen`'s nonempty-blocks requirement) from a `[Nonempty T]`
hypothesis. -/
theorem card_pos {T : Type*} [inst : ExhaustiveGenerator T] [FiniteGenerator T]
    [Nonempty T] : 0 < card (T := T) := by
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨n, hn, -⟩ := inst.occurs_exactly_once t
  by_contra h
  rw [gen_none n (by omega)] at hn
  exact Option.some_ne_none t hn.symm

/-- `mapGen` preserves `FiniteGenerator` data with the SAME bound: relabeling
along `f` does not change which positions are `some` (`Option.map` sends
`none ↔ none`). This is how the flat tuple/vec composites inherit their finite
bound from the underlying nested pair. -/
@[reducible] def map {S T : Type*} (f : S → T) (hf : Function.Bijective f)
    (g : ExhaustiveGenerator S) (fg : @FiniteGenerator S g) :
    @FiniteGenerator T (ExhaustiveGenerator.mapGen f hf g) :=
  -- NB explicit `mk` (not `where`): structure-instance notation fails to unify
  -- the explicit instance argument when it is an application, not a variable.
  @FiniteGenerator.mk T (ExhaustiveGenerator.mapGen f hf g) fg.card
    (fun n hn => by
      show (g.gen n).map f = none
      rw [fg.gen_none n hn, Option.map_none])
    (fun n hn => by
      show (g.gen n).map f ≠ none
      rw [Ne, Option.map_eq_none_iff]
      exact fg.gen_some n hn)

end FiniteGenerator

/-- The exhaustive generator for `AzNat`: `gen n = some (AzNat.ofNat n)`,
producing `0, 1, 2, …`. Bijectivity of `AzNat.ofNat` follows from the
`ℕ ↔ AzNat` round-trip lemmas `AzNat.toNat_ofNat` and `AzNat.ofNat_toNat`. -/
theorem naturals_bijective : Function.Bijective AzNat.ofNat := by
  constructor
  · -- injective: `ofNat n = ofNat m → n = m` via `toNat_ofNat`
    intro n m h
    have := congrArg AzNat.toNat h
    rwa [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
  · -- surjective: `a = ofNat a.toNat` via `ofNat_toNat`
    intro a
    exact ⟨a.toNat, AzNat.ofNat_toNat a⟩

instance naturalsGen : ExhaustiveGenerator AzNat :=
  ExhaustiveGenerator.ofBijective AzNat.ofNat naturals_bijective

instance : Contiguous AzNat := ExhaustiveGenerator.contiguous_of_gen_some naturalsGen rfl

-- Demonstrate the `AzNat` generator produces `0, 1, 2, …`.
#guard ((ExhaustiveGenerator.firstN AzNat 5).map (·.toNat)) == [0, 1, 2, 3, 4]

end Azurite
