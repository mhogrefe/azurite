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
      rw [if_pos hi, hfi]
    · intro m hm
      have hm' : (if m < card then some (f m) else none) = some t := hm
      by_cases hmc : m < card
      · rw [if_pos hmc] at hm'
        exact hinj m i hmc hi (by rw [Option.some.inj hm', hfi])
      · rw [if_neg hmc] at hm'
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
      rw [dif_pos hi, hfi]
    · intro m hm
      have hm' : (if h : m < card then some (f m h) else none) = some t := hm
      by_cases hmc : m < card
      · rw [dif_pos hmc] at hm'
        exact hinj m i hmc hi (by rw [Option.some.inj hm', hfi])
      · rw [dif_neg hmc] at hm'
        exact absurd hm' (by simp)

/-- Build a (finite) generator from an explicit duplicate-free list that
contains every value of `T`: `gen n = l[n]?`. Existence of the index comes from
completeness (`hcomp`), uniqueness from `hnd` (`List.getElem?_inj`). Since
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
      exact ((List.getElem?_inj hn hnd).mp hmn).symm

variable {T : Type*} [ExhaustiveGenerator T]

/-- The first `n` generated values, dropping any `none`s. A pure inspection
helper for previewing what a generator produces; for a finite generator with
`card ≤ n`, this yields the whole (finite) enumeration. -/
def firstN (T : Type*) [ExhaustiveGenerator T] (n : ℕ) : List T :=
  (List.range n).filterMap (gen (T := T))

end ExhaustiveGenerator

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

-- Demonstrate the `AzNat` generator produces `0, 1, 2, …`.
#guard ((ExhaustiveGenerator.firstN AzNat 5).map (·.toNat)) == [0, 1, 2, 3, 4]

end Azurite
