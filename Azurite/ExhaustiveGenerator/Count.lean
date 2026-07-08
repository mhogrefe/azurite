/-
  Element counts for every `ExhaustiveGenerator`.

  Since a generator covers its type `T` exactly once (`occurs_exactly_once`),
  the number of elements it produces is exactly `|T|`:
    * `Infinite T`               for the 7 infinite (always-`some`) generators,
    * `Fintype.card T = N`       for the 28 finite (eventually-`none`) ones.

  The finite base types (`UIntX`/`IntX`) and the order subtypes have no
  `Fintype` instance in Mathlib, so this file DERIVES one for each from the
  generator's own bijection `T ≃ Fin N` (`equivFin`), then reads off the card.
-/
import Azurite.ExhaustiveGenerator.PositiveNaturals
import Azurite.ExhaustiveGenerator.Integers
import Azurite.ExhaustiveGenerator.Signeds
import Azurite.ExhaustiveGenerator.Unsigneds
import Mathlib.Data.Fintype.Card

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

/-- Derive a `Fintype T` instance from the finite generator's `T ≃ Fin bound`. -/
@[reducible] noncomputable def fintypeOfBounded [ExhaustiveGenerator T] (bound : ℕ)
    (hnone : ∀ n, bound ≤ n → gen (T := T) n = none)
    (hsome : ∀ n, n < bound → gen (T := T) n ≠ none) : Fintype T :=
  Fintype.ofEquiv _ (equivFin bound hnone hsome).symm

/-- An always-`some` generator built from a bijection `f : ℕ → T` makes `T`
infinite. -/
theorem infinite_of_bijective (f : ℕ → T) (hf : Function.Bijective f) : Infinite T :=
  Infinite.of_injective f hf.injective

end Azurite.ExhaustiveGenerator

namespace Azurite

open ExhaustiveGenerator

/-! ### Infinite generators: `Infinite T` -/

theorem naturalsGen_infinite : Infinite AzNat :=
  infinite_of_bijective AzNat.ofNat naturals_bijective

theorem positiveNaturalsGen_infinite : Infinite {n : AzNat // 0 < n} :=
  infinite_of_bijective positiveNaturalsFun positiveNaturalsFun_bijective

theorem positiveIntegersGen_infinite : Infinite {z : AzInt // 0 < z} :=
  infinite_of_bijective positiveIntegersFun positiveIntegersFun_bijective

theorem nonnegativeIntegersGen_infinite : Infinite {z : AzInt // 0 ≤ z} :=
  infinite_of_bijective nonnegativeIntegersFun nonnegativeIntegersFun_bijective

theorem negativeIntegersGen_infinite : Infinite {z : AzInt // z < 0} :=
  infinite_of_bijective negativeIntegersFun negativeIntegersFun_bijective

theorem integersGen_infinite : Infinite AzInt :=
  infinite_of_bijective integers integers_bijective

theorem nonzeroIntegersGen_infinite : Infinite {z : AzInt // z ≠ 0} :=
  infinite_of_bijective nonzeroIntegersFun nonzeroIntegersFun_bijective

/-! ### Finite generators: `Fintype.card T = N`

Each type gets a `Fintype` instance derived from its generator's
`T ≃ Fin N`, then the card is read off. The `hnone`/`hsome` obligations are
one-liners because the finite builders' `gen` is definitionally an
`if`/`dif` on `n < card`. -/

noncomputable instance : Fintype (UInt8) :=
  fintypeOfBounded (2 ^ 8)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt8) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint8Gen` produces `2 ^ 8` elements. -/
theorem uint8Gen_card : Fintype.card (UInt8) = 2 ^ 8 :=
  fintypeCard_eq (2 ^ 8)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt8) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (UInt16) :=
  fintypeOfBounded (2 ^ 16)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt16) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint16Gen` produces `2 ^ 16` elements. -/
theorem uint16Gen_card : Fintype.card (UInt16) = 2 ^ 16 :=
  fintypeCard_eq (2 ^ 16)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt16) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (UInt32) :=
  fintypeOfBounded (2 ^ 32)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt32) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint32Gen` produces `2 ^ 32` elements. -/
theorem uint32Gen_card : Fintype.card (UInt32) = 2 ^ 32 :=
  fintypeCard_eq (2 ^ 32)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt32) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (UInt64) :=
  fintypeOfBounded (2 ^ 64)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt64) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint64Gen` produces `2 ^ 64` elements. -/
theorem uint64Gen_card : Fintype.card (UInt64) = 2 ^ 64 :=
  fintypeCard_eq (2 ^ 64)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := UInt64) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (Int8) :=
  fintypeOfBounded (2 ^ 8)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int8) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `int8Gen` produces `2 ^ 8` elements. -/
theorem int8Gen_card : Fintype.card (Int8) = 2 ^ 8 :=
  fintypeCard_eq (2 ^ 8)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int8) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (Int16) :=
  fintypeOfBounded (2 ^ 16)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int16) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `int16Gen` produces `2 ^ 16` elements. -/
theorem int16Gen_card : Fintype.card (Int16) = 2 ^ 16 :=
  fintypeCard_eq (2 ^ 16)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int16) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (Int32) :=
  fintypeOfBounded (2 ^ 32)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int32) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `int32Gen` produces `2 ^ 32` elements. -/
theorem int32Gen_card : Fintype.card (Int32) = 2 ^ 32 :=
  fintypeCard_eq (2 ^ 32)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int32) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype (Int64) :=
  fintypeOfBounded (2 ^ 64)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int64) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

/-- `int64Gen` produces `2 ^ 64` elements. -/
theorem int64Gen_card : Fintype.card (Int64) = 2 ^ 64 :=
  fintypeCard_eq (2 ^ 64)
    (fun _ _ => if_neg (by omega))
    (fun _ _ => by rw [show gen (T := Int64) _ = some _ from if_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : UInt8 // 0 < x}) :=
  fintypeOfBounded (2 ^ 8 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt8 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveUInt8Gen` produces `2 ^ 8 - 1` elements. -/
theorem positiveUInt8Gen_card : Fintype.card ({x : UInt8 // 0 < x}) = 2 ^ 8 - 1 :=
  fintypeCard_eq (2 ^ 8 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt8 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : UInt16 // 0 < x}) :=
  fintypeOfBounded (2 ^ 16 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt16 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveUInt16Gen` produces `2 ^ 16 - 1` elements. -/
theorem positiveUInt16Gen_card : Fintype.card ({x : UInt16 // 0 < x}) = 2 ^ 16 - 1 :=
  fintypeCard_eq (2 ^ 16 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt16 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : UInt32 // 0 < x}) :=
  fintypeOfBounded (2 ^ 32 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt32 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveUInt32Gen` produces `2 ^ 32 - 1` elements. -/
theorem positiveUInt32Gen_card : Fintype.card ({x : UInt32 // 0 < x}) = 2 ^ 32 - 1 :=
  fintypeCard_eq (2 ^ 32 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt32 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : UInt64 // 0 < x}) :=
  fintypeOfBounded (2 ^ 64 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt64 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveUInt64Gen` produces `2 ^ 64 - 1` elements. -/
theorem positiveUInt64Gen_card : Fintype.card ({x : UInt64 // 0 < x}) = 2 ^ 64 - 1 :=
  fintypeCard_eq (2 ^ 64 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : UInt64 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int8 // 0 < x}) :=
  fintypeOfBounded (2 ^ 7 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveInt8Gen` produces `2 ^ 7 - 1` elements. -/
theorem positiveInt8Gen_card : Fintype.card ({x : Int8 // 0 < x}) = 2 ^ 7 - 1 :=
  fintypeCard_eq (2 ^ 7 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int16 // 0 < x}) :=
  fintypeOfBounded (2 ^ 15 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveInt16Gen` produces `2 ^ 15 - 1` elements. -/
theorem positiveInt16Gen_card : Fintype.card ({x : Int16 // 0 < x}) = 2 ^ 15 - 1 :=
  fintypeCard_eq (2 ^ 15 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int32 // 0 < x}) :=
  fintypeOfBounded (2 ^ 31 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveInt32Gen` produces `2 ^ 31 - 1` elements. -/
theorem positiveInt32Gen_card : Fintype.card ({x : Int32 // 0 < x}) = 2 ^ 31 - 1 :=
  fintypeCard_eq (2 ^ 31 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int64 // 0 < x}) :=
  fintypeOfBounded (2 ^ 63 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `positiveInt64Gen` produces `2 ^ 63 - 1` elements. -/
theorem positiveInt64Gen_card : Fintype.card ({x : Int64 // 0 < x}) = 2 ^ 63 - 1 :=
  fintypeCard_eq (2 ^ 63 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // 0 < x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int8 // 0 ≤ x}) :=
  fintypeOfBounded (2 ^ 7)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonnegativeInt8Gen` produces `2 ^ 7` elements. -/
theorem nonnegativeInt8Gen_card : Fintype.card ({x : Int8 // 0 ≤ x}) = 2 ^ 7 :=
  fintypeCard_eq (2 ^ 7)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int16 // 0 ≤ x}) :=
  fintypeOfBounded (2 ^ 15)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonnegativeInt16Gen` produces `2 ^ 15` elements. -/
theorem nonnegativeInt16Gen_card : Fintype.card ({x : Int16 // 0 ≤ x}) = 2 ^ 15 :=
  fintypeCard_eq (2 ^ 15)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int32 // 0 ≤ x}) :=
  fintypeOfBounded (2 ^ 31)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonnegativeInt32Gen` produces `2 ^ 31` elements. -/
theorem nonnegativeInt32Gen_card : Fintype.card ({x : Int32 // 0 ≤ x}) = 2 ^ 31 :=
  fintypeCard_eq (2 ^ 31)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int64 // 0 ≤ x}) :=
  fintypeOfBounded (2 ^ 63)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonnegativeInt64Gen` produces `2 ^ 63` elements. -/
theorem nonnegativeInt64Gen_card : Fintype.card ({x : Int64 // 0 ≤ x}) = 2 ^ 63 :=
  fintypeCard_eq (2 ^ 63)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // 0 ≤ x}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int8 // x < 0}) :=
  fintypeOfBounded (2 ^ 7)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `negativeInt8Gen` produces `2 ^ 7` elements. -/
theorem negativeInt8Gen_card : Fintype.card ({x : Int8 // x < 0}) = 2 ^ 7 :=
  fintypeCard_eq (2 ^ 7)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int16 // x < 0}) :=
  fintypeOfBounded (2 ^ 15)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `negativeInt16Gen` produces `2 ^ 15` elements. -/
theorem negativeInt16Gen_card : Fintype.card ({x : Int16 // x < 0}) = 2 ^ 15 :=
  fintypeCard_eq (2 ^ 15)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int32 // x < 0}) :=
  fintypeOfBounded (2 ^ 31)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `negativeInt32Gen` produces `2 ^ 31` elements. -/
theorem negativeInt32Gen_card : Fintype.card ({x : Int32 // x < 0}) = 2 ^ 31 :=
  fintypeCard_eq (2 ^ 31)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int64 // x < 0}) :=
  fintypeOfBounded (2 ^ 63)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `negativeInt64Gen` produces `2 ^ 63` elements. -/
theorem negativeInt64Gen_card : Fintype.card ({x : Int64 // x < 0}) = 2 ^ 63 :=
  fintypeCard_eq (2 ^ 63)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // x < 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int8 // x ≠ 0}) :=
  fintypeOfBounded (2 ^ 8 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonzeroInt8Gen` produces `2 ^ 8 - 1` elements. -/
theorem nonzeroInt8Gen_card : Fintype.card ({x : Int8 // x ≠ 0}) = 2 ^ 8 - 1 :=
  fintypeCard_eq (2 ^ 8 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int8 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int16 // x ≠ 0}) :=
  fintypeOfBounded (2 ^ 16 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonzeroInt16Gen` produces `2 ^ 16 - 1` elements. -/
theorem nonzeroInt16Gen_card : Fintype.card ({x : Int16 // x ≠ 0}) = 2 ^ 16 - 1 :=
  fintypeCard_eq (2 ^ 16 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int16 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int32 // x ≠ 0}) :=
  fintypeOfBounded (2 ^ 32 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonzeroInt32Gen` produces `2 ^ 32 - 1` elements. -/
theorem nonzeroInt32Gen_card : Fintype.card ({x : Int32 // x ≠ 0}) = 2 ^ 32 - 1 :=
  fintypeCard_eq (2 ^ 32 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int32 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

noncomputable instance : Fintype ({x : Int64 // x ≠ 0}) :=
  fintypeOfBounded (2 ^ 64 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `nonzeroInt64Gen` produces `2 ^ 64 - 1` elements. -/
theorem nonzeroInt64Gen_card : Fintype.card ({x : Int64 // x ≠ 0}) = 2 ^ 64 - 1 :=
  fintypeCard_eq (2 ^ 64 - 1)
    (fun _ _ => dif_neg (by omega))
    (fun _ _ => by rw [show gen (T := {x : Int64 // x ≠ 0}) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

end Azurite
