/-
  Finite exhaustive generators for small explicit enumerations
  (Malachite `exhaustive_bools`, `orderings_increasing`,
  `exhaustive_orderings`, `exhaustive_rounding_modes`).

  Each is a one-line `ExhaustiveGenerator.ofListNodup` over the type's
  constructor list, with `Nodup`/completeness discharged by `decide` (or a
  `cases` when the type has no `Fintype`). Counts follow via `fintypeCard_eq`
  with `bound = l.length`.
-/
import Azurite.ExhaustiveGenerator.Count
import Azurite.Rounding.Mode
import Mathlib.Data.Fintype.Card

namespace Azurite

open ExhaustiveGenerator

/-! ### The four generators -/

/-- `exhaustive_bools`: `[false, true]`. -/
instance boolsGen : ExhaustiveGenerator Bool :=
  ofListNodup [false, true] (by decide) (by decide)

/-- `orderings_increasing`: `[Less, Equal, Greater]`. -/
instance orderingsIncreasingGen : ExhaustiveGenerator Ordering :=
  ofListNodup [.lt, .eq, .gt] (by decide) (by decide)

/-- `exhaustive_orderings`: `[Equal, Less, Greater]` (Equal first). NB this is a
second `ExhaustiveGenerator Ordering`; reference it explicitly by name (it is
not the default instance). -/
@[reducible] def orderingsGen : ExhaustiveGenerator Ordering :=
  ofListNodup [.eq, .lt, .gt] (by decide) (by decide)

/-- `exhaustive_rounding_modes`: Azurite's `RoundingMode` has five variants
(`Floor/Ceiling/Down/Up/Nearest`, no `Exact`), enumerated in Malachite's order
minus the nonexistent `Exact`: `[Down, Up, Floor, Ceiling, Nearest]`. -/
instance roundingModesGen : ExhaustiveGenerator RoundingMode :=
  ofListNodup [.Down, .Up, .Floor, .Ceiling, .Nearest] (by decide)
    (by intro t; cases t <;> decide)

/-! ### Counts

`Bool` and `Ordering` have Mathlib `Fintype` instances; `RoundingMode` does
not, so we derive one from `roundingModesGen`'s bijection (as `Count.lean` does
for `UIntX`/`IntX`). The `hnone`/`hsome` obligations are `List.getElem?`
length facts. -/

/-- `boolsGen` produces `2` elements. -/
theorem boolsGen_card : Fintype.card Bool = 2 :=
  fintypeCard_eq 2 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show gen (T := Bool) _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

/-- `orderingsIncreasingGen` produces `3` elements. -/
theorem orderingsIncreasingGen_card : Fintype.card Ordering = 3 :=
  fintypeCard_eq 3 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show gen (T := Ordering) _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

/-- `orderingsGen` produces `3` elements (same type, so same card as the
increasing variant; proved through `orderingsGen`'s own bijection). -/
theorem orderingsGen_card : Fintype.card Ordering = 3 :=
  @fintypeCard_eq Ordering orderingsGen _ 3 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show @gen Ordering orderingsGen _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

noncomputable instance : Fintype RoundingMode :=
  fintypeOfBounded 5 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show gen (T := RoundingMode) _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

/-- `roundingModesGen` produces `5` elements. -/
theorem roundingModesGen_card : Fintype.card RoundingMode = 5 :=
  fintypeCard_eq 5 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show gen (T := RoundingMode) _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

/-! ### Guards -/

#guard firstN Bool 10 = [false, true]
#guard firstN Ordering 10 = [.lt, .eq, .gt]
#guard (@firstN Ordering orderingsGen 10) = [.eq, .lt, .gt]
#guard firstN RoundingMode 10 = [.Down, .Up, .Floor, .Ceiling, .Nearest]
-- Finiteness: each stops at its cardinality, not at the requested `10`.
#guard (firstN Bool 10).length == 2
#guard (firstN RoundingMode 10).length == 5

end Azurite
