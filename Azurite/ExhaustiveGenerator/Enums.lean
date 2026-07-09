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

instance : Contiguous Bool := contiguous_of_getElem? boolsGen rfl
instance : Contiguous Ordering := contiguous_of_getElem? orderingsIncreasingGen rfl
instance : Contiguous RoundingMode := contiguous_of_getElem? roundingModesGen rfl

-- Finite bounds as literal data (the runtime radix for compositional generators).
instance : FiniteGenerator Bool := .ofListNodup boolsGen 2 rfl rfl
instance : FiniteGenerator Ordering := .ofListNodup orderingsIncreasingGen 3 rfl rfl
instance : FiniteGenerator RoundingMode := .ofListNodup roundingModesGen 5 rfl rfl

/-! ### Counts

`Bool` and `Ordering` have Mathlib `Fintype` instances; `RoundingMode` does
not, so we supply a COMPUTABLE hand-written one from the constructor list
(computability matters: a noncomputable `Fintype` here would poison nothing in
this file, but keeping every instance in the library computable is the standing
rule). The counts are the `FiniteGenerator` literals via the bridge. -/

/-- `boolsGen` produces `2` elements. -/
theorem boolsGen_card : Fintype.card Bool = 2 := fintypeCard_eq_finiteCard

/-- `orderingsIncreasingGen` produces `3` elements. -/
theorem orderingsIncreasingGen_card : Fintype.card Ordering = 3 := fintypeCard_eq_finiteCard

/-- `orderingsGen` produces `3` elements (same type, so same card as the
increasing variant; proved through `orderingsGen`'s own bijection, which is a
named generator rather than the instance — hence the explicit `@`). -/
theorem orderingsGen_card : Fintype.card Ordering = 3 :=
  @fintypeCard_eq Ordering orderingsGen _ 3 (fun _ h => List.getElem?_eq_none h)
    (fun _ h => by rw [show @gen Ordering orderingsGen _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _)

/-- A computable `Fintype` for `RoundingMode` from its constructor list. -/
instance : Fintype RoundingMode where
  elems := ⟨([.Down, .Up, .Floor, .Ceiling, .Nearest] : List RoundingMode), by decide⟩
  complete x := by cases x <;> decide

/-- `roundingModesGen` produces `5` elements. -/
theorem roundingModesGen_card : Fintype.card RoundingMode = 5 := fintypeCard_eq_finiteCard

/-! ### Guards -/

#guard firstN Bool 10 = [false, true]
#guard firstN Ordering 10 = [.lt, .eq, .gt]
#guard (@firstN Ordering orderingsGen 10) = [.eq, .lt, .gt]
#guard firstN RoundingMode 10 = [.Down, .Up, .Floor, .Ceiling, .Nearest]
-- Finiteness: each stops at its cardinality, not at the requested `10`.
#guard (firstN Bool 10).length == 2
#guard (firstN RoundingMode 10).length == 5

end Azurite
