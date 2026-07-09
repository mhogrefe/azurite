/-
  `lex_triples` / `lex_quadruples` — lexicographic triple and quadruple
  generation (Malachite `lex_triples`, `lex_quadruples`).

  Malachite yields FLAT tuples, so the outputs here are flat newtypes
  `LexTriple A B C` and `LexQuadruple A B C D` (not nested pairs). They are
  built, however, by NESTING `LexPair`s and relabeling along a computable
  flattening bijection via `mapGen` — this reuses the pair generator's
  odometer proof wholesale, so no fresh mixed-radix arithmetic is needed.

  The nesting is `LexPair A (LexPair B C)` for triples and
  `LexPair A (LexPair B (LexPair C D))` for quadruples, with the LAST
  coordinate varying fastest. The key enabler is
  `lexPairGen_contiguous`/`lexPairGenOfFinite_contiguous` (in `LexPairs.lean`):
  a composed pair generator of contiguous generators is itself contiguous, so
  the inner `LexPair …` generator can serve as the FINITE second argument of
  the next `lexPairGen` out. Consequently **all but the first component must be
  finite** (`B, C[, D]`); the first (`A`) may be infinite.

  We use the nesting route (not a direct n-ary mixed-radix builder) precisely
  because it reuses `lexPairGen`'s proven odometer and the contiguity lemma:
  the builders below are proof-free assemblies, and correctness is inherited.
-/
import Azurite.ExhaustiveGenerator.LexPairs
import Mathlib.Data.Fintype.Prod

namespace Azurite

/-! ### Flat tuple newtypes -/

/-- A lexicographically-ordered triple: a flat newtype for `A × B × C`, kept
distinct from `A × B × C` (and from nested `LexPair`s) so it can carry its own
lexicographic `ExhaustiveGenerator`. The last coordinate (`thd`) varies
fastest; `B` and `C` must be finite, `A` may be infinite. -/
structure LexTriple (A B C : Type*) where
  /-- The first (slowest) coordinate; may range over an infinite type. -/
  fst : A
  /-- The middle coordinate; must range over a finite type. -/
  snd : B
  /-- The last (fastest) coordinate; must range over a finite type. -/
  thd : C
  deriving DecidableEq

/-- A lexicographically-ordered quadruple: a flat newtype for `A × B × C × D`.
The last coordinate (`fth`) varies fastest; `B`, `C`, `D` must be finite, `A`
may be infinite. -/
structure LexQuadruple (A B C D : Type*) where
  /-- The first (slowest) coordinate; may range over an infinite type. -/
  fst : A
  /-- The second coordinate; must range over a finite type. -/
  snd : B
  /-- The third coordinate; must range over a finite type. -/
  thd : C
  /-- The last (fastest) coordinate; must range over a finite type. -/
  fth : D
  deriving DecidableEq

namespace LexTriple

/-- The obvious computable equivalence `LexTriple A B C ≃ A × B × C`. Lets us
borrow `Prod`'s `Fintype`/cardinality facts for the count lemmas. -/
@[simps] def equivProd {A B C : Type*} : LexTriple A B C ≃ A × B × C where
  toFun t := (t.fst, t.snd, t.thd)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LexTriple

namespace LexQuadruple

/-- The obvious computable equivalence `LexQuadruple A B C D ≃ A × B × C × D`. -/
@[simps] def equivProd {A B C D : Type*} : LexQuadruple A B C D ≃ A × B × C × D where
  toFun t := (t.fst, t.snd, t.thd, t.fth)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LexQuadruple

namespace ExhaustiveGenerator

/-! ### The flattening bijections -/

/-- Flatten a nested pair into a `LexTriple` (computable, bijective). -/
@[reducible] def flattenTriple {A B C : Type*} (p : LexPair A (LexPair B C)) :
    LexTriple A B C := ⟨p.fst, p.snd.fst, p.snd.snd⟩

theorem flattenTriple_bijective {A B C : Type*} :
    Function.Bijective (flattenTriple : LexPair A (LexPair B C) → LexTriple A B C) := by
  constructor
  · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [flattenTriple, LexTriple.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  · rintro ⟨a, b, c⟩; exact ⟨⟨a, ⟨b, c⟩⟩, rfl⟩

/-- Flatten a doubly-nested pair into a `LexQuadruple` (computable, bijective). -/
@[reducible] def flattenQuad {A B C D : Type*} (p : LexPair A (LexPair B (LexPair C D))) :
    LexQuadruple A B C D := ⟨p.fst, p.snd.fst, p.snd.snd.fst, p.snd.snd.snd⟩

theorem flattenQuad_bijective {A B C D : Type*} :
    Function.Bijective
      (flattenQuad : LexPair A (LexPair B (LexPair C D)) → LexQuadruple A B C D) := by
  constructor
  · rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    simp only [flattenQuad, LexQuadruple.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, ⟨b, ⟨c, d⟩⟩⟩, rfl⟩

/-! ### The tuple generators -/

/-- **The lexicographic triple generator.** Nest `LexPair B C` inside
`LexPair A _` (using `lexPairGenOfFinite_contiguous` to present the inner pair
generator as the finite second component), then relabel to `LexTriple A B C`
via `mapGen flattenTriple`. `B` and `C` are finite (supplied by their
contiguity witnesses `hnone*`/`hsome*`); `A` may be infinite. The last
coordinate varies fastest. -/
@[reducible] def lexTripleGen {A B C : Type*} {cB cC : ℕ} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C)
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none) (hsomeB : ∀ n, n < cB → gB.gen n ≠ none)
    (hnoneC : ∀ n, cC ≤ n → gC.gen n = none) (hsomeC : ∀ n, n < cC → gC.gen n ≠ none) :
    ExhaustiveGenerator (LexTriple A B C) :=
  mapGen flattenTriple flattenTriple_bijective
    (lexPairGenOfFinite gA (lexPairGenOfFinite gB gC hnoneC hsomeC)
      (lexPairGenOfFinite_contiguous gB gC hnoneB hsomeB hnoneC hsomeC).1
      (lexPairGenOfFinite_contiguous gB gC hnoneB hsomeB hnoneC hsomeC).2)

/-- **The lexicographic quadruple generator.** One more nesting level than
`lexTripleGen`: `LexPair C D` inside `LexPair B _` inside `LexPair A _`, then
relabel to `LexQuadruple A B C D`. `B`, `C`, `D` finite; `A` may be infinite. -/
@[reducible] def lexQuadrupleGen {A B C D : Type*} {cB cC cD : ℕ}
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (gC : ExhaustiveGenerator C) (gD : ExhaustiveGenerator D)
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none) (hsomeB : ∀ n, n < cB → gB.gen n ≠ none)
    (hnoneC : ∀ n, cC ≤ n → gC.gen n = none) (hsomeC : ∀ n, n < cC → gC.gen n ≠ none)
    (hnoneD : ∀ n, cD ≤ n → gD.gen n = none) (hsomeD : ∀ n, n < cD → gD.gen n ≠ none) :
    ExhaustiveGenerator (LexQuadruple A B C D) :=
  mapGen flattenQuad flattenQuad_bijective
    (lexPairGenOfFinite gA
      (lexPairGenOfFinite gB (lexPairGenOfFinite gC gD hnoneD hsomeD)
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).1
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).2)
      (lexPairGenOfFinite_contiguous gB (lexPairGenOfFinite gC gD hnoneD hsomeD) hnoneB hsomeB
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).1
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).2).1
      (lexPairGenOfFinite_contiguous gB (lexPairGenOfFinite gC gD hnoneD hsomeD) hnoneB hsomeB
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).1
        (lexPairGenOfFinite_contiguous gC gD hnoneC hsomeC hnoneD hsomeD).2).2)

end ExhaustiveGenerator

/-! ### Counts

Each flat tuple is its `Prod` up to the `equivProd` newtype wrapper, so its
cardinality is the product of the components' cardinalities when all are
finite, and it is infinite when the first component is infinite (and the rest
nonempty). -/

namespace LexTriple

/-- `LexTriple A B C` is infinite when `A` is infinite and `B`, `C` nonempty. -/
instance {A B C : Type*} [Infinite A] [Nonempty B] [Nonempty C] : Infinite (LexTriple A B C) :=
  Infinite.of_injective (fun a => ⟨a, Classical.arbitrary B, Classical.arbitrary C⟩)
    (fun _ _ h => congrArg LexTriple.fst h)

/-- A `Fintype` for `LexTriple A B C` when all three components are finite. -/
instance instFintype {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    Fintype (LexTriple A B C) :=
  Fintype.ofEquiv _ equivProd.symm

/-- The cardinality of `LexTriple A B C` is `|A| * |B| * |C|`. -/
theorem card {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (LexTriple A B C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod, Nat.mul_assoc]

end LexTriple

namespace LexQuadruple

/-- `LexQuadruple A B C D` is infinite when `A` is infinite and `B,C,D` nonempty. -/
instance {A B C D : Type*} [Infinite A] [Nonempty B] [Nonempty C] [Nonempty D] :
    Infinite (LexQuadruple A B C D) :=
  Infinite.of_injective
    (fun a => ⟨a, Classical.arbitrary B, Classical.arbitrary C, Classical.arbitrary D⟩)
    (fun _ _ h => congrArg LexQuadruple.fst h)

/-- A `Fintype` for `LexQuadruple A B C D` when all four components are finite. -/
instance instFintype {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] :
    Fintype (LexQuadruple A B C D) :=
  Fintype.ofEquiv _ equivProd.symm

/-- The cardinality of `LexQuadruple A B C D` is `|A| * |B| * |C| * |D|`. -/
theorem card {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] :
    Fintype.card (LexQuadruple A B C D)
      = Fintype.card A * Fintype.card B * Fintype.card C * Fintype.card D := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Nat.mul_assoc, Nat.mul_assoc]

end LexQuadruple

/-! ### The `ExhaustiveGenerator`/`Contiguous` instances on the flat tuples

These re-express the `lexTripleGen`/`lexQuadrupleGen` `def`s as INSTANCES: the
finiteness/contiguity of the components is now resolved from the `[Fintype] +
[Contiguous]` mixins (via the nested `LexPair` instances) rather than threaded
explicitly. The first component `A` may be infinite; the remaining components
must be finite + contiguous. `Contiguous` of the tuple follows (with
`[Contiguous A]`) from `mapGen_contig_step` over the underlying nested pair. -/

open ExhaustiveGenerator

/-- Lexicographic `ExhaustiveGenerator` on the flat `LexTriple A B C` (last
coordinate fastest); `B`, `C` finite + contiguous, `A` possibly infinite. -/
instance instExhaustiveGeneratorTriple {A B C : Type*} [ExhaustiveGenerator A]
    [ExhaustiveGenerator B] [Fintype B] [Contiguous B]
    [ExhaustiveGenerator C] [Fintype C] [Contiguous C] :
    ExhaustiveGenerator (LexTriple A B C) :=
  mapGen flattenTriple flattenTriple_bijective inferInstance

/-- The triple generator is contiguous when all components are. -/
instance instContiguousTriple {A B C : Type*} [ExhaustiveGenerator A] [Contiguous A]
    [ExhaustiveGenerator B] [Fintype B] [Contiguous B]
    [ExhaustiveGenerator C] [Fintype C] [Contiguous C] :
    Contiguous (LexTriple A B C) :=
  mapGen_contiguous flattenTriple flattenTriple_bijective inferInstance inferInstance

/-- Lexicographic `ExhaustiveGenerator` on the flat `LexQuadruple A B C D`. -/
instance instExhaustiveGeneratorQuadruple {A B C D : Type*} [ExhaustiveGenerator A]
    [ExhaustiveGenerator B] [Fintype B] [Contiguous B]
    [ExhaustiveGenerator C] [Fintype C] [Contiguous C]
    [ExhaustiveGenerator D] [Fintype D] [Contiguous D] :
    ExhaustiveGenerator (LexQuadruple A B C D) :=
  mapGen flattenQuad flattenQuad_bijective inferInstance

/-- The quadruple generator is contiguous when all components are. -/
instance instContiguousQuadruple {A B C D : Type*} [ExhaustiveGenerator A] [Contiguous A]
    [ExhaustiveGenerator B] [Fintype B] [Contiguous B]
    [ExhaustiveGenerator C] [Fintype C] [Contiguous C]
    [ExhaustiveGenerator D] [Fintype D] [Contiguous D] :
    Contiguous (LexQuadruple A B C D) :=
  mapGen_contiguous flattenQuad flattenQuad_bijective inferInstance inferInstance

/-! ### Guards

Two triple enumerations (infinite-first `AzNat × Bool × Bool`, and fully-finite
`Bool × Bool × Bool` which caps at `8`) and the analogous quadruple cases,
confirming lexicographic order with the FIRST coordinate slowest / LAST
fastest. -/

open ExhaustiveGenerator

-- `boolsGen` produces values exactly at positions `0, 1` (`cB = 2`).
private theorem boolsGen_hnone : ∀ n, 2 ≤ n → boolsGen.gen n = none :=
  fun _ h => List.getElem?_eq_none h
private theorem boolsGen_hsome : ∀ n, n < 2 → boolsGen.gen n ≠ none :=
  fun _ h => by
    rw [show boolsGen.gen _ = some _ from List.getElem?_eq_getElem h]; exact Option.some_ne_none _

/-- Infinite-first triple: `AzNat` lex `Bool` lex `Bool`, last coordinate fastest. -/
@[reducible] def natBoolBoolLex : ExhaustiveGenerator (LexTriple AzNat Bool Bool) :=
  lexTripleGen naturalsGen boolsGen boolsGen
    boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome

/-- Fully-finite triple: `Bool × Bool × Bool`; runs out after `8` elements. -/
@[reducible] def boolTripleLex : ExhaustiveGenerator (LexTriple Bool Bool Bool) :=
  lexTripleGen boolsGen boolsGen boolsGen
    boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome

/-- Infinite-first quadruple: `AzNat × Bool × Bool × Bool`. -/
@[reducible] def natBoolBoolBoolLex : ExhaustiveGenerator (LexQuadruple AzNat Bool Bool Bool) :=
  lexQuadrupleGen naturalsGen boolsGen boolsGen boolsGen
    boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome

/-- Fully-finite quadruple: `Bool × Bool × Bool × Bool`; runs out after `16`. -/
@[reducible] def boolQuadrupleLex : ExhaustiveGenerator (LexQuadruple Bool Bool Bool Bool) :=
  lexQuadrupleGen boolsGen boolsGen boolsGen boolsGen
    boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome boolsGen_hnone boolsGen_hsome

-- Triple (a) first 8: first coordinate slowest, last fastest.
#guard (@firstN _ natBoolBoolLex 8).map (fun t => (t.fst.toNat, t.snd, t.thd))
  = [(0, false, false), (0, false, true), (0, true, false), (0, true, true),
     (1, false, false), (1, false, true), (1, true, false), (1, true, true)]

-- Triple (b) all 8 in lex order; caps at 8.
#guard (@firstN _ boolTripleLex 20).map (fun t => (t.fst, t.snd, t.thd))
  = [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
     (true, false, false), (true, false, true), (true, true, false), (true, true, true)]
#guard (@firstN _ boolTripleLex 20).length == 8

-- Quadruple (a) first 16: last coordinate fastest.
#guard (@firstN _ natBoolBoolBoolLex 16).map (fun t => (t.fst.toNat, t.snd, t.thd, t.fth))
  = [(0, false, false, false), (0, false, false, true), (0, false, true, false),
     (0, false, true, true), (0, true, false, false), (0, true, false, true),
     (0, true, true, false), (0, true, true, true), (1, false, false, false),
     (1, false, false, true), (1, false, true, false), (1, false, true, true),
     (1, true, false, false), (1, true, false, true), (1, true, true, false),
     (1, true, true, true)]

-- Quadruple (b) fully finite: caps at 16.
#guard (@firstN _ boolQuadrupleLex 40).length == 16

/-! The same enumerations via the tuple INSTANCES (resolved by `inferInstance`,
no explicit builder/contiguity arguments), confirming instance resolution and
identical lexicographic order. -/

-- Instance-resolved fully-finite triple `Bool × Bool × Bool`: same 8 elements.
#guard (firstN (LexTriple Bool Bool Bool) 20).map (fun t => (t.fst, t.snd, t.thd))
  = [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
     (true, false, false), (true, false, true), (true, true, false), (true, true, true)]
#guard (firstN (LexTriple Bool Bool Bool) 20).length == 8

-- Instance-resolved infinite-first triple `AzNat × Bool × Bool`.
#guard (firstN (LexTriple AzNat Bool Bool) 8).map (fun t => (t.fst.toNat, t.snd, t.thd))
  = [(0, false, false), (0, false, true), (0, true, false), (0, true, true),
     (1, false, false), (1, false, true), (1, true, false), (1, true, true)]

-- Instance-resolved fully-finite quadruple `Bool × Bool × Bool × Bool`: caps at 16.
#guard (firstN (LexQuadruple Bool Bool Bool Bool) 40).length == 16

end Azurite
