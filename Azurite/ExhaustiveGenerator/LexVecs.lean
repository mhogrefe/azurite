/-
  `lex_vecs_fixed_length` — lexicographic enumeration of all fixed-length vecs
  over a finite type (Malachite `lex_vecs_fixed_length` /
  `lex_vecs_fixed_length_from_single`).

  Given an exhaustive generator for a FINITE type `T`, enumerate all length-`n`
  vecs `[t₀, …, t_{n-1}]` over `T` in LEXICOGRAPHIC order — position `0` slowest,
  position `n-1` fastest. Building the enumeration from a SINGLE generator for
  all positions forces `T` to be finite: for `n ≥ 2` the non-first positions
  reuse the generator and must run out (Malachite: "`xs` must be finite"). The
  explicit builder takes `T`'s finite bound `cT` with its witnesses; the
  INSTANCE is gated on `[FiniteGenerator T]` (whose literal `card` keeps the
  enumeration computable), giving `cT ^ n` vecs (`n = 0` ⇒ the single empty
  vec; `n = 1` ⇒ the `T` values).

  We take the RECURSIVE route on `n`, reusing `lexPairGen`'s proven odometer
  wholesale (no fresh mixed-radix arithmetic): the length-`(n+1)` generator is
  `mapGen cons (lexPairGen T (LexVec T n))` — head slowest (first coordinate),
  the length-`n` tail as the FINITE second component. The tail is finite +
  contiguous, so `lexPairGenOfFinite`/`lexPairGenOfFinite_contiguous` apply. The
  per-level finite bounds (`(card T) ^ n` positions produce values) are threaded
  through the recursion in the bundled `LexVecData`, so each step can present the
  previous generator as the finite argument of the next.

  As with `LexPair`, the output is a genuine newtype `LexVec T n` wrapping
  `List.Vector T n`, kept distinct from the bare vec type so it can carry its own
  (lexicographic) `ExhaustiveGenerator` without clashing with any future default.
-/
import Azurite.ExhaustiveGenerator.LexPairs
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

namespace Azurite

/-- A lexicographically-ordered fixed-length vec: a newtype for `List.Vector T n`
(`= {l : List T // l.length = n}`), kept distinct from the bare vec type so it
can carry its own lexicographic `ExhaustiveGenerator`. The FIRST coordinate is
slowest, the LAST varies fastest; `T` must be finite. -/
structure LexVec (T : Type*) (n : ℕ) where
  /-- The underlying length-`n` vec. -/
  val : List.Vector T n
deriving DecidableEq

namespace LexVec

/-- The obvious computable equivalence `LexVec T n ≃ List.Vector T n`. Lets us
borrow `List.Vector`'s `Fintype`/cardinality facts. -/
@[simps] def equivVector {T : Type*} {n : ℕ} : LexVec T n ≃ List.Vector T n where
  toFun := LexVec.val
  invFun := LexVec.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `Fintype` for `LexVec T n` when `T` is finite. -/
instance instFintype {T : Type*} [Fintype T] {n : ℕ} : Fintype (LexVec T n) :=
  Fintype.ofEquiv _ equivVector.symm

/-- The cardinality of `LexVec T n` is `(Fintype.card T) ^ n`. -/
theorem card {T : Type*} [Fintype T] {n : ℕ} :
    Fintype.card (LexVec T n) = (Fintype.card T) ^ n := by
  rw [Fintype.card_congr equivVector, card_vector]

/-- Every length-`0` vec is the empty vec (`List.Vector.eq_nil`). -/
theorem eq_zero {T : Type*} (t : LexVec T 0) : t = ⟨List.Vector.nil⟩ := by
  obtain ⟨v⟩ := t; rw [v.eq_nil]

end LexVec

namespace ExhaustiveGenerator

/-- Prepend a head to a length-`n` vec, giving a length-`(n+1)` vec. This is the
computable flattening bijection `LexPair T (LexVec T n) → LexVec T (n+1)` (head =
first/slowest coordinate). -/
@[reducible] def consVec {T : Type*} {n : ℕ} (p : LexPair T (LexVec T n)) :
    LexVec T (n + 1) := ⟨p.fst ::ᵥ p.snd.val⟩

theorem consVec_bijective {T : Type*} {n : ℕ} :
    Function.Bijective (consVec : LexPair T (LexVec T n) → LexVec T (n + 1)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun p => ⟨p.val.head, ⟨p.val.tail⟩⟩,
     fun p => by
       obtain ⟨a, ⟨v⟩⟩ := p
       show (⟨(a ::ᵥ v).head, ⟨(a ::ᵥ v).tail⟩⟩ : LexPair T (LexVec T n)) = ⟨a, ⟨v⟩⟩
       rw [List.Vector.head_cons, List.Vector.tail_cons],
     fun p => by
       obtain ⟨v⟩ := p
       exact congrArg LexVec.mk (List.Vector.cons_head_tail v)⟩

/-- **Bundled recursion carrier.** A length-`n` vec generator together with its
finite bounds: values are produced exactly at positions `0, …, cT^n - 1`, where
`cT` is the bound of `T`'s own generator. Threading the bounds through the
recursion is what lets each step present the previous (length-`n`) generator as
the FINITE second component of the next `lexPairGenOfFinite`. -/
structure LexVecData (T : Type*) (cT : ℕ) (n : ℕ) where
  /-- The length-`n` vec generator. -/
  gen : ExhaustiveGenerator (LexVec T n)
  /-- Positions at or beyond `cT ^ n` produce `none`. -/
  hnone : ∀ k, cT ^ n ≤ k → gen.gen k = none
  /-- Positions below `cT ^ n` produce a value. -/
  hsome : ∀ k, k < cT ^ n → gen.gen k ≠ none

/-- The finite bounds make the bundled generator contiguous (a `none` at `k`
means `k ≥ cT^n`, so `k+1 ≥ cT^n` is `none` too). -/
theorem LexVecData.contiguous {T : Type*} {cT n : ℕ} (d : LexVecData T cT n) :
    @Contiguous _ d.gen := by
  refine @Contiguous.mk (LexVec T n) d.gen (fun k h => d.hnone (k + 1) ?_)
  by_contra hlt
  exact d.hsome k (by omega) h

/-- **The recursive length-`n` vec generator with bounds.** `n = 0` is the single
empty vec; `n+1` nests `LexVec T n` (finite, by the induction bounds) as the fast
component of `lexPairGen g _`, relabeled to a `LexVec T (n+1)` via `consVec`. The
first coordinate (head) is slowest; the last varies fastest. `g` is the generator
for `T`, presented (per the builder convention) with explicit finiteness
witnesses `hnone`/`hsome` for its bound `cT`. -/
def lexVecData {T : Type*} (g : ExhaustiveGenerator T) {cT : ℕ}
    (hnone : ∀ k, cT ≤ k → g.gen k = none) (hsome : ∀ k, k < cT → g.gen k ≠ none) :
    (n : ℕ) → LexVecData T cT n
  | 0 =>
    let G : ExhaustiveGenerator (LexVec T 0) :=
      ofListNodup [⟨List.Vector.nil⟩] (by simp)
        (fun t => by rw [LexVec.eq_zero t]; exact List.mem_singleton_self _)
    { gen := G
      hnone := fun k hk => by
        rw [pow_zero] at hk
        exact List.getElem?_eq_none (by simpa using hk)
      hsome := fun k hk => by
        rw [pow_zero] at hk
        rw [show G.gen k = some _ from List.getElem?_eq_getElem (by simpa using hk)]
        exact Option.some_ne_none _ }
  | n + 1 =>
    let prev := lexVecData g hnone hsome n
    let pair := lexPairGenOfFinite g prev.gen prev.hnone prev.hsome
    have hc := lexPairGenOfFinite_contiguous g prev.gen
      hnone hsome prev.hnone prev.hsome
    { gen := mapGen consVec consVec_bijective pair
      hnone := fun k hk => by
        show (pair.gen k).map consVec = none
        rw [Option.map_eq_none_iff]
        exact hc.1 k (by rw [Nat.mul_comm, ← pow_succ]; exact hk)
      hsome := fun k hk => by
        show (pair.gen k).map consVec ≠ none
        rw [Ne, Option.map_eq_none_iff]
        exact hc.2 k (by rw [Nat.mul_comm, ← pow_succ]; exact hk) }

/-- **The lexicographic fixed-length vec generator** (Malachite
`lex_vecs_fixed_length_from_single`): all length-`n` vecs over the finite type
`T`, first coordinate slowest / last fastest. `g` is `T`'s generator, with
explicit witnesses that it is finite with bound `cT` (builder convention:
explicit builders take explicit witnesses, no instance constraints on the
explicit `g`). Extracted from the bundled `lexVecData`. -/
@[reducible] def lexVecsFixedLength {T : Type*} (n : ℕ) (g : ExhaustiveGenerator T)
    {cT : ℕ} (hnone : ∀ k, cT ≤ k → g.gen k = none)
    (hsome : ∀ k, k < cT → g.gen k ≠ none) : ExhaustiveGenerator (LexVec T n) :=
  (lexVecData g hnone hsome n).gen

end ExhaustiveGenerator

/-! ### The `ExhaustiveGenerator`/`FiniteGenerator` instances on `LexVec`

With `[FiniteGenerator T]`, the fixed-length vec generator becomes a genuine
computable `ExhaustiveGenerator (LexVec T n)` INSTANCE, itself a
`FiniteGenerator` with `card = (card T) ^ n` — so a `LexVec` can serve as a
finite component of further compositions (and `Contiguous (LexVec T n)` follows
via `FiniteGenerator.toContiguous`). -/

open ExhaustiveGenerator

/-- Lexicographic `ExhaustiveGenerator` on `LexVec T n` (first coordinate
slowest, last fastest); `T` must have a finite generator. -/
instance instExhaustiveGeneratorLexVec {T : Type*} {n : ℕ} [inst : ExhaustiveGenerator T]
    [FiniteGenerator T] : ExhaustiveGenerator (LexVec T n) :=
  lexVecsFixedLength n inst FiniteGenerator.gen_none FiniteGenerator.gen_some

/-- The fixed-length vec generator is finite with `card = (card T) ^ n`. -/
instance instFiniteGeneratorLexVec {T : Type*} {n : ℕ} [inst : ExhaustiveGenerator T]
    [FiniteGenerator T] : FiniteGenerator (LexVec T n) where
  card := (FiniteGenerator.card (T := T)) ^ n
  gen_none := (lexVecData inst FiniteGenerator.gen_none FiniteGenerator.gen_some n).hnone
  gen_some := (lexVecData inst FiniteGenerator.gen_none FiniteGenerator.gen_some n).hsome

/-! ### Guards

Lexicographic enumerations rendered by `.val.toList`. `Bool` (`card 2`) at
lengths `0`–`3` and `Ordering` (`card 3`) at length `2`, each capping at
`(card T) ^ n`, confirm the first coordinate is slowest / the last fastest. -/

open ExhaustiveGenerator

-- Length 2 over `Bool`: `2 ^ 2 = 4` vecs in lex order; caps at 4.
#guard (firstN (LexVec Bool 2) 10).map (fun v => v.val.toList)
  = [[false, false], [false, true], [true, false], [true, true]]
#guard (firstN (LexVec Bool 2) 10).length == 4

-- Length 3 over `Bool`: `2 ^ 3 = 8` vecs in lex order; caps at 8.
#guard (firstN (LexVec Bool 3) 20).map (fun v => v.val.toList)
  = [[false, false, false], [false, false, true], [false, true, false], [false, true, true],
     [true, false, false], [true, false, true], [true, true, false], [true, true, true]]
#guard (firstN (LexVec Bool 3) 20).length == 8

-- Length 0: the single empty vec.
#guard (firstN (LexVec Bool 0) 10).map (fun v => v.val.toList) = [[]]
#guard (firstN (LexVec Bool 0) 10).length == 1

-- Length 1: the `T` values.
#guard (firstN (LexVec Bool 1) 10).map (fun v => v.val.toList) = [[false], [true]]
#guard (firstN (LexVec Bool 1) 10).length == 2

-- Length 2 over the 3-element `Ordering`: `3 ^ 2 = 9` vecs in lex order; caps at 9.
#guard (firstN (LexVec Ordering 2) 20).map (fun v => v.val.toList)
  = [[.lt, .lt], [.lt, .eq], [.lt, .gt], [.eq, .lt], [.eq, .eq], [.eq, .gt],
     [.gt, .lt], [.gt, .eq], [.gt, .gt]]
#guard (firstN (LexVec Ordering 2) 20).length == 9

-- The explicit builder produces the identical order as the instance.
#guard (@firstN _
    (lexVecsFixedLength 2 boolsGen FiniteGenerator.gen_none FiniteGenerator.gen_some) 10).map
    (fun v => v.val.toList)
  = [[false, false], [false, true], [true, false], [true, true]]

-- A previously-poisoned component type (`UInt8`'s old `Fintype` was
-- noncomputable): length-2 vecs over `UInt8`, radix `2^8` per position.
#guard (firstN (LexVec UInt8 2) 10).map (fun v => v.val.toList.map (·.toNat))
  = [[0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8], [0, 9]]

-- Composite of composites: an infinite-first pair whose finite component is
-- itself a composite (`LexVec Bool 2`, card `4`).
#guard (firstN (LexPair AzNat (LexVec Bool 2)) 5).map
    (fun p => (p.fst.toNat, p.snd.val.toList))
  = [(0, [false, false]), (0, [false, true]), (0, [true, false]), (0, [true, true]),
     (1, [false, false])]

end Azurite
