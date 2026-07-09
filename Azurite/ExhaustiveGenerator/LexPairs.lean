/-
  `lex_pairs` — lexicographic pair generation (Malachite `lex_pairs`).

  Given an exhaustive generator for `A` (possibly infinite) and a FINITE
  exhaustive generator for `B`, enumerate `A × B` in LEXICOGRAPHIC order, the
  LAST coordinate varying fastest:
    `(a₀,b₀), (a₀,b₁), …, (a₀,b_{cB-1}), (a₁,b₀), …`
  This is a mixed-radix odometer: position `k` maps to `(k / cB, k % cB)` where
  `cB` is the number of `B`-values (`Nat.div_add_mod`). Because the last
  coordinate cycles, `B` must be finite; `A` may be infinite.

  This is the first *compositional* generator: it takes generators and produces
  a new one. The finite component is presented as an ordered enumeration
  `eB : Fin cB → B` together with a bijectivity proof (a plain FUNCTION, not a
  bundled `Equiv`, so that the built generator stays *computable* — the honest
  inverse coming out of `Count.equivFin` is `noncomputable`, which would block
  `#eval`/`#guard`). `lexPairGenOfFinite` supplies this function from `B`'s own
  finite generator, in `B`'s generator order (faithful to Malachite).

  To avoid colliding with the future default `ExhaustiveGenerator (A × B)` (the
  BitDistributor composition, not built yet), the output type is the newtype
  `LexPair A B`, NOT `A × B`.
-/
import Azurite.ExhaustiveGenerator.Count
import Azurite.ExhaustiveGenerator.Enums
import Mathlib.Data.Fintype.Prod

namespace Azurite

/-- A lexicographically-ordered pair: a genuine newtype for `A × B` used as the
output of `lexPairGen`, kept distinct from `A × B` so it can carry its own
(lexicographic) `ExhaustiveGenerator` without clashing with the eventual default
product generator. The last coordinate (`snd`) varies fastest. -/
structure LexPair (A B : Type*) where
  /-- The first (slow) coordinate; may range over an infinite type. -/
  fst : A
  /-- The last (fast) coordinate; must range over a finite type. -/
  snd : B
  deriving DecidableEq

namespace LexPair

/-- The obvious computable equivalence `LexPair A B ≃ A × B`. Lets us borrow
`Prod`'s `Fintype`/cardinality facts for the count lemmas. -/
@[simps] def equivProd {A B : Type*} : LexPair A B ≃ A × B where
  toFun p := (p.fst, p.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LexPair

namespace ExhaustiveGenerator

/-- **The core lexicographic pair generator.** Given a generator `gA` for `A`
and an ordered enumeration `eB : Fin cB → B` of a finite `B` (bijective via
`hbij`), enumerate `LexPair A B` with the last coordinate varying fastest:
position `k` produces `⟨gA(k / cB), eB(k % cB)⟩`. When `cB = 0`, `B` is empty
(`eB` is a bijection out of `Fin 0`), so `LexPair A B` is empty and `gen ≡ none`
(the `dite` takes the `else` branch); the exactly-once obligation is then
vacuous. -/
@[reducible] def lexPairGen {A B : Type*} {cB : ℕ} (gA : ExhaustiveGenerator A)
    (eB : Fin cB → B) (hbij : Function.Bijective eB) :
    ExhaustiveGenerator (LexPair A B) where
  gen k :=
    if h : 0 < cB then
      (gA.gen (k / cB)).map (fun a => ⟨a, eB ⟨k % cB, Nat.mod_lt k h⟩⟩)
    else none
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    rcases Nat.eq_zero_or_pos cB with hcB | hcB
    · subst hcB
      obtain ⟨i, _⟩ := hbij.surjective b
      exact i.elim0
    · obtain ⟨⟨iB, hlt⟩, hiFin⟩ := hbij.surjective b
      refine ⟨iA * cB + iB, ?_, ?_⟩
      · -- Existence: the odometer decodes `iA * cB + iB` back to `(iA, iB)`.
        have hdiv : (iA * cB + iB) / cB = iA := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hcB, Nat.div_eq_of_lt hlt, Nat.zero_add]
        have hmod : (iA * cB + iB) % cB = iB := by
          rw [Nat.mul_comm iA cB, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
        have hb : eB ⟨(iA * cB + iB) % cB, Nat.mod_lt _ hcB⟩ = b := by
          rw [show (⟨(iA * cB + iB) % cB, Nat.mod_lt _ hcB⟩ : Fin cB) = ⟨iB, hlt⟩ from
            Fin.ext hmod, hiFin]
        beta_reduce
        rw [dif_pos hcB, hdiv, hiA, Option.map_some, hb]
      · -- Uniqueness: any producing position decodes to `(iA, iB)`.
        rintro m hm
        rw [dif_pos hcB] at hm
        rcases hga : gA.gen (m / cB) with _ | a'
        · rw [hga] at hm; simp at hm
        · rw [hga, Option.map_some] at hm
          have hfst : a' = a := congrArg LexPair.fst (Option.some.inj hm)
          have hsnd : eB ⟨m % cB, Nat.mod_lt m hcB⟩ = b := congrArg LexPair.snd (Option.some.inj hm)
          have hdivm : m / cB = iA := huA _ (hga.trans (by rw [hfst]))
          have hmodm : m % cB = iB := by
            have hfin : (⟨m % cB, Nat.mod_lt m hcB⟩ : Fin cB) = ⟨iB, hlt⟩ :=
              hbij.injective (hsnd.trans hiFin.symm)
            exact congrArg Fin.val hfin
          calc m = cB * (m / cB) + m % cB := (Nat.div_add_mod m cB).symm
            _ = iA * cB + iB := by rw [hdivm, hmodm, Nat.mul_comm]

/-- **Convenience builder.** Present `B`'s FINITE generator `gB` as the ordered
enumeration `Fin cB → B` (in `B`'s own generator order — faithful to Malachite:
`i ↦ (gB.gen i).get`), then feed it to `lexPairGen`. The `hnoneB` / `hsomeB`
hypotheses say `gB` produces values exactly at positions `0, …, cB-1`; all of
Azurite's finite generators have this contiguous-`some` shape, so they satisfy
them out of the box. The enumeration function is spelled out explicitly (rather
than reusing the `noncomputable` `equivFin`) so this builder stays computable;
its bijectivity is borrowed from `equivFin.symm`. -/
@[reducible] def lexPairGenOfFinite {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) {cB : ℕ}
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none)
    (hsomeB : ∀ n, n < cB → gB.gen n ≠ none) : ExhaustiveGenerator (LexPair A B) :=
  lexPairGen gA (fun i : Fin cB => (gB.gen i.val).get (Option.isSome_iff_ne_none.mpr (hsomeB i.val i.isLt)))
    (@equivFin B gB cB hnoneB hsomeB).symm.bijective

/-- **Contiguity is preserved by `lexPairGen`.** If the first generator `gA` is
*contiguous* (produces values exactly at positions `0, …, cA-1`) and the finite
second component has `cB` values, then the composed pair generator is again
contiguous, with bound `cA * cB`: position `k` produces a value iff `k < cA*cB`.
The `else` (`cB = 0`) branch makes `gen ≡ none` and `cA * 0 = 0`, so both halves
hold vacuously. This lets a nested `lexPairGen` be re-fed as the *finite* second
argument of an outer `lexPairGen` (the basis for tuple generators). Note the
enumeration function `eB`/`hbij` is irrelevant to contiguity — only `cA`, `cB`,
and `gA`'s shape matter. -/
theorem lexPairGen_contiguous {A B : Type*} {cA cB : ℕ} (gA : ExhaustiveGenerator A)
    (eB : Fin cB → B) (hbij : Function.Bijective eB)
    (hnoneA : ∀ n, cA ≤ n → gA.gen n = none)
    (hsomeA : ∀ n, n < cA → gA.gen n ≠ none) :
    (∀ n, cA * cB ≤ n → (lexPairGen gA eB hbij).gen n = none) ∧
    (∀ n, n < cA * cB → (lexPairGen gA eB hbij).gen n ≠ none) := by
  constructor
  · intro n hn
    show (if h : 0 < cB then _ else none) = none
    rcases Nat.eq_zero_or_pos cB with hcB | hcB
    · rw [dif_neg (by omega)]
    · rw [dif_pos hcB, hnoneA (n / cB) ((Nat.le_div_iff_mul_le hcB).mpr hn), Option.map_none]
  · intro n hn
    have hcB : 0 < cB := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    show (if h : 0 < cB then _ else none) ≠ none
    rw [dif_pos hcB]
    have hlt : n / cB < cA := (Nat.div_lt_iff_lt_mul hcB).mpr hn
    rcases hga : gA.gen (n / cB) with _ | a
    · exact absurd hga (hsomeA (n / cB) hlt)
    · rw [Option.map_some]; exact Option.some_ne_none _

/-- **Contiguity of `lexPairGenOfFinite`.** The `OfFinite` builder is
`lexPairGen` with the finite second component presented in `gB`'s own order; it
inherits contiguity (bound `cA * cB`) directly from `lexPairGen_contiguous`. This
is the exact interface the nested tuple builders consume: it takes the same
contiguity witnesses used to *construct* the generator and returns the composed
contiguity. -/
theorem lexPairGenOfFinite_contiguous {A B : Type*} {cA cB : ℕ}
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (hnoneA : ∀ n, cA ≤ n → gA.gen n = none) (hsomeA : ∀ n, n < cA → gA.gen n ≠ none)
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none) (hsomeB : ∀ n, n < cB → gB.gen n ≠ none) :
    (∀ n, cA * cB ≤ n → (lexPairGenOfFinite gA gB hnoneB hsomeB).gen n = none) ∧
    (∀ n, n < cA * cB → (lexPairGenOfFinite gA gB hnoneB hsomeB).gen n ≠ none) :=
  lexPairGen_contiguous gA _ _ hnoneA hsomeA

/-- **`lexPairGen` preserves the `contig` step.** If the first generator `gA`
satisfies the raw `contig`-step (`none` at `n` forces `none` at `n+1`), so does
the composed pair generator — regardless of the enumeration `eB`/bound `cB`.
When `cB = 0` the generator is constantly `none` (trivial); otherwise a `none`
at `k` means `gA.gen (k / cB) = none`, and since `(k+1) / cB ≥ k / cB`, monotone
`none`-propagation (`gen_none_of_le_step`) gives `gA.gen ((k+1) / cB) = none`,
hence `none` at `k+1`. This is exactly what the `Contiguous (LexPair A B)`
instance needs (no cardinality bookkeeping). -/
theorem lexPairGen_contig_step {A B : Type*} {cB : ℕ} (gA : ExhaustiveGenerator A)
    (eB : Fin cB → B) (hbij : Function.Bijective eB)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) :
    ∀ k, (lexPairGen gA eB hbij).gen k = none → (lexPairGen gA eB hbij).gen (k + 1) = none := by
  intro k h
  rcases Nat.eq_zero_or_pos cB with hcB | hcB
  · subst hcB
    show (if h : 0 < 0 then _ else none) = none
    rw [dif_neg (lt_irrefl 0)]
  · -- Extract `gA.gen (k / cB) = none` from the `none` at `k`.
    have hk : (lexPairGen gA eB hbij).gen k
        = (gA.gen (k / cB)).map (fun a => (⟨a, eB ⟨k % cB, Nat.mod_lt k hcB⟩⟩ : LexPair A B)) := by
      show (if h : 0 < cB then _ else none) = _
      rw [dif_pos hcB]
    rw [hk, Option.map_eq_none_iff] at h
    -- Propagate to `(k+1) / cB ≥ k / cB`, then repackage as `none` at `k+1`.
    show (if h : 0 < cB then (gA.gen ((k + 1) / cB)).map _ else none) = none
    rw [dif_pos hcB, Option.map_eq_none_iff]
    exact gen_none_of_le_step gA hA (Nat.div_le_div_right (Nat.le_succ k)) h

/-- `contig`-step form for `lexPairGenOfFinite` (the shape the `Contiguous`
instance consumes): inherited from `lexPairGen_contig_step`. Stated over
`lexPairGenOfFinite` verbatim so the `Contiguous (LexPair A B)` instance body
matches the `ExhaustiveGenerator (LexPair A B)` instance definitionally. -/
theorem lexPairGenOfFinite_contig_step {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) {cB : ℕ}
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none) (hsomeB : ∀ n, n < cB → gB.gen n ≠ none)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) :
    ∀ k, (lexPairGenOfFinite gA gB hnoneB hsomeB).gen k = none →
      (lexPairGenOfFinite gA gB hnoneB hsomeB).gen (k + 1) = none :=
  lexPairGen_contig_step gA _ _ hA

/-- **`lexPairGenOfFinite`'s `gen` does not depend on the finiteness
witnesses.** Any two presentations of `B`'s bound (`cB = cB'`, with whatever
`hnone`/`hsome` proofs) produce the same `gen`: after `subst`, the remaining
difference is proofs, and proof irrelevance makes the two generators
definitionally equal. This is the radix-rewriting glue between the
`FiniteGenerator`-literal instance path and any other witness presentation
(e.g. the `Fintype.card`-based `finiteBound_none`/`finiteBound_some`). -/
theorem lexPairGenOfFinite_gen_irrel {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) {cB cB' : ℕ}
    (hnoneB : ∀ n, cB ≤ n → gB.gen n = none) (hsomeB : ∀ n, n < cB → gB.gen n ≠ none)
    (hnoneB' : ∀ n, cB' ≤ n → gB.gen n = none) (hsomeB' : ∀ n, n < cB' → gB.gen n ≠ none)
    (hc : cB = cB') :
    (lexPairGenOfFinite gA gB hnoneB hsomeB).gen
      = (lexPairGenOfFinite gA gB hnoneB' hsomeB').gen := by
  subst hc; rfl

end ExhaustiveGenerator

/-! ### Counts

`LexPair A B` is `A × B` up to the `equivProd` newtype wrapper, so its
cardinality is `|A| * |B|` when both are finite (and the finite `cB` from a
generator equals `|B|` by `fintypeCard_eq`). When `A` is infinite and `B`
nonempty, `LexPair A B` is infinite. -/

namespace LexPair

/-- `LexPair A B` is infinite when `A` is infinite and `B` is nonempty: the map
`a ↦ ⟨a, b₀⟩` is injective. -/
instance {A B : Type*} [Infinite A] [Nonempty B] : Infinite (LexPair A B) :=
  Infinite.of_injective (fun a => ⟨a, Classical.arbitrary B⟩)
    (fun _ _ h => congrArg LexPair.fst h)

/-- A `Fintype` for `LexPair A B` when both components are finite. -/
instance instFintype {A B : Type*} [Fintype A] [Fintype B] : Fintype (LexPair A B) :=
  Fintype.ofEquiv _ equivProd.symm

/-- The cardinality of `LexPair A B` is the product `|A| * |B|`. -/
theorem card {A B : Type*} [Fintype A] [Fintype B] :
    Fintype.card (LexPair A B) = Fintype.card A * Fintype.card B := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod]

end LexPair

/-! ### The `ExhaustiveGenerator`/`Contiguous`/`FiniteGenerator` instances on `LexPair`

With `[FiniteGenerator B]` supplying the finite bound as a LITERAL plus its
`gen_none`/`gen_some` witnesses, the lexicographic pair generator becomes a
genuine COMPUTABLE `ExhaustiveGenerator (LexPair A B)` INSTANCE (the
deliverable): the FIRST component `A` may be infinite, while the LAST component
`B` must have a finite generator (its `FiniteGenerator.card` literal is the
odometer's runtime radix `cB`). Computability is exactly why the class carries
the bound as data — the noncomputable `Fintype.card B` route would poison
`#eval`/`#guard` (and even a computable `Fintype.card` is runtime-infeasible
for the big fixed-width types). When `A` is additionally contiguous, so is the
pair (via `lexPairGen_contig_step`); when `A` is also finite, the pair is a
`FiniteGenerator` with `card = card A * card B`, so pairs compose further. -/

open ExhaustiveGenerator in
/-- Lexicographic `ExhaustiveGenerator` on the newtype `LexPair A B` (last
coordinate fastest); `A` may be infinite, `B` must have a finite generator. -/
instance instExhaustiveGeneratorLexPair {A B : Type*} [ExhaustiveGenerator A]
    [ExhaustiveGenerator B] [FiniteGenerator B] : ExhaustiveGenerator (LexPair A B) :=
  lexPairGenOfFinite inferInstance inferInstance
    FiniteGenerator.gen_none FiniteGenerator.gen_some

open ExhaustiveGenerator in
/-- The lex pair generator is contiguous when the first component is (needed so
a `LexPair` with infinite `A` can still feed the dependent/`mapGen` layers; for
finite `A` the `FiniteGenerator` instance below subsumes this via
`FiniteGenerator.toContiguous`). -/
instance instContiguousLexPair {A B : Type*} [ExhaustiveGenerator A] [Contiguous A]
    [ExhaustiveGenerator B] [FiniteGenerator B] : Contiguous (LexPair A B) :=
  ⟨lexPairGenOfFinite_contig_step inferInstance inferInstance
    FiniteGenerator.gen_none FiniteGenerator.gen_some (fun n => Contiguous.contig n)⟩

open ExhaustiveGenerator in
/-- The lex pair generator is finite with `card = card A * card B` when both
components are — this is what lets a `LexPair` serve as the finite LAST
component of a further composition. -/
instance instFiniteGeneratorLexPair {A B : Type*} [ExhaustiveGenerator A] [FiniteGenerator A]
    [ExhaustiveGenerator B] [FiniteGenerator B] : FiniteGenerator (LexPair A B) where
  card := FiniteGenerator.card (T := A) * FiniteGenerator.card (T := B)
  gen_none := (lexPairGenOfFinite_contiguous inferInstance inferInstance
    FiniteGenerator.gen_none FiniteGenerator.gen_some
    FiniteGenerator.gen_none FiniteGenerator.gen_some).1
  gen_some := (lexPairGenOfFinite_contiguous inferInstance inferInstance
    FiniteGenerator.gen_none FiniteGenerator.gen_some
    FiniteGenerator.gen_none FiniteGenerator.gen_some).2

open ExhaustiveGenerator in
/-- The instance path (`FiniteGenerator`-literal radix) and the classic
`Fintype`-witness builder path produce the SAME enumeration: the radix rewrite
is `fintypeCard_eq_finiteCard` through `lexPairGenOfFinite_gen_irrel`. -/
theorem instExhaustiveGeneratorLexPair_gen_eq {A B : Type*} [ExhaustiveGenerator A]
    [ExhaustiveGenerator B] [FiniteGenerator B] [Fintype B] [Contiguous B] :
    (instExhaustiveGeneratorLexPair (A := A) (B := B)).gen
      = (lexPairGenOfFinite inferInstance inferInstance
          finiteBound_none finiteBound_some).gen :=
  lexPairGenOfFinite_gen_irrel inferInstance inferInstance
    FiniteGenerator.gen_none FiniteGenerator.gen_some
    finiteBound_none finiteBound_some fintypeCard_eq_finiteCard.symm

/-! ### Guards

Two lexicographic enumerations, rendered by mapping `LexPair` through its
components. Case (a) is infinite-first (`AzNat × Bool`); case (b) is
finite × finite (`Bool × Bool`), which runs out after `4` elements. -/

open ExhaustiveGenerator

/-- (a) Infinite-first: `AzNat` lex `Bool`, last coordinate fastest. The
`hnone`/`hsome` witnesses come straight off `Bool`'s `FiniteGenerator`. -/
@[reducible] def natBoolLex : ExhaustiveGenerator (LexPair AzNat Bool) :=
  lexPairGenOfFinite naturalsGen boolsGen FiniteGenerator.gen_none FiniteGenerator.gen_some

/-- (b) Finite × finite: `Bool` lex `Bool`; runs out after `4` elements. -/
@[reducible] def boolBoolLex : ExhaustiveGenerator (LexPair Bool Bool) :=
  lexPairGenOfFinite boolsGen boolsGen FiniteGenerator.gen_none FiniteGenerator.gen_some

-- (a) first 6: (0,F),(0,T),(1,F),(1,T),(2,F),(2,T).
#guard (@firstN _ natBoolLex 6).map (fun p => (p.fst.toNat, p.snd))
  = [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

-- (b) all 4: (F,F),(F,T),(T,F),(T,T); then none, so length caps at 4.
#guard (@firstN _ boolBoolLex 10).map (fun p => (p.fst, p.snd))
  = [(false, false), (false, true), (true, false), (true, true)]
#guard (@firstN _ boolBoolLex 10).length == 4

/-! The same enumerations via the `ExhaustiveGenerator (LexPair ·) ·` INSTANCE
(resolved by `inferInstance`, no explicit builder arguments), confirming the
instance produces the identical lexicographic order. -/

-- Instance-resolved `Bool` lex `Bool`: same 4 elements as `boolBoolLex`.
#guard (firstN (LexPair Bool Bool) 10).map (fun p => (p.fst, p.snd))
  = [(false, false), (false, true), (true, false), (true, true)]
#guard (firstN (LexPair Bool Bool) 10).length == 4

-- Instance-resolved infinite-first `AzNat` lex `Bool` (radix from `FiniteGenerator Bool`).
#guard (firstN (LexPair AzNat Bool) 6).map (fun p => (p.fst.toNat, p.snd))
  = [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

-- Instance-resolved `Ordering` lex `Bool`: 3 * 2 = 6 elements, last fastest.
#guard (firstN (LexPair Ordering Bool) 10).map (fun p => (p.fst, p.snd))
  = [(.lt, false), (.lt, true), (.eq, false), (.eq, true), (.gt, false), (.gt, true)]

/-! Components whose old `Fintype`-based instances were NONCOMPUTABLE (the
`fintypeOfBounded`-derived `RoundingMode`/`UIntX` instances): with the bound now
a `FiniteGenerator` literal, these must genuinely `#eval`. -/

-- Instance-resolved `Bool` lex `RoundingMode`: all 2 * 5 = 10 elements.
#guard (firstN (LexPair Bool RoundingMode) 12).map (fun p => (p.fst, p.snd))
  = [(false, .Down), (false, .Up), (false, .Floor), (false, .Ceiling), (false, .Nearest),
     (true, .Down), (true, .Up), (true, .Floor), (true, .Ceiling), (true, .Nearest)]
#guard (firstN (LexPair Bool RoundingMode) 12).length == 10

-- Instance-resolved infinite-first `AzNat` lex `UInt8` (radix `2^8`).
#guard (firstN (LexPair AzNat UInt8) 5).map (fun p => (p.fst.toNat, p.snd.toNat))
  = [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

end Azurite
