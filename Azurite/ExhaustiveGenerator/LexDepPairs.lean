/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `lex_dependent_pairs` — lexicographic DEPENDENT-pair generation (Malachite
  `lex_dependent_pairs`).

  Generates dependent pairs `⟨a, b⟩ : Σ (a : A), B a` where the SECOND
  component's TYPE `B a` depends on the first component's VALUE `a`. For each `a`
  produced by a generator of `A` (possibly infinite, the SLOWEST coordinate),
  a finite `a`-specific block of `B a`-values is enumerated, then the next `a` —
  lexicographic with `a` slowest. Block sizes VARY per `a` ("ragged"): the
  odometer is a RAGGED prefix sum rather than a fixed-radix one (`lexPairGen`).

  The output type is the dependent-pair newtype `LexDepPair A B` (kept distinct
  from `Sigma B` so it can carry its own lexicographic generator, mirroring how
  `LexPair` is kept distinct from `A × B`).

  Each per-`a` block is packaged computably as a `DepFinGen`: a `card`, a proof
  `0 < card` (blocks are REQUIRED nonempty — see the termination note), a
  computable enumeration `enum : Fin card → B a`, and a `Prop`-level bijectivity
  proof `bij`. Faithful to the STANDING RULE: the finite component travels as a
  plain COMPUTABLE `Fin card → B a` function plus a `Prop` bijectivity witness,
  never a `noncomputable` bundled `Equiv`, so `#guard`s compute.

  **Termination.** The gen walks `i = 0, 1, 2, …` accumulating the prefix sum
  `S(i) = Σ_{j<i} card(dB aⱼ)` and stops when `gA.gen i = none` (⇒ `none`) or
  when the target index `k` lands in block `i` (`S(i) ≤ k < S(i+1)`). Because
  every block is nonempty (`0 < card`), the "remaining index" strictly
  decreases at each step while `gA` is `some`, so fuel `k + 1` always resolves
  the search. Empty blocks are NOT handled generally (they would break the
  strict-decrease termination and prefix-sum monotonicity); the target use
  (degree × length-n coefficient vectors) has every block nonempty.

  **Contiguity requirement.** Since the walk STOPS at the first `gA.gen i =
  none`, the first generator `gA` must be `Contiguous` (once `none`, always
  `none`) for the enumeration to reach every `a`: a `none` gap before a later
  `some` block would truncate the walk. `Contiguous A` is exactly this
  hypothesis; every Azurite base generator satisfies it.
-/
import Azurite.ExhaustiveGenerator.Basic
import Azurite.ExhaustiveGenerator.Enums
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace Azurite

/-- A lexicographically-ordered DEPENDENT pair: a newtype for `Σ (a : A), B a`,
kept distinct from `Sigma B` so it can carry its own (ragged) lexicographic
`ExhaustiveGenerator`. The first coordinate (`fst : A`) is slowest; the second
(`snd : B fst`) ranges over the finite `fst`-specific block. -/
structure LexDepPair (A : Type*) (B : A → Type*) where
  /-- The first (slow) coordinate; may range over an infinite type. -/
  fst : A
  /-- The last (fast) coordinate; ranges over the finite block `B fst`. -/
  snd : B fst

namespace LexDepPair

/-- The obvious computable equivalence `LexDepPair A B ≃ Σ (a : A), B a`. Lets us
borrow `Sigma`'s `Fintype`/cardinality facts for the count lemmas. -/
@[simps] def equivSigma {A : Type*} {B : A → Type*} : LexDepPair A B ≃ Σ (a : A), B a where
  toFun p := ⟨p.fst, p.snd⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `DecidableEq` for `LexDepPair A B` when `A` and each fiber `B a` have it
(via the `Sigma` equivalence). -/
instance instDecidableEq {A : Type*} {B : A → Type*} [DecidableEq A] [∀ a, DecidableEq (B a)] :
    DecidableEq (LexDepPair A B) :=
  fun p q => decidable_of_iff (equivSigma p = equivSigma q) equivSigma.injective.eq_iff

end LexDepPair

/-- A computable finite enumeration of the `a`-specific block `B a`: its size
`card` (REQUIRED nonempty via `pos`), an explicit ordered enumeration
`enum : Fin card → B a`, and a `Prop`-level bijectivity witness `bij`. This is
the per-`a` data consumed by `lexDepPairGen`. Kept as a plain function + `Prop`
(not a bundled `Equiv`) so the built generator stays computable. -/
structure DepFinGen {A : Type*} (B : A → Type*) (a : A) where
  /-- The number of values in the `a`-specific block. -/
  card : ℕ
  /-- Blocks are required nonempty (needed for termination of the odometer). -/
  pos : 0 < card
  /-- The ordered enumeration of the block. -/
  enum : Fin card → B a
  /-- The enumeration is a bijection onto `B a`. -/
  bij : Function.Bijective enum

/-- The block size is honest: `card` equals the fiber's cardinality (one line
from the block bijection `enum : Fin card ≃ B a`). -/
theorem DepFinGen.card_eq {A : Type*} {B : A → Type*} {a : A} [Fintype (B a)]
    (d : DepFinGen B a) : d.card = Fintype.card (B a) := by
  rw [← Fintype.card_of_bijective d.bij, Fintype.card_fin]

namespace DepFinGen

/-- Read a bounded generator at a `Fin`-position: positions below the bound
are `some` (by `hsome`), so the read is total. This is the enumeration
underlying `DepFinGen.ofBounded`. -/
def boundedEnum {S : Type*} (g : ExhaustiveGenerator S) {c : ℕ}
    (hsome : ∀ k, k < c → g.gen k ≠ none) (i : Fin c) : S :=
  (g.gen i).get (Option.isSome_iff_ne_none.mpr (hsome i i.isLt))

/-- The bounded read enumerates the type bijectively: injectivity is the
uniqueness half of `occurs_exactly_once`, surjectivity its existence half
(with the producing position below `c` by `hnone`). -/
theorem boundedEnum_bijective {S : Type*} (g : ExhaustiveGenerator S) {c : ℕ}
    (hnone : ∀ k, c ≤ k → g.gen k = none) (hsome : ∀ k, k < c → g.gen k ≠ none) :
    Function.Bijective (boundedEnum g hsome) := by
  constructor
  · intro i j h
    have hi : g.gen i = some (boundedEnum g hsome i) := (Option.some_get _).symm
    have hj : g.gen j = some (boundedEnum g hsome j) := (Option.some_get _).symm
    obtain ⟨n, _, hun⟩ := g.occurs_exactly_once (boundedEnum g hsome i)
    have h1 : (i : ℕ) = n := hun i hi
    have h2 : (j : ℕ) = n := hun j (hj.trans (congrArg some h.symm))
    exact Fin.ext (h1.trans h2.symm)
  · intro b
    obtain ⟨n, hn, -⟩ := g.occurs_exactly_once b
    have hlt : n < c := by
      by_contra hge
      rw [hnone n (by omega)] at hn
      exact Option.some_ne_none b hn.symm
    refine ⟨⟨n, hlt⟩, ?_⟩
    simp only [boundedEnum]
    apply Option.some_injective
    rw [Option.some_get]
    exact hn

/-- **Build `DepFinGen` block data from any bounded generator of the fiber**:
`enum i` reads the generator at position `i`; bijectivity comes from
`occurs_exactly_once` and the bounds. This is the bridge that lets an existing
finite generator (e.g. a `lexVecData` level) serve as a per-`a` block of
`lexDepPairGen`. -/
@[reducible] def ofBounded {A : Type*} {B : A → Type*} {a : A}
    (g : ExhaustiveGenerator (B a)) {c : ℕ} (hpos : 0 < c)
    (hnone : ∀ k, c ≤ k → g.gen k = none) (hsome : ∀ k, k < c → g.gen k ≠ none) :
    DepFinGen B a where
  card := c
  pos := hpos
  enum := boundedEnum g hsome
  bij := boundedEnum_bijective g hnone hsome

end DepFinGen

namespace ExhaustiveGenerator

/-! ### The ragged prefix sum and its monotonicity -/

/-- The prefix sum `S(i) = Σ_{j < i} card(dB aⱼ)` of block sizes, where
`aⱼ = (gA.gen j).get?` (blocks past `gA`'s end contribute `0`). This is the
ragged odometer's cumulative offset: the values in block `i` occupy the index
window `[S(i), S(i+1))`. -/
def blockSum {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    blockSum gA dB i +
      match gA.gen i with
      | some a => (dB a).card
      | none => 0

/-- The per-block size at index `i`: `card (dB aᵢ)` if `gA.gen i = some aᵢ`,
else `0`. Equal to `S(i+1) - S(i)`. -/
theorem blockSum_succ {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) (i : ℕ) :
    blockSum gA dB (i + 1) =
      blockSum gA dB i + (match gA.gen i with | some a => (dB a).card | none => 0) := rfl

/-- `blockSum` is monotone (each step adds a nonnegative block size). -/
theorem blockSum_mono {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) : Monotone (blockSum gA dB) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [blockSum_succ]
  exact Nat.le_add_right _ _

/-- **Strict increase across a `some`-block.** If `gA.gen i = some a`, then
`S(i) < S(i+1)` (the block has `card ≥ 1` by `pos`). This is the key arithmetic
fact powering both termination and uniqueness. -/
theorem blockSum_lt_succ {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) {i : ℕ} {a : A} (ha : gA.gen i = some a) :
    blockSum gA dB i < blockSum gA dB (i + 1) := by
  rw [blockSum_succ, ha]
  exact Nat.lt_add_of_pos_right (dB a).pos

/-- **Prefix sum dominates the index across `some`-blocks.** If every block
`j < i` is `some`, then `i ≤ S(i)` (each contributes `card ≥ 1`). This gives the
fuel bound `i < S(i) + jB + 1` for `depFind_hit_gen`. -/
theorem le_blockSum_of_some {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ i, (∀ j, j < i → gA.gen j ≠ none) → i ≤ blockSum gA dB i := by
  intro i
  induction i with
  | zero => intro _; exact Nat.zero_le _
  | succ i ih =>
    intro hsome
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (hsome i (Nat.lt_succ_self i))
    have hlt : blockSum gA dB i < blockSum gA dB (i + 1) := blockSum_lt_succ gA dB ha
    have := ih (fun j hj => hsome j (Nat.lt_succ_of_lt hj))
    omega

/-- **Block location.** An index below the prefix sum `S(c)` lands in some
block `i < c`: `S(i) ≤ k < S(i+1)`. Induction on `c` (the last block or the
inductive prefix). -/
theorem exists_block {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (c k : ℕ), k < blockSum gA dB c →
      ∃ i, i < c ∧ blockSum gA dB i ≤ k ∧ k < blockSum gA dB (i + 1) := by
  intro c
  induction c with
  | zero => intro k hk; simp [blockSum] at hk
  | succ c ih =>
    intro k hk
    by_cases h : k < blockSum gA dB c
    · obtain ⟨i, h1, h2, h3⟩ := ih k h
      exact ⟨i, by omega, h2, h3⟩
    · exact ⟨c, by omega, by omega, hk⟩

/-! ### The gen (ragged prefix-sum odometer via fuel recursion) -/

/-- The recursive search: given `fuel`, current block index `i`, and remaining
index `r = k - S(i)`, find the pair. If `gA.gen i = none` (or fuel runs out),
return `none`; if `r < card (dB aᵢ)`, emit `⟨aᵢ, enum ⟨r, _⟩⟩`; else recurse
into block `i+1` with `r - card`. Fuel `k + 1` always suffices because `r`
strictly decreases by `≥ 1` (nonempty blocks) at each recursion while `gA` is
`some`. -/
def depFind {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) : ℕ → ℕ → ℕ → Option (LexDepPair A B)
  | 0, _, _ => none
  | fuel + 1, i, r =>
    match gA.gen i with
    | none => none
    | some a =>
      if hr : r < (dB a).card then
        some ⟨a, (dB a).enum ⟨r, hr⟩⟩
      else
        depFind gA dB fuel (i + 1) (r - (dB a).card)

/-- **Generalized hit lemma.** Starting the walk at block `i₀` with remaining
index `r`, if the target block is `i = i₀ + d` (`gA.gen i = some a`), all
intermediate blocks `i₀, …, i-1` are `some` (`hmid`), `jB < card (dB a)`, and
`r = (S(i) − S(i₀)) + jB`, then with fuel `≥ d + 1` the walk reaches block `i`
and emits `⟨a, enum ⟨jB, _⟩⟩`. Proof by induction on the gap `d`. -/
theorem depFind_hit_gen {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (d fuel i₀ jB : ℕ) (a : A) (hjB : jB < (dB a).card),
      gA.gen (i₀ + d) = some a →
      (∀ j, j < d → gA.gen (i₀ + j) ≠ none) →
      d < fuel →
      depFind gA dB fuel i₀ (blockSum gA dB (i₀ + d) - blockSum gA dB i₀ + jB) =
        some ⟨a, (dB a).enum ⟨jB, hjB⟩⟩ := by
  intro d
  induction d with
  | zero =>
    intro fuel i₀ jB a hjB hga _ hfuel
    -- Gap 0: `i₀` is the target block; remaining is exactly `jB < card`.
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [Nat.add_zero] at hga
    have hidx : blockSum gA dB (i₀ + 0) - blockSum gA dB i₀ + jB = jB := by
      rw [Nat.add_zero, Nat.sub_self, Nat.zero_add]
    rw [hidx]
    show depFind gA dB (fuel' + 1) i₀ jB = _
    unfold depFind
    rw [hga]
    simp only
    rw [dite_eq_left hjB]
  | succ d ih =>
    intro fuel i₀ jB a hjB hga hmid hfuel
    -- Gap `d+1`: block `i₀` is `some a₀`; step into `i₀+1`.
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hmid0 : gA.gen (i₀ + 0) ≠ none := hmid 0 (by omega)
    rw [Nat.add_zero] at hmid0
    obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp hmid0
    -- The remaining index `r` is at least `card (dB a₀)` (the first block's size).
    have hstep : gA.gen (i₀ + (d + 1)) = some a := hga
    have hmono : blockSum gA dB (i₀ + 1) ≤ blockSum gA dB (i₀ + (d + 1)) :=
      blockSum_mono gA dB (by omega)
    have hc0 : blockSum gA dB (i₀ + 1) = blockSum gA dB i₀ + (dB a₀).card := by
      rw [blockSum_succ, ha₀]
    have hge : (dB a₀).card ≤ blockSum gA dB (i₀ + (d + 1)) - blockSum gA dB i₀ + jB := by
      omega
    show depFind gA dB (fuel' + 1) i₀ _ = _
    unfold depFind
    rw [ha₀]
    simp only
    rw [dite_eq_right (by omega)]
    -- Recurse into `i₀+1`, gap `d`; rewrite the remaining index accordingly.
    have hkey : blockSum gA dB (i₀ + (d + 1)) - blockSum gA dB i₀ + jB - (dB a₀).card =
        blockSum gA dB ((i₀ + 1) + d) - blockSum gA dB (i₀ + 1) + jB := by
      rw [show (i₀ + 1) + d = i₀ + (d + 1) by omega]
      omega
    rw [hkey]
    exact ih fuel' (i₀ + 1) jB a hjB (by rw [show (i₀ + 1) + d = i₀ + (d + 1) by omega]; exact hga)
      (fun j hj => by rw [show (i₀ + 1) + j = i₀ + (j + 1) by omega]; exact hmid (j + 1) (by omega))
      (by omega)

/-- **Generalized decode lemma.** If the walk from block `i₀` with remaining `r`
emits `⟨a', b'⟩`, then there is a target block `i ≥ i₀` with `gA.gen i = some a'`
holding the value: some `jB' < card (dB a')` with `b' = enum ⟨jB', _⟩` and the
absolute-index identity `r + S(i₀) = S(i) + jB'`. Proof by strong induction on
`fuel`. This is the inverse of `depFind_hit_gen` and drives uniqueness. -/
theorem depFind_decode {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (fuel i₀ r : ℕ) (a' : A) (b' : B a'),
      depFind gA dB fuel i₀ r = some ⟨a', b'⟩ →
      ∃ (i : ℕ) (jB' : ℕ) (hj : jB' < (dB a').card),
        i₀ ≤ i ∧ gA.gen i = some a' ∧ b' = (dB a').enum ⟨jB', hj⟩ ∧
        r + blockSum gA dB i₀ = blockSum gA dB i + jB' := by
  intro fuel
  induction fuel with
  | zero => intro i₀ r a' b' h; simp [depFind] at h
  | succ fuel ih =>
    intro i₀ r a' b' h
    rw [depFind] at h
    rcases hga : gA.gen i₀ with _ | a₀
    · rw [hga] at h; simp at h
    · rw [hga] at h
      simp only at h
      by_cases hr : r < (dB a₀).card
      · -- Value found in block `i₀`.
        rw [dite_eq_left hr] at h
        have heq : (⟨a₀, (dB a₀).enum ⟨r, hr⟩⟩ : LexDepPair A B) = ⟨a', b'⟩ := Option.some.inj h
        obtain ⟨rfl, hb⟩ := LexDepPair.mk.injEq .. ▸ heq
        -- `hb : enum ⟨r, hr⟩ ≍ b'`; fst equal ⇒ heq collapses to a plain eq.
        refine ⟨i₀, r, hr, le_refl _, hga, (eq_of_heq hb).symm, ?_⟩
        omega
      · -- Recurse into block `i₀+1` with `r - card`.
        rw [dite_eq_right hr] at h
        obtain ⟨i, jB', hj, hle, hgi, hbi, hsum⟩ := ih (i₀ + 1) (r - (dB a₀).card) a' b' h
        refine ⟨i, jB', hj, by omega, hgi, hbi, ?_⟩
        have hc0 : blockSum gA dB (i₀ + 1) = blockSum gA dB i₀ + (dB a₀).card := by
          rw [blockSum_succ, hga]
        omega

/-- **Fuel irrelevance.** With sufficient fuel (`r < fuel`), the walk's result
does not depend on the fuel: nonempty blocks make the remaining index strictly
decrease at each step, so any fuel above `r` resolves the same search. Strong
induction on the remaining index `r`. -/
theorem depFind_fuel_irrel {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (r fuel fuel' i : ℕ), r < fuel → r < fuel' →
      depFind gA dB fuel i r = depFind gA dB fuel' i r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro fuel fuel' i hf hf'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f2, fuel' = f2 + 1 := ⟨fuel' - 1, by omega⟩
    unfold depFind
    rcases hga : gA.gen i with _ | a
    · rfl
    · simp only
      by_cases hr : r < (dB a).card
      · rw [dite_eq_left hr, dite_eq_left hr]
      · rw [dite_eq_right hr, dite_eq_right hr]
        have hpos := (dB a).pos
        exact ih (r - (dB a).card) (by omega) f f' (i + 1) (by omega) (by omega)

/-- **`none`-step for the ragged walk.** If the walk (with its exactly-adequate
fuel `r + 1`) returns `none` at remaining index `r`, it returns `none` at
`r + 1` too: the walk stops only by running off `gA`'s end, and a larger
remaining index reaches at least as far. Strong induction on `r`, with
`depFind_fuel_irrel` aligning the fuels across the recursive step. -/
theorem depFind_none_step {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (r i : ℕ), depFind gA dB (r + 1) i r = none →
      depFind gA dB (r + 2) i (r + 1) = none := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro i h
    rw [depFind] at h
    show depFind gA dB ((r + 1) + 1) i (r + 1) = none
    unfold depFind
    rcases hga : gA.gen i with _ | a
    · rfl
    · rw [hga] at h
      simp only at h ⊢
      have hpos := (dB a).pos
      by_cases hr : r < (dB a).card
      · rw [dite_eq_left hr] at h
        exact absurd h (Option.some_ne_none _)
      · rw [dite_eq_right hr] at h
        rw [dite_eq_right (by omega)]
        -- Align the recursive hypothesis to fuel `r' + 1` (`r' := r - card`),
        -- step it, then align to the goal's fuel `r + 1`.
        have h' : depFind gA dB (r - (dB a).card + 1) (i + 1) (r - (dB a).card) = none :=
          (depFind_fuel_irrel gA dB (r - (dB a).card) _ r (i + 1) (by omega) (by omega)).trans h
        have hstep := ih (r - (dB a).card) (by omega) (i + 1) h'
        rw [show r + 1 - (dB a).card = (r - (dB a).card) + 1 from by omega]
        exact (depFind_fuel_irrel gA dB (r - (dB a).card + 1) _ _ (i + 1)
          (by omega) (by omega)).trans hstep

/-- **Generalized miss lemma** (the dual of `depFind_hit_gen`): if block
`i₀ + d` is `none` in `gA`, all intermediate blocks are `some`, and the
remaining index `r` reaches at least the sum of the intervening block sizes,
the walk runs off `gA`'s end and returns `none`. Induction on the gap `d`. -/
theorem depFind_miss_gen {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a) :
    ∀ (d fuel i₀ r : ℕ),
      gA.gen (i₀ + d) = none →
      (∀ j, j < d → gA.gen (i₀ + j) ≠ none) →
      blockSum gA dB (i₀ + d) - blockSum gA dB i₀ ≤ r →
      d < fuel →
      depFind gA dB fuel i₀ r = none := by
  intro d
  induction d with
  | zero =>
    intro fuel i₀ r hga _ _ hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [Nat.add_zero] at hga
    unfold depFind
    rw [hga]
  | succ d ih =>
    intro fuel i₀ r hga hmid hsum hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hmid0 : gA.gen (i₀ + 0) ≠ none := hmid 0 (by omega)
    rw [Nat.add_zero] at hmid0
    obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp hmid0
    have hc0 : blockSum gA dB (i₀ + 1) = blockSum gA dB i₀ + (dB a₀).card := by
      rw [blockSum_succ, ha₀]
    have hmono : blockSum gA dB (i₀ + 1) ≤ blockSum gA dB (i₀ + (d + 1)) :=
      blockSum_mono gA dB (by omega)
    unfold depFind
    rw [ha₀]
    simp only
    rw [dite_eq_right (by omega)]
    refine ih f (i₀ + 1) (r - (dB a₀).card) ?_ ?_ ?_ (by omega)
    · rw [show (i₀ + 1) + d = i₀ + (d + 1) by omega]; exact hga
    · intro j hj
      rw [show (i₀ + 1) + j = i₀ + (j + 1) by omega]
      exact hmid (j + 1) (by omega)
    · rw [show (i₀ + 1) + d = i₀ + (d + 1) by omega]
      omega

/-- **Uniqueness of the producing position.** Any `m` with `gen m = some ⟨a, b⟩`
equals `S(iA) + jB`, where `iA = idx a` and `jB` is `b`'s block position.
Recovers the block index via `gA`-uniqueness (`huA`) and the offset via `enum`
injectivity. -/
theorem depFind_unique {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (m : ℕ) (a : A) (b : B a) (iA : ℕ) (hiA : gA.gen iA = some a)
    (huA : ∀ y, gA.gen y = some a → y = iA) (jB : ℕ) (hjB : jB < (dB a).card)
    (hjFin : (dB a).enum ⟨jB, hjB⟩ = b)
    (hm : depFind gA dB (m + 1) 0 m = some ⟨a, b⟩) :
    m = blockSum gA dB iA + jB := by
  obtain ⟨i, jB', hj, _, hgi, hbi, hsum⟩ := depFind_decode gA dB (m + 1) 0 m a b hm
  -- The block holding `a` is `iA` (uniqueness of `gA`-index).
  have hi : i = iA := huA i hgi
  subst hi
  -- The offset is `jB` (injectivity of `enum` on the fiber `B a`).
  have hjeq : (⟨jB', hj⟩ : Fin (dB a).card) = ⟨jB, hjB⟩ :=
    (dB a).bij.injective (by rw [← hbi, hjFin])
  have : jB' = jB := congrArg Fin.val hjeq
  subst this
  -- `m + S(0) = S(iA) + jB'`, and `S(0) = 0`.
  simpa [blockSum] using hsum

/-- **The core lexicographic dependent-pair generator.** Position `k` walks the
ragged odometer from block `0` with remaining index `k`: it decodes `k` as
`S(iₐ) + jᵦ` and emits `⟨aₖ, enum jᵦ⟩`. `A` may be infinite; each block `B a`
is finite (via `dB a`) and must be nonempty. The `contig`-step hypothesis `hA`
(a `none` at `n` forces a `none` at `n+1`) is required because the walk STOPS at
the first `none`: it ensures no `some`-block sits past a `none` gap. Every
Azurite base generator satisfies it (see `contiguous_of_*`). -/
@[reducible] def lexDepPairGen {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) :
    ExhaustiveGenerator (LexDepPair A B) where
  gen k := depFind gA dB (k + 1) 0 k
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    -- `a`'s unique `gA`-index, and `b`'s unique block position.
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨⟨jB, hjB⟩, hjFin⟩ := (dB a).bij.surjective b
    -- Intermediate blocks `0, …, iA-1` are all `some` (contiguity from `hA`).
    have hmid : ∀ j, j < iA → gA.gen (0 + j) ≠ none := by
      intro j hj hjnone
      rw [Nat.zero_add] at hjnone
      have hnone : gA.gen iA = none := gen_none_of_le_step gA hA (le_of_lt hj) hjnone
      rw [hnone] at hiA
      exact Option.some_ne_none a hiA.symm
    -- The target index is `S(iA) + jB`; `S(0+iA) − S(0) = S(iA)` since `S(0)=0`.
    have hSeq : blockSum gA dB (0 + iA) - blockSum gA dB 0 + jB = blockSum gA dB iA + jB := by
      simp [blockSum]
    refine ⟨blockSum gA dB iA + jB, ?_, ?_⟩
    · -- Existence: `depFind` from block `0` reaches block `iA` and emits `⟨a, b⟩`.
      show depFind gA dB (blockSum gA dB iA + jB + 1) 0 (blockSum gA dB iA + jB) = _
      have hle : iA ≤ blockSum gA dB iA :=
        le_blockSum_of_some gA dB iA (fun j hj => by rw [← Nat.zero_add j]; exact hmid j hj)
      have hhit := depFind_hit_gen gA dB iA (blockSum gA dB iA + jB + 1) 0 jB a hjB
        (by rw [Nat.zero_add]; exact hiA) hmid (by omega)
      rw [hSeq] at hhit
      rw [hhit, hjFin]
    · -- Uniqueness: any producing position decodes back to `S(iA) + jB`.
      intro m hm
      exact depFind_unique gA dB m a b iA hiA huA jB hjB hjFin hm

/-! ### The composition kit: contiguity and finite bounds for `lexDepPairGen`

These export the walk's structure in the interface the compositional layers
consume: the `contig`-step (so a `LexDepPair` can feed `mapGen`/further
compositions), and — when `gA` is finite with bound `cA` — the exact
`hnone`/`hsome` bounds at the total block count `blockSum gA dB cA`, packaged
as `FiniteGenerator` data. -/

/-- **`lexDepPairGen` preserves the `contig` step**: the walk stops at the
first `gA`-`none`, and a larger target index stops at the same block
(`depFind_none_step`). Note this holds for ANY `gA` — the `hA` hypothesis of
the generator itself is only needed for coverage, not contiguity. -/
theorem lexDepPairGen_contig_step {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) :
    ∀ k, (lexDepPairGen gA dB hA).gen k = none →
      (lexDepPairGen gA dB hA).gen (k + 1) = none :=
  fun k h => depFind_none_step gA dB k 0 h

/-- Packaged `Contiguous` form of `lexDepPairGen_contig_step`. -/
theorem lexDepPairGen_contiguous {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) :
    @Contiguous (LexDepPair A B) (lexDepPairGen gA dB hA) :=
  @Contiguous.mk (LexDepPair A B) (lexDepPairGen gA dB hA) (lexDepPairGen_contig_step gA dB hA)

/-- **Finite bound, `none` half**: when `gA` is finite with bound `cA`, the
dependent-pair generator runs out exactly at the total block count
`blockSum gA dB cA` (the ragged analogue of `cA * cB`). Via `depFind_miss_gen`
with the `none` block at gap `cA`. -/
theorem lexDepPairGen_gen_none {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) {cA : ℕ}
    (hnoneA : ∀ n, cA ≤ n → gA.gen n = none) (hsomeA : ∀ n, n < cA → gA.gen n ≠ none) :
    ∀ k, blockSum gA dB cA ≤ k → (lexDepPairGen gA dB hA).gen k = none := by
  intro k hk
  have hle : cA ≤ blockSum gA dB cA :=
    le_blockSum_of_some gA dB cA (fun j hj => hsomeA j hj)
  show depFind gA dB (k + 1) 0 k = none
  refine depFind_miss_gen gA dB cA (k + 1) 0 k ?_ ?_ ?_ (by omega)
  · rw [Nat.zero_add]; exact hnoneA cA (le_refl _)
  · intro j hj; rw [Nat.zero_add]; exact hsomeA j hj
  · rw [Nat.zero_add]
    simp only [blockSum]
    omega

/-- **Finite bound, `some` half**: positions below the total block count
`blockSum gA dB cA` produce a value. Locate the block (`exists_block`), then
run the hit lemma at its offset. -/
theorem lexDepPairGen_gen_some {A : Type*} {B : A → Type*} (gA : ExhaustiveGenerator A)
    (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) {cA : ℕ}
    (hsomeA : ∀ n, n < cA → gA.gen n ≠ none) :
    ∀ k, k < blockSum gA dB cA → (lexDepPairGen gA dB hA).gen k ≠ none := by
  intro k hk
  obtain ⟨i, hic, h1, h2⟩ := exists_block gA dB cA k hk
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (hsomeA i hic)
  have hcard : blockSum gA dB (i + 1) = blockSum gA dB i + (dB a).card := by
    rw [blockSum_succ, ha]
  have hjB : k - blockSum gA dB i < (dB a).card := by omega
  have hile : i ≤ blockSum gA dB i :=
    le_blockSum_of_some gA dB i (fun j hj => hsomeA j (by omega))
  have hhit := depFind_hit_gen gA dB i (k + 1) 0 (k - blockSum gA dB i) a hjB
    (by rw [Nat.zero_add]; exact ha)
    (fun j hj => by rw [Nat.zero_add]; exact hsomeA j (by omega))
    (by omega)
  have hSeq : blockSum gA dB (0 + i) - blockSum gA dB 0 + (k - blockSum gA dB i) = k := by
    rw [Nat.zero_add]
    simp only [blockSum]
    omega
  rw [hSeq] at hhit
  show depFind gA dB (k + 1) 0 k ≠ none
  rw [hhit]
  exact Option.some_ne_none _

/-- **`FiniteGenerator` data for `lexDepPairGen`** over a finite first
component: `card` is the total block count `blockSum gA dB cA` — COMPUTABLE
when `cA` is a literal (a fold of the block sizes over `gA`'s enumeration). An
INSTANCE form is deliberately not provided: the per-fiber block data `dB` is
value-indexed data with no typeclass carrier (unlike `FiniteGenerator B` for
the non-dependent `LexPair`). -/
@[reducible] def lexDepPairGen_finiteGenerator {A : Type*} {B : A → Type*}
    (gA : ExhaustiveGenerator A) (dB : (a : A) → DepFinGen B a)
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none) {cA : ℕ}
    (hnoneA : ∀ n, cA ≤ n → gA.gen n = none) (hsomeA : ∀ n, n < cA → gA.gen n ≠ none) :
    @FiniteGenerator (LexDepPair A B) (lexDepPairGen gA dB hA) :=
  @FiniteGenerator.mk (LexDepPair A B) (lexDepPairGen gA dB hA) (blockSum gA dB cA)
    (lexDepPairGen_gen_none gA dB hA hnoneA hsomeA)
    (lexDepPairGen_gen_some gA dB hA hsomeA)

end ExhaustiveGenerator

/-! ### Counts

`LexDepPair A B` is `Σ (a : A), B a` up to the `equivSigma` newtype wrapper, so
its cardinality is `∑ a, |B a|` when `A` and every fiber are finite (and each
`(dB a).card` equals `|B a|` by the block bijection). When `A` is infinite and
every fiber nonempty, `LexDepPair A B` is infinite. -/

namespace LexDepPair

/-- `LexDepPair A B` is infinite when `A` is infinite and every fiber nonempty:
the map `a ↦ ⟨a, b₀⟩` is injective. -/
instance {A : Type*} {B : A → Type*} [Infinite A] [∀ a, Nonempty (B a)] :
    Infinite (LexDepPair A B) :=
  Infinite.of_injective (fun a => ⟨a, Classical.arbitrary (B a)⟩)
    (fun _ _ h => congrArg LexDepPair.fst h)

/-- A `Fintype` for `LexDepPair A B` when `A` and every fiber are finite. -/
instance instFintype {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] :
    Fintype (LexDepPair A B) :=
  Fintype.ofEquiv _ equivSigma.symm

/-- The cardinality of `LexDepPair A B` is `∑ a, |B a|`. -/
theorem card {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] :
    Fintype.card (LexDepPair A B) = ∑ a, Fintype.card (B a) := by
  rw [Fintype.card_congr equivSigma, Fintype.card_sigma]

end LexDepPair

/-! ### Guards

Two dependent enumerations. Case (a) has RAGGED blocks over a finite first
coordinate: `A = Bool`, `B false = Fin 1`, `B true = Fin 3`, so the block sizes
are `1` then `3` and the enumeration is `⟨false,0⟩, ⟨true,0⟩, ⟨true,1⟩,
⟨true,2⟩` — confirming the ragged prefix-sum order (last coordinate fastest).
Case (b) is infinite-first with CONSTANT blocks (`A = AzNat`, `B _ = Bool`),
which must agree with a plain lexicographic pair. -/

namespace ExhaustiveGenerator

-- `boolsGen`/`naturalsGen` are contiguous, giving the `contig`-step hypothesis.
private theorem boolsGen_contigStep : ∀ n, boolsGen.gen n = none → boolsGen.gen (n + 1) = none :=
  fun n => Contiguous.contig n
private theorem naturalsGen_contigStep :
    ∀ n, naturalsGen.gen n = none → naturalsGen.gen (n + 1) = none :=
  fun n => Contiguous.contig n

/-- (a) RAGGED finite-first: `B false = Fin 1`, `B true = Fin 3`. -/
private def raggedB : Bool → Type := fun b => if b then Fin 3 else Fin 1

/-- Per-block data for `raggedB`: block `false` has size `1`, block `true` size `3`. -/
private def raggedDB : (b : Bool) → DepFinGen raggedB b
  | false => { card := 1, pos := Nat.one_pos, enum := id, bij := Function.bijective_id }
  | true  => { card := 3, pos := by norm_num, enum := id, bij := Function.bijective_id }

/-- The ragged dependent-pair generator over `Bool`. -/
@[reducible] def raggedGen : ExhaustiveGenerator (LexDepPair Bool raggedB) :=
  lexDepPairGen boolsGen raggedDB boolsGen_contigStep

/-- Render a `raggedB` pair as `(Bool, ℕ)` for the guard. -/
private def raggedRender : LexDepPair Bool raggedB → Bool × ℕ
  | ⟨false, c⟩ => (false, (c : Fin 1).val)
  | ⟨true, c⟩  => (true, (c : Fin 3).val)

/-- (b) CONSTANT infinite-first: `A = AzNat`, `B _ = Bool` (card `2` each). -/
@[reducible] private def constB : AzNat → Type := fun _ => Bool

/-- Per-block data for `constB`: every block is `[false, true]` (`Bool`, size `2`). -/
private def constDB : (a : AzNat) → DepFinGen constB a := fun _ =>
  { card := 2, pos := by norm_num, enum := ![false, true],
    bij := (by decide : Function.Bijective (![false, true] : Fin 2 → Bool)) }

/-- The constant-block dependent-pair generator over `AzNat` (agrees with a
plain lex pair `AzNat × Bool`). -/
@[reducible] def natConstGen : ExhaustiveGenerator (LexDepPair AzNat constB) :=
  lexDepPairGen naturalsGen constDB naturalsGen_contigStep

end ExhaustiveGenerator

open ExhaustiveGenerator

-- (a) ragged blocks: `⟨false,0⟩, ⟨true,0⟩, ⟨true,1⟩, ⟨true,2⟩`; caps at 4.
#guard (@firstN _ raggedGen 10).map raggedRender
  = [(false, 0), (true, 0), (true, 1), (true, 2)]
#guard (@firstN _ raggedGen 10).length == 4

-- (b) constant blocks over infinite `AzNat`: same order as a lex pair.
#guard (@firstN _ natConstGen 6).map (fun p => (p.fst.toNat, (p.snd : Bool)))
  = [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

end Azurite
