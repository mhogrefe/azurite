/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `shortlex_vecs` — all vecs over a finite type in SHORTLEX order (Malachite
  `shortlex_vecs`): shortest first, and same-length vecs in lexicographic
  order.

  Malachite's `ShortlexVecs` IS `LexDependentPairs<u64, Vec<T>>` — first
  component `exhaustive_unsigneds()` (the lengths `0, 1, 2, …`), per-length
  blocks `lex_vecs_fixed_length`, projected to the second coordinate. The port
  mirrors this exactly: `lexDepPairGen` over the lengths generator with fibers
  `LexVec T n` (each level of the bundled `lexVecData` recursion supplies its
  `DepFinGen` block data through the `DepFinGen.ofBounded` bridge), relabeled
  through the flattening bijection `⟨n, v⟩ ↦ v.toList`. Flattening is a genuine
  bijection because a list determines its length, so dropping the first
  coordinate (Malachite's `.map(|p| p.1)`) loses nothing.

  The output is the newtype `ShortlexVec T` wrapping `List T`, kept distinct
  from the bare list type so the later `exhaustive_vecs` port (the
  BitDistributor-backed default order) can claim its own generator without
  clashing — the same newtype discipline as `LexPair` vs `A × B`.

  `T` must be FINITE (Malachite: "`xs` must be finite; if it's infinite, only
  vecs of length 0 and 1 are ever produced" — the Lean port simply requires
  the bound) and NONEMPTY: the length-`n` block has `cT ^ n` vecs, and
  `lexDepPairGen` requires nonempty blocks (`cT = 0` would make every block
  past length `0` empty, breaking the ragged odometer's termination).
  Malachite's empty-`xs` boundary ("if `xs` is empty, the output length is 1",
  the single empty vec) is the degenerate case excluded by `0 < cT`; no
  Azurite base type is empty, and `[Nonempty T]` discharges the bound
  positivity via `FiniteGenerator.card_pos`.

  The lengths generator `lengthsGen : ExhaustiveGenerator ℕ` is a local `def`,
  deliberately NOT an instance: `AzNat` is Azurite's computational number type
  and no global `ExhaustiveGenerator ℕ` default is claimed. Here the lengths
  are the structural indices of the fibers `LexVec T n` (necessarily `ℕ`) and
  stay tiny — the output lengths grow logarithmically in the position.
-/
import Azurite.ExhaustiveGenerator.LexDepPairs
import Azurite.ExhaustiveGenerator.LexVecs

namespace Azurite

/-- A shortlex-ordered vec of any length: a newtype for `List T`, kept
distinct from the bare list type so it can carry the SHORTLEX
`ExhaustiveGenerator` (shortest first, same-length vecs lexicographically)
without clashing with the later `exhaustive_vecs` port's default order. `T`
must be finite and nonempty. -/
structure ShortlexVec (T : Type*) where
  /-- The underlying list. -/
  val : List T
deriving DecidableEq

namespace ShortlexVec

/-- The obvious computable equivalence `ShortlexVec T ≃ List T`. -/
@[simps] def equivList {T : Type*} : ShortlexVec T ≃ List T where
  toFun := ShortlexVec.val
  invFun := ShortlexVec.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ShortlexVec T` is infinite whenever `T` is nonempty (`n ↦` the length-`n`
constant list is injective). This is why the shortlex generator carries no
`FiniteGenerator` data — it never runs out. -/
instance instInfinite {T : Type*} [Nonempty T] : Infinite (ShortlexVec T) :=
  Infinite.of_injective (fun n : ℕ => ⟨List.replicate n (Classical.arbitrary T)⟩)
    (fun a b h => by simpa using congrArg (fun v => v.val.length) h)

end ShortlexVec

namespace ExhaustiveGenerator

/-- The lengths generator `0, 1, 2, …` — the first (slowest) coordinate of the
shortlex dependent pair (Malachite `exhaustive_unsigneds()`). A local `def`,
NOT an instance (see the module header). -/
@[reducible] def lengthsGen : ExhaustiveGenerator ℕ :=
  ofBijective id Function.bijective_id

/-- `lengthsGen` never produces `none`, so its `contig`-step is vacuous. -/
theorem lengthsGen_contigStep :
    ∀ n, lengthsGen.gen n = none → lengthsGen.gen (n + 1) = none :=
  fun _ h => absurd h (Option.some_ne_none _)

/-- The per-length block data: length `n`'s block is the `cT ^ n` length-`n`
vecs in lexicographic order, read off the bundled `lexVecData` level through
the `DepFinGen.ofBounded` bridge. Nonemptiness of every block is exactly
`0 < cT`. -/
@[reducible] def shortlexBlocks {T : Type*} (g : ExhaustiveGenerator T) {cT : ℕ}
    (hpos : 0 < cT) (hnone : ∀ k, cT ≤ k → g.gen k = none)
    (hsome : ∀ k, k < cT → g.gen k ≠ none) (n : ℕ) :
    DepFinGen (fun n => LexVec T n) n :=
  DepFinGen.ofBounded (lexVecData g hnone hsome n).gen (pow_pos hpos n)
    (lexVecData g hnone hsome n).hnone (lexVecData g hnone hsome n).hsome

/-- Flatten a length-tagged vec to its underlying list. This is the computable
bijection `LexDepPair ℕ (LexVec T ·) → ShortlexVec T` (Malachite's
`.map(|p| p.1)` — but here a bijection, since the length is recoverable). -/
@[reducible] def flattenShortlex {T : Type*} :
    LexDepPair ℕ (fun n => LexVec T n) → ShortlexVec T :=
  fun p => ⟨p.snd.val.toList⟩

theorem flattenShortlex_bijective {T : Type*} :
    Function.Bijective (flattenShortlex (T := T)) := by
  constructor
  · -- Injective: the list determines the length, then the vec.
    rintro ⟨n, ⟨v⟩⟩ ⟨m, ⟨w⟩⟩ h
    have hl : v.toList = w.toList := congrArg ShortlexVec.val h
    have hnm : n = m := by
      have := congrArg List.length hl
      rwa [v.toList_length, w.toList_length] at this
    subst hnm
    rw [List.Vector.eq v w hl]
  · -- Surjective: a list `l` is the flattening of `⟨l.length, ⟨l⟩⟩`.
    rintro ⟨l⟩
    exact ⟨⟨l.length, ⟨⟨l, rfl⟩⟩⟩, rfl⟩

/-- **The shortlex vec generator** (Malachite `shortlex_vecs`): all vecs over
the finite nonempty type `T`, shortest first, same-length vecs
lexicographically. `g` is `T`'s generator with explicit witnesses that it is
finite with POSITIVE bound `cT` (builder convention: explicit builders take
explicit witnesses). The dependent-pair walk decodes position `k` into a
length (slow) and an in-block lex index (fast): positions `0`, `1..cT`,
`cT+1..cT+cT²`, … hold the length-`0`, `1`, `2`, … blocks. -/
@[reducible] def shortlexVecs {T : Type*} (g : ExhaustiveGenerator T) {cT : ℕ}
    (hpos : 0 < cT) (hnone : ∀ k, cT ≤ k → g.gen k = none)
    (hsome : ∀ k, k < cT → g.gen k ≠ none) : ExhaustiveGenerator (ShortlexVec T) :=
  mapGen flattenShortlex flattenShortlex_bijective
    (lexDepPairGen lengthsGen (shortlexBlocks g hpos hnone hsome) lengthsGen_contigStep)

end ExhaustiveGenerator

/-! ### The `ExhaustiveGenerator` instance on `ShortlexVec`

With `[FiniteGenerator T]` (whose literal `card` keeps the block sizes
computable) and `[Nonempty T]` (which makes that card positive,
`FiniteGenerator.card_pos`), the shortlex generator becomes a genuine
computable instance. It is INFINITE (`ShortlexVec.instInfinite`) — every
position produces a value — so there is no `FiniteGenerator` companion;
`Contiguous` holds (vacuously) via the dependent-pair walk's `contig`-step,
letting `ShortlexVec T` feed further compositions as an infinite first
component. -/

open ExhaustiveGenerator

/-- Shortlex `ExhaustiveGenerator` on `ShortlexVec T`: shortest first,
same-length vecs lexicographically; `T` must have a finite generator and be
nonempty. -/
instance instExhaustiveGeneratorShortlexVec {T : Type*} [inst : ExhaustiveGenerator T]
    [FiniteGenerator T] [Nonempty T] : ExhaustiveGenerator (ShortlexVec T) :=
  shortlexVecs inst FiniteGenerator.card_pos
    FiniteGenerator.gen_none FiniteGenerator.gen_some

/-- The shortlex generator is contiguous (its `none`s — of which there are
none — form a final segment), so it composes as an infinite first
component. -/
instance instContiguousShortlexVec {T : Type*} [inst : ExhaustiveGenerator T]
    [FiniteGenerator T] [Nonempty T] : Contiguous (ShortlexVec T) :=
  mapGen_contiguous flattenShortlex flattenShortlex_bijective _
    (lexDepPairGen_contiguous lengthsGen _ lengthsGen_contigStep)

/-! ### Guards

The 20-value `Bool` table is Malachite's `shortlex_vecs` doctest verbatim
(`vecs/exhaustive.rs`). `Ordering` (card `3`) crosses a non-power-of-two radix
through length `2`; `UInt8` spot-checks a large radix deep into the length-`2`
block (position `257 + j` holds the `j`-th length-`2` vec `[j / 256, j % 256]`). -/

-- The Malachite doctest, verbatim: lengths `0, 1, 2, 3` complete (1+2+4+8 =
-- 15 values), then the first 5 length-`4` vecs.
#guard (firstN (ShortlexVec Bool) 20).map (·.val)
  = [[],
     [false], [true],
     [false, false], [false, true], [true, false], [true, true],
     [false, false, false], [false, false, true], [false, true, false], [false, true, true],
     [true, false, false], [true, false, true], [true, true, false], [true, true, true],
     [false, false, false, false], [false, false, false, true], [false, false, true, false],
     [false, false, true, true], [false, true, false, false]]

-- The generator is infinite: no `none`s in any prefix.
#guard (firstN (ShortlexVec Bool) 40).length == 40

-- `Ordering` (card 3): lengths `0, 1, 2` complete (1 + 3 + 9 = 13 values).
#guard (firstN (ShortlexVec Ordering) 13).map (·.val)
  = [[],
     [.lt], [.eq], [.gt],
     [.lt, .lt], [.lt, .eq], [.lt, .gt], [.eq, .lt], [.eq, .eq], [.eq, .gt],
     [.gt, .lt], [.gt, .eq], [.gt, .gt]]

-- `UInt8` (card `2^8`): the singletons occupy positions `1..256`; the
-- length-`2` block starts at `257`, in lex order with the head slowest.
#guard (gen (T := ShortlexVec UInt8) 0).map (·.val.map (·.toNat)) == some []
#guard (gen (T := ShortlexVec UInt8) 256).map (·.val.map (·.toNat)) == some [255]
#guard (gen (T := ShortlexVec UInt8) 257).map (·.val.map (·.toNat)) == some [0, 0]
#guard (gen (T := ShortlexVec UInt8) 300).map (·.val.map (·.toNat)) == some [0, 43]
#guard (gen (T := ShortlexVec UInt8) (257 + 5 * 256 + 7)).map (·.val.map (·.toNat))
  == some [5, 7]

-- The explicit builder produces the identical order as the instance.
#guard (@firstN _
    (shortlexVecs boolsGen FiniteGenerator.card_pos
      FiniteGenerator.gen_none FiniteGenerator.gen_some)
    7).map (·.val)
  = [[], [false], [true], [false, false], [false, true], [true, false], [true, true]]

-- Composite: an infinite-first lex pair with `ShortlexVec Bool` as the SLOW
-- coordinate and a finite second component — exercising the `Contiguous`
-- instance in composition.
#guard (firstN (LexPair (ShortlexVec Bool) Bool) 6).map (fun p => (p.fst.val, p.snd))
  = [([], false), ([], true),
     ([false], false), ([false], true),
     ([true], false), ([true], true)]

end Azurite
