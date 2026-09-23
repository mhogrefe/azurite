/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `GenCache` — the `IteratorCache` port: an Array-backed fill-forward cache
  over a `StreamFor`, plus CACHED drivers for the fair composite generators.

  The fair composites (`FairPairs`/`FairTuples`/`FairVecs`/`FairCapped`)
  random-access their component generators: position `k` deinterleaves into
  component indices that are REVISITED many times across a prefix walk
  (Z-order visits a component index at every counter whose slot bits decode
  to it), and the spec rail recomputes the component value from scratch at
  every visit — ruinous for O(index)-per-call components like the
  Calkin–Wilf rationals. A `GenCache` wraps a component's `StreamFor` and
  remembers everything the stream has emitted: `get i` answers from the
  cache when `i` is covered (NO stream work, `get_snd_of_lt`) and otherwise
  advances the stream JUST past `i`, appending one entry per step — so any
  access pattern touching indices `≤ M` costs at most `M + 1` stream steps
  TOTAL (the cache never re-advances; `get_snd_cache_size`). The bridge law
  is `get_fst : (c.get i).1 = g.gen i` (from the invariant + the stream's
  `emits`).

  This mirrors Malachite's `IteratorCache` (`{xs, cache: Vec, done}`), with
  one deliberate difference: the `done` flag is NOT ported. Our cache
  entries are `Option T` — a `none` entry IS the exhaustion marker at its
  index — and a `StreamFor.next` is a total function (it keeps emitting
  `none` past the end), so filling forward past exhaustion is well-defined
  and the flag has nothing left to guard.

  The payoff is the cached drivers `fairPairFirstNCached` /
  `fairTripleFirstNCached` / `fairQuadrupleFirstNCached` /
  `fairVecFirstNCached`: one forward walk of the counter, each component
  value computed ONCE, provably equal to the spec rail — instance-level
  (`… = firstN _ n`, the composite instances being `fairPairGen`-shaped) on
  top of assignment-generic builder-level laws. The capped siblings
  `fairPairCappedFirstNCached` / `fairTripleCappedFirstNCached` /
  `fairQuadrupleCappedFirstNCached` / `fairVecCappedFirstNCached` walk the RAW
  capped builders (`fairPairGenCapped` etc.) — the cache returns exactly the
  component `Option`s the capped `gen` binds through (the vec driver threads
  ONE shared cache across all coordinates and reconstructs each vec from it) —
  with laws stated against the raw builder's prefix
  (`(List.range n).filterMap gen`): the public capped
  INSTANCES are hole-compressed (`compress` re-indexes positions), so their
  prefixes are the raw walker's output continued until `n` values
  accumulate, not a fixed-`n` counter window.

  Also here: `StreamFor.map`, the transport combinator producing a
  `StreamFor (mapGen f hf g)` from a `StreamFor g`, so cached components
  compose through relabelings.

  Component-index bound (why the caches stay small): walking counters
  `k < n` touches component indices `deinterleave j k ≤ k`, and for the
  weight-1 round-robin assignments each slot reads only every `m`-th
  counter bit — so the touched indices are ~`n^(1/m)` for an `m`-slot
  composite (~`√n` for pairs). The caches therefore hold ~`n^(1/m)`
  entries after an `n`-prefix walk (not proven here; the drivers' laws do
  not need it).
-/
import Azurite.ExhaustiveGenerator.Stream
import Azurite.ExhaustiveGenerator.FairCapped

namespace Azurite

open ExhaustiveGenerator

/-- Two `Option.get`s of equal options are equal (the proof arguments are
irrelevant). The congruence lemma the cached drivers use to trade a cache
read for the spec's `gen` call under `Option.get`. -/
private theorem option_get_congr {α : Type*} {o o' : Option α} (h : o = o')
    (ho : o.isSome) (ho' : o'.isSome) : o.get ho = o'.get ho' := by
  subst h
  rfl

/-! ### The cache -/

/-- **A fill-forward cache over a stream** (the `IteratorCache` port). The
DATA is the stream state `state` (advanced exactly past the cache) and the
`cache` array; the invariant fields are `Prop`s (erased at runtime) tying
them to the generator: entry `i` of the cache is `g.gen i`, and `state` is
the `cache.size`-fold advance of the stream — so filling forward resumes
exactly where the cache ends. No `done` flag (unlike Malachite): a cached
`none` entry is itself the exhaustion marker, and `next` is total. -/
structure GenCache {T : Type*} {g : ExhaustiveGenerator T} (s : StreamFor g) where
  /-- The stream state, advanced exactly past the cached prefix. -/
  state : s.σ
  /-- The cached emissions: `cache[i] = g.gen i` for every `i < cache.size`. -/
  cache : Array (Option T)
  /-- State invariant: `state` is the `cache.size`-fold advance from `init`. -/
  state_inv : state = advanceN s.next s.init cache.size
  /-- Cache invariant: every cached entry is the generator's value there. -/
  cache_inv : ∀ i (h : i < cache.size), cache[i] = g.gen i

namespace GenCache

variable {T : Type*} {g : ExhaustiveGenerator T} {s : StreamFor g}

/-- The empty cache: the stream at `init`, nothing cached. -/
def init (s : StreamFor g) : GenCache s where
  state := s.init
  cache := #[]
  state_inv := rfl
  cache_inv i h := absurd h (Nat.not_lt_zero i)

/-- Advance the stream ONE step, appending the emission to the cache. The
new entry is `g.gen cache.size` by the stream's `emits` law (through the
state invariant). -/
def push (c : GenCache s) : GenCache s where
  state := (s.next c.state).2
  cache := c.cache.push (s.next c.state).1
  state_inv := by
    rw [Array.size_push, c.state_inv]
    rfl
  cache_inv := by
    intro i h
    have h' : i < c.cache.size + 1 := by simpa using h
    rw [Array.getElem_push]
    rcases Nat.lt_or_ge i c.cache.size with hi | hi
    · rw [dite_eq_left hi]
      exact c.cache_inv i hi
    · have hie : i = c.cache.size := by omega
      subst hie
      rw [dite_eq_right (Nat.lt_irrefl _), c.state_inv]
      exact s.emits c.cache.size

theorem push_cache_size (c : GenCache s) : c.push.cache.size = c.cache.size + 1 :=
  Array.size_push _

/-- `n`-fold `push`: fill the cache forward by `n` entries (one stream step
per entry). -/
def fillN (c : GenCache s) : ℕ → GenCache s
  | 0 => c
  | n + 1 => c.push.fillN n

theorem fillN_cache_size (c : GenCache s) (n : ℕ) :
    (c.fillN n).cache.size = c.cache.size + n := by
  induction n generalizing c with
  | zero => rfl
  | succ m ih =>
    show (c.push.fillN m).cache.size = c.cache.size + (m + 1)
    rw [ih c.push, push_cache_size]
    omega

/-- The fill in `get` always covers the requested index. -/
theorem lt_fillN_cache_size (c : GenCache s) (i : ℕ) :
    i < (c.fillN (i + 1 - c.cache.size)).cache.size := by
  rw [fillN_cache_size]
  omega

/-- **Cached read.** If `i` is covered, read the cache (NO stream work);
otherwise fill forward from `state` through `i` (one `next` per new entry),
then read. Returns the value together with the (possibly grown) cache, to
be threaded through the caller's fold. Amortization: across ANY access
sequence, total stream work = total cache growth ≤ (max index accessed)+1,
since covered reads do no stream work and the fill never overshoots. -/
def get (c : GenCache s) (i : ℕ) : Option T × GenCache s :=
  let c' := c.fillN (i + 1 - c.cache.size)
  (c'.cache[i]'(lt_fillN_cache_size c i), c')

/-- **The cache law**: a cached read produces exactly the generator's value
— the invariant transported through the fill. This is what lets the cached
drivers replace every `g.gen` call of the composite generators. -/
theorem get_fst (c : GenCache s) (i : ℕ) : (c.get i).1 = g.gen i :=
  (c.fillN (i + 1 - c.cache.size)).cache_inv i (lt_fillN_cache_size c i)

/-- `Option.get`-ready form of `get_fst` for never-`none` components. -/
theorem get_fst_isSome (c : GenCache s) (h : ∀ n, g.gen n ≠ none) (i : ℕ) :
    (c.get i).1.isSome := by
  rw [get_fst]
  exact Option.isSome_iff_ne_none.mpr (h i)

/-- A covered read leaves the cache untouched (the fill count is `0`). -/
theorem get_snd_of_lt (c : GenCache s) {i : ℕ} (h : i < c.cache.size) :
    (c.get i).2 = c := by
  show c.fillN (i + 1 - c.cache.size) = c
  rw [Nat.sub_eq_zero_of_le h]
  rfl

/-- The cache size after a read: grown exactly to cover `i`, never beyond
(and never shrunk) — the amortization accounting in one equation. -/
theorem get_snd_cache_size (c : GenCache s) (i : ℕ) :
    (c.get i).2.cache.size = max c.cache.size (i + 1) := by
  show (c.fillN (i + 1 - c.cache.size)).cache.size = _
  rw [fillN_cache_size]
  omega

end GenCache

/-! ### The transport combinator -/

/-- **Relabel a stream along `mapGen`.** A `StreamFor (mapGen f hf g)` from
a `StreamFor g`: same state, emissions mapped through `f`. This is what
lets a cached component compose through the relabelings the nested tuple
generators use. -/
def StreamFor.map {S T : Type*} {g : ExhaustiveGenerator S} (f : S → T)
    (hf : Function.Bijective f) (s : StreamFor g) :
    StreamFor (ExhaustiveGenerator.mapGen f hf g) where
  σ := s.σ
  init := s.init
  next st := ((s.next st).1.map f, (s.next st).2)
  emits n := by
    have hstate : ∀ m, advanceN (fun st => ((s.next st).1.map f, (s.next st).2)) s.init m
        = advanceN s.next s.init m := by
      intro m
      induction m with
      | zero => rfl
      | succ k ih =>
        rw [advanceN, ih]
        rfl
    have h := s.emits n
    rw [emitAt_fst] at h
    rw [emitAt_fst, hstate n]
    show (s.next (advanceN s.next s.init n)).1.map f = (g.gen n).map f
    rw [h]

namespace ExhaustiveGenerator

/-! ### The cached fair pair driver -/

variable {A B C D : Type*} {gA : ExhaustiveGenerator A} {gB : ExhaustiveGenerator B}
  {gC : ExhaustiveGenerator C} {gD : ExhaustiveGenerator D}

/-- Core walker for the cached fair pair driver, generic over the 2-slot
assignment: at counter `k`, `get` each component through ITS cache (threaded
through the walk), assemble the pair, recurse. Each component value is
computed ONCE across the whole walk (`GenCache.get` never re-advances). -/
def fairPairCachedGo (P : BitAssignment 2) (sA : StreamFor gA) (sB : StreamFor gB)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) :
    GenCache sA → GenCache sB → ℕ → ℕ → List (A × B)
  | _, _, _, 0 => []
  | cA, cB, k, n + 1 =>
    let rA := cA.get (P.deinterleave 0 k)
    let rB := cB.get (P.deinterleave 1 k)
    (rA.1.get (cA.get_fst_isSome hA _), rB.1.get (cB.get_fst_isSome hB _)) ::
      fairPairCachedGo P sA sB hA hB rA.2 rB.2 (k + 1) n

/-- The walker law: the cached walk from counter `k` equals the composite
generator's outputs on the counter window — `GenCache.get_fst` transported
along the walk. -/
theorem fairPairCachedGo_eq (P : BitAssignment 2) (sA : StreamFor gA) (sB : StreamFor gB)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (cA : GenCache sA) (cB : GenCache sB) (k n : ℕ) :
    fairPairCachedGo P sA sB hA hB cA cB k n
      = (List.range' k n).filterMap (fairPairGenWith P gA gB hA hB).gen := by
  induction n generalizing cA cB k with
  | zero => rfl
  | succ m ih =>
    have hgk : (fairPairGenWith P gA gB hA hB).gen k
        = some ((gA.gen (P.deinterleave 0 k)).get (Option.isSome_iff_ne_none.mpr (hA _)),
          (gB.gen (P.deinterleave 1 k)).get (Option.isSome_iff_ne_none.mpr (hB _))) := rfl
    show ((cA.get (P.deinterleave 0 k)).1.get (cA.get_fst_isSome hA _),
        (cB.get (P.deinterleave 1 k)).1.get (cB.get_fst_isSome hB _))
        :: fairPairCachedGo P sA sB hA hB (cA.get (P.deinterleave 0 k)).2
          (cB.get (P.deinterleave 1 k)).2 (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap (fairPairGenWith P gA gB hA hB).gen
    rw [List.filterMap_cons_some hgk, ih]
    congr 1
    rw [Prod.mk.injEq]
    exact ⟨option_get_congr (GenCache.get_fst cA _) _ _,
      option_get_congr (GenCache.get_fst cB _) _ _⟩

/-- **The cached fair pair driver.** One forward walk of `n` counters over
the weight-1 `fairPairAssignment`, each component value computed ONCE (its
cache fills forward to ~`√n` and answers all revisits for free) — where the
spec rail recomputes both components from scratch at every position. -/
def fairPairFirstNCached (sA : StreamFor gA) (sB : StreamFor gB)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (n : ℕ) : List (A × B) :=
  fairPairCachedGo fairPairAssignment sA sB hA hB (GenCache.init sA) (GenCache.init sB) 0 n

/-- The driver law, builder form: the cached driver equals the fair pair
generator's prefix. -/
theorem fairPairFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (n : ℕ) :
    fairPairFirstNCached sA sB hA hB n
      = (List.range n).filterMap (fairPairGen gA gB hA hB).gen := by
  rw [List.range_eq_range']
  exact fairPairCachedGo_eq fairPairAssignment sA sB hA hB _ _ 0 n

/-- **The driver law, instance form**: the cached driver over the components'
registered instances equals `firstN (A × B) n` — the composite instance
`instExhaustiveGeneratorProd` IS `fairPairGen` at those arguments. -/
theorem fairPairFirstNCached_eq_firstN {A B : Type*} [instA : ExhaustiveGenerator A]
    [Contiguous A] [Infinite A] [instB : ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    (sA : StreamFor instA) (sB : StreamFor instB) (n : ℕ) :
    fairPairFirstNCached sA sB gen_ne_none_of_infinite gen_ne_none_of_infinite n
      = firstN (A × B) n :=
  fairPairFirstNCached_eq sA sB gen_ne_none_of_infinite gen_ne_none_of_infinite n

/-! ### The cached fair triple driver -/

/-- Core walker for the cached fair triple driver (3-slot analogue of
`fairPairCachedGo`). -/
def fairTripleCachedGo (P : BitAssignment 3) (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) :
    GenCache sA → GenCache sB → GenCache sC → ℕ → ℕ → List (A × B × C)
  | _, _, _, _, 0 => []
  | cA, cB, cC, k, n + 1 =>
    let rA := cA.get (P.deinterleave 0 k)
    let rB := cB.get (P.deinterleave 1 k)
    let rC := cC.get (P.deinterleave 2 k)
    (rA.1.get (cA.get_fst_isSome hA _), rB.1.get (cB.get_fst_isSome hB _),
        rC.1.get (cC.get_fst_isSome hC _)) ::
      fairTripleCachedGo P sA sB sC hA hB hC rA.2 rB.2 rC.2 (k + 1) n

/-- The walker law for triples. -/
theorem fairTripleCachedGo_eq (P : BitAssignment 3) (sA : StreamFor gA)
    (sB : StreamFor gB) (sC : StreamFor gC) (hA : ∀ n, gA.gen n ≠ none)
    (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none)
    (cA : GenCache sA) (cB : GenCache sB) (cC : GenCache sC) (k n : ℕ) :
    fairTripleCachedGo P sA sB sC hA hB hC cA cB cC k n
      = (List.range' k n).filterMap (fairTripleGenWith P gA gB gC hA hB hC).gen := by
  induction n generalizing cA cB cC k with
  | zero => rfl
  | succ m ih =>
    have hgk : (fairTripleGenWith P gA gB gC hA hB hC).gen k
        = some ((gA.gen (P.deinterleave 0 k)).get (Option.isSome_iff_ne_none.mpr (hA _)),
          (gB.gen (P.deinterleave 1 k)).get (Option.isSome_iff_ne_none.mpr (hB _)),
          (gC.gen (P.deinterleave 2 k)).get (Option.isSome_iff_ne_none.mpr (hC _))) := rfl
    show ((cA.get (P.deinterleave 0 k)).1.get (cA.get_fst_isSome hA _),
        (cB.get (P.deinterleave 1 k)).1.get (cB.get_fst_isSome hB _),
        (cC.get (P.deinterleave 2 k)).1.get (cC.get_fst_isSome hC _))
        :: fairTripleCachedGo P sA sB sC hA hB hC (cA.get (P.deinterleave 0 k)).2
          (cB.get (P.deinterleave 1 k)).2 (cC.get (P.deinterleave 2 k)).2 (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap (fairTripleGenWith P gA gB gC hA hB hC).gen
    rw [List.filterMap_cons_some hgk, ih]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨option_get_congr (GenCache.get_fst cA _) _ _,
      option_get_congr (GenCache.get_fst cB _) _ _,
      option_get_congr (GenCache.get_fst cC _) _ _⟩

/-- **The cached fair triple driver** (weight-1 flat 3-way interleave). -/
def fairTripleFirstNCached (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none)
    (n : ℕ) : List (A × B × C) :=
  fairTripleCachedGo fairTripleAssignment sA sB sC hA hB hC
    (GenCache.init sA) (GenCache.init sB) (GenCache.init sC) 0 n

/-- The triple driver law, builder form. -/
theorem fairTripleFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (n : ℕ) :
    fairTripleFirstNCached sA sB sC hA hB hC n
      = (List.range n).filterMap (fairTripleGen gA gB gC hA hB hC).gen := by
  rw [List.range_eq_range']
  exact fairTripleCachedGo_eq fairTripleAssignment sA sB sC hA hB hC _ _ _ 0 n

/-- The triple driver law, instance form (`instExhaustiveGeneratorProd3`). -/
theorem fairTripleFirstNCached_eq_firstN {A B C : Type*} [instA : ExhaustiveGenerator A]
    [Contiguous A] [Infinite A] [instB : ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [instC : ExhaustiveGenerator C] [Contiguous C] [Infinite C]
    (sA : StreamFor instA) (sB : StreamFor instB) (sC : StreamFor instC) (n : ℕ) :
    fairTripleFirstNCached sA sB sC gen_ne_none_of_infinite gen_ne_none_of_infinite
        gen_ne_none_of_infinite n
      = firstN (A × B × C) n :=
  fairTripleFirstNCached_eq sA sB sC gen_ne_none_of_infinite gen_ne_none_of_infinite
    gen_ne_none_of_infinite n

/-! ### The cached fair quadruple driver -/

/-- Core walker for the cached fair quadruple driver (4-slot analogue of
`fairPairCachedGo`). -/
def fairQuadrupleCachedGo (P : BitAssignment 4) (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (sD : StreamFor gD) (hA : ∀ n, gA.gen n ≠ none)
    (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none) :
    GenCache sA → GenCache sB → GenCache sC → GenCache sD → ℕ → ℕ → List (A × B × C × D)
  | _, _, _, _, _, 0 => []
  | cA, cB, cC, cD, k, n + 1 =>
    let rA := cA.get (P.deinterleave 0 k)
    let rB := cB.get (P.deinterleave 1 k)
    let rC := cC.get (P.deinterleave 2 k)
    let rD := cD.get (P.deinterleave 3 k)
    (rA.1.get (cA.get_fst_isSome hA _), rB.1.get (cB.get_fst_isSome hB _),
        rC.1.get (cC.get_fst_isSome hC _), rD.1.get (cD.get_fst_isSome hD _)) ::
      fairQuadrupleCachedGo P sA sB sC sD hA hB hC hD rA.2 rB.2 rC.2 rD.2 (k + 1) n

/-- The walker law for quadruples. -/
theorem fairQuadrupleCachedGo_eq (P : BitAssignment 4) (sA : StreamFor gA)
    (sB : StreamFor gB) (sC : StreamFor gC) (sD : StreamFor gD)
    (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none)
    (cA : GenCache sA) (cB : GenCache sB) (cC : GenCache sC) (cD : GenCache sD) (k n : ℕ) :
    fairQuadrupleCachedGo P sA sB sC sD hA hB hC hD cA cB cC cD k n
      = (List.range' k n).filterMap (fairQuadrupleGenWith P gA gB gC gD hA hB hC hD).gen := by
  induction n generalizing cA cB cC cD k with
  | zero => rfl
  | succ m ih =>
    have hgk : (fairQuadrupleGenWith P gA gB gC gD hA hB hC hD).gen k
        = some ((gA.gen (P.deinterleave 0 k)).get (Option.isSome_iff_ne_none.mpr (hA _)),
          (gB.gen (P.deinterleave 1 k)).get (Option.isSome_iff_ne_none.mpr (hB _)),
          (gC.gen (P.deinterleave 2 k)).get (Option.isSome_iff_ne_none.mpr (hC _)),
          (gD.gen (P.deinterleave 3 k)).get (Option.isSome_iff_ne_none.mpr (hD _))) := rfl
    show ((cA.get (P.deinterleave 0 k)).1.get (cA.get_fst_isSome hA _),
        (cB.get (P.deinterleave 1 k)).1.get (cB.get_fst_isSome hB _),
        (cC.get (P.deinterleave 2 k)).1.get (cC.get_fst_isSome hC _),
        (cD.get (P.deinterleave 3 k)).1.get (cD.get_fst_isSome hD _))
        :: fairQuadrupleCachedGo P sA sB sC sD hA hB hC hD (cA.get (P.deinterleave 0 k)).2
          (cB.get (P.deinterleave 1 k)).2 (cC.get (P.deinterleave 2 k)).2
          (cD.get (P.deinterleave 3 k)).2 (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap
          (fairQuadrupleGenWith P gA gB gC gD hA hB hC hD).gen
    rw [List.filterMap_cons_some hgk, ih]
    congr 1
    rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨option_get_congr (GenCache.get_fst cA _) _ _,
      option_get_congr (GenCache.get_fst cB _) _ _,
      option_get_congr (GenCache.get_fst cC _) _ _,
      option_get_congr (GenCache.get_fst cD _) _ _⟩

/-- **The cached fair quadruple driver** (weight-1 flat 4-way interleave). -/
def fairQuadrupleFirstNCached (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (sD : StreamFor gD) (hA : ∀ n, gA.gen n ≠ none) (hB : ∀ n, gB.gen n ≠ none)
    (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none) (n : ℕ) : List (A × B × C × D) :=
  fairQuadrupleCachedGo fairQuadrupleAssignment sA sB sC sD hA hB hC hD
    (GenCache.init sA) (GenCache.init sB) (GenCache.init sC) (GenCache.init sD) 0 n

/-- The quadruple driver law, builder form. -/
theorem fairQuadrupleFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (sD : StreamFor gD) (hA : ∀ n, gA.gen n ≠ none)
    (hB : ∀ n, gB.gen n ≠ none) (hC : ∀ n, gC.gen n ≠ none) (hD : ∀ n, gD.gen n ≠ none)
    (n : ℕ) :
    fairQuadrupleFirstNCached sA sB sC sD hA hB hC hD n
      = (List.range n).filterMap (fairQuadrupleGen gA gB gC gD hA hB hC hD).gen := by
  rw [List.range_eq_range']
  exact fairQuadrupleCachedGo_eq fairQuadrupleAssignment sA sB sC sD hA hB hC hD _ _ _ _ 0 n

/-- The quadruple driver law, instance form (`instExhaustiveGeneratorProd4`). -/
theorem fairQuadrupleFirstNCached_eq_firstN {A B C D : Type*}
    [instA : ExhaustiveGenerator A] [Contiguous A] [Infinite A]
    [instB : ExhaustiveGenerator B] [Contiguous B] [Infinite B]
    [instC : ExhaustiveGenerator C] [Contiguous C] [Infinite C]
    [instD : ExhaustiveGenerator D] [Contiguous D] [Infinite D]
    (sA : StreamFor instA) (sB : StreamFor instB) (sC : StreamFor instC)
    (sD : StreamFor instD) (n : ℕ) :
    fairQuadrupleFirstNCached sA sB sC sD gen_ne_none_of_infinite gen_ne_none_of_infinite
        gen_ne_none_of_infinite gen_ne_none_of_infinite n
      = firstN (A × B × C × D) n :=
  fairQuadrupleFirstNCached_eq sA sB sC sD gen_ne_none_of_infinite gen_ne_none_of_infinite
    gen_ne_none_of_infinite gen_ne_none_of_infinite n

/-! ### The cached fair vec driver

All `m + 1` coordinates draw from the SAME component generator, so they
share ONE cache: each position first folds the coordinates' `get`s through
the cache (filling it), then reads the (now covered) indices back to
assemble the vec — `2(m + 1)` cache calls, at most one stream step per NEW
component index across the whole walk. -/

variable {T : Type*} {g : ExhaustiveGenerator T}

/-- Core walker for the cached fair vec driver. -/
def fairVecCachedGo (m : ℕ) (s : StreamFor g) (h : ∀ n, g.gen n ≠ none) :
    GenCache s → ℕ → ℕ → List (List.Vector T (m + 1))
  | _, _, 0 => []
  | c, k, n + 1 =>
    let c' := (List.finRange (m + 1)).foldl
      (fun cc j => (cc.get ((fairVecAssignment m).deinterleave j k)).2) c
    (List.Vector.ofFn fun j => ((c'.get ((fairVecAssignment m).deinterleave j k)).1).get
        (c'.get_fst_isSome h _)) ::
      fairVecCachedGo m s h c' (k + 1) n

/-- The walker law for vecs. -/
theorem fairVecCachedGo_eq (m : ℕ) (s : StreamFor g) (h : ∀ n, g.gen n ≠ none)
    (c : GenCache s) (k n : ℕ) :
    fairVecCachedGo m s h c k n
      = (List.range' k n).filterMap (fairVecGen g h m).gen := by
  induction n generalizing c k with
  | zero => rfl
  | succ p ih =>
    have hgk : (fairVecGen g h m).gen k
        = some (List.Vector.ofFn fun j => (g.gen ((fairVecAssignment m).deinterleave j k)).get
          (Option.isSome_iff_ne_none.mpr (h _))) := rfl
    show (List.Vector.ofFn fun j =>
        ((((List.finRange (m + 1)).foldl
            (fun cc j' => (cc.get ((fairVecAssignment m).deinterleave j' k)).2) c).get
          ((fairVecAssignment m).deinterleave j k)).1).get
          (((List.finRange (m + 1)).foldl
            (fun cc j' => (cc.get ((fairVecAssignment m).deinterleave j' k)).2)
              c).get_fst_isSome h _))
        :: fairVecCachedGo m s h
          ((List.finRange (m + 1)).foldl
            (fun cc j' => (cc.get ((fairVecAssignment m).deinterleave j' k)).2) c) (k + 1) p
      = (k :: List.range' (k + 1) p).filterMap (fairVecGen g h m).gen
    rw [List.filterMap_cons_some hgk, ih]
    congr 1
    refine congrArg List.Vector.ofFn (funext fun j => ?_)
    exact option_get_congr (GenCache.get_fst _ _) _ _

/-- **The cached fair vec driver** (positive length `m + 1`, one shared
component cache). -/
def fairVecFirstNCached (m : ℕ) (s : StreamFor g) (h : ∀ n, g.gen n ≠ none) (n : ℕ) :
    List (List.Vector T (m + 1)) :=
  fairVecCachedGo m s h (GenCache.init s) 0 n

/-- The vec driver law, builder form. -/
theorem fairVecFirstNCached_eq (m : ℕ) (s : StreamFor g) (h : ∀ n, g.gen n ≠ none)
    (n : ℕ) :
    fairVecFirstNCached m s h n = (List.range n).filterMap (fairVecGen g h m).gen := by
  rw [List.range_eq_range']
  exact fairVecCachedGo_eq m s h _ 0 n

/-- The vec driver law, instance form: `instExhaustiveGeneratorVector` at
positive length `m + 1` IS `fairVecGen` at these arguments. -/
theorem fairVecFirstNCached_eq_firstN {T : Type*} [inst : ExhaustiveGenerator T]
    [Contiguous T] [Infinite T] (s : StreamFor inst) (m n : ℕ) :
    fairVecFirstNCached m s gen_ne_none_of_infinite n
      = firstN (List.Vector T (m + 1)) n :=
  fairVecFirstNCached_eq m s gen_ne_none_of_infinite n

/-! ### The cached capped fair pair driver (raw layer)

The capped composites bind through their components' `Option` outputs — and
`GenCache.get` returns exactly those `Option`s, so the cache threads
straight through: the walker replays the RAW builder `fairPairGenCapped`
(counter-validity guard + `Option.bind`/`map` through cached reads),
skipping holes. Its law is stated against the raw builder's prefix: the
public capped INSTANCES are the raw builders hole-COMPRESSED
(`Compress.lean` re-indexes positions), so an instance-level fixed-`n` law
has no counter window to walk — a compressed prefix is this walker run
until `n` values accumulate. -/

/-- Core walker for the cached capped fair pair driver. -/
def fairPairCappedCachedGo (sA : StreamFor gA) (sB : StreamFor gB)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB) :
    GenCache sA → GenCache sB → ℕ → ℕ → List (A × B)
  | _, _, _, 0 => []
  | cA, cB, k, n + 1 =>
    let rA := cA.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 0 k)
    let rB := cB.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 1 k)
    (if (fairPairCappedAssignment slA.bits slB.bits).Valid k then
        rA.1.bind fun a => rB.1.map fun b => (a, b)
      else none).toList
      ++ fairPairCappedCachedGo sA sB slA slB rA.2 rB.2 (k + 1) n

/-- The walker law for capped pairs: the cached walk equals the RAW capped
builder's outputs on the counter window (holes skipped). -/
theorem fairPairCappedCachedGo_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB)
    (cA : GenCache sA) (cB : GenCache sB) (k n : ℕ) :
    fairPairCappedCachedGo sA sB slA slB cA cB k n
      = (List.range' k n).filterMap (fairPairGenCapped gA gB slA slB).gen := by
  induction n generalizing cA cB k with
  | zero => rfl
  | succ m ih =>
    show (if (fairPairCappedAssignment slA.bits slB.bits).Valid k then
          (cA.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 0 k)).1.bind
            fun a =>
              (cB.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 1 k)).1.map
                fun b => (a, b)
        else none).toList
        ++ fairPairCappedCachedGo sA sB slA slB
          (cA.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 0 k)).2
          (cB.get ((fairPairCappedAssignment slA.bits slB.bits).deinterleave 1 k)).2
          (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap (fairPairGenCapped gA gB slA slB).gen
    rw [GenCache.get_fst cA, GenCache.get_fst cB, ih]
    show ((fairPairGenCapped gA gB slA slB).gen k).toList
        ++ (List.range' (k + 1) m).filterMap (fairPairGenCapped gA gB slA slB).gen
      = (k :: List.range' (k + 1) m).filterMap (fairPairGenCapped gA gB slA slB).gen
    cases hgk : (fairPairGenCapped gA gB slA slB).gen k with
    | none => rw [List.filterMap_cons_none hgk]; rfl
    | some t => rw [List.filterMap_cons_some hgk]; rfl

/-- **The cached capped fair pair driver** (raw layer): walk `n` raw
counters, cached components, holes skipped. -/
def fairPairCappedFirstNCached (sA : StreamFor gA) (sB : StreamFor gB)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB) (n : ℕ) : List (A × B) :=
  fairPairCappedCachedGo sA sB slA slB (GenCache.init sA) (GenCache.init sB) 0 n

/-- The capped pair driver law (raw builder prefix). -/
theorem fairPairCappedFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB) (n : ℕ) :
    fairPairCappedFirstNCached sA sB slA slB n
      = (List.range n).filterMap (fairPairGenCapped gA gB slA slB).gen := by
  rw [List.range_eq_range']
  exact fairPairCappedCachedGo_eq sA sB slA slB _ _ 0 n

/-- Core walker for the cached capped fair triple driver (mirror of
`fairPairCappedCachedGo`). -/
def fairTripleCappedCachedGo (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC) :
    GenCache sA → GenCache sB → GenCache sC → ℕ → ℕ → List (A × B × C)
  | _, _, _, _, 0 => []
  | cA, cB, cC, k, n + 1 =>
    let rA := cA.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 0 k)
    let rB := cB.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 1 k)
    let rC := cC.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 2 k)
    (if (fairTripleCappedAssignment slA.bits slB.bits slC.bits).Valid k then
        rA.1.bind fun a => rB.1.bind fun b => rC.1.map fun c => (a, b, c)
      else none).toList
      ++ fairTripleCappedCachedGo sA sB sC slA slB slC rA.2 rB.2 rC.2 (k + 1) n

/-- The walker law for capped triples: the cached walk equals the RAW capped
builder's outputs on the counter window (holes skipped). -/
theorem fairTripleCappedCachedGo_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC)
    (cA : GenCache sA) (cB : GenCache sB) (cC : GenCache sC) (k n : ℕ) :
    fairTripleCappedCachedGo sA sB sC slA slB slC cA cB cC k n
      = (List.range' k n).filterMap (fairTripleGenCapped gA gB gC slA slB slC).gen := by
  induction n generalizing cA cB cC k with
  | zero => rfl
  | succ m ih =>
    show (if (fairTripleCappedAssignment slA.bits slB.bits slC.bits).Valid k then
          (cA.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 0 k)).1.bind
            fun a =>
              (cB.get
                ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 1 k)).1.bind
                fun b =>
                  (cC.get ((fairTripleCappedAssignment
                    slA.bits slB.bits slC.bits).deinterleave 2 k)).1.map fun c => (a, b, c)
        else none).toList
        ++ fairTripleCappedCachedGo sA sB sC slA slB slC
          (cA.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 0 k)).2
          (cB.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 1 k)).2
          (cC.get ((fairTripleCappedAssignment slA.bits slB.bits slC.bits).deinterleave 2 k)).2
          (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap (fairTripleGenCapped gA gB gC slA slB slC).gen
    rw [GenCache.get_fst cA, GenCache.get_fst cB, GenCache.get_fst cC, ih]
    show ((fairTripleGenCapped gA gB gC slA slB slC).gen k).toList
        ++ (List.range' (k + 1) m).filterMap (fairTripleGenCapped gA gB gC slA slB slC).gen
      = (k :: List.range' (k + 1) m).filterMap (fairTripleGenCapped gA gB gC slA slB slC).gen
    cases hgk : (fairTripleGenCapped gA gB gC slA slB slC).gen k with
    | none => rw [List.filterMap_cons_none hgk]; rfl
    | some t => rw [List.filterMap_cons_some hgk]; rfl

/-- **The cached capped fair triple driver** (raw layer). -/
def fairTripleCappedFirstNCached (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC) (n : ℕ) :
    List (A × B × C) :=
  fairTripleCappedCachedGo sA sB sC slA slB slC
    (GenCache.init sA) (GenCache.init sB) (GenCache.init sC) 0 n

/-- The capped triple driver law (raw builder prefix). -/
theorem fairTripleCappedFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC)
    (n : ℕ) :
    fairTripleCappedFirstNCached sA sB sC slA slB slC n
      = (List.range n).filterMap (fairTripleGenCapped gA gB gC slA slB slC).gen := by
  rw [List.range_eq_range']
  exact fairTripleCappedCachedGo_eq sA sB sC slA slB slC _ _ _ 0 n

/-- Core walker for the cached capped fair quadruple driver (mirror of
`fairPairCappedCachedGo`). -/
def fairQuadrupleCappedCachedGo (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (sD : StreamFor gD) (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC)
    (slD : @FairSlot D gD) :
    GenCache sA → GenCache sB → GenCache sC → GenCache sD → ℕ → ℕ → List (A × B × C × D)
  | _, _, _, _, _, 0 => []
  | cA, cB, cC, cD, k, n + 1 =>
    let A' := fairQuadrupleCappedAssignment slA.bits slB.bits slC.bits slD.bits
    let rA := cA.get (A'.deinterleave 0 k)
    let rB := cB.get (A'.deinterleave 1 k)
    let rC := cC.get (A'.deinterleave 2 k)
    let rD := cD.get (A'.deinterleave 3 k)
    (if A'.Valid k then
        rA.1.bind fun a => rB.1.bind fun b => rC.1.bind fun c => rD.1.map fun d => (a, b, c, d)
      else none).toList
      ++ fairQuadrupleCappedCachedGo sA sB sC sD slA slB slC slD rA.2 rB.2 rC.2 rD.2 (k + 1) n

/-- The walker law for capped quadruples. -/
theorem fairQuadrupleCappedCachedGo_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (sD : StreamFor gD) (slA : @FairSlot A gA) (slB : @FairSlot B gB)
    (slC : @FairSlot C gC) (slD : @FairSlot D gD) (cA : GenCache sA) (cB : GenCache sB)
    (cC : GenCache sC) (cD : GenCache sD) (k n : ℕ) :
    fairQuadrupleCappedCachedGo sA sB sC sD slA slB slC slD cA cB cC cD k n
      = (List.range' k n).filterMap
        (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen := by
  induction n generalizing cA cB cC cD k with
  | zero => rfl
  | succ m ih =>
    show (if (fairQuadrupleCappedAssignment slA.bits slB.bits slC.bits slD.bits).Valid k then
          (cA.get ((fairQuadrupleCappedAssignment
            slA.bits slB.bits slC.bits slD.bits).deinterleave 0 k)).1.bind fun a =>
              (cB.get ((fairQuadrupleCappedAssignment
                slA.bits slB.bits slC.bits slD.bits).deinterleave 1 k)).1.bind fun b =>
                  (cC.get ((fairQuadrupleCappedAssignment
                    slA.bits slB.bits slC.bits slD.bits).deinterleave 2 k)).1.bind fun c =>
                      (cD.get ((fairQuadrupleCappedAssignment
                        slA.bits slB.bits slC.bits slD.bits).deinterleave 3 k)).1.map
                        fun d => (a, b, c, d)
        else none).toList
        ++ fairQuadrupleCappedCachedGo sA sB sC sD slA slB slC slD
          (cA.get ((fairQuadrupleCappedAssignment
            slA.bits slB.bits slC.bits slD.bits).deinterleave 0 k)).2
          (cB.get ((fairQuadrupleCappedAssignment
            slA.bits slB.bits slC.bits slD.bits).deinterleave 1 k)).2
          (cC.get ((fairQuadrupleCappedAssignment
            slA.bits slB.bits slC.bits slD.bits).deinterleave 2 k)).2
          (cD.get ((fairQuadrupleCappedAssignment
            slA.bits slB.bits slC.bits slD.bits).deinterleave 3 k)).2
          (k + 1) m
      = (k :: List.range' (k + 1) m).filterMap
        (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen
    rw [GenCache.get_fst cA, GenCache.get_fst cB, GenCache.get_fst cC, GenCache.get_fst cD, ih]
    show ((fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen k).toList
        ++ (List.range' (k + 1) m).filterMap
          (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen
      = (k :: List.range' (k + 1) m).filterMap
        (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen
    cases hgk : (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen k with
    | none => rw [List.filterMap_cons_none hgk]; rfl
    | some t => rw [List.filterMap_cons_some hgk]; rfl

/-- **The cached capped fair quadruple driver** (raw layer). -/
def fairQuadrupleCappedFirstNCached (sA : StreamFor gA) (sB : StreamFor gB) (sC : StreamFor gC)
    (sD : StreamFor gD) (slA : @FairSlot A gA) (slB : @FairSlot B gB) (slC : @FairSlot C gC)
    (slD : @FairSlot D gD) (n : ℕ) : List (A × B × C × D) :=
  fairQuadrupleCappedCachedGo sA sB sC sD slA slB slC slD
    (GenCache.init sA) (GenCache.init sB) (GenCache.init sC) (GenCache.init sD) 0 n

/-- The capped quadruple driver law (raw builder prefix). -/
theorem fairQuadrupleCappedFirstNCached_eq (sA : StreamFor gA) (sB : StreamFor gB)
    (sC : StreamFor gC) (sD : StreamFor gD) (slA : @FairSlot A gA) (slB : @FairSlot B gB)
    (slC : @FairSlot C gC) (slD : @FairSlot D gD) (n : ℕ) :
    fairQuadrupleCappedFirstNCached sA sB sC sD slA slB slC slD n
      = (List.range n).filterMap
        (fairQuadrupleGenCapped gA gB gC gD slA slB slC slD).gen := by
  rw [List.range_eq_range']
  exact fairQuadrupleCappedCachedGo_eq sA sB sC sD slA slB slC slD _ _ _ _ 0 n

/-- Core walker for the cached capped fair vec driver: one shared component
cache across all `m + 1` coordinates (mirror of `fairVecCachedGo` with the
capped validity-and-`isSome` guard). -/
def fairVecCappedCachedGo (m : ℕ) (s : StreamFor g) (sl : @FairSlot T g) :
    GenCache s → ℕ → ℕ → List (List.Vector T (m + 1))
  | _, _, 0 => []
  | c, k, n + 1 =>
    let c' := (List.finRange (m + 1)).foldl
      (fun cc j => (cc.get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).2) c
    (if h : (fairVecCappedAssignment m sl.bits).Valid k ∧
        ∀ j, ((c'.get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).isSome then
        [List.Vector.ofFn fun j =>
          ((c'.get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).get (h.2 j)]
      else [])
      ++ fairVecCappedCachedGo m s sl c' (k + 1) n

/-- The walker law for capped vecs: the cached walk equals the RAW capped
builder's outputs on the counter window (holes skipped). Each emitted vec is
reconstructed from the shared cache (`GenCache.get_fst` identifies a cached
read with the underlying `gen`, so both the guard and the coordinates match
the raw builder). -/
theorem fairVecCappedCachedGo_eq (m : ℕ) (s : StreamFor g) (sl : @FairSlot T g)
    (c : GenCache s) (k n : ℕ) :
    fairVecCappedCachedGo m s sl c k n
      = (List.range' k n).filterMap (fairVecGenCapped g sl m).gen := by
  induction n generalizing c k with
  | zero => rfl
  | succ p ih =>
    show (if h : (fairVecCappedAssignment m sl.bits).Valid k ∧
          ∀ j, ((((List.finRange (m + 1)).foldl
            (fun cc j' => (cc.get ((fairVecCappedAssignment m sl.bits).deinterleave j' k)).2)
              c).get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).isSome then
          [List.Vector.ofFn fun j => ((((List.finRange (m + 1)).foldl
            (fun cc j' => (cc.get ((fairVecCappedAssignment m sl.bits).deinterleave j' k)).2)
              c).get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).get (h.2 j)]
        else [])
        ++ fairVecCappedCachedGo m s sl ((List.finRange (m + 1)).foldl
          (fun cc j' => (cc.get ((fairVecCappedAssignment m sl.bits).deinterleave j' k)).2)
            c) (k + 1) p
      = (k :: List.range' (k + 1) p).filterMap (fairVecGenCapped g sl m).gen
    rw [ih]
    have hcell : ∀ c' : GenCache s,
        (if h : (fairVecCappedAssignment m sl.bits).Valid k ∧
            ∀ j, ((c'.get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).isSome then
            [List.Vector.ofFn fun j =>
              ((c'.get ((fairVecCappedAssignment m sl.bits).deinterleave j k)).1).get (h.2 j)]
          else [])
          = ((fairVecGenCapped g sl m).gen k).toList := by
      intro c'
      simp only [GenCache.get_fst]
      rw [show (fairVecGenCapped g sl m).gen k
          = dite ((fairVecCappedAssignment m sl.bits).Valid k ∧
              ∀ j, (g.gen ((fairVecCappedAssignment m sl.bits).deinterleave j k)).isSome)
            (fun h => some (List.Vector.ofFn fun j =>
              (g.gen ((fairVecCappedAssignment m sl.bits).deinterleave j k)).get (h.2 j)))
            (fun _ => none) from rfl, apply_dite Option.toList]
      simp only [Option.toList_some, Option.toList_none]
    rw [hcell]
    cases hgk : (fairVecGenCapped g sl m).gen k with
    | none => rw [List.filterMap_cons_none hgk]; rfl
    | some t => rw [List.filterMap_cons_some hgk]; rfl

/-- **The cached capped fair vec driver** (positive length `m + 1`, one shared
component cache). -/
def fairVecCappedFirstNCached (m : ℕ) (s : StreamFor g) (sl : @FairSlot T g) (n : ℕ) :
    List (List.Vector T (m + 1)) :=
  fairVecCappedCachedGo m s sl (GenCache.init s) 0 n

/-- The capped vec driver law (raw builder prefix). -/
theorem fairVecCappedFirstNCached_eq (m : ℕ) (s : StreamFor g) (sl : @FairSlot T g) (n : ℕ) :
    fairVecCappedFirstNCached m s sl n
      = (List.range n).filterMap (fairVecGenCapped g sl m).gen := by
  rw [List.range_eq_range']
  exact fairVecCappedCachedGo_eq m s sl _ 0 n

end ExhaustiveGenerator

/-! ### Guards

The cached drivers replay the existing doctest tables (the laws made
concrete), plus the case caching exists for: Calkin–Wilf components, whose
spec rail pays O(index) bignum steps PER call — the cached run computes
each rational once. -/

-- Cache behavior sanity: a fill to index 5 grows the cache to exactly 6;
-- covered reads (a smaller index, then the SAME index again) return the
-- right values with the cache size unchanged.
#guard (let r5 := (GenCache.init naturalsStream).get 5
        let r3 := r5.2.get 3
        let r5' := r5.2.get 5
        r5.1.map (·.toNat) == some 5 && r5.2.cache.size == 6
          && r3.1.map (·.toNat) == some 3 && r3.2.cache.size == 6
          && r5'.1.map (·.toNat) == some 5 && r5'.2.cache.size == 6)

open ExhaustiveGenerator

-- The cached pair driver replays the Z-order pairs doctest…
#guard (fairPairFirstNCached naturalsStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite 10).map
    (fun p => (p.1.toNat, p.2.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1)]

-- …and THE motivating case: Calkin–Wilf rationals × naturals. Every
-- rational is computed once (the rational cache fills forward through
-- ~√n Stern–Brocot steps total); the spec rail re-iterates from `(0, 1)`
-- at every one of the `n` positions.
#guard (fairPairFirstNCached positiveRationalsStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite 10).map
    (fun p => (p.1.val.toString, p.2.toNat))
  = [("1", 0), ("1", 1), ("1/2", 0), ("1/2", 1), ("1", 2), ("1", 3), ("1/2", 2), ("1/2", 3),
     ("2", 0), ("2", 1)]

-- The longer demonstration run: 100 pairs, pinned to the spec rail and by
-- value at the end (`k = 99` deinterleaves to `(5, 9)`; rational index 5 is
-- `2/3` in Calkin–Wilf order).
#guard (fairPairFirstNCached positiveRationalsStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite 100).map
    (fun p => (p.1.val.toString, p.2.toNat))
  = (firstN ({q : AzRat // 0 < q} × AzNat) 100).map (fun p => (p.1.val.toString, p.2.toNat))
#guard ((fairPairFirstNCached positiveRationalsStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite 100).getLast?).map
    (fun p => (p.1.val.toString, p.2.toNat)) = some ("2/3", 9)

-- The cached triple driver replays the heterogeneous flat-triple table.
#guard (fairTripleFirstNCached naturalsStream integersStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite gen_ne_none_of_infinite 10).map
    (fun t => (t.1.toNat, t.2.1.toInt, t.2.2.toNat))
  = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
     (0, 0, 2), (0, 0, 3)]

-- The cached quadruple driver replays the 4-way Z-order table.
#guard (fairQuadrupleFirstNCached naturalsStream naturalsStream naturalsStream naturalsStream
    gen_ne_none_of_infinite gen_ne_none_of_infinite gen_ne_none_of_infinite
    gen_ne_none_of_infinite 16).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.1.toNat, t.2.2.2.toNat))
  = [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1),
     (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 1, 0), (0, 1, 1, 1),
     (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 0), (1, 0, 1, 1),
     (1, 1, 0, 0), (1, 1, 0, 1), (1, 1, 1, 0), (1, 1, 1, 1)]

-- The cached vec driver: length 2 replays the pairs table as lists, and a
-- length-3 Calkin–Wilf vec (ONE shared rational cache across all three
-- coordinates) matches the spec rail.
#guard (fairVecFirstNCached 1 naturalsStream gen_ne_none_of_infinite 10).map
    (fun v => v.toList.map (·.toNat))
  = [[0, 0], [0, 1], [1, 0], [1, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1]]
#guard (fairVecFirstNCached 2 positiveRationalsStream gen_ne_none_of_infinite 20).map
    (fun v => v.toList.map (·.val.toString))
  = (firstN (List.Vector {q : AzRat // 0 < q} 3) 20).map
    (fun v => v.toList.map (·.val.toString))

-- The cached capped pair driver (raw layer) replays the `Ordering × AzNat`
-- raw hand table: 14 counters, holes at `k = 10, 11` skipped, 12 values.
#guard (fairPairCappedFirstNCached (StreamFor.ofGen orderingsIncreasingGen) naturalsStream
    inferInstance inferInstance 14).map (fun p => (p.1, p.2.toNat))
  = [(.lt, 0), (.lt, 1), (.eq, 0), (.eq, 1), (.lt, 2), (.lt, 3), (.eq, 2), (.eq, 3),
     (.gt, 0), (.gt, 1), (.gt, 2), (.gt, 3)]

-- The cached capped triple driver (raw layer): `Ordering × Ordering × AzNat`
-- (two finite slots, one infinite). Over the first 16 counters no hole
-- truncates, so this raw prefix matches the public instance's `firstN`.
#guard (fairTripleCappedFirstNCached (StreamFor.ofGen orderingsIncreasingGen)
    (StreamFor.ofGen orderingsIncreasingGen) naturalsStream
    inferInstance inferInstance inferInstance 16).map (fun t => (t.1, t.2.1, t.2.2.toNat))
  = [(.lt, .lt, 0), (.lt, .lt, 1), (.lt, .eq, 0), (.lt, .eq, 1),
     (.eq, .lt, 0), (.eq, .lt, 1), (.eq, .eq, 0), (.eq, .eq, 1),
     (.lt, .lt, 2), (.lt, .lt, 3), (.lt, .eq, 2), (.lt, .eq, 3),
     (.eq, .lt, 2), (.eq, .lt, 3), (.eq, .eq, 2), (.eq, .eq, 3)]

-- The cached capped vec driver (raw layer): `List.Vector Ordering 2`. The raw
-- counter walk skips holes, so 12 counters yield the 8 raw values below — one
-- SHORT of the compressed instance's 9-element `firstN` (the 9th, `[gt, gt]`,
-- sits past counter 12). This is the raw-layer/instance distinction the
-- driver documents.
#guard (fairVecCappedFirstNCached 1 (StreamFor.ofGen orderingsIncreasingGen)
    inferInstance 12).map (fun v => v.toList)
  = [[.lt, .lt], [.lt, .eq], [.eq, .lt], [.eq, .eq],
     [.lt, .gt], [.eq, .gt], [.gt, .lt], [.gt, .eq]]

end Azurite
