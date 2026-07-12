/-
  `FairCapped` — fair products and vecs with FINITE (capped) components:
  the `CappedBitAssignment` siblings of `FairPairs`/`FairTuples`/`FairVecs`
  (Malachite `exhaustive_pairs` etc. with `BitDistributor` max-bits caps).

  The per-component data is the `FairSlot` class: an infinite component
  contributes an uncapped slot (`bits = none`), a finite one a slot capped at
  `(card - 1).size` bits — the width of its largest index. The capped fair
  generators run the counter through `cappedRoundRobin` (`update_bit_map`'s
  weight-1 drop-out rotation): while every slot is active the enumeration is
  the familiar Z-order, and once a finite slot's bits are exhausted the
  remaining slots absorb all further counter bits.

  HOLES AND COMPRESSION: a finite component whose `card` is NOT a power of
  two occupies only `card` of the `2 ^ bits` index patterns its slot can
  carry, so some counters decode to an out-of-range component index — the RAW
  builder returns `none` there (an INTERIOR hole, unlike the initial-segment
  `none`s of the lex generators). Likewise, when ALL slots are capped,
  counters `k ≥ 2 ^ ∑ bits` are invalid. The raw builders (`fair*GenCapped`)
  remain the SEMANTIC layer; the public instances run them through the FAST
  hole compression of `CompressFast.lean` (`compressFast`, re-indexing along
  the increasing enumeration of the live counters by digit-DP rank/unrank —
  gen-pointwise identical to `Compress.lean`'s spec `compress`) — the VALUE
  sequence is
  unchanged (compression deletes gaps, order untouched; hole-free cases like
  power-of-two cards are gen-pointwise untouched), but positions are DENSE
  again, so capped composites are `Contiguous` and, when every component is
  finite, carry `FiniteGenerator` data at the exact product card (pair
  `cardA * cardB`, vec `card ^ n`) — hence a `FairSlot`. The live count fed
  to `compress` is `mulCount` over the per-slot `FairSlot.count`s, with the
  count hypotheses supplied by `hasCount_h`/`hasCount_h'` from the
  `HasCount` cardinality data (`FairSlot.hasCount`, composed by
  `HasCount.prod`/`HasCount.vector`).

  Instance priorities (each capped variant BELOW its all-infinite counterpart,
  since `FairSlot` also covers infinite components, and ABOVE the lower-arity
  capped variants so mixed products resolve at maximal flat width):

    quad 1200 > capped quad 1150 > triple 1100 > capped triple 1050
      > pair 1000 > capped pair 900;   vec 1000 > capped vec 900.

  5-TUPLES: `A × B × C × D × E` resolves as the flat quadruple over
  `A, B, C, (D × E)` — and the tail pair now ALWAYS has a `FairSlot`: an
  all-infinite or mixed pair is `Contiguous` + `Infinite` (infinite slot), an
  all-finite pair carries `FiniteGenerator` data (capped slot). Chunk 4b's
  documented finite-tail gap is CLOSED (see the resolution pins below).

  The compression consumes one hypothesis beyond the counts: the per-arity
  LIVENESS BRIDGES `fair*GenCapped_gen_isSome_iff` (proved next to the
  builders below) identify each raw builder's producing counters with
  `CompressFast.Live`, which is what lets `compressFast` replace the spec
  `unrank`'s linear scan by the digit-DP `fastUnrank` — reaching compressed
  position `i` in `O(bits³ · m)`, so even DEEP single accesses go through the
  INSTANCE (see the `10^6`-index guards and the `10^12 + 39`-card scale
  demonstration at the bottom).
-/
import Azurite.ExhaustiveGenerator.FairTuples
import Azurite.ExhaustiveGenerator.FairVecs
import Azurite.ExhaustiveGenerator.BitInterleaveCapped
import Azurite.ExhaustiveGenerator.CompressFast
import Azurite.ExhaustiveGenerator.Enums
import Mathlib.Algebra.BigOperators.Fin

namespace Azurite

/-! ### The `FairSlot` class — per-component slot spec -/

/-- A **fair slot spec** for a component type `T`: the data a fair capped
product generator needs about one of its components. `bits = none` marks an
INFINITE slot (the generator never runs out); `bits = some b` a slot capped at
`b` counter bits, carrying `card` values on the initial index segment
`0, …, card - 1` with `card ≤ 2 ^ b` (so every producible index fits in the
slot's bits; indices in `[card, 2 ^ b)` are the HOLES). `card` is junk (`0`)
on infinite slots. Both `bits` and `card` are DATA — `bits` feeds the
`cappedRoundRobin` cap vector at runtime, and `card` is the live-count bound
the hole compression consumes (via `FairSlot.count`/`mulCount`). NB the named
`[inst : …]` binding (same gotcha as
`Contiguous`/`FiniteGenerator`): the spec fields must refer to THIS instance's
`gen`. -/
class FairSlot (T : Type*) [inst : ExhaustiveGenerator T] where
  /-- `none`: an infinite slot; `some b`: a slot capped at `b` counter bits. -/
  bits : Option ℕ
  /-- The number of values produced (meaningful on capped slots; `0` junk on
  infinite ones). -/
  card : ℕ
  /-- An infinite slot's generator never runs out. -/
  spec_none : bits = none → ∀ n, inst.gen n ≠ none
  /-- A capped slot's generator produces exactly the indices below `card`,
  and `card` fits in the slot's `b` bits. -/
  spec_some : ∀ b, bits = some b →
    card ≤ 2 ^ b ∧ (∀ n, n < card → inst.gen n ≠ none) ∧ (∀ n, card ≤ n → inst.gen n = none)

open ExhaustiveGenerator in
/-- **The infinite slot.** A `Contiguous` generator on an `Infinite` type is an
uncapped slot: `bits = none` via the infiniteness bridge
`gen_ne_none_of_infinite`. Low priority (like `FiniteGenerator.toContiguous`)
so it is the fallback; it never actually overlaps `fairSlotOfFinite` (no type
is both `Infinite` and finitely generated). -/
instance (priority := 100) fairSlotOfInfinite {T : Type*} [ExhaustiveGenerator T]
    [Contiguous T] [Infinite T] : FairSlot T where
  bits := none
  card := 0
  spec_none _ := gen_ne_none_of_infinite
  spec_some _ h := nomatch h

/-- **The finite slot.** A `FiniteGenerator` is a slot capped at
`(card - 1).size` bits — the width of the largest produced index; `card ≤ 2 ^
bits` is `Nat.lt_size_self` (with the `card = 0` empty-type edge case landing
on `(0 - 1).size = 0` and `0 ≤ 2 ^ 0`), and the index bounds are the
generator's own `gen_some`/`gen_none`. -/
instance fairSlotOfFinite {T : Type*} [ExhaustiveGenerator T] [FiniteGenerator T] :
    FairSlot T where
  bits := some ((FiniteGenerator.card (T := T) - 1).size)
  card := FiniteGenerator.card (T := T)
  spec_none h := nomatch h
  spec_some b hb := by
    obtain rfl := Option.some.inj hb
    have hlt := Nat.lt_size_self (FiniteGenerator.card (T := T) - 1)
    exact ⟨by omega, FiniteGenerator.gen_some, FiniteGenerator.gen_none⟩

namespace FairSlot

/-- **The producing-index bound.** Any index at which the generator produces a
value fits in a capped slot's bits: it is below `card` (else `spec_some`'s
`none` half would contradict production) and `card ≤ 2 ^ b`. This is exactly
the per-slot hypothesis `deinterleave_interleave` needs of the witness index
tuple `![idx a, idx b, …]`. -/
theorem lt_two_pow_of_gen_some {T : Type*} {g : ExhaustiveGenerator T} (s : @FairSlot T g)
    {n : ℕ} {t : T} (h : g.gen n = some t) : ∀ b, s.bits = some b → n < 2 ^ b := by
  intro b hb
  obtain ⟨hcard, -, hnone⟩ := s.spec_some b hb
  by_contra hge
  rw [Nat.not_lt] at hge
  exact Option.some_ne_none _ (h.symm.trans (hnone n (by omega)))

/-- The slot's **optional value count**: `none` for an infinite slot, `some
card` for a capped one. This is the per-component input to `mulCount`, whose
product is the live count of a capped product generator. -/
def count {T : Type*} {g : ExhaustiveGenerator T} (s : @FairSlot T g) : Option ℕ :=
  s.bits.map fun _ => s.card

open ExhaustiveGenerator in
/-- The slot spec is honest cardinality data for its type: an infinite slot's
never-`none` generator injects `ℕ` into `T`, a capped slot's exact-`card`
production shape gives `T ≃ Fin card` (`equivFin`). This is what feeds the
compression count hypotheses (`hasCount_h`/`hasCount_h'`). -/
theorem hasCount {T : Type*} {g : ExhaustiveGenerator T} (s : @FairSlot T g) :
    HasCount T s.count := by
  rcases hb : s.bits with _ | b
  · -- Infinite slot: `n ↦ (gen n).get` is injective by index uniqueness.
    simp only [FairSlot.count, hb, Option.map_none]
    have hne := s.spec_none hb
    refine ⟨fun n => (g.gen n).get (Option.isSome_iff_ne_none.mpr (hne n)), ?_⟩
    intro n m hnm
    have hnm' : (g.gen n).get (Option.isSome_iff_ne_none.mpr (hne n))
        = (g.gen m).get (Option.isSome_iff_ne_none.mpr (hne m)) := hnm
    obtain ⟨j, -, hu⟩ := g.occurs_exactly_once
      ((g.gen n).get (Option.isSome_iff_ne_none.mpr (hne n)))
    have h1 : g.gen n = some ((g.gen n).get (Option.isSome_iff_ne_none.mpr (hne n))) :=
      (Option.some_get _).symm
    have h2 : g.gen m = some ((g.gen n).get (Option.isSome_iff_ne_none.mpr (hne n))) := by
      rw [hnm']
      exact (Option.some_get _).symm
    rw [hu n h1, hu m h2]
  · -- Capped slot: production exactly on `[0, card)` is `equivFin`'s shape.
    simp only [FairSlot.count, hb, Option.map_some]
    obtain ⟨-, hsome, hnone⟩ := s.spec_some b hb
    exact ⟨@equivFin T g s.card hnone hsome⟩

end FairSlot

/-- Cardinality data for fixed-length vecs: `T ≃ Fin c` gives
`List.Vector T n ≃ Fin (c ^ n)` (via `Fin n → T` and `finFunctionFinEquiv`).
The vec analogue of `HasCount.prod`. -/
theorem HasCount.vector {T : Type*} {c : ℕ} (hc : HasCount T (some c)) (n : ℕ) :
    HasCount (List.Vector T n) (some (c ^ n)) := by
  obtain ⟨e⟩ := hc
  exact ⟨(Equiv.vectorEquivFin T n).trans
    ((Equiv.arrowCongr (Equiv.refl (Fin n)) e).trans finFunctionFinEquiv)⟩

/-! ### The capped slot assignments

Unlike the fixed uncapped `fairPairAssignment` etc., these take the slot caps
as arguments (the caps are per-component data). Each is `cappedRoundRobin` on
the cap vector; with all caps `none` it degenerates to the uncapped
`roundRobin` assignment (`cappedRoundRobin_pos_none`), so the capped
generators reproduce the all-infinite Z-order until a cap bites. -/

/-- The 2-slot capped drop-out rotation underlying the capped fair pair: slot 0
is the FIRST component, slot 1 (the last still-active slot each round) owns
the least-significant live counter bit. -/
def fairPairCappedAssignment (bA bB : Option ℕ) : CappedBitAssignment 2 :=
  cappedRoundRobin ![bA, bB]

/-- The 3-slot capped drop-out rotation underlying the capped fair triple. -/
def fairTripleCappedAssignment (bA bB bC : Option ℕ) : CappedBitAssignment 3 :=
  cappedRoundRobin ![bA, bB, bC]

/-- The 4-slot capped drop-out rotation underlying the capped fair quadruple. -/
def fairQuadrupleCappedAssignment (bA bB bC bD : Option ℕ) : CappedBitAssignment 4 :=
  cappedRoundRobin ![bA, bB, bC, bD]

/-- The `(m + 1)`-slot capped drop-out rotation underlying the capped fair
fixed-length vec: every coordinate shares the single component cap `b`. -/
def fairVecCappedAssignment (m : ℕ) (b : Option ℕ) : CappedBitAssignment (m + 1) :=
  cappedRoundRobin fun _ => b

namespace ExhaustiveGenerator

/-- **The capped fair pair generator (builder form).** Given two generators
with slot specs `sA`/`sB`, enumerate the PLAIN product `A × B` fairly with
finite components allowed: position `k`'s bits are deinterleaved by the capped
assignment into the two component indices. The component `gen`s already return
`none` above their cards, which IS the interior-hole check (non-power-of-two
cards); only the counter-validity guard `Valid k` (every set bit of `k` at an
owned position — automatic when either slot is infinite) needs adding, so the
`gen` is a guarded `Option.bind`/`map` through the component outputs.
Exactly-once: the unique index of `(a, b)` is `interleave ![idx a, idx b]` —
the per-slot bounds `idx < card ≤ 2 ^ bits` (`lt_two_pow_of_gen_some`) feed
`deinterleave_interleave` and `interleave_valid` discharges the guard;
conversely a producing `k` is `Valid` (from the `gen` shape) with each
`deinterleave j k` pinned by the components' uniqueness, so
`interleave_deinterleave` pins `k`. -/
@[reducible] def fairPairGenCapped {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (sA : @FairSlot A gA) (sB : @FairSlot B gB) :
    ExhaustiveGenerator (A × B) where
  gen k :=
    if (fairPairCappedAssignment sA.bits sB.bits).Valid k then
      (gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)).bind fun a =>
        (gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)).map fun b =>
          (a, b)
    else none
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    have hcap : ∀ j bb, (fairPairCappedAssignment sA.bits sB.bits).cap j = some bb →
        (![iA, iB] : Fin 2 → ℕ) j < 2 ^ bb := by
      intro j bb hj
      match j with
      | ⟨0, _⟩ => exact sA.lt_two_pow_of_gen_some hiA bb hj
      | ⟨1, _⟩ => exact sB.lt_two_pow_of_gen_some hiB bb hj
    refine ⟨(fairPairCappedAssignment sA.bits sB.bits).interleave ![iA, iB], ?_, ?_⟩
    · -- Existence: the witness is valid and decodes back to `(iA, iB)`.
      have h0 : gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0
          ((fairPairCappedAssignment sA.bits sB.bits).interleave ![iA, iB])) = some a := by
        rw [(fairPairCappedAssignment sA.bits sB.bits).deinterleave_interleave ![iA, iB] hcap 0]
        exact hiA
      have h1 : gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1
          ((fairPairCappedAssignment sA.bits sB.bits).interleave ![iA, iB])) = some b := by
        rw [(fairPairCappedAssignment sA.bits sB.bits).deinterleave_interleave ![iA, iB] hcap 1]
        exact hiB
      beta_reduce
      rw [if_pos ((fairPairCappedAssignment sA.bits sB.bits).interleave_valid ![iA, iB]),
        h0, h1]
      rfl
    · -- Uniqueness: a producing position is valid with pinned components.
      intro k hk
      have hk' : (if (fairPairCappedAssignment sA.bits sB.bits).Valid k then
            (gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)).bind
              fun a' => (gB.gen
                ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)).map fun b' =>
                  (a', b')
          else none) = some (a, b) := hk
      by_cases hv : (fairPairCappedAssignment sA.bits sB.bits).Valid k
      · rw [if_pos hv] at hk'
        rcases hga : gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)
          with _ | a'
        · rw [hga] at hk'
          exact absurd hk' (by simp)
        rcases hgb : gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)
          with _ | b'
        · rw [hga, hgb] at hk'
          exact absurd hk' (by simp)
        rw [hga, hgb] at hk'
        have heq : (a', b') = (a, b) := Option.some.inj hk'
        injection heq with ha' hb'
        subst ha'; subst hb'
        have htup : (fairPairCappedAssignment sA.bits sB.bits).deinterleaveTuple k
            = ![iA, iB] := by
          funext j
          match j with
          | ⟨0, _⟩ => exact huA _ hga
          | ⟨1, _⟩ => exact huB _ hgb
        calc k = (fairPairCappedAssignment sA.bits sB.bits).interleave
              ((fairPairCappedAssignment sA.bits sB.bits).deinterleaveTuple k) :=
              ((fairPairCappedAssignment sA.bits sB.bits).interleave_deinterleave k hv).symm
          _ = (fairPairCappedAssignment sA.bits sB.bits).interleave ![iA, iB] := by rw [htup]
      · rw [if_neg hv] at hk'
        exact absurd hk' (by simp)

/-- **The capped fair triple generator (builder form).** The 3-slot analogue of
`fairPairGenCapped`: a guarded `Option.bind` chain through the three component
outputs at the deinterleaved indices, holes reported by the component `gen`s
themselves and counter validity by the `Valid` guard. The unique index of
`(a, b, c)` is `interleave ![idx a, idx b, idx c]`. -/
@[reducible] def fairTripleGenCapped {A B C : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C) (sA : @FairSlot A gA)
    (sB : @FairSlot B gB) (sC : @FairSlot C gC) : ExhaustiveGenerator (A × B × C) where
  gen k :=
    if (fairTripleCappedAssignment sA.bits sB.bits sC.bits).Valid k then
      (gA.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 0 k)).bind
        fun a =>
          (gB.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 1 k)).bind
            fun b =>
              (gC.gen ((fairTripleCappedAssignment
                sA.bits sB.bits sC.bits).deinterleave 2 k)).map fun c => (a, b, c)
    else none
  occurs_exactly_once := by
    rintro ⟨a, b, c⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    obtain ⟨iC, hiC, huC⟩ := gC.occurs_exactly_once c
    have hcap : ∀ j bb, (fairTripleCappedAssignment sA.bits sB.bits sC.bits).cap j = some bb →
        (![iA, iB, iC] : Fin 3 → ℕ) j < 2 ^ bb := by
      intro j bb hj
      match j with
      | ⟨0, _⟩ => exact sA.lt_two_pow_of_gen_some hiA bb hj
      | ⟨1, _⟩ => exact sB.lt_two_pow_of_gen_some hiB bb hj
      | ⟨2, _⟩ => exact sC.lt_two_pow_of_gen_some hiC bb hj
    refine ⟨(fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave ![iA, iB, iC],
      ?_, ?_⟩
    · -- Existence: the witness is valid and decodes back to `(iA, iB, iC)`.
      have h0 : gA.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 0
          ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave ![iA, iB, iC]))
          = some a := by
        rw [(fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave_interleave
          ![iA, iB, iC] hcap 0]
        exact hiA
      have h1 : gB.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 1
          ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave ![iA, iB, iC]))
          = some b := by
        rw [(fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave_interleave
          ![iA, iB, iC] hcap 1]
        exact hiB
      have h2 : gC.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 2
          ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave ![iA, iB, iC]))
          = some c := by
        rw [(fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave_interleave
          ![iA, iB, iC] hcap 2]
        exact hiC
      beta_reduce
      rw [if_pos ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave_valid
        ![iA, iB, iC]), h0, h1, h2]
      rfl
    · -- Uniqueness: a producing position is valid with pinned components.
      intro k hk
      have hk' : (if (fairTripleCappedAssignment sA.bits sB.bits sC.bits).Valid k then
            (gA.gen ((fairTripleCappedAssignment
              sA.bits sB.bits sC.bits).deinterleave 0 k)).bind fun a' =>
                (gB.gen ((fairTripleCappedAssignment
                  sA.bits sB.bits sC.bits).deinterleave 1 k)).bind fun b' =>
                    (gC.gen ((fairTripleCappedAssignment
                      sA.bits sB.bits sC.bits).deinterleave 2 k)).map fun c' => (a', b', c')
          else none) = some (a, b, c) := hk
      by_cases hv : (fairTripleCappedAssignment sA.bits sB.bits sC.bits).Valid k
      · rw [if_pos hv] at hk'
        rcases hga : gA.gen ((fairTripleCappedAssignment
            sA.bits sB.bits sC.bits).deinterleave 0 k) with _ | a'
        · rw [hga] at hk'
          exact absurd hk' (by simp)
        rcases hgb : gB.gen ((fairTripleCappedAssignment
            sA.bits sB.bits sC.bits).deinterleave 1 k) with _ | b'
        · rw [hga, hgb] at hk'
          exact absurd hk' (by simp)
        rcases hgc : gC.gen ((fairTripleCappedAssignment
            sA.bits sB.bits sC.bits).deinterleave 2 k) with _ | c'
        · rw [hga, hgb, hgc] at hk'
          exact absurd hk' (by simp)
        rw [hga, hgb, hgc] at hk'
        have heq : (a', b', c') = (a, b, c) := Option.some.inj hk'
        injection heq with ha' hbc'
        injection hbc' with hb' hc'
        subst ha'; subst hb'; subst hc'
        have htup : (fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleaveTuple k
            = ![iA, iB, iC] := by
          funext j
          match j with
          | ⟨0, _⟩ => exact huA _ hga
          | ⟨1, _⟩ => exact huB _ hgb
          | ⟨2, _⟩ => exact huC _ hgc
        calc k = (fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave
              ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleaveTuple k) :=
              ((fairTripleCappedAssignment
                sA.bits sB.bits sC.bits).interleave_deinterleave k hv).symm
          _ = (fairTripleCappedAssignment sA.bits sB.bits sC.bits).interleave ![iA, iB, iC] :=
              by rw [htup]
      · rw [if_neg hv] at hk'
        exact absurd hk' (by simp)

/-- **The capped fair quadruple generator (builder form).** The 4-slot analogue
of `fairPairGenCapped`. The unique index of `(a, b, c, d)` is
`interleave ![idx a, idx b, idx c, idx d]`. -/
@[reducible] def fairQuadrupleGenCapped {A B C D : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C) (gD : ExhaustiveGenerator D)
    (sA : @FairSlot A gA) (sB : @FairSlot B gB) (sC : @FairSlot C gC) (sD : @FairSlot D gD) :
    ExhaustiveGenerator (A × B × C × D) where
  gen k :=
    if (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).Valid k then
      (gA.gen ((fairQuadrupleCappedAssignment
        sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k)).bind fun a =>
          (gB.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k)).bind fun b =>
              (gC.gen ((fairQuadrupleCappedAssignment
                sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k)).bind fun c =>
                  (gD.gen ((fairQuadrupleCappedAssignment
                    sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k)).map fun d =>
                      (a, b, c, d)
    else none
  occurs_exactly_once := by
    rintro ⟨a, b, c, d⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨iB, hiB, huB⟩ := gB.occurs_exactly_once b
    obtain ⟨iC, hiC, huC⟩ := gC.occurs_exactly_once c
    obtain ⟨iD, hiD, huD⟩ := gD.occurs_exactly_once d
    have hcap : ∀ j bb,
        (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).cap j = some bb →
        (![iA, iB, iC, iD] : Fin 4 → ℕ) j < 2 ^ bb := by
      intro j bb hj
      match j with
      | ⟨0, _⟩ => exact sA.lt_two_pow_of_gen_some hiA bb hj
      | ⟨1, _⟩ => exact sB.lt_two_pow_of_gen_some hiB bb hj
      | ⟨2, _⟩ => exact sC.lt_two_pow_of_gen_some hiC bb hj
      | ⟨3, _⟩ => exact sD.lt_two_pow_of_gen_some hiD bb hj
    refine ⟨(fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).interleave
      ![iA, iB, iC, iD], ?_, ?_⟩
    · -- Existence: the witness is valid and decodes back to `(iA, iB, iC, iD)`.
      have h0 : gA.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 0 ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).interleave ![iA, iB, iC, iD])) = some a := by
        rw [(fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave_interleave ![iA, iB, iC, iD] hcap 0]
        exact hiA
      have h1 : gB.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 1 ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).interleave ![iA, iB, iC, iD])) = some b := by
        rw [(fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave_interleave ![iA, iB, iC, iD] hcap 1]
        exact hiB
      have h2 : gC.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 2 ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).interleave ![iA, iB, iC, iD])) = some c := by
        rw [(fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave_interleave ![iA, iB, iC, iD] hcap 2]
        exact hiC
      have h3 : gD.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 3 ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).interleave ![iA, iB, iC, iD])) = some d := by
        rw [(fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave_interleave ![iA, iB, iC, iD] hcap 3]
        exact hiD
      beta_reduce
      rw [if_pos ((fairQuadrupleCappedAssignment
        sA.bits sB.bits sC.bits sD.bits).interleave_valid ![iA, iB, iC, iD]), h0, h1, h2, h3]
      rfl
    · -- Uniqueness: a producing position is valid with pinned components.
      intro k hk
      have hk' : (if (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).Valid k
          then
            (gA.gen ((fairQuadrupleCappedAssignment
              sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k)).bind fun a' =>
                (gB.gen ((fairQuadrupleCappedAssignment
                  sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k)).bind fun b' =>
                    (gC.gen ((fairQuadrupleCappedAssignment
                      sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k)).bind fun c' =>
                        (gD.gen ((fairQuadrupleCappedAssignment
                          sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k)).map fun d' =>
                            (a', b', c', d')
          else none) = some (a, b, c, d) := hk
      by_cases hv : (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).Valid k
      · rw [if_pos hv] at hk'
        rcases hga : gA.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k) with _ | a'
        · rw [hga] at hk'
          exact absurd hk' (by simp)
        rcases hgb : gB.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k) with _ | b'
        · rw [hga, hgb] at hk'
          exact absurd hk' (by simp)
        rcases hgc : gC.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k) with _ | c'
        · rw [hga, hgb, hgc] at hk'
          exact absurd hk' (by simp)
        rcases hgd : gD.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k) with _ | d'
        · rw [hga, hgb, hgc, hgd] at hk'
          exact absurd hk' (by simp)
        rw [hga, hgb, hgc, hgd] at hk'
        have heq : (a', b', c', d') = (a, b, c, d) := Option.some.inj hk'
        injection heq with ha' hbcd'
        injection hbcd' with hb' hcd'
        injection hcd' with hc' hd'
        subst ha'; subst hb'; subst hc'; subst hd'
        have htup : (fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleaveTuple k = ![iA, iB, iC, iD] := by
          funext j
          match j with
          | ⟨0, _⟩ => exact huA _ hga
          | ⟨1, _⟩ => exact huB _ hgb
          | ⟨2, _⟩ => exact huC _ hgc
          | ⟨3, _⟩ => exact huD _ hgd
        calc k = (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).interleave
              ((fairQuadrupleCappedAssignment
                sA.bits sB.bits sC.bits sD.bits).deinterleaveTuple k) :=
              ((fairQuadrupleCappedAssignment
                sA.bits sB.bits sC.bits sD.bits).interleave_deinterleave k hv).symm
          _ = (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).interleave
              ![iA, iB, iC, iD] := by rw [htup]
      · rw [if_neg hv] at hk'
        exact absurd hk' (by simp)

end ExhaustiveGenerator

/-! ### Slot production bounds and the liveness bridges

`compressFast` consumes, per instance, a bridge identifying the raw builder's
producing counters with `CompressFast.Live` — mechanical per arity, from the
per-slot production shape `FairSlot.gen_isSome_iff`. -/

/-- A slot's generator produces a value exactly when the index is under the
capped card (vacuously always, for an infinite slot): the `isSome` shape of
`spec_none`/`spec_some`, matching the per-slot guard of
`CompressFast.Live`. -/
theorem FairSlot.gen_isSome_iff {T : Type*} {g : ExhaustiveGenerator T}
    (s : @FairSlot T g) (x : ℕ) :
    (g.gen x).isSome ↔ ∀ b, s.bits = some b → x < s.card := by
  constructor
  · intro hs b hb
    obtain ⟨-, -, hnone⟩ := s.spec_some b hb
    by_contra hge
    rw [hnone x (Nat.le_of_not_lt hge)] at hs
    exact absurd hs (by simp)
  · intro h
    rcases hb : s.bits with _ | b
    · exact Option.isSome_iff_ne_none.mpr (s.spec_none hb x)
    · obtain ⟨-, hsome, -⟩ := s.spec_some b hb
      exact Option.isSome_iff_ne_none.mpr (hsome x (h b hb))

namespace CompressFast

open ExhaustiveGenerator

/-- **The raw capped pair builder's liveness is `Live`**: a counter produces a
value exactly when it is valid and both slots decode in range. -/
theorem fairPairGenCapped_gen_isSome_iff {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (sA : @FairSlot A gA) (sB : @FairSlot B gB) (k : ℕ) :
    ((fairPairGenCapped gA gB sA sB).gen k).isSome
      ↔ Live ![sA.bits, sB.bits] ![sA.card, sB.card] k := by
  have hgen : (fairPairGenCapped gA gB sA sB).gen k
      = if (fairPairCappedAssignment sA.bits sB.bits).Valid k then
          (gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)).bind fun a =>
            (gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)).map fun b =>
              (a, b)
        else none := rfl
  rw [hgen]
  by_cases hv : (fairPairCappedAssignment sA.bits sB.bits).Valid k
  · rw [if_pos hv]
    constructor
    · intro hs
      refine ⟨hv, ?_⟩
      rcases hga : gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)
        with _ | a
      · rw [hga] at hs
        exact absurd hs (by simp)
      rcases hgb : gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)
        with _ | b
      · rw [hga, hgb] at hs
        exact absurd hs (by simp)
      intro j bb hj
      match j with
      | ⟨0, _⟩ =>
        exact (sA.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨a, hga⟩) bb hj
      | ⟨1, _⟩ =>
        exact (sB.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨b, hgb⟩) bb hj
    · rintro ⟨-, hlt⟩
      have ha : (gA.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 0 k)).isSome :=
        (sA.gen_isSome_iff _).mpr fun bb hb => hlt 0 bb hb
      have hb : (gB.gen ((fairPairCappedAssignment sA.bits sB.bits).deinterleave 1 k)).isSome :=
        (sB.gen_isSome_iff _).mpr fun bb hb => hlt 1 bb hb
      obtain ⟨a, hga⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨b, hgb⟩ := Option.isSome_iff_exists.mp hb
      rw [hga, hgb]
      rfl
  · rw [if_neg hv]
    exact iff_of_false (by simp) fun hlive => hv hlive.1

/-- **The raw capped triple builder's liveness is `Live`**: the 3-slot clone
of `fairPairGenCapped_gen_isSome_iff`. -/
theorem fairTripleGenCapped_gen_isSome_iff {A B C : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C) (sA : @FairSlot A gA)
    (sB : @FairSlot B gB) (sC : @FairSlot C gC) (k : ℕ) :
    ((fairTripleGenCapped gA gB gC sA sB sC).gen k).isSome
      ↔ Live ![sA.bits, sB.bits, sC.bits] ![sA.card, sB.card, sC.card] k := by
  have hgen : (fairTripleGenCapped gA gB gC sA sB sC).gen k
      = if (fairTripleCappedAssignment sA.bits sB.bits sC.bits).Valid k then
          (gA.gen ((fairTripleCappedAssignment sA.bits sB.bits sC.bits).deinterleave 0 k)).bind
            fun a =>
              (gB.gen ((fairTripleCappedAssignment
                sA.bits sB.bits sC.bits).deinterleave 1 k)).bind fun b =>
                  (gC.gen ((fairTripleCappedAssignment
                    sA.bits sB.bits sC.bits).deinterleave 2 k)).map fun c => (a, b, c)
        else none := rfl
  rw [hgen]
  by_cases hv : (fairTripleCappedAssignment sA.bits sB.bits sC.bits).Valid k
  · rw [if_pos hv]
    constructor
    · intro hs
      refine ⟨hv, ?_⟩
      rcases hga : gA.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 0 k) with _ | a
      · rw [hga] at hs
        exact absurd hs (by simp)
      rcases hgb : gB.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 1 k) with _ | b
      · rw [hga, hgb] at hs
        exact absurd hs (by simp)
      rcases hgc : gC.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 2 k) with _ | c
      · rw [hga, hgb, hgc] at hs
        exact absurd hs (by simp)
      intro j bb hj
      match j with
      | ⟨0, _⟩ =>
        exact (sA.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨a, hga⟩) bb hj
      | ⟨1, _⟩ =>
        exact (sB.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨b, hgb⟩) bb hj
      | ⟨2, _⟩ =>
        exact (sC.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨c, hgc⟩) bb hj
    · rintro ⟨-, hlt⟩
      have ha : (gA.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 0 k)).isSome :=
        (sA.gen_isSome_iff _).mpr fun bb hb => hlt 0 bb hb
      have hb : (gB.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 1 k)).isSome :=
        (sB.gen_isSome_iff _).mpr fun bb hb => hlt 1 bb hb
      have hc : (gC.gen ((fairTripleCappedAssignment
          sA.bits sB.bits sC.bits).deinterleave 2 k)).isSome :=
        (sC.gen_isSome_iff _).mpr fun bb hb => hlt 2 bb hb
      obtain ⟨a, hga⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨b, hgb⟩ := Option.isSome_iff_exists.mp hb
      obtain ⟨c, hgc⟩ := Option.isSome_iff_exists.mp hc
      rw [hga, hgb, hgc]
      rfl
  · rw [if_neg hv]
    exact iff_of_false (by simp) fun hlive => hv hlive.1

/-- **The raw capped quadruple builder's liveness is `Live`**: the 4-slot
clone of `fairPairGenCapped_gen_isSome_iff`. -/
theorem fairQuadrupleGenCapped_gen_isSome_iff {A B C D : Type*}
    (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B) (gC : ExhaustiveGenerator C)
    (gD : ExhaustiveGenerator D) (sA : @FairSlot A gA) (sB : @FairSlot B gB)
    (sC : @FairSlot C gC) (sD : @FairSlot D gD) (k : ℕ) :
    ((fairQuadrupleGenCapped gA gB gC gD sA sB sC sD).gen k).isSome
      ↔ Live ![sA.bits, sB.bits, sC.bits, sD.bits] ![sA.card, sB.card, sC.card, sD.card] k := by
  have hgen : (fairQuadrupleGenCapped gA gB gC gD sA sB sC sD).gen k
      = if (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).Valid k then
          (gA.gen ((fairQuadrupleCappedAssignment
            sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k)).bind fun a =>
              (gB.gen ((fairQuadrupleCappedAssignment
                sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k)).bind fun b =>
                  (gC.gen ((fairQuadrupleCappedAssignment
                    sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k)).bind fun c =>
                      (gD.gen ((fairQuadrupleCappedAssignment
                        sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k)).map fun d =>
                          (a, b, c, d)
        else none := rfl
  rw [hgen]
  by_cases hv : (fairQuadrupleCappedAssignment sA.bits sB.bits sC.bits sD.bits).Valid k
  · rw [if_pos hv]
    constructor
    · intro hs
      refine ⟨hv, ?_⟩
      rcases hga : gA.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k) with _ | a
      · rw [hga] at hs
        exact absurd hs (by simp)
      rcases hgb : gB.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k) with _ | b
      · rw [hga, hgb] at hs
        exact absurd hs (by simp)
      rcases hgc : gC.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k) with _ | c
      · rw [hga, hgb, hgc] at hs
        exact absurd hs (by simp)
      rcases hgd : gD.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k) with _ | d
      · rw [hga, hgb, hgc, hgd] at hs
        exact absurd hs (by simp)
      intro j bb hj
      match j with
      | ⟨0, _⟩ =>
        exact (sA.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨a, hga⟩) bb hj
      | ⟨1, _⟩ =>
        exact (sB.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨b, hgb⟩) bb hj
      | ⟨2, _⟩ =>
        exact (sC.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨c, hgc⟩) bb hj
      | ⟨3, _⟩ =>
        exact (sD.gen_isSome_iff _).mp (Option.isSome_iff_exists.mpr ⟨d, hgd⟩) bb hj
    · rintro ⟨-, hlt⟩
      have ha : (gA.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 0 k)).isSome :=
        (sA.gen_isSome_iff _).mpr fun bb hb => hlt 0 bb hb
      have hb : (gB.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 1 k)).isSome :=
        (sB.gen_isSome_iff _).mpr fun bb hb => hlt 1 bb hb
      have hc : (gC.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 2 k)).isSome :=
        (sC.gen_isSome_iff _).mpr fun bb hb => hlt 2 bb hb
      have hd : (gD.gen ((fairQuadrupleCappedAssignment
          sA.bits sB.bits sC.bits sD.bits).deinterleave 3 k)).isSome :=
        (sD.gen_isSome_iff _).mpr fun bb hb => hlt 3 bb hb
      obtain ⟨a, hga⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨b, hgb⟩ := Option.isSome_iff_exists.mp hb
      obtain ⟨c, hgc⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨d, hgd⟩ := Option.isSome_iff_exists.mp hd
      rw [hga, hgb, hgc, hgd]
      rfl
  · rw [if_neg hv]
    exact iff_of_false (by simp) fun hlive => hv hlive.1

end CompressFast

open ExhaustiveGenerator in
/-- **The capped fair `ExhaustiveGenerator (A × B)` instance**: `fairPairGenCapped`
on the components' `FairSlot` specs, COMPRESSED (holes deleted, value sequence
untouched) at the live count `mulCount sA.count sB.count` — through the FAST
path `compressFast` (gen-pointwise identical to the spec `compress` by
`compressFast_gen_eq_compress`, so nothing observable changed in the swap),
with the liveness bridge `fairPairGenCapped_gen_isSome_iff` feeding the digit
DP. Priority 900 sits
BELOW the all-infinite fair pair (default 1000) — `FairSlot` also covers
infinite components, so on an all-infinite product both apply and the uncapped
one (whose values agree, the capped assignment degenerating to `roundRobin`)
deterministically wins. Compression makes this `Contiguous` (below) and, when
both components are finite, a `FiniteGenerator` of card `cardA * cardB`. -/
instance (priority := 900) instExhaustiveGeneratorProdCapped {A B : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] : ExhaustiveGenerator (A × B) :=
  CompressFast.compressFast ![sA.bits, sB.bits] ![sA.card, sB.card]
    (fairPairGenCapped gA gB sA sB) (mulCount sA.count sB.count)
    (hasCount_h _ (sA.hasCount.prod sB.hasCount))
    (hasCount_h' _ (sA.hasCount.prod sB.hasCount))
    (CompressFast.fairPairGenCapped_gen_isSome_iff gA gB sA sB)

open ExhaustiveGenerator in
/-- Compressed capped fair pairs are contiguous (priority matching the
generator instance, as in `FairTuples`). -/
instance (priority := 900) instContiguousProdCapped {A B : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] : Contiguous (A × B) :=
  CompressFast.compressFast_contiguous ![sA.bits, sB.bits] ![sA.card, sB.card]
    (fairPairGenCapped gA gB sA sB) (mulCount sA.count sB.count)
    (hasCount_h _ (sA.hasCount.prod sB.hasCount))
    (hasCount_h' _ (sA.hasCount.prod sB.hasCount))
    (CompressFast.fairPairGenCapped_gen_isSome_iff gA gB sA sB)

open ExhaustiveGenerator in
/-- A compressed capped fair pair of FINITE components is a finite generator
with the exact product card — restoring the pair's own `FairSlot` (via
`fairSlotOfFinite`), so capped pairs can be components again (the 5-tuple
finite-tail case). -/
instance (priority := 900) instFiniteGeneratorProdCapped {A B : Type*}
    [gA : ExhaustiveGenerator A] [FiniteGenerator A] [gB : ExhaustiveGenerator B]
    [FiniteGenerator B] : FiniteGenerator (A × B) :=
  FiniteGenerator.ofCompressFast
    ![(fairSlotOfFinite (T := A)).bits, (fairSlotOfFinite (T := B)).bits]
    ![(fairSlotOfFinite (T := A)).card, (fairSlotOfFinite (T := B)).card]
    (fairPairGenCapped gA gB fairSlotOfFinite fairSlotOfFinite)
    (FiniteGenerator.card (T := A) * FiniteGenerator.card (T := B))
    (hasCount_h _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (fairSlotOfFinite (T := B)).hasCount))
    (hasCount_h' _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (fairSlotOfFinite (T := B)).hasCount))
    (CompressFast.fairPairGenCapped_gen_isSome_iff gA gB fairSlotOfFinite fairSlotOfFinite)

open ExhaustiveGenerator in
/-- **The capped fair `ExhaustiveGenerator (A × B × C)` instance**, compressed
at the live count `mulCount sA.count (mulCount sB.count sC.count)`. Priority
1050 sits below the all-infinite flat triple (1100) and above the fair pair
(1000) and capped pair (900), so a mixed bare triple resolves at the balanced
FLAT 3-way width — never as a pair with a capped-product slot. -/
instance (priority := 1050) instExhaustiveGeneratorProd3Capped {A B C : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] [gC : ExhaustiveGenerator C] [sC : FairSlot C] :
    ExhaustiveGenerator (A × B × C) :=
  CompressFast.compressFast ![sA.bits, sB.bits, sC.bits] ![sA.card, sB.card, sC.card]
    (fairTripleGenCapped gA gB gC sA sB sC)
    (mulCount sA.count (mulCount sB.count sC.count))
    (hasCount_h _ (sA.hasCount.prod (sB.hasCount.prod sC.hasCount)))
    (hasCount_h' _ (sA.hasCount.prod (sB.hasCount.prod sC.hasCount)))
    (CompressFast.fairTripleGenCapped_gen_isSome_iff gA gB gC sA sB sC)

open ExhaustiveGenerator in
/-- Compressed capped fair triples are contiguous. -/
instance (priority := 1050) instContiguousProd3Capped {A B C : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] [gC : ExhaustiveGenerator C] [sC : FairSlot C] :
    Contiguous (A × B × C) :=
  CompressFast.compressFast_contiguous ![sA.bits, sB.bits, sC.bits]
    ![sA.card, sB.card, sC.card] (fairTripleGenCapped gA gB gC sA sB sC)
    (mulCount sA.count (mulCount sB.count sC.count))
    (hasCount_h _ (sA.hasCount.prod (sB.hasCount.prod sC.hasCount)))
    (hasCount_h' _ (sA.hasCount.prod (sB.hasCount.prod sC.hasCount)))
    (CompressFast.fairTripleGenCapped_gen_isSome_iff gA gB gC sA sB sC)

open ExhaustiveGenerator in
/-- A compressed capped fair triple of FINITE components is a finite generator
with the exact product card. -/
instance (priority := 1050) instFiniteGeneratorProd3Capped {A B C : Type*}
    [gA : ExhaustiveGenerator A] [FiniteGenerator A] [gB : ExhaustiveGenerator B]
    [FiniteGenerator B] [gC : ExhaustiveGenerator C] [FiniteGenerator C] :
    FiniteGenerator (A × B × C) :=
  FiniteGenerator.ofCompressFast
    ![(fairSlotOfFinite (T := A)).bits, (fairSlotOfFinite (T := B)).bits,
      (fairSlotOfFinite (T := C)).bits]
    ![(fairSlotOfFinite (T := A)).card, (fairSlotOfFinite (T := B)).card,
      (fairSlotOfFinite (T := C)).card]
    (fairTripleGenCapped gA gB gC fairSlotOfFinite fairSlotOfFinite fairSlotOfFinite)
    (FiniteGenerator.card (T := A) * (FiniteGenerator.card (T := B)
      * FiniteGenerator.card (T := C)))
    (hasCount_h _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (((fairSlotOfFinite (T := B)).hasCount).prod (fairSlotOfFinite (T := C)).hasCount)))
    (hasCount_h' _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (((fairSlotOfFinite (T := B)).hasCount).prod (fairSlotOfFinite (T := C)).hasCount)))
    (CompressFast.fairTripleGenCapped_gen_isSome_iff gA gB gC fairSlotOfFinite
      fairSlotOfFinite fairSlotOfFinite)

open ExhaustiveGenerator in
/-- **The capped fair `ExhaustiveGenerator (A × B × C × D)` instance**,
compressed at the product live count. Priority 1150 sits below the
all-infinite flat quadruple (1200) and above the triple variants (1100/1050),
so a mixed bare quadruple resolves at the balanced FLAT 4-way width. A
5-tuple resolves through here as the flat quadruple over `A, B, C, (D × E)` —
and compression gives the tail pair its `FairSlot` in EVERY case (finite tail
pairs included; the 4b gap is closed). -/
instance (priority := 1150) instExhaustiveGeneratorProd4Capped {A B C D : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] [gC : ExhaustiveGenerator C] [sC : FairSlot C]
    [gD : ExhaustiveGenerator D] [sD : FairSlot D] :
    ExhaustiveGenerator (A × B × C × D) :=
  CompressFast.compressFast ![sA.bits, sB.bits, sC.bits, sD.bits]
    ![sA.card, sB.card, sC.card, sD.card]
    (fairQuadrupleGenCapped gA gB gC gD sA sB sC sD)
    (mulCount sA.count (mulCount sB.count (mulCount sC.count sD.count)))
    (hasCount_h _ (sA.hasCount.prod (sB.hasCount.prod (sC.hasCount.prod sD.hasCount))))
    (hasCount_h' _ (sA.hasCount.prod (sB.hasCount.prod (sC.hasCount.prod sD.hasCount))))
    (CompressFast.fairQuadrupleGenCapped_gen_isSome_iff gA gB gC gD sA sB sC sD)

open ExhaustiveGenerator in
/-- Compressed capped fair quadruples are contiguous. -/
instance (priority := 1150) instContiguousProd4Capped {A B C D : Type*}
    [gA : ExhaustiveGenerator A] [sA : FairSlot A] [gB : ExhaustiveGenerator B]
    [sB : FairSlot B] [gC : ExhaustiveGenerator C] [sC : FairSlot C]
    [gD : ExhaustiveGenerator D] [sD : FairSlot D] :
    Contiguous (A × B × C × D) :=
  CompressFast.compressFast_contiguous ![sA.bits, sB.bits, sC.bits, sD.bits]
    ![sA.card, sB.card, sC.card, sD.card]
    (fairQuadrupleGenCapped gA gB gC gD sA sB sC sD)
    (mulCount sA.count (mulCount sB.count (mulCount sC.count sD.count)))
    (hasCount_h _ (sA.hasCount.prod (sB.hasCount.prod (sC.hasCount.prod sD.hasCount))))
    (hasCount_h' _ (sA.hasCount.prod (sB.hasCount.prod (sC.hasCount.prod sD.hasCount))))
    (CompressFast.fairQuadrupleGenCapped_gen_isSome_iff gA gB gC gD sA sB sC sD)

open ExhaustiveGenerator in
/-- A compressed capped fair quadruple of FINITE components is a finite
generator with the exact product card. -/
instance (priority := 1150) instFiniteGeneratorProd4Capped {A B C D : Type*}
    [gA : ExhaustiveGenerator A] [FiniteGenerator A] [gB : ExhaustiveGenerator B]
    [FiniteGenerator B] [gC : ExhaustiveGenerator C] [FiniteGenerator C]
    [gD : ExhaustiveGenerator D] [FiniteGenerator D] :
    FiniteGenerator (A × B × C × D) :=
  FiniteGenerator.ofCompressFast
    ![(fairSlotOfFinite (T := A)).bits, (fairSlotOfFinite (T := B)).bits,
      (fairSlotOfFinite (T := C)).bits, (fairSlotOfFinite (T := D)).bits]
    ![(fairSlotOfFinite (T := A)).card, (fairSlotOfFinite (T := B)).card,
      (fairSlotOfFinite (T := C)).card, (fairSlotOfFinite (T := D)).card]
    (fairQuadrupleGenCapped gA gB gC gD fairSlotOfFinite fairSlotOfFinite fairSlotOfFinite
      fairSlotOfFinite)
    (FiniteGenerator.card (T := A) * (FiniteGenerator.card (T := B)
      * (FiniteGenerator.card (T := C) * FiniteGenerator.card (T := D))))
    (hasCount_h _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (((fairSlotOfFinite (T := B)).hasCount).prod
        (((fairSlotOfFinite (T := C)).hasCount).prod (fairSlotOfFinite (T := D)).hasCount))))
    (hasCount_h' _ ((fairSlotOfFinite (T := A)).hasCount.prod
      (((fairSlotOfFinite (T := B)).hasCount).prod
        (((fairSlotOfFinite (T := C)).hasCount).prod (fairSlotOfFinite (T := D)).hasCount))))
    (CompressFast.fairQuadrupleGenCapped_gen_isSome_iff gA gB gC gD fairSlotOfFinite
      fairSlotOfFinite fairSlotOfFinite fairSlotOfFinite)

/-! ### Capped fair vecs -/

namespace ExhaustiveGenerator

/-- **The capped fair fixed-length vec generator (builder form, positive
length).** All `m + 1` coordinates share the single component slot spec `s`;
position `k`'s bits are deinterleaved by `fairVecCappedAssignment m s.bits`
into the coordinate indices. The `gen` guard checks counter validity AND that
every coordinate's decoded index produces a value (`isSome` — the interior-hole
check for non-power-of-two cards); on success the vec is assembled by
`Option.get` on those witnesses. The unique index of `v` is
`interleave (fun j => idx (v.get j))`, exactly as in the uncapped `fairVecGen`
but through the guarded round-trips. -/
@[reducible] def fairVecGenCapped {T : Type*} (g : ExhaustiveGenerator T)
    (s : @FairSlot T g) (m : ℕ) : ExhaustiveGenerator (List.Vector T (m + 1)) where
  gen k :=
    if h : (fairVecCappedAssignment m s.bits).Valid k ∧
        ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).isSome then
      some (List.Vector.ofFn fun j =>
        (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).get (h.2 j))
    else none
  occurs_exactly_once v := by
    -- One unique component index per coordinate.
    choose idxf hidx huniq using fun j : Fin (m + 1) => g.occurs_exactly_once (v.get j)
    have hcap : ∀ j bb, (fairVecCappedAssignment m s.bits).cap j = some bb →
        idxf j < 2 ^ bb :=
      fun j bb hj => s.lt_two_pow_of_gen_some (hidx j) bb hj
    have hd : ∀ j, (fairVecCappedAssignment m s.bits).deinterleave j
        ((fairVecCappedAssignment m s.bits).interleave idxf) = idxf j :=
      (fairVecCappedAssignment m s.bits).deinterleave_interleave idxf hcap
    refine ⟨(fairVecCappedAssignment m s.bits).interleave idxf, ?_, ?_⟩
    · -- Existence: the witness is valid, every coordinate decodes to `idxf j`,
      -- and the assembled vec is `v` coordinatewise.
      have hcond : (fairVecCappedAssignment m s.bits).Valid
          ((fairVecCappedAssignment m s.bits).interleave idxf) ∧
          ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j
            ((fairVecCappedAssignment m s.bits).interleave idxf))).isSome := by
        refine ⟨(fairVecCappedAssignment m s.bits).interleave_valid idxf, fun j => ?_⟩
        rw [hd j, hidx j]
        rfl
      beta_reduce
      rw [dif_pos hcond, Option.some.injEq]
      apply List.Vector.ext
      intro j
      rw [List.Vector.get_ofFn]
      apply Option.some.inj
      rw [Option.some_get, hd j]
      exact hidx j
    · -- Uniqueness: a producing position is valid with every coordinate pinned.
      intro k hk
      have hk' : (if h : (fairVecCappedAssignment m s.bits).Valid k ∧
            ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).isSome then
          some (List.Vector.ofFn fun j =>
            (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).get (h.2 j))
        else none) = some v := hk
      by_cases hc : (fairVecCappedAssignment m s.bits).Valid k ∧
          ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).isSome
      · rw [dif_pos hc] at hk'
        have hg : ∀ j, g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)
            = some (v.get j) := by
          intro j
          have hj := congrArg (fun w => List.Vector.get w j) (Option.some.inj hk')
          simp only [List.Vector.get_ofFn] at hj
          rw [← hj, Option.some_get]
        have htup : (fairVecCappedAssignment m s.bits).deinterleaveTuple k = idxf :=
          funext fun j => huniq j _ (hg j)
        calc k = (fairVecCappedAssignment m s.bits).interleave
              ((fairVecCappedAssignment m s.bits).deinterleaveTuple k) :=
              ((fairVecCappedAssignment m s.bits).interleave_deinterleave k hc.1).symm
          _ = (fairVecCappedAssignment m s.bits).interleave idxf := by rw [htup]
      · rw [dif_neg hc] at hk'
        exact absurd hk' (by simp)

end ExhaustiveGenerator

namespace CompressFast

open ExhaustiveGenerator

/-- **The raw capped vec builder's liveness is `Live`** (positive length,
every slot sharing the component's cap and card): the vec clone of
`fairPairGenCapped_gen_isSome_iff` — simpler, because the builder's own guard
already carries the per-coordinate `isSome` conjunct. -/
theorem fairVecGenCapped_gen_isSome_iff {T : Type*} (g : ExhaustiveGenerator T)
    (s : @FairSlot T g) (m k : ℕ) :
    ((fairVecGenCapped g s m).gen k).isSome
      ↔ Live (fun _ : Fin (m + 1) => s.bits) (fun _ => s.card) k := by
  have hgen : (fairVecGenCapped g s m).gen k
      = if h : (fairVecCappedAssignment m s.bits).Valid k ∧
          ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).isSome then
        some (List.Vector.ofFn fun j =>
          (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).get (h.2 j))
      else none := rfl
  rw [hgen]
  by_cases hc : (fairVecCappedAssignment m s.bits).Valid k ∧
      ∀ j, (g.gen ((fairVecCappedAssignment m s.bits).deinterleave j k)).isSome
  · rw [dif_pos hc]
    exact iff_of_true rfl ⟨hc.1, fun j b hj => (s.gen_isSome_iff _).mp (hc.2 j) b hj⟩
  · rw [dif_neg hc]
    refine iff_of_false (by simp) fun hlive => hc ⟨hlive.1, fun j => ?_⟩
    exact (s.gen_isSome_iff _).mpr fun b hb => hlive.2 j b hb

end CompressFast

open ExhaustiveGenerator in
/-- **The capped fair `ExhaustiveGenerator (List.Vector T n)` instance** for a
FINITE component: by cases on `n`, the singleton empty-vec generator at length
`0` (shared with the all-infinite instance's zero case) and, at positive
length, the flat `(n)`-way `fairVecGenCapped` on the finite slot spec,
COMPRESSED at the live count `card ^ n`. Priority 900 sits below the
all-infinite vec instance (default 1000); they never actually overlap (no
component is both `Infinite` and finitely generated). Compression makes every
length `Contiguous` and a `FiniteGenerator` (below). -/
instance (priority := 900) instExhaustiveGeneratorVectorCapped {T : Type*}
    [inst : ExhaustiveGenerator T] [FiniteGenerator T] :
    {n : ℕ} → ExhaustiveGenerator (List.Vector T n)
  | 0 => fairVecGenZero T
  | m + 1 => CompressFast.compressFast (fun _ => (fairSlotOfFinite (T := T)).bits)
      (fun _ => (fairSlotOfFinite (T := T)).card)
      (fairVecGenCapped inst fairSlotOfFinite m)
      (some (FiniteGenerator.card (T := T) ^ (m + 1)))
      (hasCount_h _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (hasCount_h' _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (CompressFast.fairVecGenCapped_gen_isSome_iff inst fairSlotOfFinite m)

open ExhaustiveGenerator in
/-- The length-0 capped vec generator is list-backed, hence contiguous (it
was the hole-free exception among capped composites even before
compression). -/
instance instContiguousVectorZeroCapped {T : Type*} [ExhaustiveGenerator T]
    [FiniteGenerator T] : Contiguous (List.Vector T 0) :=
  contiguous_of_getElem? (instExhaustiveGeneratorVectorCapped (n := 0)) rfl

open ExhaustiveGenerator in
/-- The length-0 capped vec generator is finite with `card = 1` (the empty
vec) — giving finite component types a canonical card-1 composite slot. -/
instance instFiniteGeneratorVectorZeroCapped {T : Type*} [ExhaustiveGenerator T]
    [FiniteGenerator T] : FiniteGenerator (List.Vector T 0) :=
  FiniteGenerator.ofListNodup (instExhaustiveGeneratorVectorCapped (n := 0)) 1 rfl rfl

open ExhaustiveGenerator in
/-- Compressed capped fair vecs are contiguous at every length. -/
instance (priority := 900) instContiguousVectorCapped {T : Type*}
    [inst : ExhaustiveGenerator T] [FiniteGenerator T] :
    {n : ℕ} → Contiguous (List.Vector T n)
  | 0 => instContiguousVectorZeroCapped
  | m + 1 => CompressFast.compressFast_contiguous
      (fun _ => (fairSlotOfFinite (T := T)).bits) (fun _ => (fairSlotOfFinite (T := T)).card)
      (fairVecGenCapped inst fairSlotOfFinite m)
      (some (FiniteGenerator.card (T := T) ^ (m + 1)))
      (hasCount_h _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (hasCount_h' _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (CompressFast.fairVecGenCapped_gen_isSome_iff inst fairSlotOfFinite m)

open ExhaustiveGenerator in
/-- A compressed capped fair vec is a finite generator with the exact card
`card ^ n` (the length-0 case is the existing card-1 instance). -/
instance (priority := 900) instFiniteGeneratorVectorCapped {T : Type*}
    [inst : ExhaustiveGenerator T] [FiniteGenerator T] :
    {n : ℕ} → FiniteGenerator (List.Vector T n)
  | 0 => instFiniteGeneratorVectorZeroCapped
  | m + 1 => FiniteGenerator.ofCompressFast
      (fun _ => (fairSlotOfFinite (T := T)).bits) (fun _ => (fairSlotOfFinite (T := T)).card)
      (fairVecGenCapped inst fairSlotOfFinite m)
      (FiniteGenerator.card (T := T) ^ (m + 1))
      (hasCount_h _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (hasCount_h' _ ((fairSlotOfFinite (T := T)).hasCount.vector (m + 1)))
      (CompressFast.fairVecGenCapped_gen_isSome_iff inst fairSlotOfFinite m)

/-! ### Instance-resolution pins

Value guards cannot distinguish the capped instance from the uncapped one on
all-infinite products (with no caps the assignments agree), so the resolution
itself is pinned by `rfl`: all-infinite products keep resolving through the
uncapped path, mixed products resolve capped at MAXIMAL FLAT width (a mixed
triple/quadruple is never a pair-of-something), and 5-tuples resolve as the
capped flat quadruple over the tail pair — now for EVERY tail: an infinite or
mixed tail pair slots in through `Contiguous` + `Infinite`
(`fairSlotOfInfinite`), an all-finite one through its restored
`FiniteGenerator` (`fairSlotOfFinite`). The last two pins are chunk 4b's
documented finite-tail GAP, now closed by compression. -/

example : (inferInstance : ExhaustiveGenerator (AzNat × AzNat))
    = instExhaustiveGeneratorProd := rfl
example : (inferInstance : ExhaustiveGenerator (AzNat × AzNat × AzNat))
    = instExhaustiveGeneratorProd3 := rfl
example : (inferInstance : ExhaustiveGenerator (UInt64 × UInt64))
    = instExhaustiveGeneratorProdCapped := rfl
example : (inferInstance : ExhaustiveGenerator (AzNat × UInt8))
    = instExhaustiveGeneratorProdCapped := rfl
example : (inferInstance : ExhaustiveGenerator (AzNat × UInt8 × AzNat))
    = instExhaustiveGeneratorProd3Capped := rfl
example : (inferInstance : ExhaustiveGenerator (AzNat × AzNat × UInt8 × AzNat))
    = instExhaustiveGeneratorProd4Capped := rfl
example : (inferInstance : ExhaustiveGenerator (UInt8 × AzNat × AzNat × AzNat × AzNat))
    = instExhaustiveGeneratorProd4Capped := rfl
-- The CLOSED 4b gap: a finite component among the last two positions. The
-- MIXED tail pair `AzNat × UInt8` is a compressed capped pair, contiguous
-- and INFINITE — so it slots into the UNCAPPED flat quadruple (1200) as an
-- ordinary infinite component; the all-finite tail pair `UInt8 × Ordering`
-- carries restored `FiniteGenerator` data (card `768`), a capped slot of the
-- capped flat quadruple.
example : (inferInstance : ExhaustiveGenerator (AzNat × AzNat × AzNat × AzNat × UInt8))
    = instExhaustiveGeneratorProd4 := rfl
example : (inferInstance : ExhaustiveGenerator (AzNat × AzNat × AzNat × UInt8 × Ordering))
    = instExhaustiveGeneratorProd4Capped := rfl

/-! ### Guards

Value-sequence fidelity: compression deletes gaps and touches nothing else,
so every VALUE table of the 4b raw layer must replay VERBATIM — with the
positions now DENSE (no `none`-skips inside the enumeration). Hole-free
cases (power-of-two cards) are gen-pointwise unchanged. The DEEP spot checks
(counters `2^16`–`2^25`) stated against the RAW builders remain the semantic
source of truth those positions pin; with the instances on `compressFast`'s
digit DP, deep accesses now ALSO go through the INSTANCES directly (the
`2^16` pin right below, and the `10^6`-index guards at the bottom). -/

open ExhaustiveGenerator

-- THE motivating case: fair pairs over a FINITE type. `exhaustive_pairs` of
-- two `u64` iterators is the Z-order pairs table — instant, with the
-- lex-unreachable `(1, 0)` at index 2 (a lex pair enumeration over `UInt64`
-- would emit `2^64` `(0, _)` pairs first). Power-of-two cards: hole-free, so
-- compression leaves the table IDENTICAL to 4b's.
#guard (firstN (UInt64 × UInt64) 10).map (fun p => (p.1.toNat, p.2.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1)]

-- Mixed infinite × finite: `cap = ![none, some 8]` assigns positions
-- `0, 2, …, 14` to the `UInt8` slot and all others to `AzNat`, which matches
-- the uncapped alternation on positions `< 16` — so the prefix replays the
-- all-infinite Z-order table (hole-free: unchanged from 4b).
#guard (firstN (AzNat × UInt8) 10).map (fun p => (p.1.toNat, p.2.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1)]

-- DEEP mixed check, past the cap (RAW layer): counter bit 16 is where the
-- UNCAPPED assignment would hand the `UInt8` component its (nonexistent) bit
-- 8; the drop-out rotation hands position 16 to `AzNat` as its rank-8 bit
-- instead, so `k = 2^16` decodes to `(2^8, 0)` — the first component absorbs
-- all remaining bits. (`AzNat × UInt8` is hole-free, so the compressed
-- instance agrees here — and the digit-DP instance reaches `2^16` directly,
-- pinned right after.)
#guard ((List.range 4).map fun i =>
    ((fairPairGenCapped naturalsGen uint8Gen inferInstance inferInstance).gen
      (65536 + i)).map (fun p => (p.1.toNat, p.2.toNat)))
  = [some (256, 0), some (256, 1), some (257, 0), some (257, 1)]
#guard (gen (T := AzNat × UInt8) 65536).map (fun p => (p.1.toNat, p.2.toNat))
  = some (256, 0)

-- Non-power-of-two: `Ordering` (card 3) is a 2-bit slot with one hole
-- pattern (`3`). `cap = ![some 2, none]`: the `Ordering` index reads counter
-- bits `{1, 3}`, `AzNat` reads `{0, 2, 4, 5, …}`. RAW hand table (`d0` =
-- Ordering index, holes where `d0 = 3 ≥ card`):
--   k : 0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15
--   d0: 0  0  1  1  0  0  1  1  2  2  3  3  2  2  3  3
--   d1: 0  1  0  1  2  3  2  3  0  1  -  -  2  3  -  -
-- The raw holes at `k = 10, 11` are pinned on the builder…
#guard ((fairPairGenCapped orderingsIncreasingGen naturalsGen
  inferInstance inferInstance).gen 10).isNone
-- …and the INSTANCE is the compressed table: DENSE positions, `firstN 12`
-- now yields 12 values (raw `k = 0, …, 9, 12, 13`), with the former raw
-- position-12/13 values `(gt, 2)`/`(gt, 3)` at compressed positions 10/11.
#guard (firstN (Ordering × AzNat) 12).map (fun p => (p.1, p.2.toNat))
  = [(.lt, 0), (.lt, 1), (.eq, 0), (.eq, 1), (.lt, 2), (.lt, 3), (.eq, 2), (.eq, 3),
     (.gt, 0), (.gt, 1), (.gt, 2), (.gt, 3)]
#guard (gen (T := Ordering × AzNat) 10).map (fun p => (p.1, p.2.toNat)) = some (.gt, 2)
#guard (gen (T := Ordering × AzNat) 13).map (fun p => (p.1, p.2.toNat)) = some (.lt, 5)

-- All-capped non-power-of-two: `Ordering × Ordering` has 9 values, raw on 4
-- counter bits (`Valid k ↔ k < 16`, values at `k = 0, 1, 2, 3, 4, 6, 8, 9,
-- 12`, holes elsewhere — pinned on the builder), compressed CONTIGUOUSLY
-- onto positions `0, …, 8` with the `FiniteGenerator` card exactly 9.
#guard ((fairPairGenCapped orderingsIncreasingGen orderingsIncreasingGen
  inferInstance inferInstance).gen 5).isNone   -- raw hole: snd index = 3
#guard firstN (Ordering × Ordering) 20
  = [(.lt, .lt), (.lt, .eq), (.eq, .lt), (.eq, .eq), (.lt, .gt), (.eq, .gt),
     (.gt, .lt), (.gt, .eq), (.gt, .gt)]
#guard (firstN (Ordering × Ordering) 20).length == 9
#guard (gen (T := Ordering × Ordering) 5) = some (.eq, .gt)  -- was a raw hole
#guard (gen (T := Ordering × Ordering) 8).isSome
#guard (gen (T := Ordering × Ordering) 9).isNone   -- contiguous cutoff at card 9
#guard (gen (T := Ordering × Ordering) 16).isNone
#guard FiniteGenerator.card (T := Ordering × Ordering) == 9

-- Power-of-two card is HOLE-FREE: `Bool` (card 2 = 2^1) fills its 1-bit slot
-- exactly. `cap = ![some 1, none]`: `Bool` owns position 1, `AzNat` the rest.
-- Compression is the identity here — both guards identical to 4b's.
#guard (firstN (Bool × AzNat) 10).map (fun p => (p.1, p.2.toNat))
  = [(false, 0), (false, 1), (true, 0), (true, 1), (false, 2), (false, 3), (true, 2),
     (true, 3), (false, 4), (false, 5)]
#guard (List.range 64).all fun k => (gen (T := Bool × AzNat) k).isSome

-- Card-1 component (`List.Vector AzNat 0`, via the length-0 capped
-- `FiniteGenerator`): a degenerate 0-bit slot (`(1 - 1).size = 0`) that owns
-- NO counter positions — the pair enumerates its partner unchanged, hole-free.
#guard (firstN (List.Vector AzNat 0 × AzNat) 5).map (fun p => (p.1.toList.length, p.2.toNat))
  = [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]
#guard (List.range 32).all fun k => (gen (T := List.Vector AzNat 0 × AzNat) k).isSome

-- Mixed FLAT triple (the priority check made visible: positions `0, …, 23`
-- rotate all three slots, so the prefix replays the all-infinite 20-term flat
-- triple table — a pair-of-pair nesting would swap indices 2/4 and 8/16).
#guard (firstN (AzNat × UInt8 × AzNat) 20).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat))
  = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
     (0, 0, 2), (0, 0, 3), (0, 1, 2), (0, 1, 3), (1, 0, 2), (1, 0, 3), (1, 1, 2), (1, 1, 3),
     (0, 2, 0), (0, 2, 1), (0, 3, 0), (0, 3, 1)]

-- DEEP triple check (RAW layer): the `UInt8` slot's 8 bits exhaust at counter
-- position 22; from position 24 on, rounds emit only slots 2 and 0 — so bit
-- 24 is the THIRD component's rank-8 bit and bit 25 the FIRST's.
#guard ((fairTripleGenCapped naturalsGen uint8Gen naturalsGen
    inferInstance inferInstance inferInstance).gen (2 ^ 24)).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (0, 0, 256)
#guard ((fairTripleGenCapped naturalsGen uint8Gen naturalsGen
    inferInstance inferInstance inferInstance).gen (2 ^ 25)).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)) = some (256, 0, 0)

-- Mixed FLAT quadruple: binary counting with one bit per component.
#guard (firstN (AzNat × AzNat × UInt8 × AzNat) 16).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.1.toNat, t.2.2.2.toNat))
  = [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1),
     (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 1, 0), (0, 1, 1, 1),
     (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 0), (1, 0, 1, 1),
     (1, 1, 0, 0), (1, 1, 0, 1), (1, 1, 1, 0), (1, 1, 1, 1)]

-- The CLOSED 5-tuple gap, valued: the finite tail pair `UInt8 × Ordering` is
-- slot 3 of the flat quadruple (a capped 10-bit slot, card 768). Position 0
-- is the tail pair's counter bit 0 (its `Ordering` coordinate), position 1
-- the third `AzNat`'s bit 0.
#guard (firstN (AzNat × AzNat × AzNat × UInt8 × Ordering) 4).map
    (fun t => (t.1.toNat, t.2.1.toNat, t.2.2.1.toNat, t.2.2.2.1.toNat, t.2.2.2.2))
  = [(0, 0, 0, 0, .lt), (0, 0, 0, 0, .eq), (0, 0, 1, 0, .lt), (0, 0, 1, 0, .eq)]

-- Capped vecs. Power-of-two component: hole-free, replays the Z-order pairs
-- table (identical to 4b's).
#guard (firstN (List.Vector UInt8 2) 10).map (fun v => v.toList.map (·.toNat))
  = [[0, 0], [0, 1], [1, 0], [1, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1]]

-- Non-power-of-two component: `List.Vector Ordering 2` is the `Ordering ×
-- Ordering` table as lists — 9 values, now contiguous, card exactly 9. The
-- raw hole at counter 5 (coordinate 1 index = 3) stays pinned on the builder;
-- the compressed position 5 holds the sixth value.
#guard ((fairVecGenCapped orderingsIncreasingGen inferInstance 1).gen 5).isNone
#guard (firstN (List.Vector Ordering 2) 20).map (·.toList)
  = [[.lt, .lt], [.lt, .eq], [.eq, .lt], [.eq, .eq], [.lt, .gt], [.eq, .gt],
     [.gt, .lt], [.gt, .eq], [.gt, .gt]]
#guard (firstN (List.Vector Ordering 2) 20).length == 9
#guard (gen (T := List.Vector Ordering 2) 5).map (·.toList) = some [.eq, .gt]
#guard (gen (T := List.Vector Ordering 2) 8).isSome
#guard (gen (T := List.Vector Ordering 2) 9).isNone  -- contiguous cutoff at card 9
#guard FiniteGenerator.card (T := List.Vector Ordering 2) == 9

-- Length 1 (a single 2-bit slot — raw hole at counter 3 compressed away, so
-- the cutoff is now at the card, 3) and length 0 (the singleton empty vec
-- through the capped zero case).
#guard (firstN (List.Vector Ordering 1) 10).map (·.toList) = [[.lt], [.eq], [.gt]]
#guard (gen (T := List.Vector Ordering 1) 3).isNone
#guard FiniteGenerator.card (T := List.Vector Ordering 1) == 3
#guard (firstN (List.Vector UInt8 0) 5).length == 1

/-! ### The digit-DP scale layer

Packaged pair rank/unrank (fast vs. spec), the generator-level `countBelow`
cross-checks, and the SCALE guards — all stated against the raw builders and
bridges above (this is `CompressFast.lean`'s machinery instantiated at the
slot specs, kept here with the builders it consumes). -/

namespace CompressFast

open ExhaustiveGenerator

/-- The fast unrank of a capped fair PAIR, with all hypotheses derived from
the slot specs: the raw counter of the `i`-th live position of
`fairPairGenCapped gA gB sA sB`. -/
def fastUnrankPair {A B : Type*} (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (sA : @FairSlot A gA) (sB : @FairSlot B gB) (i : ℕ) : ℕ :=
  fastUnrank ![sA.bits, sB.bits] ![sA.card, sB.card] (fairPairGenCapped gA gB sA sB)
    (mulCount sA.count sB.count)
    (hasCount_h _ (sA.hasCount.prod sB.hasCount))
    (fairPairGenCapped_gen_isSome_iff gA gB sA sB) i

/-- The SPEC unrank of a capped fair pair — the linear scan, for
cross-checking. -/
def specUnrankPair {A B : Type*} (gA : ExhaustiveGenerator A) (gB : ExhaustiveGenerator B)
    (sA : @FairSlot A gA) (sB : @FairSlot B gB) (i : ℕ) : ℕ :=
  unrank (fairPairGenCapped gA gB sA sB) (mulCount sA.count sB.count)
    (hasCount_h _ (sA.hasCount.prod sB.hasCount)) i

/-- The packaged pair unranks agree (unconditionally). -/
theorem fastUnrankPair_eq_specUnrankPair {A B : Type*} (gA : ExhaustiveGenerator A)
    (gB : ExhaustiveGenerator B) (sA : @FairSlot A gA) (sB : @FairSlot B gB) (i : ℕ) :
    fastUnrankPair gA gB sA sB i = specUnrankPair gA gB sA sB i :=
  fastUnrank_eq_unrank (fairPairGenCapped_gen_isSome_iff gA gB sA sB) i

/-! ### Guards

Small cross-checks against the spec `unrank` and `rankSpec`, then the SCALE
demonstration: a `10^12 + 39`-card component (a 40-bit capped slot) paired
with `Ordering`, fast-unranked at compressed index `10^9` — where the spec
path would scan `1 333 333 333` raw counters, `fastUnrank` answers
instantly, with the expected raw counter verifiable by hand: the `Ordering`
slot reads counter bits `{0, 2}`, so exactly the counters `k ≡ 5, 7 (mod 8)`
are holes (`6` live per `8`-block) at this depth, and
`10^9 = 6 · 166666666 + 4` places the answer at `8 · 166666666 + 4`.
Finally, the DEEP INSTANCE accesses the swap to `compressFast` makes
feasible: compressed positions `~10^6` read through the PUBLIC instances,
where the spec path would scan `~1.3 × 10^6` raw counters per access. -/

-- `countBelow` = `rankSpec` on the raw pair builders (the generator bridge,
-- valued).
#guard (List.range 40).all fun n =>
  countBelow ![some 2, some 2] ![3, 3] n
    == ExhaustiveGenerator.rankSpec
      (fairPairGenCapped orderingsIncreasingGen orderingsIncreasingGen
        inferInstance inferInstance) n
#guard (List.range 40).all fun n =>
  countBelow ![some 2, none] ![3, 0] n
    == ExhaustiveGenerator.rankSpec
      (fairPairGenCapped orderingsIncreasingGen naturalsGen
        inferInstance inferInstance) n

-- `fastUnrank` = spec `unrank`, including past the live count (both junk `0`
-- from index 9 on for the all-finite pair).
#guard (List.range 16).all fun i =>
  fastUnrankPair orderingsIncreasingGen orderingsIncreasingGen inferInstance inferInstance i
    == specUnrankPair orderingsIncreasingGen orderingsIncreasingGen
      inferInstance inferInstance i
#guard (List.range 40).all fun i =>
  fastUnrankPair orderingsIncreasingGen naturalsGen inferInstance inferInstance i
    == specUnrankPair orderingsIncreasingGen naturalsGen inferInstance inferInstance i

/-- The scale-demo component: a `Fin`-backed finite generator with the LARGE
non-power-of-two card `10^12 + 39` (a 40-bit capped slot — the
polynomial-coefficient scale the spec scan cannot reach). -/
@[reducible] def bigDemoGen : ExhaustiveGenerator (Fin (10 ^ 12 + 39)) :=
  ofBoundedBijOn (10 ^ 12 + 39) (fun n h => ⟨n, h⟩)
    (fun _ _ _ _ hij => congrArg Fin.val hij)
    (fun t => ⟨t.val, t.isLt, rfl⟩)

/-- `FiniteGenerator` data for the scale-demo component. -/
@[reducible] def bigDemoFinite : @FiniteGenerator _ bigDemoGen :=
  FiniteGenerator.ofBoundedBijOn bigDemoGen (10 ^ 12 + 39) rfl

/-- The scale-demo slot: `10^12 + 39` values on 40 counter bits. -/
@[reducible] def bigDemoSlot : @FairSlot _ bigDemoGen :=
  @fairSlotOfFinite _ bigDemoGen bigDemoFinite

-- The demo slot caps at exactly 40 bits.
#guard bigDemoSlot.bits == some 40

-- The TOTAL live count of the `big × Ordering` product, read off instantly
-- at the full `2^42` validity budget: exactly `3 · (10^12 + 39)` — the digit
-- DP's clamp formula hitting the full cards.
#guard countBelow ![some 40, some 2] ![10 ^ 12 + 39, 3] (2 ^ 42) == 3 * (10 ^ 12 + 39)

-- THE SCALE DEMONSTRATION: fast-unrank the `big × Ordering` product at
-- compressed index `10^9`. The spec `unrank` would scan ~`1.33 × 10^9` raw
-- counters; `fastUnrank` binary-searches `countBelow` and answers instantly.
#guard fastUnrankPair bigDemoGen orderingsIncreasingGen bigDemoSlot inferInstance (10 ^ 9)
  == 1333333332

-- Round-trip: the found counter ranks back to exactly `10^9`…
#guard countBelow ![some 40, some 2] ![10 ^ 12 + 39, 3] 1333333332 == 10 ^ 9

-- …is live for the liveness predicate…
#guard decide (Live ![some 40, some 2] ![10 ^ 12 + 39, 3] 1333333332)

-- …and the raw pair builder produces a value there — with the expected
-- `Ordering` coordinate: counter bits `{0, 2}` of `1333333332 ≡ 4 (mod 8)`
-- decode the `Ordering` index `2 = .gt`.
#guard ((fairPairGenCapped bigDemoGen orderingsIncreasingGen bigDemoSlot inferInstance).gen
  1333333332).map Prod.snd == some Ordering.gt

/-- The scale demo COMPRESSED: `compressFast` on the `big × Ordering` raw
builder — exactly the shape of the public capped pair instance, at a card the
spec scan cannot reach. -/
@[reducible] def bigDemoCompressedGen :
    ExhaustiveGenerator (Fin (10 ^ 12 + 39) × Ordering) :=
  compressFast ![bigDemoSlot.bits, (fairSlotOfFinite (T := Ordering)).bits]
    ![bigDemoSlot.card, (fairSlotOfFinite (T := Ordering)).card]
    (fairPairGenCapped bigDemoGen orderingsIncreasingGen bigDemoSlot fairSlotOfFinite)
    (mulCount bigDemoSlot.count (fairSlotOfFinite (T := Ordering)).count)
    (hasCount_h _ (bigDemoSlot.hasCount.prod (fairSlotOfFinite (T := Ordering)).hasCount))
    (hasCount_h' _ (bigDemoSlot.hasCount.prod (fairSlotOfFinite (T := Ordering)).hasCount))
    (fairPairGenCapped_gen_isSome_iff bigDemoGen orderingsIncreasingGen bigDemoSlot
      fairSlotOfFinite)

-- The big non-power-of-two demo, END TO END: a single deep `firstN`-free
-- access through the compressed generator at index `10^9` — the value at the
-- raw counter found above (`Fin` index `bit 1 + (k >> 4) · 4 = 333333332`,
-- `Ordering` index `2 = .gt`).
#guard (bigDemoCompressedGen.gen (10 ^ 9)).map (fun p => (p.1.val, p.2))
  == some (333333332, Ordering.gt)

-- The mixed regime at depth: `Ordering × AzNat` (holes at counter bits
-- `{1, 3}` both set — 12 live per 16-block), fast-unranked at `10^9 + 5 =
-- 12 · 83333333 + 9`: the 9th live offset of block `16 · 83333333` is 9.
#guard fastUnrankPair orderingsIncreasingGen naturalsGen inferInstance inferInstance
  (10 ^ 9 + 5) == 1333333337
#guard countBelow ![some 2, none] ![3, 0] 1333333337 == 10 ^ 9 + 5

end CompressFast

-- THE DEEP INSTANCE ACCESSES (new with the `compressFast` swap): compressed
-- position `10^6` read directly through the PUBLIC instances. For the pair,
-- `10^6 = 12 · 83333 + 4` lands on raw counter `16 · 83333 + 4 = 1333332`
-- (12 live per 16-block, holes at counter bits `{1, 3}` both set), whose
-- `Ordering` bits `{1, 3}` are clear (`.lt`) and whose `AzNat` index is
-- `bit 0 + bit 2 · 2 + (k >> 4) · 4 = 333334`.
#guard (gen (T := Ordering × AzNat) (10 ^ 6)).map (fun p => (p.1, p.2.toNat))
  = some (.lt, 333334)

end Azurite
