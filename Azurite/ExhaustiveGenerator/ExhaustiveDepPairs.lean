/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `exhaustive_dependent_pairs` — FAIR dependent-pair generation (Malachite
  `exhaustive_dependent_pairs`): pairs `⟨a, b⟩` where `b`'s type depends on
  `a`'s value and — unlike the lexicographic `lexDepPairGen` — each fiber may
  be INFINITE. A scheduling sequence decides, at each step, which `a`'s fiber
  to advance: step `n` emits fiber `s n`'s next unseen value, so the value
  index within the fiber is the number of PRIOR occurrences of `s n` in the
  schedule (`occCount`).

  Malachite's contract on the scheduler is verbatim the hypothesis here:
  "`index_generator` must generate every natural number infinitely many
  times. Good generators can be created using `ruler_sequence` or
  `bit_distributor_sequence`." The two certificates are exactly the theorems
  proved in their ports — `exists_le_and_rulerSequence_eq` and
  `exists_le_and_bitDistributorSequence_eq` plug straight into the `hs`
  argument. `occurs_exactly_once` reduces to the schedule combinatorics:
  every fiber index pair `(i, j)` is realized at exactly one counter — the
  `(j+1)`-th occurrence of `i` in the schedule (existence
  `exists_occCount_eq` by induction on `j` through least-occurrence steps;
  uniqueness `eq_of_occCount_eq` since a later occurrence strictly grows the
  count).

  The output is the bare Σ-type `(a : A) × B a` with a DEFAULT instance
  (ruler-scheduled), matching the product precedent — the fair enumeration
  owns the type, the lexicographic `LexDepPair` is the newtype.

  FIDELITY: in the headline regime (infinite `A`, infinite fibers — the
  doctest) the port matches the Rust stream verbatim (no exhaustion ever
  fires). For finite components the Rust REMOVES exhausted iterators and
  re-targets the scheduler at the live slots (`i %= len`, `remove(i)`) — a
  stateful liveness optimization; the port keeps ABSOLUTE slots and yields
  `none` at dead ones (holes, as in the capped raw builders), preserving
  occurs-exactly-once with a different post-exhaustion ORDER. (The Rust's
  order-guarantee is weaker anyway: its `xs` is an arbitrary iterator, which
  may repeat values — the second Rust doctest emits `(3, 300)` twice; an
  `ExhaustiveGenerator` first component rules that out.) The
  `stop_after_empty_ys` variant is a raw-iterator device with no
  occurs-exactly-once reading and is not ported.
-/
import Azurite.ExhaustiveGenerator.RulerSequence
import Azurite.ExhaustiveGenerator.BitDistributorSequence
import Azurite.ExhaustiveGenerator.Enums
import Azurite.ExhaustiveGenerator.PositiveNaturals

namespace Azurite

namespace ExhaustiveGenerator

/-! ### Schedule combinatorics: occurrence counting -/

/-- The number of occurrences of `i` in the schedule `s` BEFORE step `n`.
This is the fiber-value index at step `n`: each earlier occurrence of `i`
consumed one value of fiber `i`. -/
def occCount (s : ℕ → ℕ) (i n : ℕ) : ℕ :=
  ((Finset.range n).filter fun m => s m = i).card

/-- **Occurrence uniqueness**: two occurrences of `i` with the same prior
count are the same step (a later occurrence sees strictly more history). -/
theorem eq_of_occCount_eq {s : ℕ → ℕ} {i n n' : ℕ} (hn : s n = i) (hn' : s n' = i)
    (h : occCount s i n = occCount s i n') : n = n' := by
  -- Symmetric in `n, n'`; a strict inequality inflates the count.
  suffices key : ∀ {a b : ℕ}, a < b → s a = i → occCount s i a < occCount s i b by
    rcases lt_trichotomy n n' with hlt | heq | hlt
    · exact absurd h (Nat.ne_of_lt (key hlt hn))
    · exact heq
    · exact absurd h.symm (Nat.ne_of_lt (key hlt hn'))
  intro a b hab ha
  have hle : (insert a ((Finset.range a).filter fun m => s m = i)).card
      ≤ ((Finset.range b).filter fun m => s m = i).card := by
    apply Finset.card_le_card
    intro m hm
    rw [Finset.mem_insert] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hm with rfl | hm
    · exact ⟨hab, ha⟩
    · rw [Finset.mem_filter, Finset.mem_range] at hm
      exact ⟨by omega, hm.2⟩
  rw [Finset.card_insert_of_notMem (fun hmem => by
    rw [Finset.mem_filter, Finset.mem_range] at hmem
    omega)] at hle
  unfold occCount
  omega

/-- **Occurrence existence**: a schedule hitting every value past every point
realizes every count — for all `i, j` some step `n` is the `(j+1)`-th
occurrence of `i` (`s n = i` with exactly `j` prior occurrences). Induction
on `j`, stepping to the LEAST next occurrence each time. -/
theorem exists_occCount_eq {s : ℕ → ℕ} (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i) (i j : ℕ) :
    ∃ n, s n = i ∧ occCount s i n = j := by
  induction j with
  | zero =>
    obtain ⟨n₀, -, hn₀⟩ := hs i 0
    have hex : ∃ n, s n = i := ⟨n₀, hn₀⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rw [occCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m hm
    rw [Finset.mem_range] at hm
    exact Nat.find_min hex hm
  | succ j ih =>
    obtain ⟨n, hn, hocc⟩ := ih
    obtain ⟨n', hn'le, hn's⟩ := hs i (n + 1)
    have hex : ∃ m, n < m ∧ s m = i := ⟨n', by omega, hn's⟩
    refine ⟨Nat.find hex, (Nat.find_spec hex).2, ?_⟩
    -- The occurrences below the least next occurrence: those below `n`, plus
    -- `n` itself (nothing strictly between, by minimality).
    have hset : (Finset.range (Nat.find hex)).filter (fun m => s m = i)
        = insert n ((Finset.range n).filter fun m => s m = i) := by
      ext m
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hmN, hmi⟩
        rcases lt_trichotomy m n with hlt | rfl | hgt
        · exact Or.inr ⟨hlt, hmi⟩
        · exact Or.inl rfl
        · exact (Nat.find_min hex hmN ⟨hgt, hmi⟩).elim
      · rintro (rfl | ⟨hmn, hmi⟩)
        · exact ⟨(Nat.find_spec hex).1, hn⟩
        · exact ⟨by have := (Nat.find_spec hex).1; omega, hmi⟩
    rw [occCount, hset, Finset.card_insert_of_notMem (fun hmem => by
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      omega)]
    rw [occCount] at hocc
    omega

/-! ### The fair dependent-pair generator -/

/-- **The fair dependent-pair generator** (Malachite
`exhaustive_dependent_pairs`): step `n` advances fiber `s n`, emitting its
`occCount s (s n) n`-th value. `A` and every fiber may be infinite; finite
parts yield `none` at their dead steps (holes; see the module header). `hs`
is Malachite's scheduler contract — every index recurs past every point —
certified for the ruler sequence by `exists_le_and_rulerSequence_eq` and for
the bit-distributor sequences by `exists_le_and_bitDistributorSequence_eq`. -/
@[reducible] def exhaustiveDepPairGen {A : Type*} {B : A → Type*}
    (s : ℕ → ℕ) (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i)
    (gA : ExhaustiveGenerator A) (gB : (a : A) → ExhaustiveGenerator (B a)) :
    ExhaustiveGenerator ((a : A) × B a) where
  gen n :=
    (gA.gen (s n)).bind fun a =>
      ((gB a).gen (occCount s (s n) n)).map fun b => ⟨a, b⟩
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨jB, hjB, huB⟩ := (gB a).occurs_exactly_once b
    -- The unique producing step: the `(jB+1)`-th occurrence of `iA` in `s`.
    obtain ⟨n, hsn, hocc⟩ := exists_occCount_eq hs iA jB
    refine ⟨n, ?_, ?_⟩
    · -- Existence: step `n` reads fiber `iA` at value index `jB`.
      show (gA.gen (s n)).bind
          (fun a' => ((gB a').gen (occCount s (s n) n)).map fun b' =>
            (⟨a', b'⟩ : (a : A) × B a))
          = some ⟨a, b⟩
      rw [hsn, hiA]
      show ((gB a).gen (occCount s iA n)).map (fun b' => (⟨a, b'⟩ : (a : A) × B a))
          = some ⟨a, b⟩
      rw [hocc, hjB]
      rfl
    · -- Uniqueness: any producing step decodes to the same `(iA, jB)`, hence
      -- to `n` by occurrence uniqueness.
      intro m hm
      replace hm : (gA.gen (s m)).bind
          (fun a' => ((gB a').gen (occCount s (s m) m)).map fun b' =>
            (⟨a', b'⟩ : (a : A) × B a))
          = some ⟨a, b⟩ := hm
      rcases hga : gA.gen (s m) with _ | a'
      · rw [hga] at hm
        exact absurd hm (by simp)
      · rw [hga] at hm
        replace hm : ((gB a').gen (occCount s (s m) m)).map (fun b' =>
            (⟨a', b'⟩ : (a : A) × B a)) = some ⟨a, b⟩ := hm
        rcases hgb : (gB a').gen (occCount s (s m) m) with _ | b'
        · rw [hgb] at hm
          exact absurd hm (by simp)
        · rw [hgb] at hm
          have heq : (⟨a', b'⟩ : (a : A) × B a) = ⟨a, b⟩ := Option.some.inj hm
          obtain ⟨rfl, hb⟩ := Sigma.mk.injEq .. ▸ heq
          -- Fiber types now agree; collapse the `HEq` and decode.
          have hb' : b' = b := eq_of_heq hb
          subst hb'
          have hsm : s m = iA := huA (s m) hga
          rw [hsm] at hgb
          have hoccm : occCount s iA m = jB := huB _ hgb
          exact eq_of_occCount_eq hsm hsn (hoccm.trans hocc.symm)

end ExhaustiveGenerator

/-! ### The default `Sigma` instance

The fair enumeration owns the bare Σ-type (the lexicographic variant is the
`LexDepPair` newtype), with Malachite's conventional scheduler — the ruler
sequence — whose recurrence certificate is `exists_le_and_rulerSequence_eq`.
No finiteness or contiguity constraints: any generator works on either side,
finite parts contributing holes. -/

open ExhaustiveGenerator

/-- Fair `ExhaustiveGenerator` on `(a : A) × B a`, ruler-scheduled (Malachite
`exhaustive_dependent_pairs` with `ruler_sequence`). -/
instance instExhaustiveGeneratorSigma {A : Type*} {B : A → Type*}
    [gA : ExhaustiveGenerator A] [gB : ∀ a, ExhaustiveGenerator (B a)] :
    ExhaustiveGenerator ((a : A) × B a) :=
  exhaustiveDepPairGen rulerSequence exists_le_and_rulerSequence_eq gA fun a => gB a

/-! ### Guards

The 50-value table is Malachite's `exhaustive_dependent_pairs` doctest
VERBATIM: `x` over the positive naturals, fiber of `x` the positive multiples
`x, 2x, 3x, …`, ruler-scheduled. The doctest's `MultiplesGeneratorHelper` is
the naturals fiber displayed through `(j+1)·x`, so the Σ-instance over
`{n : AzNat // 0 < n} × AzNat` replays it exactly (all parts infinite — the
no-holes regime where port and Rust agree step for step). -/

-- Malachite's doctest, verbatim.
#guard (firstN ((_ : {n : AzNat // 0 < n}) × AzNat) 50).map
    (fun p => (p.1.val.toNat, (p.2.toNat + 1) * p.1.val.toNat))
  = [(1, 1), (2, 2), (1, 2), (3, 3), (1, 3), (2, 4), (1, 4), (4, 4), (1, 5), (2, 6),
     (1, 6), (3, 6), (1, 7), (2, 8), (1, 8), (5, 5), (1, 9), (2, 10), (1, 10), (3, 9),
     (1, 11), (2, 12), (1, 12), (4, 8), (1, 13), (2, 14), (1, 14), (3, 12), (1, 15),
     (2, 16), (1, 16), (6, 6), (1, 17), (2, 18), (1, 18), (3, 15), (1, 19), (2, 20),
     (1, 20), (4, 12), (1, 21), (2, 22), (1, 22), (3, 18), (1, 23), (2, 24), (1, 24),
     (5, 10), (1, 25), (2, 26)]

section MixedGuard

/-- A genuinely dependent family with a FINITE fiber: `false ↦ Ordering`
(3 values, then holes), `true ↦ AzNat` (infinite). -/
private def mixedB : Bool → Type := fun b => match b with
  | false => Ordering
  | true => AzNat

@[reducible] private def mixedGB : (b : Bool) → ExhaustiveGenerator (mixedB b) := fun b => match b with
  | false => orderingsIncreasingGen
  | true => naturalsGen

private def mixedRender : ((b : Bool) × mixedB b) → Bool × ℕ
  | ⟨false, c⟩ => (false, match (c : Ordering) with | .lt => 0 | .eq => 1 | .gt => 2)
  | ⟨true, n⟩ => (true, (n : AzNat).toNat)

-- Explicit builder, mixed fibers, OUR hole order (not a Rust doctest — the
-- Rust re-targets its scheduler after exhaustion; see the module header):
-- 16 ruler-scheduled counters, the `false` fiber exhausts after 3 values,
-- `s n ≥ 2` are `boolsGen` holes — 7 values survive.
#guard ((List.range 16).filterMap
    ((exhaustiveDepPairGen rulerSequence exists_le_and_rulerSequence_eq
      boolsGen mixedGB).gen)).map mixedRender
  = [(false, 0), (true, 0), (false, 1), (false, 2), (true, 1), (true, 2), (true, 3)]

end MixedGuard

-- The other certified scheduler: `bit_distributor_sequence(normal(1),
-- normal(1))` (OEIS A059905) plugs into the same builder via
-- `exists_le_and_bitDistributorSequence_eq`.
#guard ((List.range 12).filterMap
    ((exhaustiveDepPairGen
      (bitDistributorSequence (weightedRoundRobin ![1, 1] (by norm_num) (by decide)))
      (exists_le_and_bitDistributorSequence_eq _)
      naturalsGen (fun _ => naturalsGen)).gen)).map (fun p => (p.1.toNat, p.2.toNat))
  = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (3, 0), (2, 1), (3, 1), (0, 2), (1, 2),
     (0, 3), (1, 3)]

end Azurite
