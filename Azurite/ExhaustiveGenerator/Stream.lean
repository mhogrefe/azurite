/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `StreamFor` — the sequential COMPUTE rail for `ExhaustiveGenerator`s.

  A generator's `gen : ℕ → Option T` is the SPEC: pure, random-access, and
  recomputed from scratch at every call. Several generators pay O(index) PER
  CALL — the Calkin–Wilf rational generators re-iterate `sternBrocotStep` from
  `(0, 1)` at every index (so `firstN n` is O(n²) bignum steps), and
  `compress` re-scans the raw counters from `0` for every compressed index. A
  `StreamFor g` is the house two-rail fix: computable iterator DATA
  (`σ`/`init`/`next`) advancing by ONE cheap step per position, tied to the
  spec by the bridge law `emits` (`n`-fold advance, then emit = `g.gen n`).
  `firstNStream` collects a prefix in one forward pass and provably equals
  the spec-side `firstN` (`firstNStream_eq_firstN`).

  Streams provided here:
  * `ofGen` — the trivial stream (state = the index) for ANY generator; no
    speedup, guarantees every generator has a stream.
  * The five Calkin–Wilf rational streams (`positiveRationalsStream`,
    `negativeRationalsStream`, `nonnegativeRationalsStream`,
    `nonzeroRationalsStream`, `rationalsStream`): the state carries the
    Stern–Brocot pair (plus the prepend/interleave bookkeeping of the
    wrappers), `next` costs at most one `sternBrocotStep` — `firstN n` drops
    from O(n²) to O(n) bignum steps.
  * `compressStream` — the state is the raw scan position (plus the emitted
    count); a `firstNStream` prefix costs ONE left-to-right pass over the raw
    counters instead of one full scan per compressed index.
  * Cheap exemplars: `naturalsStream` (an `AzNat` `+ 1` per step instead of
    re-running the limb-decomposition `AzNat.ofNat` on a GMP `Nat` per
    index), `integersStream` (zig-zag by negate/increment instead of
    `AzInt.ofInt` from scratch), and `azNatRangeStream` (current value +
    remaining count).

  NOT here: streams for the fair composite generators (pairs/tuples/vecs).
  Those random-access their component generators, so their compute rail is a
  CACHED driver — an `IteratorCache` port: an Array-backed fill-forward cache
  (`GenCache`) over a `StreamFor`, with cached drivers threading component
  caches. That is `Cache.lean`. (This mirrors Malachite, where the exhaustive
  iterators are stateful and `IteratorCache` builds on them.)
-/
import Azurite.ExhaustiveGenerator.Basic
import Azurite.ExhaustiveGenerator.Compress
import Azurite.ExhaustiveGenerator.Rationals
import Azurite.ExhaustiveGenerator.Integers
import Azurite.ExhaustiveGenerator.AzRanges
import Azurite.AzNat.Equiv.Add
import Azurite.AzInt.Equiv.Add

namespace Azurite

open ExhaustiveGenerator

/-! ### The stream structure -/

/-- `n`-fold advance of a stream stepper: apply `next` `n` times to `s`,
keeping only the state. `advanceN next s (n + 1) = (next (advanceN next s n)).2`
holds definitionally, which is the shape the per-stream `emits` inductions
consume. -/
def advanceN {T σ : Type*} (next : σ → Option T × σ) (s : σ) : ℕ → σ
  | 0 => s
  | n + 1 => (next (advanceN next s n)).2

/-- Advance `n` times, then take one full step: the emission (and successor
state) at position `n` when starting from `s`. -/
def emitAt {T σ : Type*} (next : σ → Option T × σ) (s : σ) (n : ℕ) : Option T × σ :=
  next (advanceN next s n)

/-- The emitted value at position `n`, unfolded (`rfl`-lemma used to expose
`advanceN` to the per-stream state lemmas). -/
theorem emitAt_fst {T σ : Type*} (next : σ → Option T × σ) (s : σ) (n : ℕ) :
    (emitAt next s n).1 = (next (advanceN next s n)).1 := rfl

/-- **The sequential compute rail for a generator `g`.** The iterator data
(`σ`/`init`/`next`) is computable; the bridge law `emits` ties it to the pure
spec: emitting at position `n` (advance `n` times, then step) produces exactly
`g.gen n`. A stream makes prefix enumeration (`firstNStream`) cost one cheap
`next` per position, where `g.gen` may pay O(index) per call. -/
structure StreamFor {T : Type*} (g : ExhaustiveGenerator T) where
  /-- The iterator state type. -/
  σ : Type*
  /-- The initial state (before anything is emitted). -/
  init : σ
  /-- Emit the value at the current position (`none` once exhausted) and
  advance to the next position's state. -/
  next : σ → Option T × σ
  /-- The bridge law: the value emitted at position `n` is `g.gen n`. -/
  emits : ∀ n, (emitAt next init n).1 = g.gen n

/-- Collect the `some`-emissions of `n` consecutive stream steps starting at
state `st` — a single forward pass. -/
def collectStream {T σ : Type*} (next : σ → Option T × σ) : σ → ℕ → List T
  | _, 0 => []
  | st, n + 1 =>
    match next st with
    | (o, st') => o.toList ++ collectStream next st' n

/-- One collection step, in projection form. -/
theorem collectStream_succ {T σ : Type*} (next : σ → Option T × σ) (st : σ) (n : ℕ) :
    collectStream next st (n + 1)
      = (next st).1.toList ++ collectStream next (next st).2 n := rfl

namespace StreamFor

variable {T : Type*} {g : ExhaustiveGenerator T}

/-- The first `n` values of the stream, dropping `none`s: ONE forward pass of
`n` steps (the compute rail's replacement for `firstN`). -/
def firstNStream (s : StreamFor g) (n : ℕ) : List T :=
  collectStream s.next s.init n

/-- Collecting `n` steps from the `k`-fold advanced state yields the generator
outputs at positions `k, …, k + n - 1` — the `emits` law transported along the
pass. -/
theorem collectStream_advanceN (s : StreamFor g) (k n : ℕ) :
    collectStream s.next (advanceN s.next s.init k) n
      = (List.range' k n).filterMap g.gen := by
  induction n generalizing k with
  | zero => rfl
  | succ m ih =>
    rw [collectStream_succ]
    have h1 : (s.next (advanceN s.next s.init k)).1 = g.gen k := s.emits k
    have h2 : (s.next (advanceN s.next s.init k)).2 = advanceN s.next s.init (k + 1) := rfl
    rw [h1, h2, ih (k + 1)]
    show _ = (k :: List.range' (k + 1) m).filterMap g.gen
    cases hgk : g.gen k with
    | none => simp [hgk]
    | some t => simp [hgk]

/-- **The prefix law, list form**: one stream pass equals the pure filterMap. -/
theorem firstNStream_eq_filterMap (s : StreamFor g) (n : ℕ) :
    s.firstNStream n = (List.range n).filterMap g.gen := by
  have h := collectStream_advanceN s 0 n
  rw [List.range_eq_range']
  exact h

/-- **The prefix law**: `firstNStream` equals the spec-side `firstN` whenever
`g` is the registered instance. -/
theorem firstNStream_eq_firstN {T : Type*} [inst : ExhaustiveGenerator T]
    (s : StreamFor inst) (n : ℕ) : s.firstNStream n = firstN T n :=
  firstNStream_eq_filterMap s n

end StreamFor

/-- The trivial stream for ANY generator: the state is the index itself and
each step calls `g.gen` once. No speedup over the spec (each `next` pays
whatever `g.gen` pays), but it guarantees total coverage: every generator has
at least this stream. -/
def StreamFor.ofGen {T : Type*} (g : ExhaustiveGenerator T) : StreamFor g where
  σ := ℕ
  init := 0
  next i := (g.gen i, i + 1)
  emits n := by
    have h : ∀ m, advanceN (fun i => (g.gen i, i + 1)) 0 m = m := by
      intro m
      induction m with
      | zero => rfl
      | succ k ih =>
        rw [advanceN, ih]
    rw [emitAt_fst, h n]

/-! ### The Calkin–Wilf streams

The five rational generators of `Rationals.lean` all sit on
`positiveRationalPair n = sternBrocotStep^[n + 1] (0, 1)`, so their `gen` is
O(n) bignum steps PER CALL and `firstN n` is O(n²). The streams below carry
the current Stern–Brocot pair in their state — plus a reachability invariant
(a `Prop`, erased at runtime) that supplies the positivity proofs the subtype
generators emit — and pay at most ONE `sternBrocotStep` per position. -/

/-- One-step recurrence for the Stern–Brocot pair (unfolds the iterate). -/
theorem positiveRationalPair_succ (n : ℕ) :
    positiveRationalPair (n + 1) = sternBrocotStep (positiveRationalPair n) := by
  show sternBrocotStep^[n + 1 + 1] (0, 1) = _
  rw [Function.iterate_succ_apply']
  rfl

/-- The Calkin–Wilf stream state: the current Stern–Brocot pair, carrying the
reachability invariant that makes the emitted rationals provably positive.
The `Prop` field is erased at runtime — the state is just the two `AzNat`s. -/
structure CWState where
  /-- The current Stern–Brocot pair `(a_n, a_{n+1})`. -/
  pair : AzNat × AzNat
  /-- Reachability: the pair is `positiveRationalPair n` for some `n`. -/
  reachable : ∃ n, pair = positiveRationalPair n

namespace CWState

/-- Two CW states with the same pair are equal (proof irrelevance). -/
theorem eq_of_pair_eq {s t : CWState} (h : s.pair = t.pair) : s = t := by
  cases s; cases t; cases h; rfl

/-- The initial state: the pair of the 0-th positive rational, `(1, 1)`. -/
def init : CWState := ⟨positiveRationalPair 0, 0, rfl⟩

/-- Advance by one `sternBrocotStep`. -/
def step (s : CWState) : CWState :=
  ⟨sternBrocotStep s.pair, by
    obtain ⟨n, hn⟩ := s.reachable
    exact ⟨n + 1, by rw [hn, positiveRationalPair_succ]⟩⟩

/-- The positive rational held by a state. -/
def q (s : CWState) : AzRat := AzRat.ofAzNats s.pair.1 s.pair.2

theorem q_pos (s : CWState) : 0 < s.q := by
  obtain ⟨n, hn⟩ := s.reachable
  show 0 < AzRat.ofAzNats s.pair.1 s.pair.2
  rw [hn]
  exact positiveRationals_pos n

theorem neg_q_neg (s : CWState) : -s.q < 0 := by
  have h := s.q_pos
  rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at h ⊢
  rw [AzRat.toRat_neg]
  linarith

end CWState

/-! #### Positive rationals -/

/-- Stepper for `positiveRationalsStream`: emit the held rational, advance the
pair. -/
def positiveRationalsNext (s : CWState) : Option {q : AzRat // 0 < q} × CWState :=
  (some ⟨s.q, s.q_pos⟩, s.step)

/-- The state after `n` advances holds the `n`-th Stern–Brocot pair. -/
theorem positiveRationals_state (n : ℕ) :
    advanceN positiveRationalsNext CWState.init n = ⟨positiveRationalPair n, n, rfl⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN, ih]
    exact CWState.eq_of_pair_eq (positiveRationalPair_succ k).symm

/-- The stream for `positiveRationalsGen`: one `sternBrocotStep` per position. -/
def positiveRationalsStream : StreamFor positiveRationalsGen where
  σ := CWState
  init := CWState.init
  next := positiveRationalsNext
  emits n := by
    rw [emitAt_fst, positiveRationals_state n]
    rfl

/-! #### Negative rationals -/

/-- Stepper for `negativeRationalsStream`: emit the negated rational. -/
def negativeRationalsNext (s : CWState) : Option {q : AzRat // q < 0} × CWState :=
  (some ⟨-s.q, s.neg_q_neg⟩, s.step)

theorem negativeRationals_state (n : ℕ) :
    advanceN negativeRationalsNext CWState.init n = ⟨positiveRationalPair n, n, rfl⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN, ih]
    exact CWState.eq_of_pair_eq (positiveRationalPair_succ k).symm

/-- The stream for `negativeRationalsGen`. -/
def negativeRationalsStream : StreamFor negativeRationalsGen where
  σ := CWState
  init := CWState.init
  next := negativeRationalsNext
  emits n := by
    rw [emitAt_fst, negativeRationals_state n]
    rfl

/-! #### Nonnegative rationals (prepend `0`) -/

/-- Stepper for `nonnegativeRationalsStream`: state `none` = "have not emitted
the leading `0` yet". -/
def nonnegativeRationalsNext (s : Option CWState) :
    Option {q : AzRat // 0 ≤ q} × Option CWState :=
  match s with
  | none => (some ⟨0, le_refl 0⟩, some CWState.init)
  | some t => (some ⟨t.q, le_of_lt t.q_pos⟩, some (t.step))

theorem nonnegativeRationals_state (n : ℕ) :
    advanceN nonnegativeRationalsNext (none : Option CWState) (n + 1)
      = some ⟨positiveRationalPair n, n, rfl⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN, ih]
    exact congrArg some (CWState.eq_of_pair_eq (positiveRationalPair_succ k).symm)

/-- The stream for `nonnegativeRationalsGen`. -/
def nonnegativeRationalsStream : StreamFor nonnegativeRationalsGen where
  σ := Option CWState
  init := none
  next := nonnegativeRationalsNext
  emits n := by
    cases n with
    | zero => rfl
    | succ m =>
      rw [emitAt_fst, nonnegativeRationals_state m]
      rfl

/-! #### Nonzero rationals (interleave `+`/`-`) -/

/-- Stepper for `nonzeroRationalsStream`: the flag records whether the
positive copy of the current pair is still owed; the pair advances only after
its negative copy is emitted. -/
def nonzeroRationalsNext (s : Bool × CWState) :
    Option {q : AzRat // q ≠ 0} × (Bool × CWState) :=
  match s with
  | (true, t) => (some ⟨t.q, ne_of_gt t.q_pos⟩, (false, t))
  | (false, t) => (some ⟨-t.q, ne_of_lt t.neg_q_neg⟩, (true, t.step))

theorem nonzeroRationals_state (n : ℕ) :
    advanceN nonzeroRationalsNext (true, CWState.init) n
      = (decide (n % 2 = 0), ⟨positiveRationalPair (n / 2), n / 2, rfl⟩) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [decide_eq_true hk, decide_eq_false (show ¬(k + 1) % 2 = 0 by omega),
        show (k + 1) / 2 = k / 2 by omega]
      rfl
    · rw [decide_eq_false (show ¬k % 2 = 0 by omega),
        decide_eq_true (show (k + 1) % 2 = 0 by omega),
        show (k + 1) / 2 = k / 2 + 1 by omega]
      exact congrArg (Prod.mk true)
        (CWState.eq_of_pair_eq (positiveRationalPair_succ (k / 2)).symm)

/-- The stream for `nonzeroRationalsGen`. -/
def nonzeroRationalsStream : StreamFor nonzeroRationalsGen where
  σ := Bool × CWState
  init := (true, CWState.init)
  next := nonzeroRationalsNext
  emits n := by
    rw [emitAt_fst, nonzeroRationals_state n]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [decide_eq_true hn]
      refine congrArg some (Subtype.ext ?_)
      show AzRat.ofAzNats (positiveRationalPair (n / 2)).1 (positiveRationalPair (n / 2)).2
        = nonzeroRationals n
      unfold nonzeroRationals
      rw [ite_eq_left hn]
      rfl
    · rw [decide_eq_false (show ¬n % 2 = 0 by omega)]
      refine congrArg some (Subtype.ext ?_)
      show -(AzRat.ofAzNats (positiveRationalPair (n / 2)).1 (positiveRationalPair (n / 2)).2)
        = nonzeroRationals n
      unfold nonzeroRationals
      rw [ite_eq_right (show ¬n % 2 = 0 by omega)]
      rfl

/-! #### All rationals (prepend `0` to the interleave) -/

/-- Stepper for `rationalsStream`: prepend-`0` state wrapped around the
`nonzeroRationals` interleave state. -/
def rationalsNext (s : Option (Bool × CWState)) :
    Option AzRat × Option (Bool × CWState) :=
  match s with
  | none => (some 0, some (true, CWState.init))
  | some (true, t) => (some t.q, some (false, t))
  | some (false, t) => (some (-t.q), some (true, t.step))

theorem rationals_state (n : ℕ) :
    advanceN rationalsNext (none : Option (Bool × CWState)) (n + 1)
      = some (decide (n % 2 = 0), ⟨positiveRationalPair (n / 2), n / 2, rfl⟩) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [decide_eq_true hk, decide_eq_false (show ¬(k + 1) % 2 = 0 by omega),
        show (k + 1) / 2 = k / 2 by omega]
      rfl
    · rw [decide_eq_false (show ¬k % 2 = 0 by omega),
        decide_eq_true (show (k + 1) % 2 = 0 by omega),
        show (k + 1) / 2 = k / 2 + 1 by omega]
      exact congrArg (fun t => some (true, t))
        (CWState.eq_of_pair_eq (positiveRationalPair_succ (k / 2)).symm)

/-- The stream for `rationalsGen` (the full `AzRat` enumeration
`0, 1, -1, 1/2, -1/2, …`): at most one `sternBrocotStep` per position, so a
prefix of length `n` costs O(n) bignum steps instead of the spec's O(n²). -/
def rationalsStream : StreamFor rationalsGen where
  σ := Option (Bool × CWState)
  init := none
  next := rationalsNext
  emits n := by
    cases n with
    | zero => rfl
    | succ m =>
      rw [emitAt_fst, rationals_state m]
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · rw [decide_eq_true hm]
        refine congrArg some ?_
        show AzRat.ofAzNats (positiveRationalPair (m / 2)).1 (positiveRationalPair (m / 2)).2
          = nonzeroRationals m
        unfold nonzeroRationals
        rw [ite_eq_left hm]
        rfl
      · rw [decide_eq_false (show ¬m % 2 = 0 by omega)]
        refine congrArg some ?_
        show -(AzRat.ofAzNats (positiveRationalPair (m / 2)).1 (positiveRationalPair (m / 2)).2)
          = nonzeroRationals m
        unfold nonzeroRationals
        rw [ite_eq_right (show ¬m % 2 = 0 by omega)]
        rfl

/-! ### The compress stream

`(compress g N h h').gen i` walks the raw counters from `0` at EVERY call
(`unrank` is an `i`-fold `Nat.find`), so `firstN n` scans the raw range `n`
times. The stream keeps the raw scan position in its state: each `next`
resumes the scan where the last one stopped, so a prefix costs ONE pass. -/

namespace ExhaustiveGenerator

variable {T : Type*}

/-- Stream state for `compress`: the next compressed index `idx` and the raw
scan position `pos`, tied by the invariant that exactly `idx` live counters
lie below `pos`. -/
structure CompressState (g : ExhaustiveGenerator T) where
  /-- The next compressed index to emit. -/
  idx : ℕ
  /-- The raw counter where the scan for the next live counter resumes. -/
  pos : ℕ
  /-- Exactly `idx` live counters lie strictly below `pos`. -/
  inv : rankSpec g pos = idx

/-- Initial compress-stream state: compressed index `0`, scan from raw `0`. -/
def compressInit (g : ExhaustiveGenerator T) : CompressState g :=
  ⟨0, 0, rankSpec_zero g⟩

/-- One compress-stream step: if the next compressed index is under the live
count, scan forward (`Nat.find`) to the next live raw counter, emit its value,
and resume past it; otherwise emit `none` and stay put. The at-least-count
hypothesis `h` (fed through the state invariant) powers the `Nat.find`. -/
def compressNext (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (s : CompressState g) : Option T × CompressState g :=
  if hu : Under N s.idx then
    have hex : ∃ k, s.pos ≤ k ∧ (g.gen k).isSome := h s.pos (by rw [s.inv]; exact hu)
    (g.gen (Nat.find hex),
      ⟨s.idx + 1, Nat.find hex + 1, by
        rw [rankSpec_succ_of_isSome (Nat.find_spec hex).2,
          rankSpec_eq_of_not_isSome g (Nat.find_spec hex).1
            fun j hj hjf hs => Nat.find_min hex hjf ⟨hj, hs⟩,
          s.inv]⟩)
  else (none, s)

variable {g : ExhaustiveGenerator T} {N : Option ℕ}
  {h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome}

/-- Scanning forward from any position of rank `i` finds exactly the `i`-th
live counter: `Nat.find` agrees with `unrank`. -/
theorem unrank_eq_find {p i : ℕ} (hp : rankSpec g p = i) (hu : Under N i)
    (hex : ∃ k, p ≤ k ∧ (g.gen k).isSome) :
    unrank g N h i = Nat.find hex := by
  have hlive : (g.gen (Nat.find hex)).isSome := (Nat.find_spec hex).2
  have hrank : rankSpec g (Nat.find hex) = i := by
    rw [rankSpec_eq_of_not_isSome g (Nat.find_spec hex).1
      fun j hj hjf hs => Nat.find_min hex hjf ⟨hj, hs⟩, hp]
  rw [← hrank]
  exact unrank_rankSpec hlive (by rw [hrank]; exact hu)

/-- A step under the live count advances the compressed index. -/
theorem compressNext_idx_of_under {s : CompressState g} (hu : Under N s.idx) :
    ((compressNext g N h s).2).idx = s.idx + 1 := by
  simp only [compressNext]
  rw [dite_eq_left hu]

/-- A step under the live count emits the next live counter's value. -/
theorem compressNext_fst_of_under {s : CompressState g} (hu : Under N s.idx)
    (hex : ∃ k, s.pos ≤ k ∧ (g.gen k).isSome) :
    (compressNext g N h s).1 = g.gen (Nat.find hex) := by
  simp only [compressNext]
  rw [dite_eq_left hu]

/-- A step past the live count emits `none` and stays put. -/
theorem compressNext_of_not_under {s : CompressState g} (hu : ¬Under N s.idx) :
    compressNext g N h s = (none, s) := by
  simp only [compressNext]
  rw [dite_eq_right hu]

/-- The compressed index after `n` advances is `n` — until the live count is
exhausted, after which the state is stuck past the count. -/
theorem compress_state (n : ℕ) :
    (advanceN (compressNext g N h) (compressInit g) n).idx = n ∨
      (¬Under N (advanceN (compressNext g N h) (compressInit g) n).idx ∧
        (advanceN (compressNext g N h) (compressInit g) n).idx ≤ n) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [advanceN]
    by_cases hu : Under N (advanceN (compressNext g N h) (compressInit g) k).idx
    · rw [compressNext_idx_of_under hu]
      rcases ih with hik | ⟨hnu, _⟩
      · exact Or.inl (by omega)
      · exact absurd hu hnu
    · rw [compressNext_of_not_under hu]
      show (advanceN (compressNext g N h) (compressInit g) k).idx = k + 1 ∨
        (¬Under N (advanceN (compressNext g N h) (compressInit g) k).idx ∧
          (advanceN (compressNext g N h) (compressInit g) k).idx ≤ k + 1)
      rcases ih with hik | ⟨hnu, hle⟩
      · exact Or.inr ⟨hu, by omega⟩
      · exact Or.inr ⟨hnu, by omega⟩

/-- **The stream for a compressed generator.** State = raw scan position (+
emitted count); each `next` resumes the raw scan where the previous step
stopped, so `firstNStream n` is ONE pass over the raw counters — versus one
full re-scan per index on the spec rail. -/
def compressStream (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k)) :
    StreamFor (compress g N h h') where
  σ := CompressState g
  init := compressInit g
  next := compressNext g N h
  emits n := by
    rw [emitAt_fst]
    show (compressNext g N h (advanceN (compressNext g N h) (compressInit g) n)).1
      = if Under N n then g.gen (unrank g N h n) else none
    rcases compress_state (g := g) (N := N) (h := h) n with hidx | ⟨hnu, hle⟩
    · by_cases hu : Under N n
      · have hu' : Under N (advanceN (compressNext g N h) (compressInit g) n).idx := by
          rw [hidx]; exact hu
        have hex : ∃ k, (advanceN (compressNext g N h) (compressInit g) n).pos ≤ k ∧
            (g.gen k).isSome :=
          h _ (by rw [(advanceN (compressNext g N h) (compressInit g) n).inv]; exact hu')
        rw [compressNext_fst_of_under hu' hex, ite_eq_left hu,
          unrank_eq_find
            (by rw [(advanceN (compressNext g N h) (compressInit g) n).inv]; exact hidx)
            hu hex]
      · rw [compressNext_of_not_under (by rw [hidx]; exact hu), ite_eq_right hu]
    · rw [compressNext_of_not_under hnu,
        ite_eq_right fun hun => hnu (Under.of_le hle hun)]

end ExhaustiveGenerator

/-! #### A concrete compressed stream (demo + guards)

A deliberately hole-y generator over `Bool` (live only at raw counters `1`
and `3`), compressed via a `HasCount` cardinality datum, then streamed. -/

/-- A hole-y two-value generator: `false` at raw counter `1`, `true` at raw
counter `3`, dead everywhere else. Exists purely to exercise
`compress`/`compressStream` on a generator with interior holes. -/
@[reducible] def holeyDemoGen : ExhaustiveGenerator Bool where
  gen n := if n = 1 then some false else if n = 3 then some true else none
  occurs_exactly_once t := by
    cases t
    · refine ⟨1, rfl, fun m hm => ?_⟩
      have hm' : (if m = 1 then some false else if m = 3 then some true else none)
          = some false := hm
      by_contra h1
      rw [ite_eq_right h1] at hm'
      by_cases h3 : m = 3
      · rw [ite_eq_left h3] at hm'
        exact Bool.noConfusion (Option.some.inj hm')
      · rw [ite_eq_right h3] at hm'
        simp at hm'
    · refine ⟨3, rfl, fun m hm => ?_⟩
      have hm' : (if m = 1 then some false else if m = 3 then some true else none)
          = some true := hm
      by_cases h1 : m = 1
      · rw [ite_eq_left h1] at hm'
        exact Bool.noConfusion (Option.some.inj hm')
      · rw [ite_eq_right h1] at hm'
        by_contra h3
        rw [ite_eq_right h3] at hm'
        simp at hm'

/-- `Bool` has exactly two values. -/
theorem holeyDemo_hasCount : HasCount Bool (some 2) := ⟨finTwoEquiv.symm⟩

/-- The hole-compressed demo generator: `false, true` at indices `0, 1`. -/
@[reducible] def holeyDemoCompressed : ExhaustiveGenerator Bool :=
  ExhaustiveGenerator.compress holeyDemoGen (some 2)
    (ExhaustiveGenerator.hasCount_h holeyDemoGen holeyDemo_hasCount)
    (ExhaustiveGenerator.hasCount_h' holeyDemoGen holeyDemo_hasCount)

/-- The stream for the compressed demo generator. -/
def holeyDemoStream : StreamFor holeyDemoCompressed :=
  ExhaustiveGenerator.compressStream holeyDemoGen (some 2)
    (ExhaustiveGenerator.hasCount_h holeyDemoGen holeyDemo_hasCount)
    (ExhaustiveGenerator.hasCount_h' holeyDemoGen holeyDemo_hasCount)

/-! ### Cheap exemplar streams -/

/-- Stepper for `naturalsStream`: emit the current `AzNat`, then `+ 1`. An
amortized-O(1) limb increment, where the spec's `AzNat.ofNat n` re-decomposes
the (GMP-backed) `Nat` index into limbs — Θ(limbs of `n`) divisions per call —
at every position. -/
def naturalsNext (a : AzNat) : Option AzNat × AzNat := (some a, a + 1)

theorem naturals_state (n : ℕ) :
    advanceN naturalsNext (0 : AzNat) n = AzNat.ofNat n := by
  induction n with
  | zero => exact AzNat.ofNat_zero.symm
  | succ k ih =>
    rw [advanceN, ih]
    show AzNat.ofNat k + 1 = AzNat.ofNat (k + 1)
    apply AzNat.toNat_injective
    rw [AzNat.toNat_add, AzNat.toNat_ofNat, AzNat.toNat_one, AzNat.toNat_ofNat]

/-- The stream for `naturalsGen`: `0, 1, 2, …` by repeated `+ 1`. -/
def naturalsStream : StreamFor naturalsGen where
  σ := AzNat
  init := 0
  next := naturalsNext
  emits n := by
    rw [emitAt_fst, naturals_state n]
    rfl

/-- The `ℤ`-value at zig-zag position `n` (the body of `integers`). -/
def zigZag (n : ℕ) : ℤ :=
  if n % 2 = 0 then -(n / 2 : ℤ) else ((n / 2 : ℤ) + 1)

theorem zigZag_succ_of_even {k : ℕ} (hk : k % 2 = 0) : zigZag (k + 1) = -zigZag k + 1 := by
  unfold zigZag
  rw [ite_eq_left hk, ite_eq_right (show ¬(k + 1) % 2 = 0 by omega)]
  omega

theorem zigZag_succ_of_odd {k : ℕ} (hk : k % 2 = 1) : zigZag (k + 1) = -zigZag k := by
  unfold zigZag
  rw [ite_eq_right (show ¬k % 2 = 0 by omega), ite_eq_left (show (k + 1) % 2 = 0 by omega)]
  omega

/-- Stepper for `integersStream`: emit the current `AzInt`; the parity flag
says whether the next value is `1 - v` (after a nonpositive value) or `-v`
(after a positive one). Negate/increment are O(1)-flag/amortized-O(1)-limb
ops, where the spec's `AzInt.ofInt` rebuilds sign + limb array from a GMP
integer at every position. -/
def integersNext (s : AzInt × Bool) : Option AzInt × (AzInt × Bool) :=
  (some s.1, if s.2 then (-s.1 + 1, false) else (-s.1, true))

theorem integers_state (n : ℕ) :
    advanceN integersNext ((0 : AzInt), true) n
      = (AzInt.ofInt (zigZag n), decide (n % 2 = 0)) := by
  induction n with
  | zero =>
    refine Prod.ext ?_ rfl
    show (0 : AzInt) = AzInt.ofInt (zigZag 0)
    rw [show zigZag 0 = 0 from rfl, AzInt.ofInt_zero]
  | succ k ih =>
    rw [advanceN, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [decide_eq_true hk]
      refine Prod.ext ?_ ?_
      · show -AzInt.ofInt (zigZag k) + 1 = AzInt.ofInt (zigZag (k + 1))
        rw [zigZag_succ_of_even hk, AzInt.ofInt_add, AzInt.ofInt_neg, AzInt.ofInt_one]
      · show false = decide ((k + 1) % 2 = 0)
        exact (decide_eq_false (show ¬(k + 1) % 2 = 0 by omega)).symm
    · rw [decide_eq_false (show ¬k % 2 = 0 by omega)]
      refine Prod.ext ?_ ?_
      · show -AzInt.ofInt (zigZag k) = AzInt.ofInt (zigZag (k + 1))
        rw [zigZag_succ_of_odd hk, AzInt.ofInt_neg]
      · show true = decide ((k + 1) % 2 = 0)
        exact (decide_eq_true (show (k + 1) % 2 = 0 by omega)).symm

/-- The stream for `integersGen`: `0, 1, -1, 2, -2, …` by negate/increment. -/
def integersStream : StreamFor integersGen where
  σ := AzInt × Bool
  init := (0, true)
  next := integersNext
  emits n := by
    rw [emitAt_fst, integers_state n]
    rfl

/-! #### An ascending range stream -/

/-- Stream state for `azNatRangeStream`: the current value and the remaining
count, with the invariant recovering the position (so the emitted value is
provably in `[a, b)`). -/
structure AzNatRangeState (a b : AzNat) where
  /-- The next value to emit. -/
  cur : AzNat
  /-- How many values remain (including `cur`). -/
  rem : ℕ
  /-- `rem` values remain out of `b.toNat - a.toNat`, and `cur` sits at the
  matching offset from `a`. -/
  inv : rem ≤ b.toNat - a.toNat ∧ cur.toNat = a.toNat + (b.toNat - a.toNat - rem)

/-- Initial range-stream state: at `a`, all `b.toNat - a.toNat` values left. -/
def azNatRangeInit (a b : AzNat) : AzNatRangeState a b :=
  ⟨a, b.toNat - a.toNat, by omega⟩

/-- Stepper for `azNatRangeStream`: emit the current value and `+ 1`, or
`none` forever once the count is exhausted. -/
def azNatRangeNext (a b : AzNat) (s : AzNatRangeState a b) :
    Option {x : AzNat // a ≤ x ∧ x < b} × AzNatRangeState a b :=
  if h : s.rem = 0 then (none, s)
  else
    (some ⟨s.cur, by
      obtain ⟨h1, h2⟩ := s.inv
      constructor
      · rw [AzNat.le_iff_toNat_le]; omega
      · rw [AzNat.lt_iff_toNat_lt]; omega⟩,
      ⟨s.cur + 1, s.rem - 1, by
        obtain ⟨h1, h2⟩ := s.inv
        rw [AzNat.toNat_add, AzNat.toNat_one]
        omega⟩)

/-- A step with values remaining emits `none` and stays put once exhausted. -/
theorem azNatRangeNext_of_zero {a b : AzNat} {s : AzNatRangeState a b} (h : s.rem = 0) :
    azNatRangeNext a b s = (none, s) := by
  simp only [azNatRangeNext]
  rw [dite_eq_left h]

/-- A live step decrements the remaining count. -/
theorem azNatRangeNext_rem_of_ne {a b : AzNat} {s : AzNatRangeState a b} (h : s.rem ≠ 0) :
    ((azNatRangeNext a b s).2).rem = s.rem - 1 := by
  simp only [azNatRangeNext]
  rw [dite_eq_right h]

theorem azNatRange_state (a b : AzNat) (n : ℕ) :
    (advanceN (azNatRangeNext a b) (azNatRangeInit a b) n).rem
      = b.toNat - a.toNat - n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [advanceN]
    by_cases h0 : (advanceN (azNatRangeNext a b) (azNatRangeInit a b) k).rem = 0
    · rw [azNatRangeNext_of_zero h0]
      show (advanceN (azNatRangeNext a b) (azNatRangeInit a b) k).rem
        = b.toNat - a.toNat - (k + 1)
      omega
    · rw [azNatRangeNext_rem_of_ne h0]
      omega

/-- The stream for `azNatRangeGen a b`: current value + remaining count. -/
def azNatRangeStream (a b : AzNat) : StreamFor (azNatRangeGen a b) where
  σ := AzNatRangeState a b
  init := azNatRangeInit a b
  next := azNatRangeNext a b
  emits n := by
    rw [emitAt_fst]
    have hrem := azNatRange_state a b n
    by_cases hn : n < b.toNat - a.toNat
    · have h0 : (advanceN (azNatRangeNext a b) (azNatRangeInit a b) n).rem ≠ 0 := by
        omega
      simp only [azNatRangeNext]
      rw [dite_eq_right h0,
        show @gen _ (azNatRangeGen a b) n = some _ from dite_eq_left (show n < b.toNat - a.toNat from hn)]
      refine congrArg some (Subtype.ext ?_)
      show (advanceN (azNatRangeNext a b) (azNatRangeInit a b) n).cur
        = AzNat.ofNat (a.toNat + n)
      apply AzNat.toNat_injective
      rw [AzNat.toNat_ofNat]
      have hinv := (advanceN (azNatRangeNext a b) (azNatRangeInit a b) n).inv
      omega
    · have h0 : (advanceN (azNatRangeNext a b) (azNatRangeInit a b) n).rem = 0 := by
        omega
      simp only [azNatRangeNext]
      rw [dite_eq_left h0, azNatRangeGen_gen_none a b n (by omega)]

/-! ### Guards

Each real stream is pinned to the spec rail on the existing doctest prefixes,
plus a longer Calkin–Wilf prefix that the pure `gen` would compute in O(n²)
bignum steps while the stream does O(n). -/

-- The Calkin–Wilf streams reproduce the Malachite doctest prefixes.
#guard ((positiveRationalsStream.firstNStream 7).map (·.val.toString)) ==
  ["1", "1/2", "2", "1/3", "3/2", "2/3", "3"]
#guard ((negativeRationalsStream.firstNStream 7).map (·.val.toString)) ==
  ["-1", "-1/2", "-2", "-1/3", "-3/2", "-2/3", "-3"]
#guard ((nonnegativeRationalsStream.firstNStream 7).map (·.val.toString)) ==
  ["0", "1", "1/2", "2", "1/3", "3/2", "2/3"]
#guard ((nonzeroRationalsStream.firstNStream 7).map (·.val.toString)) ==
  ["1", "-1", "1/2", "-1/2", "2", "-2", "1/3"]
#guard ((rationalsStream.firstNStream 10).map AzRat.toString) ==
  ["0", "1", "-1", "1/2", "-1/2", "2", "-2", "1/3", "-1/3", "3/2"]
-- Stream rail = spec rail on the doctest prefix.
#guard ((rationalsStream.firstNStream 10).map AzRat.toString) ==
  ((ExhaustiveGenerator.firstN AzRat 10).map AzRat.toString)
-- A longer prefix: O(n) via the stream (one `sternBrocotStep` per element),
-- O(n²) via the pure `gen`. Spot value: `rationals 299 = positiveRationals 149
-- = fusc 150 / fusc 151 = 18/25`.
#guard (rationalsStream.firstNStream 300).length == 300
#guard ((rationalsStream.firstNStream 300).getLast?.map AzRat.toString) == some "18/25"

-- The compressed demo generator and its stream: holes deleted, order kept.
#guard (@ExhaustiveGenerator.firstN _ holeyDemoGen 6) == [false, true]
#guard holeyDemoStream.firstNStream 5 == [false, true]
#guard holeyDemoStream.firstNStream 5 == (@ExhaustiveGenerator.firstN _ holeyDemoCompressed 5)

-- Cheap exemplars against their doctest prefixes.
#guard ((naturalsStream.firstNStream 5).map (·.toNat)) == [0, 1, 2, 3, 4]
#guard ((naturalsStream.firstNStream 5).map (·.toNat)) ==
  ((ExhaustiveGenerator.firstN AzNat 5).map (·.toNat))
#guard ((integersStream.firstNStream 10).map (·.toInt)) ==
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 5]
#guard ((integersStream.firstNStream 10).map (·.toInt)) ==
  ((ExhaustiveGenerator.firstN AzInt 10).map (·.toInt))
#guard (((azNatRangeStream (AzNat.ofNat 3) (AzNat.ofNat 7)).firstNStream 10).map
  (·.val.toNat)) == [3, 4, 5, 6]
#guard (((azNatRangeStream (AzNat.ofNat 5) (AzNat.ofNat 5)).firstNStream 10).map
  (·.val.toNat)) == []

end Azurite
