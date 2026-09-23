/-
  `Compress` — hole compression for `ExhaustiveGenerator`s.

  A generator's LIVE counters are the `k` with `(gen k).isSome`. Base and
  all-infinite composite generators are hole-free (`Contiguous`), but the
  capped fair products of `FairCapped.lean` have INTERIOR holes: counters
  where a non-power-of-two capped slot decodes out of range (plus, in the
  all-capped case, everything past `2 ^ ∑ bits`). Compression re-indexes any
  generator through the increasing enumeration of its live counters —
  `compress g …` produces the SAME value sequence with the gaps deleted, so
  the result is contiguous again (and finitely bounded when the live set is
  finite).

  The two regimes are unified by an optional live count `N : Option ℕ`
  (`none` = infinitely many live counters, `some n` = exactly `n`), with the
  guard `Under N c` (`c` is below the count) written in the same
  `∀ b, N = some b → c < b` shape as the capped-assignment rank guards.
  `compress` consumes two count hypotheses:
  * `h`  (at least `N` live): below the count there is always a next live
    counter — this powers the `Nat.find` recursion of `unrank`;
  * `h'` (at most `N` live): every live counter's rank is below the count —
    this places every value at a compressed index.

  `rankSpec k` counts the live counters below `k` (a `Finset.range` filter
  card — the computable-but-linear SPEC; the drop-in fast digit-DP rank/unrank
  lives in `CompressFast.lean`). `unrank` walks the live counters by iterated `Nat.find`
  (`unrankAux` packages the walk with its invariant, so the runtime cost of
  `unrank i` is ONE scan of the raw counters up to the `i`-th live one —
  `rankSpec` itself is never evaluated at runtime). `rankSpec`/`unrank` are
  mutually inverse order isomorphisms between the compressed indices and the
  live counters, `compress` is the re-indexed generator, and the no-holes
  lemmas make compression the identity (gen-pointwise) on generators that
  were contiguous already.

  Feeding the count hypotheses: the live counters of ANY generator for `T`
  biject with `T` itself (`occurs_exactly_once`), so a cardinality datum for
  the TYPE suffices. `HasCount T N` packages it (`T ≃ Fin n` resp. `ℕ ↪ T`),
  `hasCount_h`/`hasCount_h'` turn it into the hypotheses for EVERY generator
  of `T`, and `HasCount.prod`/`mulCount` compose counts across products
  (with the `∞ * 0 = 0` convention for an infinite component paired with an
  empty one). `FairCapped.lean` instantiates all of this per slot spec.
-/
import Azurite.ExhaustiveGenerator.Count
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Fin.Basic

namespace Azurite

/-! ### The optional-count guard -/

/-- `c` lies **under** the optional count `N`: vacuous for `N = none`
(infinitely many), `c < n` for `N = some n`. Same shape as the capped
assignment rank guards of `BitInterleaveCapped.lean`. -/
def Under (N : Option ℕ) (c : ℕ) : Prop := ∀ b, N = some b → c < b

instance : (N : Option ℕ) → (c : ℕ) → Decidable (Under N c)
  | none, _ => isTrue fun _ h => nomatch h
  | some b, c =>
    decidable_of_iff (c < b) ⟨fun h _ hb' => Option.some.inj hb' ▸ h, fun h => h b rfl⟩

theorem under_none (c : ℕ) : Under none c := fun _ h => nomatch h

theorem under_some_iff {n c : ℕ} : Under (some n) c ↔ c < n :=
  ⟨fun h => h n rfl, fun h _ hb => Option.some.inj hb ▸ h⟩

/-- Being under a count is downward closed. -/
theorem Under.of_le {N : Option ℕ} {c c' : ℕ} (hcc : c ≤ c') (h : Under N c') : Under N c :=
  fun b hb => Nat.lt_of_le_of_lt hcc (h b hb)

namespace ExhaustiveGenerator

variable {T : Type*}

/-! ### The live-counter rank (spec) -/

/-- The **rank** of a raw counter `k`: the number of LIVE counters (positions
where `g.gen` produces a value) strictly below `k`. This is the compressed
index of `k` when `k` is itself live. A computable `Finset` count, but LINEAR
in `k` — it is the SPEC; a fast digit-DP replacement is future work (chunk
4d). It is also never evaluated at runtime by `compress` (it appears only in
proofs; `unrank` scans with `Nat.find` directly). -/
def rankSpec (g : ExhaustiveGenerator T) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun k' => (g.gen k').isSome).card

theorem rankSpec_zero (g : ExhaustiveGenerator T) : rankSpec g 0 = 0 := by
  simp [rankSpec]

theorem rankSpec_succ_of_isSome {g : ExhaustiveGenerator T} {k : ℕ}
    (hk : (g.gen k).isSome) : rankSpec g (k + 1) = rankSpec g k + 1 := by
  rw [rankSpec, Finset.range_add_one, Finset.filter_insert, ite_eq_left hk,
    Finset.card_insert_of_notMem (by simp)]
  rfl

theorem rankSpec_succ_of_not_isSome {g : ExhaustiveGenerator T} {k : ℕ}
    (hk : ¬(g.gen k).isSome) : rankSpec g (k + 1) = rankSpec g k := by
  rw [rankSpec, Finset.range_add_one, Finset.filter_insert, ite_eq_right hk]
  rfl

theorem rankSpec_le_rankSpec (g : ExhaustiveGenerator T) {k k' : ℕ} (h : k ≤ k') :
    rankSpec g k ≤ rankSpec g k' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- A counter's rank is at most the counter itself. -/
theorem rankSpec_le (g : ExhaustiveGenerator T) (k : ℕ) : rankSpec g k ≤ k :=
  le_of_le_of_eq (Finset.card_filter_le _ _) (Finset.card_range k)

/-- The rank does not move across a dead stretch `[a, b)`. -/
theorem rankSpec_eq_of_not_isSome (g : ExhaustiveGenerator T) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j < b → ¬(g.gen j).isSome) : rankSpec g b = rankSpec g a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [rankSpec_succ_of_not_isSome (h n hn (Nat.lt_succ_self n))]
    exact ih fun j hj hjn => h j hj (Nat.lt_succ_of_lt hjn)

/-- On an all-live prefix the rank is the identity. -/
theorem rankSpec_eq_self_of_isSome (g : ExhaustiveGenerator T) {b : ℕ}
    (h : ∀ j, j < b → (g.gen j).isSome) : rankSpec g b = b := by
  rw [rankSpec, Finset.filter_true_of_mem fun j hj => h j (Finset.mem_range.mp hj),
    Finset.card_range]

/-- The rank strictly increases across a LIVE counter. -/
theorem rankSpec_lt_rankSpec {g : ExhaustiveGenerator T} {k k' : ℕ}
    (hk : (g.gen k).isSome) (hkk' : k < k') : rankSpec g k < rankSpec g k' := by
  have h1 := rankSpec_succ_of_isSome hk
  have h2 := rankSpec_le_rankSpec g (show k + 1 ≤ k' from hkk')
  omega

/-- The rank is injective on live counters. -/
theorem eq_of_rankSpec_eq {g : ExhaustiveGenerator T} {k k' : ℕ}
    (hk : (g.gen k).isSome) (hk' : (g.gen k').isSome)
    (h : rankSpec g k = rankSpec g k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := rankSpec_lt_rankSpec hk hlt; omega
  · exact heq
  · have := rankSpec_lt_rankSpec hk' hgt; omega

/-! ### Unranking: the increasing enumeration of the live counters -/

/-- **The live-counter walk.** `unrankAux g N h i hi` is the `i`-th live
counter of `g` (0-based), packaged with the walk's invariant: it IS live and
its rank is `i`. Each step is a `Nat.find` for the next live counter, whose
existence comes from the at-least-`N` hypothesis `h` at the guard
`Under N (rankSpec …)` maintained by the invariant — so the runtime cost is a
single left-to-right scan of the raw counters (the `rankSpec` bookkeeping is
proof-only and erased). -/
def unrankAux (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome) :
    (i : ℕ) → Under N i → {k : ℕ // (g.gen k).isSome ∧ rankSpec g k = i}
  | 0, hi =>
    have hex := h 0 (by rw [rankSpec_zero]; exact hi)
    ⟨Nat.find hex, (Nat.find_spec hex).2, by
      rw [rankSpec_eq_of_not_isSome g (Nat.zero_le _)
        (fun j _ hj hs => Nat.find_min hex hj ⟨Nat.zero_le j, hs⟩), rankSpec_zero]⟩
  | i + 1, hi =>
    let u := unrankAux g N h i (Under.of_le (Nat.le_succ i) hi)
    have hex := h (u.1 + 1) (by rw [rankSpec_succ_of_isSome u.2.1, u.2.2]; exact hi)
    ⟨Nat.find hex, (Nat.find_spec hex).2, by
      rw [rankSpec_eq_of_not_isSome g (Nat.find_spec hex).1
        (fun j hj hjf hs => Nat.find_min hex hjf ⟨hj, hs⟩),
        rankSpec_succ_of_isSome u.2.1, u.2.2]⟩

/-- **Unrank**: the `i`-th live counter of `g` (`0` junk past the live count).
The order isomorphism inverse to `rankSpec` between compressed indices under
`N` and live counters (`rankSpec_unrank`/`unrank_rankSpec`). -/
def unrank (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome) (i : ℕ) : ℕ :=
  if hi : Under N i then (unrankAux g N h i hi).1 else 0

variable {g : ExhaustiveGenerator T} {N : Option ℕ}
  {h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome}

/-- The `i`-th live counter is live. -/
theorem gen_unrank_isSome {i : ℕ} (hi : Under N i) : (g.gen (unrank g N h i)).isSome := by
  rw [unrank, dite_eq_left hi]
  exact (unrankAux g N h i hi).2.1

/-- `rankSpec` is a left inverse of `unrank` on indices under the count. -/
theorem rankSpec_unrank {i : ℕ} (hi : Under N i) : rankSpec g (unrank g N h i) = i := by
  rw [unrank, dite_eq_left hi]
  exact (unrankAux g N h i hi).2.2

/-- `unrank` is strictly monotone on the indices under the count. -/
theorem unrank_lt_unrank {i j : ℕ} (hij : i < j) (hj : Under N j) :
    unrank g N h i < unrank g N h j := by
  have hi : Under N i := Under.of_le (Nat.le_of_lt hij) hj
  by_contra hge
  have hmono := rankSpec_le_rankSpec g (Nat.le_of_not_lt hge)
  rw [rankSpec_unrank hi, rankSpec_unrank hj] at hmono
  omega

/-- `unrank` is a right inverse of `rankSpec` on live counters: every live
counter is the `rankSpec k`-th live counter. -/
theorem unrank_rankSpec {k : ℕ} (hk : (g.gen k).isSome) (hr : Under N (rankSpec g k)) :
    unrank g N h (rankSpec g k) = k :=
  eq_of_rankSpec_eq (gen_unrank_isSome hr) hk (rankSpec_unrank hr)

/-! ### The compressed generator -/

/-- **Hole compression.** Re-index `g` through the increasing enumeration of
its live counters: `gen i = g.gen (unrank … i)` for `i` under the live count
`N`, `none` past it. The VALUE SEQUENCE is exactly `g`'s (compression deletes
the gaps, order untouched); the compressed generator is always contiguous
(`compress_contiguous`) and is finitely bounded at `n` when `N = some n`
(`FiniteGenerator.ofCompress`). The count hypotheses `h`/`h'` (at least resp.
at most `N` live counters) are typically supplied by
`hasCount_h`/`hasCount_h'` from a `HasCount` cardinality datum. -/
@[reducible] def compress (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k)) : ExhaustiveGenerator T where
  gen i := if Under N i then g.gen (unrank g N h i) else none
  occurs_exactly_once t := by
    obtain ⟨n, hn, hun⟩ := g.occurs_exactly_once t
    have hlive : (g.gen n).isSome := by rw [hn]; rfl
    have hU : Under N (rankSpec g n) := h' n hlive
    refine ⟨rankSpec g n, ?_, ?_⟩
    · -- Existence: the compressed index of `t` is the rank of its raw index.
      show (if Under N (rankSpec g n) then g.gen (unrank g N h (rankSpec g n)) else none)
        = some t
      rw [ite_eq_left hU, unrank_rankSpec hlive hU]
      exact hn
    · -- Uniqueness: a producing compressed index unranks to the raw index.
      intro j hj
      have hj' : (if Under N j then g.gen (unrank g N h j) else none) = some t := hj
      by_cases hUj : Under N j
      · rw [ite_eq_left hUj] at hj'
        have hjeq : unrank g N h j = n := hun _ hj'
        calc j = rankSpec g (unrank g N h j) := (rankSpec_unrank hUj).symm
          _ = rankSpec g n := by rw [hjeq]
      · rw [ite_eq_right hUj] at hj'
        exact absurd hj' (by simp)

/-- The compressed generator produces a value at every index under the count. -/
theorem compress_gen_isSome (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k)) {i : ℕ} (hi : Under N i) :
    ((compress g N h h').gen i).isSome := by
  show (if Under N i then g.gen (unrank g N h i) else none).isSome
  rw [ite_eq_left hi]
  exact gen_unrank_isSome hi

/-- The compressed generator is `none` at every index past the count. -/
theorem compress_gen_none (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k)) {i : ℕ} (hi : ¬Under N i) :
    (compress g N h h').gen i = none :=
  ite_eq_right hi

/-- **Compression restores contiguity**: the compressed generator is `some`
exactly on the initial segment under the count, hence `Contiguous` — in both
regimes (always-`some` for `N = none`). -/
theorem compress_contiguous (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k)) :
    @Contiguous T (compress g N h h') :=
  @Contiguous.mk T (compress g N h h') fun n hnone => by
    cases N with
    | none =>
      exact absurd hnone
        (Option.isSome_iff_ne_none.mp (compress_gen_isSome g none h h' (under_none n)))
    | some m =>
      by_cases hn : n < m
      · exact absurd hnone (Option.isSome_iff_ne_none.mp
          (compress_gen_isSome g (some m) h h' (under_some_iff.mpr hn)))
      · exact compress_gen_none g (some m) h h'
          fun hu => hn (Nat.lt_of_succ_lt (under_some_iff.mp hu))

/-! ### No-holes transparency

On a generator that is already hole-free (every counter under the count is
live), compression is the identity: `unrank` is the identity on the valid
range and `compress` agrees with `g` gen-pointwise EVERYWHERE — so hole-free
cases (e.g. power-of-two cards like `UInt64 × UInt64`) are unchanged. -/

/-- On a no-holes generator, `unrank` is the identity under the count. -/
theorem unrank_eq_self (hnh : ∀ k, Under N k → (g.gen k).isSome) {i : ℕ} (hi : Under N i) :
    unrank g N h i = i := by
  have h1 : rankSpec g (unrank g N h i) = i := rankSpec_unrank hi
  have h2 := rankSpec_le g (unrank g N h i)
  rcases Nat.lt_or_ge i (unrank g N h i) with hlt | hge
  · have hpre : rankSpec g (i + 1) = i + 1 := rankSpec_eq_self_of_isSome g fun j hj =>
      hnh j (Under.of_le (Nat.lt_succ_iff.mp hj) hi)
    have := rankSpec_le_rankSpec g (show i + 1 ≤ unrank g N h i from hlt)
    omega
  · omega

/-- On a no-holes generator, compression is gen-pointwise the identity (the
at-most hypothesis `h'` forces `g` to be `none` past the count too). -/
theorem compress_gen_eq_of_no_holes (g : ExhaustiveGenerator T) (N : Option ℕ)
    (h : ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under N (rankSpec g k))
    (hnh : ∀ k, Under N k → (g.gen k).isSome) (i : ℕ) :
    (compress g N h h').gen i = g.gen i := by
  show (if Under N i then g.gen (unrank g N h i) else none) = g.gen i
  by_cases hi : Under N i
  · rw [ite_eq_left hi, unrank_eq_self hnh hi]
  · rw [ite_eq_right hi]
    cases N with
    | none => exact absurd (under_none i) hi
    | some m =>
      have hm : m ≤ i := Nat.le_of_not_lt fun hlt => hi (under_some_iff.mpr hlt)
      by_contra hne
      have hlive : (g.gen i).isSome :=
        Option.isSome_iff_ne_none.mpr fun h0 => hne (h0 ▸ rfl)
      have hcnt : rankSpec g i < m := under_some_iff.mp (h' i hlive)
      have hpre : rankSpec g m = m :=
        rankSpec_eq_self_of_isSome g fun j hj => hnh j (under_some_iff.mpr hj)
      have := rankSpec_le_rankSpec g hm
      omega

end ExhaustiveGenerator

/-! ### `FiniteGenerator` data for a finitely compressed generator -/

open ExhaustiveGenerator in
/-- `FiniteGenerator` data for `compress g (some n) …`: the compressed
generator produces exactly the indices below the live count `n`. -/
@[reducible] def FiniteGenerator.ofCompress {T : Type*} (g : ExhaustiveGenerator T) (n : ℕ)
    (h : ∀ m, Under (some n) (rankSpec g m) → ∃ k, m ≤ k ∧ (g.gen k).isSome)
    (h' : ∀ k, (g.gen k).isSome → Under (some n) (rankSpec g k)) :
    @FiniteGenerator T (compress g (some n) h h') :=
  -- NB explicit `mk` (not `where`): structure-instance notation fails to unify
  -- the explicit instance argument when it is an application, not a variable.
  @FiniteGenerator.mk T (compress g (some n) h h') n
    (fun i hi => compress_gen_none g (some n) h h'
      fun hu => absurd (under_some_iff.mp hu) (by omega))
    (fun i hi => Option.isSome_iff_ne_none.mp
      (compress_gen_isSome g (some n) h h' (under_some_iff.mpr hi)))

/-! ### Cardinality data: feeding the count hypotheses

The live counters of ANY generator for `T` biject with `T` itself
(`occurs_exactly_once`: live `k ↦ (gen k).get`, inverse `t ↦ idx t`). So the
at-least/at-most count hypotheses of `compress` follow from a cardinality
datum for the TYPE alone — `HasCount T N` — which composes across products by
pure type arithmetic, with no reference to any particular generator. -/

/-- Optional-count multiplication with the `∞ * 0 = 0` convention: `none`
(infinite) absorbs everything except a zero factor. This is the live count of
a product generator from its components' counts. -/
def mulCount : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a * b)
  | some 0, none => some 0
  | some (_ + 1), none => none
  | none, some 0 => some 0
  | none, some (_ + 1) => none
  | none, none => none

/-- Cardinality data for `T` matching an optional count: an enumeration
`T ≃ Fin n` for `some n`, an injection `ℕ → T` (so `T` is infinite) for
`none`. A `Prop` (the equivalence is only ever used inside count proofs). -/
def HasCount (T : Type*) : Option ℕ → Prop
  | some n => Nonempty (T ≃ Fin n)
  | none => ∃ f : ℕ → T, Function.Injective f

/-- Cardinality data composes across binary products, with `mulCount` giving
the product count (an infinite factor paired with an EMPTY one yields the
empty product — the `∞ * 0 = 0` convention). -/
theorem HasCount.prod {A B : Type*} {a b : Option ℕ} (ha : HasCount A a)
    (hb : HasCount B b) : HasCount (A × B) (mulCount a b) := by
  match a, b with
  | some m, some n =>
    obtain ⟨eA⟩ := ha
    obtain ⟨eB⟩ := hb
    exact ⟨(eA.prodCongr eB).trans finProdFinEquiv⟩
  | some 0, none =>
    obtain ⟨eA⟩ := ha
    have : IsEmpty A := ⟨fun x => (eA x).elim0⟩
    exact ⟨Equiv.equivOfIsEmpty (A × B) (Fin 0)⟩
  | some (m + 1), none =>
    obtain ⟨eA⟩ := ha
    obtain ⟨f, hf⟩ := hb
    exact ⟨fun k => (eA.symm 0, f k), fun k k' hkk' => hf (congrArg Prod.snd hkk')⟩
  | none, some 0 =>
    obtain ⟨eB⟩ := hb
    have : IsEmpty B := ⟨fun x => (eB x).elim0⟩
    exact ⟨Equiv.equivOfIsEmpty (A × B) (Fin 0)⟩
  | none, some (n + 1) =>
    obtain ⟨f, hf⟩ := ha
    obtain ⟨eB⟩ := hb
    exact ⟨fun k => (f k, eB.symm 0), fun k k' hkk' => hf (congrArg Prod.fst hkk')⟩
  | none, none =>
    obtain ⟨f, hf⟩ := ha
    obtain ⟨fB, -⟩ := hb
    exact ⟨fun k => (f k, fB 0), fun k k' hkk' => hf (congrArg Prod.fst hkk')⟩

namespace ExhaustiveGenerator

variable {T : Type*}

/-- **The at-least-`N`-live hypothesis from cardinality data.** For ANY
generator of `T`: below the live count there is always a next live counter.
(If all live counters sat below `n`, the unique indices `idx t` of `N`-many
distinct values would inject into the `rankSpec g n < N` live counters below
`n` — resp. `n + 1` values into `n` counters in the infinite regime.) -/
theorem hasCount_h (g : ExhaustiveGenerator T) {N : Option ℕ} (hc : HasCount T N) :
    ∀ n, Under N (rankSpec g n) → ∃ k, n ≤ k ∧ (g.gen k).isSome := by
  intro n hUn
  by_contra hno
  have hdead : ∀ k, n ≤ k → ¬(g.gen k).isSome := fun k hk hs => hno ⟨k, hk, hs⟩
  -- Every value's unique index is live and (by `hdead`) below `n`.
  have hmem : ∀ t : T, @idx T g t ∈ (Finset.range n).filter fun k => (g.gen k).isSome := by
    intro t
    have hlive : (g.gen (@idx T g t)).isSome := by rw [@gen_idx T g t]; rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlive⟩
    by_contra hge
    exact hdead _ (Nat.le_of_not_lt hge) hlive
  have hidx_inj : ∀ t t' : T, @idx T g t = @idx T g t' → t = t' := by
    intro t t' htt
    have h1 := @gen_idx T g t
    rw [htt, @gen_idx T g t'] at h1
    exact (Option.some.inj h1).symm
  cases N with
  | none =>
    obtain ⟨f, hf⟩ := hc
    -- `n + 1` distinct values inject into the live counters below `n`.
    have hcard := Finset.card_le_card_of_injOn (fun i => @idx T g (f i))
      (fun i _ => Finset.mem_coe.mpr (hmem (f i)))
      (fun i _ j _ hij => hf (hidx_inj _ _ hij))
      (s := Finset.range (n + 1))
    have hle : ((Finset.range n).filter fun k => (g.gen k).isSome).card ≤ n :=
      le_of_le_of_eq (Finset.card_filter_le _ _) (Finset.card_range n)
    rw [Finset.card_range] at hcard
    omega
  | some m =>
    obtain ⟨e⟩ := hc
    -- `m` distinct values inject into the `rankSpec g n < m` live counters.
    have hcard := Finset.card_le_card_of_injOn (fun i => @idx T g (e.symm i))
      (fun i _ => Finset.mem_coe.mpr (hmem (e.symm i)))
      (fun i _ j _ hij => e.symm.injective (hidx_inj _ _ hij))
      (s := (Finset.univ : Finset (Fin m)))
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have hUm : rankSpec g n < m := under_some_iff.mp hUn
    exact absurd hcard (by rw [rankSpec] at hUm; omega)

/-- **The at-most-`N`-live hypothesis from cardinality data.** For ANY
generator of `T`: every live counter's rank is below the live count. (A live
`k` of rank `≥ n` would put `n + 1` live counters — each carrying a distinct
value — into a type of `n` elements.) Vacuous in the infinite regime. -/
theorem hasCount_h' (g : ExhaustiveGenerator T) {N : Option ℕ} (hc : HasCount T N) :
    ∀ k, (g.gen k).isSome → Under N (rankSpec g k) := by
  intro k hk
  cases N with
  | none => exact under_none _
  | some m =>
    obtain ⟨e⟩ := hc
    rw [under_some_iff]
    by_contra hge
    rw [Nat.not_lt] at hge
    -- `k` and the live counters below it: `rankSpec g k + 1 ≥ m + 1` live
    -- counters carrying distinct values, injected into `Fin m`.
    have hSlive : ∀ j ∈ insert k ((Finset.range k).filter fun k' => (g.gen k').isSome),
        (g.gen j).isSome := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hk
      · exact (Finset.mem_filter.mp hj').2
    have hinj : Set.InjOn (fun j => e ((g.gen j).getD ((g.gen k).get hk)))
        ↑(insert k ((Finset.range k).filter fun k' => (g.gen k').isSome)) := by
      intro i hi j hj hij
      obtain ⟨vi, hvi⟩ := Option.isSome_iff_exists.mp (hSlive i (Finset.mem_coe.mp hi))
      obtain ⟨vj, hvj⟩ := Option.isSome_iff_exists.mp (hSlive j (Finset.mem_coe.mp hj))
      simp only [hvi, hvj, Option.getD_some] at hij
      have hvij : vi = vj := e.injective hij
      obtain ⟨n₀, -, hu⟩ := g.occurs_exactly_once vi
      rw [hu i hvi, hu j (show g.gen j = some vi by rw [hvj, hvij])]
    have hcard := Finset.card_le_card_of_injOn _
      (fun j _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    rw [Finset.card_insert_of_notMem (fun hmem =>
        absurd (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1) (lt_irrefl k)),
      Finset.card_univ, Fintype.card_fin] at hcard
    rw [rankSpec] at hge
    omega

end ExhaustiveGenerator

end Azurite
