/-
  Level 2: the Rust-exact simulator as a PROVEN `ExhaustiveGenerator`.

  `ExhaustiveDepPairsSim.lean` replays Malachite's `ExhaustiveDependentPairs`
  stream bit for bit; this file proves that stream enumerates every dependent
  pair exactly once (`simGen`), under exactly the hypotheses the Rust
  semantics forces and the clean port (`exhaustiveDepPairGen`) does not need:

  * CONTIGUITY of `xs` and of every fiber — iterator semantics (first `none`
    is the permanent end) must agree with generator semantics, else the
    machine stops early and misses values;
  * NONEMPTY fibers (`ysGen x 0 ≠ none`) — precisely excluding the
    documented Rust hang, which genuinely breaks coverage (the machine
    spins appending and discarding empty fibers, never reaching later
    values);
  * the scheduler certificate (every value past every point), as always.

  PROOF SHAPE. Uniqueness: an emission of `⟨a, b⟩` (with `b` the fiber's
  `j`-th value) establishes the monotone witness `Iwit a iA (j+1)` — "`a`'s
  creation index is consumed and every live cursor for `a` is `≥ j+1`" —
  which every later step preserves (appends read FRESH `xs` indices, and
  `xs`-honesty says `a` can never be appended again), and which blocks any
  second emission of `⟨a, b⟩` (that would need cursor `j` again). Existence:
  a step scheduling value `iA` forces creation (the pull reaches list index
  `iA`, or `xs` is discovered done — and by contiguity everything, `a`
  included, was already created); then the CURSOR CLIMB: while `a`'s cursor
  is `≤ j`, removal is impossible (fiber contiguity — pulls at those cursors
  emit), `a`'s position in the live list is nonincreasing (removals shift
  down, appends go after), hence stabilizes; the scheduler certificate hits
  the stable position, and a hit at cursor `c` emits `⟨a, c-th value⟩` and
  increments — so the cursor passes every `c ≤ j`, and the increment at `j`
  emits `⟨a, b⟩`. Throughout, the per-call fuel `origI + len + 2` is shown
  sufficient (each retry permanently removes a fiber; a filled pull ends the
  call by emitting from a FRESH, nonempty fiber), so the fuel-0 branch — the
  hang marker — is unreachable.
-/
import Azurite.ExhaustiveGenerator.ExhaustiveDepPairsSim

namespace Azurite

namespace ExhaustiveGenerator

namespace DepPairsSim

variable {X : Type*} {B : X → Type*}

/-! ### The run: step-indexed states and emissions -/

/-- The per-call fuel (the simulator's `slack := 0` formula). -/
def stepFuel (st : State X) (origI : ℕ) : ℕ :=
  origI + st.live.length + 2

/-- The machine state BEFORE step `n`, frozen once done (Rust:
`if self.done { return None }`). -/
def runState (xs : ℕ → Option X) (ysGen : (x : X) → ℕ → Option (B x))
    (s : ℕ → ℕ) : ℕ → State X
  | 0 => .init
  | n + 1 =>
    let st := runState xs ysGen s n
    if st.done then st else (next xs ysGen (stepFuel st (s n)) (s n) st).2

/-- The value emitted at step `n` (`none` at and after the end). -/
def emitAt (xs : ℕ → Option X) (ysGen : (x : X) → ℕ → Option (B x))
    (s : ℕ → ℕ) (n : ℕ) : Option ((x : X) × B x) :=
  let st := runState xs ysGen s n
  if st.done then none else (next xs ysGen (stepFuel st (s n)) (s n) st).1

/-! ### List helpers -/

/-- Setting an index to the value it already holds is the identity. -/
theorem set_of_getElem? {α : Type*} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : l.set i a = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      rw [List.set_cons_zero, Option.some.inj h]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [List.set_cons_succ, ih h]

/-- A `filterMap` whose function is `some` on every element keeps the
length. -/
theorem length_filterMap_of_forall_isSome {α β : Type*} {f : α → Option β}
    {l : List α} (h : ∀ a ∈ l, (f a).isSome) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h hd (by simp))
    rw [List.filterMap_cons_some hb, List.length_cons, List.length_cons,
      ih (fun a ha => h a (List.mem_cons_of_mem hd ha))]

/-! ### The pull specification -/

theorem pull_succ_some {xs : ℕ → Option X} {st : State X} {x : X}
    (hx : xs st.xsCursor = some x) (c : ℕ) :
    pull xs (c + 1) st
      = pull xs c ⟨st.live ++ [(x, 0)], st.xsCursor + 1, st.xsDone, st.done⟩ := by
  rw [pull, hx]

theorem pull_succ_none {xs : ℕ → Option X} {st : State X}
    (hx : xs st.xsCursor = none) (c : ℕ) :
    pull xs (c + 1) st = st := by
  rw [pull, hx]

/-- What `pull` does, exactly: advances the cursor by some `d ≤ count`,
appends the (all-`some`) reads as fresh fibers, touches nothing else, and
stops early only at a `none`. -/
theorem pull_spec (xs : ℕ → Option X) (count : ℕ) (st : State X) :
    ∃ d ≤ count,
      (pull xs count st).xsCursor = st.xsCursor + d ∧
      (pull xs count st).live = st.live
        ++ (List.range' st.xsCursor d).filterMap
            (fun k => (xs k).map fun x => ((x, 0) : X × ℕ)) ∧
      (pull xs count st).xsDone = st.xsDone ∧
      (pull xs count st).done = st.done ∧
      (∀ k, st.xsCursor ≤ k → k < st.xsCursor + d → xs k ≠ none) ∧
      (d = count ∨ xs (st.xsCursor + d) = none) := by
  induction count generalizing st with
  | zero =>
    exact ⟨0, le_refl 0, rfl, by simp [pull], rfl, rfl,
      fun k h1 h2 => absurd h2 (by omega), Or.inl rfl⟩
  | succ c ih =>
    cases hx : xs st.xsCursor with
    | none =>
      rw [pull_succ_none hx]
      exact ⟨0, Nat.zero_le _, rfl, by simp, rfl, rfl,
        fun k h1 h2 => absurd h2 (by omega), Or.inr (by simpa using hx)⟩
    | some x =>
      rw [pull_succ_some hx c]
      obtain ⟨d, hd, hcur, hlive, hxd, hdone, hsome, hlast⟩ :=
        ih ⟨st.live ++ [(x, 0)], st.xsCursor + 1, st.xsDone, st.done⟩
      have hc' : (⟨st.live ++ [(x, 0)], st.xsCursor + 1, st.xsDone, st.done⟩ :
          State X).xsCursor = st.xsCursor + 1 := rfl
      rw [hc'] at hcur hsome hlast
      refine ⟨d + 1, by omega, by rw [hcur]; omega, ?_, hxd, hdone, ?_, ?_⟩
      · rw [hlive]
        rw [List.range'_succ, List.filterMap_cons_some
          (f := fun k => (xs k).map fun x => ((x, 0) : X × ℕ))
          (show ((xs st.xsCursor).map fun x => ((x, 0) : X × ℕ)) = some (x, 0) by
            rw [hx]; rfl)]
        simp
      · intro k h1 h2
        rcases h1.eq_or_lt with heq | hlt
        · rw [← heq, hx]; exact Option.some_ne_none x
        · exact hsome k hlt (by omega)
      · rcases hlast with heq | hnone
        · exact Or.inl (by omega)
        · refine Or.inr ?_
          rw [show st.xsCursor + (d + 1) = st.xsCursor + 1 + d from by omega]
          exact hnone

/-! ### Phase mini-lemmas -/

theorem pullPhase_live_prefix (xs : ℕ → Option X) (origI : ℕ) (st : State X) :
    ∃ tail, (pullPhase xs origI st).live = st.live ++ tail := by
  unfold pullPhase
  split_ifs with h1 h2
  · exact ⟨[], by simp⟩
  · obtain ⟨d, -, -, hlive, -⟩ := pull_spec xs (origI - st.live.length + 1) st
    exact ⟨_, hlive⟩
  · exact ⟨[], by simp⟩

theorem pullPhase_xsCursor_le (xs : ℕ → Option X) (origI : ℕ) (st : State X) :
    st.xsCursor ≤ (pullPhase xs origI st).xsCursor := by
  unfold pullPhase
  split_ifs with h1 h2
  · exact le_refl _
  · obtain ⟨d, -, hcur, -⟩ := pull_spec xs (origI - st.live.length + 1) st
    omega
  · exact le_refl _

theorem pullPhase_xsDone (xs : ℕ → Option X) (origI : ℕ) (st : State X) :
    (pullPhase xs origI st).xsDone = st.xsDone := by
  unfold pullPhase
  split_ifs with h1 h2
  · rfl
  · obtain ⟨d, -, -, -, hxd, -⟩ := pull_spec xs (origI - st.live.length + 1) st
    exact hxd
  · rfl

theorem pullPhase_done (xs : ℕ → Option X) (origI : ℕ) (st : State X) :
    (pullPhase xs origI st).done = st.done := by
  unfold pullPhase
  split_ifs with h1 h2
  · rfl
  · obtain ⟨d, -, -, -, -, hdone, -⟩ := pull_spec xs (origI - st.live.length + 1) st
    exact hdone
  · rfl

theorem discover_live (origI : ℕ) (st : State X) :
    (discover origI st).live = st.live := by
  unfold discover; split_ifs <;> rfl

theorem discover_xsCursor (origI : ℕ) (st : State X) :
    (discover origI st).xsCursor = st.xsCursor := by
  unfold discover; split_ifs <;> rfl

theorem discover_done (origI : ℕ) (st : State X) :
    (discover origI st).done = st.done := by
  unfold discover; split_ifs <;> rfl

theorem discover_xsDone_latch (origI : ℕ) (st : State X) (h : st.xsDone = true) :
    (discover origI st).xsDone = true := by
  unfold discover; split_ifs with hc
  · rfl
  · exact h

/-- If discovery leaves `xsDone` false, the list was already long enough. -/
theorem discover_not_xsDone (origI : ℕ) (st : State X)
    (h : (discover origI st).xsDone = false) :
    st.xsDone = false ∧ origI < st.live.length := by
  by_cases hc : st.xsDone = false ∧ st.live.length ≤ origI
  · rw [discover, if_pos hc] at h
    exact absurd h (by simp)
  · rw [discover, if_neg hc] at h
    refine ⟨h, ?_⟩
    by_contra hlt
    exact hc ⟨h, by omega⟩

/-- The pulled index is in range once the (post-discovery) list is
nonempty: modular when `xsDone`, and below the length otherwise. -/
theorem targetIdx_lt (origI : ℕ) (st : State X)
    (hlen : (discover origI st).live.length ≠ 0) :
    targetIdx origI (discover origI st) < (discover origI st).live.length := by
  unfold targetIdx
  split_ifs with h
  · exact Nat.mod_lt _ (by omega)
  · obtain ⟨-, hlt⟩ := discover_not_xsDone origI st (by simpa using h)
    rw [discover_live]
    exact hlt

/-! ### Well-formedness -/

/-- The machine well-formedness invariant: live values are (in order) a
sublist of the `xs` values read so far — which yields at-most-one-entry-per-
value whenever `xs` is duplicate-free — and the `xsDone` flag is honest
(`xs` really ends at the cursor). -/
structure WF (xs : ℕ → Option X) (st : State X) : Prop where
  sub : List.Sublist (st.live.map Prod.fst) ((List.range st.xsCursor).filterMap xs)
  xsdone_none : st.xsDone = true → xs st.xsCursor = none

theorem WF.init (xs : ℕ → Option X) : WF xs (State.init (X := X)) :=
  ⟨by simp [State.init], by simp [State.init]⟩

/-- Live length is bounded by the number of `xs` reads. -/
theorem WF.length_le {xs : ℕ → Option X} {st : State X} (h : WF xs st) :
    st.live.length ≤ st.xsCursor := by
  have h1 := h.sub.length_le
  rw [List.length_map] at h1
  exact h1.trans ((List.length_filterMap_le _ _).trans (by rw [List.length_range]))

/-- The tail appended by a pull, projected to values, is the fresh window of
`xs` reads. -/
theorem pullTail_map_fst (xs : ℕ → Option X) (c d : ℕ) :
    ((List.range' c d).filterMap (fun k => (xs k).map fun x => ((x, 0) : X × ℕ))).map
        Prod.fst
      = (List.range' c d).filterMap xs := by
  rw [List.map_filterMap]
  congr 1
  funext k
  cases xs k <;> rfl

/-- Range split: reads so far plus the fresh window. -/
theorem filterMap_range_add (xs : ℕ → Option X) (c d : ℕ) :
    (List.range (c + d)).filterMap xs
      = (List.range c).filterMap xs ++ (List.range' c d).filterMap xs := by
  rw [← List.filterMap_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range',
    ← List.range'_append_1 (s := 0) (m := c) (n := d)]
  norm_num

/-- `pull` preserves well-formedness (appended values are exactly the fresh
reads). -/
theorem WF.pull {xs : ℕ → Option X} {st : State X} (h : WF xs st) (count : ℕ) :
    WF xs (DepPairsSim.pull xs count st) := by
  obtain ⟨d, -, hcur, hlive, hxd, -, hsome, -⟩ := pull_spec xs count st
  constructor
  · rw [hlive, hcur, List.map_append, pullTail_map_fst, filterMap_range_add]
    exact h.sub.append (List.Sublist.refl _)
  · intro hxd'
    rw [hxd] at hxd'
    -- A set flag means the old cursor was `none`, so the all-`some` window
    -- is empty and the cursor has not moved.
    have hnone := h.xsdone_none hxd'
    have hd0 : d = 0 := by
      by_contra hne
      exact hsome st.xsCursor (le_refl _) (by omega) hnone
    rw [hcur, hd0]
    exact hnone

/-- `pullPhase` preserves well-formedness. -/
theorem WF.pullPhase {xs : ℕ → Option X} {st : State X} (h : WF xs st) (origI : ℕ) :
    WF xs (DepPairsSim.pullPhase xs origI st) := by
  unfold DepPairsSim.pullPhase
  split_ifs with h1 h2
  · exact h
  · exact h.pull _
  · exact h

/-- The key discovery fact: if the pull phase left the list at length
`≤ origI` with `xsDone` still false, the pull hit a `none` (the requested
window was longer than what arrived). -/
theorem pullPhase_short_none {xs : ℕ → Option X} {st : State X} (origI : ℕ)
    (hxd : (pullPhase xs origI st).xsDone = false)
    (hshort : (pullPhase xs origI st).live.length ≤ origI) :
    xs (pullPhase xs origI st).xsCursor = none := by
  unfold pullPhase at *
  split_ifs at * with h1 h2
  · simp_all
  · obtain ⟨d, hd, hcur, hlive, -, -, hsome, hlast⟩ :=
      pull_spec xs (origI - st.live.length + 1) st
    rw [hlive, List.length_append] at hshort
    have hlen : ((List.range' st.xsCursor d).filterMap
        (fun k => (xs k).map fun x => ((x, 0) : X × ℕ))).length = d := by
      rw [length_filterMap_of_forall_isSome, List.length_range']
      intro k hk
      rw [List.mem_range'_1] at hk
      cases hxk : xs k with
      | none => exact absurd hxk (hsome k hk.1 hk.2)
      | some x => rfl
    rw [hlen] at hshort
    -- The pull fell short of the requested `origI - len + 1`, so it ended
    -- at a `none`.
    have hdlt : d ≠ origI - st.live.length + 1 := by omega
    rcases hlast with rfl | hnone
    · exact absurd rfl hdlt
    · rw [hcur]
      exact hnone
  · omega

/-- Both phases preserve well-formedness (`discover`'s honesty obligation is
exactly `pullPhase_short_none`). -/
theorem WF.phases {xs : ℕ → Option X} {st : State X} (h : WF xs st) (origI : ℕ) :
    WF xs (DepPairsSim.discover origI (DepPairsSim.pullPhase xs origI st)) := by
  have h1 := h.pullPhase (origI := origI)
  unfold DepPairsSim.discover
  split_ifs with hc
  · exact ⟨h1.sub, fun _ => pullPhase_short_none origI hc.1 hc.2⟩
  · exact h1

/-! ### The fuel account

Each retry loop iteration beyond the last permanently removes a fiber, and
(before `xs` is done) one append batch can intervene — after which the
pulled entry is FRESH, hence (nonempty fibers) emits and ends the call. The
lower bound `fuelLB` tracks exactly this: one unit per removable fiber, one
for the final action, and `origI + 1` while an append batch is possible. -/

/-- The loop-fuel lower bound making the hang branch unreachable. -/
def fuelLB (st : State X) (origI : ℕ) : ℕ :=
  st.live.length + 1 + (if st.xsDone then 0 else origI + 1)

theorem fuelLB_pos (st : State X) (origI : ℕ) : 0 < fuelLB st origI := by
  unfold fuelLB; split_ifs <;> omega

theorem stepFuel_ge (st : State X) (origI : ℕ) : fuelLB st origI ≤ stepFuel st origI := by
  unfold fuelLB stepFuel; split_ifs <;> omega

/-- **Removal-branch trichotomy.** In a retry (the pulled entry is exhausted)
the phases fall in exactly one of three shapes: `xs` was already done (no
append, flag persists); no append was needed (`origI` inside the list); or
the discovery fired (`xs` ended, list at most `origI` long). The fourth
combination — a pull that reached `origI` with `xsDone` still false — cannot
retry: the pulled entry would be fresh (cursor `0`), and nonempty fibers
make it emit. -/
theorem phases_trichotomy {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hne : ∀ x, ysGen x 0 ≠ none) {st : State X} {origI : ℕ} {x : X} {j : ℕ}
    (h2 : (discover origI (pullPhase xs origI st)).live[
        targetIdx origI (discover origI (pullPhase xs origI st))]? = some (x, j))
    (hy : ysGen x j = none) :
    (st.xsDone = true
        ∧ (discover origI (pullPhase xs origI st)).live.length = st.live.length
        ∧ (discover origI (pullPhase xs origI st)).xsDone = true)
    ∨ ((discover origI (pullPhase xs origI st)).xsDone = false
        ∧ (discover origI (pullPhase xs origI st)).live.length = st.live.length
        ∧ origI < st.live.length ∧ st.xsDone = false)
    ∨ ((discover origI (pullPhase xs origI st)).xsDone = true
        ∧ (discover origI (pullPhase xs origI st)).live.length ≤ origI
        ∧ st.xsDone = false) := by
  cases hxd : st.xsDone with
  | true =>
    -- No pull, no discovery change; everything persists.
    have hpp : pullPhase xs origI st = st := by
      unfold pullPhase; rw [if_pos hxd]
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · rw [discover_live, hpp]
    · rw [hpp]; exact discover_xsDone_latch origI st hxd
  | false =>
    by_cases hlen : st.live.length ≤ origI
    · -- A pull fired. Split on whether discovery followed.
      cases hxd2 : (discover origI (pullPhase xs origI st)).xsDone with
      | true =>
        refine Or.inr (Or.inr ⟨rfl, ?_, rfl⟩)
        -- Discovery fired (the pre-discover flag was false), so its
        -- condition held: the list stayed at length `≤ origI`.
        by_contra hlong
        have hxd1 : (pullPhase xs origI st).xsDone = false := by
          rw [pullPhase_xsDone]; exact hxd
        rw [discover_live] at hlong
        unfold discover at hxd2
        rw [if_neg (fun hc => hlong (by omega))] at hxd2
        rw [hxd1] at hxd2
        exact Bool.false_ne_true hxd2
      | false =>
        -- Impossible: the pulled entry at `origI` is fresh, hence emits.
        exfalso
        obtain ⟨hxd1, hlt1⟩ := discover_not_xsDone origI _ hxd2
        have hidx : targetIdx origI (discover origI (pullPhase xs origI st)) = origI := by
          unfold targetIdx
          rw [if_neg (by rw [hxd2]; exact Bool.false_ne_true)]
        rw [hidx, discover_live] at h2
        -- The entry sits in the appended tail: its cursor is `0`.
        unfold pullPhase at h2
        rw [if_neg (by rw [hxd]; exact Bool.false_ne_true), if_pos hlen] at h2
        obtain ⟨d, -, -, hlive, -⟩ := pull_spec xs (origI - st.live.length + 1) st
        rw [hlive, List.getElem?_append_right hlen] at h2
        have hmem := List.mem_of_getElem? h2
        rw [List.mem_filterMap] at hmem
        obtain ⟨k, -, hk⟩ := hmem
        cases hxk : xs k with
        | none => rw [hxk] at hk; simp at hk
        | some x' =>
          rw [hxk] at hk
          have : x' = x ∧ 0 = j := by
            have := Option.some.inj hk
            exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
          rw [← this.2] at hy
          exact hne x (this.1 ▸ hy)
    · -- No pull was needed; nothing changes.
      have hpp : pullPhase xs origI st = st := by
        unfold pullPhase
        rw [if_neg (by rw [hxd]; exact Bool.false_ne_true), if_neg hlen]
      have hdis : discover origI (pullPhase xs origI st) = st := by
        rw [hpp]
        unfold discover
        rw [if_neg (fun hc => hlen hc.2)]
      refine Or.inr (Or.inl ⟨?_, ?_, by omega, rfl⟩)
      · rw [hdis]; exact hxd
      · rw [hdis]

/-- The recursion-fuel account: a removal branch grants the recursive call
its own lower bound. Stated in field form (the caller's `fuelLB st₃ origI`
unfolds to it definitionally). -/
theorem fuelLB_le_of_erase {st st₂ : State X} {origI fuel i : ℕ}
    (hfuel : fuelLB st origI ≤ fuel + 1) (hi : i < st₂.live.length)
    (hcases :
      (st.xsDone = true ∧ st₂.live.length = st.live.length ∧ st₂.xsDone = true)
      ∨ (st₂.xsDone = false ∧ st₂.live.length = st.live.length
          ∧ origI < st.live.length ∧ st.xsDone = false)
      ∨ (st₂.xsDone = true ∧ st₂.live.length ≤ origI ∧ st.xsDone = false)) :
    (st₂.live.eraseIdx i).length + 1 + (if st₂.xsDone then 0 else origI + 1) ≤ fuel := by
  rw [List.length_eraseIdx_of_lt hi]
  unfold fuelLB at hfuel
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · rw [h1, if_pos rfl] at hfuel
    rw [h3, if_pos rfl]
    omega
  · rw [h4, if_neg (by simp)] at hfuel
    rw [h1, if_neg (by simp)]
    omega
  · rw [h3, if_neg (by simp)] at hfuel
    rw [h1, if_pos rfl]
    omega

/-! ### Per-call monotonicity (fuel induction over the retry loop) -/

/-- Across one `next()` call: the `xs` cursor never retreats and the two
flags only latch. Unconditional (the fuel-0 branch also satisfies it). -/
theorem next_mono {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)} :
    ∀ (fuel origI : ℕ) (st : State X),
      st.xsCursor ≤ (next xs ysGen fuel origI st).2.xsCursor
        ∧ (st.xsDone = true → (next xs ysGen fuel origI st).2.xsDone = true)
        ∧ (st.done = true → (next xs ysGen fuel origI st).2.done = true)
  | 0, origI, st => ⟨le_refl _, fun h => h, fun _ => rfl⟩
  | fuel + 1, origI, st => by
    simp only [next]
    have hpc := pullPhase_xsCursor_le xs origI st
    have hpd := pullPhase_xsDone xs origI st
    have hpdn := pullPhase_done xs origI st
    have hdc := discover_xsCursor origI (pullPhase xs origI st)
    have hdd := discover_done origI (pullPhase xs origI st)
    by_cases hlen0 : (pullPhase xs origI st).live.length = 0
    · rw [if_pos hlen0]
      exact ⟨hpc, fun h => by rw [hpd]; exact h, fun _ => rfl⟩
    · rw [if_neg hlen0]
      split
      · -- defensive `getElem? = none` branch
        exact ⟨by rw [hdc]; exact hpc,
          fun h => discover_xsDone_latch origI _ (by rw [hpd]; exact h),
          fun _ => rfl⟩
      · rename_i heq
        split
        · -- emit branch: only the live list changes
          exact ⟨by rw [hdc]; exact hpc,
            fun h => discover_xsDone_latch origI _ (by rw [hpd]; exact h),
            fun h => by rw [hdd, hpdn]; exact h⟩
        · -- removal branch
          rename_i hy
          split_ifs with hdone
          · exact ⟨by rw [hdc]; exact hpc,
              fun h => discover_xsDone_latch origI _ (by rw [hpd]; exact h),
              fun _ => rfl⟩
          · -- retry: chain the IH through the (cursor/flag-preserving) erase
            obtain ⟨ih1, ih2, ih3⟩ := next_mono fuel origI
              ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                  (targetIdx origI (discover origI (pullPhase xs origI st))),
                (discover origI (pullPhase xs origI st)).xsCursor,
                (discover origI (pullPhase xs origI st)).xsDone,
                (discover origI (pullPhase xs origI st)).done⟩
            exact ⟨(by rw [hdc]; exact hpc : st.xsCursor
                ≤ (discover origI (pullPhase xs origI st)).xsCursor).trans ih1,
              fun h => ih2 (discover_xsDone_latch origI _ (by rw [hpd]; exact h)),
              fun h => ih3 (by rw [hdd, hpdn]; exact h)⟩

/-! ### Per-call well-formedness -/

/-- Erasing preserves well-formedness. -/
theorem WF.erase {xs : ℕ → Option X} {st : State X} (h : WF xs st) (i : ℕ) :
    WF xs ⟨st.live.eraseIdx i, st.xsCursor, st.xsDone, st.done⟩ :=
  ⟨((st.live.eraseIdx_sublist i).map Prod.fst).trans h.sub, h.xsdone_none⟩

/-- The emitting cursor bump preserves well-formedness (the value at the
bumped index is unchanged, so the projected list is untouched). -/
theorem WF.setBump {xs : ℕ → Option X} {st : State X} (h : WF xs st) {i : ℕ}
    {x : X} {j j' : ℕ} (hent : st.live[i]? = some (x, j)) :
    WF xs ⟨st.live.set i (x, j'), st.xsCursor, st.xsDone, st.done⟩ := by
  refine ⟨?_, h.xsdone_none⟩
  have hmap : (st.live.set i (x, j')).map Prod.fst = st.live.map Prod.fst := by
    rw [List.map_set]
    exact set_of_getElem? (by rw [List.getElem?_map, hent]; rfl)
  rw [hmap]
  exact h.sub

/-- One `next()` call preserves well-formedness — unconditionally (the
fuel-out branch touches only the `done` flag). -/
theorem next_WF {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)} :
    ∀ (fuel origI : ℕ) (st : State X), WF xs st → WF xs (next xs ysGen fuel origI st).2
  | 0, _, _, h => ⟨h.sub, h.xsdone_none⟩
  | fuel + 1, origI, st, h => by
    simp only [next]
    have h₂ := h.phases (origI := origI)
    by_cases hlen0 : (pullPhase xs origI st).live.length = 0
    · rw [if_pos hlen0]
      exact ⟨(h.pullPhase origI).sub, (h.pullPhase origI).xsdone_none⟩
    · rw [if_neg hlen0]
      split
      · exact ⟨h₂.sub, h₂.xsdone_none⟩
      · rename_i heq
        split
        · exact h₂.setBump heq
        · rename_i hy
          have herase := h₂.erase
            (targetIdx origI (discover origI (pullPhase xs origI st)))
          split_ifs with hdone
          · exact ⟨herase.sub, herase.xsdone_none⟩
          · exact next_WF fuel origI _ herase

/-! ### The per-entry step lemma -/

/-- **The per-entry step lemma.** A live entry `(a, c)` at index `i` either
survives the call at an index `≤ i` (removals below shift it down, appends
land after it), or is the emitting pull — the call emits `⟨a, y⟩` with
`ysGen a c = some y` and the cursor bumps to `c + 1` in place — or its fiber
is exhausted at `c` (`ysGen a c = none`, the only way `a` can disappear). In
the first two cases the `done` flag is untouched. -/
theorem next_entry {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hne : ∀ x, ysGen x 0 ≠ none) :
    ∀ (fuel origI : ℕ) (st : State X), fuelLB st origI ≤ fuel → WF xs st →
      ∀ (a : X) (c i : ℕ), st.live[i]? = some (a, c) →
      ((∃ i' ≤ i, (next xs ysGen fuel origI st).2.live[i']? = some (a, c))
          ∧ (next xs ysGen fuel origI st).2.done = st.done)
        ∨ (∃ y, (next xs ysGen fuel origI st).1 = some ⟨a, y⟩ ∧ ysGen a c = some y
            ∧ (∃ i' ≤ i, (next xs ysGen fuel origI st).2.live[i']? = some (a, c + 1))
            ∧ (next xs ysGen fuel origI st).2.done = st.done)
        ∨ ysGen a c = none
  | 0, origI, st, hfuel, _, _, _, _, _ =>
    absurd hfuel (by have := fuelLB_pos st origI; omega)
  | fuel + 1, origI, st, hfuel, hWF, a, c, i, hent => by
    simp only [next]
    have hilt : i < st.live.length := (List.getElem?_eq_some_iff.mp hent).1
    obtain ⟨tail, htail⟩ := pullPhase_live_prefix xs origI st
    have hent₂ : (discover origI (pullPhase xs origI st)).live[i]? = some (a, c) := by
      rw [discover_live, htail, List.getElem?_append_left hilt]
      exact hent
    have hilt₂ : i < (discover origI (pullPhase xs origI st)).live.length :=
      (List.getElem?_eq_some_iff.mp hent₂).1
    have hlen0 : ¬(pullPhase xs origI st).live.length = 0 := by
      rw [htail, List.length_append]
      omega
    rw [if_neg hlen0]
    have hWF₂ := hWF.phases (origI := origI)
    have hdd := discover_done origI (pullPhase xs origI st)
    have hpdn := pullPhase_done xs origI st
    have htlt : targetIdx origI (discover origI (pullPhase xs origI st))
        < (discover origI (pullPhase xs origI st)).live.length :=
      targetIdx_lt origI (pullPhase xs origI st) (by omega)
    split
    · -- defensive branch: the target is in range, so its read is `some`
      rename_i heq0
      rw [List.getElem?_eq_getElem htlt] at heq0
      exact absurd heq0 (Option.some_ne_none _)
    · rename_i heq
      by_cases hti : targetIdx origI (discover origI (pullPhase xs origI st)) = i
      · -- the pulled entry IS ours
        rw [hti] at heq
        have hxa := Option.some.inj (heq.symm.trans hent₂)
        have hx : _ = a := congrArg Prod.fst hxa
        have hj : _ = c := congrArg Prod.snd hxa
        subst hx hj
        split
        · -- emit: branch 2
          rename_i y hy
          refine Or.inr (Or.inl ⟨y, rfl, hy, ⟨i, le_refl i, ?_⟩, by rw [hdd, hpdn]⟩)
          rw [hti, List.getElem?_set_self hilt₂]
        · -- exhausted: branch 3, independent of the retry outcome
          rename_i hy
          exact Or.inr (Or.inr hy)
      · -- the pulled entry is another fiber
        split
        · -- emit elsewhere: our entry is untouched
          rename_i y hy
          refine Or.inl ⟨⟨i, le_refl i, ?_⟩, by rw [hdd, hpdn]⟩
          rw [List.getElem?_set_ne hti]
          exact hent₂
        · -- removal elsewhere: our entry shifts down by at most one, retry
          rename_i hy
          set t := targetIdx origI (discover origI (pullPhase xs origI st)) with hts
          -- our entry inside the erased list
          have hent₃ : ((discover origI (pullPhase xs origI st)).live.eraseIdx t)[
              if t < i then i - 1 else i]? = some (a, c) := by
            rw [List.getElem?_eraseIdx]
            by_cases htc : t < i
            · rw [if_pos htc, if_neg (by omega)]
              rw [show (i - 1) + 1 = i from by omega]
              exact hent₂
            · rw [if_neg htc, if_pos (by omega)]
              exact hent₂
          have hne3 : ¬((discover origI (pullPhase xs origI st)).live.eraseIdx t).isEmpty
              = true := by
            have hlt := (List.getElem?_eq_some_iff.mp hent₃).1
            intro hemp
            rw [List.isEmpty_iff] at hemp
            rw [hemp] at hlt
            simp at hlt
          rw [if_neg (fun hcond => hne3 hcond.2)]
          -- recurse on the erased state
          have hrec := next_entry hne fuel origI
            ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx t,
              (discover origI (pullPhase xs origI st)).xsCursor,
              (discover origI (pullPhase xs origI st)).xsDone,
              (discover origI (pullPhase xs origI st)).done⟩
            (fuelLB_le_of_erase hfuel htlt (phases_trichotomy hne (hts ▸ heq) hy))
            (hWF₂.erase t) a c (if t < i then i - 1 else i) hent₃
          have hle : (if t < i then i - 1 else i) ≤ i := by split <;> omega
          rcases hrec with ⟨⟨i', hi', hent'⟩, hdone'⟩ | ⟨y, hem, hyc, ⟨i', hi', hent'⟩, hdone'⟩ | h3
          · exact Or.inl ⟨⟨i', by omega, hent'⟩, by rw [hdone', hdd, hpdn]⟩
          · exact Or.inr (Or.inl ⟨y, hem, hyc, ⟨i', by omega, hent'⟩,
              by rw [hdone', hdd, hpdn]⟩)
          · exact Or.inr (Or.inr h3)

/-! ### Creation -/

/-- Contiguity closes upward: a `none` read stays `none`. -/
theorem contig_closure {xs : ℕ → Option X}
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none) :
    ∀ {c k : ℕ}, c ≤ k → xs c = none → xs k = none := by
  intro c k hck
  induction hck with
  | refl => exact fun h => h
  | step _ ih => exact fun h => hcontig _ (ih h)

/-- After the two phases, either the cursor has passed `origI` or `xs` is
known done. -/
theorem phases_created {xs : ℕ → Option X} (origI : ℕ) (st : State X) (hWF : WF xs st) :
    origI < (discover origI (pullPhase xs origI st)).xsCursor
      ∨ (discover origI (pullPhase xs origI st)).xsDone = true := by
  by_cases hxd : st.xsDone = true
  · exact Or.inr (discover_xsDone_latch origI _
      (by rw [pullPhase_xsDone]; exact hxd))
  · by_cases hlen : st.live.length ≤ origI
    · by_cases hlen1 : (pullPhase xs origI st).live.length ≤ origI
      · refine Or.inr ?_
        unfold discover
        rw [if_pos ⟨by rw [pullPhase_xsDone]; simpa using hxd, hlen1⟩]
      · refine Or.inl ?_
        rw [discover_xsCursor]
        have := (hWF.pullPhase origI).length_le
        omega
    · refine Or.inl ?_
      rw [discover_xsCursor]
      have h1 := hWF.length_le
      have h2 := pullPhase_xsCursor_le xs origI st
      omega

/-- **Creation.** A call scheduling value `origI` — an index whose `xs` read
exists — pushes the cursor past `origI`: the pull reaches list index
`origI`, or `xs`-done is discovered, which by contiguity means index `origI`
was already read. -/
theorem next_created {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none) {origI : ℕ}
    (hiA : xs origI ≠ none) :
    ∀ (fuel : ℕ) (st : State X), fuelLB st origI ≤ fuel → WF xs st →
      origI < (next xs ysGen fuel origI st).2.xsCursor := by
  intro fuel st hfuel hWF
  -- Established at the post-phase state, monotone thereafter.
  have hkey : origI < (discover origI (pullPhase xs origI st)).xsCursor := by
    rcases phases_created origI st hWF with h | h
    · exact h
    · by_contra hle
      exact hiA (contig_closure hcontig (by omega)
        ((hWF.phases origI).xsdone_none h))
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
    ⟨fuel - 1, by have := fuelLB_pos st origI; omega⟩
  simp only [next]
  have hc1 : (pullPhase xs origI st).xsCursor
      = (discover origI (pullPhase xs origI st)).xsCursor :=
    (discover_xsCursor origI _).symm
  by_cases hlen0 : (pullPhase xs origI st).live.length = 0
  · rw [if_pos hlen0]
    show origI < (pullPhase xs origI st).xsCursor
    omega
  · rw [if_neg hlen0]
    split
    · exact hkey
    · rename_i heq
      split
      · exact hkey
      · rename_i hy
        split_ifs with hdone
        · exact hkey
        · exact hkey.trans_le ((next_mono f origI
            ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                (targetIdx origI (discover origI (pullPhase xs origI st))),
              (discover origI (pullPhase xs origI st)).xsCursor,
              (discover origI (pullPhase xs origI st)).xsDone,
              (discover origI (pullPhase xs origI st)).done⟩).1)

/-- **The hit lemma.** A call whose scheduler value is exactly the index of
a live entry pulls THAT entry first: it either emits the entry's current
fiber value (bumping the cursor in place) or discovers the fiber exhausted.
No induction — the retry loop is never entered. -/
theorem next_hit {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    {st : State X} {origI : ℕ} {a : X} {c : ℕ}
    (hent : st.live[origI]? = some (a, c)) (fuel : ℕ) :
    (∃ y, (next xs ysGen (fuel + 1) origI st).1 = some ⟨a, y⟩ ∧ ysGen a c = some y
        ∧ (next xs ysGen (fuel + 1) origI st).2.live[origI]? = some (a, c + 1)
        ∧ (next xs ysGen (fuel + 1) origI st).2.done = st.done)
      ∨ ysGen a c = none := by
  have hilt : origI < st.live.length := (List.getElem?_eq_some_iff.mp hent).1
  -- Both phases are no-ops: the list is already long enough.
  have hpp : pullPhase xs origI st = st := by
    unfold pullPhase
    split_ifs with h1 h2
    · rfl
    · omega
    · rfl
  have hdis : discover origI (pullPhase xs origI st) = st := by
    rw [hpp]
    unfold discover
    rw [if_neg (fun hc => by omega)]
  have htgt : targetIdx origI (discover origI (pullPhase xs origI st)) = origI := by
    rw [hdis]
    unfold targetIdx
    split_ifs with h
    · exact Nat.mod_eq_of_lt hilt
    · rfl
  simp only [next]
  rw [if_neg (by rw [hpp]; omega)]
  split
  · rename_i heq0
    rw [htgt, hdis, hent] at heq0
    exact absurd heq0 (Option.some_ne_none _)
  · rename_i heq
    rw [htgt, hdis, hent] at heq
    have hxa := Option.some.inj heq
    have hx : a = _ := congrArg Prod.fst hxa
    have hj : c = _ := congrArg Prod.snd hxa
    subst hx hj
    split
    · rename_i y hy
      refine Or.inl ⟨y, rfl, hy, ?_, by rw [discover_done, pullPhase_done]⟩
      rw [htgt, hdis, List.getElem?_set_self hilt]
    · rename_i hy
      exact Or.inr hy

/-! ### The uniqueness witness -/

/-- The monotone uniqueness witness for value `a` (with `xs`-index `iA`):
`a` has been created, and every live cursor for `a` is at least `c`. Once an
emission establishes it, every later step preserves it, because appends read
only FRESH `xs` indices — `a` can never be appended again. -/
def Iwit (_xs : ℕ → Option X) (a : X) (iA c : ℕ) (st : State X) : Prop :=
  iA < st.xsCursor ∧ ∀ e ∈ st.live, e.1 = a → c ≤ e.2

theorem Iwit.pull {xs : ℕ → Option X} {a : X} {iA c : ℕ} {st : State X}
    (h : Iwit xs a iA c st) (huniq : ∀ k, xs k = some a → k = iA) (count : ℕ) :
    Iwit xs a iA c (pull xs count st) := by
  obtain ⟨d, -, hcur, hlive, -⟩ := pull_spec xs count st
  refine ⟨by have := h.1; omega, ?_⟩
  intro e he hea
  rw [hlive, List.mem_append] at he
  rcases he with he | he
  · exact h.2 e he hea
  · exfalso
    rw [List.mem_filterMap] at he
    obtain ⟨k, hk, hke⟩ := he
    rw [List.mem_range'_1] at hk
    cases hxk : xs k with
    | none => rw [hxk] at hke; simp at hke
    | some x' =>
      rw [hxk] at hke
      have hx' : x' = e.1 := congrArg Prod.fst (Option.some.inj hke)
      have hkA : k = iA := huniq k (by rw [hxk, hx', hea])
      have := h.1
      omega

theorem Iwit.phases {xs : ℕ → Option X} {a : X} {iA c : ℕ} {st : State X}
    (h : Iwit xs a iA c st) (huniq : ∀ k, xs k = some a → k = iA) (origI : ℕ) :
    Iwit xs a iA c (discover origI (pullPhase xs origI st)) := by
  have h1 : Iwit xs a iA c (pullPhase xs origI st) := by
    unfold pullPhase
    split_ifs with h1 h2
    · exact h
    · exact h.pull huniq _
    · exact h
  exact ⟨by rw [discover_xsCursor]; exact h1.1,
    fun e he hea => h1.2 e (by rw [discover_live] at he; exact he) hea⟩

theorem Iwit.erase {xs : ℕ → Option X} {a : X} {iA c : ℕ} {st : State X}
    (h : Iwit xs a iA c st) (t : ℕ) :
    Iwit xs a iA c ⟨st.live.eraseIdx t, st.xsCursor, st.xsDone, st.done⟩ :=
  ⟨h.1, fun e he hea => h.2 e ((st.live.eraseIdx_sublist t).subset he) hea⟩

/-- One `next()` call preserves the witness (unconditionally — appends read
fresh indices, emissions only raise cursors, removals only shrink). -/
theorem next_Iwit {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    {a : X} {iA c : ℕ} (huniq : ∀ k, xs k = some a → k = iA) :
    ∀ (fuel origI : ℕ) (st : State X), Iwit xs a iA c st →
      Iwit xs a iA c (next xs ysGen fuel origI st).2
  | 0, _, st, h => ⟨h.1, h.2⟩
  | fuel + 1, origI, st, h => by
    simp only [next]
    have h₂ := h.phases huniq origI
    have h₁ : Iwit xs a iA c (pullPhase xs origI st) := by
      unfold pullPhase
      split_ifs with hh1 hh2
      · exact h
      · exact h.pull huniq _
      · exact h
    by_cases hlen0 : (pullPhase xs origI st).live.length = 0
    · rw [if_pos hlen0]
      exact ⟨h₁.1, h₁.2⟩
    · rw [if_neg hlen0]
      split
      · exact ⟨h₂.1, h₂.2⟩
      · rename_i heq
        split
        · -- emit: the bumped entry only raises its cursor
          rename_i y hy
          refine ⟨h₂.1, ?_⟩
          intro e he hea
          rcases List.mem_or_eq_of_mem_set he with he' | rfl
          · exact h₂.2 e he' hea
          · have hold := h₂.2 _ (List.mem_of_getElem? heq) hea
            omega
        · rename_i hy
          have h₃ := h₂.erase
            (targetIdx origI (discover origI (pullPhase xs origI st)))
          split_ifs with hdone
          · exact ⟨h₃.1, h₃.2⟩
          · exact next_Iwit huniq fuel origI _ h₃

/-! ### Honest reads and per-value index uniqueness -/

/-- Honest (injective-on-`some`) reads are duplicate-free. -/
theorem nodup_reads {xs : ℕ → Option X}
    (hinj : ∀ k k' (v : X), xs k = some v → xs k' = some v → k = k') (c : ℕ) :
    ((List.range c).filterMap xs).Nodup :=
  List.Nodup.filterMap
    (fun k k' v hv hv' => hinj k k' v (Option.mem_def.mp hv) (Option.mem_def.mp hv'))
    List.nodup_range

/-- At most one live entry carries a given value (index form). -/
theorem WF.fst_index_inj {xs : ℕ → Option X} {st : State X} (hWF : WF xs st)
    (hinj : ∀ k k' (v : X), xs k = some v → xs k' = some v → k = k')
    {i i' : ℕ} {a : X} {u v : ℕ}
    (h1 : st.live[i]? = some (a, u)) (h2 : st.live[i']? = some (a, v)) : i = i' := by
  have hnd : (st.live.map Prod.fst).Nodup := hWF.sub.nodup (nodup_reads hinj _)
  have g1 : (st.live.map Prod.fst)[i]? = some a := by
    rw [List.getElem?_map, h1]; rfl
  have g2 : (st.live.map Prod.fst)[i']? = some a := by
    rw [List.getElem?_map, h2]; rfl
  have hlt : i < (st.live.map Prod.fst).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp h1).1
  exact (List.getElem?_inj hlt hnd).mp (g1.trans g2.symm)

/-- A live value was read: its unique `xs` index is already consumed. -/
theorem WF.created_of_mem {xs : ℕ → Option X} {st : State X} (hWF : WF xs st)
    {a : X} {iA : ℕ} (huniq : ∀ k, xs k = some a → k = iA)
    {e : X × ℕ} (he : e ∈ st.live) (hea : e.1 = a) : iA < st.xsCursor := by
  have hmem : a ∈ (List.range st.xsCursor).filterMap xs := by
    refine hWF.sub.subset ?_
    rw [List.mem_map]
    exact ⟨e, he, hea⟩
  rw [List.mem_filterMap] at hmem
  obtain ⟨k, hk, hka⟩ := hmem
  rw [List.mem_range] at hk
  rw [huniq k hka] at hk
  exact hk

/-! ### The emission source (invariant-parametric) -/

/-- **Every emission has a source**: an invariant-satisfying mid-call state
`st₂` (the phase image survives `P`; each retry is an erase) with the pulled
entry at some index `t`, whose fiber value at the entry's cursor is the
emitted value, and the post-state is exactly the cursor bump. Parametric in
the invariant `P`, so Iwit-establishment, Iwit-blocking, and any future
emission analysis are corollaries — with NO fuel or nonemptiness
hypotheses (an emission that happened needs no liveness argument). -/
theorem next_emit_inv {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (P : State X → Prop)
    (hphases : ∀ (origI : ℕ) (st : State X), P st →
      P (discover origI (pullPhase xs origI st)))
    (herase : ∀ (st : State X) (t : ℕ), P st →
      P ⟨st.live.eraseIdx t, st.xsCursor, st.xsDone, st.done⟩) :
    ∀ (fuel origI : ℕ) (st : State X), P st →
      ∀ {v : (x : X) × B x}, (next xs ysGen fuel origI st).1 = some v →
      ∃ (st₂ : State X) (t j : ℕ), P st₂
        ∧ st₂.live[t]? = some (v.1, j) ∧ ysGen v.1 j = some v.2
        ∧ (next xs ysGen fuel origI st).2.live = st₂.live.set t (v.1, j + 1)
        ∧ (next xs ysGen fuel origI st).2.xsCursor = st₂.xsCursor
        ∧ (next xs ysGen fuel origI st).2.xsDone = st₂.xsDone
        ∧ (next xs ysGen fuel origI st).2.done = st₂.done
  | 0, origI, st, hP, v, hem => absurd hem (by simp [next])
  | fuel + 1, origI, st, hP, v, hem => by
    have hP₂ := hphases origI st hP
    by_cases hlen0 : (pullPhase xs origI st).live.length = 0
    · refine absurd hem ?_
      have hstep : next xs ysGen (fuel + 1) origI st
          = (none, ⟨(pullPhase xs origI st).live, (pullPhase xs origI st).xsCursor,
              (pullPhase xs origI st).xsDone, true⟩) := by
        simp only [next]
        rw [if_pos hlen0]
      rw [hstep]
      simp
    · rcases heq : (discover origI (pullPhase xs origI st)).live[
          targetIdx origI (discover origI (pullPhase xs origI st))]? with _ | ⟨x, j⟩
      · refine absurd hem ?_
        have hstep : next xs ysGen (fuel + 1) origI st
            = (none, ⟨(discover origI (pullPhase xs origI st)).live,
                (discover origI (pullPhase xs origI st)).xsCursor,
                (discover origI (pullPhase xs origI st)).xsDone, true⟩) := by
          simp only [next]
          rw [if_neg hlen0]
          simp only [heq]
        rw [hstep]
        simp
      · rcases hy : ysGen x j with _ | y
        · -- removal: rewrite to the recursive call, then recurse
          by_cases hdone : (discover origI (pullPhase xs origI st)).xsDone = true
              ∧ ((discover origI (pullPhase xs origI st)).live.eraseIdx
                  (targetIdx origI (discover origI (pullPhase xs origI st)))).isEmpty = true
          · refine absurd hem ?_
            have hstep : next xs ysGen (fuel + 1) origI st
                = (none, ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                      (targetIdx origI (discover origI (pullPhase xs origI st))),
                    (discover origI (pullPhase xs origI st)).xsCursor,
                    (discover origI (pullPhase xs origI st)).xsDone, true⟩) := by
              simp only [next]
              rw [if_neg hlen0]
              simp only [heq, hy]
              rw [if_pos hdone]
            rw [hstep]
            simp
          · have hstep : next xs ysGen (fuel + 1) origI st
                = next xs ysGen fuel origI
                    ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                        (targetIdx origI (discover origI (pullPhase xs origI st))),
                      (discover origI (pullPhase xs origI st)).xsCursor,
                      (discover origI (pullPhase xs origI st)).xsDone,
                      (discover origI (pullPhase xs origI st)).done⟩ := by
              simp only [next]
              rw [if_neg hlen0]
              simp only [heq, hy]
              rw [if_neg hdone]
            rw [hstep] at hem ⊢
            exact next_emit_inv P hphases herase fuel origI _ (herase _ _ hP₂) hem
        · -- emit: the source is the phase image
          have hstep : next xs ysGen (fuel + 1) origI st
              = (some ⟨x, y⟩,
                  ⟨(discover origI (pullPhase xs origI st)).live.set
                      (targetIdx origI (discover origI (pullPhase xs origI st))) (x, j + 1),
                    (discover origI (pullPhase xs origI st)).xsCursor,
                    (discover origI (pullPhase xs origI st)).xsDone,
                    (discover origI (pullPhase xs origI st)).done⟩) := by
            simp only [next]
            rw [if_neg hlen0]
            simp only [heq, hy]
          rw [hstep] at hem ⊢
          have hv : (⟨x, y⟩ : (x : X) × B x) = v := Option.some.inj hem
          refine ⟨discover origI (pullPhase xs origI st),
            targetIdx origI (discover origI (pullPhase xs origI st)), j, hP₂,
            ?_, ?_, ?_, rfl, rfl, rfl⟩
          · rw [heq, ← hv]
          · rw [← hv]
            exact hy
          · rw [← hv]

/-- **Establishment**: an emission of `⟨a, b⟩` (with `b` the fiber's unique
`jb`-th value) establishes the witness at `jb + 1` on the post-state. -/
theorem next_Iwit_establish {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hinj : ∀ k k' (v : X), xs k = some v → xs k' = some v → k = k')
    {a : X} {iA : ℕ} (huniq : ∀ k, xs k = some a → k = iA)
    (fuel origI : ℕ) (st : State X) (hWF : WF xs st)
    {b : B a} {jb : ℕ} (hem : (next xs ysGen fuel origI st).1 = some ⟨a, b⟩)
    (hjb : ∀ j', ysGen a j' = some b → j' = jb) :
    Iwit xs a iA (jb + 1) (next xs ysGen fuel origI st).2 := by
  obtain ⟨st₂, t, j, hP₂, hent, hyv, hlive, hcur, -, -⟩ :=
    next_emit_inv (WF xs) (fun o s h => h.phases o) (fun s t h => h.erase t)
      fuel origI st hWF hem
  have hjjb : j = jb := hjb j hyv
  subst hjjb
  constructor
  · rw [hcur]
    exact hP₂.created_of_mem huniq (List.mem_of_getElem? hent) rfl
  · intro e he hea
    rw [hlive] at he
    obtain ⟨i_e, hie⟩ := List.mem_iff_getElem?.mp he
    have hlt2 : t < st₂.live.length := (List.getElem?_eq_some_iff.mp hent).1
    rw [List.getElem?_set] at hie
    by_cases hit : t = i_e
    · rw [if_pos hit, if_pos hlt2] at hie
      have hje := Option.some.inj hie
      rw [← hje]
    · rw [if_neg hit] at hie
      -- a second live entry with value `a`: impossible by index-uniqueness
      exfalso
      have hea' : e = (a, e.2) := by
        rw [← hea]
      rw [hea'] at hie
      exact hit (hP₂.fst_index_inj hinj hent hie)

/-- **Blocking**: under the witness at `c`, an emission of `⟨a, b⟩` (with `b`
the fiber's unique `jb`-th value) forces `c ≤ jb` — the pulled cursor was at
least `c`. -/
theorem next_Iwit_block {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    {a : X} {iA c : ℕ} (huniq : ∀ k, xs k = some a → k = iA)
    (fuel origI : ℕ) (st : State X) (hIw : Iwit xs a iA c st)
    {b : B a} {jb : ℕ} (hem : (next xs ysGen fuel origI st).1 = some ⟨a, b⟩)
    (hjb : ∀ j', ysGen a j' = some b → j' = jb) :
    c ≤ jb := by
  obtain ⟨st₂, t, j, hP₂, hent, hyv, -⟩ :=
    next_emit_inv (Iwit xs a iA c) (fun o s h => h.phases huniq o)
      (fun s t h => h.erase t) fuel origI st hIw hem
  have hcj : c ≤ j := hP₂.2 _ (List.mem_of_getElem? hent) rfl
  rw [hjb j hyv] at hcj
  exact hcj

/-! ### Liveness of the uncreated phase -/

/-- If the phases advanced the cursor past `a`'s (not yet consumed) index,
`a`'s fresh entry is alive in the phase image. -/
theorem phases_creates_entry {xs : ℕ → Option X} {st : State X} {origI : ℕ}
    {a : X} {iA : ℕ} (hiA : xs iA = some a) (hlo : st.xsCursor ≤ iA)
    (hhi : iA < (discover origI (pullPhase xs origI st)).xsCursor) :
    (a, 0) ∈ (discover origI (pullPhase xs origI st)).live := by
  rw [discover_live]
  rw [discover_xsCursor] at hhi
  unfold pullPhase at hhi ⊢
  split_ifs at hhi ⊢ with h1 h2
  · omega
  · obtain ⟨d, -, hcur, hlive, -⟩ := pull_spec xs (origI - st.live.length + 1) st
    rw [hlive]
    rw [hcur] at hhi
    refine List.mem_append_right _ ?_
    rw [List.mem_filterMap]
    exact ⟨iA, by rw [List.mem_range'_1]; omega, by rw [hiA]; rfl⟩
  · omega

/-- A fresh (cursor-`0`) entry survives an exhaustion removal: the removed
entry's fiber died at its cursor, and fresh fibers are nonempty. -/
theorem mem_erase_of_ne_target {ysGen : (x : X) → ℕ → Option (B x)}
    (hne : ∀ x, ysGen x 0 ≠ none) {live : List (X × ℕ)} {t : ℕ}
    {x : X} {j : ℕ} (heq : live[t]? = some (x, j)) (hy : ysGen x j = none)
    {a : X} (hmem : (a, 0) ∈ live) :
    (a, 0) ∈ live.eraseIdx t := by
  obtain ⟨i_a, hia⟩ := List.mem_iff_getElem?.mp hmem
  have hne_idx : i_a ≠ t := by
    intro h
    rw [h, heq] at hia
    have hxa := Option.some.inj hia
    have hj0 : j = 0 := congrArg Prod.snd hxa
    exact hne x (hj0 ▸ hy)
  rw [List.mem_iff_getElem?]
  by_cases hlt : i_a < t
  · exact ⟨i_a, by rw [List.getElem?_eraseIdx, if_pos hlt]; exact hia⟩
  · refine ⟨i_a - 1, ?_⟩
    rw [List.getElem?_eraseIdx, if_neg (by omega),
      show i_a - 1 + 1 = i_a from by omega]
    exact hia

/-- **Liveness before creation**: while `a`'s index is unread, the machine
cannot finish — `xs` still has `a` in store (contiguity), and if the call
creates `a` mid-flight, its fresh nonempty fiber keeps the list alive. -/
theorem next_notDone_uncreated {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hne : ∀ x, ysGen x 0 ≠ none)
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none)
    {a : X} {iA : ℕ} (hiA : xs iA = some a) :
    ∀ (fuel origI : ℕ) (st : State X), fuelLB st origI ≤ fuel → WF xs st →
      st.done = false → st.xsCursor ≤ iA →
      (next xs ysGen fuel origI st).2.done = false
  | 0, origI, st, hfuel, _, _, _ =>
    absurd hfuel (by have := fuelLB_pos st origI; omega)
  | fuel + 1, origI, st, hfuel, hWF, hdone, hlo => by
    have hWF₂ := hWF.phases (origI := origI)
    simp only [next]
    by_cases hlen0 : (pullPhase xs origI st).live.length = 0
    · -- excluded: the pull cannot die before `a`'s index
      exfalso
      unfold pullPhase at hlen0
      split_ifs at hlen0 with h1 h2
      · -- `xsDone` before `a` was read contradicts contiguity
        have hnone := hWF.xsdone_none h1
        rw [contig_closure hcontig hlo hnone] at hiA
        exact Option.some_ne_none a hiA.symm
      · -- the pull produced nothing, so `xs` ended at the (pre-`iA`) cursor
        obtain ⟨d, hdc, hcur, hlive, -, -, hsome, hlast⟩ :=
          pull_spec xs (origI - st.live.length + 1) st
        rw [hlive, List.length_append,
          length_filterMap_of_forall_isSome (fun k hk => by
            rw [List.mem_range'_1] at hk
            cases hxk : xs k with
            | none => exact absurd hxk (hsome k hk.1 hk.2)
            | some x => rfl),
          List.length_range'] at hlen0
        have hd0 : d = 0 := by omega
        rcases hlast with heqc | hnone
        · omega
        · rw [hd0, Nat.add_zero] at hnone
          rw [contig_closure hcontig hlo hnone] at hiA
          exact Option.some_ne_none a hiA.symm
      · omega
    · rw [if_neg hlen0]
      have hlen2ne : (discover origI (pullPhase xs origI st)).live.length ≠ 0 := by
        rw [discover_live]
        exact hlen0
      have htlt := targetIdx_lt origI (pullPhase xs origI st) hlen2ne
      split
      · -- defensive: the target is in range
        rename_i heq0
        rw [List.getElem?_eq_getElem htlt] at heq0
        exact absurd heq0 (Option.some_ne_none _)
      · rename_i heq
        split
        · -- emit: `done` unchanged
          show (discover origI (pullPhase xs origI st)).done = false
          rw [discover_done, pullPhase_done]
          exact hdone
        · rename_i hy
          by_cases hcm : (discover origI (pullPhase xs origI st)).xsCursor ≤ iA
          · -- still uncreated: contiguity blocks the empty-done branch,
            -- and the recursion carries the invariant
            split_ifs with hdd
            · exfalso
              have hnone := hWF₂.xsdone_none hdd.1
              rw [contig_closure hcontig hcm hnone] at hiA
              exact Option.some_ne_none a hiA.symm
            · exact next_notDone_uncreated hne hcontig hiA fuel origI _
                (fuelLB_le_of_erase hfuel htlt (phases_trichotomy hne heq hy))
                (hWF₂.erase _)
                (show (discover origI (pullPhase xs origI st)).done = false by
                  rw [discover_done, pullPhase_done]; exact hdone)
                hcm
          · -- created mid-call: the fresh entry keeps the list alive
            have hmem : (a, 0) ∈ (discover origI (pullPhase xs origI st)).live :=
              phases_creates_entry hiA hlo (by omega)
            have hmem₃ := mem_erase_of_ne_target hne heq hy hmem
            split_ifs with hdd
            · exfalso
              rw [List.isEmpty_iff.mp hdd.2] at hmem₃
              simp at hmem₃
            · obtain ⟨i₃, hi₃⟩ := List.mem_iff_getElem?.mp hmem₃
              have hrec := next_entry hne fuel origI
                ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                    (targetIdx origI (discover origI (pullPhase xs origI st))),
                  (discover origI (pullPhase xs origI st)).xsCursor,
                  (discover origI (pullPhase xs origI st)).xsDone,
                  (discover origI (pullPhase xs origI st)).done⟩
                (fuelLB_le_of_erase hfuel htlt (phases_trichotomy hne heq hy))
                (hWF₂.erase _) a 0 i₃ hi₃
              rcases hrec with ⟨-, hdn⟩ | ⟨-, -, -, -, hdn⟩ | h0
              · rw [hdn]
                show (discover origI (pullPhase xs origI st)).done = false
                rw [discover_done, pullPhase_done]
                exact hdone
              · rw [hdn]
                show (discover origI (pullPhase xs origI st)).done = false
                rw [discover_done, pullPhase_done]
                exact hdone
              · exact absurd h0 (hne a)

/-- **The creation call's postcondition**: if the call consumed `a`'s index,
its fresh entry ends the call alive — at cursor `0`, or at cursor `1` having
just emitted the fiber's `0`-th value. In both cases `done` is untouched. -/
theorem next_fresh {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)}
    (hne : ∀ x, ysGen x 0 ≠ none) {a : X} {iA : ℕ} (hiA : xs iA = some a) :
    ∀ (fuel origI : ℕ) (st : State X), fuelLB st origI ≤ fuel → WF xs st →
      st.xsCursor ≤ iA → iA < (next xs ysGen fuel origI st).2.xsCursor →
      ((∃ i : ℕ, (next xs ysGen fuel origI st).2.live[i]? = some (a, 0))
          ∨ (∃ y, (next xs ysGen fuel origI st).1 = some ⟨a, y⟩
              ∧ ysGen a 0 = some y
              ∧ ∃ i : ℕ, (next xs ysGen fuel origI st).2.live[i]? = some (a, 1)))
        ∧ (next xs ysGen fuel origI st).2.done = st.done
  | 0, origI, st, hfuel, _, _, _ =>
    absurd hfuel (by have := fuelLB_pos st origI; omega)
  | fuel + 1, origI, st, hfuel, hWF, hlo, hhi => by
    have hWF₂ := hWF.phases (origI := origI)
    by_cases hcm : (discover origI (pullPhase xs origI st)).xsCursor ≤ iA
    · -- the phases did not create; only a retry could have
      by_cases hlen0 : (pullPhase xs origI st).live.length = 0
      · exfalso
        have hstep : next xs ysGen (fuel + 1) origI st
            = (none, ⟨(pullPhase xs origI st).live, (pullPhase xs origI st).xsCursor,
                (pullPhase xs origI st).xsDone, true⟩) := by
          simp only [next]
          rw [if_pos hlen0]
        rw [hstep] at hhi
        have hhi' : iA < (pullPhase xs origI st).xsCursor := hhi
        rw [discover_xsCursor] at hcm
        omega
      · have hlen2ne : (discover origI (pullPhase xs origI st)).live.length ≠ 0 := by
          rw [discover_live]
          exact hlen0
        have htlt := targetIdx_lt origI (pullPhase xs origI st) hlen2ne
        rcases heq : (discover origI (pullPhase xs origI st)).live[
            targetIdx origI (discover origI (pullPhase xs origI st))]? with _ | ⟨x, j⟩
        · exfalso
          have hstep : next xs ysGen (fuel + 1) origI st
              = (none, ⟨(discover origI (pullPhase xs origI st)).live,
                  (discover origI (pullPhase xs origI st)).xsCursor,
                  (discover origI (pullPhase xs origI st)).xsDone, true⟩) := by
            simp only [next]
            rw [if_neg hlen0]
            simp only [heq]
          rw [hstep] at hhi
          have hhi' : iA < (discover origI (pullPhase xs origI st)).xsCursor := hhi
          omega
        · rcases hy : ysGen x j with _ | y
          · by_cases hdd : (discover origI (pullPhase xs origI st)).xsDone = true
                ∧ ((discover origI (pullPhase xs origI st)).live.eraseIdx
                    (targetIdx origI (discover origI (pullPhase xs origI st)))).isEmpty = true
            · exfalso
              have hstep : next xs ysGen (fuel + 1) origI st
                  = (none, ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                        (targetIdx origI (discover origI (pullPhase xs origI st))),
                      (discover origI (pullPhase xs origI st)).xsCursor,
                      (discover origI (pullPhase xs origI st)).xsDone, true⟩) := by
                simp only [next]
                rw [if_neg hlen0]
                simp only [heq, hy]
                rw [if_pos hdd]
              rw [hstep] at hhi
              have hhi' : iA < (discover origI (pullPhase xs origI st)).xsCursor := hhi
              omega
            · have hstep : next xs ysGen (fuel + 1) origI st
                  = next xs ysGen fuel origI
                      ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                          (targetIdx origI (discover origI (pullPhase xs origI st))),
                        (discover origI (pullPhase xs origI st)).xsCursor,
                        (discover origI (pullPhase xs origI st)).xsDone,
                        (discover origI (pullPhase xs origI st)).done⟩ := by
                simp only [next]
                rw [if_neg hlen0]
                simp only [heq, hy]
                rw [if_neg hdd]
              rw [hstep] at hhi ⊢
              have hrec := next_fresh hne hiA fuel origI
                ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                    (targetIdx origI (discover origI (pullPhase xs origI st))),
                  (discover origI (pullPhase xs origI st)).xsCursor,
                  (discover origI (pullPhase xs origI st)).xsDone,
                  (discover origI (pullPhase xs origI st)).done⟩
                (fuelLB_le_of_erase hfuel htlt (phases_trichotomy hne heq hy))
                (hWF₂.erase _) hcm hhi
              refine ⟨hrec.1, ?_⟩
              rw [hrec.2]
              show (discover origI (pullPhase xs origI st)).done = st.done
              rw [discover_done, pullPhase_done]
          · exfalso
            have hstep : next xs ysGen (fuel + 1) origI st
                = (some ⟨x, y⟩,
                    ⟨(discover origI (pullPhase xs origI st)).live.set
                        (targetIdx origI (discover origI (pullPhase xs origI st))) (x, j + 1),
                      (discover origI (pullPhase xs origI st)).xsCursor,
                      (discover origI (pullPhase xs origI st)).xsDone,
                      (discover origI (pullPhase xs origI st)).done⟩) := by
              simp only [next]
              rw [if_neg hlen0]
              simp only [heq, hy]
            rw [hstep] at hhi
            have hhi' : iA < (discover origI (pullPhase xs origI st)).xsCursor := hhi
            omega
    · -- the phases created: the fresh entry is alive mid-call
      have hmem : (a, 0) ∈ (discover origI (pullPhase xs origI st)).live :=
        phases_creates_entry hiA hlo (by omega)
      obtain ⟨i_a, hia⟩ := List.mem_iff_getElem?.mp hmem
      simp only [next]
      by_cases hlen0 : (pullPhase xs origI st).live.length = 0
      · exfalso
        have := (List.getElem?_eq_some_iff.mp hia).1
        rw [discover_live] at this
        omega
      · rw [if_neg hlen0]
        have hlen2ne : (discover origI (pullPhase xs origI st)).live.length ≠ 0 := by
          rw [discover_live]
          exact hlen0
        have htlt := targetIdx_lt origI (pullPhase xs origI st) hlen2ne
        split
        · rename_i heq0
          rw [List.getElem?_eq_getElem htlt] at heq0
          exact absurd heq0 (Option.some_ne_none _)
        · rename_i heq
          split
          · -- emit: at `a`'s entry (cursor bumps, value emitted) or elsewhere
            rename_i y hy
            by_cases hti : targetIdx origI (discover origI (pullPhase xs origI st)) = i_a
            · rw [hti] at heq
              have hxa := Option.some.inj (heq.symm.trans hia)
              have hx : _ = a := congrArg Prod.fst hxa
              have hj : _ = 0 := congrArg Prod.snd hxa
              subst hx hj
              refine ⟨Or.inr ⟨y, rfl, hy, i_a, ?_⟩, ?_⟩
              · rw [hti, List.getElem?_set_self
                  ((List.getElem?_eq_some_iff.mp hia).1)]
              · show (discover origI (pullPhase xs origI st)).done = st.done
                rw [discover_done, pullPhase_done]
            · refine ⟨Or.inl ⟨i_a, ?_⟩, ?_⟩
              · rw [List.getElem?_set_ne hti]
                exact hia
              · show (discover origI (pullPhase xs origI st)).done = st.done
                rw [discover_done, pullPhase_done]
          · -- removal: the fresh entry survives; finish with `next_entry`
            rename_i hy
            have hmem₃ := mem_erase_of_ne_target hne heq hy hmem
            split_ifs with hdd
            · exfalso
              rw [List.isEmpty_iff.mp hdd.2] at hmem₃
              simp at hmem₃
            · obtain ⟨i₃, hi₃⟩ := List.mem_iff_getElem?.mp hmem₃
              have hrec := next_entry hne fuel origI
                ⟨(discover origI (pullPhase xs origI st)).live.eraseIdx
                    (targetIdx origI (discover origI (pullPhase xs origI st))),
                  (discover origI (pullPhase xs origI st)).xsCursor,
                  (discover origI (pullPhase xs origI st)).xsDone,
                  (discover origI (pullPhase xs origI st)).done⟩
                (fuelLB_le_of_erase hfuel htlt (phases_trichotomy hne heq hy))
                (hWF₂.erase _) a 0 i₃ hi₃
              rcases hrec with ⟨⟨i', -, hent'⟩, hdn⟩ | ⟨y, hem', hyc, ⟨i', -, hent'⟩, hdn⟩ | h0
              · refine ⟨Or.inl ⟨i', hent'⟩, ?_⟩
                rw [hdn]
                show (discover origI (pullPhase xs origI st)).done = st.done
                rw [discover_done, pullPhase_done]
              · refine ⟨Or.inr ⟨y, hem', hyc, i', hent'⟩, ?_⟩
                rw [hdn]
                show (discover origI (pullPhase xs origI st)).done = st.done
                rw [discover_done, pullPhase_done]
              · exact absurd h0 (hne a)

/-! ### The run-level invariants -/

section Run

variable {xs : ℕ → Option X} {ysGen : (x : X) → ℕ → Option (B x)} {s : ℕ → ℕ}

theorem runState_WF (n : ℕ) : WF xs (runState xs ysGen s n) := by
  induction n with
  | zero => exact WF.init xs
  | succ n ih =>
    simp only [runState]
    split_ifs with h
    · exact ih
    · exact next_WF _ _ _ ih

theorem runState_succ_of_not_done {n : ℕ}
    (h : (runState xs ysGen s n).done = false) :
    runState xs ysGen s (n + 1)
      = (next xs ysGen (stepFuel (runState xs ysGen s n) (s n)) (s n)
          (runState xs ysGen s n)).2 := by
  simp only [runState]
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

theorem emitAt_of_not_done {n : ℕ} (h : (runState xs ysGen s n).done = false) :
    emitAt xs ysGen s n
      = (next xs ysGen (stepFuel (runState xs ysGen s n) (s n)) (s n)
          (runState xs ysGen s n)).1 := by
  simp only [emitAt]
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

theorem runState_cursor_mono {n m : ℕ} (h : n ≤ m) :
    (runState xs ysGen s n).xsCursor ≤ (runState xs ysGen s m).xsCursor := by
  induction h with
  | refl => exact le_refl _
  | step _ ih =>
    refine ih.trans ?_
    simp only [runState]
    split_ifs with hd
    · exact le_refl _
    · exact (next_mono _ _ _).1

theorem runState_Iwit {a : X} {iA c : ℕ} (huniq : ∀ k, xs k = some a → k = iA)
    {n m : ℕ} (h : n ≤ m) (hIw : Iwit xs a iA c (runState xs ysGen s n)) :
    Iwit xs a iA c (runState xs ysGen s m) := by
  induction h with
  | refl => exact hIw
  | step _ ih =>
    simp only [runState]
    split_ifs with hd
    · exact ih
    · exact next_Iwit huniq _ _ _ ih

/-- Liveness before creation, along the run. -/
theorem run_notDone_uncreated (hne : ∀ x, ysGen x 0 ≠ none)
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none)
    {a : X} {iA : ℕ} (hiA : xs iA = some a) :
    ∀ n : ℕ, (runState xs ysGen s n).xsCursor ≤ iA →
      (runState xs ysGen s n).done = false := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hcm
    have hprev : (runState xs ysGen s n).xsCursor ≤ iA :=
      le_trans (runState_cursor_mono (Nat.le_succ n)) hcm
    have hnd := ih hprev
    rw [runState_succ_of_not_done hnd]
    exact next_notDone_uncreated hne hcontig hiA _ _ _
      (stepFuel_ge _ _) (runState_WF n) hnd hprev

/-- **The base of the climb**: some step leaves `a` freshly alive at cursor
`0` — or emits its `0`-th value, leaving cursor `1` — with the machine still
running. Taken at the FIRST step whose call consumes `a`'s index. -/
theorem run_base (hne : ∀ x, ysGen x 0 ≠ none)
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none)
    {a : X} {iA : ℕ} (hiA : xs iA = some a)
    (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i) :
    ∃ n : ℕ, (runState xs ysGen s (n + 1)).done = false
      ∧ ((∃ i : ℕ, (runState xs ysGen s (n + 1)).live[i]? = some (a, 0))
        ∨ (∃ y, emitAt xs ysGen s n = some ⟨a, y⟩ ∧ ysGen a 0 = some y
            ∧ ∃ i : ℕ, (runState xs ysGen s (n + 1)).live[i]? = some (a, 1))) := by
  have hcreated : ∃ n, iA < (runState xs ysGen s (n + 1)).xsCursor := by
    obtain ⟨n₀, -, hsn⟩ := hs iA 0
    refine ⟨n₀, ?_⟩
    by_cases hcm : iA < (runState xs ysGen s n₀).xsCursor
    · exact hcm.trans_le
        (runState_cursor_mono (xs := xs) (ysGen := ysGen) (s := s) (Nat.le_succ n₀))
    · have hnd := run_notDone_uncreated hne hcontig hiA n₀ (Nat.le_of_not_lt hcm)
      rw [runState_succ_of_not_done hnd, ← hsn]
      exact next_created hcontig
        (by rw [hsn, hiA]; exact Option.some_ne_none a) _ _
        (stepFuel_ge _ _) (runState_WF n₀)
  -- take the FIRST creating step: before it, `a` is uncreated
  have hpre : (runState xs ysGen s (Nat.find hcreated)).xsCursor ≤ iA := by
    by_cases h0 : Nat.find hcreated = 0
    · rw [h0]
      exact Nat.zero_le _
    · obtain ⟨m, hm⟩ : ∃ m, Nat.find hcreated = m + 1 :=
        ⟨Nat.find hcreated - 1, by omega⟩
      rw [hm]
      have := Nat.find_min hcreated (show m < Nat.find hcreated from by omega)
      omega
  have hnd := run_notDone_uncreated hne hcontig hiA (Nat.find hcreated) hpre
  have hN := Nat.find_spec hcreated
  rw [runState_succ_of_not_done hnd] at hN
  have hfresh := next_fresh hne hiA _ _ (runState xs ysGen s (Nat.find hcreated))
    (stepFuel_ge _ _) (runState_WF (Nat.find hcreated)) hpre hN
  refine ⟨Nat.find hcreated, ?_, ?_⟩
  · rw [runState_succ_of_not_done hnd, hfresh.2]
    exact hnd
  · rw [runState_succ_of_not_done hnd, emitAt_of_not_done hnd]
    exact hfresh.1

/-- **Tracking**: over `Δ` steps, a live `(a, c)` entry either has its
`c`-th value emitted (with the cursor bumped to `c + 1`), or survives at a
NONINCREASING index. -/
theorem track_to (hne : ∀ x, ysGen x 0 ≠ none) {a : X} {c : ℕ}
    (hyc : ysGen a c ≠ none) :
    ∀ (Δ n₀ i₀ : ℕ), (runState xs ysGen s n₀).live[i₀]? = some (a, c) →
      (runState xs ysGen s n₀).done = false →
      (∃ n₁ y, n₀ ≤ n₁ ∧ emitAt xs ysGen s n₁ = some ⟨a, y⟩ ∧ ysGen a c = some y
          ∧ (∃ i : ℕ, (runState xs ysGen s (n₁ + 1)).live[i]? = some (a, c + 1))
          ∧ (runState xs ysGen s (n₁ + 1)).done = false)
        ∨ (∃ i₁ ≤ i₀, (runState xs ysGen s (n₀ + Δ)).live[i₁]? = some (a, c)
            ∧ (runState xs ysGen s (n₀ + Δ)).done = false)
  | 0, n₀, i₀, halive, hnd => Or.inr ⟨i₀, le_refl _, halive, hnd⟩
  | Δ + 1, n₀, i₀, halive, hnd => by
    rw [show n₀ + (Δ + 1) = n₀ + Δ + 1 from rfl]
    rcases track_to hne hyc Δ n₀ i₀ halive hnd with hleft | ⟨i₁, hi₁, halive', hnd'⟩
    · exact Or.inl hleft
    · have hstep := next_entry hne (stepFuel _ (s (n₀ + Δ))) (s (n₀ + Δ))
        (runState xs ysGen s (n₀ + Δ)) (stepFuel_ge _ _)
        (runState_WF (n₀ + Δ)) a c i₁ halive'
      rw [← runState_succ_of_not_done hnd', ← emitAt_of_not_done hnd'] at hstep
      rcases hstep with ⟨⟨i', hi', hent'⟩, hdone'⟩
        | ⟨y, hem, hyc', ⟨i', hi', hent'⟩, hdone'⟩ | h3
      · exact Or.inr ⟨i', by omega, hent', by rw [hdone']; exact hnd'⟩
      · exact Or.inl ⟨n₀ + Δ, y, by omega, hem, hyc', ⟨i', hent'⟩,
          by rw [hdone']; exact hnd'⟩
      · exact absurd h3 hyc

/-- **The climb step** (strong induction on the position): a live `(a, c)`
entry with a nonexhausted cursor eventually has its `c`-th value emitted.
The scheduler hits the entry's index; between the start and the hit the
entry only moves DOWN (tracking), so either the hit lands (emission), or the
index strictly dropped and the induction applies. -/
theorem climb_step (hne : ∀ x, ysGen x 0 ≠ none)
    (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i) {a : X} {c : ℕ} (hyc : ysGen a c ≠ none) :
    ∀ (i₀ n₀ : ℕ), (runState xs ysGen s n₀).live[i₀]? = some (a, c) →
      (runState xs ysGen s n₀).done = false →
      ∃ n₁ y, n₀ ≤ n₁ ∧ emitAt xs ysGen s n₁ = some ⟨a, y⟩ ∧ ysGen a c = some y
        ∧ (∃ i : ℕ, (runState xs ysGen s (n₁ + 1)).live[i]? = some (a, c + 1))
        ∧ (runState xs ysGen s (n₁ + 1)).done = false := by
  intro i₀
  induction i₀ using Nat.strong_induction_on with
  | _ i₀ ih =>
    intro n₀ halive hnd
    obtain ⟨n, hn₀n, hsn⟩ := hs i₀ n₀
    obtain ⟨Δ, rfl⟩ : ∃ Δ, n = n₀ + Δ := ⟨n - n₀, by omega⟩
    rcases track_to hne hyc Δ n₀ i₀ halive hnd with hleft | ⟨i₁, hi₁, halive', hnd'⟩
    · exact hleft
    · rcases Nat.lt_or_ge i₁ i₀ with hlt | hge
      · obtain ⟨n₁, y, hle, rest⟩ := ih i₁ hlt (n₀ + Δ) halive' hnd'
        exact ⟨n₁, y, by omega, rest⟩
      · have hi₀ : i₁ = i₀ := by omega
        subst hi₀
        -- the hit: the scheduler value IS the entry's index
        have hent : (runState xs ysGen s (n₀ + Δ)).live[s (n₀ + Δ)]?
            = some (a, c) := by
          rw [hsn]
          exact halive'
        obtain ⟨f, hf⟩ : ∃ f,
            stepFuel (runState xs ysGen s (n₀ + Δ)) (s (n₀ + Δ)) = f + 1 :=
          ⟨stepFuel (runState xs ysGen s (n₀ + Δ)) (s (n₀ + Δ)) - 1,
            by unfold stepFuel; omega⟩
        have hhit := next_hit (xs := xs) (ysGen := ysGen) hent f
        rw [← hf, ← runState_succ_of_not_done hnd', ← emitAt_of_not_done hnd'] at hhit
        rcases hhit with ⟨y, hem, hyy, hpost, hdone1⟩ | h3
        · exact ⟨n₀ + Δ, y, by omega, hem, hyy, ⟨s (n₀ + Δ), hpost⟩,
            by rw [hdone1]; exact hnd'⟩
        · exact absurd h3 hyc

/-- **The full climb**: from a live `(a, c₀)` entry with `c₀ ≤ j` (and all
fiber values through `j` present), the `j`-th value is eventually emitted. -/
theorem climb_to (hne : ∀ x, ysGen x 0 ≠ none)
    (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i) {a : X} {j : ℕ}
    (hval : ∀ c, c ≤ j → ysGen a c ≠ none) :
    ∀ (k c₀ n₀ i₀ : ℕ), j + 1 - c₀ ≤ k → c₀ ≤ j →
      (runState xs ysGen s n₀).live[i₀]? = some (a, c₀) →
      (runState xs ysGen s n₀).done = false →
      ∃ n y, emitAt xs ysGen s n = some ⟨a, y⟩ ∧ ysGen a j = some y
  | 0, c₀, n₀, i₀, hk, hcj, _, _ => absurd hk (by omega)
  | k + 1, c₀, n₀, i₀, hk, hcj, halive, hnd => by
    obtain ⟨n₁, y, -, hem, hyc, ⟨i', hent'⟩, hnd'⟩ :=
      climb_step hne hs (hval c₀ hcj) i₀ n₀ halive hnd
    rcases Nat.eq_or_lt_of_le hcj with rfl | hlt
    · exact ⟨n₁, y, hem, hyc⟩
    · exact climb_to hne hs hval k (c₀ + 1) (n₁ + 1) i' (by omega) (by omega)
        hent' hnd'

/-- **Existence**: every dependent pair is emitted. -/
theorem emit_exists (hne : ∀ x, ysGen x 0 ≠ none)
    (hcontig : ∀ k, xs k = none → xs (k + 1) = none)
    (hys_contig : ∀ x j, ysGen x j = none → ysGen x (j + 1) = none)
    (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i)
    {a : X} {iA : ℕ} (hiA : xs iA = some a)
    {b : B a} {j : ℕ} (hyb : ysGen a j = some b)
    (hujb : ∀ j', ysGen a j' = some b → j' = j) :
    ∃ n, emitAt xs ysGen s n = some ⟨a, b⟩ := by
  have hval : ∀ c, c ≤ j → ysGen a c ≠ none := by
    intro c hc hnone
    rw [contig_closure (hys_contig a) hc hnone] at hyb
    exact Option.some_ne_none b hyb.symm
  obtain ⟨N, hndN, hbase⟩ := run_base hne hcontig hiA hs
  have hemit : ∃ n y, emitAt xs ysGen s n = some ⟨a, y⟩ ∧ ysGen a j = some y := by
    rcases hbase with ⟨i0, hent0⟩ | ⟨y, hemy, hy0, i1, hent1⟩
    · exact climb_to hne hs hval (j + 1) 0 (N + 1) i0 (by omega) (Nat.zero_le j)
        hent0 hndN
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact ⟨N, y, hemy, hy0⟩
      · exact climb_to hne hs hval j 1 (N + 1) i1 (by omega) (by omega) hent1 hndN
  obtain ⟨n, y, hem, hyj⟩ := hemit
  have hby : y = b := Option.some.inj (hyj.symm.trans hyb)
  subst hby
  exact ⟨n, hem⟩

/-- **Uniqueness**: a pair is emitted at most once — the first emission
establishes the monotone witness, which blocks any later one. -/
theorem emit_unique
    (hinj : ∀ k k' (v : X), xs k = some v → xs k' = some v → k = k')
    {a : X} {iA : ℕ} (huniq : ∀ k, xs k = some a → k = iA)
    {b : B a} {jb : ℕ} (hjb : ∀ j', ysGen a j' = some b → j' = jb)
    {n n' : ℕ} (hem : emitAt xs ysGen s n = some ⟨a, b⟩)
    (hem' : emitAt xs ysGen s n' = some ⟨a, b⟩) : n = n' := by
  -- an emission at `m` before an emission at `m'` is impossible
  suffices key : ∀ {m m' : ℕ}, m < m' → emitAt xs ysGen s m = some ⟨a, b⟩ →
      emitAt xs ysGen s m' = some ⟨a, b⟩ → False by
    rcases lt_trichotomy n n' with h | h | h
    · exact absurd hem' (fun hc => key h hem hc)
    · exact h
    · exact absurd hem (fun hc => key h hem' hc)
  intro m m' hmm hemm hemm'
  -- the emissions force live steps
  have hndm : (runState xs ysGen s m).done = false := by
    by_contra hd
    rw [emitAt, if_pos (by simpa using hd)] at hemm
    exact Option.some_ne_none _ hemm.symm
  have hndm' : (runState xs ysGen s m').done = false := by
    by_contra hd
    rw [emitAt, if_pos (by simpa using hd)] at hemm'
    exact Option.some_ne_none _ hemm'.symm
  rw [emitAt_of_not_done hndm] at hemm
  rw [emitAt_of_not_done hndm'] at hemm'
  -- establish the witness after `m`, carry it to `m'`, block there
  have hIw1 : Iwit xs a iA (jb + 1) (runState xs ysGen s (m + 1)) := by
    rw [runState_succ_of_not_done hndm]
    exact next_Iwit_establish hinj huniq _ _ _ (runState_WF m) hemm hjb
  have hIw2 : Iwit xs a iA (jb + 1) (runState xs ysGen s m') :=
    runState_Iwit huniq (by omega) hIw1
  have := next_Iwit_block huniq _ _ _ hIw2 hemm' hjb
  omega

end Run

/-! ### The generator -/

/-- **The Rust-exact stream as a proven `ExhaustiveGenerator`** (Level 2):
Malachite's `ExhaustiveDependentPairs` semantics — live-list re-targeting,
mid-call retries and all — enumerates every dependent pair exactly once,
given honest generators, contiguity on both sides (iterator semantics =
generator semantics), nonempty fibers (excluding the documented hang), and
the scheduler certificate. The `gen` IS the simulator stream (`emitAt`, the
`slack := 0` fuel). -/
@[reducible] def simGen {A : Type*} {B : A → Type*}
    (gA : ExhaustiveGenerator A) (gB : (a : A) → ExhaustiveGenerator (B a))
    (hA : ∀ n, gA.gen n = none → gA.gen (n + 1) = none)
    (hB : ∀ a n, (gB a).gen n = none → (gB a).gen (n + 1) = none)
    (hne : ∀ a, (gB a).gen 0 ≠ none)
    (s : ℕ → ℕ) (hs : ∀ i N, ∃ n, N ≤ n ∧ s n = i) :
    ExhaustiveGenerator ((a : A) × B a) where
  gen n := emitAt gA.gen (fun a => (gB a).gen) s n
  occurs_exactly_once := by
    rintro ⟨a, b⟩
    obtain ⟨iA, hiA, huA⟩ := gA.occurs_exactly_once a
    obtain ⟨jb, hjb, hujb⟩ := (gB a).occurs_exactly_once b
    have hinj : ∀ k k' (v : A), gA.gen k = some v → gA.gen k' = some v → k = k' := by
      intro k k' v h1 h2
      obtain ⟨i, -, hu⟩ := gA.occurs_exactly_once v
      rw [hu k h1, hu k' h2]
    obtain ⟨n, hn⟩ := emit_exists hne hA hB hs hiA hjb
      (fun j' hj' => hujb j' hj')
    exact ⟨n, hn, fun m hm =>
      emit_unique hinj (fun k hk => huA k hk) (fun j' hj' => hujb j' hj') hm hn⟩

end DepPairsSim

end ExhaustiveGenerator

/-! ### Guards

The Level-2 generator's stream IS the Level-1 simulator's, and hence the
Rust's — checked concretely on the two headline configurations. -/

open ExhaustiveGenerator ExhaustiveGenerator.DepPairsSim

section Guards

/-- Fibers of the `exhaustive_vecs` configuration are contiguous (needed by
the Rust semantics: iterator end = generator end). -/
private theorem vecContig : ∀ (n k : ℕ),
    (gen (T := List.Vector AzNat n) k) = none →
    (gen (T := List.Vector AzNat n) (k + 1)) = none :=
  fun _ => Contiguous.contig

/-- Fibers of the `exhaustive_vecs` configuration are nonempty (excluding
the Rust hang: every length has at least one vec over a nonempty type). -/
private theorem vecNe : ∀ n : ℕ, (gen (T := List.Vector AzNat n) 0) ≠ none
  | 0 => fun h => Option.some_ne_none _ h
  | _ + 1 => fun h => Option.some_ne_none _ h

end Guards

-- Level 2 ≡ Level 1, all-infinite configuration (ruler-scheduled ℕ-pairs):
-- the proven generator's stream is the simulator's, value for value.
#guard ((List.range 20).filterMap
    ((DepPairsSim.simGen lengthsGen (fun _ => lengthsGen)
      (fun n h => absurd h (Option.some_ne_none n))
      (fun _ n h => absurd h (Option.some_ne_none n))
      (fun _ h => Option.some_ne_none 0 h)
      rulerSequence exists_le_and_rulerSequence_eq).gen))
  = DepPairsSim.firstN (fun k => some k) (fun _ j => some j) rulerSequence 0 20

-- Level 2 ≡ Level 1 on the `exhaustive_vecs` configuration — finite
-- length-0 fiber, removals, re-targeting: the proven stream is the RUST
-- stream (third output `[1]`).
#guard ((List.range 20).filterMap
    ((DepPairsSim.simGen lengthsGen
      (fun n => (inferInstance : ExhaustiveGenerator (List.Vector AzNat n)))
      (fun n h => absurd h (Option.some_ne_none n))
      vecContig vecNe rulerSequence exists_le_and_rulerSequence_eq).gen)).map
    (fun p => p.2.toList.map (·.toNat))
  = [[], [0], [1], [0, 0, 0], [2], [0, 0], [3], [0, 0, 0, 0], [4], [0, 1], [5], [0, 0, 1],
     [6], [1, 0], [7], [0, 0, 0, 0, 0], [8], [1, 1], [9], [0, 1, 0]]

-- Occurs-exactly-once, concrete: a long prefix of the Rust-order stream has
-- no duplicates (the theorem's uniqueness half made visible).
#guard ((List.range 60).filterMap
    ((DepPairsSim.simGen lengthsGen
      (fun n => (inferInstance : ExhaustiveGenerator (List.Vector AzNat n)))
      (fun n h => absurd h (Option.some_ne_none n))
      vecContig vecNe rulerSequence exists_le_and_rulerSequence_eq).gen)).map
    (fun p => p.2.toList.map (·.toNat)) |>.Nodup

end Azurite