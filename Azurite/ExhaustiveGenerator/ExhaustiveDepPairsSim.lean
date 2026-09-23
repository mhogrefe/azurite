/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Rust-exact simulator for `ExhaustiveDependentPairs` — the Level-1 fidelity
  artifact for `exhaustive_dependent_pairs` / `exhaustive_vecs`.

  `ExhaustiveDepPairs.lean` ports the MATHEMATICS (occurs-exactly-once via
  absolute slots and occurrence counting); its interleaving diverges from the
  Rust stream once a component exhausts, because the Rust `next()` REMOVES
  exhausted fiber iterators from its live list (`xs_yss.remove(i)`, shifting
  every later index down) and re-targets the scheduler at the survivors
  (`i %= len` once `xs` is done), retrying in an inner loop until something
  emits. This file ports that STATE MACHINE literally, so the emitted stream
  is bit-for-bit the Rust one — the exact-behavior witness for differential
  testing against Malachite, cross-checked here against both Rust doctests
  verbatim (including the one the clean port structurally cannot replay:
  duplicated `xs` values and empty fibers).

  It is a SIMULATOR, not an `ExhaustiveGenerator`: no occurs-exactly-once is
  claimed (the Rust stream doesn't satisfy it for repeating `xs` anyway —
  its own doctest emits `(3, 300)` twice). The compute shape is the stream
  rail's: state + step, values collected in emission order.

  Inputs are RAW iterator functions (`xs : ℕ → Option X`, fibers
  `ysGen : X → ℕ → Option Y`), read with iterator semantics BY CONSTRUCTION:
  the first `none` permanently ends a source, because the `xs` cursor never
  advances past a `none` and an exhausted fiber is removed rather than
  re-read. So no contiguity hypotheses are needed for fidelity — arbitrary
  functions behave as the iterators they induce, and `xs` need not be a
  generator at all (duplicates give fresh fibers, as in Rust).

  FUEL: the Rust `next()` genuinely hangs when every remaining fiber is
  empty and `xs` is infinite (documented: "the output iterator will hang…
  try `exhaustive_dependent_pairs_stop_after_empty_ys`"). The inner loop
  here is fueled — `s n + live.length + slack + 2` per step, where each
  iteration beyond the first is a permanent fiber removal, `s n + 1` bounds
  the live-list capacity, and `slack` covers empty fibers appended
  mid-retry. `slack := 0` suffices when no fiber is empty (e.g.
  `exhaustive_vecs` over nonempty `T`); the Rust hang is exactly the case
  where no finite slack does, and the simulator then marks the stream done
  where the Rust would spin forever — the one (deliberate) divergence, in a
  regime where the Rust produces nothing anyway.
-/
import Azurite.ExhaustiveGenerator.ExhaustiveVecs

namespace Azurite

namespace ExhaustiveGenerator

namespace DepPairsSim

/-- The simulator state — Rust `ExhaustiveDependentPairs` minus the
iterators-as-values: `live` is `xs_yss` with each fiber iterator reduced to
its read cursor, `xsCursor` the `xs` read position, `xsDone`/`done` the two
flags. -/
structure State (X : Type*) where
  /-- The live fibers, in Rust list order: `(x value, next fiber index)`. -/
  live : List (X × ℕ)
  /-- The `xs` read position (never advances past a `none`). -/
  xsCursor : ℕ
  /-- Set once a pull finds `xs` exhausted; the scheduler then wraps
  (`i %= len`). -/
  xsDone : Bool
  /-- Set once the stream ends (or on fuel exhaustion — the Rust hang). -/
  done : Bool

variable {X : Type*} {B : X → Type*}

/-- The empty initial state. -/
def State.init : State X := ⟨[], 0, false, false⟩

/-- The pull phase (`for x in (&mut self.xs).take(count)`): read up to
`count` values of `xs` at the cursor, appending each as a fresh fiber
(cursor `0`); stop early at a `none` WITHOUT advancing past it (rereads stay
`none` — iterator semantics). -/
def pull (xs : ℕ → Option X) : ℕ → State X → State X
  | 0, st => st
  | count + 1, st =>
    match xs st.xsCursor with
    | some x =>
      pull xs count
        { st with live := st.live ++ [(x, 0)], xsCursor := st.xsCursor + 1 }
    | none => st

/-- The append phase of a `next()` call (`else if i >= xs_yss_len { … }`):
top the live list up toward `origI + 1` fibers, unless `xs` is already known
done or the list is long enough. -/
def pullPhase (xs : ℕ → Option X) (origI : ℕ) (st : State X) : State X :=
  if st.xsDone then st
  else if st.live.length ≤ origI then pull xs (origI - st.live.length + 1) st
  else st

/-- The `xs_done` discovery: the pull could not reach `origI + 1` fibers, so
`xs` is exhausted. -/
def discover (origI : ℕ) (st : State X) : State X :=
  if st.xsDone = false ∧ st.live.length ≤ origI then { st with xsDone := true }
  else st

/-- The pulled position: the raw scheduler value, wrapped modulo the live
count once `xs` is done (`i %= len`). -/
def targetIdx (origI : ℕ) (st : State X) : ℕ :=
  if st.xsDone then origI % st.live.length else origI

/-- One Rust `next()` call: the retry loop at scheduler value `origI`.
Mirrors the Rust control flow line for line — append phase (only while `xs`
is not done and the list is short), empty-list bailout, `xs_done` discovery
with `i %= len` re-targeting, then pull fiber `i`: a value emits (cursor
bumped in place), an exhausted fiber is REMOVED (later indices shift down)
and the loop retries the same `origI` against the shorter list. Fibers may
be TYPE-dependent on their `x` (`B x`); Rust's non-dependent pairs are the
constant-`B` case. -/
def next (xs : ℕ → Option X) (ysGen : (x : X) → ℕ → Option (B x)) :
    ℕ → ℕ → State X → Option ((x : X) × B x) × State X
  | 0, _, st =>
    -- Fuel exhausted: the documented Rust hang. Mark done (Rust spins).
    (none, { st with done := true })
  | fuel + 1, origI, st =>
    let st₁ := pullPhase xs origI st
    if st₁.live.length = 0 then
      -- `if xs_yss_len == 0 { done = true; return None }`.
      (none, { st₁ with done := true })
    else
      let st₂ := discover origI st₁
      let i := targetIdx origI st₂
      match st₂.live[i]? with
      | none => (none, { st₂ with done := true }) -- unreachable (`i < len`)
      | some (x, j) =>
        match ysGen x j with
        | some y =>
          -- Emit, bumping fiber `i`'s cursor in place.
          (some ⟨x, y⟩, { st₂ with live := st₂.live.set i (x, j + 1) })
        | none =>
          -- `xs_yss.remove(i)`: drop the exhausted fiber, indices shift.
          let st₃ := { st₂ with live := st₂.live.eraseIdx i }
          if st₃.xsDone ∧ st₃.live.isEmpty then
            (none, { st₃ with done := true })
          else
            next xs ysGen fuel origI st₃

/-- The emitted stream: run `next()` for up to `steps` scheduler values,
collecting emissions in order, stopping where the Rust iterator ends. Per
step the loop fuel is `s n + live.length + slack + 2` (see the module
header; `slack := 0` suffices when no fiber is empty). -/
def firstN (xs : ℕ → Option X) (ysGen : (x : X) → ℕ → Option (B x)) (s : ℕ → ℕ)
    (slack : ℕ) (steps : ℕ) : List ((x : X) × B x) :=
  go 0 steps State.init
where
  /-- The collector: step counter, remaining steps, state. -/
  go (n : ℕ) : ℕ → State X → List ((x : X) × B x)
    | 0, _ => []
    | steps + 1, st =>
      if st.done then []
      else
        match next xs ysGen (s n + st.live.length + slack + 2) (s n) st with
        | (some v, st') => v :: go (n + 1) steps st'
        | (none, _) => []

end DepPairsSim

end ExhaustiveGenerator

/-! ### Guards — the Rust streams, bit for bit

Both `exhaustive_dependent_pairs` doctests and the `exhaustive_vecs` doctest
replay VERBATIM — including everything the clean port deliberately does
differently: the post-exhaustion re-targeting (`exhaustive_vecs`' third
output is `[1]` here, a hole there), the duplicated-`xs` doctest with its
repeated `(3, 300)` and its exact 9-value termination, and the no-exhaustion
doctest on which simulator, clean port, and Rust all agree step for step. -/

open ExhaustiveGenerator

-- Malachite's `exhaustive_vecs(exhaustive_unsigneds::<u32>())` doctest,
-- verbatim: lengths `0, 1, 2, …` as `xs`, the fair fixed-length vecs as
-- fibers, ruler-scheduled. Note the third output `[1]`: the length-`0`
-- fiber dies at step `2` and the scheduler re-targets slot `0` at the
-- length-`1` fiber — the exact behavior the clean port renders as a hole.
#guard (DepPairsSim.firstN (fun k => some k)
      (fun n j => (gen (T := List.Vector AzNat n) j).map (fun v => v.toList.map (·.toNat)))
      rulerSequence 0 20).map (·.2)
  = [[], [0], [1], [0, 0, 0], [2], [0, 0], [3], [0, 0, 0, 0], [4], [0, 1], [5], [0, 0, 1],
     [6], [1, 0], [7], [0, 0, 0, 0, 0], [8], [1, 1], [9], [0, 1, 0]]

-- Malachite's duplicated-`xs` doctest, verbatim — structurally out of reach
-- of the clean port (`xs = [1, 2, 3, 2, 3, 2, 2]` repeats values; `2` maps
-- to an EMPTY fiber): note the repeated `(3, 300)` (two separate fibers for
-- the duplicated `3`) and the exact 9-value termination, which exercises
-- the whole machine — mid-call cascaded removals, `xs`-end discovery, and
-- `i %= len` wraparound.
#guard (DepPairsSim.firstN (fun k => [1, 2, 3, 2, 3, 2, 2][k]?)
      (fun x j => (match x with
        | 1 => [100, 101, 102]
        | 3 => [300, 301, 302]
        | _ => ([] : List ℕ))[j]?)
      rulerSequence 8 20).map (fun p => (p.1, p.2))
  = [(1, 100), (3, 300), (1, 101), (3, 300), (1, 102), (3, 301), (3, 302), (3, 301),
     (3, 302)]

-- The no-exhaustion regime (the 50-pair multiples doctest): simulator and
-- CLEAN generator agree step for step — no removal ever fires, so the
-- absolute-slot and live-list views coincide.
#guard (DepPairsSim.firstN (fun k => some (k + 1)) (fun x j => some ((j + 1) * x))
      rulerSequence 0 50).map (fun p => (p.1, p.2))
  = (firstN ((_ : {n : AzNat // 0 < n}) × AzNat) 50).map
      (fun p => (p.1.val.toNat, (p.2.toNat + 1) * p.1.val.toNat))

-- Cross-check against the clean `exhaustive_vecs`: the streams interleave
-- differently but enumerate the same lists — every simulator value appears
-- in a clean-generator prefix, and the simulator emits no duplicates.
#guard (let sim := (DepPairsSim.firstN (fun k => some k)
      (fun n j => (gen (T := List.Vector AzNat n) j).map List.Vector.toList)
      rulerSequence 0 30).map (·.2)
  sim.Nodup && (let clean := (List.range 200).filterMap (gen (T := List AzNat))
    sim.all (· ∈ clean)))

end Azurite
