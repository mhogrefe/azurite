# Planning: completing `bodyStep_BZ` and `q_init_bounds`

## Context

Two open sorries gate the BZ correctness chain:

```
schoolbookDivMod_toNat  ← go_toNat  ← bodyStep_BZ  ← {q_init_bounds, fuel-safety}
```

- `q_init_bounds` (Knuth/Möller–Granlund two-correction): asserts
  `q_true ≤ q_init.toNat ≤ q_true + 2`.
- `bodyStep_BZ`: ties together `subMulLimbs_toNat`, `addback_toNat`,
  `q_init_bounds`, and the `bodyStep` identity to produce the post-step
  invariant `R < B  ∧  A_local = digit · B + R`.

The structural blocker for `bodyStep_BZ` is `bodyStep_toNat`'s hypothesis

```lean
h_q_safe : (subMulLimbs … q_init …).2 = true → 2 ≤ q_init.toNat
```

which is **too strong** at the corner `q_true = 0, q_init = 1`. Algorithmically
only one addback iteration ever fires there (the new borrow is `false`
after one round, so `q = 0 → q − 1 = wraparound` is never executed), but
the current `addback_toNat` cannot see that — it bounds fuel uniformly.

Independently, `q_init_bounds` itself is a substantial Knuth-style proof
(~150–300 lines) regardless of which path we take for `bodyStep_BZ`.

---

## Approach A — Strengthen `addback_toNat` with a value-based hypothesis

### Idea
Replace the current fuel hypothesis

```lean
borrow = true → fuel ≤ q.toNat
```

with a **value-based** invariant tracking the signed running value
`A_local + r.2·β^(n+1) − q_init·B` (or equivalent), so that the fuel bound
follows from the bound `q_init ≤ q_true + 2 ≤ β-1 + 2`.

A first cut:

```lean
hq_value : ∀ k, k ≤ fuel → borrow_after_k = true → k < q.toNat
```

— but this is hard to state without already having the addback semantics.
A more practical version: a single hypothesis bounding the *true* value,
e.g. `r_true_value ≥ −fuel · B` (so each addback strictly decreases
fuel-needed), specialized so callers don't have to track signed arithmetic.

### Pros
- Conceptually clean: addback fuel = "rounds of correction needed", which
  is what M–G proves bounded.
- Single change, all downstream consumers (only `bodyStep_toNat` so far)
  benefit.
- The hypothesis becomes the natural M–G consequence (already what
  `q_init_bounds` provides).

### Cons
- Requires re-proving `addback_toNat`. The current proof's induction is
  on `fuel` with simple arithmetic; the new proof must thread a
  value-based invariant through.
- Statement design is non-trivial — too weak and downstream proofs choke,
  too strong and the inductive step doesn't close.
- Touching `Addback.lean` risks breaking the schoolbook chain in
  `schoolbookDivMod_toNat`'s suffix preservation lemmas (which also use
  `addback_toNat`'s identity, *not* the safety hypothesis — but worth
  auditing).

### Estimated effort
- ~80–150 lines changed in `Addback.lean`.
- Knock-on edits in `BodyStep.lean` (`bodyStep_toNat`'s call site).
- Re-verify all `addback_toNat`/`addback_*` consumers compile.

---

## Approach B — Sub-case `bodyStep_BZ` on `q_init.toNat ∈ {0, 1, ≥2}`

### Idea
Keep `addback_toNat` as-is. In `bodyStep_BZ`, split on the value of
`q_init.toNat`:

- **`q_init = 0`**: `subMul` doesn't borrow (since `0 · B = 0 ≤ A_local`),
  addback is a no-op, `bodyStep` reduces to a `set` of `0` at the high
  slot. Trivial value identity.
- **`q_init = 1`**: case-split on whether `subMul` borrows.
  - No borrow → addback no-op, `bodyStep` stores `1` at high slot,
    value identity `A_local = 1·B + (A_local − B)` directly.
  - Borrow → inline the single addback iteration manually using
    `addSameLengthLimbs_toNat` (one round, then exit on
    `borrow_in = false`). Show `q_true = 0`, digit stored = `0`,
    remainder = `A_local`.
- **`q_init ≥ 2`**: `bodyStep_toNat`'s `h_q_safe` is satisfied; use it
  directly. Combine with `q_init_bounds` to identify `fixup.2 = q_true`
  and `Flo < B`.

### Pros
- Localized: no touching of `Addback.lean` or `bodyStep_toNat`.
- Each sub-case has a clear algorithmic story matching the M–G analysis.
- The `q_init = 1` corner is small (≤ ~50 lines of inlined addback
  reasoning).

### Cons
- Triplicates structural work: every "value identity ⇒ `R < B  ∧  digit
  = q_true`" extraction has to be done in each branch.
- The `q_init = 1, borrow = true` branch requires a manual replay of one
  addback step — bypasses the addback abstraction we already built.
- Adds a permanent asymmetry to the proof; future maintainers must
  understand why fuel = 2 but the `q_init = 1` branch is special.

### Estimated effort
- ~150–250 lines in `BodyStep.lean`.
- No edits to other files.

---

## Approach C — Hybrid: minimal addback strengthening + thin bodyStep proof

### Idea
Add a **second** lemma `addback_toNat_strict` next to the existing one,
specialized to `fuel = 2`, with a hypothesis that's tractable:

```lean
addback_toNat_two
  (h_value_bound : A_local + r.2·β^(n+1) ≥ q_init.toNat · B − 2 · B)
  : ∃ b_out, …  -- same conclusion as addback_toNat
```

The condition says "at most 2 addbacks are needed", which is exactly what
`q_init_bounds` (`q_true ≤ q_init ≤ q_true + 2`) gives us for free. We
keep the existing `addback_toNat` for use elsewhere; the new lemma is
called only by `bodyStep_BZ`.

### Pros
- Doesn't disturb existing `addback_toNat` users.
- The hypothesis is the *exact* fact M–G provides — minimal mismatch.
- `bodyStep_BZ`'s proof becomes a clean chain: `q_init_bounds → value
  bound → addback_toNat_two → bodyStep identity`.

### Cons
- Adds ~80–150 lines to `Addback.lean` for the new lemma. The proof is
  similar to the existing `addback_toNat` but uses the value bound
  instead of the fuel bound, threading through the sign-flip on each
  iteration.
- Two slightly different addback correctness lemmas — mild proof-bloat.
- The value-bound hypothesis is value-arithmetic; the proof's induction
  step needs to argue that after one addback, the bound shifts by `B`
  (so fuel decreases consistently with required-fuel).

### Estimated effort
- ~100–180 lines in `Addback.lean`.
- ~50–80 lines for `bodyStep_BZ` in `BodyStep.lean`.

---

## Independent: `q_init_bounds` (Knuth/M–G two-correction)

Regardless of which approach above we pick, `q_init_bounds` must be
proved. Its proof structure:

1. **Decompose limb arrays**:
   `A_local = A_top·β^n + A_next·β^(n-1) + A_rest` with `A_rest < β^(n-1)`.
   `B = bn1·β^(n-1) + B_rest` with `B_rest < β^(n-1)`.
2. **Cap branch (`bn1 ≤ A_top`)**: must show `q_init = β − 1` lies in
   `[q_true, q_true + 2]`.
   - `A_local < β·B` (BZ invariant) ⇒ `q_true < β`, so `q_true ≤ β−1`.
   - Lower bound: `q_true ≥ β − 3`. Uses `A_local ≥ A_top·β^n ≥ bn1·β^n`
     and `B < (bn1 + 1)·β^(n−1)`, giving `A_local/B > β − 3`.
3. **`div2By1` branch (`A_top < bn1`)**: `q_init = ⌊(A_top·β + A_next) / bn1⌋`
   exactly (`toNat_div2By1` lemma, which we already have).
   - Upper bound: standard Knuth — `q_init` overestimates by at most 2
     because the omitted `A_rest` and `B_rest` each contribute < `β^(n−1)`.
   - Lower bound: similarly bounded.

Estimated effort: **~150–300 lines** in `BodyStep.lean` (or split out into
`QInitBounds.lean`). This is largely independent of the addback approach.

---

## Recommendation matrix

| Goal | Best approach |
|------|---------------|
| Fastest to ship | **B** (no Addback edits) |
| Cleanest long-term API | **A** (single addback lemma, value-based) |
| Risk-minimized incremental | **C** (additive, no API breakage) |
| Closest to BZ paper structure | **C** (mirrors M–G's value-bound argument) |

If the project plans further proofs of multi-precision routines that
re-use `addback`, **A** pays off. If `addback` is only ever used inside
`schoolbookDivMod`, **B** is fine. If we want to keep options open,
**C** is the safest middle ground.

---

## Critical files

- [Azurite/AzNat/Equiv/Addback.lean](../../Azurite/AzNat/Equiv/Addback.lean)
  — `addback_toNat` (relevant for A and C).
- [Azurite/AzNat/Equiv/BodyStep.lean](../../Azurite/AzNat/Equiv/BodyStep.lean)
  — `bodyStep_toNat` call site, `q_init_bounds`, `bodyStep_BZ`.
- [Azurite/AzNat/Equiv/Div.lean](../../Azurite/AzNat/Equiv/Div.lean)
  — `go_toNat`, `schoolbookDivMod_toNat` (consumers of `bodyStep_BZ`,
  unaffected by the choice).
- [Azurite/AzNat/Div.lean](../../Azurite/AzNat/Div.lean) — `addback`,
  `bodyStep`, `go` definitions (unchanged in all approaches).

## Verification

After implementation:

1. `lean_diagnostic_messages` on `Addback.lean`, `BodyStep.lean`,
   `Div.lean` (under `Equiv/`).
2. `lake build` / `lean_build` for the full project.
3. Spot-check: `lean_verify Azurite.AzNat.schoolbookDivMod_toNat` —
   axiom check should reveal only `q_init_bounds` and `bodyStep_BZ` as
   remaining sorries (or zero, once those land).
