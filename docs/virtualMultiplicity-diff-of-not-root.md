# Planning: `virtualMultiplicity_diff_of_not_root`

Proof-plan for the single remaining `sorry` in
[`Azurite/BasuPollackRoy/Chapter2/VirtualRoots.lean`](../Azurite/BasuPollackRoy/Chapter2/VirtualRoots.lean),
at the theorem `virtualMultiplicity_diff_of_not_root`. Lemma 2.48 compiles
modulo this one claim.

## The claim

For `P ∈ R[X]` nonzero, `P' ≠ 0`, and `c : R` with `P(c) ≠ 0`, let
`ν := (derivative P).rootMultiplicity c`. Then

```
(v(P, c) : ℤ) − (v(P', c) : ℤ)
  =
  if Even ν then 0
  else if 0 < P.eval c * P^(ν+1).eval c then 1 else -1
```

Here `v(·, c)` is `virtualMultiplicity = (virtualRoots …).count c`, and
`P^(k)` abbreviates `(⇑derivative)^[k] P`.

Intuitively this is BPR Proposition 2.46 interpretation (3): the sign of
`P(c) · P^(ν+1)(c)` and the parity of `ν` together determine which of the
three trichotomy cases holds when `c` is not a root of `P`.

## What is already in place

* **Trichotomy.** `virtualMultiplicity_derivative_cases` pins the
  difference to `{-1, 0, 1}` via the interlacing count bound
  `Internal.Interlaced.count_diff_le_one`.

* **Root case.** `virtualMultiplicity_derivative_of_root` handles
  `P(c) = 0` via the argmin-chain recursion
  `Internal.count_eq_of_root_from_aux`.

* **Sign infrastructure.** `Proposition_2_21`'s `HasSignLeft` /
  `HasSignRight` give the one-sided sign of an iterated derivative near
  `c`. These are what drive the LHS-side computation in
  `varBetween_der_succ_of_not_root_at_c`.

* **`Lemma_2_48.lean` compiles** with the non-root case closed modulo
  this claim: the key equation
  `varBetween_der_succ_of_not_root_at_c` shows

  ```
  varBetween (der P) d c − varBetween (der Q) d c
    = v(P, c) − v(Q, c)
  ```

  under the root-free hypothesis, by computing both sides as the same
  sign formula. The LHS side uses sign analysis + `varAt_cons_der_eq`.
  The RHS side is exactly `virtualMultiplicity_diff_of_not_root`.

## Approaches explored (and why each fails to close)

This claim has resisted every "slick" workaround. Enumerated so the next
attempt doesn't rediscover them.

1. **Telescoping via the existing key equation.**
   `varBetween(der P) d c − varBetween(der Q) d c = v(P, c) − v(Q, c)`
   is the goal restated. Tautological.

2. **Strong induction on `P.natDegree`.** IH gives Lemma 2.48 for
   `Q = P'`, i.e. `v(Q, c) = varBetween(der Q) d c`, but the step from
   there to `v(P, c) = varBetween(der P) d c` reduces back to this
   claim. Circular.

3. **Iterated Prop 2.46(1) to `P^(k*)`.** Let
   `k* = min { k : P^(k)(c) ≠ 0 }`. When `k* ≥ 1`, root-case
   `virtualMultiplicity_derivative_of_root` applied `k*` times gives
   `v(P, c) = v(P^(k*), c) + k*`, and the prefix sign analysis cleanly
   shows `varBetween(der P) d c = varBetween(der P^(k*)) d c + k*`. So IH
   on `P^(k*)` (smaller degree) closes — **unless `k* = 0`**, which is
   exactly our case `P(c) ≠ 0`. Handles zero-prefix collapse, not the
   residual claim.

4. **Reduction via `(X − c) · P`.** `P̃ = (X − c) · P` satisfies
   `P̃(c) = 0`, so root case applies; however, `P̃'(x) = P(x) + (x − c)
   P'(x)` can vanish inside `[d, c)`, so the no-root hypothesis doesn't
   transfer to `P̃`. Dead end.

5. **Perturbation to `c' > c`.** Pick `c'` slightly right of `c` with
   no `P^(k)(c') = 0`. Then `v(P, c') = v(Q, c') = 0` by
   `virtualMultiplicity_eq_zero_of_no_derivative_root`, giving only the
   trivial equality `0 = 0`. No useful relation to `v(P, c) − v(Q, c)`.

6. **Uniqueness of argmin partition.** Constructing a candidate `xs'`
   from `ys` + inserting `c` and invoking `ArgminPartition.unique`
   requires knowing where to insert, which in turn requires the very
   count information we're trying to compute.

7. **Additivity of `varBetween` in `d`.** Shrinking `d → c⁻` (all on the
   root-free region) leaves `varBetween(der P) d c` constant because
   `varAt(der P)` is locally constant on a root-free region — so no new
   information.

The residual obstruction in every path is the **ν-odd sub-case**: the
trichotomy gives `v(P, c) − v(Q, c) ∈ {-1, 0, 1}`, and we need to
distinguish `+1` from `-1` using the *direction* of the sign of
`P(c) · P^(ν+1)(c)`. That directional information lives in the
argmin-chain structure.

## Proposed approach: argmin-chain recursion

Mirror `Internal.count_eq_of_root_from_aux` (at
[`Internal.lean:2306`](../Azurite/BasuPollackRoy/Chapter2/VirtualRoots/Internal.lean#L2306))
but replace the "root at `c` ⇒ argmin on `[v, y]` equals `c`" lemma with
a sign-based case analysis.

### Shape of the new internal lemma

```lean
private lemma count_diff_of_not_root_from_aux
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {ys_full : List R}
    (hys_full_sort : ys_full.Pairwise (· ≤ ·))
    (hsg_ys : SignConstantOnGaps (derivative P) ys_full)
    (hsg_xs : SignConstantOnGaps P xs_full)       -- likely needed
    {c : R} (hPc : P.eval c ≠ 0) :
    ∀ {xs ys : List R} {v : R} {past : List R},
      ys_full = past ++ ys →
      Interlaced xs ys →
      ArgminPartitionFrom P v xs ys →
      v ≤ c →
      (∀ p ∈ past, p ≤ v) →
      (xs.count c : ℤ) − (ys.count c : ℤ) = F(P, c)
```

where `F(P, c)` is the target sign formula. Since `F` is a *global*
constant (depends on `P`, `c` only, not on the local `xs`/`ys`), the
recursion preserves it as the invariant at every step.

### Recursion structure (cases at each step)

Induct on `ys` with side invariants as in `count_eq_of_root_from_aux`.
At the recursive step `ys = y :: ys'`, `xs = x₀ :: x₁ :: xs''`:

* **Case `c < y`** or **`c = y`**: the current interval `[v, y]`
  contains `c`. Sub-case-split on whether `x₀ = c`:
  - `x₀ = c`: contributes `+1` to the `xs`-count. If also `y = c`,
    contributes `+1` to `ys`-count; advance past both and recurse with
    residual formula.
  - `x₀ ≠ c`: `x₀` is an argmin on `[v, y]` at a point other than `c`.
    Use sign analysis (via `sign_const_of_argmin_strictMonoOn_Icc` and
    friends, plus the no-root-of-`Q`-in-gap assumption from
    `SignConstantOnGaps (derivative P)`) to argue `c` is *not* a virtual
    root of `P` in this interval. The formula target is the residual
    on `(x₁ :: xs'', ys')`.

* **Case `y < c`**: neither `x₀` nor `y` equals `c`, so advance past
  both without accumulating to the count, and recurse with `v ← y`.

### Key helper lemmas to write

1. **Argmin ⇒ critical point when `P(c) ≠ 0` and `c` is interior.**
   If `x₀ = c ∈ (v, y)` is an argmin of `|P|` on `[v, y]` with
   `P(c) ≠ 0`, then `P'(c) = 0`. Interior-argmin of `|P|` is a critical
   point of `|P|`, and `(|P|)' = sign(P) · P'`, so `P'(c) = 0`.

2. **Direction of `|P|` near `c` from the sign of `P(c) · Q^(ν+1)(c)`.**
   For `ν := rootMult(Q, c)`, Prop 2.21 gives the one-sided signs of
   `Q = P'` near `c`. Combined with the sign of `P` near `c`
   (constant because `P(c) ≠ 0`), determine whether `|P|` is locally
   minimised at `c` (argmin forced) vs. locally non-minimised
   (argmin forced away from `c`).

3. **Sign-on-argmin transfer between `P`-gaps and `Q`-gaps.** Tie the
   existing `sign_const_of_argmin_*` family to the specific shape
   `ArgminPartitionFrom` uses.

### Top-level public lemma

```lean
lemma count_diff_of_not_root
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {xs ys : List R}
    (hi : Interlaced xs ys)
    (hys_sort : ys.Pairwise (· ≤ ·))
    (harg : ArgminPartition P xs ys)
    (hsg_xs : SignConstantOnGaps P xs)
    (hsg_ys : SignConstantOnGaps (derivative P) ys)
    {c : R} (hPc : P.eval c ≠ 0) :
    (xs.count c : ℤ) − (ys.count c : ℤ) = F(P, c)
```

mirrors the structure of `count_eq_of_root` — one base match on
`ArgminPartition` shapes, then dispatch to the `_from_aux` version.

Wired into `virtualMultiplicity_diff_of_not_root` by extracting the five
properties of `virtualRoots` (see the call site of `count_eq_of_root` in
`virtualMultiplicity_derivative_of_root`).

## Effort and risks

- **Size.** Rough parity with `count_eq_of_root_from_aux` + helpers:
  ~200–300 lines of Lean.

- **Trickiest piece.** Helper lemma (2) — tying Prop 2.21 one-sided
  signs to the argmin structure on `[v, y]`. Some existing
  `sign_const_of_argmin_*` lemmas help but are phrased in terms of
  strict monotonicity of `P`, not directly in terms of iterated
  derivatives. Bridge carefully or add a new specialization.

- **Risk.** The recursion invariant `xs.count c − ys.count c = F`
  needs to survive all four case branches. Worth sanity-checking on
  one or two concrete worked examples before committing deeply
  (e.g. `P = X² + 1, c = 0` for ν-odd-positive; `P = X² − 1, c = 0` for
  ν-odd-negative).

- **Not risky but easy to slip.** `SignType.sign` algebra:
  `(-1)^ν · τ` matching `σ_P · τ` or its negation is where the
  `Even ν` / `Odd ν` dichotomy actually lands. The existing key
  equation `varBetween_der_succ_of_not_root_at_c` already has the
  pattern — reuse it verbatim.

## Invariant obstruction discovered (2026-04-24)

After filling the `y < c` recursive case and the `c < y, v < c` terminal
case, a **structural issue** was discovered that blocks the naïve
recursion at `c = y, x₀ ≠ c`.

### The issue

The recursion invariant
`(xs.count c : ℤ) − (ys.count c : ℤ) = nonRootDiffFormula P c`
is **not preserved** by every step of the recursion.

Worked example. `P = X² − 1, c = 0, ν = 1`. Formula = −1.
* Top level: `xs = [−1, 1]`, `ys = [0]`. LHS diff = `0 − 1 = −1 = formula`. ✓
* First step: `y = 0 = c`, `x₀ = −1 ≠ c`. This is the `c = y, x₀ ≠ c`
  case.
* Residual: `xs' = [1]`, `ys' = []`. Residual diff = `0 − 0 = 0 ≠ −1`.
* Invariant broken: the step consumed a `c` from `ys` but not from `xs`,
  so the residual diff differs from the formula by `+1`.

### Case-by-case preservation

* `y < c`: both `x₀ ≠ c` and `y ≠ c`. Diff unchanged. ✓ **Preserved.**
* `c = y, x₀ = c`: both drop by one; diff unchanged. ✓ **Preserved.**
* `c = y, x₀ ≠ c`: only `y` count drops by one; diff increases by one.
  ✗ **Not preserved.**
* `c < y` (terminal): computed directly.

### Secondary issue: `c < y, v = c`

Even in the terminal `c < y` case, a subcase `v = c` (entered from a
prior `y = c, x₀ = c` step) allows `x₀ = c` as a right-boundary argmin
on `[c, y]`. The formula value can then be `1` (ν odd, positive product)
**or** `0` (ν even ≥ 2, with `P` crossing monotonically through `c`).
`LHS = 𝟙(x₀ = c)` gives `1` in both cases — a mismatch when ν is even.

So the current aux lemma's target `(xs.count c) − (ys.count c) =
nonRootDiffFormula P c` is strictly a **top-level** statement, not a
statement about arbitrary sub-chain states.

## Revised approach

Two viable paths:

### Path A: offset-parameterised aux

Add a parameter `δ : ℤ` tracking "contribution consumed so far":

```
(xs.count c : ℤ) − (ys.count c : ℤ) = nonRootDiffFormula P c − δ
```

The top level supplies `δ = 0` in most cases, `δ = −1` when entering
from `c = y, x₀ ≠ c` (left-boundary consumed but unmatched).

Recursion preserves `δ` through `y < c` and `c = y, x₀ = c`, decrements
by 1 at `c = y, x₀ ≠ c`. Terminal cases compute the state-specific
value of `nonRootDiffFormula P c − δ` using sign helpers.

### Path B: terminal-block analysis

Keep the aux restricted to `y < c` recursion only. When first hitting
`c ≤ y` or `ys = nil`, dispatch to a separate lemma that processes the
**entire c-block** (all consecutive `c`s in `ys` plus boundary x-positions)
as a single unit using Helper (2) on both boundaries.

## Sequence of commits

Completed:

1. Helper (1) `deriv_eq_zero_of_isArgminAbsOn_interior`.
2. Helper (2) `rootMult_odd_and_sign_pos_of_isArgminAbsOn_interior`.
3. Skeleton of `count_diff_of_not_root_from_aux` with `nonRootDiffFormula`
   def. Three sorries.
4. Filled `y < c` recursive case (trivial: both x₀, y ≠ c).
5. Filled `c < y, v < c` terminal subcase (c strictly interior → ν = 0
   via `eval_ne_zero_of_not_mem_of_signConstantOnGaps`, formula = 0,
   Helper 1 gives x₀ ≠ c).

Remaining (three `sorry`s):

* **Base case `ys = nil`**, `xs = [z]`. `z` is argmin of `|P|` on
  `Set.Ici v`. Needs analysis of whether `z = c` against the formula
  value via Helper 2 and Prop 2.21 one-sided signs.
* **`c < y, v = c`** (right-boundary subcase). Needs right-boundary
  analog of Helper 2 OR absorption into an offset / terminal-block
  refactor.
* **`c = y`** (c-block case, `x₀ = c` and `x₀ ≠ c` subcases). Needs
  either the offset parameter (Path A) or the c-block lemma (Path B).

Plus the top-level `count_diff_of_not_root` wrapper and wiring into
`virtualMultiplicity_diff_of_not_root`.
