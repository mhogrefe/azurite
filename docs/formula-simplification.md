# Formula Simplification: Scaling Assessment

Architectural notes on `Azurite/AzFormula/` simplification — how the
current design scales as more rules are added, where it breaks down,
and what to change before investing in substantial new rules.

## Current architecture

Three layers cooperate to keep generated formulas small:

1. **Oracle pattern.** `isAzTrue` / `isAzFalse` are narrow syntactic
   predicates on atoms — they recognize `0 = 0`, `0 ≠ 0`, and nonzero
   constants.

2. **Smart constructors.** `azSmartAnd`, `azSmartOr` consult the oracle
   for each child and absorb trivial cases at construction time.
   `azConjList` / `azDisjList` extend this to lists.

3. **Post-pass `azSimplify`.** A composition of three normal-form
   passes: `elimTrivialAtoms ∘ elimVacuousQuantifiers ∘ elimDoubleNeg`.

Correctness is certified by two theorems per pass:
- `azRealization_*` — the pass preserves semantics.
- Certification via `isAzSimplified` — the pass produces a formula
  satisfying a boolean predicate that enumerates forbidden shapes.

## What scales well

**Strengthening the oracle is free.** Adding a new syntactic
triviality to `isAzTrue` / `isAzFalse` automatically benefits every
call site of the smart constructors, with no proof changes beyond the
oracle itself.

**Adding a post-pass is linear.** One new pass = one preservation
theorem + one clause in `isAzSimplified`. The composition in
`azSimplify` just grows by one more `∘`.

## Where it stops scaling

Looking at the Exercise 1.9 outputs — `P ≠ 0 ∨ P ≠ 0`,
`P = 0 ∧ P = 0`, `a ∧ (a = 0 ∨ a ≠ 0)`, `a ≠ 0 ∧ a = 0`, etc. — the
remaining redundancies fall into patterns the current design can't
express naturally:

1. **Pairwise/sibling reasoning.** Smart constructors ask a *unary*
   question per child ("are you trivial?"). Idempotence
   (`Φ ∨ Φ = Φ`) and contradiction (`Φ ∧ ¬Φ = ⊥`) are *binary* — they
   compare children to each other. Each new binary rule means a new
   comparison and a new smart-constructor clause. After a handful of
   these, the constructors become unreadable match ladders, and
   ordering matters (which rule fires first?).

2. **Non-local rules.** `a ∧ (a = 0 ∨ a ≠ 0)` requires looking
   *through* a child into a grandchild. Smart constructors are local
   by design — they can't see this without recursion, at which point
   they've become a separate pass.

3. **No fixpoint.** `azSimplify` runs its three passes once. With more
   rules, one pass often exposes opportunities for another — e.g.,
   contradiction elimination collapses a branch, which then unlocks
   vacuous-quantifier elimination. Without iteration, you get
   order-dependent residuals; with iteration, you owe a termination
   proof.

4. **`isAzSimplified` scales quadratically in case interactions.**
   It's a per-constructor enumeration of forbidden shapes. Every new
   rule adds a clause, and the certification proof
   `isAzSimplified_azSimplify` grows with the cross-product of case
   interactions. It's tractable for 3 rules; at 10+ it becomes the
   bottleneck.

5. **Construction-time performance.** Pairwise atom comparison
   requires `DecidableEq` on polynomials, which is `O(|support|)` per
   compare. If every smart constructor starts comparing siblings,
   formula-building cost inflates noticeably on the 11-disjunct /
   8-disjunct outputs we already produce — and much more on realistic
   inputs.

## Fault line

The switch point is when rules become *binary or non-local*.
Everything we can observe in the Exercise 1.9 outputs — idempotence,
pairwise contradiction, through-child tautology — sits on the wrong
side of that line.

The current design is sized right for ~3-5 more oracle-style rules
(syntactic atom-level trivialities, binder cleanup). For the
dozen-plus structural rules the current outputs suggest, the
smart-constructor / pass / predicate triad starts working against us.

## What to change before adding many rules

- **Canonicalize the polynomial inside each atom.** Before comparing
  atoms for equality, normalize each polynomial to a canonical
  representative: **primitive** (divide out the content), **squarefree**
  (divide by `gcd(P, P')`), and with a **positive leading coefficient**
  (negate if necessary). Under these normalizations, `P = 0` and
  `λ·P = 0` collapse to the same atom, `P = 0` and `P² = 0` collapse,
  and `P = 0` vs `(-P) = 0` collapse — all of which the Exercise 1.9
  outputs exhibit repeatedly (e.g. `-8*c = 0` vs `2*c ≠ 0`,
  `-2*a^2*c^3+8*b*c^4` vs `a^2*c-4*b*c^2`). This is an atom-level
  canonicalization: it must happen before any structural
  deduplication, since the structural layer compares atoms by syntactic
  equality. Preservation: `P = 0 ↔ normalize(P) = 0` is a standard
  fact (positive constant factor and positive power preserve zero set
  over a domain); the proof obligation is bounded and one-time.

- **Canonicalize atom lists.** Represent `∧` / `∨` chains as sorted,
  dedup'd lists of atoms, ordered by a polynomial ordering (we already
  have one). Idempotence and commutativity fall out of construction
  and need no rules.

- **Use `Ord`, not `LinearOrder`, for the polynomial comparator.**
  Sorting atom lists requires a total comparator on `AzMvPolynomial`
  and `AzPolynomial`. The right tool is Lean-core `Ord` — a pure
  comparator for data structures — not Mathlib's `LinearOrder`. A
  `LinearOrder` on polynomials has no algebraic meaning: `a ≤ b` on
  polynomials doesn't express divisibility, ideal containment, or
  degree. Mathlib deliberately omits `LinearOrder` on `MvPolynomial`
  and `Polynomial` for this reason; we should follow suit. `Ord`
  avoids the typeclass pollution (no `Lattice`, `max`, `sup`, …), is
  cheap to define, and is exactly what sort/dedup data structures
  consume. For `AzMvPolynomial n R ord`, the comparator is lex over
  sorted monomial-coefficient pairs, reusing the existing
  `MonomialOrder ord`. For `AzPolynomial R`, compare by degree, then
  coefficients from the top. Both require `[Ord R]` on the
  coefficient ring. A small `LawfulOrd`-style compatibility lemma
  with `DecidableEq` makes dedup correct. Add these instances
  alongside the canonicalization work, not speculatively — adding
  them early invites misuse in places where a total order on
  polynomials is meaningless.

- **Atom-set simplifier as a separate phase.** Operate on
  `(List eqAtoms, List neqAtoms)` per conjunction — detect
  `P ∈ eqAtoms ∧ P ∈ neqAtoms → ⊥`, detect subsumption across
  disjuncts, etc. Factoring this out keeps the Formula-level rewriter
  small.

- **Target a normal form, not a checklist.** `isAzSimplified` is
  currently "avoids bad shapes." Replace with "is in DNF of canonical
  atom sets" or a similar precise target. Then simplification has a
  concrete destination, and its certification is one theorem rather
  than a case-by-case enumeration.

- **If you want structural rewriting (absorption, distribution),
  build a fixpoint rewriter.** A single function `step : Formula →
  Formula` that applies one normalization, iterated until stable,
  with termination by a size measure. Each new rule is then one case
  in `step` + one lemma `realization_step`, not a new pass + new
  `isAzSimplified` clause + new preservation theorem.

- **Beyond syntactic reasoning.** Redundancies that require noting
  two polynomials are equivalent up to units, or that one ideal
  contains another, are beyond any purely syntactic simplifier. That
  is the boundary where Groebner / factoring / real-algebraic
  machinery takes over — out of scope for the simplification layer.

## Recommendation

Keep extending the oracle pattern opportunistically — it's cheap and
composable. But before investing in structural rules (idempotence,
absorption, pairwise contradiction), migrate `∧` / `∨` to sorted
canonical atom lists with a precise normal-form target. That one
structural change unlocks most of the observed redundancies for free
and gives subsequent rules a stable foundation to build on.
