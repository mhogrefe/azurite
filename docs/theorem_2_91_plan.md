# Plan: finishing Theorem 2.91 (`R⟨⟨ε⟩⟩` is real closed)

> ✅ **DONE.** `Azurite.BPR.isRealClosed_puiseuxSeries` (`Section2_6/Theorem_2_91Complete.lean`) is
> complete and axiom-clean. Parts A–D all landed; both the never-barrier (infinite `x̄`) and barrier
> (finite partial-sum) cases are handled. This doc is retained as a design record.

Status of the convergence core (the "(d)" wall). Everything finite is done and axiom-clean;
what remains is the infinite assembly. This doc de-risks it into concrete lemmas with the Mathlib
API and proof strategies.

## ✅ PROGRESS (all axiom-clean, building)

- **Part A** DONE: `stabilized_coeff_order` (`StabilizedStep.lean`) — single segment, `Q = c(X−x)^r`,
  `o(coeff (r−1)) = −newtonSlope = ξ`. Edge exposed through `recursion_step_neg` → `StepResult`
  (fields `edgeA/edgeB/colA/colB/xi_eq/beta_eq/next_mult_eq`, plus `xi_pos`).
- **Part B** DONE (`BoundedDenom.lean`, `BoundedSubst.lean`, `ChainBounded.lean`):
  `BoundedBy M` predicate + ring closure + `constPuiseux`/`puiseuxMonomial` membership +
  `boundedBy_puiseuxOrder_mem` (order extraction) + `boundedBy_substPoly` (substitution preserves)
  + `exists_boundedBy`. Chain invariant `stateSeq_boundedBy` (returns stabilization `hN` + bound).
  `stateSeq_xibeta_mem`: for `n ≥ N`, `ξₙ, βₙ ∈ (1/M)ℤ`.
- **η-sequence** DONE (`LimitSequence.lean`): `InLattice M q := ∃k, q = k/M` + closure +
  `inLattice_den`/`exists_inLattice_finset`. `etaSeq s0 n = Σ_{k≤n} ξₖ`; `strictMono_etaSeq`
  (under never-barrier `hnb`); `etaSeq_inLattice` (all `ηₙ ∈ (1/M)ℤ`, one fixed `M`).
- Positivity (`RootSequence.lean`): `xSeq_ne_zero`, `xiSeq_pos`, `betaSeq_pos` (under `hnb`);
  `step_xi_pos`.

### REMAINING: Part C (limit `x̄`) + Part D (telescoping + finish).

**Chosen route for C/D** (cleaner than raw ℚ-level `hsum`):
- Integer level: `γ n : ℤ` with `ηₙ = γₙ/M` (`Classical.choose` from `etaSeq_inLattice`); `γ`
  strictMono. `lfam : SummableFamily ℤ R ℕ`, `lfam n = single (γₙ) (xₙ)`; `z := lfam.hsum`.
  PWO of `range γ` via `wellFoundedOn_range` (relation `(·<·) on γ = (·<·)` by strictMono) +
  `Set.IsWF.isPWO`. `finite_co_support` via `γ` injective. `z.coeff (γₘ) = xₘ`.
- `x̄ := puiseuxEmb M z` ⇒ **membership free** (`∈ puiseuxSubfield M = (puiseuxEmb M).fieldRange`).
  `x̄` coeffs via `embDomain_coeff`/`embDomain_notin_range`; order via `orderTop_embDomain`
  (already used in `BoundedDenom`).
- Telescoping (ℚ/PuiseuxSeries level): tails `r_j := ε^{−η_{j-1}}·(x̄ − Σ_{n<j} xₙ ε^{ηₙ})`
  satisfy `r_j = ε^{ξ_j}(x_j + r_{j+1})` **by pure field algebra** (no hsum). `o(r_{j+1}) > 0`
  from `x̄` support `⊆ {ηₙ}` (integer-level `z` support `> γ_j`). Then `substPoly_eval` telescopes
  `P₀.eval x̄ = ε^{Σ_{k<j}βₖ}·P_j.eval r_j`; `step_order_jump` ⇒ `o > Σ_{k<j}βₖ → ∞` (`Σβ→∞`
  from `βₖ ≥ 1/M`, `k ≥ N`) ⇒ `o(P₀.eval x̄) = ⊤` ⇒ `P₀.eval x̄ = 0`. Barrier case = finite root
  via `substPoly_eval` at `y = 0`.

## 0. Where we are

`isRealClosed_puiseux_of_exists_root` reduces Theorem 2.91 to:

```
exists_root : ∀ {P : (R⟨⟨ε⟩⟩)[X]}, Odd P.natDegree → ∃ x, P.IsRoot x   -- [R real closed, ordered]
```

Done and axiom-clean (see `reference_puiseux_2_6.md` memory for full list):
- `recursion_step` (first step), `recursion_step_neg` (continuation: `r' ≤ r`, `β > 0`).
- `RecState` + `step` + `stateSeq`/`xSeq`/`xiSeq`/`betaSeq`; `stateSeq_mult_eventually_const`.
- `substPoly_natDegree` (degree preserved), `substPoly_eval` (`P(ε^ξ(x+y)) = ε^β P₁(y)`).
- `CharPolyDegree`: `natDegree = B.1`, `natTrailingDegree = A.1`, `rootMultiplicity ≤ B.1`.

The root we will produce: with `s₀` = the `RecState` from the bootstrap (`exists_initial_RecState`
applied to `P`), the chain `stateSeq s₀` gives data `(xₙ, ξₙ, βₙ)`. Set `ηₙ = Σ_{k≤n} ξₖ` (plus
the bootstrap `ξ₀`). The root is `x̄ = Σ xₙ ε^{ηₙ}`, and `P(x̄) = 0`.

## ⭐ Key de-risking insight (avoids Lemma 2.97 / "q eventually 1" entirely)

BPR proves bounded denominators via "q eventually 1" (a Newton-polygon-2.97 + `X¹`-coefficient
argument). **We can avoid all of it.** Once the multiplicity stabilizes at `r` (n ≥ N), the edge
must be the *single segment* `[0, r]` and `Q = c(X − x)^r`. Then **`ξₙ` is literally a coefficient
order**:

> `ξₙ = o(Pₙ.coeff (r−1))`.

Proof: edge `A = (0, βₙ)`, `B = (r, 0)`, so `newtonSlope A B = −βₙ/r` and `ξₙ = βₙ/r`. The line
value at column `r−1` is `lineValue A B (r−1) = βₙ + (−βₙ/r)(r−1) = βₙ/r = ξₙ`. From
`Q = c(X−x)^r` (with `x ≠ 0`), `Q.coeff (r−1) = c·r·(−x) ≠ 0`, so column `r−1` is **on the edge**
(`colOnLine`), giving `o(Pₙ.coeff (r−1)) = lineValue A B (r−1) = ξₙ`. (For `r = 1`, `r−1 = 0` and
`ξₙ = βₙ = o(Pₙ.coeff 0)`; works uniformly.)

Consequence: if all of `Pₙ`'s coefficients lie in `puiseuxSubfield M` (Laurent series in `ε^{1/M}`),
then `ξₙ = o(Pₙ.coeff (r−1)) ∈ (1/M)ℤ`, so the substitution `Pₙ₊₁ = substPoly Pₙ xₙ ξₙ βₙ` keeps
all coefficients in `puiseuxSubfield M` (closed under the ring ops + `ε^{±ξ}` with `ξ ∈ (1/M)ℤ`).
**The denominator stops growing — no `q`, no Lemma 2.97 needed.**

This replaces the hardest blocker with elementary facts about coefficient orders + subfield closure.

---

## Part A — Stabilization ⇒ single segment ⇒ `Q = c(X − x)^r`

### A1. `rootMultiplicity ≤ span` for a nonzero root  *(small)*
`OddMultiplicityRoot.lean` already has `Q = X^t · h` with `rootMult x Q = rootMult x h` for `x ≠ 0`.
Expose:
```
charPoly_rootMultiplicity_ne_zero_le_span :
  x ≠ 0 → (charPoly P A B).rootMultiplicity x ≤ B.1 - A.1
```
via `rootMult x Q = rootMult x h ≤ h.natDegree = natDegree − natTrailingDegree = B.1 − A.1`
(`charPoly_natDegree_eq`, `charPoly_natTrailingDegree_eq`).

### A2. Expose the edge in `recursion_step_neg`  *(medium refactor)*
Add outputs (or a parallel lemma `recursion_step_neg'`) returning the edge endpoints `A B` and:
`A.1 < B.1`, `B.1 ≤ r`, `newtonSlope A B < 0`, `colPoints`, and crucially
`r' = (charPoly P A B).rootMultiplicity x` with `r' ≤ B.1 − A.1` (A1) and `ξ = −newtonSlope A B`,
`β = A.2 + A.1·ξ`. (These are all already computed internally in `exists_neg_slope_odd_edge` /
`recursion_step_neg`; just thread them out.) Mirror into `StepResult` / `step`.

### A3. Single segment  *(small, given A1–A2)*
When `r' = r` (stabilization): `r = r' ≤ span = B.1 − A.1 ≤ B.1 ≤ r` forces `B.1 = r`, `A.1 = 0`,
`span = r`. `omega` after extracting the three `≤`.

### A4. `Q = c(X − x)^r`  *(medium)*
With `A.1 = 0`, `B.1 = r`: `Q.natDegree = r` (`charPoly_natDegree_eq`), and `rootMult x Q = r`.
Then `(X − C x)^r ∣ Q` (`pow_rootMultiplicity_dvd`) and `deg ((X−Cx)^r) = r = deg Q`, so the
cofactor is a constant `= leadingCoeff Q =: c ≠ 0`:
```
Q = C c * (X - C x) ^ r,   c ≠ 0.
```
Lemma to prove (general): `p ≠ 0 → p.natDegree = n → rootMultiplicity a p = n →
  p = C p.leadingCoeff * (X - C a)^n`. Use `eq_prod_roots`-style or: `q := p /ₘ (X-Ca)^n` is monic
of degree 0 hence `C (...)`; `leadingCoeff`. (Check Mathlib `Polynomial.eq_pow_rootMultiplicity_mul`,
`Polynomial.Monic.eq_one_of_...`, or do it by `natDegree`/`leadingCoeff` of the cofactor directly.)

### A5. Column `r−1` on the edge, `ξₙ = o(coeff (r−1))`  *(small, given A4)*
From A4: `Q.coeff (r−1) = c · (r.choose (r−1)) · (−x)^1 = c·r·(−x) ≠ 0` (need `coeff` of
`C c * (X − C x)^r`; use `Polynomial.coeff_C_mul` + a `(X - C a)^n` coeff lemma, e.g. via
`add_pow`/`coeff_X_sub_C_pow`, or just `Q.coeff (r−1) ≠ 0` from `natTrailingDegree = 0 < r−1 < r`
and the explicit binomial). Hence `r−1 ∈ filter` ⇒ `colOnLine P A B (r−1)` ⇒
`o(P.coeff (r−1)) = ↑(lineValue A B (r−1)) = ↑ξ` (the de-risking insight). Edge case `r = 1`:
use `colOnLine_left` (column `0 = A.1` is on its own edge), `ξ = β = o(coeff 0)`.

**Deliverable of Part A:** a lemma usable at stabilized steps:
```
stabilized_step : (stateSeq s₀ n).mult = r → r ≤ (stateSeq s₀ n).mult → n ≥ N →
  (xiSeq s₀ n) = (the order o((stateSeq s₀ n).poly.coeff (r-1)))   -- ∈ ℚ, equals a coeff order
```

---

## Part B — Bounded denominators (the `puiseuxSubfield M` invariant)

### B1. `puiseuxMonomial ξ ∈ puiseuxSubfield M`  *(small)*
`puiseuxMonomial ξ = single ξ 1`. Generalize `single_mem_puiseux`: `single ξ c ∈ puiseuxSubfield M`
iff `M • ξ ∈ ℤ` (i.e. `ξ.den ∣ M`). For our use `ξ ∈ (1/M)ℤ ⇒ puiseuxMonomial ξ ∈ puiseuxSubfield M`.
Also `constPuiseux x ∈ puiseuxSubfield M` (exponent 0).

### B2. Coefficient order lives in `(1/M)ℤ`  *(small)*
If `a ∈ puiseuxSubfield M` and `a ≠ 0`, then `HahnSeries.order ↑a ∈ (1/M)ℤ`
(`a = puiseuxEmb M a'`, `order = a'.order / M`). State: `∃ k : ℤ, colOrd P i = k / M` or
`(colOrd P i) * M ∈ ℤ`. Combined with A5: `ξₙ * M ∈ ℤ`.

### B3. `substPoly` preserves `(puiseuxSubfield M)[X]`  *(medium)*
Cleanest via `Polynomial.map`: if `P = P♭.map (puiseuxSubfield M).subtype` for some
`P♭ : (puiseuxSubfield M)[X]`, and `ξ, β ∈ (1/M)ℤ`, `x ∈ R`, then
`substPoly P x ξ β = (substPoly-over-the-subfield).map (...).subtype`. Because `substPoly` is built
from `C`, `comp`, `*`, `X` (all commute with `Polynomial.map` of a ring hom) and the scalars
`puiseuxMonomial (±·)`, `constPuiseux x` are in the subfield (B1). So every coefficient of
`substPoly P …` is in `puiseuxSubfield M`. (Alternatively: prove directly `∀ i, (substPoly P x ξ β).coeff i
∈ puiseuxSubfield M` by the `substPoly_coeff` sum formula — every summand is a product of subfield
elements.)

### B4. The invariant along the chain, from step `N` on  *(medium)*
Pick `M₀` = a common denominator for the (finitely many) coefficients of `(stateSeq s₀ N).poly`
(each coeff is some Puiseux series ∈ `puiseuxSubfield qᵢ`; `M₀ = lcm qᵢ`). Then by induction for
`n ≥ N`: all coeffs of `(stateSeq s₀ n).poly ∈ puiseuxSubfield M₀` ⇒ (A5,B2) `ξₙ ∈ (1/M₀)ℤ` ⇒ (B3)
all coeffs of `(stateSeq s₀ (n+1)).poly ∈ puiseuxSubfield M₀`. Also `βₙ = o(coeff 0) ∈ (1/M₀)ℤ`.
**Conclusion:** for `n ≥ N`, `ξₙ, βₙ ∈ (1/M₀)ℤ` and `βₙ > 0` ⇒ `βₙ ≥ 1/M₀`.

### B5. `ηₙ` bounded denominator; `Σβ → ∞`  *(small)*
`ηₙ = Σ_{k} ξₖ`; the finitely many `k < N` contribute denominators `dₖ`, the rest `∈ (1/M₀)ℤ`. So
all `ηₙ ∈ (1/M)ℤ` with `M = lcm(M₀, d₀, …, d_{N-1})`. And `Σ_{k≤n} βₖ ≥ (n−N)/M₀ → ∞` (B4).

---

## Part C — The limit `x̄ ∈ R⟨⟨ε⟩⟩`

Use `HahnSeries.SummableFamily` (Mathlib `RingTheory/HahnSeries/Summable.lean`).

### C1. The family  *(medium)*
`fam : SummableFamily ℚ R ℕ`, `fam n = constPuiseux-coeff xₙ • single ηₙ 1` (i.e. `xₙ ε^{ηₙ}` as a
`HahnSeries ℚ R`). Obligations:
- `isPWO_iUnion_support`: `⋃ₙ support(fam n) ⊆ {ηₙ : n}`. `ηₙ` is strictly increasing (`ξₖ > 0` for
  `k ≥ 1`; handle the possibly-nonpositive bootstrap `ξ₀` by starting `η` at the first continuation),
  so the set is well-ordered ⇒ PWO. (`Set.IsWF` of a strictly-mono ℕ-indexed set; or
  `Set.IsPWO` from order embedding of ℕ.)
- `finite_co_support g`: `(fam n).coeff g ≠ 0` ⇒ `g = ηₙ`; `η` injective (strict mono) ⇒ at most one
  `n`. So the support is `{the unique n}` or `∅` — finite.

`x̄ := fam.hsum : HahnSeries ℚ R`, with `x̄.coeff (ηₙ) = xₙ` and `x̄.coeff g = 0` off `{ηₙ}`
(`coeff_hsum`, `finite_co_support`).

### C2. `x̄ ∈ PuiseuxSeries R`  *(small, given B5 + C1)*
`support x̄ ⊆ {ηₙ} ⊆ (1/M)ℤ` (B5) ⇒ `x̄ ∈ puiseuxSubfield M` (`mem_puiseuxSeries_iff`: the
exponent-`/M` embedding hits exactly the `(1/M)ℤ`-supported series). So `x̄ : PuiseuxSeries R`.

### C3. Tail identity  *(medium)*
`t_j := Σ_{n > j} xₙ ε^{ηₙ − η_j}` (another `hsum`, or `ε^{−η_j} · (x̄ − partialSum_j)`). Prove
`o(t_j) > 0` (its support `⊆ {ηₙ − η_j : n > j} ⊆ (0, ∞)` since `η` strictly increasing) and the
recursion `t_j = ε^{ξ_{j+1}}(constPuiseux x_{j+1} + t_{j+1})` (factor `ε^{η_{j+1}−η_j} = ε^{ξ_{j+1}}`).
Also `x̄ = ε^{ξ₀}(constPuiseux x₀ + t₀)` (or the bootstrap analogue).

---

## Part D — `P(x̄) = 0` and the finish

### D1. Telescoping  *(medium)*
By induction on `j`, using `substPoly_eval` and `(stateSeq …).step_props.next_poly`:
```
P.eval x̄ = puiseuxMonomial (Σ_{k≤j} βₖ) * (stateSeq s₀ j).poly.eval (t_j).
```
(`substPoly_eval` peels one factor: `Pₖ.eval(ε^{ξ}(xₖ + tₖ)) = ε^{βₖ} Pₖ₊₁.eval(tₖ)`; the inner
arg equals `t_{k-1}` by C3.)

### D2. `o(P(x̄)) = ∞`  *(small)*
`o(P.eval x̄) = (Σ_{k≤j} βₖ) + o(Pⱼ.eval(tⱼ))`. From `step_order_jump` (Lemma 2.95b) with
`y = t_j`, `o(Pⱼ.eval(tⱼ)) > β_{j+1} > 0`, so `o(P.eval x̄) > Σ_{k≤j} βₖ → ∞` (B5). Hence
`o(P.eval x̄) = ⊤`, i.e. `P.eval x̄ = 0`.

### D3. Barrier case  *(small)*
If the chain hits `(stateSeq s₀ n).poly.coeff 0 = 0` at some `n`, the construction is finite:
`substPoly_eval` at `y = 0` gives `P.eval (partial root) = ε^{Σβ} · Pₙ.eval 0 = ε^{Σβ} · (coeff 0) = 0`.
So the finite partial sum is an exact root. (Decide barrier-vs-forever by `Classical`.)

### D4. Assemble  *(small)*
`exists_root P (Odd P.natDegree)`: bootstrap to `s₀`; case on barrier-ever:
- barrier at some `n` ⇒ D3 finite root;
- never ⇒ D1+D2 give `P.eval x̄ = 0` (need `x̄ ≠ 0`? No — `IsRoot` only needs `eval = 0`; but the
  produced root must witness `∃ x, P.IsRoot x`, which `x̄` does).
Then `isRealClosed_puiseux_of_exists_root exists_root` ⇒ **Theorem 2.91**. Also handle `X ∣ P`
(constant term zero) at the very top: `0` is a root, or factor; the recursion needs `P.coeff 0 ≠ 0`.

---

## Mathlib API checklist (verify before each part)

- `Polynomial.eq_pow_rootMultiplicity_mul`, `pow_rootMultiplicity_dvd`, `natDegree_le_of_dvd`,
  `Polynomial.coeff_X_sub_C_pow`/`add_pow` (A4, A5). ✅ `pow_rootMultiplicity_dvd`, `natDegree_le_of_dvd` present.
- `HahnSeries.SummableFamily`, `.hsum`, `coeff_hsum`, `support_hsum_subset`, `single`,
  `finite_co_support`, `isPWO_iUnion_support` (C). ✅ present in `HahnSeries/Summable.lean`.
- `mem_puiseuxSeries_iff`, `puiseuxSubfield`, `puiseuxEmb`, `single_mem_puiseux` (B,C). ✅ ours.
- `HahnSeries.order_le_of_coeff_ne_zero`, `order_eq_orderTop_of_ne_zero` (B2). ✅ used already.
- `Set.IsPWO` of a strictly monotone ℕ-image / `Set.IsWF` (C1) — check
  `Set.IsWF`/`StrictMono.isPWO`-style lemmas.

## Suggested order & risk

1. **A1–A5** (single segment + `Q = c(X−x)^r` + `ξₙ = o(coeff(r−1))`). Tractable; the only refactor
   is exposing the edge from `recursion_step_neg` (A2). *Low–medium risk.*
2. **B1–B5** (subfield invariant ⇒ bounded denom + `Σβ → ∞`). The de-risked path; mostly subfield
   closure bookkeeping. *Medium risk* (B3 map-commutation is the fiddly bit; fallback = direct
   `substPoly_coeff` sum).
3. **C1–C3** (`SummableFamily` limit). New `HahnSeries` work but the infra exists. *Medium risk*
   (PWO of `{ηₙ}`, the tail identity C3).
4. **D1–D4** (telescoping + finish). Mostly mechanical given A–C. *Low risk.*

The previously-feared blockers (Lemma-2.97 `q`-tracking, the `X¹`-coefficient argument) are
**eliminated** by the `ξₙ = o(coeff(r−1))` insight. The remaining genuinely-new pieces are the
subfield-closure bookkeeping (B3) and the `SummableFamily` limit + tail identity (C1, C3).
