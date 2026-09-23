# APR-CL implementation plan

Target: a computable, proven primality test following the 1987 Cohen–A. K. Lenstra
algorithm (1.3), built on the formalized 1984 theory in `Azurite/CohenLenstra/`.

```lean
def aprclTest (n : AzNat) : Option Bool          -- some true / some false / none (gave up)
theorem aprclTest_true  : aprclTest n = some true  → n.toNat.Prime
theorem aprclTest_false : aprclTest n = some false → ¬ n.toNat.Prime
```

Both verdict theorems are unconditional; `none` covers every search that fails
(cap 50 on witness searches, no `q` in (1.3)(j), `t` beyond the table) and inputs
beyond the table capacity (`t ≤ 55440`, about 200 digits).  The pattern is the one
already used twice (`finiteFieldTest`, `gaussSumsTestO`).

Design decisions taken (revisit only if a phase shows a problem):

* **Ring model.** The cyclotomic computation ring is `AzPolyMod` over `AzZMod n` with
  modulus `Φ_{p^k}`, not a bespoke "cyclotomic field" type.  `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]`
  is a ring, not a field (even for prime `n` it is a product of fields), and
  `AzPolyMod` already has a computable `CommRing`, sliding-window powers, and the
  bridge `ringEquivAdjoinRoot` to Mathlib's `AdjoinRoot`; `cycM_quot_equiv` then
  identifies it with the abstract model `CycM`.  A dedicated coefficient-vector type
  with the `zeta_pow_eq_neg_sum` reduction is a Phase D optimization.
* **Flag route only.** Method (10.3) is used exactly as the paper does: `f = 1`
  (`flag_{p^k}`, `λ`-route (i2a)); the `n ≡ −1 mod p^k` analogue (4.6) is not built.
* **Generator/checker split.** All searches produce a certificate record; a
  deterministic checker recomputes the tables and verifies.  Only the checker is
  proven.  `aprclTest n = aprclCheck n (aprclGenerate n)`.
* **Final trial division** uses the size-tested variant `step5_prime_sqrt` (5.6)/(5.9)
  so Lenstra's `s > √n·t` idea can be switched on later without new proofs.
* **Out of scope for v1**: the `N^{1/3}` refinement (1.5) via `lenstraDivisors`,
  Remark (5.7)'s shrunken `s`, the `p ∣ n+1` speed-up (4.6), Winograd/Appendix
  formulae.

---

## Phase A — Computable primitives (each independently testable)

### A1. Cyclotomic ring `CycT n p k`
Files: `Azurite/AzPolyMod/Cyclotomic.lean`, `Azurite/AzPolyMod/Equiv/Cyclotomic.lean`.

1. `cyclotomicPrimePow p k : AzPolynomial (AzZMod n)` = `Σ_{i<p} X^(i·p^(k−1))`
   (generalizes `cyclotomicPrime`); monic `Fact` instance; degree `(p−1)p^(k−1)`.
2. `abbrev CycT n p k := AzPolyMod (cyclotomicPrimePow p k)`; `zetaT := ofPoly X`.
3. Bridge: `toPoly (cyclotomicPrimePow p k) = cyclotomic (p^k) (ZMod n)` via
   `cyclotomic_prime_pow_eq_sum` (Impl_6), so
   `CycT n p k ≃+* CycModN (p^k) n ≃+* CycM (p^k) ⧸ (n)`.  This is the single
   theorem every later congruence check passes through.
4. Operations with specs already proven abstractly:
   * `sigmaInvT (x) : CycT → CycT` on the coefficient array = `sigmaInvCoeff`
     (spec `sigmaInv_spec`, `sigmaN_sigmaInv`);
   * `findHT : CycT → Option ℕ` = `findH` on coefficients (spec `findH_spec`,
     corrected `h = l + m` in the second case);
   * `lambdaT (β : AzZMod n) : CycT → AzZMod n` Horner evaluation (spec
     `lambdaHom_sum`, `sub_mem_mKernel_iff`).
5. Guards: `p^k ∈ {3,4,5,7,8,9,11,16}`, small `n`; `zetaT^(p^k) = 1`; `sigmaInvT x
   (sigmaT x a) = a` on random `a`.

### A2. Quadratic ring `QuadT n u a`
Files: `Azurite/AzZMod/Quad.lean`, `Azurite/AzZMod/Equiv/Quad.lean`.

Pair structure `⟨x₀, x₁⟩` over `AzZMod n` with `mul` (general formula; the (4.9)
three-multiplication schemes `quadElt_mul_c1`/`_c2` as the two instances actually
used), `squareNormOne` (`quadElt_sq_of_quadNorm_one`), `norm` (`quadNorm`),
`conj`, `pow` via `slidingWindowPow` (generic `Mul`+`Square`, Remark (3.8)).
Bridge `toQuadRing : QuadT n u a → QuadRing (ZMod n) u a` sending `⟨x₀,x₁⟩` to
`quadElt u a x₀ x₁`, multiplicative by `quadElt_mul`; `norm` multiplicative by
`quadNorm_mul_coords`, so the norm-one squaring is legitimate along a power.
Norm-one candidate `(α+m)/(ᾱ+m)` by `norm_one_candidate_spec` +
`quadNorm_norm_one_candidate`, denominator inverse by `AzZMod.inv`
(`norm_one_denominator_isUnit`: a non-unit denominator is a composite verdict).

### A3. Jacobi symbol
File: `Azurite/AzNat/JacobiSym.lean` + `Equiv`.
Binary algorithm (factor out 2s, `(2/n)` by `n mod 8`, reciprocity flip by
`a mod 4, n mod 4`); ℕ reference + `AzNat` port; proof against Mathlib's
`jacobiSym` via `jacobiSym.quadratic_reciprocity`, `jacobiSym.at_two`,
`jacobiSym.mod_left`.  Needed by (4.4)(c2) and by the soundness hypotheses of
Test (4.3) and (4.10).

### A4. Tables (1.1)
File: `Azurite/CohenLenstra/Tables.lean` + `Equiv`.
1. `e t` is already computable (`Azurite.CL.e`); `qPrimes t` = primes `q` with
   `q−1 ∣ t` (guarded in Impl_7 against the paper's list).
2. Per `q`: least primitive root `g`; index table `f` with `1 − g^x = g^(f x)` by a
   discrete-log table in `UInt64`/`ℕ` (q ≤ 55441).  Certified by its defining
   property, not by how it was found.
3. `jacobiSumT (a b : ℕ) : CycT n p k` by the (1.1)(b2) incremental vector
   algorithm; correctness = `jacobiSum_eq_sum_gen_pow` (Algorithm_12_1) at
   `(1,1), (2,1), (3·2^(k−3), 2^(k−3))` for `j, j*, j#`, with the character
   `χ : MulChar (ZMod q) (CycM (p^k))`, `χ g = ζ` (`CycM` is a domain), pushed
   through the A1 bridge.  Reduction rule `zeta_pow_eq_neg_sum` (Impl_1_1).

### A5. Small helpers
`smoothPart`/`oddPrimeDivs` (Impl_7) rewritten on `AzNat` with the bitpacked sieve;
`qCost`, `s1`, `s2`, `selection_5_5` (Impl_5_1/5_2) ported from ℕ to `AzNat`
(spec-level correctness only needs `bigEnough`); `isPow` (done, `RootInt`).

---

## Phase B — Remaining mathematics (the long pole)

### B1. Lucas–Lehmer confinement with coherent exponents  →  (5.3), (4.1)
For each prime `r ∣ n` an `ε(r) ∈ {0,1}` (`= 1` iff `T² − uT − a` is irreducible mod
`r`, iff `(Δ/r) = −1`) such that
* `r ≡ 1 (mod p^{v_p(F)})` for `p ∣ f⁻` (done: Pocklington, `cond_6_4_of_test_4_2`);
* `r ≡ n^{ε(r)} (mod p^{v_p(F)})` for odd `p ∣ f⁺`: coordinate faithfulness of the
  norm-one element `x̄` in `A ⊗ ℤ/r` (unit coordinate from (4.4)(f) ⟹ `x̄^{(n+1)/p} ≠ 1`),
  order of `x̄` divides `r − 1` (split) or `r + 1` (irreducible), double-root case
  excluded by `p ∤ n`;
* 2-adic: parity-refined `proposition_7_24` (via `lemma_7_23`'s Legendre criterion)
  and `proposition_10_8` giving `l ≡ ε(r) (mod 2)`.
Then `proposition_10_7` at `f = 2`, `i ∈ {0,1}` gives (6.4) at odd `p ∣ f⁺`
(the `f⁺` half of Remark (4.5)), and the (4.1) early exit follows.

### B2. Generalized Theorem (6.3)
Hypotheses per `(r, p)`: one exponent `l_{r,p}` with the (6.5) character equations
for `q ∣ s₂`, `p ∣ q − 1`, and (6.4) modulo `p^{v_p(s)}`; coherence
`r ≡ n^{l_{r,2}} (mod p)` at odd `p ∣ s₁`; `n^{t'} ≡ 1 (mod s)` (proven:
`pow_modEq_one_s1_mul_s2`) replacing condition (2.3).  Conclusion (2.5).  Proof =
the existing `theorem_6_3` with `theorem_6_3_prime` refactored to take `q − 1 ∣ t'`
directly instead of `s ∣ e t`.

### B3. From the Jacobi-sum checks to the (6.5)/(6.4) inputs
* (i2b)/(i2a) pass `j₀^u·j_v ≡ ζ^h` ⟹ via Theorem (7.8)/(8.5)/(9.10)/(9.19) the
  per-`(p,q)` congruence `χ(r) = χ(n)^{l}` with one `l` per `(r,p)` across all `q`
  (the "χ(n) = η alignment" recorded in the ledger).
* (6.4) sources: flags (`beta_zero_of_cyclotomic`, `lambdaHom` route, (10.7) at
  `f = 1`), Lucas–Lehmer (`cond_6_4_two_of_c1/c2`, B1), (i3) `h ≢ 0 (mod p)`
  (Theorem (7.19)), (j)/(k) (`isPrimitiveRoot_chi_natCast`).
* **Completeness halves** (needed for every `some false`): for prime `n` an `h`
  exists in (i2) and (k) (the prime-case Jacobi-sum congruences), and `h` is unique
  by power-basis independence (`cycModN_dim`).  All other composite verdicts are
  already proven (Fermat, `prod = 0`, norm-one `x^{n+1} ≠ 1`, `α^{n+1} ≠ −1`,
  non-unit denominator, perfect power, trial division, MR).

### B4. Final trial division
`step5_prime_sqrt` (done) with `n^{t'} ≡ 1 (mod s)` bounding the loop.

---

## Phase C — The algorithm

### C1. Certificate and stage outcomes
```lean
structure AprclCert where
  B : ℕ                        -- trial division bound
  mrBases : List AzNat         -- (3.4) witnesses tried
  llWitnesses : List (ℕ × ℕ)   -- (4.2): (p, x) ; (4.3): (p, m) norm-one parameter
  c1a : Option ℕ               -- (4.4)(c1) prime a
  c2u : Option ℕ               -- (4.4)(c2) u
  t' : ℕ ; s2bar : List ℕ      -- (5.5) selection
  gens : List (ℕ × ℕ)          -- per q: primitive root g
  auxQ : List (ℕ × ℕ)          -- (j): per p, the auxiliary q
inductive Outcome (α) | fail | composite (witness : AzNat) | pass (a : α)
```
Stages: `trialDivision`, `mrStage`, `flags`, `lucasLehmer` (→ `β_{p^k}`, `F`),
`selectTS`, `jacobiStage` (per `p`, per `q`; records `h`, sets `λ_p`),
`additionalTests`, `finalTrialDivision`.  Each stage returns `Outcome`, and each has
one soundness theorem: `composite w → w ∣ n ∧ 1 < w < n` (or `¬ n.Prime` directly),
and `pass a → ⟨the mathematical data B needs⟩`.

### C2. Early milestone: Lucas–Lehmer-only proofs
Ship `aprclTest` first with the Jacobi stage stubbed to `fail`: primality by (4.1),
(4.12), BLS-style bounds from the C&P inventory (`corollary_4_1_4`, `morrison_test`,
Theorem 4.2.10).  Two-sided, proven, and already useful (the 247-digit example has
`F` of 22 digits so it does not qualify, but many test primes will).

### C3. Full assembly
Compose the stage theorems through B2 and `step5_prime_sqrt` into `aprclTest_true`;
`aprclTest_false` is the disjunction of the per-stage composite verdicts.

---

## Phase D — Performance and validation
1. Benchmarks against Table 2 ratios (Jacobi stage dominant, then final trial
   division, then Lucas–Lehmer); the 180- and 247-digit §7 primes as end-to-end tests
   (`prime247_2_892`, `prime180_table2`), Table 3 `h`-values with the least
   primitive roots, small primes cross-checked against `isPrime`.
2. `AzZMod` Montgomery multiplication (the (i2) `u`-th power dominates).
3. Dedicated `Φ_{p^k}` vector reduction; Karatsuba/Toom thresholds for degree
   `< 40` polynomials over `AzZMod`; compare with the Appendix operation counts
   (`p^k = 16`: 27 mul / 18 sq).
4. Lenstra's `s > √n·t` (5.9) once (5.6) is measured.

---

## Order of work and acceptance criteria
| Step | Deliverable | Done when |
|---|---|---|
| A1 | `CycT`, bridge, `sigmaInvT`, `findHT`, `lambdaT` | guards for all 8 `p^k`; axiom-clean bridge |
| A2 | `QuadT` + bridge | (4.4)(c2) check `α^{n+1} = −1` runs on 200-digit `n` |
| A3 | `jacobiSym` | `= Mathlib.jacobiSym` on `AzNat`, guards |
| A4 | tables | `jacobiSumT` matches `jacobiSum` for `q ≤ 61` by `decide`/guards |
| C2 | LL-only `aprclTest` | two-sided theorem; certifies primes with `F > n^{1/3}` |
| B1–B2 | confinement + generalized (6.3) | axiom-clean, blueprinted |
| B3 | alignment + completeness halves | axiom-clean |
| C3 | full `aprclTest` | `prime247_2_892 ↦ some true` end to end |
| D | tuning | Table-2 ratio profile; benchmark session with the user |

Recommended start: **A1** (this week's question), then A3 and A2 in parallel, then
C2 to get a shippable two-sided test early while B proceeds.

---

## Status log

* **2026-09-22** — A1 (`AzPolyMod/Cyclotomic`, `Equiv/Cyclotomic`), A2 (`AzZMod/Quad`,
  `Equiv/Quad`), A3 (`AzNat/JacobiSym`, `Equiv/JacobiSym`), A4
  (`CohenLenstra/Tables`) done, all axiom-clean and blueprinted.  The (4.3)/(4.4)/(4.10)
  verdict lemmas now take `u a : ZMod n` with a nonsquare-discriminant hypothesis
  (`not_isSquare_disc` recovers the Jacobi-symbol form).  A5 (AzNat ports of the
  §2/§5 helpers) pending.
* **Design fork for B1/C2 (open)**: the Lucas–Lehmer confinement with coherent exponents
  is *already proven* in Lucas-sequence form as C&P Theorem 4.2.10
  (`theorem_4_2_10`: every prime `r ∣ n` is `≡ 1` or `≡ n` mod `lcm F₁ F₂`), with the
  `n+1` side phrased through `lucasU`.  Test (4.3)'s norm-one powers are Lucas
  `V`/`U`-sequences with `Q = 1` (`x^k + x̄^k = V_k(tr x, 1)`), so either (i) bridge
  `QuadT` powers to `lucasU`/`lucasV` and reuse 4.2.10, or (ii) prove the ring-level
  confinement in `A ⊗ ℤ/r` directly as planned.  Decide before starting B1.
* **2026-09-22 (decisions)** — keep the generic `AzPolyMod` ring through Phase C; the
  Phase D list is: dedicated `Φ_{p^k}` reduction (the current `modByMonic` doubles every
  ring multiplication), lazy coefficient reduction + Montgomery in `AzZMod`, array-accumulated
  `jacobiSumT`, small-constant multiplications in `QuadT`, prime-only trial division with the
  (2.1) single reduction.  **Fork resolved: option (ii), ring-level.**  Test (4.3)'s
  condition (a *unit coordinate* of `x^{(n+1)/p} − 1`) is not the Lucas condition
  `gcd(U_{(n+1)/p}, n) = 1` (the constant coordinate can be a unit while `U` is not), so the
  4.2.10 bridge would change the test; instead prove the confinement in
  `A_r = (ℤ/r)[T]/(T² − uT − a)`: inert ⟹ `x^{r+1} = N(x)` (have it), split with distinct
  roots ⟹ `x^{r−1} = 1` via the two evaluation maps, ramified ⟹ `x^{2r} = 1` via
  `ε² = 0` and `add_pow_char`; the splitting type is the coherent `ε(r)`.
* **2026-09-22 (B1 base level done)** — `CohenLenstra/Impl_5_3.lean`: `normOne_pow_cases`
  (inert/split/ramified structure of `A_r`), `test_4_3_confinement` (odd `p`: `r ≡ n^{ε(r)}
  mod p^v`, `ε(r)` = inertness of `Δ` mod `r`), `c1_two_adic`/`c2_two_adic` (the 2-adic
  parity is the same `ε(r)`).  Next in B: the parity-forcing lemma for lifted exponents,
  (10.7) lifting to all levels, then B2 (generalized Theorem (6.3)).
* **2026-09-22 (B2 done)** — `CohenLenstra/Theorem_6_3_LL.lean`: `theorem_6_3_LL`, the
  generalized (6.3) for `s = s₁·s₂` with the LL base congruence + parity at `s₁`-primes and
  characters at `s₂`-primes.  Remaining in B: B3 (feed the per-(p,q) Jacobi checks and the
  (6.4) sources — flags, LL via (10.7) lifting, (i3)/(j)(k) — into `theorem_6_3_LL`'s
  hypotheses; completeness halves).
* **2026-09-22 (B3 done at the theorem level)** — `Impl_5_3_Lift.lean` (f⁺ (6.4) via (10.7);
  2-adic parity = ε(r)) and `Alignment.lean` (`chi_eq_chi_pow`: (7.8) outputs → (6.3) inputs
  with one exponent per (r,p)).  What remains of B is glue that belongs with the certificate
  in Phase C: per (p,q), `theorem_8_5`/(9.10)/(9.19) → `theorem_7_8` → `chi_eq_chi_pow`, the
  (6.4) sources by case, and the completeness halves.
* **2026-09-22 (C1/C2 milestone: Lucas–Lehmer stage shipped)** — `Azurite/APRCL/LucasLehmer.lean`
  (`Outcome`, `LLCert`, `test42`/`test43`/`ringParams`/`structOK`/`llStage`/`llCheck`, generator
  `llGenerate`, `llTest : AzNat → Option Bool`) + `Equiv/LucasLehmer.lean` (`llCheck_true`,
  `llCheck_false`, both 3-axiom).  Primality = `theorem_6_3_LL` at `s₁ = F, s₂ = 1, t' = 2` +
  `step5_prime`; the full 2-part of `n² − 1` needed strengthening `c2_two_adic` (inert clause
  `r ≡ n (mod 2^(v+1))`) and a (c1) pinning lemma.  Supporting: `map_slidingWindowPowAzNat`
  (transport of AzNat-exponent powers along a multiplicative map — `QuadT`/`NormOne.powAzNat`
  need no `Monoid`), `toQuad_powAzNat`, `alpha_powAzNat_card_succ`, `powAzNat_card_succ_eq_one`.
  Also fixed the vacuous `step5_prime`/`step5_prime_sqrt` sweep hypothesis (`j ≤ i` → `j < i`).
  Next: the Jacobi-sum stage certificate (per `(p, q)` chain → `chi_eq_chi_pow` → `theorem_6_3_LL`
  with `s₂ ≠ 1`), then `aprclTest` composing both stages, then A5 ports and Phase D.
* **2026-09-22 (C3: full APR-CL test shipped)** — `Azurite/APRCL/JacobiStage.lean` (per-`(p,q)`
  tests `jOdd`/`j2k1`/`j2k2`/`j2k3`/`jTest` in `CycT`, tables read as `J(χ^{x⁻¹}, χ^{x⁻¹})`
  directly instead of `σ_x⁻¹`), `Equiv/JacobiStage.lean` (each `some h` = `n ∣ W − ζ^h` in
  `ℤ[ζ_{p^k}]`), `Equiv/JacobiChain.lean` (common ring `ℤ[ζ_{q p^k}]`, `χ_R`, `ψ`, CRT-twisted
  `σ`, `(n)`; chains 8.5/9.1/9.3/9.5/9.10/9.19 → 7.8; 7.19 source), `Equiv/JacobiAlign.lean`
  (ℂ-characters `Yc`, `clause_odd`/`clause_two`), `Test.lean` (`Cert`, `aprclCheck`, `generate`,
  `aprclTest`), `Equiv/Test.lean` (`prime_of_aprcl`, `aprclCheck_true`/`_false`, all 3-axiom).
  Design: `s₁ = F` (not the (5.2) `s1 t' F` — the `t'`-lift is a refinement), `s₂ = ∏ q^e`
  with `n^t' ≡ 1 mod q^e` checked computationally, non-Wieferich check per odd `p` (needed for
  `a = b = 1` in Theorem 8.5), (6.4) sources LL / (7.18) / (7.19); not implemented: flags +
  `λ`-route (i2a), the (j)/(k) auxiliary-`q` tests, `n` a `p`-th power ⟹ composite, completeness
  halves (checker returns `none` where the paper says "composite" without proof here).
  Guards: 10^6+3, 10^18+3, 10^18+9 certified through the Jacobi stage.  Next: A5 ports and (5.5)
  selection as generator, then Phase D (dedicated Φ-reduction, Montgomery, benchmarks — ask first).
* **2026-09-22 (A5: (5.5) selection ported)** — `Azurite/APRCL/Select.lean`: `qExp`, `s2OfListAz`,
  `bigEnoughAz`, `s2barInitAz`, `pruneStepAz`/`pruneAz`, `procedureAz`, `selectionAz`,
  `certOfSelection`, `generateSel`, `aprclTestSel` (+ `aprclTestSel_true/false`).  Only the guard
  touches `n`.  `t` tried from `[2, 12, 60, 120, 720, 5040, 55440, 720720]`; 2^127−1 certified.
  Remaining generator-side ports (`smoothPart`/`oddPrimeDivs`/prime-only trial division with (2.1))
  are Phase D items together with the performance work.
* **2026-09-22 ((1.3)(j)/(k) additional tests + p-th-power verdict)** — `Cert.aux : List (p, q', g')`;
  `auxOK` (q' prime, `p ∣ q'−1`, `q' ∤ n`, certified g'/index table, `jOdd n p 1 q' f = some h`,
  `p ∤ h`) is a fourth (6.4) source in `sixFourOK` (sound via `sixFour_of_jOdd` = Theorem 7.19 at
  `k = 1`); `pCheck` returns `composite` when `n.isPow p` (`not_prime_of_eq_pow`); generator
  `findAux`/`generateAux` (q' = 2pm+1, m ≤ 50, `n^((q'−1)/p) ≢ 1 mod q'`).  Only the λ-route
  and the completeness halves remain unimplemented from (1.3).
* **2026-09-23 (Phase D, first round — benchmarks + three fixes)** — `benchmark aprcl` added
  (`Azurite/Benchmark/Aprcl.lean`: `digits:D` finds the next prime above 10^D and profiles
  generator/checker/stages, `paper:180|247`, `detail:1` per-(p,q), `prims:1` primitives).
  Baseline 247-digit paper prime: 94 s.  Fixes: (1) `indexTable` was a partially applied
  function rebuilding the discrete-log table per lookup (O(q²) each!) → `indexTableArr`
  materialized once + `indexTableOf` (41 digits: 28 s → 0.3 s); (2) `jacobiSumT` computed one
  sum per coefficient (O(m·q)) → `expCounts` one pass + `c_i − c_{m+(i mod P)}`, proven equal to
  the spec `jacobiSumTSum` (247: 94 → 66 s, tables now negligible); (3) `AzPolyMod/CycArith`:
  additive Φ-reduction `reduceCyc`, `cycMul`, wrapper `CycF`, `cycPow`, proven (`cycMul_eq`,
  `cycPow_eq`); all Jacobi-test powers routed through `cycPow` (ring mult 445 → 267 µs; 247:
  66 → 60 s).  Selection cost model → `testCost p k = m²` (no effect at 247 digits: t' = 65520
  forced by size).  Current: 21 digits 0.16 s, 41: 0.25 s, 101: 3.0 s, 180: 20 s, 247: 60 s;
  time = the u-th powers = AzZMod multiplication (2.2 µs mul + 4.3 µs mod at 13 limbs ≈ 13 ns per
  limb product, boxing-bound) — further speedups are AzNat codegen work (unboxed limbs /
  Montgomery), not APR-CL-specific.  Also remaining: λ-route (i2a) for flagged p^k, the (5.2)
  `s1 t' F` lift (theory already supports it), incremental `checkIndexTable`.
* **2026-09-23 (Phase D, second round)** — (4) `Algorithm/WindowPowAzNat.lean` + Equiv: fixed 5-bit
  window exponentiation for `AzNat` exponents (`windowPowAzNat_eq_pow`); `slidingWindowPowAzNat`
  was plain square-and-multiply (≈ s/2 extra multiplications). (5) `cycMul` now lazy: product over
  `AzNat` residues (`liftNat`), one reduction per product coefficient (`reduceCoeffs`), then
  `reduceCyc` — proofs via `toPoly_reduceCoeffs`/`toPoly_map_liftNat` (coefficient map along
  `ofAzNatRingHom`).  Corrected primitive probe (full-size operands): generic degree-12 mult
  1110 µs, cycMul 466 µs.  Timings: 101 digits 2.8 s, 180: 14.3 s, 247: 38 s (from 60), 301: 90 s
  (t' = 240240, 244 tests).  (6) Generator: factorization-based `divisorsFast`/`qPrimesFast`
  (`Nat.divisors` scans `[1, t]`), `t` candidates extended to 6983776800.  Remaining ideas, by
  payoff: dedicated squaring (symmetric products, ~25% of the powers); λ-route (i2a) for flagged
  `p^k` via the extension `Λ : ℤ[ζ_{q p^k}] → (ℤ/n)[y]/(Φ_q)`, `ζ_{p^k} ↦ β`, whose kernel is a
  σ-stable ideal meeting ℤ in nℤ (needs Φ_{q p^k}(β·y) = 0 in the target ring); the (5.2) `s₁`
  lift (~3%); AzNat multiplication (deferred by the user).
* **2026-09-23 (Phase D, third round)** — (7) `cycSquare`: symmetric square on the lifted `AzNat`
  polynomial (`coeffSq`/`squareNat`, `squareNat_eq_mul` via `sum_antidiagonal_symm`), the wrapper's
  `Square`; 247: 38 → 31.5 s.  (8) The (5.2) `s₁` lift: `liftedS1 cert t' = 2^(e₂+v₂(t')−1)·∏
  p^(e+v_p(t'))` in checker, generator and `prime_of_aprcl` (`pow_modEq_one_of_sq` Hensel lift;
  `p ∤ t'` keeps `v_p(s₁) = e`); with trial division to 10^6 (adaptive default `B`: 10^4/10^5/10^6
  by size) `s₁` = 80 bits at 247 digits and the selection takes `t' = 55440` — no degree-12 tests:
  247: 26.5 s (194 tests), 180: 12.3 s, 101: 2.3 s.  Deferred with design notes: λ-route (i2a)
  — estimated ≤ 8% for the 247-digit example (only `p = 7` and small `2^k` are flagged), needs the
  tower ring `ℤ[ζ_{p^k}][ζ_q]` as a domain (generalize `CycPQDomain` to `p^k`) and
  `Λ = AdjoinRoot.lift` twice into `CycModN q n`; AzNat multiplication (user-deferred).
* **2026-09-23 (Completeness of the Jacobi tests)** — `Azurite/APRCL/Equiv/Complete.lean`: for
  prime `n` coprime to `p q` every `jTest` returns `some h` (`jTest_isSome`; checker shape
  `jTest_isSome_of_checks` with certified generator/index table), so `qCheck` now returns
  `composite` when a Jacobi test finds no `h` (and checks `p ∤ n` per `p ∣ q−1` first: a proper
  `p ∣ n` is composite).  Proof: (1) descent `natCast_dvd_of_phiR_dvd` — `N ∣ φ(x)` in
  `ℤ[ζ_{q p^k}]` ⟹ `N ∣ x` in `ℤ[ζ_{p^k}]` (φ(ζ^i) = ζ^{qi}, `q·i < φ(q p^k)` since
  `φ(p^k) < q`, contents agree); (2) generic converse `exists_dvd_sub_zP_pow_of_identity` — from
  an exact identity `u·W·∏τ(χ^{Nx})^ν = (∏τ(χ^x)^ν)^N` (u a power of ζ_P, χ^x ≠ 1) and
  `corollary_7_5`, with Gauss sums units mod prime `N` (`isUnit_mk_gaussSum` via
  `tau_mul_tau_inv`), to `W ≡ ζ_P^h`; instances: odd `p` (`jacobi_tau_identity`), `p^k = 4`
  (the (9.3)/(9.5) identities re-derived from `eq_8_2` + `gaussSum_sq`), `k ≥ 3`
  (`jacobi_tau_identity_M2(_neg)` reindexed by `minv`); `p^k = 2` directly by Euler's criterion
  in `CycM 2`; (3) `findHT_complete`: `a = zetaT^h`, `h < p^k` ⟹ `findHT a` is `some`
  (`coeffT_ofCoeffFn`, `zetaT_pow_eq_ofCoeffFn`).  `Equiv/JacobiStage.lean` now exports the
  computed elements as `findHT (reduceCycT W)` (`jOdd_eq`, `j2k1_eq`, `j2k2_eq_one/three`,
  `j2k3_eq_low/high`); the `_spec` lemmas are one-liners from them.  Not proven (checker keeps
  `none`): the auxiliary route (k) with `p ∣ h`, and the two-sided statement "prime + valid
  certificate ⟹ `some true`" (would need completeness of the Lucas–Lehmer stage, of the (6.4)
  sources and of the final division).
