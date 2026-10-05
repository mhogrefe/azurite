# Plan: `AzFloat`, arbitrary-precision binary floating point

Status: started 2026-10-01; see the status log at the end.

## Provenance rules (important)

* The **representation** follows the author's own Malachite `Float` (`malachite-float`): a
  sign, an exponent, a precision, and a limb-aligned significand, with `NaN`, `±∞` and zero as
  separate constructors.  That layout may be used as a template.
* **No algorithm may be ported from `malachite-float`.**  Its arithmetic is largely ported from
  MPFR, which is off limits for Azurite like GMP (`docs/bibliography.md`).  Every `AzFloat`
  operation is derived from first principles or from public descriptions, chiefly Brent and
  Zimmermann, *Modern Computer Arithmetic* (MCA), Chapter 3 (floating-point arithmetic).  Each
  operation's docstring and this plan record its source.
* MCA text is supplied by the author in reformatted chunks on request (the raw PDF copy mangles
  the mathematics); nothing is read from the PDF directly.
* Expected values in tests are computed independently (by hand or by exact rational
  arithmetic), not copied from `malachite-float`'s tests.

## Design decisions

| Question | Decision | Why |
|---|---|---|
| Exponent type | `AzInt`, unbounded | Author's requirement: no minimum or maximum exponent, hence no overflow, no underflow, no subnormals.  A huge exponent costs a few limbs, not a huge significand; Lean's `Int` would silently use its own big-number arithmetic for such exponents. |
| Precision type | `Nat` | Bounded by the significand's bit length, so always a small scalar; `Nat` avoids `UInt64` wraparound side conditions in proofs and an `AzNat` would be pure overhead. |
| Significand layout | left-aligned at a limb boundary: bit length `alignedBits p = 64·⌈p/64⌉`, low `alignedBits p − p` bits zero, top bit set | Comparisons and same-exponent additions work limb by limb from the top with no shift; multiplication renormalizes by at most one bit and rounds at a fixed position in the lowest limb; precision changes within a limb count are masks.  The price is the invariant `FiniteValid`, established once in `mkFinite`. |
| Exponent convention | `2^(e−1) ≤ |x| < 2^e`, i.e. `e = ⌊log₂ |x|⌋ + 1`; value `± m · 2^(e − m.size)` | Malachite's convention; `1.0` has exponent `1`. |
| Negative zero | **none** | Its IEEE 754 purpose is to remember the sign of a value that underflowed to zero; with an unbounded exponent nothing underflows (a nonzero value rounded to any positive precision is nonzero).  Dropping it removes a case from every operation's sign rules and makes the value model faithful. |
| `NaN` and `±∞` | kept | `x / 0`, `∞ − ∞`, `0 · ∞`, `√(−1)` and friends need them; `NaN` is also the result for a zero precision. |
| Value model | `toVal : AzFloat → Option EReal` (`none` = `NaN`, `⊤`/`⊥` = `±∞`) | `Option EReal` is enough: `NaN` propagation is `Option.bind`, and the exceptional cases of each operation are stated by its specification function, not by `EReal`'s conventions (Mathlib has `⊤ + ⊥ = ⊥`).  A dedicated inductive would be isomorphic and lose the library. |
| Rounding target | `floatSet p` = values of the precision-`p` floats = `precisionSet 2 p ∪ {⊤, ⊥}` (`AzFloat/Equiv/Rounding.lean`, `Rounding/SciPrecision.lean`) | The numbers with at most `p` significant bits are exactly the precision-`p` floats of unbounded exponent, so every correctly rounded operation is specified as `round (floatSet p) mode (exact result)`, which agrees with `precisionSet 2 p` on reals.  Nearest ties go to even. |
| Lifting | `lift (f : ℝ → ℝ) (top bot := none) : AzFloat → (p) → mode → AzFloat × Ordering`, via `roundVal p mode : Option EReal → AzFloat × Ordering` and `liftVal` on `EReal → Option EReal` (binary: `lift₂`, `liftVal₂`) | Every operation is *specified* as a lift (`op x p mode = lift f … x p mode`, as `neg_eq_lift`) and *implemented* computably; the `Ordering` is the comparison of the rounded result with the exact value, `eq` for `NaN` and infinities. `floatSet p` is a `SymmetricRoundingTarget` (the precision tiebreak was made symmetric for this), so `round_neg` is available for sign arguments. |
| Noncomputable rounding | `ofEReal p mode : EReal → AzFloat`, `ofVal p mode : Option EReal → AzFloat` | The specification-side inverse of `toVal`: the float of precision `p` with the rounded value (`±∞` stay, `none ↦ nan`).  The representation of a value at a precision is unique (`toVal_injective`), so computable operations can be proven *equal* to `ofVal` of their specification, not just equal in value (`ofAzRatRound_eq_ofEReal`). |

## Milestones

1. **Core (done).**  `AzFloat/Basic.lean`: the type, `FiniteValid`, `alignedBits`, the smart
   constructor `mkFinite` (left-aligns a significand of at most the requested precision; zero
   significand gives `zero`), classification, accessors, `neg`/`abs`, constants
   (`powerOf2`, `one`, `two`, `oneHalf`, …).  `AzFloat/Conversion.lean`: `ofAzNat`, `ofAzInt`
   (exact), `ofAzRatRound`/`ofAzRat` (first principles: with `e = ⌊log₂ |q|⌋` the significand is
   the integer rounding of `q · 2^(p−1−e)`, one signed division via `AzRat.scaledRound`; a carry
   to `2^p` is halved with the exponent raised), `toAzRat?`.  Proofs: `toVal_mkFinite`,
   `toVal_neg`, `toVal_abs`, `toVal_ofAzNat`, `toVal_ofAzInt`, `toVal_of_toAzRat?`,
   `toVal_ofAzRatRound` (`= round (precisionSet 2 p) mode (toRat q)`), `precision?_ofAzRatRound`,
   `snd_ofAzRatRound`.  Tests `AzFloat/Tests/Basic.lean`.  `AzFloat/Equiv/Rounding.lean`: the
   target `floatSet p` with its `RoundingTarget` instance and `val_round_floatSet`, the
   noncomputable `ofEReal`/`ofVal`, `toVal_injective`, `ofAzRatRound_eq_ofEReal`, `ofVal_toVal`.
2. **Precision and comparison (done).**  `AzFloat/Precision.lean`: `setPrecRound x p mode`
   (raising the precision re-aligns the padding-free significand; lowering it is one signed
   `AzInt.shiftRightRound`, carry to `2^p` halved), `setPrec`, `ulp?`; proven
   `setPrecRound_eq_liftE : setPrecRound x p mode = liftE id x p mode` through the reusable
   `normalize_spec`.  `AzFloat/Compare.lean`: `partialCompare` (exponents, then limb-padded
   significands), `eqIEEE`/`lt`/`le`/`gt`/`ge`; proven `partialCompare_eq` (comparison of the
   values, `none` iff a `NaN` is involved).  Structural `=` keeps seeing the precision; no
   `LT`/`LE` instances, since `NaN` makes the relations irreflexive.  `min`/`max` deferred to
   the arithmetic milestone.  Tests `AzFloat/Tests/Precision.lean`.
2b. **Shifts (done).**  `AzFloat/Shift.lean`: `shiftLeft`/`shiftRight` by an `AzInt` (and `Nat`)
   move the exponent only — exact with an unbounded exponent; proven `toVal_shiftLeft` and
   `shiftLeft_eq_liftE`.
3. **Addition and subtraction (done)** (MCA §3.2.1 Algorithm FPadd and §3.2.2 as supplied,
   reorganized).  `AzFloat/Add.lean` (primitive in `RoundScaled.lean`): `roundScaled s S w p mode` rounds the exact
   `±S · 2^w` once (no round/sticky/round2 bookkeeping, no double rounding).  With `B` the larger
   magnitude, `T = max(p_B, p)` and gap `G = e_B − e_C`: in the **near** case (`G ≤ T + 1`) the sum
   or difference is formed exactly on the common scale `min(ulp B, ulp C)` and rounded, which
   also covers cancellation (the exact difference is short; Sterbenz comes for free); in the
   **far** case (`G ≥ T + 2`) `C < 2^(e_B − T − 2)`, so `B ± C` lies in an open cell of width
   `2^(e_B − T − 2)` containing no precision-`p` grid point or midpoint (even below a power of
   two), and the representative `8 B ± 2^(e_B − T − 3)` rounds the same way.  `addPrecRound`,
   `subPrecRound` (`x + (−y)`), `Add`/`Sub` instances at the larger operand precision.  Proven
   (`Equiv/Add.lean`): `addPrecRound_eq_liftVal₂ : addPrecRound x y p mode = liftVal₂ Spec.add
   x y p mode` and `subPrecRound_eq_liftVal₂`, where `Spec.add a b` is `EReal` addition with
   `∞ + (−∞) = none`.  Tests `AzFloat/Tests/Add.lean`.
4. **Multiplication, squaring, division, square root (done)** (MCA §3.3–§3.5 as supplied): `mulPrecRound x y p mode` multiplies the two cores in full and rounds once with
   `roundScaled` on the scale `(e₁ − p₁) + (e₂ − p₂)` (MCA Algorithm FPmultiply without the
   `n + g` truncation; the short product of Algorithm 3.4 is only an approximation and is left
   for a later performance pass); `sqrPrecRound` uses `AzNat.square`; `0 · (±∞)` is `NaN`, the
   sign of an infinite product is the product of the signs; `Mul` instance at the larger
   operand precision, `sqr` at the operand's.  Proven: `mulPrecRound_eq_liftVal₂` with
   `Spec.mul` (`EReal` multiplication, `0 · (±∞)` undefined) and
   `sqrPrecRound_eq_liftE : sqrPrecRound x p mode = liftE (fun v => v * v) x p mode`.
   `divPrecRound x y p mode` (MCA §3.4.2, the single-division reduction): with `g = p + p₂ − p₁`,
   or one less when `n₁ / 2^p₁ ≥ n₂ / 2^p₂` (one `compareMagnitude` of the aligned significands),
   the quotient `n₁ · 2^g / n₂` lies in `[2^(p−1), 2^p)`, so one `AzInt.divRound` of the shifted
   cores gives the `p`-bit significand and the comparison tag from the remainder, and
   `normalizeCarry` handles a carry to `2^p`; `∞ / ∞` and `0 / 0` are `NaN`, `x / 0 = ±∞` with
   the sign of `x`, `x / ∞ = 0`; `Div` instance.  Proven `divPrecRound_eq_liftVal₂` with
   `Spec.div` (`EReal` division except `a / 0 = ±∞`).  The approximate methods of §3.4 (Newton
   reciprocal with the wrap-around trick, DivideNewton, ShortDivision, Barrett) all need a
   correction step before they round correctly and were not used; the truncated division of
   Lemma 3.10 with a full-width remainder correction is the planned fast path for operands much
   wider than the result.  `sqrtPrecRound x p mode` (MCA §3.5 Algorithm FPSqrt, extended to
   nearest per Exercise 3.14): with `e − q = t + 2w`, `t = 2p − q − (e mod 2)`, the scaled
   significand `M = n · 2^t` lies in `[2^(2p−2), 2^(2p))`, so `s = ⌊√⌊M⌋⌋` (`AzNat.sqrtRem`) has
   `p` bits; exactness is "remainder zero and no bits shifted out", the midpoint test is the
   exact integer comparison of `4M` with `(2s + 1)²`, and `roundFromFloor` turns the three facts
   into the rounded integer and the tag in every mode; negatives (and `−∞`) give `NaN`,
   `√∞ = ∞`; `sqrt` at the operand's precision.  Proven `sqrtPrecRound_eq_liftVal` with
   `Spec.sqrt` (`EReal` square root, undefined on negatives), through the reusable
   `roundFromFloor_spec` (integer rounding of a real from its floor, exactness and midpoint
   position) and `scaled_floor`.
   Reciprocal square root (MCA §3.5.1; the Newton iteration of Algorithm 3.9 with the bound of
   Lemma 3.15 is an approximation kept for a later performance path): `rsqrtPrecRound x p mode`
   scales so that `√(2^D / n)` has exactly `p` bits — `D = 2p + q − 2` for even `e`, `2p + q − 1`
   for odd `e`, `2p + q − 3` when `e` is odd and `n = 2^(q−1)` (then `x` is an even power of two
   and the result's exponent is one higher) — takes `⌊√⌊2^D / n⌋⌋`, decides exactness by
   `s² n = 2^D` and the midpoint by `2^(D+2) ⋚ (2s+1)² n`, and rounds with `roundFromFloor`;
   `0 ↦ +∞`, `+∞ ↦ 0`, negatives `NaN`; `rsqrt` at the operand's precision.  Proven
   `rsqrtPrecRound_eq_liftVal` with `Spec.rsqrt`.
4b. **Hexadecimal debug format (done).**  `AzFloat/HexString.lean`: `toHexString`/`ofHexString`,
   the author's Malachite `{:#x}` of a `ComparableFloat` (`0x0.8#5`); proven
   `ofHexString_toHexString : ofHexString (toHexString x) = some x` for every float.
4c. **Decimal output (done).**  `AzFloat/ToString.lean`: `toDecimalString`, the shortest
   round-tripping decimal (smallest `p` whose nearest `p`-digit decimal converts back to the
   float at its precision; exponential-then-binary search), with `toDecimalAt`; proofs of the
   search and of the rendering's value in `Equiv/ToString.lean`.  The bound
   `⌈P·log₁₀ 2⌉ + 2` is checked at run time, not formalized.
5. **Conversions and text (done).**  Text input: `ofDecimalStringRound s p mode` reads the
   language of `AzRat.fromSci` (sign, digits, optional point, optional `e` exponent) plus the
   special spellings `NaN`, `Infinity`, `-Infinity`, and rounds the exact rational with
   `ofAzRatRound`; `ofDecimalString` rounds to nearest.  Proven `toVal_ofDecimalStringRound` and
   the round trip `ofDecimalString_toDecimalString` (via `fromSci_ensurePoint_toString`, the
   parser's inverse theorem redone for the writer's `.0` convention).  Output with options:
   `toSci x o` / `toSciNumber` render the exact value with `AzRat.toSci`'s `SciOptions` (base,
   digit count, digit rounding, layout); proven `toSciNumber_value_precision`.  Literals:
   `OfNat` (exact), `OfScientific` (nearest at `literalPrecision = 53`), `Repr` (the exact
   hexadecimal debug format; `ToString` stays the shortest decimal); proven `toVal_ofNat`,
   `toVal_ofScientific`.  Lean's `Float`: `ofFloat64` (exact, through the model's unpacked form)
   and `toFloat64 x mode` (53-bit rounding in the normal range, rounding to a multiple of
   `2^-1074` below it, IEEE overflow to `±∞` or the largest finite value by mode), packed with
   the model's `pack`.  Since `Float` is a structure around `Float.Model`, these are proven end
   to end: `toVal_ofFloat64`, `unpack_pack`/`model_unpack_pack` (the model's `pack` and `unpack`
   are inverse on representable unpacked floats), `toUnpacked_binary64` (every result is
   representable), hence `ofFloat64_toFloat64 : ofFloat64 (toFloat64 x mode) = ofUnpacked
   (toUnpacked x mode)` unconditionally, and the value theorems
   `toVal_ofFloat64_toFloat64_normal` (`= round (precisionSet 2 53) mode (toVal x)` for
   `-1021 ≤ e ≤ 1023`) and `_subnormal` (`e ≤ -1022`).  Not formalized: the overflow rule
   (tested), and a `binary64` rounding target unifying the three regimes.
6. **Elementary functions** (later): `exp`, `log`, trigonometric functions, with MCA Chapter 4
   as the source.

## Housekeeping

Each item: `Azurite.lean` and `AzuriteTests.lean` imports (sorted), `docs/module_map.md`
(`AzFloat/` row and `Equiv/*` rows), this status log, the blueprint chapter
`blueprint/src/azurite/azfloat.tex`, memory.

## Status log

- 2026-10-05: `Arith.lean` split per operation like `AzInt`: `RoundScaled.lean` (shared `roundScaled`,
  `normalizeCarry`, `roundFromFloor`, `combinedPrecision`), `Add.lean`, `Mul.lean`, `Div.lean`, `Sqrt.lean`,
  `Rsqrt.lean`, with matching `Equiv/` (specs `Spec.op` next to their proofs; the cell lemma and
  `decide_pos_finiteVal` in `Equiv/RoundScaled`) and `Tests/` files.  No statement changed.
- 2026-10-05: **Ziv's strategy and `AzFloat + AzRat`.**  Source: the author's MCA §3.1.8–3.1.10 text
  (Ziv's strategy, Algorithm 3.1 RoundingPossible, Theorem 3.2, Table 3.1).  Design (user-corrected: a first
  draft squeezed the result between *two* approximations per level, floor and ceiling of `q`, i.e. two
  divisions; Ziv computes one approximation and tests it): `Ziv.lean` — `roundingPossible y ε p mode`
  (RoundingPossible in the form of two cheap roundings: `setPrecRound y p mode = addPrecRound y ε p mode`,
  float and tag; stricter than MCA at a cell boundary, which the tag needs), `zivLoop approx exact p mode
  fuel w` (one `(y, ε)` per level with `y ≤ v ≤ y + ε`, doubling `w`, exact fallback when the fuel is
  spent — correctness never depends on the fuel), `zivGuardBits = 64`, `zivFuel p n = log₂(p+n) + 8`,
  `truncError f = ulp? f` (or `0`).  `AddSubRat.lean` — `addRatApprox x q w`: `lo = ⌊q⌋_w` (the one division),
  `y = ⌊x + lo⌋_{w+2}`, `ε = ⌈truncError lo + truncError y⌉_2`; `zivStart q p = p + 64`, raised to
  `q.num.size` for dyadic `q` (exactness pre-test); `addRatExact` = `ofAzRatRound (x.toAzRat? + q)`;
  `addRatPrecRound`, `subRatPrecRound x q = add x (−q)`, `ratSubPrecRound q x = add (−x) q`.  Proofs:
  `Rounding/Between.lean` `round_between` (the squeeze, any `SymmetricRoundingTarget`, from the extremal
  properties of floor/ceiling only — no cell geometry; `round_between_of_lt` + symmetry for the `.gt`
  side); `Equiv/Ziv.lean` `roundVal_eq_of_between`, `roundingPossible_eq`, `zivLoop_eq`,
  `lt_add_ulp_of_floor` (`⌊x⌋_p` lies within one of its own ulps below `x`: `x − ⌊x⌋ < precScale x ≤
  precScale ⌊x⌋`, the binade of the floor being at least that of `x`), `eq_zero_of_roundFloor_eq_zero`,
  `truncError_spec`; `Equiv/AddSubRat.lean` `ofAzRatRound_eq_roundVal` (pair form), `addRatExact_eq`,
  `addRatApprox_spec`, `addRatPrecRound_eq_liftVal`, `subRatPrecRound_eq_liftVal`,
  `ratSubPrecRound_eq_liftVal`.  Tests `Tests/AddSubRat.lean` include a sum `2^-80/3` above/below the one-bit
  midpoint (first level fails, second succeeds) and agreement with the exact fallback.  NOT timed (user
  rule: pause before benchmarks).  `HAdd`/`HSub` instances (user decision 2026-10-05): nearest at the
  float's precision, `1` for a special float (`ratOpPrecision`), consistent with `combinedPrecision` and
  with Malachite, although `zero + 1/3 = 1/4` is a little awkward.  Open: `×`, `÷` with a rational next (`mulRatApprox`: `x · ⌊q⌋_w` with `ε = |x| · ulp`;
  division via `⌊1/q⌋_w` or `x / ⌊q⌋_w` bracketing); the `roundVal_congr_cell` bit-scan form of
  RoundingPossible as an alternative test; a provable fuel bound (distance of `x + q` from the boundaries
  is at least `2^-k / den`) would remove the fallback.

* **2026-10-01 — representation decided and core implemented.**  The first draft stored no
  precision (significand of exactly `p` bits, LSB-aligned); switched to the Malachite layout for
  the constant-factor reasons above, at the author's request.  Negative zero removed, also at
  the author's request.  Milestone 1 files written: `AzFloat/Basic.lean`,
  `AzFloat/Conversion.lean`, `AzFloat/Equiv/Basic.lean`, `AzFloat/Equiv/Conversion.lean`,
  `AzFloat/Tests/Basic.lean`.
* **2026-10-01 — the fixed-precision target and the noncomputable conversion.**  At the author's
  request: `floatSet p` (values of the non-`NaN` floats of precision `p`; `floatSet_eq` shows it is
  `precisionSet 2 p ∪ {⊤, ⊥}`), a `RoundingTarget` instance built by adjoining the infinities to
  `precisionSet 2 p`'s (the tiebreak defers to `precTiebreak`; infinities never tie), and
  `val_round_floatSet`.  `ofEReal p mode x` chooses the float whose value is the rounding
  (`±∞` fixed), `ofVal` sends `none` to `nan`.  `toVal_injective` (the left-aligned
  representation of a value at a precision is unique: sign from the value's sign, exponent from
  `2^(e−1) ≤ |v| < 2^e`, significand from the value) turns value equalities into equalities of
  floats: `ofAzRatRound_eq_ofEReal` and `ofVal_toVal`.
* **2026-10-01 — symmetric targets and the lifting layer.**  `precTiebreak` redefined on the
  magnitudes' coordinates (even wins; equal parities fall back to the candidate nearer `0`, then
  the first), which agrees with the old rule on genuine ties and makes `precisionSet b p` a
  `SymmetricRoundingTarget`; `floatTiebreak` extended with the finite-beats-infinite rule and
  `floatSymmetricRoundingTarget` proven.  `roundVal`, `applyReal`, `liftVal`, `lift`, `liftVal₂`,
  `lift₂`, `liftE` (total `EReal → EReal` functions) with `roundVal_coe`, `roundVal_of_toVal`,
  `lift_coe`, and `neg_eq_lift` (`liftE (fun v => -v) x p mode = (-x, .eq)` at the float's
  precision; `EReal`'s own negation supplies `-(±∞) = ∓∞`, at the author's suggestion).
* **2026-10-02 — milestone 2.**  `setPrecRound`/`setPrec`/`ulp?` and `partialCompare` with the
  Boolean relations, each specified by a lift or by the values: `setPrecRound_eq_liftE`,
  `partialCompare_eq`, `eqIEEE_iff`.  `normalize_spec` factors the carry normalization shared by
  `ofAzRatRound` and `setPrecRound` (and by the coming arithmetic); `log_abs_finiteVal` turns
  the exponent convention into `Int.log`.  The hand-computed test for `1/3` at `64` bits caught
  a wrong expectation (the `63`-bit value) — the tests are doing their job.
* **2026-10-02 — shifts.**  `shiftLeft x k`/`shiftRight x k` (`k : AzInt`, `<<<`/`>>>` also with a
  `Nat`): exponent arithmetic only.  `toVal_shiftLeft : (x <<< k).toVal = x.toVal.map (· * 2^k)`
  (`EReal.top_mul_of_pos` handles the infinities) and `shiftLeft_eq_liftE`.
* **2026-10-02 — hexadecimal debug format.**  Writer: `E = ⌊(e−1)/4⌋`, leading digit holds
  `m' = ((e−1) mod 4) + 1` bits, `D = ⌈(p − m')/4⌉ + 1` digits of `N = core · 2^(4(D−1)+m'−p)`;
  scientific layout iff `E ≤ −6 ∨ E ≥ D`, never an empty fractional part, `#p` suffix; the
  layout rules were checked against an independent Python model and Malachite's own vectors.
  Reader: strict grammar (`NaN`, `±Infinity`, `0x0.0`, or `-?0x<digits>[E±d]#p`), rebuilding
  `mkFinite sign (|N| + 4(E − k)) p (N >>> (|N| − p))` and rejecting inexact or zero-with-precision
  inputs.  Proof `ofHexChars_toHexChars`: a shape lemma for the reader (`ofHexChars_shape`),
  digit-string lemmas via `AzRat.parseMagnitude_eq`, and per layout the rebuilt exponent equals
  `e` (`omega` over `4E + m' = e`).  No `i64` hypotheses: the exponent digits are parsed as an
  `AzNat`.
* **2026-10-02 — decimal output.**  Author's rule (as clarified: the literal Floor/Ceiling
  agreement would be exactness): the smallest `p` such that the nearest `p`-digit decimal of the
  exact value converts back to the float at its precision.  The predicate is monotone, so `p` is
  found by `searchLeast` below `⌈P·log₁₀ 2⌉ + 2` (doubled if the estimate ever failed).  Output
  layout is `toSci`'s with the `.0` convention: `1.0`, `0.5`, `1.0e6`, `8.0e-6`,
  `0.3333333333333333`.  Proven: `SciNumber.toRat_toAzRat`, the search lemmas, and
  `toDecimalString_spec`; the digit bound itself is checked at run time.
* **2026-10-02 — addition and subtraction.**  Source: the author's reformatted MCA §3.2.1
  (Algorithm FPadd, Table 3.2, Theorem 3.3) and §3.2.2 (cancellation, Sterbenz).  FPadd's
  round/sticky bits and `round2` were replaced by a single exact rounding `roundScaled` of
  `±S · 2^w`, with the near/far split at `G = T + 2` justified by the cell argument above; the
  near case is exact integer arithmetic on a common scale.  Proofs: `roundScaled_eq_roundVal`
  (via `normalize_spec`), `toInt_round_intSet_congr`/`roundVal_congr_cell` (two reals in the same
  open half-cell round identically in every mode, with equal tags), `roundVal_far`,
  `addMagnitudes_eq`/`subMagnitudes_eq`, `addPrecRound_eq_liftVal₂`, `subPrecRound_eq_liftVal₂`.
  Test expectations were computed by hand (e.g. `1 + 2^−100` at 53 bits rounds to `1` with tag
  `.lt`, Floor gives `0x0.fffffffffffff8#53` for the difference).
* **2026-10-02 — multiplication and squaring.**  Source: the author's reformatted MCA §3.3
  (FPmultiply, the short-product error analysis of Theorem 3.5, the middle product, Payne–Hanek).
  Only FPmultiply is used: a full product of the cores and one `roundScaled`.  The short
  product (error up to `3(n − 1)` units) would need a fallback to decide the rounding and the
  tag, so it is deferred; the middle product is noted for Newton division (§4.2).  Proofs are
  short on top of `roundScaled_eq_roundVal`: `mul_cores_scaled`, `Spec.mul_inf_coe`/`mul_coe_inf`
  (sign of an infinite product), `mulPrecRound_eq_liftVal₂`, `sqrPrecRound_eq_liftE`.
* **2026-10-02 — division.**  Source: the author's reformatted MCA §3.4 (reciprocal and Newton's
  iteration, Lemma 3.7, Algorithm ApproximateReciprocal and Lemma 3.8, the wrap-around trick,
  §3.4.2 with Theorem 3.9, DivideNewton, Lemma 3.10, ShortDivision and Theorem 3.11, Barrett and
  Lemma 3.12).  Decision: the correctly rounded primitive is the direct reduction of §3.4.2 to one
  rounded integer division of the scaled cores (`AzInt.divRound`, already proven against the
  rounding spec), since every approximate method needs a correction before it rounds correctly;
  the reciprocal, middle product and Lemma 3.10 truncation are recorded for later.  Proofs:
  `quotient_scale_bounds` (the `p`-bit scaling), `divCores_eq` (via `val_round_precisionSet`,
  `AzInt.toInt_divRound`/`snd_divRound`, `normalizeCarry_spec` = `normalize_spec`),
  `divPrecRound_eq_liftVal₂`.  Lean note: `set` variables had to be made opaque with
  `clear_value` once their defining facts were recorded, otherwise unification unfolded the
  symbolic `AzInt.divRound` and timed out.
* **2026-10-02 — square root.**  Source: the author's reformatted MCA §3.5 (Algorithm FPSqrt,
  Theorem 3.13).  FPSqrt covers directed modes only; round-to-nearest (Exercise 3.14) was derived
  from first principles: `√M` lies in `(s, s+1)` with `s = ⌊√⌊M⌋⌋`, is exactly `s` iff the
  remainder vanishes and nothing was shifted out, and sits below, at or above the midpoint
  `s + 1/2` according to the exact comparison `4M ⋚ (2s+1)²` (ties are real: `√(9/4) = 3/2`).
  The general decision procedure `roundFromFloor` and its spec `roundFromFloor_spec` (against
  `round intSet`, all five modes, including the even tiebreak) are reusable for any future
  irrational-valued operation computed through a floor and a midpoint test.  Proofs:
  `compareScaled_eq`, `scaled_floor`, `sqrtCore_eq`, `sqrtPrecRound_eq_liftVal`.
* **2026-10-02 — fast shortest-decimal output.**  The author observed that printing a
  10,000-bit square root took seconds under `#eval`.  Measured compiled (`az_float_to_string`):
  the square root itself is 0.02 ms; the print was 39 ms, of which a round-trip probe's `toSci`
  and `ofAzRat` were 0.04 and 0.03 ms but `SciNumber.toAzRat` was 9.5 ms — the gcd that reduces
  the fraction `mantissa / 10^scale` to lowest terms dominated everything.  Two changes:
  (1) `shortestDecimalPrecision` gallops down from the digit bound (`hi − 1, hi − 3, hi − 7, …`)
  and bisects the last step (`searchLeastFromTop`, same three lemmas as `searchLeast`), since the
  answer is almost always within a few digits of `⌈P·log₁₀ 2⌉ + 1`; (2) the probe rounds the
  unreduced fraction directly with the division machinery (`ofFractionRound`, proven equal to
  rounding the reduced rational by `ofFractionRound_eq` and `fst_ofFractionRound`, with
  `SciNumber.value_eq_fraction`), so no gcd is computed.  `decimalRoundTrips_iff` keeps its old
  statement, so `toDecimalString_spec` is unchanged.  Result (compiled, ms): 53 bits 0.115 →
  0.004; 1,000 bits 3.6 → 0.018; 10,000 bits 39 → 0.37; 100,000 bits 722 → 20; the interpreted
  `#eval` of the 10,000-bit print went from 3.8 s to 1.15 s (the rest is interpretation).  The
  interval test considered earlier is not needed.
* **2026-10-02 — text input.**  `AzFloat/OfString.lean`: `ofDecimalStringRound`,
  `ofDecimalString` (specials tested first, then `fromSci` and `ofAzRatRound`).
  `Equiv/OfString.lean`: `ensurePoint` lemmas (`ensurePoint_of_mem`, `ensurePoint_no_e`,
  `ensurePoint_e`, `mem_ensurePoint`, `ensurePoint_ne_special`), `sciVal_append_zero`,
  `fromSci_ensurePoint_toString` (a copy of the `fromSci_toString` case analysis in which the
  three point-free shapes acquire `.0`; restricted to bases at most 14 and a lowercase `e`, since
  `ensurePoint` looks for `'e'`), `toVal_ofDecimalStringRound`, `ofDecimalString_toDecimalString`.
  Lean notes: specials are tested before parsing so that the lemmas about them need no kernel
  evaluation of `fromSci` on string literals; `congr 1` on `some (ofAzRatRound (ofRat …) …).1 =
  some x` timed out (its `rfl` attempt unfolds the conversion), `Option.some.injEq` does not; the
  base of `decimalOptions` is rewritten to the literal `10` by `rfl` before unifying with
  `fromSci`'s default base.
* **2026-10-02 — milestone 5 complete.**  `toSci` with options, literals and `Repr`, and the
  `Float` conversions.  Discovery: Lean 4.34's `Float` is `structure Float where ofModel ::
  toModel : Float.Model`, a wrapper around a logical model (a valid binary64 bit pattern with
  `unpack`/`pack` to `UnpackedFloat`: `NaN`, signed infinity, signed zero, `± m · 2^e`), so
  `(Float.ofModel m).toModel = m` is `rfl` and conversions can be proven end to end rather than
  only at the bit level.  `toFloat64` rounds with our own proven `AzInt.shiftRightRound` (the
  model's `round` is nearest-even only and has no lemmas) and packs with the model's `pack`; the
  inverse theorem `unpack_pack` is BitVec bookkeeping (`unpackMantissa/Exponent_packComponents`
  from core, our `unpackSign_packComponents`, `Nat.two_pow_add_eq_or_of_lt` for the hidden bit).
  Lean notes: `rw` cannot rewrite under the `0 < mantissa` proof argument of `UnpackedFloat.finite`
  (unfold `Binary64`/`toVal` first); `UnpackedFloat` has no `DecidableEq` (closed cases via `simp
  +decide only`); `Int.ceil_nonpos` is an iff.
* **2026-10-04 — reciprocal square root.**  Source: the author's reformatted MCA §3.5.1 (Lemma
  3.14, Algorithm ApproximateRecSquareRoot with Lemma 3.15, and the FFT-range remark).  The
  Newton route is an approximation with error `2β^(−n)` and is recorded for later; the primitive
  reuses the square-root method with the scaling `D` chosen per parity and the power-of-two
  boundary case, so that no carry analysis is needed and `roundFromFloor` does the rounding.
  Proofs: `AzInt.toInt_shiftRight_one` (floor halving of the exponent), `rsqrtCore_eq` (the three
  `D` cases give `2^(2p−2) ≤ 2^D/n < 2^(2p)`, then the tail of `sqrtCore_eq`),
  `rsqrtPrecRound_eq_liftVal`.
