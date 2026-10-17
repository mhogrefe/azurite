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
- 2026-10-05: **Ziv's strategy and `AzFloat ± AzRat`** (`Ziv.lean`, `AddSubRat.lean`, Equiv, tests).
  Source: the author's MCA §3.1.8–3.1.10 text (Ziv's strategy, Algorithm 3.1 RoundingPossible, Theorem 3.2,
  Table 3.1).  Three user interventions shaped the design: (1) a first draft squeezed the result between
  *two* approximations per level (floor and ceiling of `q`, two divisions) — Ziv computes ONE approximation
  and tests it; (2) the user asked whether the exact fallback was needed — examining that showed the
  closed-interval test fails forever when the truncated sum is itself a boundary (`x ≫ q`), so far-apart
  operands silently fell through to the fallback and materialized `2^|e|`; the user chose a proven fuel
  bound with no fallback; (3) the truncation design that followed (`y = ⌊x + lo⌋_{w+2}` plus an error
  bound) still needed `w ≈ |e|` when the sum lies just *below* a boundary (`2^(10⁹) − 1/3`: the truncation
  error added back overshoots the boundary), which the test suite caught as a 36-minute hang; the user
  approved the final **exact-bracket** design.  Final design: `Roundable := Nat → RoundingMode → AzFloat ×
  Ordering` (an exact real given by its rounding procedure); `truncError r` is `0` for an exact truncation
  (tag `.eq`) else one ulp, and `lo + truncError lo` is the next float up (`truncError_spec` proves it is
  again a `w`-bit float); the bracket of `x + q` at level `w` is `x + lo ≤ x + q ≤ x + hi` with
  `lo = ⌊q⌋_w` (the one division) and `hi = lo + ulp`, both ends rounded on demand by `addPrecRound`,
  cheap in every regime (far cases via its sticky representative); `roundingPossible l h p mode` = MCA
  RoundingPossible in bracket form: `⌊l⌋_{p+1} = ⌊h⌋_{p+1}` (no boundary in `(l, h]`), result
  `round_p h`; `zivLoop approx p mode fuel w` (fuel+1 attempts, doubling, `(nan, .eq)` after the last —
  proven unreachable); NO fallback.  `zivStart q p = p + 64` or `max (p+64) q.num.size` for dyadic `q`;
  `addRatFuel` = `zivFuel (p + |num| + 2|den| + |m| + 2) + |e|.size + 1` doublings (`zivFuel W` = bit length
  of `W`, via `AzNat.size`, no `Nat.log2`).  Proofs: `Equiv/Ziv.lean` `roundVal_congr_of_no_boundary`
  (from `roundVal_congr_cell` with `j = ⌊log₂|v'|⌋ − p`, `k = ⌊v'/2^j⌋`), `Rounds`, `roundingPossible_eq`,
  `zivLoop_eq` (hypotheses: bracketing, `∀ w ≥ W` possible, `W ≤ w₀·2^fuel`), `lt_add_ulp_of_floor`
  (`x − ⌊x⌋_p < precScale x ≤ precScale ⌊x⌋_p`), `truncError_spec`, boundary arithmetic
  (`boundary_repr`, `exists_int_mul_sub_dyadic`, `one_div_le_abs_of_mul_eq_int`);
  `Equiv/AddSubRat.lean` `addRatApprox_spec`, **`addRatApprox_possible`** (termination: `v` boundary ⇒ `q`
  dyadic (`toRat_mem_precisionSet_of_dyadic`, via coprimality and `Nat.dvd_prime_pow`) ⇒ `lo = q` ⇒ bracket
  is a point; else `|v − b^±| ≥ 1/(den·2^a)` for the adjacent boundaries (`dist_sum_boundary`, integrality;
  their binade is at least `v`'s, and `⌊log₂|v|⌋ ≥ −|den| − a₀` from `|v| ≥ 1/(den 2^{a₀})`), while the
  bracket width `ε ≤ 2^(|num|+1−w)`), `addRatBound_le`, the three lift theorems.  The bound is deliberately
  loose (it costs a few doublings of fuel, never iterations: the loop stops at the first passing level,
  level 1 in all far cases).  Lean notes: `#guard` evaluates compiled code (the interpreter), not kernel
  reduction — a hang in a `#guard` is a runtime problem; the earlier `decide`-needs-structural-recursion
  rule is about kernel evaluation.  Tests include the exponent-`±10⁹` far cases in both directions and a
  sum `2^-80/3` above/below the one-bit midpoint.  NOT timed (pause rule).  `HAdd`/`HSub` instances (user
  decision): nearest at the float's precision, `1` for a special float (`ratOpPrecision`), consistent with
  `combinedPrecision` and with Malachite, although `zero + 1/3 = 1/4` is a little awkward.
- 2026-10-05: **`AzFloat × AzRat`, `AzFloat / AzRat`, `AzRat / AzFloat`** (`MulRat.lean`, `DivRat.lean`, Equiv,
  tests) — **without Ziv.**  A first `×` used the Ziv bracket (`x·lo`, `x·hi` by the sign of `x`) and needed
  an exactness pre-test (`3 · 1/3 = 1` is a boundary with non-dyadic `q`, and a bracket straddles it
  forever): product dyadic iff the odd part of `den` divides `m`, then `mulRatExact`; it was proven and
  gate-green (commit history), then replaced.  Working out `q / x` showed the structural fact: for a product
  or quotient the exponent of `x` factors out as a pure shift — `x·q = ±(m·num/den)·2^(e−|m|)`,
  `x/q = ±(m·den/num)·2^(e−|m|)`, `q/x = ±(num/(den·m))·2^(|m|−e)` — so each is ONE `ofFractionRound` of a
  small unreduced fraction (a single division, no gcd; the primitive from the decimal round-trip work)
  followed by an exact shift: no loop, no fuel, no termination proof, no exactness test, cost at or below
  one Ziv level.  Ziv is needed only for `±`, where the exponent enters the numerator.  (User: Malachite does
  not use Ziv for these either.)  Proofs: `Equiv/Shift.lean` `log_abs_mul_two_zpow`, `val_round_mul_two_zpow`
  (rounding commutes with scaling by `2^k`, via the integer-rounding form `val_round_precisionSet` and the
  scale-covariance of `precScale`), `roundVal_mul_two_zpow` (float by `toVal_injective`, tag by
  `compare_mul_right_pos`); `Equiv/MulRat.lean` `shift_ofFractionRound_eq`, `finiteVal_mul_toRat`,
  `sign_eq_decide_pos`, `mulRatPrecRound_eq_liftVal`; `Equiv/DivRat.lean` `finiteVal_div_toRat`,
  `toRat_div_finiteVal`, `divRatPrecRound_eq_liftVal`, `ratDivPrecRound_eq_liftVal` (specials by the
  `Spec.div` lemmas: `x/0 = ±∞` by the sign of `x`, `0/0` NaN, `q/±∞ = 0`, `q/0 = ±∞` by the sign of `q`).
  The Ziv termination geometry (`adjacent_boundaries`, `no_boundary_of_dist`, …) stays in `Equiv/Ziv.lean`
  for the sum.  `HMul`/`HDiv` instances at the float's precision.  Tests: exact and rounded products and
  quotients in all modes and both signs, ties, exponents `±10⁹`, the instances.  NOT timed.  The mixed
  `AzFloat`/`AzRat` arithmetic is complete.
- 2026-10-05: **Constants** (`Constants.lean`, `Equiv/Constants.lean`, `Tests/Constants.lean`; user request,
  after Malachite's `Float` constants `(prec, rm) ↦ Float`).  Spec form `liftVal₀ v p mode := roundVal p
  mode v` (nullary lift, in `Equiv/Rounding.lean`).  `sqrt2PrecRound p mode = sqrtPrecRound two p mode`,
  `sqrt2 p`; `sqrt2PrecRound_eq_liftVal₀ : … = liftVal₀ (some √2) p mode` via `sqrtPrecRound_eq_liftVal`,
  `toVal_two`, `Spec.sqrt_coe`.  Tests: 1, 2, 53 bits in several modes (binary64 `0x1.6a09e667f3bcd`
  is ABOVE `√2`, tag `.gt`), shortest decimals at 53 and 100 bits.  Note: `sqrtPrecRound` at precision `0`
  returns `(zero, .gt)` where the other operations return `NaN` — harmless (precision `0` is outside every
  spec) but inconsistent; left as is.
- 2026-10-05: **all quadratic-irrational constants of Malachite** (user request): `sqrt3`, `sqrt5`
  (`sqrtPrecRound (ofAzNat 3/5)`), `sqrt2Over2`, `sqrt3Over3`, `sqrt5Over5` (`rsqrtPrecRound`; spec value
  `√n / n`, from `(√n)⁻¹` by `Real.sqrt_div_self'`), and `phi` = `(1 + √5)/2` — the first constant that is
  not a single primitive: Ziv's loop (`phiApprox w`: `l = ⌊√5⌋_w`, `h = l + truncError`, ends
  `addPrecRound (l >>> 1) oneHalf` and `addPrecRound (h >>> 1) oneHalf`, exact floats plus one half; start
  `p + 64`, fuel `zivFuel (2p + 6)`).  Termination `phiApprox_possible`: `φ ∈ (1, 2)` is irrational
  (`irrational_sqrt_natCast_iff`, `¬ IsSquare 5` by `interval_cases` — `decide` cannot evaluate `Nat.sqrt`),
  so not a boundary; for a boundary `b` adjacent to `φ` (`1 ≤ b < 5/2`, `b = M 2^k`, `k ≥ −p`),
  `c = 2b − 1` is a multiple of `2^-p`, `5 − c²` a nonzero multiple of `4^-p`, hence
  `|φ − b| = |√5 − c|/2 = |5 − c²| / (2(√5 + c)) ≥ 2^(−2p−4)`, while the bracket has width
  `ε/2 ≤ 2^(1−w)`; `w ≥ 2p + 6` suffices.  Tests: hand-rounded low precisions for all seven constants,
  the 53-bit decimals, and `√2/2` against `√2 >>> 1` (an exact shift, so the two routes must agree).
  Further constants (`π`, `e`, `ln 2`, Euler's `γ`, …) need the elementary functions or dedicated series
  (MCA Ch. 4, user to supply text).
- 2026-10-05: **Prouhet–Thue–Morse constant** (`ProuhetThueMorse.lean`, `Equiv/ProuhetThueMorse.lean`, `Tests/ProuhetThueMorse.lean`;
  user request, "implement it efficiently: the limbs of an approximation take on only two values").
  Definition `prouhetThueMorseConstant : ℝ := ∑' n, tₙ / 2^(n+1)` (noncomputable, in Equiv), `prouhetThueMorseSeq` by binary
  recursion (WF on `n / 2`; equation lemma `prouhetThueMorseSeq_eq` holds at `0` too).  Key identity `t (2^k a + b) =
  t a xor t b` (`b < 2^k`) ⇒ word `j` of 64 bits is `T₆ = 0x6996966996696996` or its complement by `t j`;
  `prouhetThueMorseLimbs N = ofLimbs (Array.ofFn fun i => prouhetThueMorseLimb (N − 1 − i))` (no arithmetic at all).
  Rounding: `Y = first p + 2 bits`, floor `Y >>> 1`, round bit `Y % 2`, `exact = false` and `cmpMid ≠ .eq`
  always (the sequence is not eventually constant: `t (2^k) = 1`, `t (3·2^k) = 0`), then `roundFromFloor` +
  `normalizeCarry` with exponent `−1` (`1/4 < τ < 1/2`).  Proof pattern = the sqrt assembly
  (`roundFromFloor_spec`, `abs_toInt_round_bounds`, `normalizeCarry_spec`, `toVal_injective`,
  `compare_mul_right_pos`).  Word value: `ptmWord` (`T₀ = 0`, `T_(k+1) = T_k·2^(2^k) + (2^(2^k) − 1 − T_k)`),
  `ptmWord_eq_sum`, and `prouhetThueMorseWord.toNat = ptmWord 6` by `decide` (6 structural steps — `decide` on the
  64-term sum with the WF `prouhetThueMorseSeq` would not reduce).  Real side: `Summable.sum_add_tsum_nat_add`,
  `Summable.le_tsum`, `Summable.tsum_lt_tsum`, `tsum_geometric_two'`.  Lean notes: `congr 1` on an equation
  between `Finset.sum`s hits a whnf timeout (it unfolds the sum) — use `congrArg₂ (· + ·)`; `decide` cannot
  evaluate `Nat.sqrt`/WF functions (`¬ IsSquare 5` by `interval_cases`).  Values checked: 53 bits
  `0x0.69969669966968`, `0.4124540336401076`; 100 bits `0.4124540336401075977833613682584`.
- 2026-10-05: **prime constant** (`PrimeConstant.lean`, `Equiv/PrimeConstant.lean`, `Tests/PrimeConstant.lean`;
  user request, "use our existing prime sieve").  `primeConstantReal : ℝ := ∑' n, [n prime] / 2^n`
  (noncomputable, Equiv).  The bits are the sieve bitmap `primeSieve (64 N)` (bit `n` ↔ `n` prime) read
  backwards: `primeConstantLimbs N = ofLimbs (Array.ofFn fun i => wordOfBits fun l => S.testBit (64N − (64 i +
  l)))`, with `wordOfBits f` a 64-step `foldl` adding `1 <<< l` (`toNat_wordOfBits` by induction on the
  prefix length with the invariant `sum < 2^j`, so no overflow; UInt64 lemmas `toNat_add/shiftLeft/ofNat'`).
  Regrouping `sum_mul_pow_regroup` (plain, no reversal) then `Finset.sum_range_reflect` to reindex `m ↦ 64N −
  n`.  The rounding is the Prouhet–Thue–Morse assembly verbatim (`roundFromFloor` on the first `p+1`
  significant bits, exponent `−1`, `1/4 < ρ < 1/2`): tail in `(0, 1)` via `Nat.exists_infinite_primes
  (E+1)` and the composite `4(E+1) = 2 · 2(E+1)` (`Nat.not_prime_mul`).  Lean notes: rewriting the condition
  of `if Nat.Prime n` with the sieve iff timed out at whnf (the decidability instance of `Nat.Prime`
  unfolds) — use `by_cases` + `ite_eq_left/right`; `if_pos/if_neg` are deprecated.  Values: 53 bits
  `0.41468250985111166`, `0x0.6a28a20a08a208`; 100 bits `0.4146825098511116602481096221542`; 20000 bits
  in well under a second (sieve + bit copy).  Together with the Thue–Morse constant these are the two
  bit-pattern constants; the remaining Malachite constants need series.

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
* **2026-10-09 — sums of lists.**  `AzFloat/Sum.lean`: `sumPrecRound xs p mode`, the correctly
  rounded sum of a list, derived from first principles (no source text): exact accumulation of a
  window of `W = p + ⌈log₂ n⌉ + 3 + 64` exponents below the largest term (`exactAdd` at the
  precision `exactSumPrec`, which holds any sum of two floats exactly), the tail bounded by
  `T = 2^(e_max(R) + ⌈log₂ |R|⌉)`, a restart on `S₁ :: R` when the window sum is below
  `2^(p+4) T` (cancellation; the list shrinks, so the fuel is the length — a one-term window
  cannot cancel, since its term is at least `2^(e_max − 1)` and the tail lies `W` exponents
  lower), and otherwise the Ziv bracket `(S₁ − T, S₁ + T)` with `roundingPossible`; when a
  boundary lies inside, it is unique (two `(p+1)`-bit floats of magnitude at least `2^(E−2)`
  are at least `2^(E−2−p)` apart, the bracket is narrower) and equal to the `(p+1)`-bit
  truncation of the upper end, and the side is decided by the exact sign of `(S₁ − b) + ΣR`
  (`signSum`, the same windowing with window `⌈log₂ n⌉ + 2`), the midpoints of the two
  half-brackets rounding like the sum.  Pitfall found by the tests: the first version computed
  `S₁ − T` exactly, which for terms `2^(10⁹)` and `2^(−10⁹)` built `2·10⁹`-bit intermediates
  (a 396 s test build); the ends are now rounded outward at precision `W` by `addPrecRound`
  (error at most `2^(E+3−W)` each), which forced the cancellation threshold up to `2^(p+4) T`
  for the uniqueness argument.  `Equiv/Sum.lean`: `Spec.sum`, `Spec.sum_eq`, `exactAdd`
  exactness, `splitWindow_spec`, `tailBound_spec`, `signSum_eq`, `boundary_dist`,
  `floor_err_le`, `setPrecRound_floor_spec`, `sumFinite_eq`, `sumPrecRound_eq`.  The `none`
  answer of `roundingPossible` is never analysed: the boundary branch is correct whether or not
  rounding was possible.  Lean notes: the equation lemma of a catch-all match arm (`| _ =>`)
  carries the side hypothesis `l = [] → False` under `rw` — use `rw [f.eq_def]`; terms
  introduced after a `set` are not abstracted, so the bracket lemma takes the operands' values as
  hypotheses (`toVal_addPrecRound_floor`); `roundFloor` and `isGreatest_roundFloor` need
  `open RoundingTarget`.  Not timed.
* **2026-10-09 — products of lists.**  `AzFloat/Product.lean`: `productPrecRound xs p mode`.
  No approximation is needed: the value of a finite float is `±core · 2^scale`, so the exact
  product is the balanced product tree of the cores (`AzNat.product`) on the summed scale, and
  one `roundScaled` rounds it — the `n`-ary form of `mulPrecRound`.  Specials by flags (`NaN`;
  zero with an infinity; an infinity with the sign `productSign`, the parity of the negative
  factors; zero), the empty product is `1`.  `Equiv/Product.lean`: `Spec.product` (fold of
  `Spec.mul` from `1`), `Spec.product_eq` (case form, proven by explicit `by_cases` on the three
  flags of the tail rather than `split_ifs`, which also splits the `if productSign` inside the
  value), `realProd_spec`, `realProd_eq`, `productPrecRound_eq`.  Tests include agreement with
  a fold of exact two-operand multiplications over several lists, precisions and modes.  Lean
  notes: `AzRat.parse` reads fractions, not decimals (`"-3/2"`, not `"-1.5"`);
  `List.filterMap_cons_some` takes the `f a = some b` proof as its only explicit argument.
  Not timed.

* **2026-10-16 — square root of a rational.**  `AzFloat/SqrtRat.lean`: `sqrtRatPrecRound q p
  mode : AzFloat × Ordering`.  First principles, mirroring `sqrtCore`: `e = ⌊log₂ (n/d)⌋` from
  the sizes and one `normalizedCompare` (as `AzRat.floorLogBase2Abs`, recomputed in `AzInt` so no
  `ℤ → AzInt` conversion is needed), `h = ⌊e/2⌋` by `AzInt.shiftRight 1`, half shift
  `k = p − 1 − h` applied as `2k` to `n` (k ≥ 0) or `d` (k < 0), so `√(A/D) ∈ [2^(p−1), 2^p)`;
  floor `s = AzNat.sqrt (A / D)` (one division; `⌊√⌊x⌋⌋ = ⌊√x⌋`), exactness `s²·D = A` and
  midpoint `4A ⋚ (2s+1)²·D` through `AzNat.compareProduct` (the swap of the product comparison
  gives the midpoint tag), `roundFromFloor`, `normalizeCarry` at exponent `h + 1`.  No Ziv loop
  and no reduction of the fraction.  `Equiv/SqrtRat.lean`: `roundFromFloor_normalizeCarry_eq`
  (the tail of `sqrtCore_eq`, factored out as a reusable lemma: a `roundFromFloor` result
  normalized at exponent `E` is `roundVal` of `y · 2^(E − p)`), `floorLog2_bounds`,
  `toInt_shiftRight_one`, `sqrtRatCore_eq`, `sqrtRatPrecRound_eq = roundVal p mode (Spec.sqrt q)`.
  Tests include agreement with `sqrtPrecRound` on exactly representable rationals in all modes.
  `rsqrtRatPrecRound q p mode` (same files, same day): `1/√(n/d) = √(d/n)` exactly, so it is
  `sqrtRatCore d n` with `0 ↦ +∞`; `rsqrtRatPrecRound_eq` via `Real.sqrt_inv` and `inv_div`.
  Not timed.

## MCA Chapter 4 ledger (elementary and special functions)

Theory first, algorithms later (user instruction 2026-10-16): each chunk of MCA Ch. 4 is digested
into Lean theorem statements (proven where feasible) before anything is implemented.

* **§4.1 Introduction (2026-10-16).**  No theorems.  Conventions adopted for this chapter: binary
  radix; `n` is the target *relative* precision in bits (absolute error `2^(−n)` for values near
  `1`); rounding is not analysed in Ch. 4 — the Ch. 3 machinery (`roundVal`, Ziv) supplies correct
  rounding on top of the approximations.  Methods announced: Newton (§4.2, inverse functions,
  e.g. `exp` from `ln`), power series (§4.4), asymptotic expansions (§4.5), continued fractions
  (§4.6), recurrences (§4.7), AGM (§4.8), binary splitting (§4.9), contour integration (§4.10).

* **§4.2 Newton's method via linearization (2026-10-16).**  States: Taylor at `x₀` (4.1), the
  step `x₁ = x₀ − f(x₀)/f'(x₀)` with `x₁ − ζ = O(|x₀ − ζ|²)`, halving `|x₁ − ζ| ≤ |x₀ − ζ|/2` near
  the zero, the iteration (4.2), order of convergence at least two (`|e_{n+1}| ≤ K|e_n|²`), and
  (4.3) `e_{n+1} = f''(ζ)/(2f'(ζ)) e_n² + O(|e_n|³)` for `f ∈ C³`.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/Newton.lean` (namespace `Azurite.BZ`, all proven): Taylor
  with Lagrange remainder to orders 1–3 between any two points in either order (`uIcc`/`uIoo`,
  through the Cauchy mean value theorem rather than Mathlib's one-directional
  `taylor_mean_remainder_lagrange`), `newtonStep`/`newtonSeq`, `newtonStep_sub_root` (= (4.1)
  rearranged, exact), `abs_newtonStep_sub_root_le` (`K = M/(2m)` from `|f''| ≤ M`, `|f'| ≥ m` on
  the interval of radius `r` about `ζ`), `newtonSeq_bounds` (stay in the interval, halve,
  `K|e_n| ≤ (K|e_0|)^(2^n)` once `K|e_0| ≤ 1/2`), `abs_newtonSeq_sub_root_le`
  (`|e_n| ≤ |e_0|/2^n`), `tendsto_newtonSeq`, and (4.3) as the explicit bound
  `newtonStep_sub_root_cubic`: `|e₁ − f''(ζ)/(2f'(ζ)) e₀²| ≤ (7M₃/(6m) + M₂²/(2m²)) |e₀|³`
  (the `O(·)` form follows; not stated separately).  Hypotheses are explicit `HasDerivAt`
  derivatives, so the later concrete functions (`1/x`, `1/√x`, …) plug in directly.  Multi-
  variable Newton (Jacobian) not formalized — not needed for the planned scalar iterations.
  Lean notes: build `HasDerivAt` terms with a type ascription and `congr_deriv`, not `convert`
  (Pi-operation function shapes don't match syntactically); after `field_simp`, substitute the
  Taylor identities with `generalize … at` + `subst` before `ring`.

* **§4.2.1 Newton's method for inverse roots (2026-10-16).**  States: for `f(x) = y − x^(−m)`,
  `f'(x) = m x^(−(m+1))`, Newton's step is `x + x(1 − xᵐy)/m` (4.4), division-free apart from
  the integer `m`, converging to `y^(−1/m)` from a close enough start; `m = 1, 2` are the
  reciprocal and reciprocal square root (§4.2.2–4.2.3).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/InverseRoot.lean` (all proven): `inverseRootFun`/`'`/`''`
  (as `y − 1/xᵐ`, `m/x^(m+1)`, `−m(m+1)/x^(m+2)`, `HasDerivAt` for `x ≠ 0`), `inverseRootStep`,
  `inverseRootSeq`, `newtonStep_inverseRootFun` ((4.4) = Newton's step), `rpow_neg_inv_pow_mul`
  and `inverseRootFun_root` (the zero), `inverseRootStep_rel` (relative-error form, the tool
  for the exact error recurrences of the next two subsections), `exists_tendsto_inverseRootSeq`
  (local convergence from the generic `newtonSeq_bounds`/`tendsto_newtonSeq` with `r = ζ/2`,
  `M = m(m+1)/(ζ/2)^(m+2)`, `m_lo = m/(3ζ/2)^(m+1)`, `δ = min(r, 1/(2K))`; the iterates never
  vanish, so they are Newton's).  Lean notes: `HasDerivAt.inv` needs
  `Mathlib.Analysis.Calculus.Deriv.Inv` (otherwise field notation reports a missing
  `HasFDerivAtFilter.inv`); `eq_inv_of_mul_eq_one_left` for `a * b = 1 → a = b⁻¹`.

* **§4.2.2 Newton's method for reciprocals (2026-10-16).**  States: `m = 1` gives (4.5)
  `x_{j+1} = x_j + x_j(1 − x_j y)`; with `u_j = 1 − x_j y`, `u_{j+1} = u_j²` (4.6), `u_j = u_0^(2^j)`
  (4.7); convergence iff `|u_0| < 1` iff `x_0 y ∈ (0, 2)`; bits double per step so the iteration
  count is predictable; hardware use with `y ∈ [1/2, 1)` and a table start.  Computational
  issues: (4.8) `x_j(2 − x_j y)` is mathematically but not computationally equivalent — in (4.5)
  the correction product needs only `n/2` bits, in (4.8) the product needs `n`; rule: separate
  terms of different order (exception: Schönhage's `3M(n)/2` reciprocal, §3.8).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/Reciprocal.lean` (all proven): `reciprocalStep`/`Seq`
  (computable, real-valued), `recipError`, (4.6), (4.7), `reciprocalSeq_sub_inv`
  (`x_j − 1/y = −u_0^(2^j)/y`), `abs_recipError_lt_one_iff`, `tendsto_recipError_iff`,
  `tendsto_reciprocalSeq_iff` (both directions; the "only if" via `|u_0|^(2^j) ≥ 1`),
  `abs_recipError_reciprocalSeq_le` (`2^(−k)` → `2^(−k·2^j)`), `abs_recipError_reciprocalSeq_le_of_le`
  (`n ≤ k·2^j`), `recipError_one_le_half`; the precision remark as exact identities for a product
  with relative error `θ`: `recipError_reciprocalStep_perturbed` (`u² − θ·u·(xy)`) vs
  `recipError_reciprocalStep'_perturbed` (`u² − θ(1 − u²)`), and the bound `3ε²` when
  `|u|, |θ| ≤ ε ≤ 1`.  Not formalized: the table-lookup start (no table yet), §3.4.1's concrete
  algorithm (already implemented exactly, `divCores`), the §3.8 exception.  Design note for the
  implementation phase: Newton reciprocal steps must compute `x(1 − xy)` at half precision and
  add it at full precision.

* **§4.2.3 Newton's method for (reciprocal) square roots (2026-10-16).**  States: `m = 2` gives
  (4.9) `x_{j+1} = x_j + x_j(1 − x_j² y)/2` → `y^(−1/2)`, division-free except by 2 (Ex. 3.15);
  `y^(1/2) = y · y^(−1/2)` in one multiplication; Newton on `x² − y` gives Heron (4.10)
  `(x_j + y/x_j)/2`, which divides by `x_j` each step, so (4.9) is expected to be cheaper
  (division vs multiplication cost); both second order; see §3.5.1, §3.8.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/InverseSqrt.lean` (all proven; goes beyond the text with the
  exact error recurrence): `rsqrtStep`/`rsqrtSeq`, `rsqrtError u = 1 − x²y`,
  `rsqrtError_rsqrtStep` (`u' = u²(3 + u)/4`), `|u| ≤ 1 ⇒ |u'| ≤ u²`, `|u_j| ≤ |u_0|^(2^j)`,
  `rsqrtStep_rel` (`ε' = −(3ε² + ε³)/2`, via `inverseRootStep_rel`), `rsqrtStep_pos`,
  `abs_rsqrtError_lt_one_iff` (`x_0² y ∈ (0, 2)`), `rsqrtSeq_pos`, `tendsto_rsqrtSeq` (basin:
  every `x_0 > 0` with `x_0² y < 2`), `inv_sqrt_eq_rpow`; `sqrt_eq_mul_inv_sqrt`,
  `mul_inv_sqrt_rel` (the final multiplication preserves the relative error exactly); Heron:
  `heronStep`/`heronSeq`, `newtonStep_sq_sub`, `heronStep_sub_sqrt` (`(x − √y)²/(2x)`),
  `sqrt_le_heronStep`, `heronStep_le`, `heronStep_sub_sqrt_le`, `tendsto_heronSeq` (from every
  `x_0 > 0`: one step lands above `√y`, then the error halves).  Not formalized: the cost
  comparison (no cost model for ℝ-level iterations).  Implementation note: the library already
  has exact `rsqrtPrecRound`/`sqrtPrecRound` (§3.5); (4.9) is the candidate for a Newton-based
  high-precision variant later, with the correction `x(1 − x²y)/2` at half precision as for
  reciprocals.

* **§4.2.4 Newton's method for formal power series (2026-10-16).**  States (complementary view,
  not needed for function evaluation; applications to Bernoulli numbers, Ex. 4.41–4.42): Newton
  applies to series with `ord A = 0`; (4.5) with `y = 1 − z`, `x_0 = 1` converges quadratically to
  `∑ zⁿ`, where quadratic means `ord e_j ~ 2^j`; `u_0 = z`, `u_j = z^(2^j)`,
  `x_j = (1 − u_j)/(1 − z)`; formal derivative `∑ j a_j z^(j−1)` and integral `∑ a_j/(j+1) z^(j+1)`
  have no integer analogue (Ex. 4.1).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/FormalPowerSeries.lean` (all proven): `ringReciprocalStep`/
  `Seq`/`ringRecipError` with (4.6), (4.7) over any `CommRing` (the ℝ version of §4.2.2 is the
  instance, `reciprocalStep_eq_ringReciprocalStep`); `ringReciprocalSeq_one_sub` (`x_j = ∑_{n<2^j} zⁿ`,
  by induction `x_{j+1} = x_j (1 + z^(2^j))` + `Finset.sum_range_add`); in `PowerSeries R`:
  `powerSeriesReciprocalSeq_sub_inv` (cancel the unit `1 − X`, inverse `mk 1` from
  `mk_one_mul_one_sub_eq_one`), `order_powerSeriesReciprocalSeq_sub_inv` (`= 2^j` exactly, via
  `order_eq_nat` + `coeff_X_pow_mul'`, needs `Nontrivial R`); `coeff_derivative'` (Mathlib's
  `PowerSeries.derivative`, a `Derivation`, matches the text); own `integral` (Mathlib has none)
  with `derivative_integral`, `integral_derivative` for `[Field K] [CharZero K]`.  Not formalized:
  the Bernoulli-number application (exercises not supplied), Exercise 4.1.  Lean notes: `order_mul`
  needs `NoZeroDivisors` — use `order_eq_nat` directly; `mk_one_mul_one_sub_eq_one` takes the ring
  explicitly; `derivative` has the ring implicit (`derivative A`, notation `d⁄dX` is scoped).

* **§4.2.5 Newton's method for functional inverses (2026-10-16).**  States: for `g` with inverse
  `h`, Newton on `f = y − g` gives `x_{j+1} = x_j + (y − g(x_j))/g'(x_j)`, evaluating only `g`,
  `g'`: `h` costs the same order as `g` when `g'` and division cost no more than `g`.  Example
  `g = ln`: (4.11) `x_{j+1} = x_j + x_j(y − ln x_j)` and Algorithm 4.1 LiftExp (`t = ln x_j` to
  `n` bits, `u = y − t`, `v = x_j u` to `n/2` bits, `x_{j+1} = x_j + v`).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/FunctionalInverse.lean` (all proven): `inverseStep`/`Seq`,
  `inverseStep_eq_newtonStep` (`a/(−b) = −(a/b)` makes this unconditional), `inverseStep_root`,
  `tendsto_inverseSeq` (generic Newton theorem with `f'' = −g''`); `expStep`/`expSeq`,
  `inverseStep_log`; `abs_log_one_add_sub_le` (`|ln(1+ε) − (ε − ε²/2)| ≤ 2|ε|³`, from Mathlib's
  `Real.abs_log_sub_add_sum_range_le` at `n = 2`, `x = −ε`); `expStep_rel`
  (`ε' = (1+ε)(1 − ln(1+ε)) − 1`), `abs_expStep_relError_le` (`≤ (9/4)ε²`); LiftExp:
  `liftExp_rel` (exact: `t = ln x_j + δ`, correction product with relative error `θ`, result
  `e^y(1 + ε − (1+ε)(1+θ)(ln(1+ε) + δ))`) and `abs_liftExp_relError_le` (`|ε|, |θ| ≤ η ≤ 1/2`,
  `|δ| ≤ η²` ⇒ `≤ 9η²`), which is the algorithm's precision claim up to the constant 9 (≈3 bits;
  MCA ignores constants).  Not formalized: the complexity statement ("same order as `g`" — no cost
  model), the `tan`/`arctan` example (same theorem, no specific content).  Design note: an
  `exp` built on a fast `ln` needs the log at full precision and the correction at half
  precision, exactly as the reciprocal; Newton-based `exp` is only worthwhile once `ln` is
  faster than the direct series (§4.4 ff.).  Lean notes: pass `(f := fun x => y - g x)`
  explicitly when the root hypothesis `f ζ = 0` is a beta-redex (`y − g ζ = 0` unifies the wrong
  way); `simp only [seq_eq]` does not rewrite an unapplied sequence in `Tendsto` — use `.congr`.

* **§4.2.6 Higher-order Newton-like methods (2026-10-16).**  States: a second-order Taylor
  approximation (4.12) gives the cubic iteration `x − f/f' − f²f''/(2f'³)`; for the reciprocal
  (4.13) `x + xε + xε²` (`ε = 1 − xy`), for `exp` by inversion (4.14) `x + xε + xε²/2`
  (`ε = y − ln x`); systematically `1/y = x ∑ εᵐ` gives the order-`k` iteration (4.15)
  `x ∑_{m<k} εᵐ`, and `e^y/x = exp ε` gives (4.16) `x ∑_{m<k} εᵐ/m!`; `k = 2` Newton, `k = 3`
  the cubic ones; generalizations in Ex. 4.3, 4.6.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/HigherOrder.lean` (all proven): `cubicStep` + the two
  instance identities (`field_simp; ring`); (4.15) `recipOrderStep`/`Seq` over any `CommRing`,
  `ringRecipError_recipOrderStep` (`ε' = ε^k`, via `mul_neg_geom_sum`) and `ε_j = ε_0^(k^j)`,
  `inv_eq_mul_tsum_geometric`; (4.16) `expOrderStep`/`_two`/`_three`, `exp_eq_mul_exp_sub_log`,
  `exp_eq_mul_tsum` (`Real.exp_eq_exp_ℝ` + `NormedSpace.exp_eq_tsum_div`), and the order-`k`
  absolute bound `abs_expOrderStep_sub_exp_le` from Mathlib's `Real.exp_bound`.  Not formalized:
  the generic `O(e³)` claim for `cubicStep` (the (4.12) derivation neglects terms; the two
  instances have exact error formulas instead), Exercises 4.3/4.6.  Design note: for the
  reciprocal, order `k` costs `k − 1` extra multiplications per step for `log₂ k` bits-doublings'
  worth of progress — the usual conclusion is that `k = 2` or `3` is best; decide when
  implementing, with the §3.4 exact division as the oracle.

* **§4.3 Argument reduction, introduction (2026-10-16).**  States: evaluate `f x` as reduce →
  evaluate (`f` or another `g`, e.g. `sin(x + π/2) = cos x`) → reconstruct by a functional
  identity; addition formulae (4.17) for `exp`, `log`, `sin`, `tan`; doubling (4.18)
  `exp 2x = (exp x)²`, tripling `sin 3x = 3 sin x − 4 sin³ x` (one function; the doubling needs
  `cos` too — fixed in §4.3.4, §4.9.1); additive (`x − kc`, periodic, `c = 2π`) vs
  multiplicative (`x/c^k`, `c = 2` for `exp`) reduction, both possible for `sin`; "increase"
  for `Γ` via `xΓ(x) = Γ(x+1)` (§4.5); none known for `erf`.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ArgumentReduction.lean` (all proven): structure
  `ArgumentReduction f` (reduce, `g`, reconstruct, spec), (4.17) incl. `tan_add'` proven directly
  from `sin_add`/`cos_add` under `cos x ≠ 0`, `cos y ≠ 0`, `1 − tan x tan y ≠ 0` (Mathlib's
  `Real.tan_add` has the `(2k+1)π/2` form), (4.18), tripling, `exp_eq_pow_two_pow`,
  `sin/cos_sub_int_mul_two_pi`, four scheme instances, `Gamma_add_nat`.  Not formalized: the
  `erf` remark; cost of reconstruction (no model).  Design note for the implementation phase:
  multiplicative reduction of `exp` by `2^k` costs `k` squarings and loses ≈`k` bits of relative
  accuracy (relative error doubles per squaring: `(1+ε)² ≈ 1 + 2ε`), so the working precision
  must grow by `k` bits — to be proven when the algorithm is specified (§4.3.1).

* **§4.3.1 Repeated doubling + §4.3.2 Loss of precision (2026-10-16).**  §4.3.1 states:
  `exp x = exp(x/2^k)^(2^k)`; for `|x| = Θ(1)` the reduced argument is `O(2^(−k))` so the series
  converges faster; cost `k` squarings; with naive series evaluation the optimal `k ~ √n` gives
  `O(√n M(n))` (beaten in §4.4.3); optimal `k` depends on `|x|` (Ex. 4.5).  §4.3.2 states:
  alternating series cancel — `exp(−10)` terms grow until `k > |x|`; 51 terms at 10 digits give
  ~3 digits; use `exp x = 1/exp(−x)`; or a sign-free series for a related function (erf, (4.22)
  vs (4.23); Ex. 4.19–4.20).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/RepeatedDoubling.lean` (all proven):
  `abs_exp_sub_sum_div_two_pow_le` (series error at `x/2^k`, from `Real.exp_bound`); the squaring
  error model `squareSeq t θ` with `squareSeq_eq` and `abs_squareSeq_sub_exp_le` — generic
  perturbation lemmas `|(1+a)^e − 1| ≤ (1+|a|)^e − 1`, the product version, `∏(1+|a_i|)^(e_i) ≤
  exp(∑ e_i|a_i|)`, `exp S − 1 ≤ 2S` (`S ≤ 1`, from `Real.exp_bound'` at `n = 1`) — REUSABLE for any
  error analysis of products of perturbed factors; conclusion: starting relative error `ε` and
  per-squaring relative errors `θ_i` give relative error `≤ 2(2^k|ε| + ∑ 2^(k−1−i)|θ_i|)`, i.e.
  the working precision must carry `k + 1` extra bits (confirms the design note of §4.3);
  `expTerm` with `expTerm_succ` (ratio `x/(m+1)`), monotonicity switch at `m + 1 = |x|`,
  `expTerm_neg_eq` (alternation), `abs_sum_perturbed_le` (generic), `sum_abs_expTerm_le`
  (`≤ exp|x|`, from `Real.sum_le_exp_of_nonneg`), `abs_sum_perturbed_le_of_nonneg` (relative `η`
  for `x ≥ 0`), `relative_loss_of_neg` (`exp|x| = exp(2|x|) exp x` for `x ≤ 0`: the cancellation
  factor), `exp_twenty_gt` (`10^8 < exp 20`, via `exp_one_gt_d9` and `2.7^20`), `exp_eq_inv_exp_neg`.
  Not formalized: the `O(√n M(n))` / optimal-`k` cost statements, Ex. 4.5/4.19/4.20, the erf
  series (await §4.4).  Lean notes: `Finset.prod_le_prod` for ℝ is now `prod_le_prod₀`-style —
  `gcongr with i _` sidesteps the name; `abs_of_pos (by positivity)` needs the target typed
  when several `|·|` are present; `set` definitions get unfolded inside `simp`/`congr` goals,
  so state `h1 : ∀ i ∈ range k, …` and `prod_congr rfl h1` explicitly.

* **§4.3.3 Guard digits (2026-10-16).**  States: guard digits = working precision beyond the
  target; too few → inaccurate, too many → expensive.  Example `exp`, `t = x/2^k = O(2^(−k))`: `t`
  to `n` bits gives `1 + t` to `n + k` bits, but forward summation at precision `n` keeps `n`;
  the `k` squarings lose ≈1 bit each → `n − k` bits; backward summation at precision `n + k`
  through the squarings → `n` bits.  Alternative: `expm1 x = exp x − 1` with a doubling formula
  avoiding loss of significance for small `|x|` (Ex. 4.7–4.9).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/GuardDigits.lean` (all proven): `abs_one_add_mul_sub_le`
  (`|tε| ≤ 2^(−(n+k))`), `relError_one_add_le` (relative `≤ 2^(1−(n+k))`, `k ≥ 1`),
  `abs_mul_one_add_sub_one_le` (compounding with the rounding at `n`); from §4.3.1's
  `abs_squareSeq_sub_exp_le`: `abs_squareSeq_sub_exp_le_of_uniform` (`|ε| ≤ 3η`, `|θ_i| ≤ η`,
  `2^(k+2)η ≤ 1` ⇒ relative `≤ 2^(k+3)η`; uses `∑_{i<k} 2^(k−1−i) = 2^k − 1` via
  `sum_range_reflect` + `geom_sum_eq`), `forwardSummation_bits` (`η = 2^(−n)` ⇒ `2^(−(n−k−3))`),
  `backwardSummation_bits` (`η = 2^(−(n+k))` ⇒ `2^(−(n−3))`) — the text's `n − k` vs `n` up to the
  constant 8; `expm1`, `expm1_two_mul`, `expm1_add_two_pos`, `expm1_two_mul_perturbed` (exact
  relative error `ε(2(e+1) + eε)/(e+2)`), `abs_expm1_two_mul_relError_le` (`≤ 2|ε| + ε²`, `x ≥ 0`),
  `expm1_of_exp_perturbed` (`ρ exp x` absolute), `expm1_le_mul_exp` (`exp x − 1 ≤ x exp x`),
  `relError_expm1_of_exp_ge` (`≥ |ρ|/x` for `x > 0`: unbounded as `x → 0`).  Not formalized: a
  rounding model of forward/backward summation itself (the bit counts are captured through the
  start error `ε` of the squaring model; a real summation model belongs with §4.4's series
  evaluation), Ex. 4.7–4.9.  Design note: our `AzFloat` ops are exactly rounded, so "working
  precision" = the `p` passed to each op; the Newton/series `exp` will take `p + k + guard` as
  working precision with `k` the reduction count, justified by `backwardSummation_bits`.

* **§4.3.4 Doubling versus tripling (2026-10-16).**  States: `sinh 2x = 2 sinh x cosh x` needs
  `cosh`; `cosh² − sinh² = 1` gives `2 sinh x √(1 + sinh²x)` (a square root); tripling (4.19)
  `sinh 3x = sinh x(3 + 4 sinh²x)`; but reducing through `exp` with (4.18) is usually cheaper
  (tripling = 1 mul + 1 square vs two squarings for a factor 4 > 3); drawback: cancellation in
  `e^x − e^(−x)` for small `|x|`, cured by (4.20) `sinh x = (expm1 x − expm1(−x))/2` (Ex. 4.10);
  more in §4.12 (FFT range).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/DoublingTripling.lean` (all proven): the three formulae
  (`cosh_eq_sqrt`, `sinh_two_mul_sqrt`, `sinh_three_mul'` from Mathlib's `sinh_three_mul`),
  `three_pow_lt_four_pow`, `sinh_of_exp_perturbed` (`±ρ` on the two exponentials → error
  `ρ cosh x`), `sinh_le_mul_exp` (`sinh x ≤ x eˣ`, all `x`), `relError_sinh_of_exp_ge`
  (`≥ |ρ|/(2x)`), `sinh_eq_expm1`, `relError_sinh_expm1_le` (`x ≥ 0`: relative `≤ η`).  Not
  formalized: the operation-count comparison beyond `3^k < 4^k` (no cost model), Ex. 4.10, §4.12.
  Design note: `sinh`/`cosh` will be built from `exp` (or `expm1` for `|x| < 1`), not from their
  own doubling/tripling formulae.

* **§4.4 Power series, introduction (2026-10-16).**  States: series for exp, ln(1+x), arctan,
  sinh; notation `x`, `n`, `d`; Taylor at `c`; (4.21) `exp x = ∑_{j<d} x^j/j! + R_d`,
  `|R_d| ≤ |x|^d e^|x|/d! ≤ e/d!` for `|x| ≤ 1`; Stirling ⇒ `d ~ n/lg n`, Horner `O(nM(n)/log n)`;
  forward recurrence `t_j = x t_{j−1}/j`, stop when `|t_d| < 2^(−n)/e` (no `d` in advance;
  backward/Horner needs it, Ex. 4.4); rounding model `◦(x op y) = (x op y)(1+δ)`, `|δ| ≤ ε`:
  `|t̂_j − t_j|/|t_j| ≤ 2jε + O(ε²)`, `|Ŝ_d − S_d| ≤ (d+2)eε + O(ε²) = O(nε)` ⇒ `ε = O(2^(−n)/n)`,
  `lg n` guard digits; backward slightly better; vary the working precision with the term size;
  large `x > 0`: `Ω(|x|)` terms; large `x < 0`: max term `≈ e^|x|/√(2π|x|)` vs result `e^(−|x|)`,
  `2|x|/log 2` guard digits (Lehmer's "catastrophic cancellation"), avoid via `1/exp(−x)`; erf
  series (4.22) (alternating, no exp) vs (4.23) (positive terms, needs `e^(−x²)`), both `Ω(x²)`
  terms for large `|x|` → asymptotic `erfc` (§4.5), continued fraction (4.40) in between.
  Formalized in `Azurite/BrentZimmermann/Chapter4/PowerSeriesEval.lean` (all proven):
  `hasSum_exp_series` (via `Real.exp_eq_exp_ℝ` + `NormedSpace.expSeries_div_hasSum_exp`),
  `hasSum_log_one_add_series` (from `Real.hasSum_pow_div_log_of_abs_lt_one` at `−x`);
  `abs_exp_sub_sum_le` for ALL `x` (tail = `∑' x^(n+d)/(n+d)!` via
  `Summable.sum_add_tsum_nat_add'` with `f` given explicitly; `d!n! ≤ (n+d)!` from
  `Nat.factorial_mul_factorial_dvd_factorial_add`; `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`,
  `tsum_mul_left`), `abs_exp_sub_sum_le_of_abs_le_one`, `exp_series_terms_suffice`,
  `exp_series_stop`; `expPartial`/`expPartial_succ`; rounding: `roundedExpTerm` (one combined
  relative error `θ_j` per term step, `|θ_j| ≤ 3ε` for mul+div), `roundedExpTerm_eq`,
  `abs_roundedExpTerm_sub_le` (`≤ 6jε|t_j|` for `3jε ≤ 1`, via the §4.3.1 product lemmas),
  `roundedSum` and the GENERIC `roundedSum_sub_le` (error recurrence
  `A_{j+1} = A_j + (t̂ − t) + σ(S_j + A_j + t̂)`; REUSABLE for any forward summation),
  `exp_roundedSum_error` (`≤ 46dε`, constants: `exp 1 ≤ 3`, `(1+ε)^d ≤ 2` from `exp_sub_one_le_two_mul`),
  `exp_guard_digits`, `guard_digits_of_neg`.  Not formalized: Stirling and `d ~ n/lg n`, Horner
  cost, the max-term estimate, arctan/sinh series (not in Mathlib), erf (no `Real.erf` in
  Mathlib; (4.22)/(4.23) deferred to §4.5), variable working precision (an algorithm, later).
  Lean notes: identifiers cannot contain combining accents (`t̂` fails to parse — use `tc`);
  `Summable.sum_add_tsum_nat_add'` needs `(f := …)` explicitly or `isDefEq` times out;
  `Real.logb` needs `Mathlib.Analysis.SpecialFunctions.Log.Base`.  Design note: our series
  `exp` will stop by the `exp_series_stop` test on the current term, work at `p + lg d + c`
  bits, and the whole error budget is `exp_guard_digits` + the §4.3 squaring loss.

* **§4.4 Assumption on the coefficients; radius of convergence (2026-10-16).**  States: assume
  `a_{j+δ}/a_j = R(j)` rational (`δ` fixed, usually 1 or 2), so the `a_j` are generated
  sequentially (exp: `1/(j+1)`); covers hypergeometric functions (holonomic: §4.9.2); `tan`
  fails it (tangent/Bernoulli numbers, §4.7.2) → Newton on `arctan` or `sin/cos`.  Entire
  functions (exp, sin): `deg den > deg num`, series converges everywhere; otherwise a boundary
  singularity: `ln(1+x)` and `arctan` have radius 1 (`arctan`: poles at `±i` despite being bounded
  on ℝ).  Formalized in `Azurite/BrentZimmermann/Chapter4/CoefficientRatio.lean` (all proven):
  `structure RationalRatio a δ` (num/den polynomials, `den` nonvanishing on ℕ, the ratio law),
  `R`, `eq_mul_prod`/`eq_mul_prod_one`, `tendsto_zero_of_degree_lt`,
  `tendsto_leadingCoeff_div_of_degree_eq` (Mathlib's `Polynomial.div_tendsto_atTop_*` composed
  with `tendsto_natCast_atTop_atTop`), `tendsto_ratio_of_degree_eq`; instances `expRatio`,
  `logRatio`, `arctanRatio` (zero even coefficients handled by the `if`), `arctanCompressedRatio`
  (`y = x²`); ratio test wrappers around Mathlib's `summable_of_ratio_test_tendsto_lt_one` /
  `not_summable_of_ratio_test_tendsto_gt_one` with `|L|` (so signed limits like `−1` work);
  radius 1 results for log and arctan, harmonic divergence at `x = −1`
  (`Real.not_summable_one_div_natCast` + `summable_nat_add_iff`).  Not formalized: `tan` has no
  rational ratio (would need the tangent numbers), hypergeometric/holonomic generalities
  (§4.9.2), the complex singularities themselves.  Lean notes: `show` cannot see through a
  `noncomputable def` structure literal — use `have hn : S.num = … := rfl` then `rw`; ascribe
  `(X + C 2 : ℝ[X])` and `(-1 : ℝ)` in leading-coefficient equations or the division elaborates
  in the wrong type; `if_pos/if_neg` are deprecated for `ite_eq_left/right`.

* **§4.4.1 Direct evaluation + §4.4.2 Series with argument reduction (2026-10-16).**  States:
  with `|x| ≤ 1/2` and radius ≥ 1, `n + O(1)` terms → `O(nM(n))` (`O(nM(n)/log n)` entire);
  reducing to `|x| < 2^(−k)` leaves `O(n/k)` terms, total `O((k + n/k)M(n))`, `k ~ √n` →
  `O(√n M(n))`; reductions `exp x = exp(x/2)²`, `log1p x = 2 log1p(x/(1+√(1+x)))`,
  `arctan x = 2 arctan(x/(1+√(1+x²)))` (square roots at `O(M(n))`, §3.5; Ex. 4.8–4.9);
  symmetries: `ln((1+y)/(1−y)) = 2∑ y^(2j+1)/(2j+1)`, `y = x/(2+x)`, halves the terms and
  `y < x/2`, usable once (Ex. 4.11).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/SeriesReduction.lean` (all proven): `abs_tail_le_of_abs_le`
  (geometric tail, `Summable.of_nonneg_of_le` + `tsum_geometric_of_lt_one`),
  `terms_suffice_direct`, `terms_suffice_reduced` (`A = 0` split off), `exp_terms_suffice_reduced`,
  `two_sqrt_le_add_div` (AM–GM), `exp_eq_sq_exp_half`, `log_one_add_eq_two_mul_log_one_add`
  (`1 + x/(1+s) = s` with `s = √(1+x)`, then `Real.log_sqrt`), `div_one_add_sqrt_lt_half`,
  `arctan_eq_two_mul_arctan` (half-angle via `sin_two_mul`/`cos_two_mul` at `θ/2`, `sin_arctan`,
  `cos_arctan`, `arctan_tan`), `abs_div_one_add_sqrt_sq_le_half`, `expHalf`, `arctanHalf`
  (`log1p` needs `x > −1` so no total instance), symmetric series via
  `Real.hasSum_log_sub_log_of_abs_lt_one` + `Real.log_div`.  Not formalized: cost statements
  (no model), Ex. 4.8/4.9/4.11.  Design note: the planned `exp` = reduce by `2^k` (`k ≈ √p`),
  series with `exp_series_stop`, `k` squarings at `p + k + lg d + c` bits; `log1p` and `arctan`
  by the same scheme with `sqrtPrecRound` in the reduction; `ln(1+x)` via the symmetric series
  as the first step.

* **§4.4.3 Rectangular series splitting — classical splitting (2026-10-16).**  States: evaluate
  `P(x) = ∑_{j<d} a_j x^j` at an `n`-bit `x`; coefficients/ratios are `O(log n)`-bit rationals, so
  scalar products are cheap and non-scalar (two `n`-bit numbers) cost `M(n)`; `O(√n)` non-scalar +
  `O(n)` scalar products + `O(n)` additions, `O(√n)` storage; classical splitting `d = jk`,
  `y = x^k`, `P = ∑_ℓ y^ℓ P_ℓ(x)`, powers `x², …, x^k` (even ones by squaring), inner `P_ℓ` by
  scalar products (NOT Horner), outer Horner in `y`; example `d = 12 = 3·4`: 5 vs `d − 2 = 10`.
  Formalized in `Azurite/BrentZimmermann/Chapter4/RectangularSplitting.lean` (all proven):
  `polyEval_split` (induction on `j` with `sum_range_add`), `hornerEval` + `hornerEval_eq`
  (induction generalizing the coefficient function), `polyEval_eq_horner`, `pow_two_mul_eq_sq`,
  `classicalNonscalar` and its three facts (`≤ d − 2` for `j, k ≥ 2`; `3·4 ↦ 5` by `decide`;
  `≥ 2√d − 2` via `two_sqrt_le_add_div`).  Not formalized: a scalar/non-scalar cost model for
  the evaluation itself (the count is a definition, not derived from an evaluation trace), the
  storage bound, hypergeometric generalization.  Design note: the series `exp` should use
  rectangular splitting with `k ≈ √d` precomputed powers and the inner sums as
  `AzNat`-coefficient × `AzFloat` scalar products (cheap: the coefficient is a small rational —
  for `exp`, accumulate `∑ x^m · (k! / (kℓ+m)!)`-style with a common denominator to keep the
  scalar products integer); modified splitting (next chunk) may change this.

* **§4.4.3 Rectangular series splitting — modular splitting (2026-10-16).**  States: transpose
  the array (generalized odd–even scheme, §1.3.5): `y = x^j`, `P(x) = ∑_{ℓ<j} x^ℓ P_ℓ(y)`,
  `P_ℓ(y) = ∑_{m<k} a_{jm+ℓ} y^m`; compute `y, y², …, y^(k−1)`, accumulate row sums `S_ℓ` by scalar
  products, finish with `∑ x^ℓ S_ℓ` (Horner); complexity almost the same (Ex. 4.12); example
  `12 = 3·4`: 6 non-scalar (4 for `y` and powers, 2 for the combination).  Formalized in the same
  file `RectangularSplitting.lean` (all proven): `modularPoly`, `polyEval_modular_split`
  (induction on `k`, `Nat.mul_succ` + `sum_range_add`), `polyEval_eq_horner_modular`,
  `modularNonscalar` (`(j−1) + (k−2) + (j−1)`), `modularNonscalar_example` (6),
  `modularNonscalar_eq` (= classical + `(j − 2)`, so swapping roles makes them within a constant
  — the "almost the same").  Not formalized: Ex. 4.12, the transposition as an explicit matrix
  identity between `innerPoly` and `modularPoly`.  Design note: modular splitting is the natural
  fit for our forward term recurrence (rows are strided subsequences of the same coefficient
  stream), so prefer it when the `exp` series is implemented; the final Horner in `x` costs
  `j − 1` non-scalar products either way.

* **§4.4.3 Complexity of rectangular series splitting (2026-10-16).**  States: `O(j + k)`
  non-scalar (`M(n)` each) + `O(jk)` scalar (`c(d)n` each, `c(d) = O(1)`, Ex. 4.13); `j ~ k ~ √d`
  → (4.24) `O(√d M(n) + dn c(d))`; with argument reduction `T(n) = O((n/d)M(n) + √d M(n) + dn)`
  (Ex. 4.14); case 1 `M(n) ≫ n^(4/3)` (schoolbook, Karatsuba `lg 3 > 4/3`, Toom 3–6, not Toom 7
  as `log_7 13 < 4/3`): `d ~ n^(2/3)`, `T = O(n^(1/3) M(n)) ≫ n^(5/3)`; case 2 `M(n) ≪ n^(4/3)`:
  balance first and last terms, `Θ(n √M(n)) ≫ n^(3/2)`; AGM's `O(n^(1+ε))` out of reach (§4.8).
  (The first transcription read `d = M(n)`; the source says `d = √M(n)`, as formalized.)  Formalized
  in `Azurite/BrentZimmermann/Chapter4/SplittingComplexity.lean` (all proven; costs as reals, no
  operation-count model): `splitCost`, `splitCost_ge` (`n^(1/3) M` for all `d ≥ 1`, by cases on
  `d ≤ n^(2/3)`), `splitCost_le_case1` (`3 n^(1/3) M`), `splitCost_le_case2` (`3 n √M`, via
  `M^(1/4) ≤ n^(1/3)` and `√M ≤ n^(2/3)`), `rpow_three_halves_le_mul_sqrt`,
  `four_thirds_lt_logb_iff`, `karatsuba_exponent` (27 > 16), `toom3` (125 > 81), `toom4`
  (343 > 256), `toom5` (729 > 625), `toom6` (1331 > 1296), `toom7_exponent` (2197 < 2401).  Not
  formalized: the `O(·)` statements as asymptotics (constants given instead), Ex. 4.13/4.14, `c(d)`.
  Design note: Azurite's ladder is schoolbook/Karatsuba/Toom-3/Toom-4/FFT; below the FFT
  cutoff we are in case 1 (`d ~ p^(2/3)` terms after reduction by `2^k`, `k ~ p^(1/3)`); in the
  FFT range (`M(n) ~ n log n log log n ≪ n^(4/3)`) case 2 applies — the series `exp` should pick
  `(k, d)` from the measured `M(p)` rather than a fixed `√p` rule.  Lean notes: `Real.rpow`
  bookkeeping via `rpow_add`/`rpow_mul` + `norm_num` on the exponents; `Real.log_lt_log_iff`
  rewrites the wrong side inside an `↔` — split with `constructor` and use
  `Real.log_lt_log` / `.mp` directly.

* **§4.5 Asymptotic expansions, introduction (2026-10-16).**  States: `E₁(x) = ∫_x^∞ e^(−u)/u`
  (4.25) (also `Ei`, `li`, principal values); power series (4.26) `E₁ + γ + ln x = ∑ (−1)^(j−1) x^j/(j!j)`
  bad for large `x`; instead (4.27) `e^x E₁(x) = ∑_{j=1}^k (j−1)!(−1)^(j−1)/x^j + R_k(x)`,
  (4.28) `R_k = k!(−1)^k e^x ∫_x^∞ e^(−u)/u^(k+1)`, `|R_k| < k!/x^(k+1)`; `R_k → 0` in `x`, not in
  `k` (divergent, asymptotic (4.29)); error often ≤ first omitted term; alternating ⇒ value between
  consecutive partial sums (true here for `x > 0`); `k = ⌊x⌋`: relative error `O(√x e^(−x))` via
  (4.30) `|R_k(k)| ≤ k!/k^(k+1) = O(k^(−1/2) e^(−k))`; precision `n` once `x > n ln 2 + O(ln n)`;
  two-sided Stirling with `e^(1/(12k))`; small `x`: Ex. 4.19 cancellation-free series.
  Formalized in `Azurite/BrentZimmermann/Chapter4/AsymptoticExpansion.lean` (all proven, Lebesgue
  integrals on `Ioi x`): `expTail`, `expIntegral`, `integrableOn_expTail` (domination by
  `e^(−u) x^(−(k+1))`, `Integrable.mono'`), `expTail_nonneg/pos` (`setIntegral_pos_iff_support_of_nonneg_ae`,
  `volume (Ioi x) = ⊤`), `expTail_le`, `expTail_succ` (Mathlib's
  `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = t^(−(k+1))`, `v = −e^(−t)`; boundary terms by
  continuity at `x` and a squeeze at `∞`), `asymptoticTerm` (indexed from 0: text's `j+1`),
  `asymptoticRemainder`, `asymptoticRemainder_succ`, `exp_mul_expIntegral_eq` (4.27),
  `abs_asymptoticRemainder_le` (≤, the text's < not needed), `abs_asymptoticRemainder_le_abs_term`,
  `tendsto_asymptoticRemainder_atTop`, `not_summable_asymptoticTerm`
  (`not_summable_of_ratio_norm_eventually_ge` with ratio `(j+1)/x ≥ 2`), `sign_asymptoticRemainder`,
  `between_partialSums` (product of the two remainders `< 0`), `factorial_le_stirling_upper`
  (`Stirling.stirlingSeq'_antitone` + `stirlingSeq_one`), `abs_asymptoticRemainder_self_le` (4.30
  with constant `e`).  Not formalized: (4.26) (needs `Real.eulerMascheroniConstant` + the integral
  representation), `Ei`/`li`/complex domain, the `e^(1/(12k))` Stirling refinement (Mathlib has
  only the lower bound `le_factorial_stirling`), the `x > n ln 2 + O(ln n)` threshold, Ex. 4.16/4.19.
  Design note: an `E₁`/`erfc` implementation would switch between the series and the asymptotic
  expansion at `x ≈ p ln 2`; `between_partialSums` gives a rigorous two-sided bracket for a Ziv-style
  correct rounding of the asymptotic branch.  Lean notes: `IntegrableOn.congr_fun` must be called
  with the explicit name when the integrable term was built by `Integrable.const_mul` (field
  notation resolves to `And`); `HasDerivAt` of `−exp(−t)` via a typed `have` + `congr_deriv`;
  `abs_of_pos (by positivity)` grabs the first `|·|` — name the argument.

* **§4.5 Euler–Maclaurin examples: γ and ζ (2026-10-16).**  States: asymptotic expansions for
  erfc, Γ, Bessel; Euler–Maclaurin `∑ f(k) − ∫ f ~ (f(a)+f(b))/2 + ∑ B_{2k}/(2k)! (f^(2k−1)(b) −
  f^(2k−1)(a))`; γ (4.31) converges slowly → split at `p`, EM on `1/x` → (4.32)
  `γ ~ H_p − ln p + ∑ B_{2k}/(2k) p^(−2k)` (faster Bessel-based method in §4.12); ζ (4.33), EM
  (4.34)–(4.36) with terms `T_{k,p}(s) = B_{2k}/(2k)! p^(1−s−2k) ∏(s+j)`, `|E_{m,p}| <
  |T_{m+1,p}(s)(s+2m+1)/(σ+2m+1)|`; for polynomial time both `m, p → ∞` so Bernoulli numbers must
  be computed on demand (§4.7); prefer expansions with known coefficients (`ln Γ` (4.38) vs
  Stirling for Γ, Ex. 4.42).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/AsymptoticExamples.lean` (all proven):
  `tendsto_harmonic_sub_log'` (Mathlib), `harmonic_sub_log_sub_gamma_bounds` (from Mathlib's
  `eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` and `log(1 + 1/N) ≤ 1/N`); `zetaReal`,
  `zetaReal_eq_riemannZeta` (`zeta_eq_tsum_one_div_nat_cpow` + `Complex.ofReal_tsum`/`ofReal_cpow`),
  `zetaTail`, `summable_zetaTail`, `zetaReal_eq_sum_add_tail`, `antitoneOn_rpow_neg`,
  `integral_Ioi_rpow_neg`, `zetaTail_bounds` (finite `AntitoneOn.integral_le_sum`/`sum_le_integral`
  on `[p, p+a]`, then `a → ∞` with `intervalIntegral_tendsto_integral_Ioi` and
  `HasSum.tendsto_sum_nat`, `le_of_tendsto_of_tendsto`), `abs_zetaReal_sub_euler_maclaurin_zero_le`
  ((4.34) with `m = 0`, error `≤ p^(−s)/2`), `zeta_tail_le_of_pow`, `zetaEMTerm`, `zetaEMTerm_one`.
  Not formalized: Euler–Maclaurin itself (no Mathlib version), hence (4.32) and (4.34)–(4.36) for
  `m ≥ 1`; analytic continuation; the lower bound showing (4.31)'s error is really `Θ(1/N)`.
  Design note: computing `γ` or `ζ(s)` to `p` bits via EM needs Bernoulli numbers `B_2..B_{2m}` with
  `m ~ p/log p` — Azurite has `AzRat`; a `bernoulli` routine (§4.7.2, tangent numbers) is the
  prerequisite; the `m = 0` bracket is already a correct-rounding-capable two-sided bound for
  `ζ(s)` at exponential cost.  Lean notes: `Real.rpow_le_rpow_of_nonpos` is the antitone lemma;
  `Summable.sum_add_tsum_nat_add'` with `k := 1` plus `sum_range_one` peels the first tail term;
  `congr 3; omega` closes `((↑(j + (p+1)))^s)⁻¹ = ((↑(j+1+p))^s)⁻¹`.

* **§4.5 The error function (2026-10-16).**  States: (4.22)/(4.23) need `Ω(x²)` terms (erf 1000
  to 6 digits: 2718279 terms); erfc (4.37) `e^(−x²)/(x√π) ∑ (−1)^j (2j)!/j! (2x)^(−2j)`, error ≤ next
  term and of its sign; `erfc 1000 ≈ 1.86·10^(−434298)`; the sum diverges, `j`-th term
  `~ √2 (j/(ex²))^j`, terms decrease while `j < x² + 1/2`, smallest `~ e^(−x²)`, so `x > √(n ln 2)`
  (833 for `n = 10⁶`; confirmed by the user as `√(n ln 2)`); only
  `m = n − λ` bits of erfc needed (`erfc ≈ 2^(−λ)`); for `j < x²`, (4.22)'s terms grow and (4.37)'s
  shrink ⇒ prefer (4.37) when accurate enough; Algorithm 4.2 Erf (`m = ⌈n − (x² + ln x +
  ln π/2)/ln 2⌉`, `(m + 1/2) ln 2 < x²` ⇒ asymptotic at precision `m`, else (4.22) for `x < 1`,
  (4.23) otherwise); `j₀` root of `j(ln j − 2 ln x − 1) = n ln 2`; examples `x = 800, 589`.
  Formalized in `Azurite/BrentZimmermann/Chapter4/ErrorFunction.lean` (all proven):
  `gaussTail`/`erfc`/`erf` (own definitions; Mathlib has no erf), `integrableOn_exp_neg_sq_Ioi`
  (from `integrable_exp_neg_mul_sq`), `gaussTail_succ` (parts with `u = t^(−(2k+1))`,
  `v = −e^(−t²)/2`; the `∞` boundary via `e^(−t²) ≤ e^(−t)` for `t ≥ 1`), `gaussTail_le`,
  `erfcCoeff`/`_succ`/`_zero`, `erfcTerm`, `erfcRem`, `erfcRem_succ`, `erfc_eq_sum_add_rem` (4.37),
  `abs_erfcRem_le_abs_term`, `sign_erfcRem`, `erfc_le_leading`, `leading_mul_le_erfc`,
  `erfcTermMag_succ_lt`, `pow_div_factorial_le_succ`, `erfcCoeff_le_stirling` (upper Stirling for
  `(2j)!`, lower for `j!`), `erfcTermMag_le`, `erfSeriesTerm_le_two_pow` (`x^(2j)/j! ≤ 2^(−n)` from
  `j! ≥ (j/e)^j`), `erf_error_of_erfc`, `asymptotic_gives_bits` (constant `(m + 4) ln 2` instead of
  `(m + 1/2) ln 2`: our term bound has constant `2e²/√π ≈ 8.3 ≤ 16`).  Not formalized: the link
  to `(2/√π)∫_0^x e^(−u²)` and oddness (would use `integral_gaussian`), the series (4.22)/(4.23)
  as series of erf (need the integral representation), the numerical examples, (4.40).
  Design note: `erf`/`erfc` implementation = Algorithm 4.2 with our `exp`; the bracket
  `leading_mul_le_erfc`/`erfc_le_leading` plus `sign_erfcRem` give two-sided bounds for correct
  rounding of the asymptotic branch; the series branch needs the §4.4 machinery with
  `j₀` from `erfSeriesTerm_le_two_pow`.  Lean notes: build `HasDerivAt (fun t => -t^2)` by
  `(hasDerivAt_pow 2 t).neg.congr_deriv` (a `simpa` produces an instance-path mismatch);
  `Even.pow_nonneg (even_two_mul j)` for `0 ≤ x^(2j)`; `Real.pi_gt_three` lives in
  `Mathlib.Analysis.Real.Pi.Bounds`.

* **§4.5 Stirling's asymptotic expansion of ln Γ (2026-10-16).**  States: (4.38) `ln Γ(x) =
  (x − 1/2) ln x − x + ln(2π)/2 + ∑_{k<m} B_{2k}/(2k(2k−1)x^(2k−1)) + R_m`, `|R_m| ≤` first omitted
  term, same sign (complex `|arg x| < π` version more delicate); ratio `t_{k+1}/t_k ≈ −(k/(πx))²`,
  terms grow for `k > πx`, so `ln|R_m(x)| > −2πx ln x + O(x)`; shift by `Γ(x+1) = xΓ(x)` to a large
  `x' = x + δ` (Ex. 4.21).  Formalized in `Azurite/BrentZimmermann/Chapter4/StirlingLogGamma.lean`
  (all proven except the remainder bound, which is stated only as a definition `stirlingRem`):
  `zetaReal_two_mul_eq` (Mathlib's `hasSum_zeta_nat`), `one_le_zetaReal_two_mul`,
  `zetaReal_two_mul_le` (`≤ ζ(2) = π²/6` via `hasSum_zeta_two`), `bernoulli_two_mul_eq_zeta`,
  `sign_bernoulli_two_mul` (alternation), `abs_stirlingTerm_eq`, `stirlingTerm_ratio_bounds`
  (`(2k)(2k−1)/(2(2πx)²) ≤ |t_{k+1}/t_k| ≤ 2(2k)(2k−1)/(2πx)²`), `abs_stirlingTerm_lt_succ`,
  `mul_log_ge_neg_inv_exp` (`y ln y ≥ −1/e`), `div_pow_self_ge` (`(u/c)^u ≥ e^(−c/e)`),
  `abs_stirlingTerm_ge` (`|t_k| ≥ e^(−2πx)/(2π²x)` — the minimal term is `≈ e^(−2πx)`, i.e. about
  `2πx/ln 2` bits attainable; the text's `−2πx ln x + O(x)` is the weaker form),
  `log_Gamma_eq_log_Gamma_add_sub`.  Not formalized: (4.38) with its remainder bound (needs
  Binet's formula / Euler–Maclaurin for ln Γ; Mathlib has neither), the complex version, Ex. 4.21.
  Design note: a `logGamma`/`Gamma` implementation = shift by `δ ≈ p ln 2/(2π)` then (4.38) with
  `m ≈ πx'` terms; Bernoulli numbers `B_2..B_{2m}` via §4.7.2; the sign/next-term facts give the
  bracket for correct rounding once (4.38) is available as a theorem (external proof needed).
  Lean notes: `zetaReal (2 * k)` elaborates with `2 * (k : ℝ)` — convert to `((2 * k : ℕ) : ℝ)` with
  `push_cast; ring` before `Real.rpow_natCast`; `generalize hε : (-1)^(k+1) = ε` and `ε^2 = 1`
  make the sign algebra a plain `calc`; `Summable.le_tsum` (not `le_tsum`); `Real.pi_lt_d2` for
  `π < 3.15`.

* **§4.6 Continued fractions, introduction (2026-10-16).**  States: `e^x E₁(x)` as a continued
  fraction, shorthand `b₀ + a₁/b₁+ a₂/b₂+ …` (4.39) `1/x+ 1/1+ 1/x+ 2/1+ 2/x+ 3/1+ …`; (4.40)
  `erfc x = (e^(−x²)/√π) 1/x+ (1/2)/x+ (2/2)/x+ …`; formal definition via `(a_j)_{j≥1}`, `(b_j)_{j≥0}`
  in `Ĉ`, value `lim f_k`, `k`-th approximant (4.41); Euler's (4.39) converges for all `x > 0`, best
  for `E₁` between cancellation and asymptotic regimes, slow for small `x`: use for
  `x ∈ (c₁n, c₂n)`, `c₁ ≈ 0.1`, `c₂ = ln 2` (Ex. 4.24).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ContinuedFraction.lean` (all proven) on Mathlib's
  `GenContFract`: `contFrac` (via `Stream'.Seq.ofStream`; `get?`/`head`/`tail` are `rfl`),
  `approximant := convs'`, `approximant_succ` (shift lemma, `rfl` after `convs'Aux_succ_some`),
  `HasContFracValue`, continuant initial values and recurrences re-exported from Mathlib
  (`zeroth_num_eq_h`, `first_num_eq`, `nums_recurrence`, …), `approximant_eq_convs` (Mathlib's
  `convs_eq_convs'` needs positive partial numerators/denominators), (4.39)/(4.40) coefficient
  sequences (`eulerNum j = max 1 ⌊j/2⌋`; `erfcCFNum 1 = 1`, else `(j−1)/2`), first two
  approximants (`1/x`, `1/(x+1)`; `1/x`, `1/(x + 1/(2x))`), `erfcCF_approximant_two_mem`.  Not
  formalized: convergence of (4.39)/(4.40) to `e^x E₁`/`erfc` (needs Stieltjes/hypergeometric
  continued-fraction theory; none in Mathlib), the `(c₁n, c₂n)` interval, Ex. 4.24, `Ĉ`.  Design
  note: continued-fraction evaluation = either backward recurrence from `f_k` (nested, needs `k`
  in advance) or forward continuants `A_k/B_k` (Mathlib's `nums`/`dens`, stoppable), both
  `O(k)` divisions/multiplications — expected to be the subject of the next chunks; our `AzFloat`
  has exact `divPrecRound` for the division steps.  Lean notes: `convs_eq_convs'` takes the
  positivity hypothesis in the form `∀ {gp m}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b`.
* **§4.6 Evaluating continued fractions; Theorem 4.1 (2026-10-16).**  States: for the finite
  fraction `y = a₁/b₁+ … a_k/b_k` (4.42) the backward recurrence `R_k = 1`, `R_{k−1} = b_k`,
  `R_j = b_{j+1}R_{j+1} + a_{j+2}R_{j+2}` (4.43) gives `y = a₁R₁/R₀` via the invariant
  `R_j/R_{j−1} = 1/b_j+ a_{j+1}/b_{j+1}+ … a_k/b_k`; the forward recurrence `P₀ = 0, P₁ = a₁, Q₀ = 1,
  Q₁ = b₁`, `P_j = b_jP_{j−1} + a_jP_{j−2}`, `Q_j` likewise (4.44) gives `y = P_k/Q_k`; backward
  needs `k` in advance, forward can stop when `D_k = P_k/Q_k − P_{k−1}/Q_{k−1}` (4.45) is small but
  costs twice as much and may be less stable; strategy: forward in single precision to find `k`,
  then backward in multiple precision; compute `D_k` by `D₁ = a₁/b₁`, `D_j = −a_jQ_{j−2}D_{j−1}/Q_j`
  (4.46) to avoid cancellation.  Theorem 4.1: for `a_j, b_j > 0` (`j ≥ 1`), `(f_{2k})` strictly
  increasing, `(f_{2k+1})` strictly decreasing, so `f_{2k} < f < f_{2k+1}` and
  `|f − (f_{m−1}+f_m)/2| < |f_m − f_{m−1}|/2`.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ContinuedFractionEval.lean` (all proven), with `b₀` kept as the
  head so (4.42) is `approximant a b k` at `b 0 = 0`: `tailFrac` (well-founded on `k + 1 − j`;
  `tailFrac_shift`, `approximant_eq_tailFrac`, `tailFrac_nonneg`), `backR` (well-founded on
  `k − j`; `backR_pos`, invariant in product form `backR_pred` and quotient form `backR_div`,
  `approximant_eq_backR`), forward recurrence = Mathlib continuants (`dens_pos`), `diff` (4.45)
  with `det_succ` (`Δ_{j+1} = −a_{j+1}Δ_j`), `diff_eq_det_div`, `diff_one`, `diff_succ` (4.46),
  `sign_diff`, `abs_diff_succ_lt` (uses `Q_{j+2} > a_{j+2}Q_j`), `diff_odd_pos`, `diff_even_neg`,
  `approximant_even_strictMono`, `approximant_odd_strictAnti`, `approximant_even_lt_odd` (through
  `max k m`), and with `HasContFracValue`: `approximant_even_lt`, `lt_approximant_odd`
  (`Monotone.ge_of_tendsto`/`Antitone.le_of_tendsto` on the subsequences), `abs_sub_midpoint_lt`.
  Not formalized: the cost/stability remarks, the single-precision forward pass, the claim that
  the forward recurrence is "twice as expensive".  Design note for the eventual `AzFloat`
  implementation: evaluate backward with `R` as exact `AzRat` or as `AzFloat` with a few guard
  bits, choosing `k` from a cheap forward pass at low precision with the (4.46) stopping rule;
  Theorem 4.1 gives a rigorous bracket `(f_{m−1}, f_m)` for `a_j, b_j > 0`, i.e. a certified
  error bound `|f_m − f_{m−1}|/2` from the midpoint, which fits the Ziv-style
  `(value, Ordering)` API.  Lean notes: `induction'` is no longer available — write the
  "strong induction on the measure" proofs as recursive theorems with `termination_by`
  (`tailFrac_shift`, `tailFrac_nonneg`, `backR_pred`, `backR_pos`); `positivity` does not look
  inside conjunctions — `obtain ⟨ha, hb⟩ := hpos j hj` first; index normalization
  `show 2 * k + 1 + 1 = 2 * k + 2 by omega` is needed before `rw [abs_of_pos h]` since `rw` is
  syntactic; `tendsto_atTop_mono (fun k => by show k ≤ _; omega) tendsto_id` for the subsequence
  `2k` (omega does not unfold `id`); `field_simp` now closes the goals of `backR_pred`/`diff_succ`
  outright (a trailing `ring` errors with "No goals").
* **§4.7 Recurrence relations, introduction (2026-10-16).**  States: continued fractions are a
  special case of evaluation by recurrences; Bessel functions `J_ν(x)` (`ν ∈ ℤ`, `x ∈ ℝ` here) via
  the generating function `exp((x/2)(t − 1/t)) = ∑_{ν∈ℤ} t^ν J_ν(x)` (4.47) or the power series
  `J_ν(x) = (x/2)^ν ∑ (−x²/4)^j/(j! Γ(ν+j+1))` (4.48, also for `ν ∉ ℤ`); second kind
  `Y_ν(x) = lim_{μ→ν} (J_μ cos πμ − J_{−μ})/sin πμ` (4.49); both solve
  `x²y'' + xy' + (x² − ν²)y = 0` (4.50).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/Bessel.lean` (all proven; Mathlib has no Bessel functions):
  `besselJTerm`/`besselJ` from (4.48) — Mathlib's `Real.Gamma` is `0` at non-positive integers,
  so `1/Γ = 0` kills the first `−ν` terms for `ν < 0` and (4.48) literally gives the standard
  `J_{−n} = (−1)^n J_n` (`besselJ_neg`); `abs_inv_Gamma_int_le_one`, `summable_besselJTerm`;
  factorial form `besselJNat n x = ∑ (−1)^j/(j!(n+j)!) (x/2)^(2j+n)` (`besselJ_natCast`);
  `besselJ_zero_left` (`J_0(0) = 1`), `besselJ_zero_of_ne`; majorant
  `besselBound R n j = (4(R+1))^(2j+n)/j!` for the series and its first two termwise derivatives
  on `|x| ≤ R` (`abs_besselCoeff_mul_le`, using `m^k ≤ 4^m`); (4.47) as
  `hasSum_besselJ_generating : HasSum (fun ν : ℤ => t^ν J_ν(x)) (exp((x/2)(t − 1/t)))` for
  `t ≠ 0`: Cauchy product of the two exponential series (`summable_mul_of_summable_norm`,
  `tsum_mul_tsum_of_summable_norm`), regrouped along the fibers of `(a, b) ↦ a − b` through the
  bijection `pairEquiv : ℕ × ℕ ≃ ℤ × ℕ`, `(a, b) ↦ (a − b, min a b)`, and
  `HasSum.prod_fiberwise`, each fiber summed by `hasSum_fiber_nonneg`/`hasSum_fiber_neg`; (4.50)
  via termwise differentiation (`hasDerivAt_tsum_of_isPreconnected` on `ball 0 (|x|+1)`, twice:
  `hasDerivAt_besselJNat`, `hasDerivAt_besselJNat'`), the termwise identity `bessel_ode_term`
  (`c_j (m(m−1)u^(m−2)/4 · x² + m u^(m−1)/2 · x − n² u^m) = 4j(j+n) c_j u^m`, `u = x/2`), the
  shifted-series identity `bessel_ode_series` (`x²S₂ + xS₁ − n²S₀ = −x²S₀` by
  `Summable.tsum_eq_zero_add` and `besselCoeff_succ`), `besselJNat_ode`, `besselJ_ode` (all
  `ν ∈ ℤ`, with `deriv`).  `besselJReal μ x` (real order, `rpow`, `besselJReal_intCast`) and
  `besselY ν x` as a `limUnder` of (4.49).  Not formalized: existence of the limit (4.49) and
  `Y_ν` solving (4.50) (needs `∂J_μ/∂μ`), complex arguments.  Design note: for an `AzFloat`
  Bessel routine the series (4.48) with `(x/2)^(2j+n)` and the exact rational coefficients
  `(−1)^j/(j!(n+j)!)` is directly usable at small `x` (alternating, so the first omitted term
  bounds the error once terms decrease); the recurrence/Miller's algorithm of the coming chunks
  will be the large-order route.  Lean notes: avoid `ring` across `(x/2)^n` and `2^(2j+n)` at
  once — it normalizes `(2^n)⁻¹` to `2⁻¹^n` and `4^j` separately from `2^(2j)` and cannot
  cancel them; keeping everything as powers of `x/2` (and `u`) removed all such goals, with
  `t^i (t^i)⁻¹ = 1` supplied to `linear_combination` where `t ≠ 0` matters;
  `Summable.sum_add_tsum_nat_add'` must be called with `(f := …)` (dot notation feeds the
  summability proof into the wrong slot and the HO unification times out);
  `summable_nat_add_iff` likewise needs `(f := …)`; `hasDerivAt_tsum_of_isPreconnected` takes
  the bound hypothesis as `∀ n y, y ∈ t → ‖g' n y‖ ≤ u n` and the derivative family as
  `∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y`; `isPreconnected_ball` lives in
  `Mathlib.Analysis.Normed.Module.Connected` (namespace `Metric`); `Int.negSucc_eq` +
  `← Nat.cast_succ` turns `Int.negSucc n` into `-↑(n+1)` (there is no `Int.negSucc_coe`);
  `omega` understands `Int.toNat`; `positivity` ignores conjunction hypotheses — destructure.
* **§4.7.1 Evaluation of Bessel functions (2026-10-16).**  States: the recurrence
  `J_{ν−1} + J_{ν+1} = (2ν/x) J_ν` (4.51); dividing by `J_ν` gives the continued fraction
  `J_ν/J_{ν−1} = 1/(2ν/x −) 1/(2(ν+1)/x −) …` (4.52) for the ratio only; Miller's algorithm: start
  at large `ν'` with `f_{ν'+1} = 0`, `f_{ν'} = 1`, run (4.53) (= (4.51)) backwards to `f_0 ≈ c J_0`,
  and fix `c` from `J_0 + 2∑_{ν≥1} J_{2ν} = 1` (4.54); why it works / why forward is unstable for
  `ν > x`: the recurrence has the two independent solutions `J_ν`, `Y_ν`, rounding gives
  `aJ_ν + bY_ν`, and `|Y_ν|` grows exponentially for `ν > ex/2` while `J_ν` is bounded; precisely
  `J_ν(x) ~ (ex/2ν)^ν/√(2πν)`, `Y_ν(x) ~ −√(2/πν) (2ν/ex)^ν` (4.55); Miller is best where the
  series (4.48) cancels catastrophically but asymptotics are not yet accurate (more in §4.12).
  Formalized in `Azurite/BrentZimmermann/Chapter4/BesselRecurrence.lean` (all proven): (4.51)
  from the series (`bessel_rec_term`: `c^n_{j+1} + c^{n+2}_j = (n+1) c^{n+1}_{j+1}` after the
  `(x/2)` shift; `besselJNat_recurrence` by `hasSum_nat_add_iff'`/`HasSum.unique`), extended to
  all `ν ∈ ℤ` by `besselJ_neg` (`besselJ_recurrence`, product form; `besselJ_recurrence'` for
  `x ≠ 0`); (4.52) as the one-step identity `besselJ_ratio_step` and the *exact* finite form
  `besselJ_ratio_eq_cf` (the `k`-fold fraction `besselRatioCF x ν k r` closed by the true tail
  `r = J_{ν+k}/J_{ν+k−1}`, needing `J_ν, …, J_{ν+k−1} ≠ 0`), plus the (4.52) coefficient sequences
  in the `contFrac` framework and `approximant_besselCF` (`f_k = besselRatioCF x ν k 0`, via the
  generic inner lemma `approximant_besselCF_inner` for all-`−1` partial numerators); (4.54) from
  the generating function at `t = ±1`: `hasSum_besselJ_int`, `hasSum_neg_one_zpow_besselJ`,
  `HasSum.nat_add_neg` + `Function.Injective.hasSum_iff` on `k ↦ 2k` (odd terms vanish) give
  `hasSum_two_mul_besselJ_even` and `besselJ_even_sum`; Miller's sequence `millerSeq x N`
  (well-founded on `N + 1 − ν`), `millerSeq_rec` (satisfies (4.53) for `1 ≤ μ ≤ N`), and the exact
  Casoratian identity `millerSeq_casoratian`: `f_ν J_{ν+1} − f_{ν+1} J_ν = J_{N+1}(x)` for `ν ≤ N`
  (downward induction; so `f_ν/J_ν − f_{ν+1}/J_{ν+1} = J_{N+1}/(J_ν J_{ν+1})`, `millerSeq_div_sub`
  — the computed sequence is proportional to `J` up to a defect of size `J_{N+1}(x)`, which is
  what Miller's algorithm relies on); the solution space of (4.53): `IsBesselRecSol`, `add`,
  `smul`, constant `casoratian`, `eq_of_init` (`Nat.twoStepInduction`), `exists_eq_comb` (every
  solution is `a g + b h` for two solutions with nonzero Casoratian — the "general solution"
  statement, instantiable with `g = J_ν` by `isBesselRecSol_besselJ`, and with `h = Y_ν` once `Y`
  is shown to solve (4.53)); the `J` half of (4.55) as inequalities: `abs_besselJNat_le`
  (`|J_n(x)| ≤ (|x|/2)^n/n! · e^(x²/4)`, from `(n+j)! ≥ n!`), `abs_besselJNat_le_stirling`
  (`≤ e^(x²/4)/√(2πn) · (e|x|/(2n))^n`, via `Stirling.le_factorial_stirling`), and
  `tendsto_besselJNat_atTop`.  Not formalized: convergence of (4.52) (not claimed by the text
  either), `Y_ν` solving (4.53) and its growth, the forward instability, the asymptotic
  equivalences themselves, §4.12.  Design note: an `AzFloat` Bessel routine for integer order
  would use the series for `|x|` small relative to `n`, and Miller's backward recurrence with
  the (4.54) normalization otherwise; the Casoratian identity gives a rigorous handle on the
  Miller defect once a lower bound on `|J_ν(x)|` is available, and `abs_besselJNat_le_stirling`
  tells how far to start (`N` with `(e|x|/(2N))^N` below the target).  Lean notes: `rw [h]` with
  `h : ∀ …` from `Summable.sum_add_tsum_nat_add'` — use `hasSum_nat_add_iff' 1` +
  `sum_range_one` + `HasSum.unique` instead of tsum rewriting; `div_sub_div` yields
  `(a d − b c)/(b d)` with `b * c` in that order; `field_simp` does not see a nonzero hypothesis
  whose terms it has reordered (`g 0 * h 1 − g 1 * h 0`) — clear denominators by hand with
  `div_mul_eq_mul_div`, `← add_div`, `eq_div_iff`; a `calc` whose first step is `|∑'…| = ‖∑'…‖`
  timed out at `whnf` where the same steps as separate `have`s compile instantly;
  `← Real.norm_eq_abs` rewrites the first `|·|` it finds (which may be `|x|`, not the sum);
  `FloorSemiring.tendsto_pow_div_factorial_atTop`; `squeeze_zero_norm`.
* **§4.7.2 Evaluation of Bernoulli and tangent numbers (2026-10-17).**  States: `B_{2k}` and
  `C_k = B_{2k}/(2k)!` (needed in (4.35), (4.38)) via the generating functions
  `∑ B_k x^k/k! = x/(e^x−1)` (4.56), `∑ C_k x^{2k} = x/(e^x−1) + x/2 = (x/2)/tanh(x/2)` (4.57);
  multiplying by `e^x − 1` gives `B_0 = 1`, `∑_{j≤k} C(k+1,j) B_j = 0` (`k > 0`) (4.58) and
  `∑_{j≤k} C_j/(2k+1−2j)! = 1/(2(2k)!)` (4.59); precision is not known in advance, so no table —
  compute at runtime; forward (4.58)/(4.59) is unstable (relative error `4^k 2^{−n}`, Ex. 4.35),
  tolerable if the `C_k` only feed an Euler–Maclaurin sum whose terms shrink by ≥ 4, or with
  exact rationals; otherwise guard digits or the stable recurrence from (4.57) × `sinh(x/2)/x`:
  `∑_{j≤k} C_j/((2k+1−2j)! 4^{k−j}) = 1/((2k)! 4^k)` (4.60), relative error `O(k² 2^{−n})`.
  Formalized in `Azurite/BrentZimmermann/Chapter4/BernoulliRecurrence.lean` (all proven, exact,
  in `ℚ` and `ℚ⟦X⟧`): `scaledBernoulli`; (4.56) is Mathlib's `bernoulliPowerSeries_mul_exp_sub_one`
  (Mathlib's `bernoulli` has `B_1 = −1/2`, matching the text); (4.57) as
  `scaledBernoulliPowerSeries = bernoulliPowerSeries ℚ + C (1/2) X` with even coefficients `C_k`
  and vanishing odd ones (`B_1 + 1/2 = 0`, `bernoulli_eq_zero_of_odd`), the identity
  `S (e^x − 1) = X + (1/2) X (e^x − 1)`, and the real closed form `div_exp_sub_one_add_half`
  (`tanh(x/2) = (e^x − 1)/(e^x + 1)`); (4.58) `bernoulli_recurrence` from `sum_bernoulli`;
  (4.59) `scaledBernoulli_rec` **for `k ≥ 1` only** — at `k = 0` the left side is `C_0 = 1`, not
  `1/2`, so the text's "for all k" needs `k ≥ 1` (like (4.58)); proof by extracting the
  `x^{2k+1}` coefficient (`coeff_mul` → `sum_antidiagonal_eq_sum_range_succ_mk` → even/odd
  split `sum_range_two_mul`, `coeff_scaledBernoulliPowerSeries_mul`); (4.60)
  `scaledBernoulli_rec_stable` for all `k`, from `scaledBernoulliPowerSeries_mul_sinh`
  (`S (E₊ − E₋) = (1/2) X (E₊ + E₋)` with `E± = rescale (±1/2) exp`, i.e. (4.57) × `2 sinh(x/2)`,
  derived by multiplying (4.57) with `e^{−x/2}` via `exp_mul_exp_eq_exp_add`) at the `x^{2k+1}`
  coefficient (`coeff m (E₊ − E₋) = ((1/2)^m − (−1/2)^m)/m!`); size: `scaledBernoulli_eq_zeta`
  and `abs_scaledBernoulli_le` (`|C_k| ≤ (π²/3)/(2π)^{2k}`), which is what makes (4.59) lose
  `≈ (2π)^{2k}` relative accuracy (the terms are `O(1)`, the result `O((2π)^{−2k})`) while in
  (4.60) the terms are themselves `O(4^{−k})`.  Not formalized: analytic convergence of
  (4.56)/(4.57) (radius `2π`, not in Mathlib), the rounding-error analysis (Ex. 4.35), tangent
  numbers (later chunks).  Design note: for `AzFloat` Euler–Maclaurin/Stirling coefficients the
  natural route is exact `AzRat` Bernoulli numbers via (4.60) (or (4.58)/(4.59) in exact
  arithmetic, where instability is irrelevant) — `C_k` sizes from `abs_scaledBernoulli_le` give
  the needed count; a floating `AzFloat` evaluation of (4.60) is the stable alternative.  Lean
  notes: `Algebra.id.map_eq_id` is gone — `algebraMap ℚ ℚ q = q` is `rfl`; `ring` does NOT
  identify `(4⁻¹)^n` (normal form `(1/4)^n`) with `(4^n)⁻¹` (normal form `4⁻¹^n`) nor `(1/2)^(2n)`
  with `4^n` — rewrite numerals to a common base (`div_pow`, `one_pow`, `Even.neg_one_pow`,
  `Odd.neg_one_pow`, `pow_mul`, `show (4:ℚ) = 2^2`) before `ring`; `rw [neg_div] at h` also
  rewrites `rescale (-1/2)` inside `h`, breaking later syntactic matches — use `div_pow` +
  `neg_one_pow` instead; `sum_eq_zero` in a `rw` list unifies with the first sum it meets — state
  the intended sum with `show … from`; identifiers cannot contain `₊`/`₋` subscripts; the
  antidiagonal/range conversion is `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`
  (`simp only` with `Nat.succ_eq_add_one`); `C (1/2) * 2 = 1` in `ℚ⟦X⟧` needs
  `map_ofNat C 2` + `map_mul` (ring treats `C (1/2)` as an atom).
* **§4.7.2, tangent numbers (2026-10-17).**  States: `tan x = ∑_{j≥1} T_j x^{2j−1}/(2j−1)!` (4.61),
  `T_j` positive integers, `T_j = (−1)^{j−1} 2^{2j}(2^{2j} − 1) B_{2j}/(2j)` (4.62) and the inverse
  `B_j = (−1)^{j/2−1} j T_{j/2}/(4^j − 2^j)` (even `j > 0`); odd primes in `den B_{2j}` divide
  `2^{2j} − 1` (von Staudt–Clausen: `p ∣ den B_{2j}` iff `(p−1) ∣ 2j`); with `t = tan x`,
  `Dt = 1 + t²`, `D(tⁿ) = n tⁿ⁻¹(1 + t²)`, `Dⁿ t = P_n(t)`, `deg P_n = n + 1`,
  `p_{n,j} = (j−1) p_{n−1,j−1} + (j+1) p_{n−1,j+1}` (4.63), `p_{n,j} = 0` for `n + j` even.
  Formalized in `Azurite/BrentZimmermann/Chapter4/TangentNumbers.lean` (all proven):
  `tanDerivPoly : ℕ → ℤ[X]` by `P_{n+1} = P_n'(1 + X²)`; (4.63) split as `p_{n+1,0} = p_{n,1}` and
  `p_{n+1,j+1} = j p_{n,j} + (j+2) p_{n,j+2}` (so the text's `(j−1) p_{n−1,j−1}` term is read as `0`
  at `j = 0`); nonnegativity, parity, `p_{n,j} = 0` for `j > n+1`, `p_{n,n+1} = n!`,
  `natDegree = n + 1`; the Leibniz identity `P_{n+1} = [n=0] + ∑_a C(n,a) P_a P_{n−a}` by induction
  with a standalone Pascal-reindexing lemma `pascal_sum`; the real statement
  `iteratedDeriv n tan x = P_n(tan x)` for `cos x ≠ 0` (induction with `Filter.EventuallyEq.deriv_eq`
  on the open set `cos ≠ 0`, `Polynomial.hasDerivAt` ∘ `Real.hasDerivAt_tan`,
  `Real.inv_one_add_tan_sq`), hence `Dⁿ tan 0 = p_{n,0}`; `tangentNumber j := p_{2j−1,0}` (`T_1 = 1`,
  `T_2 = 2`, `T_3 = 16` by unrolling the recurrence); (4.62) via formal power series over `ℚ`:
  `tanDerivSeries = ∑ p_{n,0} Xⁿ/n!` solves `y' = 1 + y²` (Leibniz identity at `t = 0`), the
  hyperbolic series `cosh = (e^x + e^{−x})/2`, `sinh`, `tanh = sinh · cosh⁻¹` (`PowerSeries.inv`,
  `constantCoeff cosh = 1`) satisfy `tanh' = 1 − tanh²` (`Derivation.leibniz`,
  `Derivation.leibniz_of_mul_eq_one` for the inverse), `X · tanh = S(4X) − S(2X)` from (4.57) rescaled
  by 2 and 4 (`exp_mul_exp_eq_exp_add`, `exp_pow_eq_rescale_exp`, cancelling `e^x − e^{−x} ≠ 0` in the
  domain `ℚ⟦X⟧`), so `coeff (2k+1) tanh = (16^{k+1} − 4^{k+1}) C_{k+1}` and even coefficients vanish;
  the sign twist `tanSeries` (`(−1)^k` at `X^{2k+1}`, i.e. `tan x = −i tanh(ix)` made rational)
  satisfies `y' = 1 + y²` (products of two odd coefficients pick up `−(−1)^k`), the formal ODE with
  `y(0) = 0` has a unique solution (strong induction on coefficients), hence
  `tanDerivSeries = tanSeries` and `T_{k+1} = (−1)^k 4^{k+1}(4^{k+1} − 1) B_{2k+2}/(2k+2)`
  (`tangentNumber_eq_bernoulli`), the inverse `bernoulli_two_mul_eq_tangentNumber`,
  `tangentNumber_pos` (via `sign_bernoulli_two_mul`), `bernoulli_den_dvd`
  (`den B_{2k+2} ∣ 4^{k+1}(4^{k+1} − 1)` by `Rat.den_dvd`) and `odd_prime_dvd_den_bernoulli`.  Not
  formalized: the analytic (4.61) (no Taylor series of `tan` in Mathlib; the Taylor coefficients
  are identified by `iteratedDeriv_tan_zero` instead); von Staudt–Clausen is Mathlib's
  `Bernoulli.vonStaudt_clausen`/`Bernoulli.dvd_den_bernoulli` (not restated).  Design note: this
  is the proven bridge for an exact integer algorithm for `T_j` (the recurrence (4.63) on a row of
  `p_{n,·}`, presumably Algorithm TangentNumbers in the next chunk) and hence for exact `B_{2j}`
  via the inverse formula — an `AzNat`-based implementation can be verified against
  `tangentNumber` directly.  Lean notes: never `open Polynomial` and `open PowerSeries` together
  (`C`, `X`, `coeff_C`, `coeff_derivative`, `derivative_C` all clash) — use two sections;
  `/.` (`Rat.divInt`) is scoped notation, write `Rat.divInt`; `Derivation.leibniz_of_mul_eq_one`
  takes the derivation explicitly (`d⁄dX`); `exp_mul_exp_neg_eq_one` has `A` implicit
  (`(A := ℚ)`); `evalNegHom (exp ℚ)` is defeq to `rescale (−1) (exp ℚ)`; `rescale_mul` is
  `rescale (a*b) = (rescale b).comp (rescale a)` — use `← RingHom.comp_apply, ← rescale_mul` to
  merge nested rescales; `ring` cannot simplify `((−1)^k)^2` — supply `hsq : ((−1)^k)^2 = 1` to
  `linear_combination`; identifiers may not contain `₊`/`₋` (but `S₂`, `S₄` are fine); for
  `tangentNumber_three` the `show (4:ℕ) = 3 + 1 by rfl` rewrites every `4`, so finish with
  `simp [tanDerivPoly_zero, coeff_X]`; `Polynomial.finset_sum_coeff` → `finsetSum_coeff`.
* **§4.7.2, Algorithm 4.3 TangentNumbers and growth (2026-10-17).**  States: using (4.63) but
  skipping the vanishing coefficients gives the in-place Algorithm 4.3 (`T_1 ← 1`;
  `T_k ← (k−1)T_{k−1}`; then for `k = 2..m`, for `j = k..m`: `T_j ← (j−k)T_{j−1} + (j−k+2)T_j`),
  non-negative integers only (overflow risk in single precision; stable in floating point, no
  cancellation); SecantNumbers is Ex. 4.40; `T_k` grows like `(2k−1)!(2/π)^{2k}` (poles of `tan` at
  `±π/2`): `T_k/(2k−1)! = 2^{2k+1}(1 − 2^{−2k})ζ(2k)/π^{2k}` (4.64) with the odd zeta function
  `(1 − 2^{−s})ζ(s) = 1 + 3^{−s} + 5^{−s} + …`; Bernoulli numbers grow more slowly (singularities at
  `±2πi`): `(−1)^{k−1}B_{2k}/(2k)! = 2ζ(2k)/(2π)^{2k}` (4.65), `ζ(2k) = 1 + O(4^{−k})`, so
  `|B_{2k}| ∼ 2(2k)!/(2π)^{2k}` (4.66); (4.64) ⟺ (4.65) via (4.62); fast Bernoulli computation is
  Ex. 4.41, low-space in §4.10.  Formalized in `Azurite/BrentZimmermann/Chapter4/TangentAlgorithm.lean`
  (all proven): the algorithm as a **model over `ℕ`** (not the `AzNat` implementation — per the
  standing "theorems, no algorithms yet" instruction): `tangentInit j = (j−1)!`, `tangentStep`
  (`Function.update`), `tangentPass k a s` (`s` inner steps), `tangentOuter m a r` (`r` passes),
  `tangentNumbersModel m = tangentOuter m tangentInit (m−1)`; loop invariant `tangentPass_spec`:
  before pass `k` the entry `j ≥ k` holds `p_{j+k−3, j−k+2}` and entries `j < k` hold the finished
  `T_j`; after `s` steps the entries `k ≤ j < k+s` hold `p_{j+k−2, j−k+1}` (one application of
  (4.63) per update, with the `j = k` step reading `(j−k) = 0` so the stale neighbour is harmless);
  `tangentOuter_spec`; `tangentNumbersModel_eq : tangentNumbersModel m j = T_j` for `1 ≤ j ≤ m`;
  `tangentNumbersModel_three` (1, 2, 16, derived); `oddZeta` and
  `one_sub_two_rpow_neg_mul_zetaReal` (`HasSum.even_add_odd` on `n^{−s}`, the even half is
  `2^{−s}ζ(s)` by `Real.mul_rpow`); (4.64) `tangentNumber_div_factorial_eq_zeta` (indexed as
  `T_{k+1}`), from (4.62) and `bernoulli_two_mul_eq_zeta` (the sign `(−1)^k·(−1)^k` handled by
  `hsq : ((−1)^k)^2 = 1` fed to `linear_combination` before clearing denominators) and
  `_eq_oddZeta`; (4.65) `neg_one_pow_mul_bernoulli_div_factorial`; `ζ(2k) − 1 ≤ 8/4^k`
  (`zetaReal_two_mul_sub_one_le`, via `n^{−2k} ≤ 4^{1−k} n^{−2}` for `n ≥ 2` and
  `∑_{n≥2} n^{−2} ≤ ζ(2) ≤ 2`), `tendsto_zetaReal_two_mul`, (4.66) `abs_bernoulli_isEquivalent`
  (`Asymptotics.isEquivalent_of_tendsto_one`, ratio `= ζ(2k)`), `tangentNumber_isEquivalent`
  (`T_k ∼ 2(2k−1)!(2/π)^{2k}`, ratio `(1 − 4^{−k})ζ(2k)`).  Not formalized: floating-point
  stability/overflow remarks, Exercises 4.40/4.41, §4.10.  Design note: the `AzNat`
  implementation of Algorithm 4.3 should be verified against `tangentNumbersModel` (a pure
  function on `ℕ → ℕ`) and hence `tangentNumber`; `tangentNumber_isEquivalent` with
  `(2k−1)!(2/π)^{2k}` sizes the integers (about `2k log₂(2k/πe)` bits for `T_k`); Bernoulli numbers
  then follow exactly from `bernoulli_two_mul_eq_tangentNumber`.  Lean notes: `HasSum.even_add_odd`,
  `summable_nat_add_iff`, `Summable.sum_add_tsum_nat_add'` all need `(f := …)` whenever `f` would
  be inferred by higher-order unification from a lambda (otherwise `whnf` timeouts); likewise
  `Summable.comp_injective (i := …)`; `local notation` cannot abbreviate a lambda with projections
  (`quotPrecheck` error) — write `(tanDerivPoly n).coeff i` out; keep `zetaReal (2 * k)` arguments
  in one cast form (`2 * ((k+1 : ℕ) : ℝ)` from Mathlib lemmas versus `2 * (↑k + 1)` from a statement)
  and `push_cast` before `field_simp`/`ring`; `decide` on the `Function.update`-based model times
  out at `whnf` — derive concrete values from the correctness theorem instead.
* **§4.8 Arithmetic-geometric mean, introduction (2026-10-17).**  States: the AGM iteration of
  Gauss/Legendre `(a_{j+1}, b_{j+1}) = ((a_j+b_j)/2, √(a_j b_j))` gives the theoretically fastest
  methods at very large precision, `O(M(n) log n)` with a large constant; for real positive starts
  it converges quadratically to `AGM(a_0, b_0)`; useful because (1) quadratic convergence ⇒
  `O(log n)` iterations, (2) each iteration `O(M(n))` (Newton square root, §3.5/§4.2.3), (3)
  suitable starts give `log` directly, other elementary functions less directly, and `π`, `ln 2`.
  Formalized in `Azurite/BrentZimmermann/Chapter4/AGM.lean` (all proven, real positive starts):
  `agmSeq` by recursion with `agmA`/`agmB`; `agm_pos`; AM–GM `b_{j+1} ≤ a_{j+1}`
  (`Real.sqrt_le_iff` + `nlinarith`), `a` antitone / `b` monotone from index 1; the gap identity
  `a_{j+1} − b_{j+1} = (√a_j − √b_j)²/2`; `≤ (a_j − b_j)/2` and `≤ (a_j − b_j)²/(8 b_j)`
  (the latter by `(s−t)²·((s+t)² − 4t²) ≥ 0`), hence `a_{j+1} − b_{j+1} ≤ (a_1 − b_1)/2^j` and, via the
  generic `quadratic_decay` (`e_{j+1} ≤ C e_j² ⇒ C e_j ≤ (C e_0)^{2^j}`), the quadratic bound
  `a_{j+1} − b_{j+1} ≤ 8 b_1 ((a_1 − b_1)/(8 b_1))^{2^j}`; the limit `AGM a b := ⨅ j, a_{j+1}` with
  `tendsto_atTop_ciInf`, the gap → 0 by squeezing, so `b_j → AGM` too; `b_j ≤ AGM ≤ a_j` (`j ≥ 1`),
  `min a b ≤ AGM ≤ max a b`, `AGM_comm`, `AGM_self`, `AGM_step` (`AGM(a,b) = AGM((a+b)/2, √(ab))`, by
  uniqueness of limits), `AGM_smul` (`AGM(ca, cb) = c·AGM(a,b)`); iteration count: once
  `a_1 ≤ 5 b_1` (i.e. `(a_1 − b_1)/(8 b_1) ≤ 1/2`), `n ≤ 2^j ⇒ a_{j+1} − b_{j+1} ≤ 8 b_1/2^n`, so
  `Nat.clog 2 n + 1` iterations give `n` bits (`agm_iterations`) — the `O(log n)` claim; the
  linear phase before that costs `O(log(a/b))` halvings (`agm_gap_le_half_pow`).  Not formalized:
  the cost model, complex starts (§4.8.5/§4.12), the applications (coming subsections).  Design
  note: an `AzFloat` AGM would iterate `(add, sqrt)` at precision `p + guard` and stop via the
  `a_j − b_j` gap, which the Ziv-style API can certify directly from the bracket
  `b_j ≤ AGM ≤ a_j`; the rounding-error propagation of the iteration (each step is a contraction
  for the gap but perturbs the common limit) is not yet analysed — the text presumably returns to
  it.  Lean notes: `le_or_lt` is gone — use `le_or_gt`; `pow_le_pow_of_le_one` needs `(a := …)` when
  the base is a numeral under `by norm_num`, and `gcongr` on `c * r^(2^j) ≤ c * r^n` wrongly tries
  the exponent-monotone lemma (asks `1 ≤ r`) — apply `mul_le_mul_of_nonneg_left` by hand;
  `simp only at h` fails with "no progress" when the lambda is already beta-reduced; convert
  `C * e_j ≤ R` to `e_j ≤ (1/C)·R` through an explicit `calc` with `field_simp` rather than
  `div_le_iff₀'` rewrites.
* **§4.8.1 Elliptic integrals (2026-10-17).**  States: `K(k) = ∫_0^{π/2} dθ/√(1 − k² sin²θ) =
  ∫_0^1 dt/√((1−t²)(1−k²t²))` (4.67), `E(k) = ∫_0^{π/2} √(1 − k² sin²θ) dθ`, modulus `k ∈ [0,1]`,
  complementary `k' = √(1−k²)`, `K'(k) := K(k')`; Gauss: `1/AGM(1,k) = (2/π) K'(k)` (4.68) — computes
  `K` fast and leads to logarithms; `K(k) = (π/2) ₂F₁(1/2,1/2;1;k²)`, `K(k) = (π/2)(1 + k²/4 + O(k⁴))`
  (4.69), `K'(k) = (2/π) ln(4/k) K(k) − k²/4 + O(k⁴)` (4.70).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/EllipticIntegrals.lean` (all proven): `ellipticK`/`ellipticE` as
  interval integrals (θ-form), `K(0) = E(0) = π/2`, `E ≤ π/2 ≤ K` (`k² < 1`), (4.69) as
  `(π/2)(1 + k²/4) ≤ K(k) ≤ (π/2)(1 + k²/4 + 3k⁴/8)` for `k² ≤ 1/2` (from
  `1 + x/2 ≤ (1−x)^{−1/2} ≤ 1 + x/2 + x²` on `[0, 1/2]` and `∫_0^{π/2} sin² = π/4`, `∫ sin⁴ = 3π/16`);
  **Gauss's theorem (4.68) PROVEN**: `J(a,b) := ∫_0^∞ dt/√((t²+a²)(t²+b²))`; `J(c,c) = π/(2c)`
  (`integral_comp_mul_left_Ioi` + `integral_Ioi_inv_one_add_sq`); kernel bounded by
  `(t² + min(a,b)²)⁻¹` ⇒ integrable on `ℝ` (comparison with `(1+t²)⁻¹`); `J` antitone in each
  argument (`setIntegral_mono_on`); the Landen map `u = (t − ab/t)/2` is injective on `(0,∞)` with
  image `ℝ` (`t = u + √(u² + ab)`), and the one-dimensional change of variables
  `integral_image_eq_integral_abs_deriv_smul` with the pointwise identity
  `|u'| · kernel(a₁,b₁)(u) = 2 kernel(a,b)(t)` (`(a₁² + u²)(b₁² + u²) = (t²+a²)(t²+b²)((t²+ab)/(4t²))²`)
  plus evenness (`integral_Iic_add_Ioi`, `integral_comp_neg_Iic`) gives `J((a+b)/2, √(ab)) = J(a,b)`;
  iterating along the AGM and squeezing `π/(2a_j) ≤ J(a,b) ≤ π/(2b_j)` gives `J(a,b) = π/(2 AGM(a,b))`
  (no continuity of `J` needed); `t = tan θ` on `(0, π/2)` (image `(0,∞)`, `Real.strictMonoOn_tan`,
  `Real.hasDerivAt_tan`) turns `J(1,k)` into `∫_0^{π/2} dθ/√(sin²θ + k² cos²θ)`, then `θ ↦ π/2 − θ`
  (`integral_comp_sub_left`) into `∫ dθ/√(cos²θ + k² sin²θ) = K(k')`; hence `one_div_AGM_one` and the
  general `∫_0^{π/2} dθ/√(a²cos²θ + b²sin²θ) = π/(2 AGM(a,b))` by homogeneity (`AGM_smul`).  Not
  formalized: the `t`-forms of (4.67) (improper at `t = 1`), the hypergeometric identification, and
  (4.70) (asymptotics of `K` near `k = 1`; the text says "it can be shown").  Design note: (4.68) is
  the rigorous basis for an `AzFloat` `ellipticK` via the AGM bracket, and together with (4.70) (still
  to be proven) for `ln`; the bracket `b_j ≤ AGM ≤ a_j` certifies the error directly.  Lean notes:
  `open Set MeasureTheory intervalIntegral` together makes `integral_const_mul` ambiguous — qualify;
  `rw [← h]` with `h : ∫_0^{π/2} 1 = π/2` rewrites the integration limit `π/2` too — use `calc`;
  `Continuous.intervalIntegrable` leaves the measure undetermined inside `integral_mono_on` (stuck
  `IsLocallyFiniteMeasure ?μ`) — state the `IntervalIntegrable … volume …` facts first; `positivity`
  cannot see `0 < min a b` for `min a b ^ 2` — use `pow_pos`; `(by positivity)` inside
  `Real.sqrt_pos.mpr` within a `rw` term runs on a metavariable goal — ascribe the type;
  `setIntegral_congr_fun` with an unspecified target function lets `rw` close the pointwise goal by
  unifying the target with the source (silently useless) — state the target integral explicitly;
  `integral_comp_sub_left` is best used forward as a `have` with `(a := 0) (b := π/2)` then
  `rw [sub_self, sub_zero]`; `Real.cos_pos_of_mem_Ioo` needs `-(π/2) < θ` (feed `Real.pi_pos`);
  `Real.pi_div_two_pos`; the Jacobian theorem lives in `Mathlib.MeasureTheory.Function.JacobianOneDim`.
* **§4.8.2 First AGM algorithm for the logarithm (2026-10-17).**  States: from (4.68)–(4.70),
  `(π/2)/AGM(1,k) = ln(4/k)(1 + O(k²))` (4.71), so `ln x = (π/2)/AGM(1, 4/x)(1 + O(1/x²))` for large
  `x`; `x ≥ 2^{n/2}` gives precision `n` in about `2 lg n` iterations for `x ∈ [2^{n/2}, 2^n]`; `π`
  needed (Ex. 4.44 via two evaluations, or Brent–Salamin from the Legendre relation
  `EK' + E'K − KK' = π/2` (4.72)); argument expansion `ln(2^ℓ x) = ℓ ln 2 + ln x` (needs `ln 2`) or
  `ln(x^{2^ℓ}) = 2^ℓ ln x` (gives `ln 2` from `π`); rigorous error `|(π/2)/AGM(1,k) − ln(4/k)| ≤
  4k²(8 − ln k)` on `(0,1]` (4.73), `0.37k²(2.4 − ln k)` on `(0, 0.5]`; the `O(k²|ln k|)` error blocks
  using larger `k`, motivating the exact theta-function formula (next).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/AGMLog.lean` (all proven): `agmLog x := (π/2)/AGM(1, 4/x)`, exactly
  `= K(√(1 − (4/x)²))` for `x ≥ 4` and `= ∫_0^{π/2} dθ/√(cos²θ + (4/x)² sin²θ)` for `x > 0` (from
  §4.8.1); `log_two_pow_mul`, `log_pow_two_pow`; error transport: shifting by `2^ℓ` keeps the absolute
  error, squaring `ℓ` times divides it by `2^ℓ` (`abs_agmLog_pow_sub`); iteration count:
  `√(b_j/a_j) ≤ b_{j+1}/a_{j+1}` (so `b_j/a_j ≥ (b/a)^{1/2^j}`, `agm_ratio_rpow_le`, rpow), the shifted
  sequence `agmSeq_shift`, `agm_ratio_one_half_le` (`n ≤ 2^m`, `k ≥ 2^{−n}` ⇒ `b_{m+1}/a_{m+1} ≥ 1/2`),
  and `agm_log_iterations`: for `2^{−n} ≤ k ≤ 1`, `a_j − b_j ≤ 8/2^n` at `j = 2⌈lg n⌉ + 1` (linear
  phase `⌈lg n⌉ + 1` steps until the ratio is ≥ 1/2, then the quadratic phase of §4.8) — the text's
  "about `2 lg n`".  **Not formalized at the time: (4.71) and (4.73)** (both proven later, see the §4.8.2 continued
  bullet below) — they need the behaviour of `K(k')` as
  `k → 0`, i.e. (4.70); a direct elementary proof (split `J(1,k) = ∫_0^∞ dt/√((1+t²)(k²+t²))` at
  `t = 1`, `asinh(1/k) = ln(2/k) + O(k²)`, and the `O(k² ln(1/k))` piece `∫_0^1 (1 − (1+t²)^{−1/2})
  (1/t − (k²+t²)^{−1/2}) dt`) is feasible but long; the planned route is the exact theta formula of
  the coming subsections, from which a clean bound should follow; also not formalized: (4.72),
  Brent–Salamin, Ex. 4.44.  Design note: an `AzFloat` `log` via AGM would use `agmLog` with
  `x ← 2^ℓ x ≥ 2^{p/2}` (needs `ln 2` and `π` as proven constants) or repeated squaring (error
  shrinks by `2^ℓ`, no `ln 2` needed), with the AGM bracket certifying the AGM value and a proven
  (4.73)-type bound certifying the truncation — the latter is the missing piece.  Lean notes:
  `(1/2 : ℝ) ^ (m + 1 : ℕ)` inside an rpow context still elaborates the exponent with a cast
  (`↑(m+1)`, rpow) — bind the natural power to a `set e := …` variable first; `agmSeq A B 0 = agmSeq
  a b m` for `A = a_m, B = b_m` needs `Prod.ext rfl rfl` (eta), not `rfl`; use
  `congrArg Prod.fst (agmSeq_shift …)` for the component shifts instead of `simp only [agmA, …]`
  (which unfolds the wrong occurrences); `mul_one_div` + `div_le_one` for `n * (1/2^m) ≤ 1`.
* **§4.8.3 Theta functions (2026-10-17).**  States: `θ₂(q) = ∑_ℤ q^{(n+1/2)²} = 2q^{1/4}∑ q^{n(n+1)}`
  (4.74), `θ₃(q) = ∑_ℤ q^{n²} = 1 + 2∑_{n≥1} q^{n²}` (4.75), `θ₄(q) = θ₃(−q)` (4.76), sparse series
  (rectangular splitting does not help; AGM-based theta evaluation would be circular); identities
  `(θ₃² + θ₄²)/2 = θ₃²(q²)`, `θ₃θ₄ = θ₄²(q²)`, so `AGM(θ₃²(q), θ₄²(q)) = AGM(θ₃²(q^{2^k}), θ₄²(q^{2^k})) = 1`
  (limit 1 since `q^{2^k} → 0`): the AGM is parameterized by `(θ₃²(q^{2^k}), θ₄²(q^{2^k}))`; scaling:
  `AGM(1, k') = 1/θ₃²(q)` for `k' = θ₄²/θ₃²`, equivalently `k = θ₂²/θ₃²` by Jacobi `θ₂⁴ + θ₄⁴ = θ₃⁴`, and
  with (4.68) `K(k) = (π/2)θ₃²(q)` (4.77), `q` the nome; inverse `q = exp(−πK'/K)`, `ln(1/q) = πK'(k)/K(k)`
  (4.78); Sasaki–Kanada `ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))` (4.79).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ThetaFunctions.lean` (all proven): `theta3`/`theta4` as `ℤ`-sums
  with `m.natAbs` exponents (keeps everything in `Monoid.npow`), `theta2` one-sided with `rpow q^{1/4}`;
  summability via `|q|^{m²} ≤ |q|^{|m|}` and `Summable.int_rec`; one-sided forms by `tsum_int_rec` +
  `tsum_eq_zero_add`; `θ₄(q) = θ₃(−q)`; `theta2_eq_tsum_int` (`0 < q < 1`); **both AGM identities
  PROVEN**: the double series over `ℤ²` (`tsum_mul_tsum_of_summable_norm`) is split by the parity of
  `m + n` (`Summable.tsum_add_tsum_compl` + explicit `Equiv`s `(a,b) ↦ (a+b, a−b)` onto the even pairs
  and `(a,b) ↦ (a+b+1, a−b)` onto the odd pairs, proofs by `omega` on `Int` division), the odd part
  vanishes pointwise (for `θ₃² + θ₄²`) or by the involution `(a,b) ↦ (a, −b−1)` (for `θ₃θ₄`), the even
  part is reassembled with `(a+b)² + (a−b)² = 2(a² + b²)` (`zify` + `sq_abs`) and the parity rule
  `(−1)^{|m|}(−1)^{|n|} = ±1` by `Even (m+n)`; bounds for `0 ≤ q < 1`: `1 ≤ θ₃ ≤ 1 + 2q/(1−q)`,
  `1 − 2q/(1−q) ≤ θ₄ ≤ θ₃`, `θ₄ ≥ 0` (from `θ₃θ₄ = θ₄(q²)² ≥ 0`) and `θ₄ > 0` (descent along `q^{2^k}`
  to a `q^{2^k} < 1/3` where the series bound is positive); `AGM_theta_step` via `AGM_step`,
  `AGM_theta_pow`, and `AGM_theta : AGM(θ₃²(q), θ₄²(q)) = 1` by squeezing between
  `(1 − 2r/(1−r))²` and `(1 + 2r/(1−r))²`, `r = q^{2^k} → 0`; `AGM_one_nomeK'` (`AGM_smul`) and (4.77)
  as `ellipticK_nome : K(√(1 − k'²)) = (π/2)θ₃²(q)` from Gauss (4.68) — no Jacobi quartic identity
  needed in this form.  **Not formalized: Jacobi's `θ₂⁴ + θ₄⁴ = θ₃⁴`** (so `nomeK = θ₂²/θ₃²` is a
  definition only and `k = √(1 − k'²)` is the modulus actually used), **the inverse nome formula
  (4.78)** and hence **Sasaki–Kanada (4.79)** — (4.78) is the Jacobi imaginary transformation
  (Mathlib: `jacobiTheta_S_smul : jacobiTheta (−1/τ) = (−Iτ)^{1/2} jacobiTheta τ` for `θ₃`, and
  `jacobiTheta₂_functional_equation` for the two-variable theta giving `θ₂ ↔ θ₄`); a real-`q`
  bridge `theta3 (exp (−πs)) = jacobiTheta (I s)` plus the `θ₂/θ₄` swap would give (4.78) and then
  (4.79) via (4.68)+(4.77)+Jacobi — the planned route to the exact log formula and to a clean (4.73).
  Design note: `θ₃`, `θ₄`, `θ₂` at a small nome are a handful of terms (`q^{n²}`) — an `AzFloat`
  implementation is a sparse-series loop with the tail bound `2q^{(N+1)²}/(1−q)`; the AGM then runs
  on `(θ₃², θ₄²)` exactly as in §4.8.  Lean notes: `Int.rec f g` is the canonical two-sided sequence
  (`tsum_int_rec`, `Summable.int_rec`, `HasSum.int_rec`), match it with `funext; rcases m with n | n <;>
  rfl`; `Summable.tsum_add_tsum_compl` is `protected` with explicit `(hs) (hsc)` and implicit `f` —
  never via dot notation on `hf`; `Equiv.tsum_eq` reversed pulls a subtype sum back to `ℤ × ℤ`;
  `rw [neg_pow]` grabs `(-1)^k` first — pass the base `neg_pow q`; `Even.pow` is not available by dot
  notation on an unfolded `Even` (use `Nat.even_pow.mpr ⟨h, two_ne_zero⟩` / `Odd.pow h`); rewriting an
  `if Even …` condition with `rw` fails (motive/Decidable) — `by_cases` + `ite_eq_left/right`;
  `zify` turns `(x.natAbs : ℤ)` into `|x|`, so finish with `sq_abs`, not `Int.natAbs_sq`; `omega`
  does not take `∧` goals from `Prod.mk.injEq` — use `Prod.ext rfl (by show …; omega)`;
  `(f / g)` (Pi) is defeq to `fun x => f x / g x`, so `exact` works where `simpa` does not.
* **§4.8.3 continued: Jacobi's identity, nome inverse (4.78), Sasaki–Kanada (4.79) (2026-10-17).**
  States: `θ₂⁴ + θ₄⁴ = θ₃⁴` (Jacobi), so `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²` are complementary moduli and
  `K(k) = (π/2)θ₃²(q)` (4.77); the nome inverse `ln(1/q) = πK'(k)/K(k)` (4.78); Sasaki–Kanada
  `ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))` (4.79).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ThetaModular.lean` (all proven): `theta2Int q = ∑_ℤ q^{a(a+1)}`
  with `θ₂ = q^{1/4}·theta2Int` (`theta2_eq_rpow_mul`, summability via `|a||a+1| ≥ |a| − 1`); two more
  `ℤ²` parity splits `θ₃² − θ₄² = 2q θ₂Int(q²)²` (`theta3_sq_sub_theta4_sq`, odd pairs via
  `(a+b+1, a−b)`) and `θ₂Int(q)² = 2θ₃(q²)θ₂Int(q²)` (`theta2Int_sq`, even pairs via `(c+d, c−d)`,
  odd via `(c+d+1, c−d)`); with `(θ₃² + θ₄²)/2 = θ₃²(q²)` these give **Jacobi's identity**
  `theta2_pow_four_add_theta4_pow_four` for `0 ≤ q < 1` by `linear_combination`, hence
  `nomeK_sq_add_nomeK'_sq`, `theta2_le_theta3`, `sqrt_one_sub_nomeK'_sq = nomeK`, and (4.77) as
  `ellipticK_nomeK : K(k) = (π/2)θ₃²`.  Bridge to Mathlib: for `q = nome s = exp(−πs)`, `τ = is`,
  `(θ₃ q : ℂ) = jacobiTheta₂ 0 τ`, `θ₄ q = jacobiTheta₂ (1/2) τ`, `θ₂ q = e^{−πs/4} jacobiTheta₂ (τ/2) τ`
  (`theta3_nome_eq`, `theta4_nome_eq`, `theta2_nome_eq`); `jacobiTheta₂_functional_equation` at
  `z = 0` and `z = 1/2` (plus evenness in `z`, `jacobiTheta₂_neg_left'`, and `(-1/τ) = i/s`) yields
  Jacobi's imaginary transformation `θ₃(q') = √s θ₃(q)`, `θ₂(q') = √s θ₄(q)`, `θ₄(q') = √s θ₂(q)` for
  `q' = exp(−π/s)` (`theta3_nome_inv`, `theta2_nome_inv`, `theta4_nome_inv`), so `k'(q) = k(q')`
  (`nomeK'_nome_eq_nomeK_inv`).  Then **(4.78)** `log_inv_nome`: `π K(k'(q))/K(k(q)) = ln(1/q)` by
  (4.77) at `q` and `q'`, and **(4.79)** `sasaki_kanada` via `AGM_smul`, `one_div_AGM_one` (Gauss),
  `sqrt_one_sub_nomeK_sq = nomeK'`, and (4.78).  Not formalized: nothing in this chunk; the (4.73)
  error bound of §4.8.2 is now derivable from (4.79) (still open), as is the Legendre relation (4.72).
  Design note: (4.79) is the exact formula an `AzFloat` log via theta functions would be certified
  against: evaluate `θ₂²(q), θ₃²(q)` by sparse series, run the AGM, divide `π` — no asymptotic
  `ln(4/k)` error term is needed.  Lean notes: no `jacobiTheta₂_neg_left` in Mathlib — evenness in
  `z` is `(Equiv.neg ℤ).tsum_eq` + `ring_nf` on the term; `Complex.exp_mul` does not exist — push the
  real `rpow` to `Real.exp (… * …)` with `← Real.exp_mul` *before* casting (`Complex.ofReal_exp`);
  `((s:ℂ))^(1/2:ℂ) = √s` is `Complex.ofReal_cpow` + `Real.sqrt_eq_rpow`; small complex identities such
  as `-1/(i s) = i/s` go through `div_eq_iff` + `linear_combination … * Complex.I_sq` rather than
  `field_simp; ring` (which loops on `I`); `Equiv.tsum_eq` reversed needs the summand given
  explicitly `(f := …)` or `rw` fails to find the pattern; after `field_simp` closes a goal, a trailing
  `ring` is an error ("No goals") — check the goal state rather than appending finishers.
* **§4.8.2 continued: the error bound (4.73) and (4.71) (2026-10-17).**  States:
  `|(π/2)/AGM(1,k) − ln(4/k)| ≤ 4k²(8 − ln k)` for `k ∈ (0,1]` (4.73); `(π/2)/AGM(1,k) =
  ln(4/k)(1 + O(k²))` (4.71).  Formalized in `Azurite/BrentZimmermann/Chapter4/AGMLogBound.lean`
  (all proven), by an elementary argument instead of the theta route: Gauss (4.68) gives
  `(π/2)/AGM(1,k) = ∫_0^∞ dt/√((1+t²)(k²+t²))`, split at `t = 1`.  On `[1,∞)` the integrand is
  `1/(t√(1+t²)) − r₁` with `0 ≤ r₁ ≤ k²/(2t³)` (`inv_sub_inv_sqrt_le`), and
  `∫_1^∞ dt/(t√(1+t²)) = arsinh 1 = ln(1+√2)` (`integral_inv_mul_sqrt_Ioi`, antiderivative
  `−arsinh(1/t)` via `integral_Ioi_of_hasDerivAt_of_nonneg'`); on `[0,1]` it is
  `1/√(k²+t²) − φ + r₂` with `φ = t/(√(1+t²)(1+√(1+t²))) = (1 − 1/√(1+t²))/t` (`agmLogPhi`,
  antiderivative `ln(1+√(1+t²))`), `∫_0^1 dt/√(k²+t²) = arsinh(1/k)` (antiderivative
  `arsinh(t/k)`), and `r₂ = (1 − 1/√(1+t²))(1/t − 1/√(k²+t²))` (`agmLogRem`, defined as the
  difference so integrability is free) with `0 ≤ r₂ ≤ t/2` on `[0,k]`, `≤ k²/(4t)` on `[k,1]`, so
  `0 ≤ R₂ ≤ (k²/4)(1 − ln k)`.  Summing, `(π/2)/AGM(1,k) = ln(4/k) + R₀ − R₁ + R₂` with
  `R₀ = ln((1+√(1+k²))/2) ∈ [0, k²/4]`, giving `abs_pi_div_AGM_sub_log_le`:
  `|(π/2)/AGM(1,k) − ln(4/k)| ≤ (k²/4)(2 − ln k)` — sixteen times sharper than (4.73), whose
  textbook form is `abs_pi_div_AGM_sub_log_le_bz`; `abs_agmLog_sub_log_le`:
  `|agmLog x − ln x| ≤ (4/x²)(2 + ln(x/4))` for `x ≥ 4`; and (4.71) explicitly as
  `pi_div_AGM_eq_log_mul`: `(π/2)/AGM(1,k) = ln(4/k)(1 + ε)`, `|ε| ≤ k²/2` (uses `exp 1 < 3` for
  `ln 4 ≥ 1`).  Not formalized: the sharper `0.37k²(2.4 − ln k)` on `(0, 0.5]` (our bound gives
  `0.25k²(2 − ln k)` there, which is better anyway); (4.70) as an asymptotic statement about `K`;
  the Legendre relation (4.72); Brent–Salamin; Ex. 4.44.  Design note: this is the certified error
  term for an `AzFloat` AGM logarithm: with `x ≥ 2^{p/2+2}` the bound `(4/x²)(2 + ln(x/4))` is
  below `2^{−p}`, so the shift `ℓ` in `agmLog (2^ℓ x)` can be chosen from `p` alone (plus the AGM
  iteration bound `agm_log_iterations`).  Lean notes: `integral_Ioi_of_hasDerivAt_of_nonneg'`
  needs `(a := …)` when the `have` has no expected type, else `linarith` on `mem_Ici.mp hx` sees
  metavariables; `rw [Real.sqrt_mul (by positivity) _]` fails on the metavariable — ascribe
  `(by positivity : (0:ℝ) ≤ …)`; `Continuous.inv₀` with a `fun t => …` goal: give the `0 < …` fact
  via `show` first, `positivity` cannot see through the unreduced beta-redex; `continuous_id.pow 2`
  yields `fun x => id x ^ 2`; `Integrable.const_mul` (not dot notation on `IntegrableOn`) for
  `k²/2 · t^{−3}` on `Ioi 1`, with `Real.rpow_neg` + `Real.rpow_natCast` after `show (3:ℝ) = ((3:ℕ):ℝ)`;
  `field_simp` often closes the goal outright — a trailing `ring` then errors; `show … by field_simp`
  may leave `k² + 1 = 1 + k²` — append `; ring`.
* **Deferred-proof sweep (2026-10-17)** — the items marked "not formalized" in this session's
  chunks that are mathematical statements (not cost models or exercises) and need no later MCA
  section.  (a) §4.4.3: the modular splitting is the transposition of the classical one —
  `classical_split_eq_modular_transpose` (`RectangularSplitting.lean`, `Finset.sum_comm`).
  (b) §4.5: the two-sided Stirling bound's upper half `n! ≤ √(2πn)(n/e)^n e^{1/(12n)}` for `n ≥ 1`
  (`factorial_le_stirling_refined`, `StirlingRefinement.lean`): Mathlib's
  `Stirling.log_stirlingSeq_sdiff_hasSum` gives `log s_{n+1} − log s_{n+2} = ∑_k r^{k+1}/(2k+3)`
  with `r = 1/(2n+3)²`; bounding `1/(2k+3) ≤ 1/3` and summing the geometric series gives
  `1/(12(n+1)) − 1/(12(n+2))`, telescoping to `log s_{n+1} − log √π ≤ 1/(12(n+1))` via
  `le_of_tendsto` and `tendsto_stirlingSeq_sqrt_pi`.  (c) §4.5: (4.31)'s error is `Θ(1/N)` —
  `harmonic_sub_log_sub_gamma_ge`: `H_N − ln N − γ ≥ 1/(8(N+1))` for `N ≥ 3`
  (`AsymptoticExamples.lean`; `−ln(1 − x) ≥ x + x²/2 − x³/(1 − x)` from
  `Real.abs_log_sub_add_sum_range_le`, one step `≥ 1/(8m(m+1))`, telescoping, `le_of_tendsto_of_tendsto'`).
  (d) §4.4/§4.5: the error function as an integral — `erf_eq_integral` (`erf x = (2/√π)∫_0^x e^{−u²}`,
  from `integral_gaussian_Ioi` and `integral_Ioi_sub_Ioi'`), `erf_neg`, `erf_zero`; (4.22)
  `hasSum_erf_series` by `intervalIntegral.hasSum_integral_of_dominated_convergence` (bound
  `(x²)^j/j!`, `Real.summable_pow_div_factorial`); (4.23) `hasSum_erf_exp_series`: with
  `c_j = 2^j/(2j+1)‼` (`erfExpCoeff`, `c_{j+1}(2j+3) = 2c_j`) the series `S(x) = ∑ c_j x^{2j+1}`
  is differentiated term by term on a ball (`hasDerivAt_tsum_of_isPreconnected`, bound
  `c_j(2j+1)R^{2j}` summable by the ratio test), satisfies `S' = 1 + 2xS`, so
  `e^{−x²}S(x) − ∫_0^x e^{−u²}` has zero derivative (`is_const_of_deriv_eq_zero`) and vanishes at `0`
  (`ErrorFunctionSeries.lean`).  (e) §4.8.1: (4.70) to first order,
  `abs_ellipticK_sqrt_sub_log_le` (`|K(k') − ln(4/k)| ≤ (k²/4)(2 − ln k)`, `AGMLogBound.lean`); the
  second-order term `−k²/4 + (k²/4)ln(4/k)` of (4.70) is NOT formalized.  (f) §4.8.2: **the Legendre
  relation (4.72) PROVEN** (`LegendreRelation.lean`): `hasDerivAt_ellipticK`/`hasDerivAt_ellipticE`
  by `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the interval
  `Ioo (−m) m`, `m = (|k|+1)/2`, with constant bounds `m/√(1−m²)^3`, `m/√(1−m²)`; the identities
  `k ∂E/∂k = E − K` (`mul_ellipticE_deriv`, pointwise `√Δ − 1/√Δ = −k² sin²θ/√Δ`) and
  `k(1−k²) ∂K/∂k = E − (1−k²)K` (`ellipticK_deriv_identity`: `d/dθ [sin θ cos θ/√Δ] =
  (1 − 2sin²θ + k² sin⁴θ)/√Δ³` integrates to `0`, and `k²(1−k²) sin²θ/√Δ³ = √Δ − (1−k²)/√Δ − k² ·
  that derivative`); `legendreL k = E K' + E' K − K K'` has derivative `0` on `(0,1)`
  (`hasDerivAt_legendreL`: chain rule through `k' = √(1−k²)` with `dk'/dk = −k/k'`, then one
  `linear_combination` of the four identities with `k'² = 1 − k²`), is constant by
  `exists_hasDerivAt_eq_slope`, and tends to `π/2` at `0⁺`: `K(k) → π/2` (squeeze with
  `ellipticK_bounds`), `E(k') → 1` (`ellipticE_one`, `|E(k') − 1| ≤ (π/2)k` from
  `√A − √B ≤ √(A − B)` via `Real.abs_le_sqrt`), `K'(k)(E − K) → 0` (`|E − K| ≤ k²K ≤ πk²` and
  `K'(k) ≤ ln(4/k) + (k²/4)(2 − ln k)`, with `tendsto_log_mul_rpow_nhdsGT_zero` for `k² ln k → 0`);
  `tendsto_nhds_unique` finishes.  `legendre_relation_sqrt_half`: `2EK − K² = π/2` at `k = 1/√2`.
  Still not formalized from this session: the Brent–Salamin algorithm's `π` formula (needs `E` in
  terms of the AGM sequence — a Landen transformation for `E`), (4.26) (γ's integral
  representation is not in Mathlib), Euler–Maclaurin and everything resting on it ((4.32),
  (4.34)–(4.36) for `m ≥ 1`, (4.38)), the continued-fraction convergence (4.39)/(4.40), `Y_ν`,
  the analytic radii (4.56)/(4.57)/(4.61), and the `t`-form of (4.67).  Design note: the Legendre
  relation plus Gauss's theorem is the certified basis for a Brent–Salamin `π`; `erf_eq_integral`
  + (4.22)/(4.23) make the erf series branches of Algorithm 4.2 provable against the same `erf`
  as the asymptotic branch.  Lean notes: `HasDerivAt.mul` of a Pi-product `sin * cos` leaves
  `(sin * cos) θ` as an atom for `field_simp`/`ring` — state the product as a lambda; `set D := √…`
  before `field_simp` keeps the square root an atom (otherwise `ring_nf` inside the argument
  produces two spellings); find `linear_combination` cofactors by polynomial division in `D²` and
  `cos²` (the residual that `ring` prints is `P − combination`); `rw [h] at r` with `h : b² = 1 − k²`
  also rewrites inside an integral — `set` the integrals first; `HasDerivAt.comp` has `x` implicit
  here (`hK'.comp k hb'`), its result is `f ∘ g`, so finish with `simp only [Function.comp_apply]`
  and `rw [← hb]` to re-fold the `set` variable; `tendsto_one_div_add_atTop_nhds_zero_nat` needs
  `(𝕜 := ℝ)`; `tendsto_const_nhds.mul` is ambiguous between `Tendsto.mul` and the smul version —
  use `Tendsto.const_mul`/`const_sub`; `Ioo_mem_nhdsGT (h : a < b) : Ioo a b ∈ 𝓝[>] a`;
  `tendsto_log_mul_rpow_nhdsGT_zero` is in the root namespace; `Summable.sum_add_tsum_nat_add'`
  takes the summability of the *shifted* sequence (`(summable_nat_add_iff 1).mpr`); `erfExpCoeff 0`
  needs `norm_num [Nat.doubleFactorial]`; `Even.pow_nonneg (even_two_mul j)` where `positivity`
  fails on `R ^ (2 * j)`.
* **§4.8.4 Second AGM algorithm for the logarithm (2026-10-17).**  States: for large `x`, `q = 1/x`,
  compute `θ₂(q⁴)`, `θ₃(q⁴)` from (4.74)/(4.75) and `ln x = (π/4)/AGM(θ₂²(q⁴), θ₃²(q⁴))` (Sasaki–Kanada
  with `q ↦ q⁴`, avoiding `q^{1/4}`); trade-off between enlarging `x` (squaring / `2^ℓ`) and the
  series cost; stop when `O(q³⁶)` is negligible: `θ₂(q⁴) = 2q + 2q⁹ + 2q²⁵ + O(q⁴⁹)`,
  `θ₃(q⁴) = 1 + 2q⁴ + 2q¹⁶ + O(q³⁶)` (the pasted text reads `2q + q⁹ + q²⁵` and `1 + 2q⁴ + q¹⁶`;
  the exact series have coefficient 2 on every term, which is what is proven); so `x ≥ 2^{n/36}`
  (vs `2^{n/2}`), saving about four AGM iterations; implementation: `AGM(θ₂², θ₃²) =
  AGM(θ₂² + θ₃², 2θ₂θ₃)/2` skips the first square root, two non-scalar products suffice (Ex. 4.45),
  squares for products (§4.12); drawbacks: not self-correcting (full precision throughout, a `log n`
  factor lost against Newton/series), `exp` only via Newton on `ln` (§4.2.5, Ex. 4.6), trigonometric
  functions need complex AGM or Landen for incomplete integrals (larger constants); at best `O(1)`
  iterations saved.  Formalized in `Azurite/BrentZimmermann/Chapter4/SecondAGMLog.lean` (all
  proven): `nome_log` (`q = e^{−πs}` with `s = −ln q/π`), hence `sasaki_kanada'` for every
  `0 < q < 1` and `log_eq_pi_div_four_div_AGM` for `x > 1`; `theta2_pow_four` via
  `Real.pow_rpow_inv_natCast`; `theta2Int_eq_two_mul_tsum` by cancelling `q^{1/4}`; the generic
  tail lemma `tsum_pow_le_of_le` (`e n ≥ M + n ⇒ ∑ q^{e n} ≤ q^M/(1−q)`), `theta3_trunc`,
  `theta2Int_trunc` (split with `Summable.sum_add_tsum_nat_add'`), the concrete
  `theta3_pow_four_trunc`/`theta2_pow_four_trunc` with tails `2q³⁶/(1−q⁴)`, `2q⁴⁹/(1−q⁴)`;
  `inv_pow_le_of_two_rpow_le` (`x ≥ 2^{n/36} ⇒ q³⁶ ≤ 2^{−n}`) and the two `_error_le` bounds;
  `AGM_sq_sq` from `AGM_step` + `AGM_smul`; `sq_add_sq_eq_half_add`, `two_mul_mul_eq_half_sub`.
  Not formalized: the "about four iterations" comparison (heuristic; `agm_log_iterations` gives
  the first algorithm's count, the analogous count for `(θ₂², θ₃²)` would need the ratio
  `θ₂²/θ₃² ≈ 4q²`), the cost trade-off, the drawbacks (prose), Ex. 4.45 beyond its identities,
  §4.12.  Design note: this is the `AzFloat` `log` plan — argument expansion to `x ≥ 2^{p/36+c}`,
  three terms of each theta series (sparse, exact tails above certify the truncation), the AGM
  started from `(θ₂² + θ₃², 2θ₂θ₃)` without a square root, `π` from Brent–Salamin or a proven
  constant; the error budget is the two tails + the AGM bracket `b_j ≤ AGM ≤ a_j`.  Lean notes:
  `rw [one_div]` rewrites the *outer* `1 / (1/x)^4` first — compute `ln(1/(1/x)^4) = 4 ln x` in a
  separate `have`; `(q^4)^{1/4} = q` is `Real.pow_rpow_inv_natCast hq (by norm_num)` after
  `show (1/4:ℝ) = ((4:ℕ):ℝ)⁻¹`; ℕ inequalities like `(N+1)² + n ≤ (n+N+1)²` defeat `nlinarith` —
  expand with `ring` and use `Nat.le_mul_of_pos_right`; `norm_num [← pow_mul] at h` rearranges a
  conjunction of bounds into `a ≤ b ∧ b ≤ c + d` form — destructure and feed `linarith`.
* **§4.8.5 The complex AGM (2026-10-17).**  States: some asymptotically fastest algorithms need
  complex arithmetic for real results: `arctan x = ℑ ln(1 + ix)` (also `arcsin`, `arccos`),
  `cos x + i sin x = exp(ix)` with the complex `exp` by Newton from the complex `ln` (4.11); the
  AGM/`ln z` theory extends to `z ∉ (−∞, 0]` with the square root of positive real part; complex
  multiplication = 3 real (Karatsuba), complex squaring = 2 real; FFT domain (1 product = 3
  transforms): squaring `2M/3`, complex product `2M` (4 forward + 2 backward), complex square
  `4M/3` (2 + 2); Table 4.1 (real/complex: squaring 0.666/1.333, multiplication 1/2, reciprocal
  1.444/3.444, division 1.666/4.777, square root 1.333/5.333, AGM iteration 2/6.666, log via AGM
  `4 lg n`/`13.333 lg n`), details in §4.12.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ComplexAGM.lean` (all proven): `arctan_eq_im_log` via
  `Complex.log_im`, `Complex.tan_arg`, `Complex.abs_arg_lt_pi_div_two_iff`, `Real.arctan_tan`;
  `arcsin_eq_arctan'`/`arccos_eq_arctan` (Mathlib's `Real.arcsin_eq_arctan`,
  `arccos_eq_pi_div_two_sub_arcsin`); `exp_mul_I_eq` (`Complex.exp_mul_I`);
  `complex_mul_three_products`, `complex_sq_two_products` (`push_cast; ring_nf; rw [I_sq]; ring`);
  `fftCost f b = (f + b)/3` with `fftCost_real_sq/real_mul/complex_mul/complex_sq`.  Not
  formalized: convergence of the complex AGM and the complex `ln` (complex Gauss/Landen theory —
  a large project, only needed if trigonometric functions go through the AGM), the complex Newton
  `exp`, the §4.12 rows of Table 4.1 (reciprocal, division, square root, AGM iteration, log), the
  claim that complex arithmetic is "significantly slower" (cost model).  Design note: Azurite has
  no complex float type; the plan for `sin`/`cos`/`arctan` is real argument reduction + series
  (§4.3–§4.4), so the complex AGM is recorded, not planned.  Lean notes: `rw [← htan]` with
  `htan : tan (arg z) = x` rewrites every `x`, including inside `z` — use `conv_lhs => rw [← htan]`;
  `(1 + ↑x * I).re` is closed by `simp`; `Complex.tan_arg` is stated with `Real.tan`.
* **§4.9 Binary splitting, introduction (2026-10-17).**  States: AGM algorithms for `arctan`,
  `sin`, `cos` have a large constant in `O(M(n) log n)`, so `O((log n)^α M(n))` binary-splitting
  algorithms (`α ≥ 1` depending on the series' convergence and the multiplication algorithm) are
  competitive; the idea: for `x = p/q` with small `p, q`, `|x| ≤ 1/2`,
  `arctan(p/q) ≈ ∑_{j≤n/2} (−1)^j p^{2j+1}/((2j+1) q^{2j+1})` (the paste reads `q^{2k+1}`), an exact
  rational `P/Q` with `log|Q| = O(n log n)` (`exp`: `∼ n/ln n` terms, `log|Q| = O(n)`); divide and
  conquer `P/Q = (P₁Q₂ + P₂Q₁)/(Q₁Q₂)` recursively (useless with quadratic multiplication, the
  balanced products profit from fast multiplication); complexity (4.80)
  `∑_{k=1}^{⌈lg n⌉} 2^k M(2^{−k} n log n) = O((log n)^α M(n))`, `α = 2` in the FFT range, `α ≤ 2` in
  general (Ex. 4.47); precision `n` at the top levels saves a little, still `α = 2`; in practice
  the multiplication algorithm depends on the operand size.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/BinarySplitting.lean` (all proven): `arctanTerm`,
  `hasSum_arctanTerm` (Mathlib has `Real.hasSum_arctan` — the §4.4 note "arctan series not in
  Mathlib" is outdated), `abs_arctan_sub_sum_le` (tail `≤ |x|^{2N+1}/((2N+1)(1−x²))` via
  `norm_tsum_le_tsum_norm` + geometric series), `abs_arctan_sub_sum_le_two_pow` (`|x| ≤ 1/2`, `n/2+1`
  terms, error `≤ 2^{−n}`); `arctanDen q N = q^{2N+1}∏_{j<N}(2j+1)`, `arctanNum` (numerators
  `(−1)^j p^{2j+1} q^{2N−2j} ∏_{i≠j}(2i+1)`), `sum_arctanTerm_div_eq` (`Finset.mul_prod_erase`,
  `field_simp`), `log_arctanDen_le : log Q ≤ (2N+1) log q + N log(2N)` (so `O(n log n)` with
  `N ∼ n/2`), `log_factorial_mul_pow_le(')` for `exp` (`Nat.factorial_le_pow`); `div_add_div_eq`,
  `sum_div_eq_sum_mul_prod_erase_div`; the cost model `quasiLinearCost m = m logb 2 m` with
  `two_pow_mul_quasiLinearCost_div_le` (`2^k M(m/2^k) = m(lg m − k) ≤ M(m)`),
  `binary_splitting_cost_le` (each level `≤ 2 lg n · M(n)` since `lg(n lg n) ≤ 2 lg n` from
  `lg n ≤ n`, i.e. `Nat.lt_two_pow_self`), `clog_le_logb_add_one` (`Nat.pow_pred_clog_lt_self`),
  `binary_splitting_cost` (`≤ 4 (lg n)² M(n)`).  Not formalized: `α ≤ 2` for other multiplication
  models (Ex. 4.47), the top-level precision saving, size-dependent algorithm choice, and the
  recursive algorithm itself (theory first; the identities above are its correctness core).  Design
  note: binary splitting over `AzNat`/`AzInt` is the natural first `arctan`/`exp`-at-rationals
  engine for Azurite (exact integer arithmetic, one final division), and the constants `π` (Machin
  formulas) and `ln 2` fall out of it; the truncation theorems certify the number of terms.  Lean
  notes: `Finset.prod_le_prod` is the ordered-monoid version (one hypothesis) — for `ℝ` use
  `Finset.prod_le_prod₀ (h0) (h1)`; `a / b * c⁻¹ = a / (b * c)` is `rw [← div_eq_mul_inv, div_div]`
  (`ring` expands `(b*c)⁻¹` when `b*c` is a product of sums); `Real.log_pow` leaves `↑(2*N+1)` — `push_cast`
  afterwards; `Nat.lt_two_pow_self` is protected with implicit `n`.
* **§4.9 continued: repeated application, complexity, generalizations (2026-10-17).**  States: for
  `x ∈ (0, 1/4)` take `p/q ≤ x < (p+1)/q`; by (4.17) `tan(arctan x − arctan(p/q)) = (x − p/q)/(1 + px/q)`,
  so `arctan x = arctan(p/q) + arctan δ`, `δ = (qx − p)/(q + px)`, `|δ| < |x − p/q| < 1/q`, repeat on
  `δ`; with about `lg n` rationals `p_i/q_i`, `q_i = 2^{2^i}`, each `arctan(p_i/q_i)` costs
  `O((log n)^α M(n))`, total `O((log n)^{α+1} M(n))`; `0 ≤ p_i < 2^{2^{i−1}}` (`2^{i−1}` bits), value
  `O(2^{−2^{i−1}})`, size `O(2^i)`; `α + 1 ∈ {2, 3}`; small constants, useful to `≥ 10⁶` digits;
  generalization: Chudnovsky bit-burst for linear ODEs (§4.9.2).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ArctanBinarySplitting.lean` (all proven): `arctan_sub_arctan`
  (from `Real.arctan_add` at `−b`), `arctan_eq_arctan_rat_add`, `delta_nonneg_le`, `delta_lt_inv`
  (`δ ≤ x − p/q` since the denominator is `≥ q`; `<` would fail at `p = 0`, where `δ = x`); the
  iteration `bitBurstQ i = 2^{2^{i+1}}` (`Q₀ = 4` matches `x < 1/4`; `Q_{i+1} = Q_i²`),
  `bitBurstRem`/`bitBurstNum` (`p_i = ⌊Q_{i+1} r_i⌋`), `bitBurstRem_bounds` by induction with
  `Int.floor_le`/`Int.lt_floor_add_one`, `bitBurstNum_lt : p_i < Q_i` (the text's
  `p_i < 2^{2^{i−1}} = √q_i`), `bitBurstNum_div_lt`; `arctan_eq_sum_bitBurst` (induction on `L`),
  `arctan_le_self` (`Real.le_tan` at `arctan t`), `arctan_bitBurstRem_lt`,
  `abs_arctan_sub_sum_bitBurst_le` (`n ≤ 2^{L+1}` ⇒ `≤ 2^{−n}`) and `_clog_le` (`L = ⌈lg n⌉` via
  `Nat.le_pow_clog`); `repeated_binary_splitting_cost` (`⌈lg n⌉ · 4(lg n)² M(n) ≤ 8 (lg n)³ M(n)`,
  `α + 1 = 3` in the `m lg m` model).  Not formalized: `α + 1 = 2` for other models, the size
  `O(2^i)` as a bit count (follows from `p_i < Q_i`, `Q_{i+1} = 2^{2^{i+2}}`), the practicality
  remark, §4.9.2.  Design note: this is exactly the `AzFloat` `arctan` plan for `|x| < 1/4` — `⌈lg p⌉`
  exact binary splittings over `AzInt` with doubling denominators, each certified by
  `abs_arctan_sub_sum_le_two_pow`, plus the exact remainder recurrence; `|x| ≥ 1/4` reduces by
  `arctan x = π/4 + arctan((x−1)/(x+1))` or the halving of §4.3.  Lean notes: `Real.arctan_add`
  needs `x * y < 1` — subtraction is `arctan_add` at `−b` with `Real.arctan_neg`; `ring` proves
  `(a + -b)/(1 - a * -b) = (a - b)/(1 + a*b)` (it normalizes inside the inverse); a `noncomputable def`
  by structural recursion on `ℕ` with `Int.floor` casts works directly, `rfl` gives the unfolding
  lemmas; `Int.floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a`.
* **§4.9.1 A binary splitting algorithm for sin, cos (2026-10-17).**  States: Brent [45, Thm 6.2]
  claims `O(M(n) log² n)` for `exp` and `sin` (proof only for `exp`, `sin` via complex `exp(ix)`);
  Algorithm 4.4 SinCos avoids complex numbers: for `0 < x < 1/2`, `x ≈ ∑_{i=0}^{k} p_i 2^{−2^{i+1}}`,
  `0 ≤ p_i < 2^{2^i}`, `k = ⌈lg n⌉ − 1`; `x_j = ∑_{i≥j}`, `x_{k+1} = 0`, `y_j = p_j 2^{−2^{j+1}}`;
  `(S_{k+1}, C_{k+1}) = (0, 1)`; for `j = k..0`: `sin y_j, cos y_j` by binary splitting,
  `S_j = sin y_j C_{j+1} + cos y_j S_{j+1}`, `C_j = cos y_j C_{j+1} − sin y_j S_{j+1}`; `x_j = y_j + x_{j+1}`
  justifies step 6 by the addition formulae; `y_j` small rational so the powers stay `≤ n` bits;
  same `O(M(n) log² n)` as Brent's `exp`; useful for `tan x` and plane rotations.  Formalized in
  `Azurite/BrentZimmermann/Chapter4/SinCosBinarySplitting.lean` (all proven): `floor_mul_pow_bounds`
  (`2^m⌊y⌋ ≤ ⌊2^m y⌋ < 2^m(⌊y⌋+1)`), the digits `sinCosDigit x i = ⌊x2^{2^{i+1}}⌋ − 2^{2^i}⌊x2^{2^i}⌋`
  with `sinCosDigit_nonneg/lt`, `sum_sinCosDigit_div` (telescoping `Finset.sum_range_sub`, `⌊2x⌋ = 0`),
  `sub_sum_sinCosDigit_bounds`/`_lt_two_pow` (`n ≤ 2^{k+1}` ⇒ `< 2^{−n}`); `tailSum`, `tailSum_eq_add`,
  `tailSum_top`, `sin_cos_add_step`; `sinCosProd` (the pair `(C_j, S_j)` as `C_j + iS_j`, a product of
  rotations), `sinCosProd_top` (`(0,1)`), `sinCosProd_re/_im` (step 6 exactly), `sinCosProd_exact`
  (`Complex.exp_sum`), `sinCosProd_exact_im/_re` (`S_j = sin x_j`, `C_j = cos x_j`);
  `norm_prod_sub_prod_le` (`‖∏a − ∏b‖ ≤ mε(1+ε)^m`, unimodular `b`, induction with
  `prod_range_succ`), `sinCos_error` (`ε`-accurate `sin y_i, cos y_i` ⇒ outputs within
  `2(k+1)ε(1+2ε)^{k+1}`: the text's "error `O(2^{−n})`" needs `ε = O(2^{−n}/lg n)`, i.e. `lg lg n`
  guard bits — the rotation structure keeps the error additive, a 1-norm argument would give
  `(√2)^k`); `pow_lt_two_pow_of_digit` (`p^N < 2^{2^j N}`).  Not formalized: the cost accounting
  `O(M(n) log² n)`, Brent's theorem, the remarks on `tan`/rotations, and the algorithm (theory first).
  Design note: the `AzFloat` `sin`/`cos` plan for `|x| < 1/2`: `sinCosDigit` blocks from the significand
  (they are literally bit slices of doubling length), exact binary splitting for each `sin y_j, cos y_j`
  over `AzInt` (certified by the §4.4 series bounds), the rotation recurrence in working precision
  `p + lg lg p + c`; `|x| ≥ 1/2` reduces by halving (§4.3) or mod `π/2`.  Lean notes: a floor divided by
  a power elaborates as integer division — ascribe `(⌊…⌋ : ℝ)`; `push_cast` turns `↑(Real.cos y)` into
  `Complex.cos ↑y`, breaking matches with `exp_mul_I_eq` — use `Complex.ofReal_sum` + `sum_mul` instead,
  and `simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]` for real/imaginary
  parts (the unused-simp-arg linter is a warning: keep only what fires); `div_add_div_same` does not
  exist — `← add_div`; `gcongr` leaves `‖a m − b m‖ ≤ ε` side goals in unpredictable order — build the
  `add_le_add (mul_le_mul …) …` term by hand.
* **§4.9.2 The bit-burst algorithm — holonomic functions (2026-10-17).**  States: the previous
  algorithms need functional equations (`tan`, `exp`, `sin` addition); the bit-burst algorithm does
  not and applies to holonomic (D-finite) functions: a linear homogeneous ODE with polynomial
  coefficients, equivalently a linear homogeneous recurrence with polynomial coefficients for the
  Taylor coefficients; closed under `+`, `×`, not `/`; `exp`, `ln`, `sin`, `cos` holonomic, `tan` not;
  hypergeometric (`u_{k+1}/u_k = R(k)`, §4.4) is the order-one case `u_{k+1}Q(k) − u_kP(k) = 0`; much
  more general (Ex. 4.48): hypergeometric term ratios have size `O(log k)`, holonomic ones can be much
  larger.  Formalized in `Azurite/BrentZimmermann/Chapter4/Holonomic.lean` (all proven): on `ℝ`,
  `IsHolonomic f := ∃ r a, (∃ i, a i ≠ 0) ∧ ∀ x, ∑_{i≤r} (a i).eval x · iteratedDeriv i f x = 0` and
  `IsPRecursive u` likewise; `isHolonomic_exp` (`−f + f′ = 0`), `isHolonomic_sin/cos` (`f + f″ = 0`),
  `isHolonomic_log` (`f′ + x f″ = 0` — true at `x = 0` too with Lean's `0⁻¹ = 0`, `Real.deriv_log'`,
  `deriv_inv'`); `RationalRatio.isPRecursive` (order `δ ≥ 1`, coefficients `−P` at `0`, `Q` at `δ`).
  Algebraic theory for a differential field extension `B/A` (Mathlib's `Differential`,
  `DifferentialAlgebra`, derivation `′`): `iterDeriv n b`, `deriv_smul_coeff` (`(c•x)′ = c′•x + c•x′`
  via `Derivation.leibniz` + `deriv_algebraMap`), `span_deriv_closed` (`Submodule.span_induction`),
  `derivSpan A b = span A {b^{(n)}}`, `IsDFinite A b := (derivSpan A b).FG`; **closure**
  `IsDFinite.add` (span of `(a+b)^{(n)}` ≤ `V ⊔ W`, `Submodule.FG.sup`) and `IsDFinite.mul` (≤ `V * W`,
  which is `′`-closed by `Submodule.mul_induction_on` + Leibniz, `Submodule.FG.mul`), with
  `fg_of_le_fg` (over a field via `fg_iff_finiteDimensional`); the ODE characterization:
  `IsDFinite.exists_relation` (`d + 1` derivatives in a `d`-dimensional space are dependent:
  `LinearIndependent.fintype_card_le_finrank`, `not_linearIndependent_iff`) and
  `isDFinite_of_relation` (induction on the order: if the top coefficient vanishes drop it via
  `Fin.sum_univ_castSucc`/`Fin.exists_castSucc_eq`, else `b^{(r)} ∈ span{b^{(i)} : i < r}` which is
  then `′`-closed, so every derivative lies in a span of finitely many).  Not formalized: ODE ⟺
  coefficient recurrence for power series (both notions defined; the bookkeeping is
  `ascPochhammer` index shifting), `tan` not holonomic, closure fails under division (example), the
  `O(log k)` ratio size, Ex. 4.48.  Design note: the D-finite closure theorems are the licence to
  build `AzFloat` evaluators compositionally (e.g. `exp·sin`, `erf` as holonomic) once a bit-burst
  evaluator exists; the concrete `IsHolonomic` examples give the ODEs an evaluator would consume.
  Lean notes: inside `theorem IsDFinite.mul`, `ha.mul hb` resolves to the theorem *being defined*
  (recursive reference) rather than `Submodule.FG.mul` — write the Mathlib name; `IsDFinite` unfolds
  to `FG` so `ha.sup hb` does find `Submodule.FG.sup`; `variable (A) in def …` for an explicit
  type argument inside a `variable {A}` section; the unused-section-variable linter wants
  `omit [Differential A] [DifferentialAlgebra A B] in` on purely linear-algebraic lemmas;
  `Fin.coe_castSucc` is deprecated for `Fin.val_castSucc`; `if_true`/`if_false` for `ite_true`/`ite_false`;
  `Submodule.span_induction` as `induction hx using Submodule.span_induction with | mem | zero | add | smul`.
* **§4.9.2 Theorem 4.2, the bit-burst algorithm (2026-10-17).**  States: `f` holonomic, no singularity
  on `[A,B] ∋ 0`, `f(0) = 0` ⇒ `f(x)` to `n` bits for `n`-bit `x ∈ (A,B)` in `O(M(n) log³ n)` (sharper:
  Ex. 4.49; `f(0)` may be any `n`-bit-computable value).  Proof: `0 ≤ x < 1`, `x = r₁ + ⋯ + r_k`
  with blocks of 1, 2, 4, … bits, `2^{k−1} ≤ n < 2^k`; `x_i = r₁ + ⋯ + r_i`, `f_i(t) = f(x_i + t)`,
  `f_i^* = f_i − f_i(0)`, telescoping `f(x) = ∑_{i<k} f_i^*(r_{i+1})`; `r_{i+1}` has a `2^i`-bit numerator
  and `0 ≤ r_{i+1} < 2^{1−2^i}`, so `n/2^i + O(log n)` terms; translate the ODE
  `∑ c_j(x_i + t) f_i^{(j)} = 0` (inhomogeneous `E = b` ⇒ `b′E − bF`), coefficient recurrence with
  `O(2^i)`-bit coefficients, `ℓ`-th coefficient size `O(ℓ(2^i + log ℓ)) = O(n log n)`; evaluate the
  partial sums `s_ℓ` via `u_ℓ = (s_ℓ − s_{ℓ−1})/r^ℓ`, order `d+1` recurrence, matrix form
  `S_ℓ = M_ℓ S_{ℓ−1}`, product (4.81) by binary splitting in `O(M(n) log² n)`; example `arctan`:
  `f′(1+t²) = 1`, `(1+x_i²)ℓu_ℓ + 2x_i(ℓ−1)u_{ℓ−1} + (ℓ−2)u_{ℓ−2} = 0`, the `v_ℓ = u_ℓ r^ℓ` and `s_ℓ` forms,
  3×3 matrices.  Formalized in `Azurite/BrentZimmermann/Chapter4/BitBurst.lean` (all proven; the
  cost claims are not): `blockNum x a b = ⌊x2^b⌋ − 2^{b−a}⌊x2^a⌋` with `0 ≤ · < 2^{b−a}`,
  `bitBlock = blockNum/2^b < 2^{−a}`, `bitBlock_eq_sub`; `burstBlock x i = bitBlock x (2^i−1) (2^{i+1}−1)`
  (`burstBlock_num_lt : < 2^{2^i}`, `burstBlock_lt : < 2·(1/2)^{2^i}`), `sum_burstBlock` (telescoping to
  the `2^k−1`-bit truncation), `sum_burstBlock_eq_self` (`x·2^n ∈ ℤ`, `n ≤ 2^k−1` ⇒ exact);
  `sum_shift_sub`, `eq_sum_shift_sub` (`Finset.sum_range_sub`); `iteratedDeriv_comp_const_add`
  (induction with `iteratedDeriv_succ'`, `deriv_comp_const_add`), `IsHolonomic.comp_const_add`
  (coefficients `c_j.comp (X + C x_i)`, `comp_X_add_C_ne_zero_iff`); `isHolonomic_of_inhomogeneous`
  (hypotheses: all `iteratedDeriv j f` differentiable, top coefficient `c_m ≠ 0`, `b ≠ 0`; the derivative
  of the relation by `HasDerivAt.sum` + `Polynomial.hasDerivAt`, uniqueness, new coefficients
  `b′c_j − b c_j′ − b c_{j−1}` built with `Fin.snoc`/`Fin.cons`, top coefficient `−b c_m`);
  `isHolonomic_arctan` (`(1+t²)f″ + 2tf′ = 0`); `arctan_shift_coeff_recurrence` for a formal power
  series `g` with `g′·(C(1+c²) + C(2c)X + X²) = 1` (coefficient `ℓ+1` of both sides;
  `PowerSeries.coeff_derivative`, `coeff_mul_X_pow'`), `arctan_v_recurrence` (`× r^{ℓ+2}`),
  `arctan_s_recurrence` (`s_{ℓ+1} = s_ℓ + v_{ℓ+1}`), `arctanStepMatrix` + `arctan_step_matrix_eq`
  (`S_{ℓ+3} = M_{ℓ+3} S_{ℓ+2}`), `matProd`/`vec_eq_matProd_mulVec` (4.81).  Not formalized: the
  `O(M(n) log³ n)`/`O(M(n) log² n)` costs, the term count `n/2^i + O(log n)` (needs coefficient bounds
  for the translated series), the size estimate `O(ℓ(2^i + log ℓ))`, the general ODE → recurrence
  translation (§4.12; done for the example), the "no singularities" hypothesis (our `IsHolonomic` on
  `ℝ` is global and the translated recurrence is a formal identity), Ex. 4.49, the algorithm.  Design
  note: for `AzFloat`, Theorem 4.2 is the blueprint for a *generic* evaluator — an ODE (as `IsHolonomic`
  data) + bit-burst blocks + exact `AzInt` matrix products; `arctan` is the worked instance and
  `arctan_step_matrix_eq` is the exact 3×3 step a Lean implementation would iterate.  Lean notes:
  `HasDerivAt.sum` yields `HasDerivAt (∑ i, A i) …` with a Pi-sum of functions — not syntactically
  `fun y => ∑ A i y`; convert with `congr_of_eventuallyEq` and `Finset.sum_apply` (explicit arguments,
  the mvars do not unify through the beta-redex); `Polynomial.hasDerivAt (p) (x)` takes `p` explicitly;
  `open scoped PowerSeries in` must precede the docstring; with both `Polynomial` and `PowerSeries`
  open, `C`/`X`/`coeff` are ambiguous — qualify; `if_pos`/`if_neg` are deprecated for
  `ite_eq_left`/`ite_eq_right`; `push_cast` normalizes `ℓ + 1 − 2` to `ℓ − 1` (a later `show` rewrite then
  fails); a `rw [show 2^k − 1 = n + (2^k−1−n) …]` also rewrites inside `2^k − 1 − n` — introduce `p` with
  `obtain ⟨p, hp⟩`; `conv_rhs => rw [hk]` to rewrite an exponent on one side only; `Matrix.dotProduct` is
  now `dotProduct`; `arctanStepMatrix c r ℓ.mulVec` parses as `ℓ.mulVec` — parenthesize.
