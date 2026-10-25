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
* **§4.10 Contour integration (2026-10-17).**  States: with complex arithmetic available, `f`
  holomorphic on `|z| < R`, `R > 1`, `f = ∑ a_j z^j` (4.82), Cauchy `a_j = (2πi)⁻¹∮_{|z|=1} f(z)z^{−j−1}dz`
  (4.83), approximated by `S_{j,k} = (1/k)∑_{m<k} f(e^{2πim/k})e^{−2πijm/k}` (4.84); for `j < k`,
  `S_{j,k} − a_j = (2πi)⁻¹∮_{C'} f(z)/((z^k−1)z^{j+1}) = a_{j+k} + a_{j+2k} + ⋯` (4.85, Ex. 4.50), so
  `|S_{j,k} − a_j| = O((R−δ)^{−(j+k)})`; for `f = z/(e^z−1) + z/2` (4.86), `a_{2j} = B_{2j}/(2j)!`,
  `R = 2π`, (4.87) and `B_{2j}` with relative error `O((2π)^{−k})` from `k` evaluations; cancellation
  ⇒ `O(j)` guard digits (`j = O(n)`); time `O(jnM(n))`, space `O(n)` (vs `Θ(jn)` for §4.7.2's
  recurrence), useful when all `B_{2i}` are consumed on the fly as in (4.38).  Formalized in
  `Azurite/BrentZimmermann/Chapter4/ContourIntegration.lean` (all proven): `hasSum_cauchy_coeff`
  ((4.83) for `f` differentiable on the closed unit disc: `f z = ∑_j ((2πi)⁻¹∮ f w/w^{j+1}) z^j`,
  from `DifferentiableOn.hasFPowerSeriesOnBall`, `HasFPowerSeriesOnBall.hasSum`,
  `cauchyPowerSeries_apply`, `circleIntegral.integral_const_mul`); `aliasSum a j k` with
  `f(ζ^m) := ∑' a_l (ζ^m)^l` and the weight `ζ⁻¹^{jm}`; `sum_zpow_primitiveRoot`
  (`∑_{m<k}(ζ^d)^m = k·[k ∣ d]`, `IsPrimitiveRoot.zpow_eq_one_iff_dvd`, `geom_sum_eq`);
  `aliasSum_eq_tsum` (interchange `Summable.tsum_finsetSum`, orthogonality, reindexing by
  `Function.Injective.tsum_eq` with `m ↦ j + mk`, using `j < k` for the support), `aliasSum_sub_eq`
  (4.85), `norm_aliasSum_sub_le` (`‖a_l‖ ≤ Cr^l` ⇒ `‖S − a_j‖ ≤ Cr^{j+k}/(1−r^k)`);
  `bernoulliCoeff l := coeff l scaledBernoulliPowerSeries` (`bernoulliCoeff_eq : = B_l/l!` for
  `l ≠ 1` via `bernoulli_eq_zero_of_odd`), `norm_bernoulliCoeff_le` (`≤ (π²/3)(2π)^{−l}` from
  `abs_scaledBernoulli_le`), `bernoulli_aliasSum_sub_eq` (4.87), `two_mul_le_norm_scaledBernoulli`
  (`‖B_{2j}/(2j)!‖ ≥ 2(2π)^{−2j}`), `norm_bernoulli_aliasSum_sub_le` (relative error
  `≤ (π²/6)(2π)^{−k}/(1−(2π)^{−k})`).  Not formalized: the contour form of (4.85) (Ex. 4.50), the
  identification of `z/(e^z−1) + z/2` with its series on `|z| < 2π` (radius `2π`: the formal series
  is used), the guard-digit remark, time/space costs, other quadratures (§4.12).  Design note:
  Azurite has no complex floats; the aliasing identity is nonetheless usable with real arithmetic
  for the *even* Bernoulli coefficients (the `k`-point sums pair conjugate roots), but §4.7.2's exact
  rational recurrence (tangent numbers, `AzRat`) is the planned Bernoulli source — this section
  stays recorded.  Lean notes: `π` without `open Real` is auto-bound as a variable (`π : ℂ`
  appeared silently — autoImplicit); `((1:ℝ≥0):ℝ)` in `closedBall`/`C(0, ↑1)` must be normalized
  with `NNReal.coe_one` before `convert`; `HasFPowerSeriesOnBall.hasSum` wants `y ∈ Metric.eball 0 r`
  (`edist_dist`, `ENNReal.ofReal_lt_ofReal_iff`); in a product with a `zpow` factor the other `^`
  exponents get coerced to `ℤ` — write the negative power as `ζ⁻¹ ^ (j*m)` and convert inside the
  proof with `inv_zpow`, `← zpow_natCast`, `← zpow_mul`, `← zpow_add₀`; `Summable.tsum_finsetSum`
  is the `tsum`/finite-sum interchange (generated by `to_additive` from `Multipliable.tprod_finsetProd`
  — grep for the multiplicative name); `Function.Injective.tsum_eq (hg) (hf : support f ⊆ range g)`
  reindexes a sum over an arithmetic progression; `ring_nf` can normalize bound variables in two
  `tsum`s differently — prefer `ring` when the atoms already match.

## MCA Chapter 4 exercises

Answers to the exercises of Brent–Zimmermann Chapter 4, one bullet each (user instruction
2026-10-17: proofs and/or prose, so the answer can be looked up here).  Formal content lives in
`Azurite/BrentZimmermann/Chapter4/Exercises.lean`.

* **Exercise 4.1** (`ln A` for a formal power series `A = ∑ a_j x^j`, `a₀ = 1`, with error
  `O(xⁿ)` in time `O(M(n))`; hint `(ln A)′ = A′/A`; and whether the same holds for `n`-bit numbers
  with `x = 1/2`).  **Answer.**  Define `ln A := ∫ A′/A` (the formal integral of §4.2.4 applied to
  `A′ · A⁻¹`); it is the unique series with constant term `0` and derivative `A′/A`
  (`logSeries`, `derivative_logSeries`, `logSeries_unique`; sanity checks `logSeries_exp : ln(exp x)
  = x`, `logSeries_mul : ln(AB) = ln A + ln B`).  *Algorithm modulo `xⁿ`*: (1) `A′` — `O(n)`
  coefficient operations; (2) `B := 1/A mod xⁿ` by Newton's iteration `x_{j+1} = x_j + x_j(1 − x_j A)`
  (§4.2.4, `ringReciprocalSeq`, error of order `2^j`), doubling the precision `1, 2, 4, …, n`, each
  step one or two products at the current precision; (3) `C := A′B mod xⁿ` — one product `M(n)`;
  (4) `ln A := ∫ C` — `n` divisions by `j + 1`, `O(n)`.  Correctness of working modulo `xⁿ`
  throughout: `X_pow_dvd_logSeries_sub` — if `A ≡ B (mod x^{n+1})` then `ln A ≡ ln B (mod x^{n+1})`
  (the numerator `A′B − AB′` of `A′/A − B′/B` is divisible by `xⁿ`, and integration raises the
  order by one, `X_pow_dvd_integral`), so only `A mod xⁿ` matters and the truncated reciprocal
  and product lose nothing.  *Cost*: the "reasonable smoothness condition" is `M(2m) ≥ 2M(m)`
  (equivalently `M(m)/m` nondecreasing); then `∑_{k<L} M(2^k) ≤ M(2^L)` (`sum_cost_le`, by
  induction: `S_L + M(2^L) ≤ 2M(2^L) ≤ M(2^{L+1})`), so Newton costs `O(M(n))`, and the total is
  `O(M(n)) + O(n) = O(M(n))`.  (Alternative: Newton for `exp` applied to `ln`, §4.2.4/§4.2.5,
  same bound.)  *The numerical question*: **no** such transfer is known.  Substituting `x = 1/2`
  turns the series into a number and the coefficient-wise steps lose their meaning: the integration
  `c_j ↦ c_j/(j+1)` is not a ring operation on the number (carries mix the "coefficients"), and
  `A′` is likewise meaningless; what survives is only the identity `(ln y)′ = 1/y` as a real
  function.  For an `n`-bit real the best known bounds are `O(M(n) log n)`, via the AGM (§4.8.2,
  our `agmLog`/`log_eq_pi_div_four_div_AGM` + `agm_log_iterations`) or Newton on `exp` with the
  series/bit-burst evaluation (§4.4, §4.9.2); no `O(M(n))` algorithm for `ln` of a number is known,
  in contrast to the formal case, which is a genuine difference between power series and numbers.
* **Exercise 4.2** (Schönhage, Schost: `1/s(x) mod xⁿ` by an odd–even scheme, §1.3.5, and its
  complexity in the FFT range).  **Answer.**  *Identity*: `s(x)s(−x)` is an even series (the odd
  coefficients `∑_{i+k odd} a_i a_k (−1)^k` cancel in pairs `(i,k) ↔ (k,i)`, `coeff_odd_mul_rescale_neg_one`),
  so `s(x)s(−x) = t(x²)` with `t_j = [x^{2j}] s(x)s(−x)` (`oddEvenT`, `mul_rescale_neg_one_eq_expand`),
  `t₀ = a₀² ≠ 0`, and `1/s(x) = s(−x) · (1/t)(x²)` (`inv_eq_rescale_mul_expand_inv`).  *Algorithm*
  `OddEvenRecip(s, n)`: (1) if `n = 1` return `1/a₀`; (2) `t := ` even part of `s(x)s(−x) mod xⁿ`
  (`⌈n/2⌉` coefficients); (3) `u := OddEvenRecip(t, ⌈n/2⌉)`; (4) return `s(−x) · u(x²) mod xⁿ`.
  Correctness of the truncations: `u ≡ 1/t (mod x^m)` ⇒ `s(−x)u(x²) ≡ 1/s (mod x^{2m})`
  (`X_pow_dvd_inv_sub_oddEven`), so with `m = ⌈n/2⌉` the result is `1/s mod xⁿ`.  The scheme is
  the §1.3.5 odd–even trick (`s(x) = s_e(x²) + x s_o(x²)`) applied to division: it halves the
  *size* instead of doubling the *precision* as Newton does, and needs no starting approximation.
  *Complexity in the FFT model* (§4.8.5: one product of two `n`-term series = three transforms of
  length `2n`, each `M(n)/3`; a transform of half length costs `M(n)/6`): per level, one forward
  transform of `s` (`M(n)/3`; the transform of `s(−x)` is the same list of values permuted — `s(−ω^k)
  = s(ω^{k+n})` for a `2n`-th root of unity — so free), one pointwise product, one *half-length*
  inverse transform for the even part `t` (the even coefficients of a convolution come from the
  averages `(P_k + P_{k+n})/2`, `M(n)/6`), the recursive call, one half-length forward transform
  of `u(x²)` (its values at the `2n`-th roots repeat those of `u` at the `n`-th roots, `M(n)/6`),
  the pointwise product with the stored transform of `s(−x)`, and one full inverse transform
  (`M(n)/3`): `T(n) ≤ T(n/2) + M(n)`, hence `T(n) ≤ T(1) + 2M(n)` when `M(2m) ≥ 2M(m)`
  (`cost_recurrence_le` with `c = 1`); i.e. about `2M(n)`, the same order as Newton's reciprocal
  and without the self-correction requirement.  MCA's Table 4.1 lists `1.444 M(n)` for the
  reciprocal in the FFT range; the extra saving over our `2M(n)` (reusing transforms across levels,
  a cheaper bottom of the recursion, wrapped transforms) is the §4.12 material we do not have —
  what is recorded here is the scheme and the `≤ 2M(n)` analysis.  Formal content:
  `Exercises.lean`, section `Exercise42`.
* **Exercise 4.3** (`g(h(x)) = x`, `y_j = h(x_j)`: show that `x_{j+1} = x_j + ∑_{m=1}^{k−1} (y − y_j)^m
  g^{(m)}(y_j)/m!` is a `k`-th order iteration converging to `x = g(y)`; generalize (4.16)).
  **Answer.**  Since `g(h(x_j)) = x_j`, the right-hand side is the degree-`(k−1)` Taylor polynomial of
  `g` at `y_j`, evaluated at `y` (its constant term `g(y_j)` *is* `x_j`; `taylorInverseStep_eq_taylor`).
  Taylor's theorem with Lagrange remainder gives `g(y) − x_{j+1} = g^{(k)}(ξ)(y − y_j)^k/k!` for some
  `ξ` strictly between `y_j` and `y` (`taylorInverseStep_sub`, from Mathlib's
  `taylor_mean_remainder_lagrange_iteratedDeriv`), so with `|g^{(k)}| ≤ M` there,
  `|x − x_{j+1}| ≤ M|y − y_j|^k/k!` (`abs_sub_taylorInverseStep_le`; the degenerate case `y_j = y`
  gives `x_{j+1} = x_j = x`).  Since `y − y_j = h(x) − h(x_j)`, if `h` is Lipschitz with constant `L`
  (e.g. `|h′| ≤ L`), `|x − x_{j+1}| ≤ (M L^k/k!)\,|x − x_j|^k` (`taylorInverseStep_order`): the
  iteration has order `k`.  For `k = 2` this is Newton's method (`x_{j+1} = x_j + (y − y_j)g′(y_j)`,
  §4.2.5 with `g′(y_j) = 1/h′(x_j)`), for `k = 3` the cubic iteration of §4.2.6 whose error
  derivation is (4.16) — the exercise replaces the explicit expansion there by the general
  Lagrange remainder.  *Convergence* ("suitable conditions"): the smoothness of `g` near `y`, the
  Lipschitz bound on `h` near `x`, and a starting point close enough that `C|x₀ − x|^{k−1} ≤ 1/2`
  with `C = ML^k/k!`; then `e_{j+1} ≤ C e_j^k ≤ (1/2) e_j`, so `|x_j − x| ≤ |x₀ − x|/2^j → 0`
  (`iterate_le_of_order`, by induction; the iterates stay in the region where the bounds hold
  because the error is decreasing), and in fact `e_{j+1} ≤ C e_j^k` is the `k`-th order statement.
  Formal content: `Exercises.lean`, section `Exercise43`.
* **Exercise 4.4** (a Horner-like algorithm evaluating `∑_{j≤k} a_j x^j` in the *forward*
  direction, deciding dynamically where to stop; `|a_j|` monotonic decreasing, `|x| < 1/2`; hint
  `y = 1/x`).  **Answer.**  Horner's rule proper runs from the top coefficient down
  (`s ← s·x + a_j`) and so needs `k` in advance.  With `y = 1/x` run Horner in `y` from the bottom
  up: `T₀ = a₀`, `T_{j+1} = T_j·y + a_{j+1}`, so that `T_j = ∑_{i≤j} a_i y^{j−i}` and the partial sum
  is `S_j = ∑_{i≤j} a_i x^i = x^j T_j` (`forwardHorner`, `forwardHorner_eq_sum`,
  `sum_eq_pow_mul_forwardHorner`): one multiplication and one addition per coefficient, in the
  order the coefficients are produced.  *Stopping*: for decreasing `|a_i|` and `|x| < 1/2` the tail
  is dominated by a geometric series, `|∑_{i>j} a_i x^i| ≤ |a_{j+1}||x|^{j+1}/(1−|x|) ≤
  2|a_{j+1}||x|^{j+1} ≤ |a_j x^j|` — the tail never exceeds the last term added
  (`abs_tsum_sub_sum_le_two_mul`, `abs_tsum_sub_sum_le_term`).  Hence: maintain `z_j = ε|y|^j`
  (`z_{j+1} = z_j·|y|`, one more multiplication) and stop as soon as `|a_j| ≤ z_j`, which is exactly
  `|a_j x^j| ≤ ε` (`stop_criterion_iff`); return `x^j·T_j` (`x^j` by binary powering, `O(log j)`
  products, or carried along).  Then `|∑ a_i x^i − x^j T_j| ≤ ε` (`abs_tsum_sub_forwardHorner_le`).
  *Algorithm* `ForwardHorner(a, x, ε)`: `y ← 1/x; T ← a₀; z ← ε; j ← 0; while |a_j| > z: j ← j+1;
  T ← T·y + a_j; z ← z·|y|; return x^j·T`.  Remarks: (i) the test is on the *coefficient* against a
  growing threshold, so no power of `x` is formed in the loop; (ii) compared with the plain forward
  recurrence `t_j = t_{j−1}x`, `S += t_j` (§4.4, stop when `|t_j| < ε`) the cost per term is the
  same (two products, one addition), but all coefficients enter through additions to `T` whose
  magnitude grows like `|y|^j` — in floating point the relative error of `T_j` is `O(jε)` as in the
  §4.4 analysis (`roundedSum_sub_le`), and the final `x^j T_j` scales it back; (iii) for a finite
  sum (`a_j = 0` for `j > k`) the loop stops at `j ≤ k` automatically; (iv) the hypothesis
  `|x| < 1/2` is what makes "tail ≤ last term" true — for `1/2 ≤ |x| < 1` the same argument gives
  tail `≤ |a_j x^j|·|x|/(1−|x|)`, i.e. the test must be scaled by `(1−|x|)/|x|`.  Formal content:
  `Exercises.lean`, section `Exercise44`.
* **Exercise 4.5** (`n` bits of `exp x`, `x` of order `2^j`, by repeated doubling (§4.3.1) and the
  naive series: the best reduced argument `x/2^k` in terms of `n` and `j`, for `j ≥ 0` and `j < 0`).
  **Answer.**  Reduce by `k` halvings to `r = x/2^k` of size `2^{j−k} = 2^{−m}`, `m := k − j`; sum
  the series for `exp r` with `d` terms; square `k` times.  *Terms needed*: with `|r| ≤ 2^{−m}`,
  `|exp r − ∑_{i<d} r^i/i!| ≤ 3·2^{−md}/d! ≤ 2^{−n}` as soon as `m·d ≥ n + 2`
  (`exp_series_terms_of_small`, from `abs_exp_sub_sum_le`; the `1/d!` is a further gain, see below),
  so `d ≈ n/m`.  *Cost*: the naive evaluation costs one multiplication per term (`d`) and the
  doublings `k` squarings, all at precision `≈ n` (plus guard bits): `(d + k) M(n) ≈ (n/m + m + j)
  M(n)`.  Minimizing `n/m + m` over `m > 0`: `n/m + m ≥ 2√n` with equality at `m = √n`
  (`doubling_cost_ge`, `doubling_cost_sqrt`, AM–GM).  Hence the **optimal reduced argument is
  `|x|/2^k ≈ 2^{−√n}`**, i.e. `k = j + √n` (rounded), giving `d ≈ √n` terms, `k ≈ j + √n` squarings
  and total cost `≈ (2√n + j) M(n)` — the `O(√n M(n))` of §4.3.1.  *Case `j ≥ 0`*: `k = j + √n`
  doublings, of which the first `j` only bring `x` below `1` and the remaining `√n` are the real
  trade-off.  *Case `j < 0`*: `x` is already small; if `|j| < √n` the same choice `k = j + √n > 0`
  applies (fewer doublings, `√n − |j|`), and if `|j| ≥ √n` no reduction is needed at all (`k = 0`,
  `m = |j| ≥ √n`, `d ≤ n/|j| ≤ √n` terms): the reduced argument is `x` itself.  *Precision loss*:
  each squaring doubles the relative error (§4.3.2, `abs_squareSeq_sub_exp_le`: the final error is
  `≈ 2^k ε + ∑ 2^{k−1−i}θ_i`), so `k = O(√n + j)` guard bits are needed — `O(√n)` for `j = O(√n)`,
  negligible against `n`, but for very large `j` the guard bits `≈ j` and the `j` extra squarings
  dominate, which is why §4.3 reduces `x ≥ 1` by `ln 2` (or `exp(x) = exp(x − ⌊x/ln2⌋ ln 2) 2^{⌊·⌋}`)
  rather than by halving.  *Refinement with `d!`*: the exact condition `2^{−md}·3/d! ≤ 2^{−n}` is
  `md + log₂(d!/3) ≥ n`, i.e. `d(m + log₂ d − 1.44…) ≳ n`; with `d ≈ √n` this shifts the optimum to
  `m ≈ √n − (1/2)log₂ n`, a lower-order correction — the reduced argument stays `2^{−√n(1 + o(1))}`.
  Formal content: `Exercises.lean`, section `Exercise45`.
* **Exercise 4.6** (given `ln x` to `n` bits in time `T(n)` with `n ≪ M(n) = o(T(n))`, compute
  `exp x` to `n` bits in time `∼ T(n)`; smoothness of `T`, `M` assumed).  **Answer.**  Invert `ln`
  by the order-`k` iteration of Exercise 4.3 with `g = exp`, `h = ln` (target `exp x`, so "`y`" is
  `x` and `y_j = ln z_j`).  Because `exp^{(m)} = exp` and `exp(ln z_j) = z_j`, the step collapses to
  `z_{j+1} = z_j · ∑_{m<k} (x − ln z_j)^m/m!` (`expViaLogStep`, `expViaLogStep_eq_taylorInverseStep`):
  one evaluation of `ln` plus a truncated exponential series of the *small* number `x − ln z_j`,
  i.e. `O(k)` multiplications.  *Error*: with `ρ_j = |exp x − z_j|/exp x ≤ 1/2`, Exercise 4.3's
  bound (Lipschitz constant `2/exp x` for `ln` on `[exp x/2, 3exp x/2]`, `abs_log_sub_log_le`, and
  `|exp^{(k)}| ≤ (3/2)exp x` on the relevant interval) gives `ρ_{j+1} ≤ (3·2^{k−1}/k!) ρ_j^k`
  (`expViaLogStep_relative_error`): a `k`-th order iteration, so the precision is multiplied by
  about `k` per step (`−log₂ ρ_{j+1} ≥ k(−log₂ ρ_j) − log₂(3·2^{k−1}/k!)`, and `2^{k−1}/k! < 1` for
  `k ≥ 4`).  *Why Newton alone gives only `∼ 2T(n)`*: with `k = 2` the precisions `n, n/2, n/4, …`
  cost `∑ T(n/2^i) ≈ T(n)(1 + 1/2 + ⋯) = 2T(n)` when `T` is linear, and more precisely
  `≤ T(n)·k/(k−1)` for the factor-`k` schedule under the smoothness `k·T(m/k) ≤ T(m)`
  (`geometric_cost_le`; this holds when `T(m)/m` is nondecreasing).  *The `∼ T(n)` algorithm*: run
  the order-`k` iteration at precisions `n, n/k, n/k², …` down to a constant, starting from a
  double-precision `exp`; the `ln` evaluations cost `≤ T(n)·k/(k−1) = T(n)(1 + 1/(k−1))`, and the
  series steps cost `O(k) M(n_i)` each, in total `O(k M(n))` (same geometric sum).  Choose
  `k = k(n) → ∞` so slowly that `k·M(n) = o(T(n))` — possible because `M(n) = o(T(n))`, e.g.
  `k = ⌊(T(n)/M(n))^{1/2}⌋`; then the total is `T(n)(1 + 1/(k−1)) + o(T(n)) = T(n)(1 + o(1)) ∼ T(n)`.
  The hypothesis `n ≪ M(n)` makes the `O(n)`-bit bookkeeping (truncations, additions) negligible,
  and the smoothness conditions are those used above (`T(m)/m` nondecreasing, the same for `M`).
  Remark: this is exactly the §4.8.4 recipe "`exp` by Newton's method from the complex/real AGM
  logarithm" — with the AGM, `T(n) = O(M(n) log n)`, so `k ≈ √(log n)` already gives `∼ T(n)`.
  Formal content: `Exercises.lean`, section `Exercise46`.
* **Exercise 4.7** (`exp x = exp(x/2^k)^{2^k}`, `x` of order unity, `k` reduction steps: show that
  about `k` bits of precision are lost, so about `k` guard bits are needed).  **Answer.**  Write the
  computed value of the reduced exponential as `exp(x/2^k)(1 + ε)`, `|ε| ≲ 2^{−p}` at working
  precision `p` (series truncation + rounding).  Squaring is *exact* in relative error:
  `(e(1+ε))^2 = e^2(1+ε)^2`, so after `k` squarings the relative error is `(1+ε)^{2^k} − 1`.
  Bernoulli's inequality gives `(1+ε)^{2^k} − 1 ≥ 2^k ε` (`two_pow_mul_le_one_add_pow_sub_one`),
  and conversely `(1+ε)^{2^k} − 1 ≤ e^{2^k ε} − 1 ≤ 2·2^k ε` while `2^k ε ≤ 1`
  (`one_add_pow_sub_one_le_two_mul`): the relative error is multiplied by a factor between `2^k`
  and `2^{k+1}`, i.e. `log₂(1/error)` drops by at least `k` (`logb_one_add_pow_sub_one_ge`:
  `log₂((1+ε)^{2^k} − 1) ≥ k + log₂ ε`) and at most `k + 1` bits — "about `k` bits are lost".  The
  rounding of the squarings themselves adds the same amount: with relative perturbations `θ_i` at
  squaring `i`, §4.3.1's `abs_squareSeq_sub_exp_le` gives the final relative error
  `≤ 2(2^k|ε| + ∑_{i<k} 2^{k−1−i}|θ_i|) ≤ 2(2^k + 2^k − 1)·2^{−p} < 2^{k+2−p}` — the first squaring's
  rounding is amplified `2^{k−1}` times, the last one not at all, and the sum is again `≈ 2^k 2^{−p}`.
  Hence to deliver `n` correct bits one must work with `p ≈ n + k + O(1)` bits: about `k` guard
  bits (the `x` of order unity matters only in that `exp x` itself is of order unity, so relative
  and absolute error agree up to a constant; for `x ≈ 2^j` the same count holds for the relative
  error, cf. Exercise 4.5).  With the optimal `k ≈ √n` of Exercise 4.5 this is `O(√n)` guard bits —
  negligible against `n`, but not against the `O(lg n)` guard bits of the series itself (§4.4).
  Formal content: `Exercises.lean`, section `Exercise47`.
* **Exercise 4.8** (the loss of Exercise 4.7 is avoided with `expm1 x = exp x − 1 = ∑_{j≥1} x^j/j!`
  and its doubling formula `expm1(2x) = expm1 x (2 + expm1 x)`).  **Answer.**  Two effects.
  (1) *Cancellation at the start*: for the reduced argument `r = x/2^k` the series for `exp r` is
  `1 + r + ⋯`, and forming `exp r − 1` from a rounded `exp r` costs the `k` leading bits (absolute
  error `ρ exp r` on a quantity of size `r ≈ 2^{−k}`, §4.3.3's `expm1_of_exp_perturbed`); summing
  the series for `expm1 r` directly (no constant term) keeps the *relative* error at `2^{−p}`.
  (2) *No amplification by the doublings*: writing the computed value as `expm1 r (1 + ε)`, one
  step gives `expm1 (2r)(1 + ε′)` with `ε′ = ε(2(e+1) + eε)/(e+2)`, `e = expm1 r` (§4.3.3's
  `expm1_two_mul_perturbed`), and for `r ≥ 0`, `|ε| ≤ 1`: `|ε′| ≤ |ε|(1 + e)`
  (`abs_expm1_relError_step_le`; the §4.3.3 bound `2|ε| + ε²` is the crude version, the true factor
  is `1 + e/(e+2)·(…) ≈ 1 + e/2`).  Since `e_i = expm1(r 2^i) ≈ x/2^{k−i}` is tiny in the early steps
  and only `≈ expm1 x` at the end, the `k` factors multiply to
  `∏_{i<k}(1 + e_i) ≤ exp(∑ e_i) ≤ exp(x eˣ)` (`prod_one_add_le_exp_sum`, `sum_expm1_two_pow_le`,
  using `expm1 y ≤ y e^y` and `∑ r 2^i ≤ x`): for `x` of order unity a *constant* — e.g. `≤ e^e ≈ 15`
  for `x ≤ 1`, i.e. at most four bits — independent of `k`, against the `2^k` of Exercise 4.7
  (`expm1DoublingSeq_relError`: relative error after `k` exact doublings `≤ |ε| ∏(1 + e_i)`).  The
  reason is structural: squaring `e^x(1+ε)` doubles `ε` because the relative error of a square is
  twice that of its base, whereas `expm1(2y) = e(2 + e)` is *linear* in `e` to first order
  (`2e + e²`), so the relative error passes through essentially unchanged while `e ≪ 1`.  The
  rounding errors `θ_i` of the doubling steps are then also not amplified (each enters with factor
  `∏_{i'>i}(1 + e_{i'}) = O(1)`), so the working precision is `n + O(1)` bits instead of `n + k`.
  Finally `exp x = 1 + expm1 x` with a single addition.  (For `x < 0` use `expm1 x = −expm1(−x)/
  (1 + expm1(−x))`, or `exp x = 1/exp(−x)`, §4.4.)  Formal content: `Exercises.lean`, section
  `Exercise48`.
* **Exercise 4.9** (`log1p` reduction formula). **Answer.** For `x > −1` put `s = √(1+x) > 0`;
  then `x/(1+s) = (s² − 1)/(s + 1) = s − 1`, so `1 + x/(1+s) = s` and
  `2 log1p(x/(1+s)) = 2 ln s = ln s² = ln(1+x) = log1p x` (`log1p_reduction`,
  `div_one_add_sqrt_eq`). Why `log1p`: for tiny `x` (say `|x| < 2^{−n/2}`) the sum `1 + x` is
  rounded to `n` bits before `ln` sees it, so `ln(1+x) = x − x²/2 + …` carries only the bits of
  `x` that survived the rounding, a loss of `−log₂|x|` bits (`relError_sub_one`: perturbing
  `y = 1 + x` by relative `ε` perturbs `y − 1` by relative `ε·y/(y−1)`). Argument reduction for
  `ln` has the same defect: `ln y = 2 ln √y` drives `y → 1`, and anything that then forms
  `√y − 1` (series in `y − 1`, or the AGM input `4/√y`'s complement) cancels. With `log1p` the
  reduction `x ↦ x/(1 + √(1+x)) = √(1+x) − 1` is computed as a *division* with no subtraction:
  the new argument is ≈ `x/2` (`sqrt_sub_one_le_half`), is obtained to full relative precision,
  and the map does not amplify relative errors (`reduced_relError_le`, condition number
  `(1+s)/(2s) ≤ 1` for `x ≥ 0`). After `k` steps the argument is ≈ `x/2^k` and the
  reconstruction `2^k · log1p(r)` is an exact scaling, so (unlike Exercise 4.7's repeated
  squaring) nothing is lost on the way back. Cost: each `expm1` reduction is a halving (free),
  each `log1p` reduction needs a square root of an `n`-bit number, ≈ `O(M(n))`, so `k`
  reductions cost `O(k M(n))` versus `O(k n)`.
* **Exercise 4.10** (`sinh` from one `expm1`). **Answer.** Let `u = expm1 |x| ≥ 0`, so
  `e^{|x|} = 1 + u` and `e^{−|x|} = 1/(1+u)`. Then
  `sinh |x| = ((1+u) − 1/(1+u))/2 = u(2+u)/(2(1+u)) = (u + u/(1+u))/2`, and
  `sinh x = sign(x) · sinh |x|` (`sinh_eq_sinhExpm1`, `sinhExpm1_eq`, `sinh_eq_sign_mul_sinh_abs`).
  Cost beyond the one `expm1`: one division, two additions, one halving (and a sign flip).
  Stability: every intermediate quantity is nonnegative and the only subtraction, the `−1` hidden
  in `expm1`, is done inside `expm1` without cancellation, so for `|x|` small the result
  `≈ u ≈ |x|` keeps full relative precision; the map `u ↦ u(2+u)/(2(1+u))` has condition number
  `1 − u/((1+u)(2+u)) ≤ 1`, so relative errors in `u` are not amplified
  (`sinhExpm1_relError_le`). Taking `|x|` matters: for `x ≪ 0` we would have `u ≈ −1` and
  `1 + u = e^x` would be formed with cancellation. Compared with (4.20),
  `sinh x = (expm1 x − expm1(−x))/2`, which is also cancellation-free but needs two `expm1`
  evaluations, this uses one. `cosh x = 1 + u²/(2(1+u))` comes from the same `u`
  (`cosh_eq_expm1`).
* **Exercise 4.11** (White: `exp` via `sinh`). **Answer.** `cosh² − sinh² = 1` and `cosh > 0`
  give `cosh x = √(1 + sinh² x)`, so `exp x = sinh x + cosh x = sinh x + √(1 + sinh² x)`
  (`exp_eq_sinh_add_sqrt`). The odd part of the exponential series is
  `sinh x = ∑_{k≥0} x^{2k+1}/(2k+1)! = x ∑_k (x²)^k/(2k+1)!` (`hasSum_sinh_series`,
  `hasSum_sinh_series'`): a series in `x²` with the same convergence rate as the full series, so
  about half the terms (and half the multiplications, after one squaring) for the price of one
  square root, which is `O(M(n))`, i.e. a constant number of terms' worth of work. Negative
  arguments: for `x < 0`, `sinh x < 0` and `sinh x + √(1 + sinh² x) = 1/(|sinh x| + √(1 + sinh² x))`
  is a difference of nearly equal numbers (`sqrt_sub_eq_inv`), losing about `−2x/ln 2` bits for
  `x ≪ 0`; so compute with `|x|` and invert: `exp x = 1/(sinh |x| + √(1 + sinh² |x|))`
  (`exp_eq_inv_sinh_abs_add_sqrt`), where every term is nonnegative and the map
  `s ↦ s + √(1 + s²)` has relative condition number `s/√(1 + s²) ≤ 1`
  (`sinh_add_sqrt_relError_le`). Other functions: the same trick works whenever the even and odd
  parts `f_e, f_o` of `f` are related algebraically. `cos x = √(1 − sin² x)` on `[−π/2, π/2]`
  (Mathlib `Real.cos_eq_sqrt_one_sub_sin_sq`; use `cos x = 1 − 2 sin²(x/2)` to avoid the loss near
  `|x| = π/2`), so `exp(ix) = cos x + i sin x` needs only the `sin` series; likewise
  `exp x = (1 + tanh(x/2))/(1 − tanh(x/2))` (`exp_eq_tanh_half`) uses only the odd function
  `tanh`, whose (Bernoulli-number) series is however less convenient than `sinh`'s;
  `cosh x = 1 + 2 sinh²(x/2)` and `ln(1+x)`/`artanh` via `artanh y = ½ ln((1+y)/(1−y))`, whose
  series `∑ y^{2k+1}/(2k+1)` is again odd (§4.4.2's `(1+x)/(1−x)` reduction), are the same
  idea.
* **Exercise 4.12** (precise non-scalar counts for §4.4.3). **Answer.** Count non-scalar products
  by writing both algorithms in a small cost-counting monad (`Counted`: a value plus the numbers
  of general products and of squarings; scalar products and additions are free) and reading the
  cost off the computation. *Classical* (`d = jk`, `y = x^k`): the table `x², …, x^k` costs
  `k − 1` products, of which the `⌊k/2⌋` even powers are squarings and `⌈k/2⌉ − 1` are general
  products; the inner polynomials are scalar; Horner in `y` over the `j` inner values costs
  `j − 1` general products (the top coefficient is multiplied directly). Total `j + k − 2`
  (`classicalEvalC_total`, `classicalEvalC_mul`, `classicalEvalC_sq`). *Modular* (`y = x^j`):
  `y` by binary powering costs `⌊log₂ j⌋` squarings and `popcount(j) − 1` general products, i.e.
  `ℓ(j) = ⌊log₂ j⌋ + popcount(j) − 1` in all (`binPowC_sq`, `binPowC_mul`), never more than the
  `j − 1` of repeated multiplication (`log_add_digits_sum_le`) and at most `2⌊log₂ j⌋`
  (`digits_sum_le_log_add_one`); the table `y², …, y^{k−1}` costs `k − 2` (`⌊(k−1)/2⌋` squarings,
  `⌈(k−1)/2⌉ − 1` products); the row sums are scalar; Horner in `x` over the `j` rows costs `j − 1`.
  Total `j + k − 3 + ℓ(j)` (`modularEvalC_total`), i.e. `ℓ(j) − 1 = O(log d)` more than classical,
  which is the "almost the same" of §4.4.3; with naive powering of `x^j` it would be
  `2j + k − 4 = modularNonscalar j k` (`modularEvalC_total_le`). Example `d = 12 = 3·4`:
  classical `5` (`x³`; `x², x⁴` squarings; two Horner products), modular `6` (`x³`: one squaring,
  one product; `y², y³`: one squaring, one product; two Horner products) (`splitting_example`).
  Optimizing: classical is minimized at `j ≈ k ≈ √d`, giving `2√d − 2`; modular at the same
  balance gives `2√d − 3 + ℓ(√d) ≈ 2√d + log₂ d`. Both evaluations are proven to compute
  `polyEval a (jk) x` (`classicalEvalC_val`, `modularEvalC_val`).
* **Exercise 4.13** (large coefficients in rectangular splitting). **Answer.** For `exp`,
  `a_i = 1/i!` has `log₂ i! ≈ i log₂ i` bits, so the scalar products `a_{kℓ+m} · x^m` of §4.4.3
  are really `n`-bit by `O(d log d)`-bit products, not `O(n)` operations. Instead use the ratios
  `r_i = a_{i+1}/a_i` (for `exp`, `1/(i+1)`), which have `O(log d)` bits. Within a block of the
  classical splitting write `a_{kℓ+m} = a_{kℓ} ∏_{i<m} r_{kℓ+i}` and evaluate the inner
  polynomial by Horner's rule *in the ratio direction*, with the stored powers of `x` playing the
  role of the coefficients:
  `P_ℓ(x)/a_{kℓ} = x⁰ + r_{kℓ}(x¹ + r_{kℓ+1}(x² + ⋯ + r_{kℓ+k−2} x^{k−1}))`
  (`ratioHorner`, `ratioHorner_eq`, `innerPoly_eq_ratioHorner`). Each step is one multiplication
  by a small numerator, one division by a small denominator and one addition, all `O(n)`; no
  multiplication by `x` occurs, so nothing non-scalar is added. The outer Horner in `y = x^k`
  then needs `a_{k(ℓ+1)}/a_{kℓ} = ∏_{i<k} r_{kℓ+i}`, a product of `k` small ratios, applied either
  as one `O(k log d)`-bit scalar or as `k` small scalar steps (`O(kn)` per block, `O(dn)` in all):
  `P(x) = a_0 [U_0 + y R_0 (U_1 + y R_1 (U_2 + ⋯))]` (`scaledHornerC`). The complete scheme
  (`ratioEvalC`) is proven to compute `P(x)` whenever `a_{i+1} = r_i a_i` (`ratioEvalC_val`) and
  uses exactly the non-scalar products of the classical splitting (`ratioEvalC_mul`,
  `ratioEvalC_sq`), so the §4.4.3 cost model `O(√d M(n) + dn)` is restored with every scalar
  multiplier of `O(log d)` bits. The classical splitting is the right one for this: consecutive
  coefficients share a block, whereas in the modular splitting the row `S_ℓ = ∑_m a_{jm+ℓ} y^m`
  links coefficients `j` apart, whose ratios are `j`-fold products of `O(j log d)` bits. For
  integer-only arithmetic, clear the `k − 1` denominators of a block at once: the integer
  coefficients then have `O(k log d)` bits, the compromise of Smith's and Johansson's
  implementations. Design note for `AzFloat` `exp`: inner sums as `AzNat`-scaled `AzFloat`
  values with `AzNat` small-divisor steps; `a_0 = 1`.
* **Exercise 4.14** (explicit `c(d)`). **Answer.** A scalar product multiplies an `n`-bit number by
  a coefficient of `b` bits; with word size `w` it costs `(n/w) · ⌈b/w⌉` word products, so
  `c(d) = ⌈b/w⌉` with `b` the bit size of the largest multiplier (`wordsOf`). With the ratio
  scheme of Exercise 4.13 the multipliers are the numerators and denominators of the ratios, for
  `exp` the integers `i + 1 ≤ d`, of `size(d) = ⌊log₂ d⌋ + 1` bits (`ratio_multiplier_size`), so
  `c(d) = ⌈size(d)/w⌉` (`ratioScalarWords`), which is `1` whenever `d < 2^w`
  (`ratioScalarWords_eq_one`): `c(d) = 1` for every term count that fits a 64-bit word, and
  `O(log d)` in bit-operation terms. Divisions by the small denominators cost the same as the
  multiplications. For a general hypergeometric ratio `p(i)/q(i)` with `deg p, deg q ≤ δ` and
  `O(1)`-bit polynomial coefficients, `b = O(δ log d)`, so `c(d) = O(δ log d / w)`; with a block's
  `k − 1` denominators cleared at once, `b = O(k log d)` and `c(d) = O(√d log d / w)`. Without
  ratios, the coefficient `1/d!` of the exponential series has
  `(d/2) log₂(d/2 + 1) < size(d!) ≤ d (log₂ d + 1)` bits (`size_factorial_gt`,
  `size_factorial_le`), i.e. `c(d) = Θ(d log d / w)` (`naiveScalarWords`), turning the `O(dn)`
  scalar term of (4.24) into `O(d² n log d / w)`, which is the problem Exercise 4.13 removes.
* **Exercise 4.15** (the remainder (4.28) of (4.27)). **Answer.** Write
  `I_k(x) = ∫_x^∞ e^{−u}/u^{k+1} du` (`expTail k x`), so `E₁(x) = I_0(x)`. Integration by parts
  with `u ↦ u^{−(k+1)}` and `u ↦ −e^{−u}` gives
  `I_k(x) = [−e^{−u}/u^{k+1}]_x^∞ − (k+1) ∫_x^∞ e^{−u}/u^{k+2} du = e^{−x}/x^{k+1} − (k+1) I_{k+1}(x)`
  (`expTail_succ`; the boundary term at `∞` vanishes since `e^{−u}/u^{k+1} ≤ e^{−u}/x^{k+1} → 0`).
  Multiplying by `k!(−1)^k e^x`: `R_k(x) = k!(−1)^k/x^{k+1} + R_{k+1}(x)`, i.e. `R_k = t_{k+1} + R_{k+1}`
  with `t_{j} = (j−1)!(−1)^{j−1}/x^j` the `j`-th term of (4.27) (`asymptoticRemainder_succ`).
  Induction on `k`: for `k = 0`, `R_0 = e^x E₁(x)` is (4.27) with an empty sum; if
  `e^x E₁(x) = ∑_{j=1}^k t_j + R_k`, then the step gives `∑_{j=1}^{k+1} t_j + R_{k+1}`
  (`exp_mul_expIntegral_eq`, text indexing `exp_mul_expIntegral_eq_text`). The bound: `I_{k+1} > 0`
  (positive integrand on a set of infinite measure, `expTail_pos`), so the parts formula gives
  `I_k(x) < e^{−x}/x^{k+1}` (`expTail_lt`) and `|R_k(x)| = k! e^x I_k(x) < k!/x^{k+1}`
  (`abs_asymptoticRemainder_lt`), the strict inequality of (4.28); the sign of `R_k` is `(−1)^k`
  (`sign_asymptoticRemainder`), so the value lies strictly between consecutive partial sums
  (`between_partialSums`). All of this was already in `AsymptoticExpansion.lean` from the §4.5
  chunk except the text indexing and the strict `<`, added in `Exercises.lean`.
* **Exercise 4.16** (`Ei` and `E₁` via the entire function `Ein`). **Answer.** Define
  `Ein z = ∑_{j≥1} (−1)^{j−1} z^j/(j! j)`. The terms are dominated by `|z|^j/j!`, so the series
  converges for every complex `z` (`summable_EinTerm`), and differentiating termwise (justified on
  every disc by the summable bound `R^n/n!`, `hasDerivAt_tsum_of_isPreconnected`) gives
  `Ein'(z) = ∑_{n≥0} (−1)^n z^n/(n+1)! = (1 − e^{−z})/z` with `Ein'(0) = 1` (`hasDerivAt_Ein`,
  `hasSum_EinDerivTerm`): `Ein` is entire, and since `Ein(0) = 0` it is the integral
  `∫_0^z (1 − e^{−t})/t dt` of an entire integrand along any path (`EinR_eq_integral` proves the
  real case `x ≥ 0` directly: the integrand is bounded by `1` on `(0, x]`, both sides vanish at `0`
  and have the same derivative on `(0, ∞)`). `Ein` is real on the real axis (`Ein_ofReal`). Now set
  `E₁(z) := −γ − Log z + Ein z` (`E1Ein`) and `Ei(x) := γ + ln|x| − Ein(−x)` (`EiEin`). These are
  (4.26) and its `Ei` analogue read as definitions. Checks: `E₁'(z) = −1/z + (1 − e^{−z})/z = −e^{−z}/z`
  off the branch cut of `Log` (`hasDerivAt_E1Ein`), which is the derivative of `∫_z^∞ e^{−u}/u du`,
  and `E₁(x) → 0` as `x → +∞` fixes the constant `−γ` (that identification is (4.26), still not
  formalized); `Ei'(x) = 1/x + (1 − e^{x})/x = e^x/x` for every `x ≠ 0` (`hasDerivAt_EiEin`), the
  integrand of `∫_{−∞}^x e^t/t dt`. So `Ei` is the antiderivative of `e^x/x` on `(−∞, 0)` that
  vanishes at `−∞` (there it equals `−E₁(−x)`), continued through the pole at `0` by the same
  formula: the principal value `PV ∫_{−∞}^x e^t/t dt` for `x > 0` is exactly what the formula
  `γ + ln x − Ein(−x)` produces, because `ln|x|` is itself the principal-value primitive of `1/x`
  across `0`, and `e^t/t − 1/t = (e^t − 1)/t` is entire so needs no principal value. Hence neither
  `Ei` nor `E₁` needs a PV integral: all singular behaviour sits in `Log`/`ln|·|`, and the only
  branch cut of `E₁` is that of `Log`. For complex `z`, `Ei(z) = γ + Log z − Ein(−z)` likewise,
  with `Ei(z) = −E₁(−z) ∓ iπ` across the cut.
* **Exercise 4.17** (`1/x − 1/x² < e^x E₁(x) < 1/x`). **Answer.** Take `k = 1` in (4.27):
  `e^x E₁(x) = 1/x + R₁(x)` with `R₁(x) = −e^x ∫_x^∞ e^{−u}/u² du`. The integral is positive, so
  `R₁ < 0`, giving the upper bound; and `|R₁(x)| < 1!/x² = 1/x²` (Exercise 4.15, strict), giving
  the lower bound. Equivalently, `k = 2` gives `e^x E₁(x) = 1/x − 1/x² + R₂` with `R₂ > 0`. The
  two bounds are the partial sums with one and two terms, between which the value lies
  (`between_partialSums`). Formalized as `exp_mul_expIntegral_bounds`.
* **Exercise 4.18** (`S(z) = e^z s(z)` for the binomial transform). **Answer.** Compare
  coefficients of `z^n`: in `e^z s(z) = (∑_k z^k/k!)(∑_j a_j z^j/j!)` the coefficient is
  `∑_{j+k=n} a_j/(j! k!) = (1/n!) ∑_{j≤n} (n!/(j!(n−j)!)) a_j = (1/n!) ∑_{j≤n} C(n,j) a_j = A_n/n!`,
  which is the coefficient of `S`. Formalized over any `ℚ`-algebra with Mathlib's
  `PowerSeries.exp` (`egf`, `binomialTransform`, `egf_binomialTransform`, via `coeff_mul` on the
  antidiagonal and `Nat.cast_choose`). Inverse: multiplying by `e^{−z}` (`exp_mul_exp_neg_eq_one`)
  gives `s(z) = e^{−z} S(z)` (`egf_eq_exp_neg_mul`), i.e. `a_n = ∑_{j≤n} (−1)^{n−j} C(n,j) A_j`.
  Used in Exercises 4.19–4.20 (series for `E₁`/`Ei` and related sums).
* **Exercise 4.19** (cancellation-free series `e^z Ein(z) = ∑_{j≥1} H_j z^j/j!`). **Answer.**
  `Ein` is the exponential generating function of `a_0 = 0`, `a_j = (−1)^{j−1}/j`. By Exercise
  4.18, `e^z Ein(z)` is the e.g.f. of the binomial transform `A_n = ∑_{j=1}^n C(n,j)(−1)^{j−1}/j`,
  and `A_n = H_n`: by induction, `A_{n+1} − A_n = ∑_{l≤n} C(n,l)(−1)^l/(l+1)` (Pascal's rule, the
  `C(n,n+1) = 0` term dropping out) `= (1/(n+1)) ∑_{l≤n} C(n+1,l+1)(−1)^l = (1/(n+1))(1 − (1−1)^{n+1})
  = 1/(n+1)` using `C(n,l)/(l+1) = C(n+1,l+1)/(n+1)` (`choose_div_succ_eq`,
  `sum_choose_alt_div_succ`, `sum_choose_alt_div_eq_harmonic`). Formally `exp · egf a = egf H`
  (`exp_mul_egf_ein`); analytically both series converge absolutely everywhere (`H_j ≤ j`,
  `harmonic_le_self`), so the Cauchy product gives `e^z Ein(z) = ∑_{j≥1} H_j z^j/j!` for every
  complex `z` (`hasSum_exp_mul_Ein`, via `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
  and the coefficient identity `sum_antidiagonal_exp_EinTerm`). Why it helps: for `z = x ≫ 0` the
  terms `(−1)^{j−1} x^j/(j! j)` of `Ein` alternate and peak near `j ≈ x` at size `≈ e^x/x^{3/2}`,
  while `Ein(x) ≈ ln x + γ`, so about `x/ln 2` bits cancel, exactly as in the series for `e^{−x}`;
  the new series has positive terms, its sum `e^x Ein(x)` is of the size of its largest term, and
  `Ein(x) = e^{−x} ∑ H_j x^j/j!` is then obtained to full relative precision with one
  exponential. For `x < 0` the original series already has positive terms and the new one would
  cancel, so choose by sign. (For `E₁(x) = Ein(x) − γ − ln x` at large `x` the subtraction itself
  cancels; there (4.27) is the right tool, as §4.5 says; this series is for moderate `x`.)
* **Exercise 4.20** ((4.23) from (4.22)). **Answer.** Put `t = x²`. By (4.22),
  `erf(x) = (2/√π) x ∑_j (−1)^j t^j/(j!(2j+1))`, i.e. `(√π/2) erf(x)/x` is the exponential
  generating function of `a_j = (−1)^j/(2j+1)`. By Exercise 4.18, `e^t` times it is the e.g.f. of
  `A_n = ∑_{j≤n} C(n,j)(−1)^j/(2j+1)`. This is `∫_0^1 (1−u²)^n du`; in closed form, for the
  general sum `C_n(s) = ∑_j C(n,j)(−1)^j/(2j+s)` Pascal's rule gives `C_{n+1}(s) = C_n(s) − C_n(s+2)`
  (`altOddSum_succ`), and induction yields `C_n(s) = 2^n n!/(s(s+2)⋯(s+2n))` (`altOddSum_eq`),
  so `A_n = C_n(1) = 2^n n!/(1·3⋯(2n+1)) = 2^n n!/(2n+1)‼` (`altOddSum_one`,
  `prod_odd_eq_doubleFactorial`). Hence `e^{x²} (√π/2) erf(x)/x = ∑_n 2^n t^n/(2n+1)‼`, which is
  (4.23): `erf(x) = (2/√π) e^{−x²} ∑_n 2^n x^{2n+1}/(2n+1)‼` (`exp_mul_egf_erf` formally;
  analytically `erf_eq_exp_mul_erfExpSum'` by the Cauchy product of (4.22) with the series of
  `e^{x²}`, both absolutely convergent, coefficient identity `sum_antidiagonal_erf_exp`). This
  reproves `erf_eq_exp_mul_erfExpSum` of `ErrorFunctionSeries.lean`, which used the differential
  equation `S' = 1 + 2xS` instead. As in Exercise 4.19, (4.23) has positive terms for `x > 0`
  while (4.22) alternates and cancels about `x²/ln 2` bits for large `x`.
* **Exercise 4.21** (`Γ(x)` for real `x ≥ 1/2` with relative error `O(2^{−n})`). **Answer.**
  *Algorithm.* Working precision `p = n + O(log n)` bits.
  (1) Shift: pick the integer `δ = ⌈n ln 2/(2π)⌉ + c` (so `x' = x + δ ≳ 0.11 n`; `c` a small
  constant absorbing the `ln(2π²x')` term) and set `x' = x + δ`.
  (2) Stirling: `L = (x' − 1/2) ln x' − x' + ln(2π)/2 + ∑_{k=1}^{m−1} B_{2k}/(2k(2k−1)x'^{2k−1})`
  with `m ≈ πx'` (stop at the smallest term, whose size is `≈ e^{−2πx'} ≤ 2^{−n}`); the sum is a
  polynomial in `1/x'²` evaluated by Horner from the top, using the Bernoulli numbers `B_2, …,
  B_{2m}` (§4.7.2) to `p` bits.
  (3) Product: `P = ∏_{i<δ} (x + i)` by `δ − 1` multiplications (or a product tree).
  (4) `Γ(x) = e^L / P`.
  *Correctness.* Exactly, `Γ(x) = e^{L+R}/P` where `R = R_m(x')` is the remainder of (4.38)
  (`Gamma_eq_exp_stirling_div`, from `Γ(x+δ) = Γ(x) ∏(x+i)`). Dropping `R` with `|R| ≤ ε ≤ 1`
  gives relative error `≤ 2ε` (`Gamma_stirling_relError`, via `|e^{−R} − 1| ≤ 2|R|`); by the
  remainder bound of (4.38) (first omitted term, not formalized) `|R| ≤ |t_m(x')| ≈ e^{−2πx'}`,
  and the shift makes this `≤ 2^{−n−1}`. Rounding: each term of `L` is `O(1)` and the leading
  terms are `O(x' ln x') = O(n log n)`, so `p`-bit arithmetic gives absolute error `O(n log n ·
  2^{−p})` in `L`, hence the same relative error in `e^L`; the `δ` factors of `P` rounded to
  relative `η = 2^{−p}` give relative error `≤ e^{δη} − 1 ≈ δ 2^{−p}` (`abs_prod_one_add_sub_one_le`,
  two-sided via `(1−η)^δ ≥ 1 − δη` and `(1+η)^δ ≤ e^{δη}`); with `p = n + 2 log₂ n + O(1)` the
  total is `O(2^{−n})`. The shift is also necessary: no term of (4.38) at `x'` is below
  `e^{−2πx'}/(2π²x')` (`abs_stirlingTerm_ge`), so accuracy `2^{−n}` forces
  `2πx' + ln(2π²x') ≥ n ln 2` (`shift_necessary`), i.e. `δ ≥ n ln 2/(2π) − x − O(log n)`.
  `x ≥ 1/2` keeps `x > 0` so all factors `x + i` are positive and the logarithms are real; for
  `0 < x < 1/2` one could use the same formula, and for `x < 0` the reflection formula.
  *Complexity.* `m ≈ πx' ≈ (ln 2/2) n ≈ 0.35 n` Horner steps and `δ ≈ 0.11 n` product
  multiplications, each an `n`-bit multiplication: `O(n M(n))`, plus `O(M(n) log n)` for `ln x'`,
  `e^L` and `ln(2π)`. The Bernoulli numbers `B_2..B_{2m}` do not depend on `x`: they can be
  precomputed and cached, or computed by Algorithm TangentNumbers / the recurrence of §4.7.2 in
  `O(m²)` integer operations on `O(m log m)`-bit integers (`O(n³ log n)` naive bit cost, which
  then dominates; via the zeta values `B_{2k} = (−1)^{k+1} 2(2k)! ζ(2k)/(2π)^{2k}` for the large
  `k`, where `ζ(2k) = 1 + O(4^{−k})` needs `O(n/k)` terms, `O(n M(n) log n)`). Hence `Γ(x)` costs
  `O(n M(n)) = O(n^{2+ε})` once the Bernoulli numbers are available, not quasi-linear: unlike
  `exp`, `ln`, `π` (§4.8) no `O(M(n) log^{O(1)} n)` algorithm for `Γ` at general real `x` is known
  (it is known only for special arguments such as `Γ(1/4)`, through elliptic integrals and the
  AGM). The rectangular splitting of §4.4.3 does not help here: the coefficients
  `B_{2k}/(2k(2k−1))` are `O(k log k)`-bit rationals whose ratios are not small (they involve
  `ζ(2k+2)/ζ(2k)`), so the scalar products are full `n`-bit multiplications.
* **Exercise 4.22** (`1/Γ(z)` on `ℂ` with relative error `O(2^{−n})`). **Answer.**
  *Algorithm* (working precision `p = n + O(log(n + |z|))` bits). (0) If `Re z < 1/2`, use the
  reflection formula `1/Γ(z) = Γ(1 − z) sin(πz)/π` (`inv_Gamma_eq_Gamma_one_sub_mul_sin`): then
  `Re(1 − z) > 1/2`, `Γ(1 − z)` is computed by steps (1)–(3) below as `e^{L}`, and `sin(πz)` by
  the complex sine (for `|Im z|` large, `sin(πz) ≈ ∓ e^{π|Im z|}/(2i)`, computed from the
  exponential with relative precision; the exact zeros at integers come out exactly since
  `sin(πk)` is evaluated after reducing `z` modulo the integers, or simply because `z` integer is
  detected and `1/Γ(k) = 1/(k−1)!`). (1) Shift: `δ = max(0, ⌈c·n − Re z⌉)` with `c ≈ 0.17`, so that
  `z' = z + δ` has `Re z' ≥ 0` and `|z'| ≥ c n`; then `1/Γ(z) = (∏_{i<δ} (z + i)) · (1/Γ(z'))`,
  an identity between entire functions valid for every `z`, poles included: at `z = −k`, `k < δ`,
  the factor `z + k` is exactly `0` (`inv_Gamma_eq_prod_mul_inv_Gamma_add`, by induction from
  Mathlib's `1/Γ(s) = s/Γ(s+1)`). (2) `L = ln Γ(z')` by the complex Stirling series (4.38) with
  `m ≈ π|z'|` terms and the principal `Log z'`. (3) `1/Γ(z) = P · e^{−L}` with `P = ∏(z + i)`.
  *Correctness.* The exact identity is `1/Γ(z) = P e^{−L−R}` with `R` the complex remainder of
  (4.38); for `Re z' ≥ 0` the classical bound is `|R_m(z')| ≤ |t_m(z')| / cos^{2m}(arg z'/2)`
  (not formalized), and with `|arg z'| ≤ π/2` the factor `sec^{2m}(π/4) = 2^m` is beaten by the
  smallest term `≈ e^{−2π|z'|}` at `m ≈ π|z'|` (net `≈ e^{−(2π − π ln 2)|z'|} = e^{−4.1|z'|}`),
  hence the constant `c = ln 2/4.1 ≈ 0.17` in the shift. An error `ε ≤ 1` in `L` (remainder plus
  rounding) gives relative error `≤ 2ε` in `P e^{−L}` (`inv_Gamma_approx_relError`, via
  `‖e^w − 1‖ ≤ 2‖w‖`); `L` has size `O(|z'| ln|z'|)`, so `p` must carry `log₂(|z'| ln |z'|)` guard
  bits; the `δ` complex factors of `P` rounded to relative `η` give relative error
  `≤ e^{δη} − 1` (`norm_prod_one_add_sub_one_le`, from `‖∏(1+e_i) − 1‖ ≤ ∏(1+‖e_i‖) − 1`,
  `norm_prod_one_add_sub_one_le_prod`). Relative error is the right notion here because `1/Γ` is
  entire with zeros: near a zero `−k` the result is small but is `P e^{−L}` with `P` containing the
  exactly-rounded small factor `z + k`, so no cancellation occurs.
  *The warning.* `|Γ(z)|` is tiny for large `|Im z|`: exactly, `Γ(iy)Γ(−iy) = π/(y sinh(πy))`
  (`Gamma_I_mul_mul_Gamma_neg`, from `Γ(1 − iy) = −iy Γ(−iy)` and the reflection formula with
  `sin(iπy) = i sinh(πy)`), so `|Γ(iy)|² = π/(y sinh(πy))` (`norm_Gamma_I_mul_sq`, using
  `Γ(conj z) = conj Γ(z)`), which is `≤ 4π e^{−πy}/y` for `πy ≥ 1` (`norm_Gamma_I_mul_sq_le`):
  `2 ln|Γ(iy)| ≈ −π|y|`. Likewise `|Γ(1/2 + iy)|² = π/cosh(πy)` (`norm_Gamma_half_add_I_mul_sq`),
  and `|Γ(1 + iy)|² = πy/sinh(πy)`; these are the cases `x = 0, 1/2, 1` of the text's
  `|Γ(x+iy)|² ≈ 2π|y|^{2x−1} e^{−π|y|}`, which in general follows from Stirling
  (`Re ln Γ(x+iy) = (x − 1/2) ln|z| − y arg z − x + ln(2π)/2 + o(1)` with `arg z → ±π/2`). The
  consequence for the algorithm: `1/Γ(z)` is huge (`≈ e^{π|y|/2}`), so an absolute-error target is
  meaningless and a fixed-point or small-exponent format would overflow; in the logarithmic form
  `P e^{−L}` the size sits in `Re L ≈ −π|y|/2`, the exponential handles it exactly through the
  exponent, and the relative error is `2ε` as above. The complexity is as in Exercise 4.21,
  `O(n M(n))` with complex arithmetic (a constant factor `3`–`4`), plus the `O(M(n) log n)` of one
  complex `Log`, one `exp` and (for `Re z < 1/2`) one `sin`.
* **Exercise 4.23** (the convergent Stirling series (4.88) is no improvement). **Answer.**
  Write `t_k(z) = c_k/((z+1)⋯(z+k))`. *Size of the coefficients.* Since
  `∑_j |s(k,j)| x^j = x(x+1)⋯(x+k−1)` (`sum_stirling1_mul_pow`, from the three-term recurrence
  `|s(n+1,j+1)| = |s(n,j)| + n|s(n,j+1)|`), `∑_j |s(k,j)| = k!` (`sum_stirling1`), and as
  `j/((j+1)(j+2)) ≥ 1/(2(k+2))` for `1 ≤ j ≤ k`, `c_k ≥ k!/(4k(k+2))` (`stirlingC_ge`); in fact
  `1/((j+1)(j+2)) = ∫_0^1 x^j(1−x) dx` gives `c_k = (1/2k) ∫_0^1 x(1−x) (x(x+1)⋯(x+k−1))' dx
  ≈ (k−1)!/(2 ln k)`. So the `c_k` are as large as the Bernoulli numbers (`O(k log k)` bits) and
  the recurrence for the `|s(k,j)|`, `k ≤ K`, costs `O(K²)` additions of such integers, the same
  order as computing `B_2, …, B_{2K}`; nothing is gained on the coefficient side.
  *Rate of convergence.* `t_{k+1}/t_k = (c_{k+1}/c_k)/(z+k+1) ≈ k/(z+k+1)`: the terms shrink
  geometrically only while `k ≪ z` (about one bit per term up to `k ≈ z/2`, giving
  `t_{z/2} ≈ (2e)^{−z/2} ≈ e^{−0.85 z}`), and for `k ≳ z` they decay like `Γ(z+1)/(2k^{z+1} ln k)`,
  a power law. Rigorously, at an integer `z = N` and for `1 ≤ K ≤ N`,
  `t_K(N) ≥ (K!/(4K(K+2)))/(2N)^K ≥ (K/(2eN))^K/(4K(K+2)) ≥ e^{−2N}/(4K(K+2))`
  (`convergentTerm_ge`, using `K! ≥ (K/e)^K` and `K ln(2eN/K) ≤ 2N`, `pow_div_ge_exp_neg`),
  whereas the divergent series (4.38) at the same `N` reaches the floor `e^{−2πN}` with `⌈πN⌉`
  terms (`abs_stirlingTerm_ge`, §4.5); since `4N(N+2) < e^{4N} ≤ e^{(2π−2)N}`,
  `t_K(N) > e^{−2πN}` for every `K ≤ N` (`convergentTerm_gt_stirling_floor`): with as many terms
  as the argument, the convergent series has not even reached the accuracy the divergent one
  attains with `πN` terms. Pushing the general estimate: with `K ≤ aN` terms,
  `t_K(N) ≳ e^{−N(1 + ln(1+a))}/(4K(K+2))`, which stays above `e^{−2πN}` until
  `1 + ln(1+a) ≥ 2π`, i.e. `a ≈ e^{2π−1} − 1 ≈ 196`: matching the accuracy `2^{−n}` of
  Exercise 4.21 at the same shifted argument `z' ≈ 0.11n` would take `≈ 200 z' ≈ 22n` terms
  instead of `πz' ≈ 0.35n`; alternatively one can enlarge the shift so that `K ≈ z'/2` terms
  suffice (`e^{−0.85 z'} ≤ 2^{−n}`, `z' ≈ 0.8n`), which multiplies the shift and the product
  `∏(z+i)` by `7`. Either way the cost is a constant factor larger, with the same `O(n M(n))`
  order and the same kind of coefficients, so (4.88) is not an improvement; its only merit is
  that the truncation error is a genuine tail of a convergent series rather than an asymptotic
  remainder estimate. (The identity (4.88) itself is not formalized; only its terms are
  analysed.)
* **Exercise 4.24** (`E₁(x)` to high precision, four methods; **PLAN ONLY**, 2026-10-18, nothing
  implemented). Target: `AzFloat` `expIntegralPrecRound (x : AzFloat) (p) (mode) : AzFloat × Ordering`
  for `x > 0` with *relative* error `≤ 2^{−p}` (so absolute error `≈ 2^{−p} e^{−x}/x` for large `x`),
  in the Ziv `(value, Ordering)` style of the existing operations, with a dispatcher choosing among
  four kernels by `(x, p)`.
  *Prerequisites (missing today).* `AzFloat` has only algebraic constants (`√2`, `φ`, …): the
  kernels need `exp`, `ln` and the constant `γ` as `AzFloat` operations, none of which exist yet;
  `exp`/`ln` are the subject of §4.3–§4.4 (argument reduction + rectangular splitting with the
  ratio scheme of Ex. 4.13, or the AGM of §4.8), and `γ` needs its own algorithm (Brent–McMillan
  via Bessel functions, or the `E₁` relation itself at a convenient point) — plan them first; (b)
  and (d) only need `exp`.
  *(a) Power series (4.26).* `E₁(x) = −γ − ln x + ∑_{j≥1} (−1)^{j−1} x^j/(j! j)`. Alternating terms
  peaking near `j ≈ x` at size `≈ e^x/x^{3/2}` against a sum `≈ ln x + γ`: `≈ x/ln 2` bits cancel in
  the sum, and the final subtraction `Ein(x) − γ − ln x` (result `≈ e^{−x}/x`) cancels another
  `x/ln 2 + log₂ x` bits when relative precision is required, so work at `p' = p + 2x/ln 2 +
  O(log(p + x))` bits; terms until `x^j/(j! j) < 2^{−p'}`, `j ≈ e x + p'/log₂(p'/(ex))`, each a
  scalar step `t_j = t_{j−1} · x/j` (one `p'`-bit multiplication by `x` — non-scalar — and a small
  division) plus the running sum; `O((x + p/log p) M(p + 3x))`. Rectangular splitting (§4.4.3 with
  Ex. 4.13 ratios `r_j = −x·j/((j+1)²)`… the ratio `a_{j+1}/a_j = −j/((j+1)²)` is a small rational, so
  the ratio-Horner scheme applies and cuts the non-scalar count to `O(√d)`). Region: small `x`
  (`x ≲ 1`), where the extra precision is negligible and no `e^{−x}` is needed.
  *(c) Exercise 4.19.* `E₁(x) = e^{−x} ∑_{j≥1} H_j x^j/j! − γ − ln x`: positive terms, so no
  cancellation in the sum; `H_j` by `H_j = H_{j−1} + 1/j` in floating point (relative errors only
  add); still the final subtraction costs `x/ln 2 + log₂ x` extra bits for relative precision, so
  `p' = p + x/ln 2 + O(log)`, half of (a)'s surplus; terms until `H_j x^j/j! e^{−x} < 2^{−p'}`,
  `j ≈ e x + p'/log₂(p'/(ex))`; one `exp` of `−x`. Ratio `a_{j+1}/a_j = H_{j+1}/((j+1) H_j)` is not a
  small rational, so plain Horner/forward summation, `O((x + p/log p) M(p + 1.5x))`. Region:
  `1 ≲ x ≲ c₁ p` (expected `c₁ ≈ 0.1`), always preferable to (a) except for tiny `x`.
  *(b) Asymptotic expansion (4.27).* `e^x E₁(x) = ∑_{j<k} (−1)^j j!/x^{j+1} + R_k`,
  `|R_k| < k!/x^{k+1}` (`abs_asymptoticRemainder_lt`), terms decreasing while `j < x`, smallest
  `≈ √(2π/x) e^{−x}` (4.30): relative precision `2^{−p}` attainable iff `x > p ln 2 + ½ log₂(2πx) +
  O(1)` (`abs_asymptoticRemainder_self_le`, `shift_necessary`-style). Terms by `t_j = t_{j−1} · j · x⁻¹`
  with `x⁻¹` precomputed: one `p`-bit multiplication each, no cancellation (alternating with
  decreasing terms, sum `≈ t_0`), stop at the first `j` with `t_j < 2^{−p} t_0`, i.e. `k ≈ x` near the
  threshold and `k ≈ p ln 2/ln(x/(p ln 2))` far above it; certified bracket from
  `between_partialSums` (value strictly between consecutive partial sums). Cost `O(k M(p))`, plus one
  `exp(−x)`. Region: `x > ln 2 · p` (plus the `½ log₂ x` margin); below it the method cannot reach
  the precision and is skipped.
  *(d) Continued fraction (4.39).* `e^x E₁(x) = 1/x+ 1/1+ 1/x+ 2/1+ 2/x+ 3/1+ ⋯` (`eulerNum`,
  `eulerDen`; all `a_j, b_j > 0`). Convergence of the `k`-th approximant like `exp(−4√(kx))`
  (Stieltjes fraction), so `k ≈ (p ln 2)²/(16x) ≈ 0.03 p²/x` terms: `0.3p` at `x = 0.1p`, `0.04p` at
  `x = 0.7p`. Evaluation exactly as §4.6 prescribes: a *forward* pass at low precision (64-bit
  `Float` or a 64-bit `AzFloat`) with the continuants `P_j, Q_j` and the difference recurrence (4.46)
  `D_j = −a_j Q_{j−2} D_{j−1}/Q_j` to find the first `k` with `|D_k| < 2^{−p−2}|f_k|`, then the
  *backward* recurrence (4.43) `R_k = 1, R_{k−1} = b_k, R_j = b_{j+1}R_{j+1} + a_{j+2}R_{j+2}` at
  `p + ⌈log₂ k⌉ + 2` bits (all quantities positive, relative error `O(k 2^{−p'})`), value
  `a₁R₁/R₀`; evaluate `f_{k−1}` and `f_k` both (or `f_k, f_{k+1}`), return the midpoint with the
  rigorous bound `|f_k − f_{k−1}|/2` from Theorem 4.1 (`abs_sub_midpoint_lt`, which needs the
  limit to be `e^x E₁(x)`: unproven, see below). Cost `O(k M(p))` with `k ≈ 0.03p²/x`, plus one
  `exp(−x)`. Region: `c₁ p < x < ln 2 · p`, `c₁ ≈ 0.1` (where `0.03p²/x` drops below the `≈ 0.3p`
  terms of (c)).
  *Empirical determination.* Harness in `benchmarks/` (reuse the tuner's single comma-separated
  config argument): for `p ∈ {64, 128, 256, 512, 1024, 4096, 16384}` and `x = 2^{e}`, `e ∈ [−10, 16]`
  in quarter steps, time each applicable kernel (skip (b) below its threshold; cap (d) at
  `k ≤ 10p`), compare against a cross-check (two methods agreeing to `p` bits), and record the two
  crossovers `x_{ac}(p)` ((a) vs (c), expected `≈ 1` and nearly independent of `p`), `x_{cd}(p)`
  ((c) vs (d), expected `≈ c₁ p` with `c₁ ≈ 0.1`; check the predicted scaling `x_{cd} ∝ p`) and
  `x_{db}(p)` ((d) vs (b), expected `= p ln 2 + O(log p)`: (b) wins as soon as it is applicable since
  `k ≈ x` terms beat `0.03p²/x ≈ 0.04p` only for `x ≲ 0.2p`… so measure whether (d) stays faster
  slightly above the (b) threshold). Store the fitted thresholds as named constants in the
  dispatcher, with the `p`-dependence explicit. Follow the benchmarking rules (quiet machine, go-ahead
  first, keep the old binary for A/B).
  *Proof status for a later certified implementation.* (b): fully proven bounds, certifiable now.
  (d): the bracket theorems are proven but convergence of (4.39) to `e^x E₁` is not (Stieltjes
  theory, not in Mathlib) — a conditional statement is available. (a)/(c): `hasSum_exp_mul_Ein` is
  proven, but (4.26) `E₁ = Ein − γ − ln x` with Mathlib's `γ` is not — implement after (4.26) or
  state the spec relative to `Ein`. Suggested order: `exp`/`ln` first; then (b) with proofs, (d),
  then `γ` and (a)/(c).
* **Exercise 4.25** (prove the backward recurrence (4.43)). **Answer.** Let
  `T_j = a_j/b_j+ a_{j+1}/b_{j+1}+ ⋯ a_k/b_k` be the tail fraction (`tailFrac`), so
  `T_j = a_j/(b_j + T_{j+1})` and `T_{k+1} = 0`. Claim: `R_{j−1} = (b_j + T_{j+1}) R_j` for
  `1 ≤ j ≤ k` (`backR_pred`). Backward induction on `j`: for `j = k`, `R_{k−1} = b_k = (b_k + 0) R_k`
  by the initial values; for `j < k`, (4.43) gives `R_{j−1} = b_j R_j + a_{j+1} R_{j+1}` and the
  induction hypothesis `R_j = (b_{j+1} + T_{j+2}) R_{j+1}` gives
  `a_{j+1} R_{j+1} = a_{j+1} R_j/(b_{j+1} + T_{j+2}) = T_{j+1} R_j`, hence
  `R_{j−1} = (b_j + T_{j+1}) R_j`. Since all `R_j > 0` (`backR_pos`, for positive `a_j, b_j`) this is
  the text's invariant `R_j/R_{j−1} = 1/(b_j + T_{j+1}) = 1/b_j+ a_{j+1}/b_{j+1}+ ⋯ a_k/b_k`
  (`backR_div`), and at `j = 1`: `R_1/R_0 = 1/(b_1 + T_2)`, so `a_1 R_1/R_0 = a_1/(b_1 + T_2) = T_1 = y`
  (`approximant_eq_backR`, restated with `b₀ = 0` as `finiteFrac_eq_backR`; `k = 2` check
  `finiteFrac_two_eq`). Positivity is only used to keep denominators nonzero; the identity holds
  whenever no `b_j + T_{j+1}` vanishes. All of this was formalized in the §4.6 chunk
  (`ContinuedFractionEval.lean`); the exercise adds only the restatements.
* **Exercise 4.26** (prove the forward recurrence (4.44)). **Answer.** Following the hint, let
  `y_k(x) = a₁/b₁+ ⋯ a_{k−1}/b_{k−1}+ a_k/(b_k + x)` (`tailFracX a b k x 1`; the general
  `tailFracX a b k x j` starts at index `j` and returns `x` when `j > k`). Peeling the innermost
  level, `y_{k+1}(x) = y_k(a_{k+1}/(b_{k+1} + x))` (`tailFracX_succ`, by recursion on the start
  index). Claim: `b₀ + y_k(x) = (P_k + P_{k−1}x)/(Q_k + Q_{k−1}x)` for `k ≥ 1`, with `P, Q` the
  continuants of (4.44), `P₀ = b₀, P₁ = b₁b₀ + a₁, Q₀ = 1, Q₁ = b₁`, `P_j = b_jP_{j−1} + a_jP_{j−2}`
  (Mathlib's `nums`/`dens`; the text's `P₀ = 0, P₁ = a₁` is the case `b₀ = 0`). Induction on `k`:
  `k = 1`: `b₀ + a₁/(b₁ + x) = (b₁b₀ + a₁ + b₀x)/(b₁ + x)`. Step: `b₀ + y_{k+1}(x) = b₀ + y_k(x')`
  with `x' = a_{k+1}/(b_{k+1} + x)`, `= (P_k + P_{k−1}x')/(Q_k + Q_{k−1}x')` by the hypothesis,
  and multiplying numerator and denominator by `b_{k+1} + x`:
  `= (P_k(b_{k+1} + x) + a_{k+1}P_{k−1})/(Q_k(b_{k+1} + x) + a_{k+1}Q_{k−1}) = (P_{k+1} + P_kx)/(Q_{k+1} + Q_kx)`
  by the recurrence (`tailFracX_eq_nums_dens`; positivity of `a_j, b_j` and `x ≥ 0` keeps all
  denominators nonzero). At `x = 0`, `y_k(0) = a₁/b₁+ ⋯ a_k/b_k` (`tailFracX_zero`), so
  `f_k = b₀ + y_k(0) = P_k/Q_k` (`approximant_eq_nums_div_dens`), which is (4.44) — an
  independent proof of `approximant_eq_convs` (previously imported from Mathlib's
  `convs_eq_convs'`). The same identity with `x = a_{k+1}/b_{k+1}+ ⋯` explains why the
  continuants can be extended one step at a time: the fraction is a Möbius transformation
  `x ↦ (P_k + P_{k−1}x)/(Q_k + Q_{k−1}x)` of its tail.
* **Exercise 4.27** (matrix form of the forward recurrence). **Answer.** Let
  `M_j = [[b_j, 1], [a_j, 0]]` and `N_k = [[Q_k, Q_{k−1}], [P_k, P_{k−1}]]` with the text's initial
  values `P₀ = 0, P₁ = a₁, Q₀ = 1, Q₁ = b₁` (Mathlib's continuants with `b₀ = 0`). Then
  `N_k M_{k+1} = [[Q_k b_{k+1} + Q_{k−1} a_{k+1}, Q_k], [P_k b_{k+1} + P_{k−1} a_{k+1}, P_k]] = N_{k+1}`
  by (4.44), and `N_1 = M_1`, so by induction `M_1 M_2 ⋯ M_k = N_k` for `k ≥ 1` (`cfProd_eq`). For
  `k = 0` the empty product is the identity, which is `N_0` once `P_{−1} := 1`, `Q_{−1} := 0`
  (`cfProd_zero`); these values are exactly what the recurrence needs to start, since then
  `P₁ = b₁P₀ + a₁P_{−1} = a₁` and `Q₁ = b₁Q₀ + a₁Q_{−1} = b₁`. Hence `f_k = P_k/Q_k` is the ratio of
  the two first-column entries of the product (`approximant_eq_cfProd`). *Remark (parallelism).*
  Matrix multiplication is associative, so the product over any segment of indices can be formed
  independently and the segments combined afterwards: `∏_{(i, i+m+n]} = ∏_{(i, i+m]} · ∏_{(i+m, i+m+n]}`
  (`cfProdRange_add`). With `p` processors each forms the product of `k/p` consecutive `M_j` and
  the `p` partial products are multiplied in a tree of depth `log₂ p`; with exact integer or
  rational `a_j, b_j` this is also the binary-splitting evaluation of §4.9 (the entries of a
  segment product of length `n` have `O(n log n)` bits, and the tree costs `O(M(k log k) log k)`
  instead of the `k` sequential full-precision operations of (4.44)); the final division `P_k/Q_k`
  is done once. Order matters: the `M_j` do not commute, so the segment products must be
  multiplied in index order.
* **Exercise 4.28** (`det [[Q_k, Q_{k−1}], [P_k, P_{k−1}]] = (−1)^k a_1 ⋯ a_k`). **Answer.** By
  Exercise 4.27 the matrix is `M_1 M_2 ⋯ M_k` with `M_j = [[b_j, 1], [a_j, 0]]`, and
  `det M_j = b_j · 0 − 1 · a_j = −a_j` (`det_cfStep`); the determinant is multiplicative, so
  `det (M_1 ⋯ M_k) = ∏_{j≤k} (−a_j) = (−1)^k a_1 ⋯ a_k` (`det_cfProdRange`, `det_cfProd`), i.e.
  `Q_k P_{k−1} − P_k Q_{k−1} = (−1)^k a_1 ⋯ a_k` (`det_continuants`; for `k = 0` with the convention
  of Exercise 4.27 the determinant of the identity is `1`, the empty product). Equivalently, by
  induction straight from (4.44): `Δ_k := P_k Q_{k−1} − P_{k−1} Q_k` satisfies `Δ_{k+1} = −a_{k+1} Δ_k`
  (`det_succ` in `ContinuedFractionEval.lean`), `Δ_1 = a_1`. Consequence: the difference of
  consecutive approximants is `f_k − f_{k−1} = Δ_k/(Q_k Q_{k−1}) = (−1)^{k−1} a_1 ⋯ a_k/(Q_k Q_{k−1})`,
  which is (4.45)–(4.46) (`diff_eq_det_div`, `diff_succ`): the sign alternates and the magnitude
  is computed without cancellation, the basis of the stopping rule and of Theorem 4.1.
* **Exercise 4.29** (prove (4.46)). **Answer.** `D_j = f_j − f_{j−1} = P_j/Q_j − P_{j−1}/Q_{j−1}
  = Δ_j/(Q_j Q_{j−1})` with `Δ_j = P_j Q_{j−1} − P_{j−1} Q_j` (`diff_eq_det_div`), and `D_1 = f_1 − f_0
  = a_1/b_1` (`diff_one`). By Exercise 4.28 (or directly from (4.44), `det_succ`),
  `Δ_j = −a_j Δ_{j−1}`, so `D_j/D_{j−1} = (Δ_j/Δ_{j−1}) · (Q_{j−1}Q_{j−2})/(Q_j Q_{j−1}) = −a_j Q_{j−2}/Q_j`,
  which is (4.46): `D_j = −a_j Q_{j−2} D_{j−1}/Q_j` (`diff_succ`). Equivalently, the closed form
  `D_k = (−1)^{k−1} a_1 a_2 ⋯ a_k/(Q_k Q_{k−1})` (`diff_eq_prod_div`) and the ratio of two
  consecutive closed forms (`diff_succ'`). Division by `Q_j` is harmless since `Q_j > 0` for
  positive coefficients (`dens_pos`). Why (4.46) matters: computing `D_j` as `P_j/Q_j − P_{j−1}/Q_{j−1}`
  subtracts two nearly equal numbers and loses `≈ log₂(|f|/|D_j|)` bits, whereas (4.46) builds
  `D_j` multiplicatively from positive quantities with a known sign `(−1)^{j−1}`, so the stopping
  test `|D_j| < ε` of §4.6 is reliable at low working precision.
* **Exercise 4.30** (prove Theorem 4.1). **Answer.** With `a_j, b_j > 0`: (i) `Q_j > 0` for all
  `j` (induction with (4.44), `dens_pos`); (ii) `D_1 = a_1/b_1 > 0` and, by (4.46),
  `D_j = −a_j Q_{j−2} D_{j−1}/Q_j`, so `D_j` has sign `(−1)^{j−1}` (`sign_diff`) and
  `|D_j| < |D_{j−1}|` because `Q_j = b_j Q_{j−1} + a_j Q_{j−2} > a_j Q_{j−2}` (`abs_diff_succ_lt`);
  (iii) hence `f_{2k+2} − f_{2k} = D_{2k+2} + D_{2k+1} > 0` since the positive `D_{2k+1}` dominates
  the negative `D_{2k+2}` (`approximant_even_lt_succ`), and symmetrically
  `f_{2k+3} − f_{2k+1} = D_{2k+3} + D_{2k+2} < 0` (`approximant_odd_succ_lt`): `(f_{2k})` is strictly
  increasing and `(f_{2k+1})` strictly decreasing (`approximant_even_strictMono`,
  `approximant_odd_strictAnti`); (iv) `f_{2k} < f_{2k+1}` (`D_{2k+1} > 0`), and comparing through
  `n = max(k, m)`, `f_{2k} ≤ f_{2n} < f_{2n+1} ≤ f_{2m+1}`: every even approximant is below every
  odd one (`approximant_even_lt_odd`); (v) if the fraction converges to `f`, the even
  subsequence increases to `f` and the odd one decreases to `f`, so `f_{2k} < f < f_{2m+1}`
  strictly (a strictly monotone sequence never attains its limit: `approximant_even_lt`,
  `lt_approximant_odd`); (vi) therefore `f` lies strictly between any two consecutive
  approximants `f_{m−1}, f_m` (one even, one odd; `approximant_between_consecutive`), and a point
  strictly inside an interval is within half its length of the midpoint:
  `|f − (f_{m−1} + f_m)/2| < |f_m − f_{m−1}|/2` (`abs_sub_midpoint_lt`). Packaged as `theorem_4_1`.
  The hypothesis that the fraction converges (`HasContFracValue`) is genuinely needed for (v)–(vi)
  and is proven here only in the sense of Mathlib's general theory (for (4.39)/(4.40) it is the
  unformalized Stieltjes result); (i)–(iv) are unconditional. Use: the midpoint of two consecutive
  backward-recurrence evaluations gives a certified error bound, the `(value, Ordering)` bracket of
  the `AzFloat` design.
* **Exercise 4.31** (the continued fraction (4.40) for `erfc`/`erf`). **Answer.** (4.40) is
  `erfc x = (e^{−x²}/√π) · 1/x+ (1/2)/x+ (2/2)/x+ (3/2)/x+ ⋯`, with `a₁ = 1`, `a_j = (j−1)/2`,
  `b_j = x`: positive coefficients for `x > 0` (`erfcCF_pos`), so Theorem 4.1 applies and
  consecutive approximants bracket the value. *How fast does it converge?* By (4.45)–(4.46),
  `|D_{k+1}| = a₁⋯a_{k+1}/(Q_{k+1}Q_k)` with `a₁⋯a_{k+1} = k!/2^k` (`erfcCF_prod_num`) and
  `Q_j = x Q_{j−1} + a_j Q_{j−2} ≥ x^j` (`erfcCF_dens_ge`), so `|D_{k+1}| ≤ k!/(2^k x^{2k+1})`
  (`erfcCF_abs_diff_le`). Compare with the asymptotic series (4.37), whose `k`-th normalized term
  is `(2k)!/(k! 4^k x^{2k}) · (1/x)`: since `(k!)² 2^k ≤ (2k)!` (`factorial_sq_mul_two_pow_le_factorial`),
  `|D_{k+1}| ≤ t_k` (`erfcCF_abs_diff_le_erfcTermMag`) — for `k ≪ x²` the fraction converges at
  least as fast as the asymptotic series, in fact with an extra factor `≈ 2^{−k}` (its steps are
  `≈ k!/2^k` against `(2k−1)‼/2^k`), and each backward-recurrence step `R_j = x R_{j+1} + a_{j+2} R_{j+2}`
  costs the same as a series term (one full multiplication by `x`, one small scalar). For
  `k ≳ x²` the asymptotic terms start to grow and (4.37) stalls at accuracy `≈ e^{−x²}`, whereas
  the fraction's steps keep shrinking (`abs_diff_succ_lt`), with the Stieltjes-type rate
  `|D_k| ≈ exp(−2√2 x√k)` for `k ≫ x²`, i.e. `k ≈ (m ln 2)²/(8x²)` terms for `m` bits.
  *Comparison with Algorithm Erf (4.2).* To get `erf x` to `n` bits one needs `erfc x` to
  `m = n − λ` bits, `λ ≈ x²/ln 2`; the asymptotic branch is usable iff `(m + ½) ln 2 < x²`, i.e.
  `x ≳ √(n ln 2/2) ≈ 0.59√n`, and just above that threshold it needs its full `≈ x² ≈ 0.35 n`
  terms; below it Algorithm Erf falls back to the series (4.22)/(4.23), which need `≈ e x²`
  terms (plus `≈ x²/ln 2` guard bits for (4.22) and for `erfc` itself). The fraction at the same
  `x` needs about `(m ln 2)²/(8x²) ≈ 0.06 n²/x² · (m/n)²` terms: at the threshold `x² ≈ 0.35n`,
  `m ≈ n/2`, this is `≈ 0.04n` terms against `0.35n` for the asymptotic series and `≈ 0.95n` for
  (4.23); somewhat below the threshold, say `x² ≈ 0.2n`, it is `≈ 0.15n` against `≈ 0.55n` series
  terms with extra precision, and the asymptotic branch is unavailable. So **yes**: there is a
  region, roughly `0.3√n ≲ x ≲ 0.6√n` (shrinking towards `x ≈ 1` as the series take over for
  small `x`, where `k ≈ 0.06 n²/x²` explodes), in which (4.40) beats every branch of Algorithm Erf,
  and above the threshold it remains at least as good as the asymptotic branch per term (the
  asymptotic branch keeps a small constant-factor edge only because its stopping index is known
  in advance and it needs no final division/bracket). For `erfc` itself (relative precision), the
  picture is the same with `m = n`: the asymptotic branch needs `x > √(n ln 2)` and the fraction
  fills the gap `√(n ln 2)/3 ≲ x ≲ √(n ln 2)` where the series would need `Ω(x²)` terms *and*
  `x²/ln 2` extra bits to beat the cancellation in `1 − erf`. Caveat: convergence of (4.40) to
  `erfc` (and the rate) is the unformalized Stieltjes theory; what is proven is the term-by-term
  comparison with (4.37) and the monotone shrinking of the steps.
* **Exercise 4.32** (evaluating (4.41) in `O(M(k) log k)` for bounded integer coefficients).
  **Answer.** By Exercise 4.27, `[[Q_k, Q_{k−1}], [P_k, P_{k−1}]] = M_1 M_2 ⋯ M_k` with
  `M_j = [[b_j, 1], [a_j, 0]]`, and `f_k = P_k/Q_k`. If `|a_j|, |b_j| ≤ B` are integers, every
  product of `n` consecutive `M_j` has integer entries bounded by `(2B)^n` (`cfStep_entry_le`,
  `cfProdRange_entry_le`: each multiplication by an `M_j` at most doubles the entry bound and
  multiplies it by `B`), so a segment product of length `n` has entries of at most
  `n log₂(2B) = O(n)` bits. Evaluate the product by binary splitting (`cfProdRange_add`): split
  the index range in half, form the two halves recursively, multiply the two `2×2` matrices.
  At depth `ℓ` of the recursion there are `2^ℓ` products of matrices with `O(k/2^ℓ)`-bit entries,
  each costing `8` integer multiplications of that size (`4` with Strassen, or `7`; the constant is
  irrelevant). In the quasi-linear model `M(m) = m lg m` the level costs `2^ℓ · 8M(ck/2^ℓ) ≤ 8M(ck)`
  (`two_pow_mul_quasiLinearCost_div_le`, `c = log₂(2B)`), so the `⌈lg k⌉` levels cost at most
  `8 ⌈lg k⌉ M(ck) = O(M(k) log k)` (`splitting_levels_cost_le`); in general the bound holds for any
  `M` with `M(2m) ≥ 2M(m)` (`sum_cost_le`, Exercise 4.1), the usual binary-splitting argument of
  §4.9. The leaves cost `O(k)` in all. Finally one division `P_k/Q_k` of `O(k)`-bit integers,
  `O(M(k))`, gives `f_k` exactly as a rational, or to any precision `n ≤ O(k)` bits by one
  floating-point division. Total `O(M(k) log k)`, against the `O(k M(k))` of the sequential forward
  or backward recurrence at `k`-bit precision (or `O(k M(n))` at a fixed working precision `n`).
  Rational coefficients with bounded numerators and denominators: clear the denominator of each
  `M_j` (multiply `M_j` by `d_j = lcm` of its two denominators, which scales `P_k, Q_k` by the same
  `∏ d_j` and leaves `f_k = P_k/Q_k` unchanged), giving integer matrices with entries `≤ B'` and the
  same analysis. For (4.39)/(4.40) the coefficients are not bounded (`a_j ≈ j/2`), but they have
  `O(log k)` bits, so the entries have `O(k log k)` bits and the cost is `O(M(k log k) log k)` — the
  same conclusion up to the logarithmic factor, as for the series in §4.9; with `x` an `n`-bit
  number (not a small rational) the entries of `M_j` carry `n` bits and the method reverts to
  `O(M(n) k)`-type costs, which is why §4.6 evaluates (4.39) by the backward recurrence instead.
* **Exercise 4.33** (normalizing Miller's algorithm by (4.54) or by (4.89)). **Answer.** Miller's
  backward recurrence produces `y_ν = c J_ν(x)(1 + ε_ν)` for `0 ≤ ν ≤ N` with `|ε_ν| ≤ ε` (the
  relative errors from the start-up defect and the rounding of the recurrence), and `c` is fixed
  from a normalization sum. *(4.54)* `J₀ + 2∑_{ν≥1} J_{2ν} = 1` (proven: `besselJ_even_sum`) gives
  `c ≈ y₀ + 2∑ y_{2ν}`, a linear sum whose terms, for `2ν < x`, are of size `≈ √(2/(πx))` and of
  *alternating, irregular signs* (the `J_{2ν}(x)` oscillate for `ν < x`), while the sum is `1`:
  the absolute error is `≤ ε ∑|t_ν|` (`abs_sum_perturbed_sub_le`), amplified by
  `κ₁ = ∑|t_ν|/|∑ t_ν| = ∑|t_ν|`. By Cauchy–Schwarz (`sum_abs_le_sqrt_card_mul_sum_sq`) and the
  identity (4.89) itself, `∑_{2ν≤N}|2J_{2ν}| ≤ √(2N ∑ 2J_{2ν}²)·… ≤ √(2(N+1))`, so `κ₁ ≤ √(2N) ≈ √x`
  (the terms beyond `ν ≈ x` are negligible): (4.54) loses at most `½ log₂ x + 1` bits, not more.
  *(4.89)* `J₀² + 2∑_{ν≥1} J_ν² = 1` gives `c² ≈ y₀² + 2∑ y_ν²`, a sum of *nonnegative* terms, whose
  relative error is `≤ 2ε + ε²` with no amplification at all (`abs_sum_sq_perturbed_sub_le`); the
  sign of `c` is not lost, because the recurrence is started with `y_N = 1 > 0` at `N > x`, where
  `J_N(x) > 0` (the first zero `j_{N,1}` exceeds `N`), so `c > 0`. Its tail also decays faster
  (`J_ν²` against `J_{2ν}`), though both sums are dominated by `ν ≲ x` and the start index `N`
  must anyway exceed `x` by `O(n^{…})` for the recurrence itself. *Costs.* (4.54) uses only the
  even indices, `N/2` additions and no multiplications; (4.89) needs `N` squarings, each a full
  `p`-bit multiplication, i.e. about as much work again as the recurrence (`y_{ν−1} = (2ν/x)y_ν −
  y_{ν+1}`: one multiplication by the precomputed `1/x` and a scalar multiplication per step).
  *Verdict.* Numerically (4.89) is preferable — positive terms, no cancellation, relative error
  `2ε + O(ε²)`, a bound that needs no knowledge of the sign pattern of the `J_{2ν}` — and it is
  the right choice at fixed (machine) precision or when a rigorous, assumption-free error bound is
  wanted. In arbitrary precision, however, (4.54)'s loss is provably at most `≈ ½ log₂ x` bits,
  which `⌈½ log₂ x⌉ + 2` guard bits absorb at negligible cost, while (4.89) roughly doubles the
  multiplication count; so for high-precision Bessel evaluation (4.54) with guard bits is the
  cheaper normalization, and (4.89) is the safer one. (4.89) itself follows from the generating
  function `e^{(x/2)(t − 1/t)} = ∑ J_ν t^ν` multiplied by its value at `1/t`: the constant term of
  the product is `∑_ν J_ν(x)² = 1`, i.e. `J₀² + 2∑_{ν≥1} J_ν² = 1` as `J_{−ν} = (−1)^ν J_ν`; this
  two-sided Cauchy product is not formalized (only `t = ±1`, i.e. (4.54), is).
* **Exercise 4.34** (the model recurrence `f_{ν−1} + f_{ν+1} = 2K f_ν`). **Answer.** `λ^ν` solves
  the recurrence iff `λ^{ν−1}(λ² − 2Kλ + 1) = 0`, i.e. iff `λ` is a root of `x² − 2Kx + 1`
  (`isConstRecSol_pow`). Solutions form a vector space (`IsConstRecSol.add`, `.smul`), and a
  solution is determined by `f₀, f₁` (two-step induction, `IsConstRecSol.eq_of_init`). For distinct
  roots `λ ≠ μ` the system `A + B = f₀`, `Aλ + Bμ = f₁` has the unique solution
  `A = (f₁ − μf₀)/(λ − μ)`, `B = (λf₀ − f₁)/(λ − μ)`, and `Aλ^ν + Bμ^ν` agrees with `f` at `0, 1`,
  hence everywhere (`IsConstRecSol.exists_eq_comb`). Vieta: `λμ = 1` and `λ + μ = 2K` in both
  cases; the discriminant is `4(K² − 1)`, nonzero as `K ≠ 1` (for `K = 1` the double root `1` gives
  the solutions `A + Bν`, excluded here). *Case `K > 1`:* `λ, μ = K ± √(K² − 1)` are real,
  `λμ = 1`, `λ > 1 > μ > 0` (`roots_of_one_lt`): one solution grows and the other decays
  geometrically. *Case `0 < K < 1`:* `λ, μ = K ± i√(1 − K²)` are complex conjugates with
  `|λ|² = K² + (1 − K²) = 1` (`roots_of_lt_one`): `λ = e^{±iθ}`, `cos θ = K`, and every real solution
  is `C cos(νθ + φ)`, bounded and oscillatory. *Insight for (4.53).* Near `ν ≈ Kx` the Bessel
  recurrence `f_{ν−1} + f_{ν+1} = (2ν/x) f_ν` has the slowly varying coefficient `2K`, so locally
  it behaves like the model: for `ν < x` (`K < 1`) both `J_ν` and `Y_ν` oscillate with comparable
  amplitude (`≈ √(2/(πx))`) and neither direction of the recurrence is unstable; for `ν > x`
  (`K > 1`) the solutions split into a geometrically decaying one (`J_ν ≈ μ^ν` direction) and a
  growing one (`Y_ν ≈ λ^ν`), so the forward recurrence loses `J_ν` to rounding (any admixture of
  `Y` is amplified by `λ ≈ 2K` per step) while the backward recurrence damps it — exactly the
  mechanism behind Miller's algorithm and the growth rates (4.55) (`λ = K + √(K² − 1) ≈ 2K` for
  large `K`, matching `Y_ν ~ (2ν/(ex))^ν` after accounting for the varying `K`).
* **Exercise 4.35** (rounding errors in the Bernoulli recurrences (4.59) and (4.60)). **Answer.**
  Write (4.59) as a convolution: `∑_{j≤k} C_j T_{k−j} = r_k` with `T_m = 1/(2m+1)!` (the
  coefficients of `sinh x/x`) and `r_k = 1/(2(2k)!)`. Computing `C_k = r_k − ∑_{j<k} C_j T_{k−j}` in
  precision `n`, the computed values `C̃_k` satisfy the same recurrence with perturbed right
  sides `r_k + ρ_k`, `|ρ_k| ≲ (k+1) 2^{−n} max_j |C̃_j T_{k−j}|` (each of the `k+1` terms rounded
  once; the terms are `O(|C_k|)` since `T_m ≤ 1/6` for `m ≥ 1`). The errors `e_k = C̃_k − C_k` then
  satisfy `∑_{j≤k} e_j T_{k−j} = ρ_k`, a linear recurrence whose solution is the convolution
  `e_k = ∑_{j≤k} ρ_j κ_{k−j}` with `κ` the convolution inverse of `T`: `κ(x²) · sinh x/x = 1`, i.e.
  `κ` has generating function `x/sinh x` (`error_propagation`, proven in `ℚ⟦X⟧` with `X` standing
  for `x²`: `mk e · mk T = mk ρ`, `mk κ · mk T = 1`, so `mk e = mk ρ · mk κ`). Explicitly
  `x/sinh x = x/tanh(x/2) − x/tanh x = 2S(x) − S(2x)`, so `κ_k = (2 − 4^k) C_k` (`bernoulliKernel`,
  `kernel_mul_sinh`: `(2S(x) − S(2x))(e^x − e^{−x}) = 2x`, obtained by rescaling (4.57) by `2`,
  multiplying through by `e^x` and cancelling `e^x` in the domain `ℚ⟦X⟧`; the coefficient of
  `x^{2k+1}` gives `∑_{j≤k} κ_j T_{k−j} = [k = 0]`, `kernel_conv_eq`). *(a)* The solution decays like
  `|C_k| ≍ (2π)^{−2k}` (`2/(2π)^{2k} ≤ |C_k| ≤ (π²/3)/(2π)^{2k}`, `abs_scaledBernoulli_ge/le`, from
  `1 ≤ ζ(2k) ≤ π²/6`), but the kernel only like `|κ_k| = (4^k − 2)|C_k| ≍ π^{−2k}`
  (`abs_bernoulliKernel_eq`): the radius of convergence of the propagation operator `x/sinh x` is
  `π`, that of the solution `2π`. Hence the rounding error `ρ_0 ≈ 2^{−n}` made at the first step
  (and the error of any early step `j`, `≈ 2^{−n}(2π)^{−2j}`) arrives in `C_k` as
  `ρ_0 κ_k`, whose size relative to `C_k` is `(4^k − 2)·6/π² ≈ 0.6 · 4^k` at least
  (`kernel_amplification_ge`): the relative error of `C_k` is of order `4^k 2^{−n}`, growing by two
  bits per step; summing over `j`, `∑_j 2^{−n}(2π)^{−2j} π^{−2(k−j)} (2π)^{2k} = 2^{−n} 4^k ∑_j 4^{−j}
  ≈ (4/3) 4^k 2^{−n}`, dominated by the first steps. *(b)* (4.60) reads, after multiplying by `4^k`,
  `∑_{j≤k} D_j T_{k−j} = 1/(2k)!` with `D_j = 4^j C_j`: the *same* convolution and the same kernel
  `κ`, but now for the sequence `D_k ≍ π^{−2k}` which decays exactly as fast as `κ`. A rounding
  error at step `j`, `|ρ_j| ≲ (j+1) 2^{−n} |D_j|`, reaches `D_k` as `ρ_j κ_{k−j}` with
  `|κ_{k−j}| |D_j| ≤ 4^{k−j}|C_{k−j}| 4^j |C_j| ≤ (π²/3)² 4^k/(2π)^{2k} ≤ (π⁴/18) |D_k|`
  (`abs_bernoulliKernel_le`, `kernel_amplification_le`): relative amplification `≤ π⁴/18 ≈ 5.4`,
  a constant. Summing the `k` steps, each contributing `O(j 2^{−n})`, the relative error of
  `D_k = 4^k C_k` (and of `C_k`, an exact power of two away) is `O(k² 2^{−n})`. In the
  generating-function picture: (4.59) inverts `sinh x/x` (radius `π`) to produce a series of
  radius `2π`, so noise at radius `π` is magnified by `(2π/π)^{2k} = 4^k`; (4.60) inverts
  `sinh(x/2)/(x/2)` (radius `2π`), the same radius as the solution, so the noise is only
  amplified polynomially — the general principle for choosing a numerically stable recurrence.
* **Exercise 4.36** ((4.57) from (4.56), and (4.62)). **Answer.** *(4.57).* Let
  `f(x) = x/(e^x − 1) + x/2`. Then `f(−x) = −x/(e^{−x} − 1) − x/2 = x e^x/(e^x − 1) − x/2`, and
  `f(−x) − f(x) = x(e^x − 1)/(e^x − 1) − x = 0`: `f` is even (`div_exp_sub_one_add_half_even`). By
  (4.56), `f(x) = ∑_k B_k x^k/k! + x/2 = 1 + (B_1 + 1/2) x + ∑_{k≥2} B_k x^k/k!`; evenness forces
  the odd coefficients to vanish, so `B_1 = −1/2` and `B_{2j+1} = 0` for `j ≥ 1`
  (`bernoulli_odd_eq_zero'`, Mathlib's `bernoulli_eq_zero_of_odd`), and what remains is
  `f(x) = ∑_k B_{2k} x^{2k}/(2k)! = ∑_k C_k x^{2k}`, which is (4.57) (`scaledBernoulliPowerSeries_eq`:
  the series `S = B(x) + x/2` has coefficient `C_k` at `x^{2k}` and `0` at `x^{2k+1}`). The closed
  form: `x/(e^x − 1) + x/2 = (x/2)(e^x + 1)/(e^x − 1) = (x/2)/tanh(x/2)` since
  `tanh(x/2) = (e^x − 1)/(e^x + 1)` (`div_exp_sub_one_add_half`, `tanh_half_eq`). *(4.62).* From
  (4.57), `x/tanh x = ∑ C_k (2x)^{2k} = ∑ 4^k C_k x^{2k}`, so
  `tanh x = 1/tanh x − 2/tanh(2x)` … more directly `tanh x = coth x − 2 coth 2x` gives
  `x tanh x = ∑_k (4^k − 16^k) C_k x^{2k}`, i.e. `tanh x = ∑_{k≥1} (4^k − 16^k) C_k x^{2k−1}`
  (`X_mul_tanhSeries`, `coeff_tanhSeries_odd`), and `tan x = tanh(ix)/i` flips the sign of every
  other coefficient: `tan x = ∑_{k≥1} (−1)^{k−1}(16^k − 4^k) C_k x^{2k−1}`. Comparing with (4.61),
  `T_k/(2k−1)! = (−1)^{k−1}(16^k − 4^k) B_{2k}/(2k)!`, hence
  `T_k = (−1)^{k−1} 4^k (4^k − 1) B_{2k}/(2k) = (−1)^{k−1} 2^{2k}(2^{2k} − 1) B_{2k}/(2k)`, which is
  (4.62) (`tangentNumber_eq_bernoulli'`, the text's indexing of `tangentNumber_eq_bernoulli`). In
  `TangentNumbers.lean` the step `tan x = tanh(ix)/i` is replaced by a formal argument: the
  sign-twisted series satisfies the same ODE `y' = 1 + y²` with `y(0) = 0` as the series of
  Taylor coefficients of `tan`, and such a solution is unique (`eq_of_derivative_eq_one_add_sq`).
* **Exercise 4.37** (bit sizes of `T_k` and of `B_{2k}`). **Answer.** *(a)* From (4.62) and
  `|B_{2k}| = 2(2k)! ζ(2k)/(2π)^{2k}` (`abs_bernoulli_two_mul_eq`),
  `|T_k| = 4^k(4^k − 1)|B_{2k}|/(2k) = 2(4^k − 1)(2k−1)! ζ(2k)/π^{2k}` (`abs_tangentNumber_eq`), and
  as `1 ≤ ζ(2k) ≤ π²/6`, `4^k/2 ≤ 4^k − 1` and `4^k ≤ π^{2k}`:
  `(4/π²)^k (2k−1)! ≤ |T_k| ≤ (π²/3)(2k−1)!` (`abs_tangentNumber_bounds`). Stirling in the form
  `m ln m − m ≤ ln m! ≤ m ln m − m + 1 + ½ ln m` (`log_factorial_bounds`, from
  `√(2πm)(m/e)^m ≤ m! ≤ e√m (m/e)^m`) with `m = 2k` and `(2k−1)! = (2k)!/(2k)` gives
  `2k ln k − 4k − ln(2k) ≤ ln|T_k| ≤ 2k ln k + 3` (`log_abs_tangentNumber_bounds`; the constants
  come from `−2 ≤ ln(4/π²)` and `ln(π²/3) ≤ 2`). Dividing by `2k ln k`, both sides tend to `1`:
  the number of bits `lg|T_k| ∼ 2k lg k`, i.e. `T_k` has about as many bits as `(2k)!` — the
  factor `(4/π²)^k ≈ 2^{−1.3k}` only shifts the count by `O(k)`. *(b)* Write `B_{2k} = N/D` in
  lowest terms. The denominator is small: `D ∣ 4^k(4^k − 1)` (`bernoulli_den_dvd`, from (4.62) with
  `T_k ∈ ℤ`; by von Staudt–Clausen `D = ∏_{(p−1)∣2k} p` is in fact much smaller still), so
  `ln D ≤ 4k ln 2` (`log_bernoulli_den_le`), `O(k)` bits. The numerator carries the size:
  `|N| = |B_{2k}| D`, so `ln|N| = ln|B_{2k}| + ln D` with `ln|B_{2k}| = ln 2 + ln(2k)! + ln ζ(2k)
  − 2k ln(2π) = 2k ln k − 2k(1 + ln π) + O(ln k)`; altogether
  `2k ln k − 8k ≤ ln|N| + ln D ≤ 2k ln k + 6k + 3` (`log_bernoulli_num_den_bounds`). Hence the
  exact rational `B_{2k}` also needs `∼ 2k lg k` bits, essentially all in the numerator, and the
  same holds for the scaled `C_k = B_{2k}/(2k)!`'s *denominator* (`(2k)! D/gcd`, `∼ 2k lg k` bits)
  while its numerator is tiny — which is why §4.7.2 prefers the integer tangent numbers (one
  `∼ 2k lg k`-bit integer, computed by an integer-only recurrence) to rational Bernoulli numbers
  (a `∼ 2k lg k`-bit numerator plus a denominator needing a gcd), and why either representation
  of `B_2, …, B_{2m}` costs `Θ(m² log m)` bits in total.
* **Exercise 4.38** (correctness of Algorithm TangentNumbers from (4.63)). **Answer.** The
  algorithm is the recurrence (4.63) `p_{n,j} = (j−1) p_{n−1,j−1} + (j+1) p_{n−1,j+1}` run on the
  nonzero coefficients only, stored diagonally in one array. Since `p_{n,j} = 0` when `n + j` is
  even, `P_n` has only the coefficients `p_{n,j}` with `j ≡ n + 1 (mod 2)`, and the ones we want are
  `T_j = p_{2j−1,0}`. *Invariant.* Before pass `k` (`k = 2, …, m`) the array holds
  `T_1, …, T_{k−1}` in positions `1, …, k−1` and `A_j = p_{j+k−3, j−k+2}` in positions
  `j = k, …, m` (the coefficients on the diagonal `n − j = 2k − 5`); initially (`k = 2`)
  `A_j = p_{j−1, j} = (j−1)!` by `p_{n,n+1} = n!` (`coeff_tanDerivPoly_top`), which is the first
  loop `T_1 = 1`, `T_k = (k−1) T_{k−1}`. Pass `k` runs `j = k, …, m` in increasing order and sets
  `A_j ← (j−k) A_{j−1} + (j−k+2) A_j`; when position `j` is reached, `A_{j−1}` has already been
  replaced by `p_{j+k−3, j−k}` (for `j = k` this is `T_{k−1} = p_{2k−3,0}`, untouched) while `A_j`
  still holds `p_{j+k−3, j−k+2}`, so by (4.63) with `n = j+k−2` and index `j−k+1`:
  `(j−k) p_{j+k−3, j−k} + (j−k+2) p_{j+k−3, j−k+2} = p_{j+k−2, j−k+1}` (`tangentStep_eq_coeff`).
  After the pass the array holds `p_{j+k−2, j−k+1}` in positions `j ≥ k`, i.e. the diagonal
  `n − j = 2k − 3`, which is the invariant for `k + 1`; and position `k` now holds
  `p_{2k−2, 1} = p_{2k−1, 0} = T_k` by the `j = 0` case of (4.63) (`p_{n+1,0} = p_{n,1}`,
  `coeff_tanDerivPoly_succ_zero`), so it is finished and never touched again (`tangentPass_spec`,
  `tangentOuter_spec`). After pass `m` all positions hold `T_1, …, T_m`
  (`tangentNumbersModel_eq`, `algorithm_tangentNumbers_correct`). Each pass therefore advances the
  stored diagonal by one `n`-step for all `j` at once, using the in-place order of evaluation to
  supply the already-updated left neighbour, which is why the inner loop must run upwards in
  `j`. All quantities are nonnegative integers (`coeff_tanDerivPoly_nonneg`), so there is no
  cancellation and the algorithm is also usable in floating point with the stated relative
  accuracy. Cost: `∑_{k=2}^m (m − k + 1) ≈ m²/2` updates on integers of up to `∼ 2m lg m` bits
  (Exercise 4.37).
* **Exercise 4.39** (Algorithm TangentNumbers costs `O(m³ log m)`). **Answer.** The algorithm
  performs `∑_{k=2}^{m} (m − k + 1) = m(m−1)/2 ≈ m²/2` updates `T_j ← (j−k)T_{j−1} + (j−k+2)T_j`,
  each two multiplications of an array entry by a small integer (`< 2m`) and one addition, hence
  `O(log T)` bit operations by the exercise's assumption, where `T` is the size of the entries
  involved. Those entries are the intermediate coefficients `p_{n,i}` with `n = j + k − 3 ≤ 2m − 3`
  (Exercise 4.38), and they are bounded by the final sizes: `p_{n,i} ≤ P_n(1) = ∑_i p_{n,i}`
  (nonnegative coefficients, `coeff_tanDerivPoly_le_eval_one`), and `P_{n+1}(1) = P_n'(1)·2 ≤
  2(n+1)P_n(1)` because `P_n'(1) = ∑ i p_{n,i} ≤ (n+1)P_n(1)` (`deg P_n = n+1`), so
  `P_n(1) ≤ 2^n (n+1)!` (`eval_one_tanDerivPoly_le`). With Exercise 4.37's `size((n+1)!) ≤
  (n+1)(lg(n+1) + 1)` this gives every entry at most `n + (n+1)(lg(n+1) + 1) ≤ 2m(lg(2m) + 2)`
  bits (`size_coeff_tanDerivPoly_le`), i.e. `O(m log m)` — the same order as the final `T_m`
  (`∼ 2m lg m` bits, Exercise 4.37), as expected since `P_n(1) = (d/dx)^n tan(x)|_{x=π/4} ≈ n!(4/π)^n`
  and `T_j = p_{2j−1,0}` is the largest-order entry. Summing, the bit cost is at most
  `m² · 2m(lg(2m) + 2) = O(m³ log m)` (`tangentAlgorithmBits`, `tangentAlgorithmBits_le`). It is
  also `Ω(m³ log m)`: the last `≈ m²/8` updates (`j, k ≥ m/2`) act on entries of `Θ(m log m)` bits
  (`p_{n,i} ≥ p_{n,0}`-type lower bounds from `T_k ≥ (2k−1)!(4/π²)^k`), so the bound is tight; the
  output itself has `∑_j 2j lg j ≈ m² lg m` bits, and the factor `m` is the number of passes
  each entry goes through. (Faster: Exercise 4.47 / §4.12 mention `O(m² log^{2+ε} m)` methods via
  the zeta values or `B_{2k}` modulo primes; our `AzNat` implementation would use this `O(m³ log m)`
  algorithm since `m` is small, `≈ 0.35 n` for `Γ` at `n` bits, Exercise 4.21.)
* **Exercise 4.40** (Algorithm SecantNumbers). **Answer.** With `s = sec x`, `t = tan x`:
  `Ds = st`, `Dt = 1 + t²`, so `Dⁿ sec x = Q_n(tan x) sec x` with `Q_0 = 1` and
  `Q_{n+1} = t Q_n + (1 + t²) Q_n'` (`secDerivPoly`, `iteratedDeriv_sec`, proven like
  `iteratedDeriv_tan` with the product rule and `D(1/cos) = sin/cos²`), hence
  `S_k = D^{2k} sec(0) = Q_{2k}(0) = q_{2k,0}` (`secantNumber`, `iteratedDeriv_sec_zero`), the
  secant (Euler) numbers `1, 1, 5, 61, 1385, …`. Coefficients: `q_{n+1,j} = j q_{n,j−1} + (j+1) q_{n,j+1}`
  (the `t Q_n` term contributes `q_{n,j−1}`, `Q_n'` contributes `(j+1) q_{n,j+1}`, `t² Q_n'`
  contributes `(j−1) q_{n,j−1}`; `coeff_secDerivPoly_succ`, `_succ_zero`), nonnegative, `q_{n,j} = 0`
  for `j > n` and `q_{n,n} = n!` (`coeff_secDerivPoly_top`), `q_{n,j} = 0` for `n + j` odd. Compared
  with the tangent recurrence `p_{n+1,j} = (j−1) p_{n,j−1} + (j+1) p_{n,j+1}`, the first coefficient
  is `j` instead of `j−1`, which is exactly the difference between the two algorithms' inner
  updates (`(j−k) S_{j−1} + (j−k+1) S_j` against `(j−k) T_{j−1} + (j−k+2) T_j`). *Verification.*
  Invariant before pass `k` (`k = 1, …, m`): positions `j < k` hold `S_j`, position `j ≥ k` holds
  `q_{j+k−1, j−k+1}`, the diagonal `n − j = 2k − 2`. Initially (`k = 1`) `A_j = j! = q_{j,j}`, which
  is the first loop `S_0 = 1`, `S_k = k S_{k−1}`. Pass `k` runs `j = k+1, …, m` upwards and sets
  `A_j ← (j−k) A_{j−1} + (j−k+1) A_j`, where `A_{j−1}` already holds `q_{j+k−1, j−k−1}` (for
  `j = k+1` this is the untouched `A_k = q_{2k−1,1} = q_{2k,0} = S_k`) and `A_j` still holds
  `q_{j+k−1, j−k+1}`, so the update is the recurrence at `n = j+k−1`, index `j−k`:
  `(j−k) q_{n, j−k−1} + (j−k+1) q_{n, j−k+1} = q_{n+1, j−k}` (`secantStep_eq_coeff`). After the pass
  position `j ≥ k+1` holds `q_{j+k, j−k}`, the diagonal `n − j = 2k`, i.e. the invariant for
  `k + 1`, and position `k` holds `q_{2k−1,1} = q_{2k,0} = S_k` without needing an update — which
  is why the inner loop starts at `j = k+1`, one later than in Algorithm TangentNumbers
  (`secantPass_spec`, `secantOuter_spec`). After pass `m`, positions `0, …, m` hold `S_0, …, S_m`
  (`secantNumbersModel_eq`; `secantNumbersModel_three` checks `1, 1, 5, 61` by `decide`). As for
  the tangent numbers, everything is a nonnegative integer, `S_k ∼ 2(2k)!(2/π)^{2k+1}` has
  `∼ 2k lg k` bits (poles of `sec` at `±π/2`), and the algorithm costs `O(m³ log m)`.
* **Exercise 4.41** (Harvey: Bernoulli numbers by a power-series reciprocal in
  `O(n² (log n)^{2+ε})`). **Answer.** *Identity.* `x/(e^x − 1) = 1/E(x)` with
  `E(x) = (e^x − 1)/x = ∑_{k≥0} x^k/(k+1)!`, so `∑ B_k x^k/k! = E(x)^{−1}`
  (`bernoulliPowerSeries_mul_recipSeries`, from Mathlib's `B(x)(e^x − 1) = x` by cancelling `x`).
  *Algorithm.* Let `R(x) = ∑_{k≤n} r_k x^k` be `E^{−1} mod x^{n+1}`, `r_k = B_k/k!`.
  (1) Compute `R` by Newton's iteration for the reciprocal, `R_0 = 1`,
  `R_{j+1} = R_j (2 − E R_j) mod x^{2^{j+1}}`: if `R_j ≡ E^{−1} mod x^{2^j}` then
  `1 − E R_{j+1} = (1 − E R_j)²` is divisible by `x^{2^{j+1}}` (`newton_reciprocal_step`,
  `newton_reciprocal_step_dvd`), so `⌈lg(n+1)⌉` steps give `R`, and since each `R_j` is the exact
  truncation of `E^{−1}`, every intermediate coefficient is a true `r_k`. (2) Do the arithmetic on
  integers: the coefficients of `E` are `1/(k+1)!`, i.e. `E_int := (n+1)!·E mod x^{n+1} ∈ ℤ[x]` with
  coefficients `(n+1)!/(k+1)! = (k+2)⋯(n+1)` of `O(n log n)` bits; the coefficients of `R` have
  `den(B_k/k!) ∣ k!·den B_k` with `den B_k ∣ 4^k(4^k − 1)` (Ex. 4.37) — in fact
  `(B_k/k!)·k!·den B_k = num B_k` (`scaled_coeff_eq_num`) — so with `L := n!·4^n·(4^n − 1)` (or
  simply `L := n!(n+1)!`, as `den B_k` is squarefree with primes `≤ k+1`) the series
  `S := L·R mod x^{n+1}` is in `ℤ[x]` with coefficients `|s_k| ≤ L` of `O(n log n)` bits. The
  Newton step in scaled form is `S_{j+1} = (2 L S_j − E_int S_j²) / ((n+1)!·L)` truncated to
  `2^{j+1}` terms, where the division is exact (the result is the integer `L R_{j+1}`); it costs
  two polynomial products of length `≤ 2^{j+1} ≤ 2n` with `O(n log n)`-bit coefficients plus
  `O(n)` exact divisions of `O(n log n)`-bit integers. (3) Recover `B_k = k!·s_k/L`, `n` exact
  divisions. *Cost.* A product of two polynomials of length `≤ 2n` with `b = O(n log n)`-bit
  coefficients is one integer multiplication of `O(n·b) = O(n² log n)` bits by Kronecker
  substitution (pack the coefficients at `2b + lg n` bits), i.e. `M(n² log n)`; the Newton steps
  have geometrically growing lengths so their total is `O(M(n² log n))`; the `O(n)` exact
  divisions and the final `k!·s_k/L` cost `O(n M(n log n)) = O(n² log n · polylog)`, dominated. With
  `M(m) = O(m log m · 2^{O(log* m)})` (or `m log m log log m`), `M(n² log n) = O(n² log n · log(n² log n)
  · loglog) = O(n² (log n)^{2+ε})`; in the quasi-linear model exactly `M(n² lg n) ≤ 3 n² (lg n)²`
  (`quasiLinearCost_sq_log_le`, using `lg(n² lg n) = 2 lg n + lg lg n ≤ 3 lg n`). This beats the
  `O(n³ log n)` of the recurrences (4.58)–(4.60) and Algorithm TangentNumbers (Ex. 4.39) and is
  quasi-optimal, since the output `B_0, …, B_n` itself has `Θ(n² log n)` bits (Ex. 4.37). *Remarks.*
  (i) Numerically the scaled Newton iteration is exact integer arithmetic, so there is no stability
  issue, unlike (4.59). (ii) Only the even `B_{2k}` are nonzero (`B_1 = −1/2`), so one may instead
  invert `∑ x^k/(2k+1)!` (the series `sinh(√x)/√x`) in the variable `x²`, halving the lengths, which
  is (4.60)'s generating function `(x/2)/tanh(x/2)` in disguise. (iii) The same reciprocal gives
  the tangent numbers through (4.62), or directly from `tan = sin/cos` by one series division.
  (iv) Harvey's own multimodular algorithm computes a single `B_n` in `O(n² (log n)^{2+ε})` with
  `O(n log n)` space by working modulo many word-size primes with the `(4.59)`-type sum over
  `ℤ/p` and CRT; the power-series version above computes all of `B_0, …, B_n` in the same time.
* **Exercise 4.42** (Algorithm SeriesExponential; Stirling's series for `n!`). **Answer.**
  *(a)* Let `A = ∑_{k≥1} a_k x^k` and let `B = ∑ b_k x^k` be the output. The recurrence
  `k b_k = ∑_{j=1}^k j a_j b_{k−j}` is exactly the coefficient of `x^{k−1}` in `B' = A' B`
  (`derivative_mk_seriesExp`): `(k b_k) = [x^{k−1}](A'B) = ∑_{j} (j a_j)(b_{k−j})`. Together with
  `b_0 = 1` this is the ODE `B' = A'B`, `B(0) = 1`, whose unique formal solution is `exp A`
  — indeed `(log B)' = B'/B = A'` and `log B` has zero constant term, so `log B = A` in the sense
  of Exercise 4.1 (`logSeries_mk_seriesExp`, from `logSeries_unique`). Since `b_k` involves only
  `a_1, …, a_k`, the first `m+1` output coefficients depend only on `a_1, …, a_m`, so
  `B = exp(A) + O(x^{m+1})`. Cost: `∑_k k = O(m²)` multiplications (or `O(M(m))` by a Newton
  iteration for the exponential, Exercise 4.1 / §4.2.3, when `m` is large). Numerically the
  algorithm is the same forward recurrence as for the reciprocal and inherits its stability only
  when the coefficients do not alternate wildly; here (b) the `a_j` alternate and grow, so the
  `b_k` suffer the same `4^k`-type amplification as (4.59) if computed in floating point —
  compute them exactly as rationals.
  *(b)* From (4.38), `ln Γ(z) = (z − ½) ln z − z + ½ ln(2π) + ∑_{k≥1} B_{2k}/(2k(2k−1)) z^{−(2k−1)}`,
  so `Γ(z) = √(2π) z^{z−½} e^{−z} exp(A(1/z))` with `A(x) = ∑_{k≥1} a_{2k−1} x^{2k−1}`,
  `a_{2k−1} = B_{2k}/(2k(2k−1))`, `a_{2k} = 0` (`stirlingLogCoeff`; `stirlingTerm_eq_stirlingLogCoeff`
  identifies the terms of (4.38) with `a_j/x^j`), and `n! = n Γ(n) = (n/e)^n √(2πn) exp(A(1/n))`.
  Hence the `b_k` of `n! ∼ (n/e)^n √(2πn) ∑ b_k/n^k` are produced by SeriesExponential applied to
  `a_1 = 1/12, a_2 = 0, a_3 = −1/360, a_4 = 0, a_5 = 1/1260, …` (`stirlingCoeff`):
  `b_0 = 1`, `b_1 = 1/12`, `b_2 = 1/288`, `b_3 = −139/51840`, `b_4 = −571/2488320`, …
  (`stirlingCoeff_zero/one/two/three`), the classical Stirling coefficients. The Bernoulli inputs
  come from §4.7.2 (tangent numbers and (4.62)) or Exercise 4.41, and the `O(m²)` rational
  operations of the exponential are negligible next to computing them; as an asymptotic series
  the result is again divergent, with the same `k ≈ πn` optimal truncation and `≈ e^{−2πn}`
  accuracy floor as (4.38), because `exp` of the asymptotic series is the asymptotic series of
  `exp` (`b_k ∼ (−1)^{…}(2k−2)!/(2π)^{2k} ·` const, from the nearest singularities).
  *(c)* Not for high precision. (i) The series `∑ b_k/x^k` is no more accurate than (4.38): its
  attainable precision is still `≈ 2πx` bits at the same number of terms, so the argument shift
  `x ↦ x + δ` of Exercise 4.21 is needed anyway, and the shift is natural for `ln Γ` (a sum of
  `δ` logarithms, or one product `∏(x+i)` followed by one `ln`) but not for `Γ` directly. (ii) What
  it saves is one `exp` evaluation, `O(M(n) log n)`, which is negligible next to the
  `O(n M(n))` of the `≈ 0.35n` series terms (Exercise 4.21); in exchange the `b_k` are harder to
  obtain than the `B_{2k}` (one more `O(m²)` pass over `O(m log m)`-bit rationals, with
  denominators `12, 288, 51840, 2488320, …` growing like `(2k)!·2^{O(k)}`), they have no closed
  form or integer recurrence like (4.62)/(4.63), and the series in `1/x` has all powers (odd and
  even), twice as many terms as (4.38) for the same accuracy. (iii) Error control is worse: in
  the `ln Γ` form the remainder bound of (4.38) (first omitted term, same sign) translates
  directly into a relative error of `Γ` (Exercise 4.21), while the exponentiated series has no
  such simple remainder estimate. (iv) The exponentiated form offers nothing for the
  cancellation-free evaluation of `1/Γ` or for complex `z` (Exercise 4.22). Where it *is* useful:
  fixed low precision (double/quad), where a handful of precomputed `b_k` evaluate `Γ` or `n!`
  with one Horner scheme and no `exp`/`ln` call (the classical Stirling formula with correction
  terms), and for exact combinatorial asymptotics of `n!` where the rational `b_k` are wanted as
  such. For `AzFloat` the `ln Γ` route of Exercise 4.21 stays the plan.
* **Exercise 4.43** (second-order AGM logarithm, `x ≥ 2^{n/4}`). **Answer.** *Expansion.* Write
  `L = ln(4/k)`, `K = K(k)`, `K' = K(k') = (π/2)/AGM(1,k)` (4.68). From (4.69)
  `K = (π/2)(1 + k²/4) + ε₁`, `|ε₁| ≤ A k⁴`, and (4.70) `K' = (2/π) L K − k²/4 + ε₂`,
  `|ε₂| ≤ B k⁴`: `K' = L(1 + k²/4) − k²/4 + (2/π)Lε₁ + ε₂`, and solving for `L` to second order,
  `L = (1 − k²/4) K' + k²/4 + E`, exactly `E = (L − 1)k⁴/16 − (1 − k²/4)((2/π)Lε₁ + ε₂)`, so
  `|E| ≤ k⁴((1/16 + 2A/π) L + 1/16 + B) = O(k⁴ ln(4/k))` (`second_order_deduction`). The proven
  (4.69) bound `(π/2)(1 + k²/4) ≤ K ≤ (π/2)(1 + k²/4 + 3k⁴/8)` (`ellipticK_bounds`, `k² ≤ 1/2`) gives
  `A = 3π/16`, hence `|E| ≤ k⁴((7/16) L + 1/16 + B)` (`second_order_expansion`); the second-order
  constant `B` of (4.70) is not proven (only the first order is, `abs_ellipticK_sqrt_sub_log_le`),
  so it enters as a hypothesis; the classical expansion `K' = (2/π)K ln(4/k) − k²/4 − 21k⁴/128 − …`
  gives `B ≈ 21/128`. *Effective bound ("any means").* Numerically, with double-precision AGM:

  | `k` | `E/k⁴` | `−(5/64) ln(4/k) + 13/128` |
  |---|---|---|
  | `1/2` | `−0.0767` | `−0.061` |
  | `1/8` | `−0.1714` | `−0.169` |
  | `1/32` | `−0.2777` | `−0.278` |
  | `1/128` | `−0.3858` | `−0.386` |
  | `1/256` | `−0.4400` | `−0.440` |

  so `E = −(5/64) k⁴ ln(4/k) + (13/128) k⁴ + O(k⁶ ln k)`, in agreement with the series
  (`−k⁴/16 + Lk⁴/16 − (9/64)Lk⁴ + 21k⁴/128 = (−5L/64 + 13/128)k⁴` from `ε₁ ≈ (9π/128)k⁴`,
  `ε₂ ≈ −21k⁴/128`), and the effective bound `|E| ≤ (5/64) k⁴ ln(4/k)` holds for `0 < k ≤ 1/2`
  (the two terms have opposite signs and `13/128 < (5/64) ln 8`). *Algorithm.* With `k = 4/x`:
  `ln x = (1 − 4/x²)·(π/2)/AGM(1, 4/x) + 4/x² + E`, `|E| ≤ (5/64)(4/x)⁴ ln x = 20 ln x/x⁴`
  (`agmLog2`, `abs_agmLog2_sub_log_le` with `c₁ = 5/64`, `c₂ = 0`, for `x ≥ 8`); the correction costs
  one extra multiplication and two cheap operations on top of the first-order formula (4.71), and
  the AGM itself is unchanged. For `n` bits one needs `20 ln x / x⁴ ≤ 2^{−n}`, i.e.
  `x⁴ ≥ 20 (ln x) 2^n` (`agmLog2_precision`: `256(c₁ ln x + c₂)2^n ≤ x⁴`), which holds as soon as
  `x ≥ 2^{n/4} (20 ln x)^{1/4}`, e.g. `x ≥ 2^{n/4 + 2}` for all `x ≤ 2^{2^{8}}`: **`x ≳ 2^{n/4}`**
  instead of the `x ≳ 2^{n/2}` of (4.71). So: scale `x ← 2^ℓ x` (or square `ℓ` times) only up to
  `2^{n/4}` rather than `2^{n/2}`, run the AGM with `k = 4/x ≥ 2^{2−n/4}` (`≈ lg(n/4) + lg n`
  iterations instead of `lg(n/2) + lg n`, one fewer, by `agm_log_iterations`), and finish with
  the second-order correction; the saving is one AGM iteration and half the shift, i.e. a few
  percent — the real gain of the next step, the exact theta formula of §4.8.3/§4.8.4
  (`sasaki_kanada`), is that *no* truncation error remains and `k` can be `O(1)`, which is why
  that is the planned `AzFloat` route. (In the same way (4.69)/(4.70) to order `k^{2m}` would give
  `x ≥ 2^{n/(2m)}`, at the price of the full expansions of `K` and `K'`.)
* **Exercise 4.44** (`π` and `ln 2` from (4.71)). **Answer.** (4.71) in its proven form is
  `|(π/2)/AGM(1,k) − ln(4/k)| ≤ (k²/4)(2 − ln k)` for `0 < k ≤ 1` (`abs_pi_div_AGM_sub_log_le`,
  (4.73)). Two evaluations of the *same* kind do not separate `π` from `ln 2`: at `x = 2^m` and
  `x = 2^{2m}` both sides are proportional to `(2/π) ln 2`, and the ratio is exactly `2`. One of
  the two logarithms must be known exactly, and the natural choice is `ln e^j = j`: `e^j` for an
  integer `j` is cheap (the exponential series by binary splitting, §4.9, `O(M(n) log² n)`, or
  `e` once and `j` squarings/multiplications). *`π`.* Turn (4.71) around: `π ≈ 2 ln(4/k)·AGM(1,k)`
  with `|2 ln(4/k) AGM(1,k) − π| ≤ 2 AGM(1,k)·(k²/4)(2 − ln k) ≤ (k²/2)(2 − ln k)` (as `AGM(1,k) ≤ 1`,
  `abs_two_mul_log_mul_AGM_sub_pi`); with `k = 4e^{−j}`, i.e. `x = e^j`, this is
  `|2j · AGM(1, 4e^{−j}) − π| ≤ 8 e^{−2j}(j + 2 − ln 4)` (`abs_pi_approx_exp`), so `j ≈ (n ln 2)/2 +
  ½ lg j ≈ 0.35n` gives `π` to `n` bits with one AGM of `≈ 2 lg n` iterations (`agm_log_iterations`)
  and one exponential; the error of `e^j` enters linearly (a relative error `δ` in `e^j` is an
  absolute error `δ` in the "known" logarithm, hence `≤ 2δ` in `π`). *`ln 2`.* With `π` in hand,
  (4.71) at `x = 2^m` gives `|(π/2)/(m·AGM(1, 2^{2−m})) − ln 2| ≤ 4^{2−m}(2 + (m − 2) ln 2)/(4m)`
  (`abs_log_two_approx`), so `m ≈ n/2 + 2` suffices; an approximate `π̃` with `|π̃ − π| ≤ δ`
  adds `δ/(2m·AGM(1, 2^{2−m}))` (`abs_log_two_approx_of_pi`), and since
  `AGM(1,k) ≥ (π/2)/(ln(4/k) + (k²/4)(2 − ln k))` (`pi_div_two_div_le_AGM`) this is
  `≈ δ·(m ln 2)/(π m) = 0.22 δ`: no loss. Both constants therefore cost two AGMs plus one
  exponential, `O(M(n) log n)` each (the exponential by binary splitting is `O(M(n) log² n)` but
  with a small constant), the same order as Brent–Salamin for `π` (which needs no exponential and
  no truncation error, via the Legendre relation (4.72), `legendre_relation`) — the exercise's
  method is mainly of interest because the AGM logarithm code then provides its own constants.
  Alternatives: `ln 2` directly from `x = 2^m` once `π` is known by any means; or `π` from
  `ln 2` by the same formula if `ln 2` is known (e.g. from the series `∑ 1/(k 2^k)` or
  Machin-like formulas, §4.9); the second-order formula of Exercise 4.43 halves the required `j`
  and `m`. For `AzFloat` the plan is Brent–Salamin for `π` (proven Legendre relation) and the
  exact theta-function logarithm (§4.8.3) for `ln 2`, with these (4.71)-based formulas as
  cross-checks.
* **Exercise 4.45** ((A) or (B) for `2θ₂θ₃` and `θ₂² + θ₃²`). **Answer.** Both methods are
  algebraically correct (`methodA_eq`, `methodB_eq`: `(θ₂+θ₃)² − 2θ₂θ₃ = θ₂² + θ₃²`,
  `((θ₂+θ₃)² ± (θ₂−θ₃)²)/2`), and both use two non-scalar products — (A) one squaring and one
  general product, (B) two squarings, so (B) is marginally cheaper (a squaring is `≈ 2/3` of a
  product). Numerically they differ sharply. In the second AGM algorithm (§4.8.4) `q` is small
  (`q = 1/x`, or `q^4` after the `q ↦ q^4` trick, down to `2^{−n/36}`), so `θ₃(q) = 1 + 2q + ⋯ ≈ 1`
  while `θ₂(q) = 2q^{1/4}(1 + q² + ⋯) ≪ 1` (`one_le_theta3`, `theta2_le_two_rpow_div`:
  `θ₂ ≤ 2q^{1/4}/(1 − q)`). *(A).* `2v = 2θ₂θ₃` is a product of positive numbers, exact to relative
  precision; `u − 2v = θ₂² + θ₃²` subtracts `2θ₂θ₃ ≤ θ₂² + θ₃²` from `u = θ₂² + θ₃² + 2θ₂θ₃ ≤ 2(θ₂² +
  θ₃²)`, so relative errors `ε` in `u, v` give an absolute error `≤ 3ε(θ₂² + θ₃²)`
  (`methodA_relError_le`): at most `lg 3 < 2` bits lost, and in the regime `θ₂ ≪ θ₃` essentially
  none. *(B).* `(u + w)/2 = θ₂² + θ₃²` is a sum of positive terms, fine; but
  `(u − w)/2 = 2θ₂θ₃` is the difference of two nearly equal squares `u ≈ w ≈ θ₃²`: with relative
  errors `±ε` the absolute error is `ε(θ₂² + θ₃²)` exactly (`methodB_amplification`), a relative
  error `ε(θ₂² + θ₃²)/(2θ₂θ₃) ≥ ε θ₃/(2θ₂) ≥ ε(1 − q)/(4q^{1/4})`, i.e. a loss of
  `¼ lg(1/q) − 2` bits — for `q ≈ 2^{−n/36}` that is `n/144` bits, and for the unshifted
  `q = 1/x ≈ 2^{−n}` a quarter of the precision. Since `2θ₂θ₃` is precisely the geometric mean
  `b₁` of the AGM started at `(θ₃², θ₂²)` (the pair `((θ₂²+θ₃²)/2, θ₂θ₃)` is the first AGM step done
  without a square root, which is the point of the remark), and the AGM then converges
  quadratically from these values, an error in `b₁` is carried through to `ln(1/q) =
  π/AGM(θ₂², θ₃²)` undamped. **Method (A) is preferable**; its one extra general product (instead
  of a squaring) costs `≈ M(n)/3`, far less than the `¼ lg(1/q)` guard bits (B) would need, and the
  `AzFloat` implementation of `sasaki_kanada'` should compute `v = θ₂θ₃` directly and
  `θ₂² + θ₃² = u − 2v` (or, equally well, `θ₂² + θ₃²` directly as two squarings plus `v`, three
  non-scalar products, if the `≤ 2`-bit loss of (A) is to be avoided too).
* **Exercise 4.46** (improving the constants of Table 4.1). **Answer.** Table 4.1 counts, in the
  FFT model where a real product is three transforms of cost `M(n)/3` each (`fftCost`): real
  squaring `2/3`, product `1`, reciprocal `13/9 ≈ 1.444`, division `5/3 ≈ 1.666`, square root
  `4/3 ≈ 1.333`, AGM iteration `2`, `ln` via AGM `4 lg n`; complex squaring `4/3`, product `2`,
  reciprocal `31/9 ≈ 3.444`, division `43/9 ≈ 4.777`, square root `16/3 ≈ 5.333`, AGM iteration
  `20/3 ≈ 6.666`, `ln` via AGM `(40/3) lg n`. *Real column.* The reciprocal and square-root
  constants are Harvey's (2011: `1.444` from Bernstein's `1.5`, `1.333` from `1.833`) and the
  division `5/3 = 13/9 + 2/9` (one extra wrapped product) follows; improving them further is a
  research question (they rest on which transforms a Newton step can share), and we do not
  attempt it here. The entries that *can* be sharpened by bookkeeping are the ones below the
  line, but note first how the complex column was obtained: through `|z|² = a² + b²`. Complex
  reciprocal: `a² + b²` with the transforms of `a, b` shared (`2 + 1` transforms, cost `1`), a real
  reciprocal `r` (`13/9`), then `a r` and `b r` from the stored transforms and one transform of
  `r` (`1 + 2`, cost `1`): total `31/9` (`complex_reciprocal_via_norm`); complex division
  `= reciprocal + complex product = 31/9 + 2 = 43/9 ... ` with the shared transforms; complex square
  root through `x = √((|z| + a)/2)`, `y = b/(2x)`: `|z|²` (`1`) + three square roots or two plus a
  division (`4/3 + 4/3 + 5/3`) `= 16/3` (`complex_sqrt_via_norm`); AGM iteration = complex product
  + complex square root `= 2 + 16/3 − 2/3` (sharing) `≈ 20/3`; `ln z` = `2 lg n` iterations
  `= (40/3) lg n`. *Improvement: do Newton over `ℂ` directly.* In the transform model a complex
  product costs exactly twice a real one (`4 + 2` against `2 + 1` transforms,
  `fftCost_complex_mul_eq_two_mul`) and a complex squaring exactly twice a real squaring (`2 + 2`
  against `1 + 1`, `fftCost_complex_sq_eq_two_mul`; both via `(a+b)(a−b) + 2abi`). A Newton
  iteration is a fixed pattern of products, squarings and additions with the same transform
  reuse in `ℂ` as in `ℝ` (the complex transform of `a + ib` is the pair of real transforms of
  `a` and `b`), so every real Newton constant doubles and nothing else changes: complex reciprocal
  `2 · 13/9 = 26/9 ≈ 2.889` (against `3.444`, `complex_reciprocal_improved`), complex division
  `2 · 5/3 = 10/3 ≈ 3.333` (against `4.777`, `complex_division_improved`), complex square root
  `2 · 4/3 = 8/3 ≈ 2.667` (against `5.333`, exactly half, `complex_sqrt_improved`), complex AGM
  iteration `2 · 2 = 4` (against `6.666`, `complex_agm_iteration_improved`), and `ln z` via the
  complex AGM `4 · 2 lg n = 8 lg n` (against `13.333 lg n`, `complex_log_improved`), i.e. the
  complex column becomes exactly twice the real column throughout, and the complex square root
  and AGM-based logarithm run in `60 %` of the table's time. (The complex Newton iterations
  converge for the principal branch, `z ∉ (−∞, 0]`, from the standard starting values, and the
  square root of positive real part is what the complex AGM needs, §4.8.5.) Further small gains:
  the `|z|²` route for the reciprocal can reuse the transforms of `a, b` in the final products
  *and* in `a² + b²`, already counted; a complex squaring inside Newton can use the three-real-
  product form when transforms cannot be cached; and for `arctan x = ℑ ln(1 + ix)` only the
  imaginary part of the result is needed, which saves the last backward transform (`1/3`). None
  of this changes the asymptotic `O(M(n) log n)`; the point of the table is the constant factor,
  and the doubling principle is the clean statement: `complex = 2 × real` once one stops going
  through `|z|²`.
* **Exercise 4.47** (justify (4.80); bound `α` when `M(n) = Θ(n^c)`, `c ∈ (1,2]`) — section
  `Exercise447` of `Exercises.lean`. **Answer.** Binary splitting of a sum of `n` terms whose
  partial products have `O(n lg n)`-bit numerators/denominators (`log_arctanDen_le`) is a tree of
  depth `⌈lg n⌉`; level `k` performs `2^k` products of `≈ n lg n/2^k`-bit numbers, so the total
  cost is `∑_{k=1}^{⌈lg n⌉} 2^k M(n lg n/2^k)`, which is (4.80). For quasi-linear `M` each level
  costs at most `2 lg n · M(n)` and there are `≤ lg n + 1` levels, giving `≤ 4 (lg n)² M(n)`,
  i.e. `α = 2` (`binary_splitting_cost`, already in `BinarySplitting.lean`). For
  `M(m) = m^c` with `1 < c ≤ 2` the level cost is `2^k (N/2^k)^c = N^c (2^(1−c))^k`
  (`two_pow_mul_div_rpow`), a geometric series with ratio `2^(1−c) < 1`, so the whole sum is
  `≤ N^c · 2^(1−c)/(1 − 2^(1−c))` for every depth (`binary_splitting_cost_pow`, via Mathlib's
  `geom_sum_Ico_le_of_lt_one`); with `N = n lg n` this is `(lg n)^c · n^c · 2^(1−c)/(1 − 2^(1−c))
  = O((lg n)^c M(n))` (`binary_splitting_cost_pow_eq`). Hence `α = c`, and `α ≤ 2` since
  `(lg n)^c ≤ (lg n)²` for `n ≥ 2` (`rpow_logb_le_sq`); the top level dominates (the
  constant is `2^(1−c)/(1 − 2^(1−c))`, e.g. `1` for Karatsuba-free `c = 2`, `≈ 1.4` for `c = lg 3`).
  Not formalized: `Θ` rather than exact `n^c`, and the `⌈lg n⌉`-level tree shape itself (the
  bound holds for any depth `L`).
* **Exercise 4.48** (Salvy: is `exp(x²) + x/(1 − x²)` holonomic?) — section `Exercise448` of
  `Exercises.lean`. **Answer.** Yes. A function is holonomic (D-finite) when it satisfies a
  linear ODE with polynomial coefficients (`IsHolonomicOn`, on an open set, leading coefficient
  nonzero). Both summands are: `f = exp(x²)` satisfies `f' − 2x f = 0` (`exp_sq_ode`) and the
  rational `g = x/(1 − x²)` satisfies `x(1 − x²) g' − (1 + x²) g = 0` (`ratPart_ode`), and
  holonomic functions form a vector space (the derivatives of `f + g` lie in the `ℝ(x)`-span of
  `f, …, f^{(r−1)}, g, …, g^{(s−1)}`, so `r + s + 1` of them are dependent). Concretely, with
  `f'' = (2 + 4x²) f`, `g' = (1 + x²)/(1 − x²)²`, `g'' = 2x(3 + x²)/(1 − x²)³`, eliminating gives
  the order-2 annihilator `(1−x²)(1−x²+2x⁴) h'' − 2x(2+x²+3x⁴−2x⁶) h' + 2(2x⁶+3x⁴+4x²−1) h = 0`
  on `{x | x² ≠ 1}` (`salvyFun_ode`, packaged as `salvyFun_isHolonomicOn` with
  `iteratedDeriv`; `deriv_deriv_salvyFun` uses eventual equality on the open set
  `isOpen_sq_ne_one`). The point of the exercise: the Taylor coefficients are `1/m!` at even
  index `2m` and `1` at odd index — two interleaved sequences with no hypergeometric ratio
  `u_{k+1}/u_k` — yet they satisfy a linear recurrence with polynomial coefficients (read off the
  ODE), so the function is in the §4.9.2 binary-splitting class even though no §4.9.1 ratio form
  exists. Not formalized: the general closure of holonomic functions under addition and the
  coefficient recurrence.
* **Exercise 4.49** (van der Hoeven, Mezzarobba: improve Theorem 4.2 to `O(M(n) log² n)`) —
  section `Exercise449` of `Exercises.lean`. **Answer.** Theorem 4.2's proof charges each of the
  `⌈lg n⌉ + 1` bit-burst steps the full (4.80) cost `O(M(n) log² n)`, using the uniform size
  estimate `O(ℓ(2^i + log ℓ)) = O(n log n)` bits at the root of every product tree. The
  improvement is a sharper per-step accounting. Step `i` sums `N_i ≈ n/2^i` terms (precisely
  `(n + O(log n))/(2^i − O(1)) + 1`, since `|r_{i+1}| < 2^{1−2^i}` and the translated Taylor
  coefficients grow at most geometrically with a polynomial factor), and its recurrence
  coefficients have `2^i + O(log N_i)` bits, so the root of the tree has `S_i = N_i(2^i + lg N_i)
  = O(n + (n/2^i) lg n)` bits (`burstStepSize n i = n + n lg n/2^i`), and the binary splitting
  costs `≤ (lg n + 1) M(S_i)` (`binary_splitting_levels_le`, from
  `two_pow_mul_quasiLinearCost_div_le`). Only the first `lg lg n` steps have `S_i ≫ n`, and
  their sizes halve: with `M(a + b) ≤ 4(M(a) + M(b))` for `a ≥ 2, b ≥ 1`
  (`quasiLinearCost_add_le`: `a + b ≤ 2 max`, `M(2m) ≤ 4M(m)`), `M(m/2^i) ≤ M(m)/2^i`
  (`quasiLinearCost_div_two_pow_le`) and `M(n lg n) ≤ 2 lg n M(n)`
  (`quasiLinearCost_natCast_mul_logb_le`), `∑_{i≤L} M(S_i) ≤ (4(L+1) + 16 lg n) M(n)` when
  `2^L ≤ n lg n` (`sum_quasiLinearCost_burstStepSize_le`, via Mathlib's `sum_geometric_two_le`),
  hence the total `∑_{i≤⌈lg n⌉} (lg n + 1) M(S_i) ≤ 56 (lg n)² M(n)` for `n ≥ 4`
  (`bit_burst_cost`), i.e. `O(M(n) log² n)`. (The first step, the plain Taylor series at `0`, is
  exactly (4.80) and is the dominant one; the last steps have `2^i`-bit coefficients but only
  `O(1 + log n/2^i)` terms each.) Not formalized: the term count `N_i` and the coefficient-size
  estimate themselves (recorded as the cost model), and the exact cost of the initial-value
  multiplications (`O(M(n))` per step, absorbed).
* **Exercise 4.50** (partial fractions for `1/(z^k − 1)`; `S_{j,k}` as a contour integral;
  deduce (4.85)) — section `Exercise450` of `Exercises.lean`. **Answer.** With `w = e^(2πi/k)`
  and `z^k ≠ 1`: `z^k − 1 = (z − w^m) ∑_{i<k} z^i w^(m(k−1−i))` for every `m`, so
  `∑_m w^m/(z − w^m) = (1/(z^k − 1)) ∑_{i<k} z^i ∑_m (w^(k−i))^m`, and by orthogonality of the
  roots of unity only `i = 0` survives, giving `k/(z^k − 1)` (`sum_primitiveRoot_div_eq`, via
  Mathlib's `geom_sum₂_mul` and the module's `sum_zpow_primitiveRoot`). For `f` holomorphic on
  `|z| ≤ R` with `R > 1` (the contour `C'` of §4.10 is `|z| = R`, inside the disc of analyticity
  and enclosing the `k`-th roots of unity) and `j < k`, write `z^(k−j−1)/(z^k − 1) · f(z) = (1/k)
  ∑_m w^m · z^(k−j−1) f(z)/(z − w^m)`; Cauchy's formula gives `(2πi)⁻¹ ∮ z^(k−j−1) f(z)/(z − w^m)
  dz = w^(m(k−j−1)) f(w^m)` (Mathlib `DifferentiableOn.circleIntegral_sub_inv_smul`), and
  `w^m · w^(m(k−j−1)) = w^(−jm)` since `w^(mk) = 1`, so `S_{j,k} = (1/k) ∑_m f(w^m) w^(−jm) =
  (2πi)⁻¹ ∮_{C'} z^(k−j−1)/(z^k − 1) f(z) dz` (`aliasSumFun_eq_circleIntegral`; `aliasSumFun` is
  (4.84) for a function and `aliasSum_eq_aliasSumFun` relates it to the series form of
  `ContourIntegration.lean`). Equivalently: the residues of `z^(k−j−1) f(z)/(z^k − 1)` at the
  simple poles `w^m` are `w^(m(k−j−1)) f(w^m)/(k w^(m(k−1))) = w^(−jm) f(w^m)/k`. Subtracting
  (4.83) `a_j = (2πi)⁻¹ ∮_{C'} f(z) z^(−j−1) dz` (`cauchyCoeff`; `hasSum_cauchyCoeff` shows these
  are the Taylor coefficients, generalizing the module's `hasSum_cauchy_coeff` to radius `R`):
  `z^(k−j−1)/(z^k − 1) − z^(−j−1) = z^(−j−1)/(z^k − 1)`, so `S_{j,k} − a_j = (2πi)⁻¹ ∮_{C'}
  f(z)/(z^(j+1)(z^k − 1)) dz` (`aliasSumFun_sub_cauchyCoeff`). On `|z| = R > 1`, `1/(z^k − 1) =
  ∑_{l≥1} z^(−lk)` uniformly, and dominated convergence (bound `R·max|f|·(R^(−k))^l`,
  `intervalIntegral.hasSum_integral_of_dominated_convergence`) exchanges sum and integral
  (`hasSum_circleIntegral_div_pow`), giving (4.85) `S_{j,k} − a_j = ∑_{l≥1} a_{j+lk}`
  (`aliasSumFun_sub_cauchyCoeff_eq_tsum`): `k` sample points cannot distinguish `a_j` from
  `a_{j+k}, a_{j+2k}, …` (aliasing). Everything is formalized; `R` is any radius in `(1, R_f)`.
* **Exercise 4.51** (`S_{2j,k}` with about `k/4` evaluations of `f` for even `k`, `k/2` for odd
  `k`; improved error for odd `k`) — section `Exercise451` of `Exercises.lean`. **Answer.** The
  function `f(z) = z/(e^z − 1) + z/2` of (4.86) is even and has real Taylor coefficients, so
  `f(conj z) = conj f(z)` and `f(−z) = f(z)`. With `w = e^(2πi/k)`: `conj w = w⁻¹`
  (`conj_exp_two_pi_div`), so `f(w^(k−m)) = conj f(w^m)` and every sample value `f(w^m)`,
  `m < k`, is `f(w^r)` or `conj f(w^r)` for some `r ≤ k/2` (`sample_reduce_conj`; this uses only
  the conjugation symmetry and holds for every `k`): about `k/2` evaluations, the rest by
  conjugation, and `S_{2j,k} = (1/k)(f(1) + 2 ∑_{0<m<k/2} Re(f(w^m) w^(−2jm)))` for odd `k`. For
  even `k`, `w^(k/2) = −1` (`exp_two_pi_div_pow_half`) so `f(w^(m+k/2)) = f(−w^m) = f(w^m)`
  halves the range to `m < k/2`, and then conjugation `f(w^(k/2−m)) = conj f(w^(k/2+m))
  = conj f(w^m)` folds `[0, k/2)` onto `[0, k/4]`: every sample is `f(w^r)` or `conj f(w^r)`
  with `r ≤ k/4` (`sample_reduce_even`), about `k/4` evaluations (the values at `m = 0, k/2`
  and, for `4 ∣ k`, `m = k/4` are real). Improved error for odd `k`: by (4.87),
  `S_{2j,k} − B_{2j}/(2j)! = ∑_{l≥1} a_{2j+lk}`, and for odd `k` the index `2j + lk` is odd
  exactly when `l` is odd, where `a_{2j+lk} = 0` (`bernoulliCoeff_odd`); the surviving terms
  `l = 2i` are `∑_{i≥1} a_{2j+i·2k}`, i.e. `S_{2j,k} = S_{2j,2k}` (`bernoulli_aliasSum_odd`,
  by Mathlib's `tsum_even_add_odd`; conceptually the `2k`-th roots of unity are the `k`-th roots
  and their negatives, on which the even `f` takes the same values). Hence the error is
  `O((2π)^(−2k))`: `‖S_{2j,k} − B_{2j}/(2j)!‖ ≤ (π²/6)(2π)^(−2k)/(1 − (2π)^(−2k)) ·
  ‖B_{2j}/(2j)!‖` (`norm_bernoulli_aliasSum_sub_le_odd`). So an odd `k` with about `k/2`
  evaluations gives the accuracy of `2k` points, which is as good per evaluation as the even
  case (`k/4` evaluations for `(2π)^(−k)`). `bernoulliCoeff_conj` records that the coefficients
  are real. Not formalized: the explicit real-part form of the sum (a direct rewrite of
  `sample_reduce_conj`), and the symmetries of the analytic function `f` itself (the module works
  with the coefficient series, where they are `bernoulliCoeff_odd`/`bernoulliCoeff_conj`).

## Brent–Salamin for `π` (started 2026-10-18)

Plan (six items, see the session of 2026-10-18): (1) Gauss's formula for `E` along the AGM;
(2) Salamin's formula `π = 4 AGM(1, 1/√2)²/(1 − ∑_{j≥1} 2^(j+1) c_j²)` (algebra from (1),
`legendre_relation_sqrt_half`, `one_div_AGM_one`); (3) the iterate `π_N` and an explicit error
bound in terms of the computed gap `a_N − b_N`; (4) directed-rounding enclosure lemmas for
`AzFloat` add/sub/mul/sqrt; (5) correct rounding via the Ziv bracket; (6) termination via
`Nat.find` + `irrational_pi` (no effective irrationality measure is available).

* **Item 1 DONE (2026-10-18): Gauss's formula for `E` via the AGM** — `EllipticEAGM.lean`.
  **Statement.** For `0 < b ≤ a`, with `(a_j, b_j)` the AGM iteration and `c_j² = a_j² − b_j²`,
  `J(a, b) := ∫_0^{π/2} √(a² cos²θ + b² sin²θ) dθ = (a² − ∑_{j≥0} 2^(j−1) c_j²) · π/(2 AGM(a, b))`
  (`agmJ_eq_tsum`); for `0 < k < 1`, `E(k) = (1 − ∑_{j≥0} 2^(j−1) c_j²) K(k)` with the AGM
  started at `(1, √(1 − k²))` (`ellipticE_eq_AGM_sum`). **Proof route** (no new change of
  variables): one-parameter `f(x) = I(1, x) = π/(2 AGM(1, x))` (`agmK`, `agmK_eq_pi_div_AGM`)
  and `g(x) = J(1, x)` (`agmE`); on `(0, 1)` they are `K(√(1−x²))`, `E(√(1−x²))`
  (`agmK_eq_ellipticK`, `agmE_eq_ellipticE`), and `ellipticK_deriv_identity` becomes
  `g(x) = x² f(x) − (1 − x²) x f'(x)` with `f` differentiable there (`agmE_eq_sub_deriv`, chain
  rule through `√(1 − x²)` + `hasDerivAt_ellipticK`). Landen for `f`: `f(x) = (2/(1+x))
  f(2√x/(1+x))` from `AGM_step` + `AGM_smul` (`agmK_landen`, `landenMap`). Differentiating the
  Landen identity (`HasDerivAt.congr_of_eventuallyEq` on `Ioi 0`) and substituting both
  expressions for `g` gives `g(x) = (1+x) g(ℓ(x)) − x f(x)` (`agmE_landen`; after `x = s²` the
  final step is `field_simp; ring`). Scaling `J(a, b) = a g(b/a)` (`agmJ_eq_mul_agmE`) gives the
  Landen step `J(a, b) = 2 J((a+b)/2, √(ab)) − ab·π/(2 AGM(a, b))` (`agmJ_landen`; `a = b`
  separately via `agmJ_self`). Telescoping: `E_n := J(a_n, b_n) − a_n² π/(2 AGM)` satisfies
  `E_n = 2E_{n+1} − (c_n²/2) π/(2 AGM)` (`agmDeficit_succ`, using `a_n b_n = 2a_{n+1}² − a_n² +
  c_n²/2` and `AGM_agmSeq`), so `E_0 = 2^n E_n − (∑_{j<n} 2^(j−1) c_j²) π/(2 AGM)`
  (`agmDeficit_zero_eq`). Limit: `−(π/2)(1 + a_1/b_1)(a_n − b_n) ≤ E_n ≤ 0` (`agmDeficit_bounds`
  from `(π/2) b_n ≤ J(a_n,b_n) ≤ (π/2) a_n`, `agmJ_bounds`, and `b_n ≤ AGM ≤ a_n`), and
  `2^n (a_n − b_n) → 0`: once `a_m − b_m ≤ 2 b_1` (some `m ≥ 1`, `exists_agm_gap_le` via
  `agm_gap_le_half_pow`) the quadratic bound `agm_gap_succ_le_sq` gives a factor `1/4` per step
  (`agm_gap_succ_le_quarter`, `agm_gap_add_le`), so `2^(m+k) g_{m+k} ≤ 2^m g_m (1/2)^k`
  (`two_pow_mul_agm_gap_le`), whence `tendsto_two_pow_mul_agm_gap`, `summable_two_pow_mul_agm_gap`
  and `summable_agm_c_sq` (`c_j² ≤ 2a (a_j − b_j)`). `tendsto_nhds_unique` on the two limits of
  `2^n E_n − S_n I` finishes `agmJ_eq_tsum`. Lean notes: `Continuous.intervalIntegrable` needs
  the measure fixed by an expected type (else `IsLocallyFiniteMeasure ?μ` is stuck); after `rw`
  with `π/(2AGM) = agmK x / a`, `ring` cannot cancel `a * a⁻¹` — rewrite the whole product
  `a b (π/(2AGM)) = b agmK x` instead; `nlinarith` failed on a goal that is linear in the product
  atoms after one explicit `calc … = _ := by ring` restatement of the hint — restate hints in the
  goal's monomials and use `linarith`; `set C := …` then `linarith` needs `rw [hC]` or the
  equation in context. Not formalized: `J(a, b)` for `b > a` (symmetry), `f'` at `x ≥ 1` (unused).
* **Item 2 DONE (2026-10-18): Salamin's formula** — `BrentSalamin.lean`. **Statement.**
  `π = 4 AGM(1, 1/√2)² / (1 − ∑_{j≥1} 2^(j+1) c_j²)` with `c_j² = a_j² − b_j²` along the AGM
  started at `(1, 1/√2)` (`salamin_formula`; the series is `salaminSum := ∑_{j≥0} 2^(j+2)
  c_{j+1}²`, summable by `summable_salaminSum`). **Proof.** `k = k' = 1/√2`
  (`sqrt_one_sub_salaminB0_sq`), so `ellipticE_eq_AGM_sum` gives `E = (1 − S)K` with `S = ∑_{j≥0}
  2^(j−1) c_j²`; splitting off `j = 0` (`Summable.tsum_eq_zero_add`, `c_0² = 1/2`) and
  reindexing (`tsum_div_const`) gives `S = 1/4 + T/4`, `T = salaminSum`; the Legendre relation
  `2EK − K² = π/2` (`legendre_relation_sqrt_half`) becomes `K²(1 − T)/2 = π/2`, and Gauss's
  theorem `K = π/(2 AGM)` (`ellipticK_salaminB0` from `one_div_AGM_one`) turns it into
  `π(1 − T) = 4 AGM²` (`salamin_identity`, a `linear_combination (1/4) * hL` after
  `field_simp`); `1 − T = 4AGM²/π > 0` (`salamin_denominator_pos`) and `eq_div_iff` finish. Also
  `agmCsq_succ`: `c_{j+1}² = ((a_j − b_j)/2)²`, the cancellation-free form the algorithm uses.
  Sanity values: `AGM(1, 1/√2) ≈ 0.847213`, `4AGM² ≈ 2.87103`, `T ≈ 0.08611`, `c_1² ≈ 0.021447`.
* **Item 3 DONE (2026-10-18): the iterate and its error bound** — `BrentSalamin.lean`.
  **Definitions.** `salaminS N = 1/2 − ∑_{j<N} 2^(j+1) c_{j+1}²` (= `1/2 − ∑_{j=1}^{N} 2^j c_j²`;
  `salaminS_zero`, `salaminS_succ`: `s_{N+1} = s_N − 2^(N+1)((a_N − b_N)/2)²`, the recurrence
  the algorithm runs), `salaminApprox N = 2 a_{N+1}²/s_N`, `salaminTail N = ∑_{i≥0} 2^(i+N+1)
  c_{i+N+1}²`. **Facts.** `s_N = (1 − T)/2 + r_N` (`salaminS_eq`, via
  `Summable.sum_add_tsum_nat_add'` with explicit `f`/`k` — implicit higher-order unification
  timed out); `s_∞ = (1 − T)/2 > 1/3` (`salaminS_limit_gt`: `AGM² ≥ b_1² = b₀ > 2/3` and `π < 4`
  on `salamin_identity`); `π = 2 AGM²/s_∞` (`pi_eq_div_salaminS_limit`); `s_N > 1/3`
  (`salaminS_gt`). Start-specific bounds: `b₀ > 2/3` (`salaminB0_gt`), `a_n ≤ 1`
  (`salamin_agmA_le_one`), `b_n > 2/3` (`salamin_agmB_gt`), `a_n − b_n ≤ 2 b_1` for `n ≥ 1`
  (`salamin_gap_le_two_mul`: the quarter-decay regime from the first step). **Tail bound**
  (`salaminTail_le`, `N ≥ 1`): `c_{i+N+1}² = ((a_{i+N} − b_{i+N})/2)²` and `g_{i+N} ≤ g_N/4^i`
  (`agm_gap_add_le`) give terms `≤ 2^(N−1) g_N² (1/8)^i`, summing to `(4/7) 2^N g_N²`
  (`Summable.tsum_le_tsum`, `tsum_geometric_of_lt_one`). **Error.** Upper: `π_N − π ≤
  2(a_{N+1}² − AGM²)/s_N` (as `s_N ≥ s_∞`), and `a_{N+1}² − AGM² ≤ 2 g_{N+1} ≤ g_N²/(4 b_N) ≤
  (3/8) g_N²` (`agm_gap_succ_le_sq`, `b_N > 2/3`), so `π_N − π ≤ (9/4) g_N²`
  (`salaminApprox_sub_pi_le`). Lower: `π_N − π ≥ 2AGM²/s_N − 2AGM²/s_∞ = −π r_N/s_N ≥ −(48/7)
  2^N g_N²` (`le_salaminApprox_sub_pi`; `π < 4`, `1/s_N < 3`). Combined:
  `|π_N − π| ≤ 7 · 2^N (a_N − b_N)²` for `N ≥ 1` (`abs_salaminApprox_sub_pi_le`) — self-validating:
  the bound is computable from the iterate's own gap; `π_N → π` (`tendsto_salaminApprox`, via
  `tendsto_two_pow_mul_agm_gap` and `squeeze_zero'`). Sanity (60-digit decimal): `N = 1`: `g_1 ≈ 1.27e−2`, `|π_1 − π| ≈ 1.01e−3`, bound
  `7·2·g_1² ≈ 2.24e−3`; `N = 2`: `g_2 ≈ 2.36e−5`, error `≈ 7.4e−9`, bound `≈ 1.56e−8`; `N = 3`:
  `g_3 ≈ 8.2e−11`, error `≈ 1.8e−19`, bound `≈ 3.8e−19`; `N = 4`: `g_4 ≈ 1.0e−21`, error
  `≈ 5.5e−41`, bound `≈ 1.1e−40` — the bound is within a factor `2.1–2.2` of the true error at
  every step; each step squares the gap, so `N ≈ lg p` steps for `p` bits.
  Lean notes: `∞` is not an identifier character (`hs∞` fails to parse); `rw [← lemma]` where the
  lemma's LHS is `salaminB0` rewrites inside `AGM 1 salaminB0` too — rewrite at the hypothesis
  instead; `field_simp` on `2M²/(u + r) − 2M²/u` needs `u`, `u + r` as atoms (`set u`) with their
  `≠ 0` facts in context. Implementation plan for `AzFloat` (items 4–6): run the recurrence with
  Floor/Ceiling enclosures `[a⁻, a⁺]`, `[b⁻, b⁺]`, `[s⁻, s⁺]`; `π_N ∈ [2(a⁻)²/s⁺, 2(a⁺)²/s⁻]`
  (monotone in each), widen by `7·2^N (a⁺ − b⁻)²`; stop when the gap bound is below the target;
  then Ziv bracket + `Nat.find` termination from `irrational_pi`.
* **Items 4–6 DONE (2026-10-18) — the `AzFloat` implementation of `π`; see the section
  "`π` for `AzFloat`" below. The original plan, for the record:**
  (4) Directed-rounding enclosure lemmas: for `mode = Floor`/`Ceiling`, `addPrecRound`,
  `subPrecRound`, `mulPrecRound`/`sqrPrecRound`, `sqrtPrecRound` return a float below/above the
  exact value (none exist yet; the `Equiv/*.lean` `liftVal` specs + `roundVal` monotonicity are
  the raw material). Then an enclosure loop for the recurrence of `BrentSalamin.lean`: `[a⁻,
  a⁺]`, `[b⁻, b⁺]`, `[s⁻, s⁺]` with `a' = (a + b)/2`, `b' = √(ab)`, `s' = s − 2^(n+1)((a − b)/2)²`
  (lower `s'` uses upper `(a⁺ − b⁻)`), started from `a = 1`, `b ∈ [sqrt2Over2 Floor, Ceiling]`,
  `s = 1/2`; `π_N ∈ [2(a⁻)²/s⁺, 2(a⁺)²/s⁻]` (monotone in each argument), widened by the proven
  `7·2^N (a⁺ − b⁻)²` (`abs_salaminApprox_sub_pi_le`, with `a_N − b_N ≤ a⁺ − b⁻`); stop when the
  widening is below `2^(−w)`; the loop terminates since the gap halves per step
  (`agm_gap_le_half_pow`) — fuel `w + O(1)` or `N = ⌈lg w⌉ + 2`.
  (5) Correct rounding as for `phi`: feed the bracket to `roundingPossible`/`zivLoop`
  (`Ziv.lean`), `piPrecRound p mode : AzFloat × Ordering`, `pi p`, and the spec theorem
  `piPrecRound p mode = liftVal₀ Real.pi p mode` in `Equiv/Constants.lean` style; tests in
  `AzFloat/Tests/` via parse(toString) and a known-digits check.
  (6) Termination: no effective irrationality measure for `π` is available, so instead of an
  explicit `2p + 6` bound (as `phiApprox_possible`) use `Nat.find` on the decidable predicate
  "`roundingPossible` at working precision `w` is `some`", with existence from `irrational_pi`
  (Mathlib `Mathlib/Analysis/Real/Pi/Irrational.lean`) + bracket width `→ 0` + a generalization
  of `roundingPossible_isSome_of_no_boundary` ("a non-boundary real with a shrinking bracket
  eventually rounds"). `Nat.find` is computable, so `piPrecRound` stays total without fuel.

## Airy functions `Ai`, `Bi` (plan started 2026-10-18)

**Goal.** `Ai`, `Bi` (and, almost for free, `Ai′`, `Bi′`) for every real `AzFloat` argument,
correctly rounded in every mode, with proven error bounds; then a port to Malachite. MPFR has only
`mpfr_ai` (Taylor series only, documented as slow/incomplete for large `|x|`) and no `Bi`, `Ai′`,
`Bi′`; covering the four functions on the whole line is the "strictly better" target.

**Facts (DLMF §9).** `Ai = c₁ f − c₂ g`, `Bi = √3(c₁ f + c₂ g)` with the series `f`, `g` of
`Azurite/Airy/Series.lean`; `ζ = (2/3)|x|^(3/2)`, `u_k = (2k+1)(2k+3)⋯(6k−1)/(216^k k!)`.
Large `x > 0` (9.7.5–9.7.8): `Ai(x) ~ e^(−ζ)/(2√π x^(1/4)) ∑ (−1)^k u_k ζ^(−k)`,
`Bi(x) ~ e^(ζ)/(√π x^(1/4)) ∑ u_k ζ^(−k)`; large `x < 0` (9.7.9–9.7.11): `Ai(−x) ~ (1/(√π x^(1/4)))
[sin(ζ+π/4) ∑(−1)^k u_{2k} ζ^(−2k) − cos(ζ+π/4) ∑(−1)^k u_{2k+1} ζ^(−2k−1)]`, `Bi(−x)` with
`cos`/`sin` swapped and `+`. Integral representations behind the rigorous remainders: for `x > 0`,
`Ai(x) = (1/π)√(x/3) K_{1/3}(ζ)`, `Bi(x) = √(x/3)(I_{−1/3}(ζ) + I_{1/3}(ζ))`, and termwise
`√(x/3) I_{−1/3}(ζ) = √3 c₁ f(x)`, `√(x/3) I_{1/3}(ζ) = √3 c₂ g(x)` (Gauss's multiplication
`(3k)! = 27^k k! (1/3)_k (2/3)_k`), with the Laplace-type integrals `I_ν(z) = (z/2)^ν/(√π Γ(ν+½))
∫_{−1}^{1} (1−t²)^(ν−½) e^(zt) dt` and `K_ν(z) = √π (z/2)^ν/Γ(ν+½) ∫_1^∞ e^(−zt) (t²−1)^(ν−½) dt`
(valid for `ν = ±1/3 > −1/2`).

**Strategy by region** (`x = m·2^e` exact dyadic, target precision `p`, rounding mode `mode`).

* *Series region* `|x| ≤ X_a(p)`, `X_a(p) := ((3/4) p ln 2)^(2/3)` (≈ 10 at `p = 64`, ≈ 65 at
  `p = 1000`, ≈ 6500 at `p = 10⁶`): choose `K ≥ |x|^(3/2)` (`halving_of_le`) large enough that the
  tail bound `2|t_K|`, `2|u_K|` (`abs_f_sub_sum_le`, `abs_g_sub_sum_le`) is below `2^(−w)` times
  the magnitude of the sum; compute `∑_{k<K} t_k` and `∑_{k<K} u_k` **exactly** as rationals by
  binary splitting (`sum_fTerm_div_eq`: `fPartialNum/fPartialDen` with `fPartialDen = q^(3K) d_K`;
  product trees over `AzNat`/`AzInt` as in `Algorithm/BalancedProduct`; MCA §4.9.1) — no rounding
  error and no internal cancellation at all, cost `O(M(K (lg K + 3|e|)) lg K)`; round each to `w`
  bits (one rounding, `AzRat → AzFloat` exists), multiply by the constants `c₁`, `c₂` at `w` bits,
  and combine with `sumPrecRound`/a bracket. The only cancellation is between `c₁ f` and `c₂ g` for
  `Ai` at `x > 0` (both ≈ `e^ζ`, `Ai ≈ e^(−ζ)`): relative error `2^(−w) e^(2ζ)`, so the working
  precision is `w = p + 64 + guard(x)` with `guard(x) = ⌈2ζ lg e⌉ = ⌈(4/3) x^(3/2) · 1.4427⌉` for
  `Ai`, `x > 0` (a heuristic for the first attempt; correctness comes from the bracket and Ziv's
  loop, which doubles `w` on failure); `guard = 0` for `Bi` at `x ≥ 0` (all terms positive) and
  `O(1)` for `x < 0` (where `f`, `g`, `Ai`, `Bi` all have amplitude `≍ |x|^(−1/4)`; near zeros of
  `Ai(−x)`, `Bi(−x)` Ziv raises `w`, as for any function). The number of terms is `K ≍ max(|x|^(3/2),
  p/lg p)`, so with `|x| ≤ X_a(p)` the cost is quasi-linear in `p`.
* *Asymptotic region* `x ≥ X_a(p)`: truncate the expansions at `n ≈ ζ` (optimal truncation,
  remainder `≍ e^(−2ζ) ≤ 2^(−p)`), `Ai` from 9.7.5 with remainder `≤` first neglected term,
  `Bi` from 9.7.7 with remainder `≤ 2 ×` first neglected term `+ O(e^(−2ζ))` (theory items T4,
  T5 below); evaluate `∑ u_k ζ^(−k)` by Horner (or rectangular splitting, MCA §4.4.3, since the
  `u_k` are rationals: `O(√n M(w) + n w)`), needs `e^(±ζ)` (`exp`), `x^(1/4) = √√x` (have),
  `√π` (have `sqrt`, `π` from Brent–Salamin). Cost `O(n M(w))`, `n ≤ p/2`.
* *Asymptotic region* `x ≤ −X_a(p)`: 9.7.9–9.7.11 with `sin`, `cos` of `ζ + π/4` and the
  remainder bounds of theory item T6 (the hardest piece); **interim fallback**: the series region
  works for every `x` (cost `O(|x|^(3/2))` terms, like MPFR's `mpfr_ai`, but with `Bi` and with
  proven bounds).
* `Ai′`, `Bi′`: the same with the derivative series `fD`, `gD` (`fDTerm_succ`, `gDTerm_succ` give
  the exact rational partial sums and tail bounds by the same argument) and 9.7.6/9.7.8.
* Correct rounding: Ziv bracket `[lo, hi]` → `roundingPossible`, doubling `w`. No irrationality or
  non-dyadicity theorem for `Ai(x)`, `Bi(x)` at dyadic `x` is available (not even for `Ai(0) = c₁`),
  so termination cannot be proven; the implementation takes fuel and returns `NaN`/`none` on
  exhaustion, with the specification "`some r ⇒ r` is the correctly rounded value" (MPFR's loop
  simply never terminates on an exact case; Malachite can expose the fallible form).

**Dependencies on other `AzFloat` functions.** Have: `+ − × ÷ √ 1/√`, `AzRat → AzFloat` rounding,
`sumPrecRound`, `productPrecRound`, Ziv (`Ziv.lean`), `AzNat`/`AzInt`/`AzRat` big arithmetic and
`BalancedProduct`. Needed: (1) the constants `c₁ = 3^(−2/3)/Γ(2/3)`, `c₂ = 3^(−1/3)/Γ(1/3)` —
i.e. `Γ(1/3)` (then `Γ(2/3) = 2π/(√3 Γ(1/3))`), `3^(±1/3)` (a cube root: `rootN`/`cbrt` for
`AzFloat` by Newton, new), and `π` (Brent–Salamin items 4–6). `Γ(1/3)` options: (a) the generic
`Γ` algorithm (Stirling + argument shift, theory Ex. 4.21; needs `exp`, `log`) — the natural
default once `exp`/`log` exist; (b) Borwein–Zucker (1992): `Γ(1/3) = 2^(7/9) 3^(−1/12) π^(2/3)
K(k₃)^(1/3)` with `K(k₃) = π/(2 AGM(1, cos(π/12)))`, `cos(π/12) = (√6 + √2)/4` — only `√`, AGM,
`π`, cube roots, quasi-linear; its proof (singular values of `K`) is deep and not planned;
(c) bootstrap from the asymptotic region: with T4/T5 and `exp`, `c₁ = (Bi(x₀)/√3 + Ai(x₀))/(2
f(x₀))`, `c₂ = (Bi(x₀)/√3 − Ai(x₀))/(2 g(x₀))` at `x₀ = X_a(p)` (no cancellation; `f(x₀)`,
`g(x₀)` by exact binary splitting) — no separate `Γ` code, and `Γ(1/3)` comes out as a by-product.
(2) `exp` — for the asymptotic regions only. (3) `sin`, `cos` — for `x ≤ −X_a(p)` only. So the
series method on the whole line is unblocked as soon as `Γ(1/3)` (and `π`, cube root) exist; the
large-`|x|` acceleration additionally needs `exp` (and `sin`/`cos` for `x < 0`).

**Theory status.** DONE (2026-10-18, `Azurite/Airy/Series.lean`, all proven): the series,
`d_k ≥ (2k)!`, growth bounds, truncation with the halving criterion, exact rational partial sums,
termwise derivatives, `f″ = xf`, `g″ = xg`, `W(f,g) = 1`, `c₁ c₂ = 1/(2√3π)`, `Ai`, `Bi`, `Ai′`,
`Bi′`, `Ai″ = x Ai`, `Bi″ = x Bi`, `W(Ai,Bi) = 1/π`. TODO: **T3** the Bessel representations —
`I_{±1/3}` Laplace integral `=` series (termwise integration, Beta integrals `∫_{−1}^1 t^(2k)
(1−t²)^(ν−½) dt = B(k+½, ν+½)`, Gauss's multiplication formula), hence `Bi(x) = √(x/3)(I_{−1/3} +
I_{1/3})(ζ)` for `x > 0`; **T4** `Bi` asymptotics with remainder: Laplace's method on
`∫_{−1}^1 (1−t²)^(ν−½) e^(zt) dt` (`t = 1 − u/z`, binomial series of `(1 − u/(2z))^(ν−½)` whose
coefficients `|C(ν−½, k)|` decrease since `−1 < ν−½ < 0`, so the remainder on `u ≤ z` is at most
twice the first neglected term; the `[−1, 0]` part is `O(e^(−z))` relative), giving `Bi(x) =
e^ζ/(√π x^(1/4)) (∑_{k<n} u_k ζ^(−k) + R_n)`, `|R_n| ≤ 2 u_n ζ^(−n) + C e^(−2ζ)`; **T5** `Ai`
asymptotics: `G(x) := (1/π)√(x/3) K_{1/3}(ζ)` via the `∫_1^∞ e^(−zt)(t²−1)^(−1/6) dt` form;
`G″ = xG` (differentiation under the integral), `G = W(G,g) f − W(G,f) g` with constant Wronskians
(the uniqueness-free "Wronskian trick": `d/dx W(G,f) = G f″ − G″ f = 0`), `W(G,g) = lim_{0⁺} G = c₁`
and `W(G,f) = −lim_{0⁺} G′ = c₂` from the `ζ → 0` behaviour of the Laplace integrals (`t = s/ζ`,
`ζ^(2/3) ∫ → Γ(2/3)`, and `G′ = −(x/(π√3)) K_{2/3}(ζ)` by integration by parts; the constants match
through Legendre's duplication `Γ(1/3)Γ(5/6) = 2^(1/3)√π Γ(2/3)` and reflection), hence `Ai = G`
on `x > 0`, and then the binomial expansion of `(1 + u/(2z))^(−1/6)` (alternating, decreasing
derivatives) gives `Ai(x) = e^(−ζ)/(2√π x^(1/4)) (∑_{k<n} (−1)^k u_k ζ^(−k) + R_n)`, `|R_n| ≤
u_n ζ^(−n)` (remainder bounded by the first neglected term); **T6** `x < 0`: rigorous remainders
for the oscillatory expansions (Hankel/Poisson integral analysis; alternatively `Ai² + Bi²` has the
Laplace integral `(1/π^(3/2)) ∫_0^∞ e^(xt − t³/12) t^(−½) dt` with a Watson's-lemma remainder,
which bounds the modulus but not the phase) — deferred, series fallback meanwhile; **T7** `Ai′`,
`Bi′` truncation lemmas for `fD`, `gD` (routine); **T8** implementation proofs: the binary-splitting
recurrences equal `fPartialNum/Den`, the enclosure of the roundings, the Ziv specification.

**Comparison with MPFR.** `mpfr_ai`: Taylor series (two variants), no asymptotics, no `Bi`/`Ai′`/
`Bi′`, documented as slow and incomplete for large `|x|`. This plan: four functions, exact
binary-splitting series with proven tails everywhere, asymptotic acceleration for `x ≥ X_a(p)`
(and later `x ≤ −X_a(p)`), correct rounding with proven brackets.

## The constant `ln 2` for `AzFloat` (started 2026-10-18)

**Algorithm chosen.** Machin-like `atanh` formula summed by exact binary splitting:
`ln 2 = 18 atanh(1/26) − 2 atanh(1/4801) + 8 atanh(1/8749)`, `atanh(1/q) = ∑ 1/((2k+1) q^(2k+1))`
(about `0.19` terms per bit; `2 atanh(1/3)` needs `0.32`; `∑ 1/(k 2^k)` needs `1.44`). Rejected:
the AGM route (needs `π` and a `p/2`-bit argument because of the `O(k² |ln k|)` error (4.73)),
Newton on `exp` (needs `exp`). Every partial sum is an exact rational and the tail is bracketed
exactly, so there is no floating-point error analysis: `ln 2 ∈ [lo, hi]` with rational `lo`, `hi`,
then `AzRat → AzFloat` rounding and `roundingPossible`. Termination of the rounding loop is not
provable from Mathlib alone (no transcendence of `e` there); **resolved 2026-10-18**: Hermite's
theorem is now proven in `Azurite/Transcendental/Exp.lean` (`transcendental_exp_one`, from Mathlib's
`LindemannWeierstrass.exp_polynomial_approx`), giving `irrational_log_two`, so `ln2PrecRound` can
use the `Nat.find` termination argument planned for `π` (existence from irrationality + shrinking
brackets) instead of fuel.

* **Step 1 DONE (2026-10-18): theory** — `Ln2BinarySplitting.lean`. `atanhTerm`, `atanhInv`;
  `hasSum_atanhTerm`/`atanhInv_eq` from `Real.hasSum_log_one_add_inv` with `a = (q−1)/2`
  (`2a + 1 = q`, `1 + a⁻¹ = (q+1)/(q−1)`); `atanhTerm_add_le`: `t_{N+i} ≤ t_N/4^i` for `q ≥ 2`
  (`4^i ≤ q^(2i)`, `2N+1 ≤ 2(N+i)+1`, `gcongr`); `sum_le_atanhInv` (positive terms,
  `Summable.sum_le_tsum`), `atanhInv_sub_sum_le` (`≤ (4/3) t_N`, geometric tail via
  `tsum_geometric_of_lt_one`), `atanhTerm_le : t_N ≤ (1/q)^(2N+1)`; `oddProd N = ∏_{j<N}(2j+1)`,
  `atanhDen q N = q^(2N+1) oddProd N`, `atanhNum q N = ∑_{k<N} q^(2(N−k)) (oddProd N/(2k+1))`,
  `sum_atanhTerm_eq_div` (`Nat.cast_div` with `dvd_oddProd`); `log_two_eq_machin`
  (`norm_num` proves `(27/25)^9 (8750/8748)^4/(4802/4800) = 2`, then `Real.log_div/mul/pow`),
  `log_two_eq_atanh`, `log_two_mem_Icc` (two-sided bracket for arbitrary `N₁ N₂ N₃`),
  `log_two_bracket_width = (4/3)(18 t₁ + 2 t₂ + 8 t₃)`. Choosing `N`: width `≤ 2^(−w)` once
  `(1/q)^(2N+1) ≤ 2^(−w−6)` for each `q` (since `(4/3)·28 < 2^6`), i.e. `(2N+1)⌊lg q⌋ ≥ w + 6`
  with `⌊lg 26⌋ = 4`, `⌊lg 4801⌋ = 12`, `⌊lg 8749⌋ = 13`. Lean notes: `Finset.sum_div` needs
  `Mathlib.Algebra.BigOperators.Field`, `Nat.cast_div` needs `Mathlib.Data.Nat.Cast.Field` (not
  pulled in by `Log.Deriv`).
* **Step 2 DONE (2026-10-18): binary-splitting evaluator** — `Azurite/AzNat/AtanhSplit.lean` +
  `Equiv/AtanhSplit.lean` + `Tests/AtanhSplit.lean`. Normalization: the state `(T, B, Q)` of the
  range `[l, l+n)` represents `∑_{k<n} 1/((2(l+k)+1) q^(2(k+1))) = T/(B·Q)` with
  `B = ∏_{k<n}(2(l+k)+1)`, `Q = (q²)^n` (every term carries its own `q²`, so the leaf is
  `(1, 2l+1, q²)` and the merge is `(T₁B₂Q₂ + B₁T₂, B₁B₂, Q₁Q₂)` — the second range's terms carry
  the extra `1/Q₁`); the full sum is `∑_{k<N} 1/((2k+1)q^(2k+1)) = q·T(0,N)/(B·Q)` (`atanhNumDen`).
  Recursion by fuel (`atanhSplitFuel`, `fuel = n` in `atanhSplit`) with the sequential `atanhSeq`
  as fallback, as in `BalancedProduct`. Proofs: `Spec q l n x` (the three facts above, the third
  over `ℝ`), `spec_atanhLeaf`, `spec_splitMerge` (`prod_range_add`, `sum_range_add`, `pow_add`,
  then `field_simp`), `spec_atanhSeq`, `spec_atanhSplitFuel` (induction on fuel, `Nat.add_sub_cancel'`
  for `m + (n − m)`), `atanhNumDen_eq : num/den = ∑_{k<N} atanhTerm q k`, `atanhNumDen_den_pos`.
  Tests: `#guard` on `toString` against an independent Python model of the recursion (itself checked
  against the exact rational sum), plus tree-shape independence (fuel `0`, `1`, `2` vs full). Lean
  notes: `ofNat : Nat → AzNat` lives in `AzNat/Equiv/Basic.lean` but is computable and is what
  implementation files use; `toNat_ofNat` is already simp; `#guard` with `toString` avoids needing
  `DecidableEq` on state triples.
* **Step 3 DONE (2026-10-18): `ln2PrecRound p mode`** — `AzFloat/Ln2Bracket.lean`,
  `AzFloat/Ln2.lean` (+ `Equiv/Ln2Bracket.lean`, `Equiv/Ln2.lean`, `Tests/Ln2.lean`) and the
  new **certified Ziv loop** `zivLoopCertified` in `AzFloat/Ziv.lean`. Design: the working precision
  `w` only sets the term counts `log2N_q w = (w+6)/(2⌊lg q⌋) + 1`; the bracket `ln2Bracket w =
  (lo, hi)` is exact rational arithmetic on the three `atanhRat` sums (one binary splitting each per
  level) with the tails `(4/3) t_N` added where they enlarge the bracket — one approximation per
  level, the `Roundable` pair being the two ends of its error interval (true Ziv); `hi − lo ≤
  2^(−w)` (`ln2Bracket_width`), `lo < ln 2 ≤ hi` (`ln2Bracket_mem`, `lo_lt_log_two`). Termination
  without fuel: `zivLoopCertified approx p mode w₀ h` doubles `w` from `w₀` until `roundingPossible`
  answers, with the certificate `h : ∃ f, isSome at w₀·2^f` and the well-founded measure
  `Nat.find h − f` (the `where go` helper takes `h` explicitly — a `where`-local does not capture
  outer variables used only in `termination_by`); spec `zivLoopCertified_eq` (induction on the
  measure; `go.eq_def` + `split`). The certificate `ln2Approx_isSome_exists`: `ln 2` is not a
  boundary (`boundary_repr` gives `M·2^k`, rational; `irrational_log_two`), `adjacent_boundaries`
  gives the distance `D = min(ln 2 − bm, bp − ln 2) > 0`, `exists_pow_lt_of_lt_one` a level with
  `2^(−w) < D`, then `no_boundary_of_dist` + `roundingPossible_isSome_of_no_boundary`. Spec:
  `ln2PrecRound_eq_liftVal₀ (p) [NeZero p] (mode)` (`p = 0` returns `(zero, .lt)`). Tests
  (`#guard`, compiled evaluation — `Nat.find`/WF recursion is fine there, but not for `decide`):
  `p = 1, 2, 3` by hand, `p = 53` (`6243314768165359/2^53`, below `ln 2`), `p = 100`
  (`878668439483319573618263538048/2^100`, below), `toString (ln2 53) = "0.6931471805599453"`.
  Lean notes: `dif_neg` deprecated — `split_ifs with hp` instead; casts `((26:ℕ):ℝ)` vs the literal
  `(26:ℝ)` are different `linarith` atoms — `simp only [Nat.cast_ofNat]`; the generic lemma
  `atanhTerm_le_half_pow` takes `2^b ≤ q` and `(2N+1) b ≥ w + 6`. Reuse: `ln 3`, `ln 5`, `ln 10`
  by their own Machin-like formulas with the same bracket/loop; `π` (Brent–Salamin items 4–6) with
  `zivLoopCertified` and `irrational_pi`.
* **Step 4 DONE (2026-10-19): float bracket, no `AzRat`.** Benchmarking `ln` showed `ln2Bracket`
  at 887 ms of 1082 at 20000 bits — not the series (6 ms) but the `AzRat` reductions (GCDs of the
  50000-bit fractions; a GCD pathology fixed the same day brought it to 236 ms, still dominant).
  Now `ln2Fractions w` forms the two exact ends as *unreduced* fractions over a common denominator
  (`AzInt` numerator `18 n₁ (d₂E₂) d₃ + 8 n₃ d₁ (d₂E₂) − 2 (n₂E₂ + 4d₂) d₁ d₃` over
  `d₁ (d₂E₂) d₃`, `E_i = atanhTailDen = 3(2N+1)q^(2N+1)` so the tail `(4/3) t_N = 4/E_i`; the
  upper end likewise) and `ln2Bracket w = (⌊lo⌋_w, ⌈hi⌉_w)` divides each once with directed
  rounding (`divFloor_abs`/`divCeiling_abs`, new signed lemmas — no positivity needed).
  `ln2Bracket_spec`: `lv ≤ ln 2 ≤ hv`, `hv − lv ≤ 8·2^(−w)` (exact width `u` plus `2·lo·u +
  2·hi·u` with `lo ≤ 1`, `hi ≤ 2`), `lv ≥ 1/5` for `w ≥ 2`; strictness from `exists_rat_of_toVal`
  (moved here from `Equiv/LnBracket`) + `irrational_log_two`; the certificate is the generic
  `exists_isSome_of_irrational` with `C = 8` (the ad-hoc `adjacent_boundaries` proof is gone).
  `log2EBracket = (⌊1/hi⌋_w, ⌈1/lo⌉_w)` for `w ≥ 2` (width `≤ 80·2^(−w)`, threshold certificate
  `W₀ = 2`). In `lnBracket` the term `ℓ ln 2` is now `|ℓ|` times the float ends (`mulFloor/
  Ceiling_err` on `ofAzNat ℓ.abs`), negated when `ℓ < 0` (`ln_L_spec`: width `≤ 12|ℓ|u`;
  `ln_final_bounds` adjusted). Timings (ms): `ln2Bracket` at 1000/5000/20000 bits 1.85/19/236 →
  0.29/4.6/57; `ln2` 2.1/20/250 → 0.29/5.9/59; `ln` 4.0/37/429 → 1.7/14/145. Breakdown at
  20000 bits: splittings 6 ms, products of the fractions 29 ms, the two divisions 23 ms; at
  100000 bits 97 / 394 / 480 ms — the divisions acted on the full ≈ 950000-bit operands.
  **Truncation DONE (same day):** `ln2Bracket` first rounds the numerator down and the
  denominator up to `w + 8` bits (`setPrecRound … .Floor/.Ceiling`, new `setPrecFloor_err`/
  `setPrecCeiling_err` in `Equiv/DirectedRounding`; the other way for the upper end), then
  divides: each division is `O(M(w))`.  Proof: `n'/d' ≤ N/D` by `div_le_div₀`, and
  `lo (1 − 4u') ≤ n'/d'` from `(1 − 4u')(1 + 2u') ≤ 1 − 2u'` (`u' = 2^(−w−8) = u/256`), likewise
  `n''/d'' ≤ hi (1 + 5u')` from `(1 + 5u')(1 − 2u') ≥ 1 + 2u'` for `u' ≤ 1/10`; the total width
  `≤ u + 14u' + 6.2u ≤ 8u` keeps the stated bound, and `lv ≥ 0.437/2 ≥ 1/5` for `w ≥ 2`.
  Positivity of the numerators needs `w ≥ 1` (`lo ≥ ln 2 − 1/2 > 0`), which `[NeZero w]` gives.
  Timings: the two divisions 23 → 1.1 ms at 20000 bits, 480 → 20 ms at 100000; `ln2Bracket`
  57 → 36 ms, `ln2` 59 → 36 ms, `ln` 145 → 125 ms at 20000 bits (`ln2Bracket` now ≈ 30 % of
  `ln`, the AGM 42 %).
* **Trimming the products DONE (same day).** The common-denominator combination (exact products
  of 50000–170000-bit numbers, 35 of the bracket's 36 ms at 20000 bits, 493 of 513 at 100000) is
  gone: each series fraction `n/d` becomes a float pair on its own (`seriesBracket`: `n`, `d`
  rounded to `k = w + 8` bits — down/up for the lower end, up/down for the upper — and one
  directed division each; `seriesBracket_spec`: `S (1 − 6·2^(−k)) ≤ lv ≤ S ≤ hv ≤ S (1 + 8·2^(−k))`
  for `k ≥ 4`), the tail bounds `(4/3) t_N ≤ (4/3)·2^(−w−6)` are replaced by the single float
  `2^(−w−5)` (`toVal_tail`; width cost `28·2^(−w−5) < 2^(−w)`), and the Machin combination
  `18 S₁ − 2 (S₂ + t) + 8 S₃` / `18 (S₁ + t) − 2 S₂ + 8 (S₃ + t)` is evaluated on floats at `k`
  bits, every operation rounded away from `ln 2` (the subtracted parts the other way); the ends
  keep precision `k`.  Proof budget: with `S₁ ≤ 1/25`, `S₂ ≤ 1/4800`, `S₃ ≤ 1/8748`
  (`sum_atanhTerm_le`, from `sum_le_atanhInv`, `atanhInv_eq` and `log x ≤ x − 1`) all
  magnitudes are `≤ 2`, so each rounding costs `≤ 4·2^(−k)` (`FloorOf.ge_of_le`/`CeilOf.le_of_le`
  with the bound `2`) and the series errors `≤ 2^(−k)` each; total width
  `≤ 2^(−w) + 28·2^(−w−5) + 208·2^(−w−8) < 2·2^(−w)`, far inside the stated `8·2^(−w)`.  Six
  divisions at `k` bits instead of ≈ 12 products and 2 divisions.  Timings (ms): `ln2Bracket` at
  1000/5000/20000/100000 bits 0.27/3.6/36/513 → 0.16/1.2/10.5/143 (the splittings alone are
  0.08/0.65/6.7/100); `ln2` 36 → 9.9 and `ln` 125 → 99 at 20000 bits (`ln2Bracket` now 10 % of
  `ln`, the AGM 55 %).  Lean notes: `simp only [ln2Bracket]` on the goal timed out (huge unfolded
  term with many `set` variables) — `refine ⟨lo, hi, hlo', hhi', …⟩` unifies by `rfl`; the
  theorem needs `maxHeartbeats 400000` (≈ 60 `linarith` calls in a 100-hypothesis context);
  `unfold f g at h₁ h₂` fails when one hypothesis lacks `g` — unfold per hypothesis. Lean notes: casts `atanhTerm (↑26) k` vs `atanhTerm 26 k` need
  `push_cast at` before `rw [← h]`; hypotheses obtained after `set u := (1/2)^w` keep the literal
  `(1/2)^w` — `rw [← hu] at` them, or `linarith` treats `2·x·(1/2)^w` and `2·x·u` as unrelated
  monomials; `haveI` on a `Prop` is a lint warning (`have`).

## Transcendence of `e` (DONE 2026-10-18)

`Azurite/Transcendental/Exp.lean`. Mathlib (pinned version) contains only the analytic part of the
Lindemann–Weierstrass project, but that part ends with the public Hermite approximation lemma
`LindemannWeierstrass.exp_polynomial_approx (f : ℤ[X]) (hf : f.eval 0 ≠ 0) : ∃ c, ∀ p >
|f(0)|, p.Prime → ∃ nₚ, ¬p ∣ nₚ ∧ ∃ gₚ, deg gₚ ≤ p deg f − 1 ∧ ∀ r ∈ f.aroots ℂ, ‖nₚ e^r − p gₚ(r)‖
≤ c^p/(p−1)!`. Hermite's theorem from it (≈ 150 lines): `rootsPoly n = ∏_{k<n}(X − (k+1))`
(`mem_aroots_rootsPoly`); `aeval_exp_one_ne_zero`: for `Q ∈ ℤ[X]` with `Q(0) ≠ 0` and `Q(e) = 0`,
cast the relation to `ℂ` (`aeval_eq_sum_range`, `Complex.exp_nat_mul`), split off `k = 0`
(`sum_range_succ'`), take the prime `p ≥ max(N, |f(0)|+1, |Q(0)|+1)` (`Nat.exists_infinite_primes`)
where `N` comes from `A c^p/(p−1)! → 0` (`FloorSemiring.tendsto_pow_div_factorial_atTop` composed
with `tendsto_sub_atTop_nat 1`, `A = ∑ ‖a_k‖`), form `E = a₀nₚ + p ∑ a_{k+1} gₚ(k+1) ∈ ℤ`
(`aeval_algebraMap_apply_eq_algebraMap_eval` makes `gₚ(k+1)` an integer), show `(E : ℂ) = ∑ a_{k+1}
(p gₚ(k+1) − nₚ e^{k+1})` by `linear_combination nₚ * relation` after splitting the sum
(`mul_sum`, `sum_sub_distrib`), bound `‖E‖ ≤ A c^p/(p−1)! < 1`, so `E = 0` (`Int.abs_lt_one_iff`)
and `p ∣ a₀ nₚ` (`Nat.prime_iff_prime_int`, `Prime.dvd_or_dvd`), contradicting `p ∤ nₚ` and
`p > |a₀|` (`Int.natAbs_dvd_natAbs`, `Nat.le_of_dvd`). `transcendental_exp_one_int` strips the
power of `X` (`exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, `X_dvd_iff`, `e ≠ 0`);
`transcendental_exp_one` over `ℚ` via `IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ`;
`transcendental_exp_nat` (`IsAlgebraic.of_pow`), `transcendental_exp_rat` (`q.den`-th power to
`e^{num}`, sign via `Int.natCast_natAbs` + `IsAlgebraic.inv_iff`); `irrational_exp_one`,
`irrational_exp_rat`, `irrational_log_rat` (`Real.log_eq_zero` for `q ≠ 0`, then `exp (log r) = r`
algebraic, `isAlgebraic_algebraMap`), `irrational_log_two`. Uses: termination of `ln2PrecRound`
(and of any `ln r` constant for rational `r`) via `Nat.find`. Lean notes: `mem_aroots` needs
`Module.IsTorsionFree ℤ ℂ` (found by inference); the bound `hbound` is on `nₚ • exp r − p • aeval r gₚ`
with `zsmul`/`nsmul` — convert with `zsmul_eq_mul`, `nsmul_eq_mul`, `← norm_neg, neg_sub`.

## The AGM for `AzFloat` (DONE 2026-10-18)

`Azurite/AzFloat/Agm.lean` (+ `Equiv/Agm.lean`, `Tests/Agm.lean`). **Question answered:** is there
a theorem that `AGM(a, b)` of distinct positive dyadic (or rational) numbers is irrational, which
would make Ziv's loop provably terminating? Yes, a deep one: `AGM(1, k') = π/(2K(k))` with
`K(k) = (π/2)·₂F₁(1/2,1/2;1;k²)`, so `AGM(a, b)` for algebraic `a ≠ b` is algebraic iff a period of
an elliptic curve over `ℚ̄` is an algebraic multiple of `π`; for non-CM curves this contradicts
the `ℚ̄`-linear independence of the periods and `2πi` (Wüstholz's analytic subgroup theorem, 1989;
Masser), and for CM curves Chudnovsky (1976) proved `ω` and `π` algebraically independent — so the
AGM of two distinct positive algebraic numbers is transcendental (Schneider 1937 already gave the
transcendence of `K(k)` itself). Nothing of this is in Mathlib and it is far beyond reach, so the
implementation uses fuel: **"correctly rounded or `NaN`"** (`agmPrecRound_eq_or`), `NaN` only
when four doublings of the working precision (`agmFuel p = zivFuel (16(p + 64))`) all fail —
which the theorem says never happens for distinct inputs; `AGM(x, x) = x` is handled exactly
(`setPrecRound`), since there the loop could not terminate (`x` may be a boundary).
**Algorithm.** Interval iteration: `AgmBounds = (aLo, aHi, bLo, bHi)`, `agmStep w` computes
`aLo' = ⌊(aLo + bLo)/2⌋_w`, `aHi' = ⌈(aHi + bHi)/2⌉_w` (the halving is an exact shift),
`bLo' = ⌊√⌊aLo·bLo⌋_w⌋_w`, `bHi' = ⌈√⌈aHi·bHi⌉_w⌉_w`; since the step is monotone in both
arguments, `aLo ≤ a_n ≤ aHi`, `bLo ≤ b_n ≤ bHi` exactly (`Encloses`, `encloses_agmStep`; the
lower bounds stay `≥ 0` because `0` is a float, `roundVal_floor_spec`); after `≥ 1` step
`bLo ≤ b_m < AGM ≤ a_m ≤ aHi` (`agmB_le_AGM`, `AGM_le_agmA`, strictness `agmB_lt_AGM` new in
`AGM.lean`), the two ends re-rounded at `p`/`p+1` are the Ziv `Roundable` pair (`rounds_setPrecRound`);
`agmConverged` stops the iteration once `aHi − bLo ≤ aHi·2^(8−w)` (speed only — any number of
steps is a valid bracket), fuel `w + |e_x| + |e_y| + 2` steps. (First version compared with half an
ulp, `aHi >>> (w+1)`, which the rounding noise alone — the bounds drift apart by about `2` ulps
per step, converging to a bracket about `8` ulps wide — never satisfies, so the loop always ran its
full step fuel: correct but slow; fixed the same day.) **Fuel exhaustion likelihood.** An attempt
at working precision `w` fails iff the bracket, of relative width `≈ 2^(8−w)`, contains a
`(p+1)`-bit boundary (relative spacing `≈ 2^(−p−1)`): for a value with "random" low-order bits
the probability is `≈ 2^(9+p−w)`, i.e. `≈ 2^(−55)` at `w = p + 64`; the failures are nested
(each is "the AGM is within `c·2^(−w)` of a boundary"), so the fuel runs out only when the AGM
is within `≈ 2^(8−16(p+64))` of a boundary — probability `≈ 2^(−15p−1015)`, `< 2^(−1800)` already
at `p = 53`. The transcendence theorem forbids exact hits; an astronomically close miss would be
a Diophantine coincidence no known result excludes (no effective irrationality measure), but
nothing suggests it. Raising `agmFuel` costs nothing unless the extra levels are used. Cost: `O(lg w + lg|e_x − e_y|)` steps,
each two adds, two muls, two sqrts at precision `w` (the interval approach doubles the work of a
plain iteration but needs no rounding-error analysis). **Proofs.** `Spec.agm` and nine special-value
lemmas (`agm_coe_coe`, `agm_of_neg_left/right`, `agm_zero_of_nonneg_ne_top`, `agm_zero_top`,
`agm_top_of_pos`, …), `roundVal_floor_spec`/`roundVal_ceiling_spec` (from `roundVal_coe`,
`val_roundFloor_floatSet`, `isGreatest_roundFloor`/`isLeast_roundCeiling`, `precisionSet_exists_real`),
`addFloor_spec` … `sqrtCeiling_spec` (one `rw` chain each through `*_eq_liftVal₂`/`Spec.*_coe_coe`),
`toVal_half`, `encloses_init/agmStep/agmIter`, `agmApprox_spec`, `zivLoop_eq_of_ne_nan` (new, in
`Equiv/Ziv.lean`), and the 16-case `agmPrecRound_eq_or` (`cases x <;> cases y`, `simp` with the
special-value lemmas and `finiteVal_true_pos_ereal`/`finiteVal_false_neg_ereal`; the finite–finite
case splits on `eqIEEE` via `eqIEEE_iff`). Tests: `AGM(1,2)`, `AGM(24,6)` (Gauss), homogeneity
`AGM(1,1/2)`, `AGM(3,1/8)` at 53 and 100 bits with 80-digit references, `AGM(x,x)`, all special
values. Lean notes: `roundFloor`/`isGreatest_roundFloor` need `open RoundingTarget`;
`finiteVal_true_pos'` already exists (`RoundScaled.lean`) — pick distinct names; conditional simp
lemmas (`agm_top_of_pos (h)`) are best passed instantiated; `if_pos`/`if_neg` deprecated —
`simp only [heq, ↓reduceIte]`; `split at hne` on a shared `match` also splits the goal.
* **Variants (2026-10-18): `agmRatPrecRound q₁ q₂` and `agmFloatRatPrecRound x q`.** The engine
  was generalized to `agmApproxFrom s₀ fuel w` (any initial enclosure `Encloses a b 0 s₀`,
  `agmApproxFrom_spec`); a rational is seeded by `ratBounds q w = ((ofAzRatRound q w .Floor).1,
  (… .Ceiling).1)` with `ratBounds_spec` (floor `≤ q ≤` ceiling, floor `≥ 0` when `q ≥ 0`, from
  `ofAzRatRound_eq_roundVal` + `roundVal_floor/ceiling_spec`). Rational–rational: negatives →
  `NaN`, zero → `0`, `q₁ = q₂` (structural, `DecidableEq`; = value equality by `toRat_injective`)
  → `ofAzRatRound q₁ p mode`, else Ziv; spec `agmRatPrecRound_eq_or` against `liftVal₀ (Spec.agm
  q₁ q₂)`. Float–rational: the special values as for floats; the exact case `x = q` cannot use
  `toAzRat?` (it materializes `x`, infeasible for huge exponents) and is detected instead by
  `(subRatPrecRound x q 1 .Floor).1.isZero` — the proven correctly rounded `x − q` (its Ziv loop
  has an explicit fuel certificate) at one bit is zero iff `x − q = 0` (`subRat_isZero_iff`,
  via `eq_zero_of_roundFloor_eq_zero`: no underflow, so a nonzero real never rounds to zero);
  spec `agmFloatRatPrecRound_eq_or` against `roundVal p mode (x.toVal.bind fun a => Spec.agm a q)`.
  Order facts for `AzRat`: `q < 0 ↔ (toRat q : ℝ) < 0` (`azRat_lt_zero_iff`, the `LT` instance is
  `cmp q r = .lt` + `cmp_eq_compare`), `q = 0 ↔ toRat q = 0`. Tests: the same reference values
  through all three entry points (`AGM(1,2)`, `AGM(3,1/8)`), consistency of rational vs mixed on
  the non-dyadic `AGM(1, 1/3)`, exactness of equal arguments (`3/4` is a 2-bit float: `.eq`; `7/4`
  rounds), special values. Lean notes: `hz : q ≠ 0` does not `rw` with an iff (`Ne` is not
  unfolded) — use `fun h => hz (iff.mpr h)`; `subst hz` on `q = 0` simplifies `if 0 < 0` with the
  hypothesis `¬ 0 < 0`; lemmas used by a later section must be defined before it (moved the
  `finiteVal_*_ereal` sign lemmas).
* **`log₂ e = 1/ln 2` DONE (2026-10-18)** — `log2EPrecRound`/`log2E` in `Ln2.lean`. The reciprocal of
  the exact `ln 2` bracket is an exact bracket: `log2EBracket w = (1/hi, 1/lo)` (`AzRat` division),
  `1/hi ≤ 1/ln 2 ≤ 1/lo` (`log2EBracket_mem`, `inv_anti₀`), width `(hi − lo)/(lo·hi) ≤ 8·(1/2)^w`
  (`log2EBracket_width`: `lo ≥ ln 2 − 1/2 > 0.19` for `w ≥ 1` via `Real.log_two_gt_d9`,
  `hi > 0.69`, so `1/(lo·hi) < 8`), certificate from `irrational_log_two.inv`. The Ziv certificate
  argument is now generic: `exists_isSome_of_irrational` in `Equiv/Ziv.lean` (irrational `v`,
  brackets of width `≤ C (1/2)^w` ⇒ `∃ f`, via `adjacent_boundaries` + `no_boundary_of_dist`) with
  `not_mem_floatSet_of_irrational`; new constants of this shape need only `Rounds`, containment,
  a width bound and an irrationality proof. Tests at 1, 2, 3, 53, 100 bits
  (`6497320848556798/2^52` below, `914416617264592211221101407495/2^99` above),
  `toString (log2E 53) = "1.4426950408889634"`. Spec also stated as `Real.logb 2 (Real.exp 1)`.
  Naming: `log2E` — base-2 logarithm of `e` (the `ln`/`log2` convention).

## Gauss's constant `G = 1/AGM(1, √2)` for `AzFloat` (DONE 2026-10-18)

`G = 0.83462684167407318628142973279904680899399301349034700244982737010368…`
`= Γ(1/4)²/(2π)^(3/2) = √2 K(1/√2)/π = ϖ/π` (lemniscate constant over `π`).

* **Irrationality.** No proof simpler than the general AGM one: `G = Γ(1/4)²/(2π)^(3/2)`, so
  irrationality of `G` is Chudnovsky's (1976) algebraic independence of `π` and `Γ(1/4)` — the CM
  case (`k = 1/√2`, `τ = i`) of the periods argument in `reference_agm_transcendence`. Nothing in
  Mathlib; even the irrationality of `Γ(1/4)` alone is not elementary. Hence **fuel**.
* **Implementation** (`AzFloat/GaussConstant.lean`). `gaussApprox w`: seed `⟨one, one, ⌊√2⌋_w,
  ⌈√2⌉_w⟩` (`sqrt2PrecRound w .Floor/.Ceiling`), one forced `agmStep` then `agmIter w (w + 4)`,
  bracket `lo = ⌊1/aHi⌋_w`, `hi = ⌈1/bLo⌉_w` (`divPrecRound one · w .Floor/.Ceiling`), Roundables
  by `setPrecRound`. `gaussConstantPrecRound p mode = zivLoop gaussApprox p mode (agmFuel p)
  (p + zivGuardBits)`; `gaussConstant p` nearest. Cost: one AGM at each Ziv level (≈ lg w steps,
  each an add, a mul and a sqrt at precision `w`) plus one division.
* **Proofs** (`Equiv/GaussConstant.lean`). `gaussConstantPrecRound_eq_or : … = liftVal₀
  (1/AGM(1, √2)) p mode ∨ … = (nan, .eq)` via `zivLoop_eq_of_ne_nan` and `gaussApprox_spec`
  (`lv ≤ G ≤ hv`, `lv < G` strictly so `lv = G → hv = G` holds vacuously). Two ingredients
  beyond `Equiv/Agm`: (a) `LowerGeOne` — both lower bounds stay `≥ 1` under `agmStep`
  (`⌊(a+b)/2⌋ ≥ 1` since `2 ∈ floatSet w`, `⌊√⌊ab⌋⌋ ≥ 1` since `1 ∈ floatSet w`; generic
  `roundVal_floor_ge`: rounding down a real `≥ c` with `c` a float stays `≥ c`), so `bLo > 0` and
  `1/bLo` is a finite upper bound; (b) `AGM_lt_agmA` (new in `Chapter4/AGM.lean`): `AGM a b <
  a_n` for `a ≠ b`, `n ≥ 1`, from `a_{n+1} = (a_n + b_n)/2 < a_n`. Also `gaussConstant_eq_ellipticK`
  (`AGM_smul`, `AGM_comm`, `one_div_AGM_one`, `sqrt_one_sub_salaminB0_sq`).
* **Tests** (`Tests/GaussConstant.lean`): precisions 1, 2, 3, 53, 100 with all four comparison
  outcomes (`G·2^53 = 7517650266313539.927…` so nearest rounds up at 53 and is `.gt`;
  `G·2^100 = …728.083…` so nearest rounds down at 100 and is `.lt`); `toString (gaussConstant 53) =
  "0.8346268416740732"`.
* **Fuel.** Same analysis as the AGM: exhaustion only if `G` is within `≈ 2^(−16(p+64))` of a
  rounding boundary at precision `p`, probability `≈ 2^(−15p−1015)` per call.

## `π` for `AzFloat` (DONE 2026-10-18, fuel-free)

Files: `AzFloat/PiBracket.lean`, `AzFloat/Pi.lean`, `AzFloat/Equiv/DirectedRounding.lean`,
`AzFloat/Equiv/PiBracket.lean`, `AzFloat/Equiv/Pi.lean`, `AzFloat/Tests/Pi.lean`; theory added
to `Chapter4/BrentSalamin.lean` and `AzFloat/Equiv/Ziv.lean`.

* **Fuel.** None. The AGM needed fuel because the *target value* might be a rounding boundary
  (not formalizable); `π` is irrational (`irrational_pi`), so once the bracket width tends to
  zero the certified loop terminates: `piPrecRound` is total and `piPrecRound_eq_liftVal₀` is
  unconditional. The price is a quantitative width analysis of the interval iteration, which the
  fuel version of the AGM skipped.
* **Steps.** `piSteps w = ⌊lg w⌋ + 1`. Theory (`BrentSalamin.lean`): `a₁ − b₁ ≤ 1/64`
  (`salamin_gap_one_le`, from `0.7071 < 1/√2 < 0.70711`), so by `agm_gap_le`
  `a_n − b_n ≤ 8·2^(−8·2^(n−1))` (`salamin_gap_le_pow`), and `|π_N − π| ≤ 7·2^N (a_N − b_N)² ≤
  2^(9+N−8·2^N) ≤ 2^(−w)` when `w + N + 9 ≤ 8·2^N` (`abs_salaminApprox_sub_pi_le_pow`), which
  `piSteps` satisfies (`piSteps_spec`, from `w < 2^(⌊lg w⌋+1)` and `⌊lg w⌋ < w`).
* **Algorithm** (`PiBracket.lean`). Enclosures `[a⁻, a⁺]`, `[b⁻, b⁺]`, `[s⁻, s⁺]` at precision
  `w`; `a' = ⌊a⁻+b⁻⌋/2, ⌈a⁺+b⁺⌉/2`; `b' = ⌊√⌊a⁻b⁻⌋⌋, ⌈√⌈a⁺b⁺⌉⌉`; `d = max(⌊a⁻−b⁺⌋, 0), ⌈a⁺−b⁻⌉`
  (the clamp matters once the AGM has converged below the enclosure width);
  `t = ⌊d⁻²⌋·2^(n−1), ⌈d⁺²⌉·2^(n−1)` (exact shifts; `2^(n+1)((a−b)/2)² = 2^(n−1)(a−b)²`);
  `s' = ⌊s⁻ − t⁺⌋, ⌈s⁺ − t⁻⌉`. Seed `a₀ = 1` exactly, `b₀ = ⌊1/√2⌋_w, ⌈1/√2⌉_w`
  (`sqrt2Over2PrecRound`), `s₀ = 1/2` exactly. Then `a_{N+1}` by one more mean,
  `n = 2a² ∈ [2⌊a⁻²⌋, 2⌈a⁺²⌉]`, `π_N ∈ [⌊n⁻/s⁺⌋, ⌈n⁺/s⁻⌉]`, widened by `2^(1−w)` on both sides
  (`powerOf2 (1 − w)`; `2^(1−w) > 2^(−w)` makes the lower end *strictly* below `π`, as
  `zivLoopCertified_eq` needs). Cost: `⌊lg w⌋ + 1` steps of one mul, one sqrt, one square, three
  add/sub at precision `w`, then a division — the standard Brent–Salamin cost, twice (two ends).
* **Width analysis** (`Equiv/PiBracket.lean`, for `w ≥ 64`; Ziv starts at `p + 64`). Generic
  tool (`Equiv/DirectedRounding.lean`): rounding `x ≥ 0` down/up at precision `w` moves it by at
  most `2x·2^(−w)` (`roundVal_floor_err`/`roundVal_ceiling_err`, from `truncError_spec`:
  `ulp = 2^(e−w) ≤ 2·|y|·2^(−w)`), lifted to every operation (`addFloor_err`, …). Invariant
  `PiEncloses w n`: with `W_n = (a⁺−a⁻)+(b⁺−b⁻)` and `u = 2^(−w)`, `W_n ≤ 2^(2n+4) u` and
  `s⁺−s⁻ ≤ 2^(3n+7) u`. Step: `W' ≤ 2.5 W + 21u` (mean: `W/2 + 5u`; geometric mean:
  `√m⁺ − √m⁻ ≤ (m⁺−m⁻)/(3/5)` since `m⁻ ≥ (29/48)² − 2u ≥ 9/25`, giving `2W + 16u`);
  `d⁺ − d⁻ ≤ 2W + 4u` in both clamp cases (if `a⁻ − b⁺ < 0` then `a − b < W`);
  `e⁺ − e⁻ ≤ 4W + 12u`; `t⁺ − t⁻ ≤ 2^(n−1)(4W + 12u) ≤ 2^(3n+6) u`; `s` adds `t`-width plus `4u`.
  All true values stay in `[2/3, 1]` (`salamin_facts`), `s_n ∈ (1/3, 1/2]`, so the ends are
  bounded and the lower ends positive once `2^(3N+16) u ≤ 1/16`, which holds for `w ≥ 64` via
  `2^N ≤ 2w` and `w³·2^30 ≤ 2^w` (`cube_mul_le_two_pow`). Final bracket width
  `≤ 2^(3N+16) u ≤ piEps w = 2^19 w³ 2^(−w) → 0` (`tendsto_piEps`, Mathlib's
  `tendsto_pow_const_mul_const_pow_of_abs_lt_one`).
* **Ziv.** Two generalizations in `Equiv/Ziv.lean`: `exists_isSome_of_irrational_threshold`
  (bracket valid only for `w ≥ W₀`, width `ε w → 0` instead of `C (1/2)^w`) and
  `zivLoopCertified_eq_threshold` (bracket valid only for `w ≥ w₀`; the loop never looks below
  `w₀`; the old `zivLoopCertified_eq` is now a corollary).
* **Tests** (`Tests/Pi.lean`): precisions 1, 2, 3, 53, 100 with the exact comparisons (`π·2^51 =
  7074237752028440.4506…` so nearest at 53 bits rounds down, `.lt`; `π·2^98 = …488.8396…` so
  nearest at 100 bits rounds down, `.lt`), `toString (pi 53) = "3.141592653589793"`, and 200 bits.
* **Proof-engineering notes.** The step lemma was split into three building blocks
  (`mean_step`, `geo_step`, `diffsq_step`) with small contexts: `nlinarith` in a 40-hypothesis
  context timed out. Products of hypotheses are formed explicitly with `mul_le_mul`; the big
  linear steps use `linarith only [...]`. `mul_le_one₀` is deprecated (lint warning) — a local
  `mul_le_one_of` replaces it.

## The lemniscate constant `ϖ` for `AzFloat` (DONE 2026-10-19)

`ϖ = 2.62205755429211981046483958989111941368275495143162316281682170380079058707041425023…`

* **Definition** (`Chapter4/Lemniscate.lean`): `lemniscate = 2 ∫₀¹ dt/√(1 − t⁴)` (the integrand
  is `(√(1 − t⁴))⁻¹`, zero at `t = 1` by Lean's conventions). Integrability by comparison with
  `(1 − t)^(−1/2)` (`intervalIntegrable_rpow'` + `comp_sub_left`, `mono_fun'`). The
  substitution `t = cos φ` uses Mathlib's `integral_comp_mul_deriv'''` (continuity of the
  integrand only on the image of the *open* interval, integrability on the closed one): since
  `1 − cos⁴φ = sin²φ (1 + cos²φ)`, `g(cos φ) sin φ = 1/√(1 + cos²φ) = (1/√2)/√(1 − sin²φ/2)` on
  `(0, π/2]`, so `∫₀¹ g = K(1/√2)/√2` and `ϖ = √2 K(1/√2)` (`lemniscate_eq_sqrt_two_mul_ellipticK`);
  with `ellipticK_salaminB0` and `AGM(1, √2) = √2 AGM(1, 1/√2)`: `ϖ = π/AGM(1, √2) = π · G`.
* **Algorithm** (`AzFloat/Lemniscate.lean`), as requested: `ϖ = π · G`. `piApprox` and
  `gaussApprox` were split into the float pairs `piBracket w`/`gaussBracket w` plus the
  `setPrecRound` wrappers; `lemniscateBracket w = (⌊π⁻ G⁻⌋_w, ⌈π⁺ G⁺⌉_w)`. Two AGMs per Ziv
  level (one for `π`, one for `G`). Fuel `agmFuel p` (irrationality of `ϖ` is Schneider's
  theorem, unavailable); spec `lemniscateConstantPrecRound_eq_or`.
* **Proof** (`Equiv/Lemniscate.lean`): `piBracket_spec` (now also `0 ≤ lv`) and
  `gaussBracket_spec` (now with `0 ≤ lv`, `lv < G`) give `π⁻ G⁻ < π G ≤ π⁺ G⁺`; the strictness
  (`lv = ϖ → hv = ϖ` vacuous) comes from `π⁻ < π` and `G⁻ < G` with `G⁻ ≥ 0`. New Ziv lemma
  `zivLoop_eq_of_ne_nan_threshold` (bracket valid only for `w ≥ w₀`, as `piBracket_spec` needs
  `w ≥ 64`).
* **Alternative not taken**: one AGM via `ϖ_N = √2 a_{N+1}/s_N` from the Brent–Salamin
  quantities (`ϖ = √2 M'/s_∞`, error `≤ 9·2^N (a_N − b_N)²`); would halve the cost.
* **Tests** (`Tests/Lemniscate.lean`): precisions 1, 2, 3, 53, 100 with exact comparisons
  (`ϖ·2^51 = 5904348712226992.4357…`, `ϖ·2^98 = …072.3447…`), `toString … 53 =
  "2.6220575542921196"`.

## `ln` for `AzFloat` (DONE 2026-10-19, fuel-free, AGM)

Files: `AzFloat/LnBracket.lean`, `AzFloat/Ln.lean`, `AzFloat/Equiv/LnBracket.lean`,
`AzFloat/Equiv/Ln.lean`, `AzFloat/Tests/Ln.lean`.

* **Method.** MCA §4.8.2 (`abs_pi_div_AGM_sub_log_le`): for `0 < k ≤ 1`,
  `|π/(2 AGM(1, k)) − ln(4/k)| ≤ (k²/4)(2 − ln k)`. At working precision `w` let
  `h = lnH w = ⌊w/4⌋ + 2`; scale `x = m·2^e` (`m ∈ [1/2, 1)`) to `y = x·2^ℓ`,
  `ℓ = 2h + 2 − e`, so `y ∈ [2^(2h+1), 2^(2h+2))` and `k = 4/y ∈ [2^(−2h), 2^(1−2h)]`
  (`ln_scale`); the error is then `≤ (2h + 2) 2^(−4h) ≤ 2^(size(2h+2) − 4h)` (`agmLog_bounds`,
  an exact power of two `eps` added on both sides). `ln x = π/(2 AGM(1, k)) − ℓ ln 2`.
  Rejected alternative: series + repeated square roots (slower at every precision here).
* **Fuel.** None: `ln x` is irrational for every float `x ≠ 1` (`irrational_log_rat`, since float
  values are rational — `exists_rat_of_toVal`), and the width tends to zero, so
  `zivLoopCertified` (threshold form, start `p + 64`) terminates; `x = 1` is caught by `eqIEEE`
  and returns `(zero, .eq)`; `lnPrecRound_eq_liftVal` is unconditional for `p ≠ 0`.
* **Algorithm** (`LnBracket.lean`). `kLo/kHi = ⌊4/y⌋_w, ⌈4/y⌉_w` (`4 = one <<< 2`, exact);
  the interval AGM `agmStep` of `Agm.lean` iterated `lnSteps w = 2⌈lg 2h⌉ + 3` times from
  `⟨1, 1, kLo, kHi⟩` (`agmIterN`); `qLo = ⌊(π⁻/2)/a⁺⌋`, `qHi = ⌈(π⁺/2)/b⁻⌉` with `piBracket w`;
  `LLo/LHi = ⌊min(ℓ·l₁, ℓ·l₂)⌋, ⌈max(ℓ·l₁, ℓ·l₂)⌉` with the rational `ln2Bracket w` (the `min/max`
  handle the sign of `ℓ`); result `(⌊⌊qLo − eps⌋ − LHi⌋, ⌈⌈qHi + eps⌉ − LLo⌉)`. Cost:
  `lnSteps w ≈ 2 lg w` AGM steps (one mul, one sqrt, two add/sub at precision `w`, twice for
  the two ends) plus `piBracket w` (`lg w` Brent–Salamin steps), `ln2Bracket w`
  (binary splitting) and three divisions.
* **Width analysis** (`Equiv/LnBracket.lean`, `w ≥ 64`, `u = 2^(−w)`). The AGM is
  homogeneous, so the natural invariant is *relative*: `RelEncloses a b n δ s` says the ends of
  `s` enclose `a_n, b_n` within factors `1 ∓ δ`; one `agmStep` adds `8u` (`relEncloses_agmStep`:
  the mean rounds within `1 ± 2u`, the square root of a product within `(1 ± 2u)(1 ± u)`, with
  `√(1−t) ≥ 1−t`, `√(1+2t) ≤ 1+t`), so after `S` steps `δ = 8uS` (`relEncloses_agmIterN`).
  The exact gap after `S = lnSteps w` steps is `≤ 8·2^(−5h)` (`agm_log_gap`:
  `agm_log_iterations` gives `≤ 8·2^(−2h)` at `2⌈lg 2h⌉ + 1` steps, then two quadratic
  steps `gap' ≤ gap²/(8b)` with `b ≥ 1/(2h+3)`). With `AGM ∈ [1/(2h+3), 1]` the quotient
  width is `≤ (piEps w + 2(a⁺ − b⁻))·(3W)²`, `W = w + |e| + 8`; `|ℓ| ≤ W`, so the `ℓ ln 2`
  term has width `≤ 5|ℓ|u` (`ln_L_spec`); all magnitudes are `≤ 17W`, so the four outer
  roundings add `≤ 108 W u`; total `≤ lnEps e w = 2^40 W^5 u` (`ln_final_bounds`, a pure
  real lemma with ~30 hypotheses — kept separate from `lnBracket_spec` whose context holds the
  float terms; `tendsto_lnEps` via `tendsto_pow_const_mul_const_pow_of_abs_lt_one` after
  expanding `(w + c)^5`).
* **Proof-engineering notes.** `set` on a real expression *after* unfolding `lnBracket` in the
  goal (huge float terms) caused whnf timeouts — the `set`s go before the unfolding, and the
  goal is rewritten back to the `set` variables (`rw [← hh_def, hS_eq, ← hℓ, ← heps]`) so the
  final `refine` is syntactic. The implementation must use the exact term the value lemma
  states (`one <<< 2`, not `powerOf2 2`): otherwise unification unfolds float arithmetic.
  `nlinarith` was replaced by explicit `mul_le_mul_of_nonneg_*` products + `linarith` in the
  step lemma; `ln_final_bounds` needs `maxHeartbeats 800000` (many `linarith` calls in a
  60-hypothesis context).
* **Tests** (`Tests/Ln.lean`): special values, `ln 2 = ln2` at 53/200 bits in three modes,
  `ln 10`, `ln 3`, `ln ½`, `ln 1.5`, `ln 10^±12`, `ln 2^100` at 53 bits, floor/ceiling tags,
  `ln 10` and `ln 3` at 200 bits.
* **Timings (2026-10-19, `az_float_ln`, ms per call, median of 3 over `ln 10, ln 3, ln ½, ln 1.5`;
  bracket pieces at `w = P + 64`).**

  | bits | `ln` | `lnBracket` | AGM only | `piBracket` | `ln2Bracket` | `sqrt` | `pi` | `ln2` |
  |---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | 53 | 0.54 | 0.56 | 0.19 | 0.12 | 0.14 | 0.002 | 0.13 | 0.14 |
  | 200 | 1.20 | 1.18 | 0.32 | 0.20 | 0.49 | 0.006 | 0.20 | 0.51 |
  | 1000 | 6.3 | 6.3 | 0.81 | 0.52 | 3.7 | 0.012 | 0.52 | 3.7 |
  | 5000 | 88 | 88 | 5.7 | 3.6 | 59 | 0.069 | 3.7 | 60 |
  | 20000 | 1077 | 1082 | 52 | 33 | 887 | 0.53 | 33 | 905 |

  After the GCD fix below (same day): `ln` 0.57 / 1.0 / 4.0 / 37 / 429 ms at 53 / 200 / 1000 /
  5000 / 20000 bits; `ln2Bracket` 0.15 / 0.34 / 1.8 / 19 / 236 ms; `ln2` 250 ms at 20000 bits.

  The Ziv loop succeeds at the first level (`ln ≈ lnBracket`). **Fix found by the benchmark:**
  `lnApprox`, `piApprox`, `gaussApprox`, `lemniscateApprox` built the bracket *inside* the two
  `Roundable` closures, and `roundingPossible` calls them three times (`l (p+1)`, `h (p+1)`,
  `h p`), so every bracket was computed three times (`ln` and `pi` were 3× `lnBracket`/`piBracket`);
  the bracket is now a `let` outside the closures (as `ln2Approx` already did). The proofs were
  unaffected.
* **Where the time goes.** Above 1000 bits `ln2Bracket` dominates (887 of 1082 ms at 20000 bits):
  not the binary splitting (6 ms for the three series) but the `AzRat` reductions — each GCD of
  the ≈ 51000-bit numerator/denominator takes 190 ms (`az_float_ln2_breakdown`), and the bracket
  does about five of them (`ofAzNatPair` ×3, the `+`/`−`/`·` of the combination). The GCD
  dispatch is the culprit: the *quadratic middle layer* (`halfBinaryGcdQuadraticThreshold =
  65536` bits, tuned on random operands with a planted common factor of a third of the size)
  takes 190 ms on these operands where the forced recursion (`gcdHalfBinaryWith 64 0`) takes
  15 ms (11.4 vs 1.6 ms at 11600 bits); on the `az_nat_gcd` random operands the quadratic layer is
  still slightly faster (25.7 vs 28.5 ms at 50000 bits, 1.5 vs 3.0 ms at 12000).
  **(a) FIXED 2026-10-19** (`docs/gcd_plan.md`): the word base case stalled on a low window
  divisible by `2^62` (the `ln 2` denominators carry `2^(2N)`) and the round fell back to the
  binary GCD; the quadratic round now strips the powers of two and re-pairs, the 51000-bit GCD is
  12.5 ms, and the threshold (re-tuned on planted-factor and coprime operands) stays at 65536
  bits.  `ln` at 20000 bits: 1077 → 429 ms; `ln2Bracket` 887 → 236 ms — the remaining `ln 2`
  cost is the `AzRat` combination of the three fractions (GCDs of 100k–400k-bit numbers).
  **(b) DONE 2026-10-19**: the float bracket of `ln 2` (ledger of the `ln 2` section, Step 4) —
  `ln` at 20000 bits 429 → 145 ms (`ln2Bracket` 236 → 57 ms, now comparable to the AGM's 52 ms),
  at 5000 bits 37 → 14 ms, at 1000 bits 4.0 → 1.7 ms.

## `ln` of a rational for `AzFloat` (DONE 2026-10-19, fuel-free)

Files: `AzFloat/LnRat.lean`, `AzFloat/Equiv/LnRat.lean`, `AzFloat/Tests/LnRat.lean`; the bracket
`lnRatApprox` and its proofs live in `AzFloat/LnBracket.lean` / `Equiv/LnBracket.lean`.

* **Design.** One AGM run, not two: `ln q` for `q = n/d > 0` is bracketed by `ln` of the single
  float `x = ⌊q⌋_w` (`ofAzRatRound q w .Floor`, one division) through `lnBracket x e w`, the
  upper end widened by the exact float `2^(2−w)`: `0 ≤ ln q − ln x = ln (q/x) ≤ q/x − 1 ≤
  2·2^(−w)/(1 − 2·2^(−w)) ≤ 4·2^(−w)`.  (`ln n − ln d` or `ln ⌊q⌋ / ln ⌈q⌉` would double the
  AGM work.)  The float is matched as `x@(finite true e _ _ _)` so that the exponent `e` is the one
  `lnBracket_spec` wants (`eq_finite_true_of_toVal_pos`: a float of positive value has this form).
* **Width.** `lnEps e w` depends on the exponent `e` of `⌊q⌋_w`, which depends on `w`; the Ziv
  certificate needs a width `ε w` depending on `q` only.  From `2^(e−1) ≤ x ≤ q` and
  `q/2 ≤ x < 2^e`: `(e − 1) ln 2 ≤ ln q < (e + 1) ln 2`, so `|e| ≤ |ln q|/ln 2 + 1 ≤ 2|ln q| + 1 ≤
  E := ⌊2|ln q|⌋₊ + 2`, and `lnEps` is monotone in `|e|` (`lnEps_mono`).  The widened end adds
  `4u + 2|hv + 4u| u` with `|hv| ≤ |ln q| + lnEps E w + 4u`; `lnRatEps E |ln q| w` collects
  this and tends to `0` (`tendsto_lnRatEps`, products of limits).  Strictness from
  `irrational_log_rat` on `q` itself.
* **Driver.** `lnRatPrecRound`: `num = 0 ↦ (−∞, .eq)`; `sign = false ↦ (NaN, .eq)`;
  `num = den ↦ (zero, .eq)` (the fraction is reduced, so this is `q = 1`;
  `toRat_eq_one_of_num_eq_den`/`toRat_ne_one_of_num_ne_den`); `p = 0 ↦ (NaN, .eq)`; otherwise
  `zivLoopCertified (lnRatApprox q) p mode (p + 64)` with the certificate from
  `toRat_pos_of_sign`.  Spec `lnRatPrecRound_eq … = roundVal p mode (Spec.log q)` (`Spec.log`
  from `Equiv/Ln`).  Cost: `lnBracket` at `w = p + 64` plus one `AzRat → AzFloat` division.
* **Tests.** Special values; agreement with `ln2` (53/200 bits) and with the float `ln` on
  representable inputs (`10`, `3/2`, `1/2`, also the `Floor` pair); `ln (1/3)`, `ln (22/7)`,
  `ln (3/2)`, `ln (123456789/1000)`, `ln 10^(−12)` at 53 bits; floor/ceiling tags; `ln (1/3)`,
  `ln (22/7)`, `ln (123456789/1000)` at 200 bits against independent 80-digit expansions.
* **Lean notes.** `(2 : AzInt).toInt = 2` is not `rfl` (the `OfNat` instance) — use
  `((2 : ℕ) : AzInt)` and `AzInt.toInt_natCast`; a cast fact about a `set` variable must be
  stated *before* the `set` (`exact_mod_cast` does not see through the local definition);
  `Rat.cast_zero` was not needed after `rw [toRat_eq_zero_iff]` (the coercion chain simplifies
  with `EReal.coe_zero` alone).

## `ln (1 + x)` for `AzFloat` (DONE 2026-10-19, fuel-free; MCA `log1p`)

Files: `AzFloat/LnP1.lean`, `AzFloat/Equiv/LnP1.lean`, `AzFloat/Tests/LnP1.lean`; the bracket
`lnP1Approx` and the generic `lnFloorApprox` live in `AzFloat/LnBracket.lean` / `Equiv/LnBracket.lean`.

* **Method vs MCA.** MCA §4.4.2 / Exercise 4.9 evaluate `log1p` by the reduction
  `log1p(x) = 2 log1p(x/(1 + √(1 + x)))` and a power series, `O(√n M(n))`; the AGM logarithm is
  `O(log n · M(n))`, so `ln (1 + x)` is `ln` of the float `y = ⌊1 + x⌋_w` with the upper end
  widened by `2^(2−w) ≥ ln ((1 + x)/y)` — the `lnRat` construction with `ofAzRatRound q w .Floor`
  replaced by `addPrecRound one x w .Floor`.  Refactor: `lnFloorApprox y w` is the common
  bracket and `lnFloorApprox_spec` the common proof (`y ≤ q ≤ y (1 + 2u)`, `ln q` irrational);
  `lnRatApprox_spec` and `lnP1Approx_spec` are two-line corollaries.
* **Why `log1p` at all.** For `|x| < 1` with exponent `e ≤ 0`, `1 + x` at precision `w` keeps
  only `w + e` bits of `x`, and `ln (1 + x) ≈ x` needs them all: the Ziv loop therefore starts at
  `w₀ = p + 64 + leadingZeroBits e` (`−e`, through `toUInt64`) instead of `p + 64`, so the first
  level determines the rounding (the plain `ln` of a float near `1` would double `w` several
  times to reach the same point).  The certificate is indifferent to `w₀`
  (`exists_isSome_of_irrational_threshold` takes any `w₀ > 0`), and `zivLoopCertified_eq_threshold`
  needs the enclosure only for `w ≥ w₀ ≥ 64`.
* **Driver.** `nan ↦ nan`, `+∞ ↦ +∞`, `−∞ ↦ nan`, `0 ↦ 0` exactly, positive `x` → the loop; negative
  `x = finite false e …`: if `e.sign ∧ e.abs ≠ 0` (exponent `≥ 1`, so `x ≤ −1`:
  `finiteVal_false_le_neg_one`) then `x = −1` (by `eqIEEE x (−one)`, `toVal_neg_one`) gives
  `(−∞, .eq)` and `x < −1` gives `(nan, .eq)`; otherwise `−1 < x < 0`
  (`finiteVal_false_gt_neg_one`, from `|x| < 2^e ≤ 1`) → the loop.  Spec
  `lnP1PrecRound_eq_liftVal : … = liftVal (fun a => Spec.log (a + 1)) x p mode` (`⊤ + 1 = ⊤`,
  `⊥ + 1 = ⊥` by `EReal.top_add_coe`/`EReal.bot_add`).
* **Tests.** Special values; agreement with `ln` on exactly representable `1 + x` (`x = 3, −1/2, 1,
  7`, also the `Floor` pair); `ln (1 ± 2^(−30))` at 53 and 200 bits, `ln (1 + 2^(−100))` at 53
  bits (rounds to `2^(−100)` from above) and 300 bits, against independent 110-digit expansions.
* **Lean notes.** `rw [add_comm]` on a goal containing `zivLoopCertified … (p + 64 + E) h` fails
  (the certificate `h` depends on the start precision — "motive is not type correct"): rewrite
  the specific real sum, `add_comm (finiteVal …) 1`.  A `match` arm `y@(finite true e _ _ _)` is
  reduced in proofs by `subst` of the constructor equation followed by `simp only [lnFloorApprox]`.

## `log₂` for `AzFloat` (DONE 2026-10-19, fuel-free)

Files: `AzFloat/Log2Bracket.lean`, `AzFloat/Log2.lean`, `AzFloat/Equiv/Log2Bracket.lean`,
`AzFloat/Equiv/Log2.lean`, `AzFloat/Tests/Log2.lean`.

* **Exact powers of two first.** The significand `m` of `x = finite true e q m hv` is a power
  of two (`AzNat.isPowerOfTwo`, `isPowerOfTwo_iff`) iff `x = 2^(e−1)` (`finiteVal_true_of_isPowerOfTwo`:
  `m = 2^k`, `m.size = k + 1` by `Nat.size_pow`), and then `log₂ x = e − 1` is returned as
  `setPrecRound (ofAzInt (e − 1)) p mode` — exact with `.eq` when `e − 1` fits `p` bits, correctly
  rounded otherwise (`log₂ 2^100` at 3 bits is `96, .lt`).
* **Irrationality for the rest.** `log₂ n` is irrational for odd `n ≠ 1`
  (`irrational_logb_two_of_odd`): `log₂ n = p/q` gives `2^(p/q) = n` (`Real.rpow_logb`), hence
  `n^q = 2^p` (`rpow_natCast`, `rpow_mul`, `rpow_intCast`; `(r : ℝ) · r.den = r.num` from
  `Rat.cast_def`); for `p ≥ 0` parity (`Nat.even_pow`; `p = 0` forces `n = 1`), for `p < 0`
  `2^p < 1 ≤ n^q`.  A float value is `(2^k n) 2^j` with `n` odd (`Nat.exists_eq_two_pow_mul_odd`),
  `n ≠ 1` unless the significand is a power of two, and `log₂ (n 2^j) = log₂ n + j`
  (`Real.logb_mul`, `logb_two_zpow`) is irrational by `Irrational.add_intCast`.
* **The bracket.** `ln x / ln 2` from `lnBracket` (`[a, b]`) and `ln2Bracket` (`[c, d]`,
  `c ≥ 1/5`): since the sign of `ln x` is unknown, the lower end is `⌊a/d⌋` for `a ≥ 0` and
  `⌊a/c⌋` for `a < 0` (`isNegative`, `toVal_sign_of_isNegative`), symmetrically above
  (`log2Lower_spec`, `log2Upper_spec`).  Width: `Q − q ≤ (b − a)/c + (|a| + |b|)(1/c − 1/d)` with
  `1/c − 1/d = (d − c)/(cd) ≤ 8u/((1/5)(0.69)) ≤ 60u`, plus the two roundings `2 (|·|/c) u ≤
  10 (|ln x| + ε) u`; `log2Eps e A w = 5 lnEps e w + 140 (A + lnEps e w) u`.  The exponent `e` of
  `x` is fixed, so no exponent bound is needed (unlike `lnRat`).  Cost: one `lnBracket` plus the
  `ln 2` bracket and two divisions.
* **Spec.** `Spec.log2` as `Spec.log` with `Real.logb 2`; `log2PrecRound_eq_liftVal`.
  `log₂ 0 = −∞`, negatives and `−∞` `NaN`, `+∞ ↦ +∞`.
* **Tests.** Special values; exact powers (`1, 2, 8, 1/4, 2^(−30), 2^100` at 53 bits, `2^100` at
  3 bits in three modes); `log₂ 10, 3, 1/3, 3/2, 10^6, 5` at 53 bits (the input `F "1/3" 53` is the
  double below `1/3`, so its logarithm ends in `…563`, not `…56`); floor/ceiling tags; `log₂ 10`
  and `log₂ 3` at 200 bits *against 80-digit rational references rounded to 200 bits* (sharper
  than a decimal string: the shortest round-trip string of a 200-bit float can differ from the
  correctly rounded expansion in its last digit, as `log₂ 10` showed — `…757` vs `…7563`).
* **Lean notes.** `le_or_lt` is gone (`le_or_gt`); the implicit `v` of
  `exists_isSome_of_irrational_threshold` must be fixed by a `have hirr` before `exact`, or the
  `rw [Real.log_div_log]` inside its argument sees a metavariable.

## `log₂` of a rational for `AzFloat` (DONE 2026-10-19, fuel-free)

Files: `AzRat/Pow2.lean` (+ `Equiv`, `Tests`), `AzFloat/Log2Rat.lean`, `AzFloat/Equiv/Log2Rat.lean`,
`AzFloat/Tests/Log2Rat.lean`; brackets and proofs in `AzFloat/Log2Bracket.lean` /
`Equiv/Log2Bracket.lean` (refactored: `log2Quotients` is the shared quotient step, `lnFloorBracket`
the shared float-level `ln` bracket of `⌊q⌋_w`).

* **Power-of-two test for `AzRat`** (new, `AzRat.isPowerOfTwo`): positive with numerator and
  denominator powers of two (`AzNat.isPowerOfTwo`); since the fraction is reduced one of them is
  `1`, so `q = 2^k` with `k = powerOfTwoExponent q = size num − size den`
  (`toRat_of_isPowerOfTwo`, from `Nat.size_pow`).  The exact branch returns
  `setPrecRound (ofAzInt k)`.
* **Irrationality.** `log₂ q` for a positive rational that is not a power of two: with
  `num = 2^a n`, `den = 2^b d` (`n, d` odd, coprime since `num, den` are), `log₂ q = log₂ (n/d) +
  (a − b)`, and `log₂ (n/d) = p/q'` would give `n^q' = 2^p d^q'`: for `p > 0` the right side is
  even and the left odd, for `p < 0` symmetrically (`n^q' 2^(−p) = d^q'`), and for `p = 0`
  `n^q' = d^q'` forces `n = d` (`Nat.pow_left_injective`), hence `n = d = 1` by coprimality
  (`Nat.coprime_self`) — but then `num, den` were powers of two (`irrational_logb_two_of_odd_div`,
  `irrational_logb_two_div`, `irrational_logb_two_toRat`).
* **Bracket.** `log2Quotients (lnFloorBracket ⌊q⌋_w w) w`: one AGM run and three divisions
  (`4/y` inside `lnBracket`, two for the quotient) plus the `ln 2` bracket.  Width
  `log2RatEps E |ln q| w = 5 lnRatEps E |ln q| w + 140 (|ln q| + lnRatEps …) 2^(−w)` with
  `E = ⌊2 |ln q|⌋ + 2` (`log2Quotients_spec` applied to `lnFloorBracket_spec`).
* **Spec.** `log2RatPrecRound_eq … = roundVal p mode (Spec.log2 q)`.
* **Tests.** `AzRat.isPowerOfTwo` on `1, 2, 8, 1/8, 2^100` (true) and `0, −8, −1/8, 3, 6, 3/4, 1/6`
  (false) with the exponents through `toInt64`; `log2Rat`: special values, exact powers
  (`1, 8, 1/8, 2^(−100)`, `2^100` at 3 bits), agreement with `log2` on representable inputs,
  `log₂ (1/3), (22/7), (3/2), (10^6/7)` at 53 bits (here `1/3` is exact, so `…56`), tags, and
  `log₂ 10`, `log₂ (1/3)` at 200 bits against 80-digit rational references.
* **Lean note.** `AzRat.toRat_eq_zero_iff` is stated over the *real* cast
  `((toRat q : ℚ) : ℝ) = 0`, not the rational — rewrite the real-valued hypothesis.

## `log₂ (1 + x)` for `AzFloat` (DONE 2026-10-19, fuel-free; C23 `log2P1`)

Files: `AzFloat/Log2P1.lean`, `AzFloat/Equiv/Log2P1.lean`, `AzFloat/Tests/Log2P1.lean`; the
bracket `log2P1Approx`, the exactness test `onePlusPow2Exponent?` and their proofs in
`AzFloat/Log2Bracket.lean` / `Equiv/Log2Bracket.lean`.

* **Exact case `1 + x = 2^k`** (`x = 2^k − 1`: `1, 3, 7, …, −1/2, −3/4, …`).  Computable test
  without forming the sum exactly: `sLo = ⌊1 + x⌋_w₀`, `sHi = ⌈1 + x⌉_w₀` at the starting precision;
  if `eqIEEE sLo sHi` the sum is exact (`lo ≤ 1 + x ≤ hi = lo`), and if the significand of `sLo` is
  a power of two the sum is `2^(e−1)` — return `e − 1` (`onePlusPow2Exponent?_some`).  Conversely a
  power of two `2^j` lies in `floatSet w` for every `w ≥ 1` (`mem_floatSet_mul_zpow` with `k = 1`),
  so both roundings return it (`val_round_of_mem`), `eqIEEE` holds and the significand is a power
  of two (`isPowerOfTwo_of_finiteVal_eq_zpow`); hence `none` means `1 + x ≠ 2^j` for all `j`
  (`onePlusPow2Exponent?_none`).
* **Irrationality for the loop.** `irrational_logb_two_of_rat`: a positive rational `v = r` with
  `v ≠ 2^j` for all `j` has irrational `log₂ v` — `r = N/D` reduced (`Rat.reduced`, `Rat.num_pos`,
  `Nat.cast_natAbs`), not both powers of two, then `irrational_logb_two_div`.  Applied to
  `1 + x = 1 + r_x` (`exists_rat_of_toVal`).
* **Bracket.** `log2Quotients (lnFloorBracket ⌊1 + x⌋_w w) w`: the `lnP1` bracket divided by the
  `ln 2` bracket; width `log2RatEps E |ln (1 + x)| w` (`log2P1Approx_spec` from
  `lnFloorBracket_spec` and `log2Quotients_spec`).  The Ziv loop starts at
  `p + 64 + leadingZeroBits e` as `lnP1` does, for the same reason (small `|x|`).
* **Driver and spec.** As `lnP1PrecRound` (sign/exponent tests `finiteVal_false_le_neg_one`,
  `finiteVal_false_gt_neg_one`, `eqIEEE x (−one)`), with `match h : onePlusPow2Exponent? x w₀ with`
  before the loop; the certificate uses `h` through `irrational_logb_two_one_add_of_none`.  The
  common finite case is `log2P1_finite_eq` (`split` on the `match`, `rename_i`), so the main
  theorem handles only the special values.  New `addFloor_abs` in `Equiv/DirectedRounding`.
* **Tests.** Special values; exact `x = 1, 3, 7, −1/2, −3/4, −7/8` and `2^100 − 1` at 110 bits;
  agreement with `log2` on `1 + x = 10, 3, 3/4`; `log₂ (3/2)`, `log₂ (1 + 2^(−30))` at 53 bits
  with tags; `log₂ 3`, `log₂ 10` at 200 bits via `x = 2, 9` against the rational references.
* **Lean notes.** `rcases h : e with … | ⟨a, b, c, d, e⟩` — constructor fields need the anonymous-
  constructor brackets, and `rcases h : e` already substitutes `e` in the context (no `rw [h]` later).

## Reciprocal (DONE 2026-10-19, thin wrapper)

`AzFloat/Recip.lean`, `Equiv/Recip.lean`, `Tests/Recip.lean`: `recipPrecRound y p mode =
divPrecRound one y p mode`, `recip y`; spec `recipPrecRound_eq_liftVal` (`liftVal (fun a =>
Spec.div 1 a)`) is the division spec with `toVal_one'`.  Assessment of a dedicated routine: the
integer division takes the Newton path for a `2n`-by-`n` quotient only from 32768 limbs, so a
reciprocal built on `approxReciprocal` (`A X < β^(2n) < A (X + 2)`) plus one exact remainder
product and a one-unit fix could be dispatched from a few thousand limbs and skip the Barrett
multiplication by the dividend — an estimated 1.3–2× there, nothing at small precision; not done
because divisions are a negligible share of the transcendental functions' cost (1.1 of 99 ms in
`ln` at 20000 bits).

## Correctly rounded `Float` functions through `AzFloat` (DONE 2026-10-19)

Malachite's `malachite-float` offers primitive-float versions of its `Float` functions
(`primitive_float_sum`, say) that compute in a `Float` at `MANTISSA_WIDTH + 1` bits in
round-to-nearest, keep the ternary, re-round into the subnormal range with the ternary
(`subnormalize_assign`), send results above the largest finite value to `∞`, and convert.  The
same recipe on `AzFloat`:

* `AzNat/ShiftRightNearestTernary.lean` (+ `Equiv/`, `Tests/`): `shiftRightNearestTernary n o sh`,
  nearest right shift with an exact tie resolved by the ternary `o` (`.lt`: the true value is
  above the stored one, round up; `.gt`: down; `.eq`: to even); `AzInt` version swaps the ternary
  for negatives.  Spec `NearestTernary (n / 2^sh) q o`.
* `Rounding/IntNearest.lean`: `round intSet .Nearest` is a nearest integer
  (`abs_toInt_round_nearest_sub_le`), ties to even (`toInt_round_nearest_half`), and
  `toInt_round_nearest_of_ternary`: if `X` is a nearest point to `w` among a grid containing the
  integers and the half-integers, and `R` is `NearestTernary X R (compare X w)`, then `R` is the
  nearest integer to `w`.  This is why one 53-bit rounding plus the ternary suffices below
  `2^-1022`: the 53-bit grid contains the subnormal grid (multiples of `2^-1074`) and its midpoints.
* `AzFloat/Float64Emulate.lean`: `toUnpackedTernary` (= `toUnpacked … .Nearest` with the subnormal
  shift replaced by `shiftRightNearestTernary`), `emulateFinish : AzFloat × Ordering → Float`,
  wrappers `emulate`/`emulate₂`/`emulateRat`/`emulateList`.  Emulated functions live next to the
  operations they wrap: `sumFloat64 : List Float → Float` in `AzFloat/Sum.lean`, its spec
  `toVal_sumFloat64` in `Equiv/Sum.lean`, its tests in `Tests/Sum.lean`.
  Likewise `productFloat64` / `toVal_productFloat64` in `Product.lean` / `Equiv/Product.lean` /
  `Tests/Product.lean` (2026-10-19); tests include intermediate over/underflow that the exact
  product ignores (`[1e200, 1e200, 1e-300] = 1e100`) and the `maxF · (1 + 2^-53) → ∞` threshold.
* `Equiv/Float64Emulate.lean`: `roundBinary64 v : EReal` (IEEE nearest-even to binary64),
  `roundBinary64Val`, and `toVal_emulateFinish_roundVal (w : Option EReal) :
  (emulateFinish (roundVal 53 .Nearest w)).toModel.unpack.toVal = roundBinary64Val w`.  Since
  every proven operation equals a `roundVal`/`liftVal`, every emulated function is correctly
  rounded with no further work (`toVal_emulate` etc.).  Proof
  structure: `toUnpackedTernary_finite` packages the result as `finishUnpacked s r t .Nearest` with
  `NearestTernary (x / 2^t) r o`; the input has precision 53 (`ofEReal_spec`), so in the normal
  range `x / 2^t` is the signed core significand (exact, `eq_of_nearestTernary_intCast`), with
  `toVal_finishUnpacked_overflow` for `e ≥ 1025`; in the subnormal range `t = −1074` and
  `toInt_round_nearest_of_ternary` applies with `B = 2^52`, the closeness hypotheses coming from
  the 53-bit scale `σ = 2^(⌊log₂|v|⌋ − 52) ≤ 2^-1075` (every `n · 2^-1075` is an integer multiple
  of `σ`).

Limitations: an exact zero result is `+0.0` (`AzFloat` has a single zero, so `−0.0` sums are not
reproduced); only round-to-nearest is emulated (as in Malachite).  Tests
(`Tests/Float64Emulate.lean`) include the double-rounding witness
`a = (1 + 2^-52) 2^-1000`, `b = (1 − 2^-53) 2^-75`: `a·b = 2^-1075 (1 + 2^-53 − 2^-105)` rounds at 53
bits to exactly `2^-1075` (ternary `.lt`), which `toFloat64` alone sends to `0` and
`emulate₂ mulPrecRound` correctly to `2^-1074`; sums with cancellation (`[1e16, 1, 1]`,
`[1e100, 1, −1e100]`), overflow at the exact IEEE threshold (`maxF + 2^970 → ∞`, `+ 2^969 → maxF`),
`ln 2` to the correctly rounded double, and the special values.

## Fused multiply-add and multiply-subtract (DONE 2026-10-20)

`AzFloat/AddMul.lean`, `Equiv/AddMul.lean`, `Tests/AddMul.lean`.  `addMulPrecRound x y z p mode`
is `x + y·z` rounded once and `subMulPrecRound` is `x − y·z`: the product is formed exactly by
`exactMul y z = (mulPrecRound y z (q_y + q_z) .Floor).1` and then one `addPrecRound`/`subPrecRound`
rounds.  `toVal_exactMul` proves the product exact on every input: for finite operands
`finiteVal_eq_int_mul_prec` writes each as `k_i · 2^(e_i − q_i)` with `|k_i| < 2^(q_i)`, so the
product is `k₁k₂ · 2^(…)` with `|k₁k₂| < 2^(q₁+q₂)` and `mem_floatSet_mul_zpow` puts it in
`floatSet (q₁+q₂)`, where rounding is the identity (`toVal_fst_roundVal`: `roundVal` returns a
float of the given value when it is `NaN`, an infinity, or a real in `floatSet p`); the special
values are `Spec.mul`'s.  Specs: `liftVal₃`, `Spec.addMul a b c = (Spec.mul b c).bind (Spec.add a)`,
`addMulPrecRound_eq_liftVal₃`, `subMulPrecRound_eq_liftVal₃` (both one-line consequences of
`toVal_exactMul` and the add/sub specs via `Option.bind_assoc`).  Default-precision `addMul`/`subMul`
use the largest operand precision.  `Float` versions `addMulFloat64`/`subMulFloat64` (IEEE `fma`)
through the new `emulate₃`/`toVal_emulate₃`.  Tests: the classic fused witness
`x = −(1 + 2^-51)`, `y = z = 1 + 2^-52` gives `2^-104` exactly (separate operations give `0`), the
rounding tags at 3 bits, `0·∞` and `∞ − ∞` to `NaN`, and `+0.0` for an exact zero `Float` result.

## Fused multiply-add and multiply-subtract with a rational factor (DONE 2026-10-20)

`AzFloat/AddMulRat.lean`, `Equiv/AddMulRat.lean`, `Tests/AddMulRat.lean`.  For floats `x`, `y`
and a rational `z`, `addMulRatPrecRound x y z p mode = x + y·z` rounded once, `subMulRatPrecRound`
likewise for `x − y·z`.  Both are instances of `fusedMulRat opF opR`: a finite `y` is converted
exactly to a rational (`toAzRat?`), the product `y·z` is exact in `AzRat`, and the float–rational
operation `opR` (`addRatPrecRound`/`subRatPrecRound`, Ziv loops already proven) performs the single
rounding; an infinite `y` becomes `infinity (s == z.sign)` (`NaN` when `z = 0`) and the float–float
operation `opF` (`addPrecRound`/`subPrecRound`) handles it.  `fusedMulRat_eq` proves the shape
correctly rounded from the two operation specs (`toVal_of_toAzRat?`, `sign_eq_decide_pos`,
`Spec.mul_inf_coe`), giving `addMulRatPrecRound_eq_liftVal₂`/`subMulRatPrecRound_eq_liftVal₂` with
`Spec.addMul a b ↑z`/`Spec.subMul`.  `Float` versions `addMulRatFloat64`/`subMulRatFloat64` through
the new wrapper `emulate₂Rat` (two `Float`s and an `AzRat`) with `toVal_emulate₂Rat`.  Tests: agreement with `addRatPrecRound` for `y = 1`, exact results, the
one-rounding witness `−1 + (1 + 2^-52)(1 + 2^-52) = 2^-51 + 2^-104` (tag `.lt`, where a rounded
product would be exact), rounding tags at 3 bits, special values.

## Sums and differences of two products (DONE 2026-10-20)

`AzFloat/MulAddMul.lean`, `Equiv/MulAddMul.lean`, `Tests/MulAddMul.lean`.
`mulAddMulPrecRound x y z w p mode = x·y + z·w` rounded once and `mulSubMulPrecRound` for
`x·y − z·w`: both products exact (`exactMul`), then one `addPrecRound`/`subPrecRound`.  Specs
`liftVal₄`, `Spec.mulAddMul`/`Spec.mulSubMul`, `mulAddMulPrecRound_eq_liftVal₄`/
`mulSubMulPrecRound_eq_liftVal₄`; the only work beyond `toVal_exactMul` is `bind_products`, which
commutes the bind of the first (closed) product past the binds of `z` and `w` by cases.  `Float`
versions `mulAddMulFloat64`/`mulSubMulFloat64` through the new `emulate₄`/`toVal_emulate₄`.
Tests: the witness `x = y = 1 + 2^-52`, `z = 1 + 2^-51`, `w = 1` with `x·y − z·w = 2^-104` exactly
(separate roundings give `0`), rounding tags at 3 bits, `0·∞`/`∞ − ∞` to `NaN`, intermediate
overflow `(10^200)^2 − (10^200)^2 = 0`, and `+0.0` for an exact zero `Float` result.

## A product plus or minus a product with a rational factor (DONE 2026-10-20)

`AzFloat/MulAddMulRat.lean`, `Equiv/MulAddMulRat.lean`, `Tests/MulAddMulRat.lean`.  For floats
`x`, `y`, `z` and a rational `w`, `mulAddMulRatPrecRound x y z w p mode = x·y + z·w` rounded once
and `mulSubMulRatPrecRound` for `x·y − z·w`: `exactMul x y` then `addMulRatPrecRound`/
`subMulRatPrecRound` (which forms `z·w` exactly in `AzRat` and rounds once).  Specs
`mulAddMulRatPrecRound_eq_liftVal₃`/`mulSubMulRatPrecRound_eq_liftVal₃` with `Spec.mulAddMul a b c ↑w`,
from `toVal_exactMul`, the `AddMulRat` specs and `bind_product_left` (the closed product bind
commutes past the bind of `z`).  `Float` versions `mulAddMulRatFloat64`/`mulSubMulRatFloat64`
through the new `emulate₃Rat`/`toVal_emulate₃Rat`.  Tests: the witness `x = y = 1 + 2^-52`,
`z = −1`, `w = 1 + 2^-51` with `x·y + z·w = 2^-104` exactly, agreement with `addRatPrecRound` when
`z = 1`, rounding tags at 3 bits, special values, `+0.0` for an exact zero `Float` result.

## Rounding to an integer (DONE 2026-10-20)

`Rounding/IntPrecision.lean`, `AzFloat/RoundToInteger.lean`, `Equiv/RoundToInteger.lean`,
`Tests/RoundToInteger.lean`.  `roundToIntegerPrecRound x p mode : AzFloat × Ordering × Bool`
rounds `x` in `mode` to an integer representable at precision `p` in a single step (`10.5` to
nearest at 2 bits is `12`, the nearer of the 2-bit integers `8` and `12`), returning the comparison
with `x` and whether `x` was an integer (the information of `mpfr_rint`'s ternary: `(.eq, true)`
unchanged, `(.lt/.gt, true)` an integer rounded to fit, `(.lt/.gt, false)` a non-integer,
`(.eq, false)` impossible); `NaN`, `±∞`, zero unchanged with `.eq`, only zero an integer.
Specification: the new rounding target `intPrecisionSet p` (integers of `precisionSet 2 p`),
whose floor/ceiling are the integer ones below `2^(p−1)` and the `p`-bit ones from there on, and
whose tiebreak `ipTiebreak` is `precTiebreak`'s parity rule at the local scale floored at `1`
(so ties below `2^(p−1)` go to the even integer, as in `intSet`, and above to the even
coordinate, as in `precisionSet`; `precTiebreak` itself is *not* ties-to-even on integers below
the scale).  Characterizations `val_round_intPrecision_small` (`= round intSet mode x`) and
`val_round_intPrecision_large` (`= round (precisionSet 2 p) mode x`), proved by matching floors,
ceilings and tiebreaks (`ipTiebreak_consecutive`/`intTiebreak_consecutive` on a tie between
consecutive integers).  Implementation: exponent `≥ p` or `x` already an integer →
`setPrecRound x p mode` (every `p`-bit value near `x` is an integer) with `isInteger`
(`isMultipleOfPow2` on the fractional bits); otherwise `|x| < 2^(p−1)` and the integer rounding is
`AzInt.shiftRightRound` of the core significand, placed at precision `p` exactly.
`roundToIntegerPrecRound_spec` ties the three components to `round (intPrecisionSet p) mode v`,
`compare`, and `∃ n : ℤ, v = n`.  Wrappers `roundToIntegerPrec`, `roundToIntegerRound`,
`roundToInteger`.  Tests: the 2-bit examples (`10 → 8` as `(.lt, true)` on a tie, `10.5 → 12`),
all five modes on `±29/4`, ties to even on `±5/2`, `7/2`, `±1/2` (to `zero`), the boundary
`7.5 → 8` at 3 bits, `2^100 + 3/4` at 200 and 5 bits.

## Rounding to an integer, then to a precision (DONE 2026-10-20)

`roundToIntegerThenPrecRound x irm p rm : AzFloat × Ordering` (Malachite's
`round_to_integer_then_prec_round`, MPFR's `mpfr_rint_*`): the exact integer rounding of `x` in
`irm`, then that integer correctly rounded to `p` bits in `rm`, with the comparison against the
exact integer; with both modes `Nearest`, `10.5 → 10 → 8` at 2 bits, where the single rounding
gives `12`.  Implementation: `setPrecRound (roundToIntegerPrecRound x q irm).1 p rm` with `q` the
float's own precision — at its own precision the single-step rounding is exactly the integer
rounding (`toVal_roundToIntegerPrecRound_self`: below `2^(q−1)` by the small characterization,
above it `x` is already an integer of `precisionSet 2 q`, so both roundings are the identity).
Spec `roundToIntegerThenPrecRound_eq_liftE : = liftE (Spec.rint irm) x p rm` with
`Spec.rint irm v = (round intSet irm v).val` (`±∞` pass through); the specials go through the
final rounding only.  `roundToIntegerThenPrec` (nearest).  Tests contrast the two forms on `10.5`
at 2 bits and cover the modes, small values, and integers passing through.

## Remainder (DONE 2026-10-20)

`AzFloat/Rem.lean`, `Equiv/Rem.lean`, `Tests/Rem.lean` (Malachite's `rem_prec_round`, C's
`fmod`).  `remPrecRound x y p mode = setPrecRound (remExact x y) p mode`: the exact remainder
`x − y·trunc(x/y)` is a float, formed exactly.  With `|x| = X·2^a`, `|y| = Y·2^b`: `|x| < |y|`
(`absLt`) gives `x`; `b ≤ a` gives `sign x · ((X·2^(a−b)) mod Y) · 2^b` with the shift never
formed — `AzNat.shiftLeftMod a k n = ((a mod n)(2^k mod n)) mod n` through `AzZMod.pow`, so a
huge exponent gap (`2^1000000 mod 7`) costs `O(log k)` modular multiplications; `a < b` gives
`sign x · (X mod (Y·2^(b−a))) · 2^a`, the shift bounded by `|y| ≤ |x|`.  Specification
`Spec.rem a b = a − b·trunc(a/b)` with `trunc = round intSet .Down` (`toInt_round_down`), `NaN`
for infinite `a` or `b = 0`, `a` for infinite `b`; `remPrecRound_eq_liftVal₂`.  Proof core:
`rem_scaled` (the integer identity `X − Y·(X/Y) = X mod Y` scaled by `2^c` with signs, through
`toInt_round_down_sign_div`: truncation of `±X/Y` is `±(X/Y)` in ℕ), `AzNat.toNat_shiftLeftMod`
(via `toZMod_pow`/`ZMod.val_natCast`), `toInt_round_down_of_abs_lt_one`.  `%` instance at the
larger precision, nearest.  No signed zero: an exact zero remainder is `zero`.  Tests: signs
(`−7 mod 3 = −1`, `7 mod −3 = 1`), `2^1000000 mod 7 = 2`, `(2^100 + 2^50) mod 3 = 2`, the tie
`37/16 mod 1 = 5/16` at 2 bits, infinite divisors, the specials.

## Base-2 logarithms of naturals and rationals (DONE 2026-10-20)

`AzNat.floorLogBase2`/`ceilingLogBase2 : AzNat → Option ℕ` (`none` for `0`; `size − 1`, and `size`
unless a power of two; specs `floorLogBase2_eq = some (Nat.log 2 n)`, `ceilingLogBase2_eq =
some (Nat.clog 2 n)` via `size_bounds`), `AzNat.checkedLogBase2 n : Option ℕ` (`AzNat/LogBase2.lean`,
`some k` iff `n = 2^k`, from `isPowerOfTwo` and `size`; `checkedLogBase2_eq_some_iff`/`_none_iff`), the power-of-two-base
versions `floorLogBasePowerOf2`/`ceilingLogBasePowerOf2`/`checkedLogBasePowerOf2 n k` (base `2^k`,
`none` for `k = 0`; exponents divided by `k`, via Mathlib's `Nat.log_pow_left`/`clog_pow_left`) and
`AzRat.checkedLogBase2 q : Option AzInt` (`AzRat/LogBase2.lean`, `some k` iff `q = 2^k`, from
`isPowerOfTwo` and `powerOfTwoExponent`; specs in `AzRat/Equiv/LogBase2.lean`, with
`toRat_of_isPowerOfTwo` moved there from `Equiv/Log2Bracket` and the new converse
`isPowerOfTwo_of_toRat_eq_zpow`).  `log2RatPrecRound` now matches on `q.checkedLogBase2` for its
exact branch (same computation as before; `checkedLogBase2_eq_some`,
`isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none` bridge the proof).  `log2PrecRound` on floats
keeps `isPowerOfTwo` on the significand: a power-of-two float is `1000…0 · 2^(e − p)` whatever
its precision, so a checked log of the significand would always be `p − 1` and carries nothing
beyond the Boolean test; the exponent `e − 1` is the answer.

## Logarithms of naturals in a general base (DONE 2026-10-20)

`AzNat/LogBase.lean`, `Equiv/LogBase.lean`, `Tests/LogBase.lean`: `floorLogBase b n`,
`ceilingLogBase b n`, `checkedLogBase b n : Option ℕ` (`none` for `b ≤ 1` or `n = 0`).  The
floor is `floorLogSearch`, a binary search on the exponent maintaining `b^lo ≤ n < b^hi` (one
`b.pow mid ≤ n` comparison per step), seeded as suggested by a `Float` estimate: `approxLog2 m` is
`log₂` of the top 64 bits plus the bits below (`estimateLogBase b n = ⌊approxLog2 n / approxLog2
b⌋`), the bracket `[e − 1, e + 2)` around it is checked with two power comparisons and used when
valid, else the always-valid `[0, size n)`.  Correctness is independent of the estimate:
`floorLogSearch_eq` holds for any valid bracket, `floorLogBase_eq : = some (Nat.log b n)`,
`ceilingLogBase_eq : = some (Nat.clog b n)` (floor plus one unless `b^floor = n`),
`checkedLogBase_eq_some_iff : = some e ↔ n = b^e`.  Tests: bases 10, 3, 2, 7, 1000, `2^100 ± 1`
around powers and at `10^300`.

## Rational ceiling and checked logarithms in a general base (DONE 2026-10-20)

`AzRat.ceilingLogBaseAbs b q : ℤ` and `AzRat.checkedLogBaseAbs b q : Option ℤ` (`AzRat/LogBase.lean`,
`b : UInt64 ≥ 2`): the existing `floorLogBaseAbs` plus one exact comparison `cmpPowAbs b e q` of
`b^e` with `|q|`.  Specs `ceilingLogBaseAbs_eq : = Int.clog b |toRat q|` (for `q ≠ 0`; `0` for
`q = 0`, the convention of the existing floor) and `checkedLogBaseAbs_eq_some_iff : = some e ↔
|toRat q| = b^e`, from `floorLogBaseAbs_eq`, `cmpPowAbs_eq`, `Int.le_zpow_iff_clog_le`/
`zpow_lt_iff_lt_clog`/`clog_zpow`.  Tests `AzRat/Tests/LogBase.lean` (bases 10, 3, 2; fractions,
negatives, the powers `3^±20`, `10^18 + 1`).  Note: `floorLogBaseAbs`/`ceilingLogBaseAbs` keep the
`ℤ`-with-`0`-at-zero convention of the pre-existing floor (used by `toSci`), unlike the new `AzNat`
functions, which return `Option`.

## Rational bases for the rational logarithms (DONE 2026-10-20)

`AzRat.floorLogBaseRatAbs`/`ceilingLogBaseRatAbs`/`checkedLogBaseRatAbs b q : Option ℤ` for a
rational base `b` (`none` unless `0 < b`, `b ≠ 1`, `q ≠ 0`).  For `b > 1`: `cmpPowRatAbs b e q`
compares `b^e` with `|q|` by cross-multiplication (`num_b^n · den_q` vs `den_b^n · num_q`, reciprocal
for `e < 0`); `floorLogSearchRat` is the binary search on the exponent; the bracket is the
`Float` estimate `estimateLogBaseRat` (from `AzNat.approxLog2` of the four numerators and
denominators) verified by two comparisons, else the doubling brackets `bracketHi`/`bracketLo` from
`1` with fuel `size (den b) + size (num q) + size (den q)` — enough because Bernoulli gives
`b^(2^F) ≥ 1 + 2^F/den b > max (num q, den q)` (`lt_pow_two_pow`), so the last doubling is always a
valid bracket.  A base in `(0, 1)` goes through its reciprocal: `⌊log_b x⌋ = −⌈log_{1/b} x⌉`
(`Real.logb_inv_base`).  Specs `floorLogBaseRatAbs_eq : = some ⌊logb b |q|⌋`,
`ceilingLogBaseRatAbs_eq`, `checkedLogBaseRatAbs_eq_some_iff : = some e ↔ |q| = b^e` (real
`Real.logb`, via `floor_logb_eq`/`ceil_logb_eq` from `Real.logb_le_logb`/`logb_lt_logb_iff` and
`logb_zpow'`).  Tests: bases `3/2`, `2/3`, `1001/1000` (exponent 13822 for `10^6`), `1/10`, and
agreement with the `UInt64` versions; `2^1000` in base `3/2` gives 1709.

## Rational logarithms in power-of-two bases (DONE 2026-10-20)

`AzRat.floorLogBasePowerOf2Abs`/`ceilingLogBasePowerOf2Abs`/`checkedLogBasePowerOf2Abs q k :
Option ℤ` (base `2^k`; `none` for `q = 0` or `k = 0`): the base-2 exponents `floorLogBase2Abs`/
`ceilingLogBase2Abs` floor- and ceiling-divided by `k`, and for the checked version the exponent
`size num − size den` when numerator and denominator are powers of two (on `|q|`, so the sign is
ignored) and `k` divides it.  Specs `floorLogBasePowerOf2Abs_eq : = some (Int.log (2 ^ k) |q|)` and
`ceilingLogBasePowerOf2Abs_eq : = some (Int.clog (2 ^ k) |q|)` through `int_log_two_pow`
(`Int.log (2^k) r = Int.log 2 r / k`) and `int_clog_two_pow` (`Int.clog (2^k) r = −((−Int.clog 2 r)
/ k)`), both by the `zpow`/`log` characterizations and `Int.emod_add_ediv`;
`checkedLogBasePowerOf2Abs_eq_some_iff : = some e ↔ |q| = (2^k)^e` through `abs_toRat_eq_zpow_iff`.
Tests: bases 16, 8, 1024 on integers, fractions and negatives, `2^100 = 1024^10`.  This completes
the non-`AzFloat` logarithm plan (1–5).

## `log_{2^k}` for `AzFloat` (DONE 2026-10-25, fuel-free)

`AzFloat/LogBasePow2Bracket.lean`, `LogBasePow2.lean`, `Equiv/…`, `Tests/LogBasePow2.lean`.
`logBasePow2PrecRound x k p mode` for `k : AzInt` (possibly negative; `k = 0`, base `1`, gives
`NaN`): `log₂ x / k`.  Exact branch: a power-of-two significand is `2^(e−1)`, so the value is the
rational `(e − 1)/k` and `ofAzRatRound (AzRat.ofAzInts (e − 1) k)` rounds it once; otherwise
`log₂ x / k` is irrational (`irrational_logb_two_finiteVal`, `Irrational.div_intCast`) and the
certified Ziv loop runs on `logBasePow2Approx`: the `log₂ x` bracket (`log2Quotients (lnBracket x)`)
divided by the exact float `|k|` with `divPrecRound … .Floor/.Ceiling`, ends negated and swapped
for `k < 0`.  The width bound `logBasePow2Eps e A w = log2Eps e A w + 4 (2A + log2Eps e A w) 2^-w`
(with `A = |ln x|`, `|log₂ x| ≤ 2 |ln x|` from `log 2 > 1/2`) reuses `log2Lower_spec`/`log2Upper_spec`
with the constant divisor bracket `(|k|, |k|)`, so no new division error lemma was needed.
Specials: `±∞` and `0` map to `±∞`/`∓∞` by the sign of `k` (`Spec.logBasePow2 k a = (log2 a).map
(· * ↑(k⁻¹))`, with `EReal.top_mul_coe_of_pos/neg`).  Tests: exact cases (`log₁₆ 8 = 3/4`,
`log₈ 2 = 1/3` rounded with tag), `k = ±1` against `log2PrecRound`, `log₁₆ 10` at 150 bits against
a 57-digit reference, `log_{2^1000} 10` at 100 bits.

## `log_{2^k}` of a rational for `AzFloat` (DONE 2026-10-25, fuel-free)

`AzFloat/LogBasePow2Rat.lean`, `Equiv/LogBasePow2Rat.lean`, `Tests/LogBasePow2Rat.lean`:
`logBasePow2RatPrecRound q k p mode = log₂ q / k` for `q : AzRat`, `k : AzInt ≠ 0`.  Exact branch:
`AzRat.checkedLogBase2 q = some j` gives the rational `j/k` through `ofAzRatRound (AzRat.ofAzInts
j k)`; otherwise the Ziv loop on `logBasePow2RatApprox q k w`.  The bracket machinery was
refactored for this: `divBracketByInt B k w` (in `LogBasePow2Bracket.lean`) divides any bracket
`B` of a value `L` by `|k|` with directed rounding (negating and swapping for `k < 0`), and
`divBracketByInt_spec` proves the bracket of `L / k` with width `ε + 4 (|L| + ε) 2^-w` once and for
all; `logBasePow2Approx` (float) and `logBasePow2RatApprox` (rational, from `log2Quotients
(lnFloorBracket ⌊q⌋_w)`) are instances with widths `logBasePow2Eps`/`logBasePow2RatEps`.  Spec
`logBasePow2RatPrecRound_eq : = roundVal p mode (Spec.logBasePow2 k.toInt (toRat q))`; `q = 0`
gives `∓∞` by the sign of `k`, `q < 0` and `k = 0` give `NaN`.  Tests: exact `j/k` cases in
every direction, `k = ±1` against `log2RatPrecRound`, `log₁₆ 10` and `log₁₆ (1/10)` at 150 bits,
`log₈ (7/3)` at 60 bits (reference from `Decimal.ln`), `log_{2^1000} 10`.

## `log_b` for `AzFloat`, natural base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseBracket.lean`, `LogBaseExact.lean`, `LogBase.lean`, `Equiv/…`, `Tests/LogBase.lean`.
`logBasePrecRound x b p mode` for a 64-bit base `b : UInt64` (`b < 2` gives `NaN`): `ln x / ln b`.
A power-of-two base `b = 2^k` (`AzNat.checkedLogBase2`) delegates to `logBasePow2PrecRound x k`
(spec bridge `Spec.logBase_two_pow`).  Exact branch otherwise: `log_b x` is rational exactly when
`x` is a positive integer `c^r` with `c` the primitive root of `b = c^s` (`s ≤ 63` maximal, found by
`AzNat.isPow` tests downward in `maxPowExp`/`maxRootBase`), and the value `r/s` is rounded once by
`ofAzRatRound` (`logBaseExact?`, `logBaseExact?_some`).  Irrationality for `none`
(`irrational_of_logBaseExact?_none`): a rational `n/d` gives `x^d = b^n`
(`pow_eq_zpow_of_log_div_log`, via `exp`/`log`); for a non-integer float `x = o · 2^j` with `o` odd
and `j < 0`, `o^d · 2^(jd) = b^n` makes `b^n` divisible by an odd `o^d > 1` while also forcing `b`
to be a power of two, contradiction (`odd_pow_eq_two_pow`); for an integer `N`, `N^d = c^(sn)` and
`Nat.exists_eq_pow_of_pow_eq_pow` give `N = y^(sn/g)`, `c = y^(d/g)` with `g = gcd(sn, d)`, and
maximality of `s` (`maxRootBase_not_pow`, using `b < 2^64`) forces `d/g = 1`, so `N` is a power
of `c` after all, contradicting `AzNat.checkedLogBase = none`.  Ziv branch: `logBaseApprox` is
`quotientBracket (lnBracket x) (lnBaseBracket b)`, the `ln x` bracket divided by the `ln b` bracket
with directed rounding (lower end of the divisor clamped at `1/2` by `clampHalf`, so positivity
holds at every working precision); `quotientBracket_spec` generalizes `log2Quotients_spec` to an
arbitrary divisor bracket, width `2ε + 8 (|L| + ε) (δ + 2^-w)`, and `logBaseEps` tends to `0`.
Tests: specials and bases `0`/`1`, exact cases (`log₁₀ 1000 = 3`, `log₃₆ 6 = 1/2`, `log₉ 27 = 3/2`,
`log₂₇ 3 = 1/3` rounded with tag, `log₁₀ 1000` at 1 bit), power-of-two bases against
`logBasePow2PrecRound` (including `2^63`), `log₁₀ 2` and `log₃ (7/4)` at 150 bits against 60-digit
references (`Decimal.ln`), the base `2^64 − 1`.

## `log_b` of a rational for `AzFloat`, natural base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseRat.lean`, `Equiv/LogBaseRat.lean`, `Tests/LogBaseRat.lean`, with the rational
pieces added to `LogBaseBracket.lean`/`LogBaseExact.lean` and their `Equiv/` files.
`logBaseRatPrecRound q b p mode = ln q / ln b` for `q : AzRat`, `b : UInt64 ≥ 2` (`b < 2` and
`q < 0` give `NaN`, `q = 0` gives `−∞`); a power-of-two base delegates to
`logBasePow2RatPrecRound`.  Exact branch: `log_b q` is rational exactly when `q = c^r` for the
primitive root `c` of `b = c^s` and an integer `r` (negative allowed, unlike the float case where
non-integers are never exact for a non-power-of-two base); `logBaseExactRat? q b` reuses
`AzRat.checkedLogBaseAbs` with the base `c` (which fits in 64 bits, `maxRootBase_lt_size`) and
returns `r/s` through `AzRat.ofAzInts`.  Irrationality for `none` (`irrational_log_div_log_of_rat`,
over Mathlib's `ℚ`): a rational `n/d` gives `q^d = b^n`; with `q = N/D` reduced, `n ≥ 0` gives
`N^d = b^n D^d`, so `D^d ∣ N^d` and coprimality (`Nat.Coprime.pow`, `Nat.Coprime.eq_one_of_dvd`)
force `D = 1`, while `n < 0` gives `N^d b^(−n) = D^d` and `N = 1`; the remaining `N^d = b^n`
(resp. `D^d = b^(−n)`) is the integer core `exists_eq_pow_maxRoot_of_pow_eq_pow`, extracted from
the float proof, so the power is `c^k` and `q = c^(±k)`.  No power-of-two restriction on `b` is
needed here.  Ziv branch: `logBaseRatApprox q b w = quotientBracket (lnFloorBracket
(ofAzRatRound q w .Floor).1 w) (lnBaseBracket b w) w`, width `logBaseRatEps` from `lnRatEps` and
`lnEps`.  Tests: specials, exact cases in both directions (`log₁₀ (1/1000) = −3`,
`log₃₆ (1/6) = −1/2`, `log₉ (1/27) = −3/2`, `log₂₇ (1/9) = −2/3` rounded with tag), power-of-two
bases against `logBasePow2RatPrecRound`, floats against `logBasePrecRound`, `log₁₀ 2`,
`log₁₀ (1/3)` and `log₃ (7/4)` at 150 bits against 60-digit references, the base `2^64 − 1`.

## `log_b (1 + x)` for `AzFloat`, natural base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseP1.lean`, `Equiv/LogBaseP1.lean`, `Tests/LogBaseP1.lean`, with the pieces added to
`LogBaseBracket.lean`/`LogBaseExact.lean` and their `Equiv/` files.  `logBaseP1PrecRound x b p
mode = ln (1 + x) / ln b` for `b : UInt64 ≥ 2`, the natural-base analogue of `log2P1`; the finite
case `x > −1` is the proof-carrying `logBaseP1Finite s e hv hgt b hb p mode` (shared by both
signs), started at `p + 64 + leadingZeroBits e` like `lnP1`.  Exact cases: for `b = 2^k`
(`AzNat.checkedLogBase2`) the existing `onePlusPow2Exponent?` detects `1 + x = 2^j` and the value
is `j/k` (`ofAzRatRound (AzRat.ofAzInts j k)`); otherwise `logBaseP1Exact? x b` tests
`isInteger` first (so non-integers cost nothing), converts the positive integer `x` to `N` and
runs `AzNat.checkedLogBase c (N + 1)` for the primitive root `c`, value `r/s`.  Irrationality:
an integer `x > −1` is a positive integer (`toAzRat?_of_nat`, extracted from the float proof) and
`irrational_log_div_log_of_int` applies to `N + 1`; a non-integer `x > −1` has `1 + x = u / 2^t`
with `u` odd and `t ≥ 1` (`one_add_finiteVal_eq_odd_div_two_pow`, from `finiteVal_eq_odd_mul_zpow`
and `Nat.Even.sub_odd` for the negative sign), and `1 + x = c^r` is impossible: `r ≥ 0` makes `u`
even, `r < 0` makes `c^(−r)` divide `2^t`, so `c` and `b` are powers of two
(`irrational_log_div_log_one_add_of_not_int`, through the `ℚ`-level
`irrational_log_div_log_of_rat`); for `b = 2^k`, `irrational_logb_two_one_add_of_none` divided by
`k` (`log_div_log_two_pow`).  Ziv branch: `logBaseP1Approx x b w = quotientBracket (lnFloorBracket
(addPrecRound one x w .Floor).1 w) (lnBaseBracket b w) w`, width `logBaseRatEps` (reused).  Spec
`= liftVal (fun a => Spec.logBase b (a + 1))`, special values as `log2P1`.  Tests: specials,
exact cases (`log₁₀ (1 + 999) = 3`, `log₃₆ (1 + 5) = 1/2`, `log₂₇ (1 + 2) = 1/3` with tag,
`log₁₀ (1 + (10^20 − 1)) = 20`), power-of-two bases (`log₈ (1 − 7/8) = −1`, `log₁₆ (1 + 3) = 1/2`,
`log₁₀₂₄ (1 + (2^100 − 1)) = 10`), agreement with `log2P1PrecRound` and with `logBasePrecRound`
on the exact `1 + x`, `log₁₀ (1 + 2^(−30))` at 100 bits against a 58-digit reference.

## `log_{2^k} (1 + x)` for `AzFloat` (DONE 2026-10-25, fuel-free)

`AzFloat/LogBasePow2P1.lean`, `Equiv/LogBasePow2P1.lean`, `Tests/LogBasePow2P1.lean`, with
`logBasePow2P1Approx` and its spec added to `LogBasePow2Bracket.lean`/`Equiv/`.
`logBasePow2P1PrecRound x k p mode = log₂ (1 + x) / k` for `k : AzInt ≠ 0`, the base-`2^k`
analogue of `log2P1`, with the proof-carrying finite core `logBasePow2P1Finite s e hv hgt k hk p
mode` (`hgt : −1 < x`) started at `p + 64 + leadingZeroBits e`.  Exact branch: the existing
`onePlusPow2Exponent?` detects `1 + x = 2^j` and `ofAzRatRound (AzRat.ofAzInts j k)` rounds
`j/k` once; otherwise `irrational_logb_two_one_add_of_none` divided by `k`
(`Irrational.div_intCast`) certifies the Ziv loop on `logBasePow2P1Approx x k w = divBracketByInt
(log2Quotients (lnFloorBracket (addPrecRound one x w .Floor).1 w) w) k w`, width
`logBasePow2RatEps` (reused: the `lnP1` bracket has the rational width bound `lnRatEps`).  Spec
`= liftVal (fun a => Spec.logBasePow2 k.toInt (a + 1))`; `+∞ ↦ ±∞` and `−1 ↦ ∓∞` by the sign of
`k`, `0 ↦ 0`, `NaN` below `−1`.  Tests: specials with both signs of `k`, exact cases
(`log₈ (1 + 7) = 1`, `log₁₆ (1 + 3) = 1/2`, `log₄ (1 − 1/2) = −1/2`, `log_{1/8} (1 − 7/8) = 1`,
`log₈ (1 + 1) = 1/3` with tag, `log₁₀₂₄ (1 + (2^100 − 1)) = 10`), `k = 1` against
`log2P1PrecRound`, agreement with `logBasePow2PrecRound` on the exact `1 + x` (including
`k = −4`, `k = 1000` and `x = −3/8`), `log₁₆ (1 + 9)` at 150 bits.

## Base-10 logarithms (DONE 2026-10-25)

`AzFloat/Log10.lean`, `Equiv/Log10.lean`, `Tests/Log10.lean`: `log10PrecRound`/`log10`,
`log10RatPrecRound`/`log10Rat` and `log10P1PrecRound`/`log10P1` are the natural-base functions
at the base `10`; `Spec.log10 = Spec.logBase 10` and the three correctness theorems are the
general ones instantiated (`toNat_ten : (10 : UInt64).toNat = 10` by `decide`).  Tests: exact
powers of ten in all three, `log₁₀ 2`, `log₁₀ (1/2)` and `log₁₀ (1 + 2^(−30))` against the
references, and agreement with the base-`10` calls of the general functions.

## `log_b x` for a float base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseFloatBracket.lean`, `LogBaseFloat.lean`, `Equiv/…`, `Tests/LogBaseFloat.lean`,
with the exactness machinery in `LogBaseExact.lean`/`Equiv/`.  `logBaseFloatPrecRound x b p mode`
is Malachite's `log_base_float_base` (user-pasted special cases; without `−0` the zero cases
collapse, and `log_b ∞` for `b = 0` is `NaN` as the more specific rule says).  Spec
`Spec.logBaseFloat a b` is a table of `if`s; the main theorem is `= liftVal₂ Spec.logBaseFloat`
by `cases x`, `cases b`.  **Exactness.** `x = o · 2^i`, `b = s · 2^j` with odd parts from
`trailingZeros`/`>>>` (`oddPart`, `dyadicExp`; `finiteVal_eq_oddPart`).  `log_b x = n/d`
(reduced) gives `x^d = b^n`, which separates (`pow_eq_zpow_sep`, by `odd_mul_two_zpow_inj`: odd
times a power of two is unique) into `o^d = s^n` and `i d = j n` (or `o = s = 1` for `n < 0`).
If `j = 0` then `i = 0` and `b = s` is an odd integer: `o` must be a power of the primitive root
of `s`, found by `maxRootBaseBounded s s.size` (the 64-bit `maxRootBase` is now the bounded
version at `63`; the lemmas take any bound `t` with `b < 2^(t+1)`).  If `j ≠ 0` then `n/d = i/j`,
so `AzRat.ofAzInts i j` is the only candidate: `r.sign` true needs `s = c^e` and `o = c^a` for a
common `c` (`isPow` and equal `rootInt`s), `r.sign` false needs `o = s = 1`; completeness uses
`Rat.num_div_eq_of_coprime`/`den_div_eq_of_coprime` to identify the reduced fraction.
**Bracket.** `ln b` may be negative or tiny, so `lnBaseFloatBracket` clamps the `lnBracket` ends
by the exact-sign bounds `⌊⌊b − 1⌋ / b⌋ ≤ (b − 1)/b ≤ ln b` (`b > 1`) and
`ln b ≤ b − 1 ≤ −⌊1 − b⌋` (`b < 1`), computed with directed rounding; the clamped end is at least
`lnKappa b` (`(b − 1)/(4b)` or `(1 − b)/2`) in absolute value at every `w ≥ 64`, so no threshold
is needed in the Ziv loop.  `divBracketByPosBracket` shifts the divisor bracket by `normShift`
(`2^(−e)` for exponent `e ≤ 0`) to `[1/2, ∞)`, reuses `quotientBracket_spec`, and shifts the
quotient back; width `divEps (1/c) |L| ε δ w = (1 + 1/c)(2ε + 8(|L| + ε)((1 + 1/c)δ + 2^−w))`, and
`logBaseFloatEps` is it with `K = 1/lnKappa b`.  For `b < 1` the negated bracket is divided and
the result negated and swapped.  Tests: the full special-case table, exact cases with power-of-two,
odd-integer and fractional bases (`log₄ 8 = 3/2`, `log₉ 27 = 3/2`, `log_{3/2} (27/8) = 3`,
`log_{1/4} (1/8) = 3/2`), agreement with `logBasePrecRound`/`logBasePow2PrecRound`/`log2PrecRound`,
`log₃ 7` and `log_{3/2} 2` at 150 bits, and the bases `1 ± 2^(−20)` at 100 bits (values
`±726817.…`, 75-digit references).

## `log_b (1 + x)` for a float base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseFloatP1.lean`, `Equiv/LogBaseFloatP1.lean`, `Tests/LogBaseFloatP1.lean`, with
`onePlusDyadic` in `LogBaseExact.lean`/`Equiv/` and `logBaseFloatP1Approx` in
`LogBaseFloatBracket.lean`/`Equiv/`.  `logBaseFloatP1PrecRound x b p mode = ln (1 + x) / ln b`.
The exactness test needs the odd part and dyadic exponent of `1 + x`, computed from those of `x`
without a big rational (`onePlusDyadic s i o`: `x = ±o · 2^i`; for `x ≥ 0`, `i ≥ 0` the integer
`o · 2^i + 1`, else `u = 2^t ± o` with `t = −i` and `1 + x = u / 2^t`; `onePlusDyadic_spec` by
`oddPart_spec`, with `o < 2^t` from `x > −1` for the minus sign), then `logBaseFloatExact?` and
its two lemmas apply verbatim (`1 + x ≠ 1` since `x ≠ 0`).  The bracket machinery was refactored:
`logBaseFloatQuot X b eb w` divides any bracket `X` by the clamped `ln b` bracket (sign dispatch,
negate and swap for `b < 1`), with `logBaseFloatQuot_spec` the former `logBaseFloatApprox_spec`
body; `logBaseFloatApprox` (`lnBracket`) and `logBaseFloatP1Approx` (`lnFloorBracket` of the
floor-rounded `1 + x`) are instances with widths `logBaseFloatEps`/`logBaseFloatP1Eps`.
Special values reuse `logBaseFloatPrecRound` at `∞`, `one` and `zero` for `x = ∞`, `x = 0` and
`x = −1`, so the spec `fun a bv => Spec.logBaseFloat (a + 1) bv` is matched through
`logBaseFloatPrecRound_eq_liftVal₂` with `⊤ + 1 = ⊤`, `0 + 1 = 1`, `−1 + 1 = 0`; the finite
`x > −1` case is `logBaseFloatP1Pos` (dispatch on `b`, `b = 1` gives `infinity s`) and
`logBaseFloatP1Finite` (exact or Ziv at `p + 64 + leadingZeroBits e`).  Tests: the special-value
table at `1 + x`, exact cases (`log₄ (1 + 7) = 3/2`, `log₉ (1 + 26) = 3/2`,
`log_{3/2} (1 + 19/8) = 3`, `log_{3/4} (1 − 7/16) = 2`, `log_{1/4} (1 − 7/8) = 3/2`), agreement
with `logBaseP1PrecRound`, `logBasePow2P1PrecRound` and `logBaseFloatPrecRound` on the exact
`1 + x`, `log₃ (1 + 6)`, `log_{3/2} (1 + 1)`, the base `1 + 2^(−20)` and the tiny argument
`2^(−30)` at base `10` against the existing references.

## `log_b q` for a rational `q` and a float base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseRatFloat.lean`, `Equiv/LogBaseRatFloat.lean`, `Tests/LogBaseRatFloat.lean`, with
`ratDyadicExp`/`logBaseRatFloatExact?` in `LogBaseExact.lean`/`Equiv/` and
`logBaseRatFloatApprox` in `LogBaseFloatBracket.lean`/`Equiv/`.  Malachite's
`log_base_rational_float_base`: `logBaseRatFloatPrecRound q b p mode = ln q / ln b`.  Exactness:
`q = (n/d) · 2^i` with `n`, `d` the odd parts of the reduced numerator and denominator
(`toRat_eq_oddParts`); `q^e = b^a` separates into odd parts and 2-exponents as in the float case,
and the odd-part equation `n^e = s^a d^e` (or `n^e s^(−a) = d^e`) with coprime `n`, `d` forces
`d = 1` (or `n = 1`), so the only rational cases are the float cases on `n · 2^i` and on
`d · 2^(−i)` (negated, `Real.log_inv`); `logBaseRatFloatExact?` dispatches on `d = 1` / `n = 1`
and returns `none` otherwise, with `irrational_of_logBaseRatFloatExact?_none` proving the
`n, d > 1` case directly through `odd_mul_two_zpow_inj` and `Nat.Coprime.eq_one_of_dvd`.  The
bracket `logBaseRatFloatApprox` is `logBaseFloatQuot` of the rational `ln` bracket
(`lnFloorBracket` of `⌊q⌋_w`), width `logBaseFloatP1Eps` (reused), Ziv from `p + 64`.  Special
values: `q = 0` and `q = 1` delegate to `logBaseFloatPrecRound` at `zero` and `one`
(`toRat_eq_one_iff : toRat q = 1 ↔ q.num = 1 ∧ q.den = 1`), `q < 0` is `NaN`, `b = 1` gives
`±∞` by `q.den < q.num` (`one_lt_toRat_iff`).  Tests: specials, exact cases including odd
denominators (`log₉ (1/27) = −3/2`, `log_{3/2} (4/9) = −2`, `log_{9/4} (2/3) = −1/2`,
`log₃ (1/243) = −5`) and never-exact `n, d > 1` cases, agreement with the natural,
power-of-two and float-argument versions, `log₃ 7`, `log₃ (1/7)`, `log_{3/2} 2`, `log₁₀ (1/3)`
and the base `1 + 2^(−20)` at 100–150 bits.

## `log_b x` for a rational base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseRatBase.lean`, `Equiv/LogBaseRatBase.lean`, `Tests/LogBaseRatBase.lean`, with
`logBaseRatBaseExact?` in `LogBaseExact.lean`/`Equiv/` and the bracket pieces in
`LogBaseFloatBracket.lean`/`Equiv/`.  Malachite's `log_base_rational_base`:
`logBaseRatBasePrecRound x b p mode = ln x / ln b`.  Exactness mirrors the rational-argument
case with the roles swapped: `b = (n/d) · 2^j`, and `x^e = b^a` separates into `o^e d^a = n^a`
(`a ≥ 0`) or `o^e n^(−a) = d^(−a)` (`a < 0`), so coprime `n, d > 1` leave only `a = 0`, i.e.
`x = 1` (excluded); the rational cases are the float cases on the bases `n · 2^j` (`d = 1`) and
`d · 2^(−j)` negated (`n = 1`).  **Bracket.** The quotient's sign dispatch was factored into
`logBaseQuotCore`/`logBaseQuotWith X B pos w` with the generic specs
`logBaseQuotCore_spec`/`logBaseQuotWith_spec` (a bracket `(c, d)` of `M` with `κ ≤ c` when
`pos`, `d ≤ −κ` otherwise); `logBaseFloatQuot` is the instance with `lnBaseFloatBracket` and
`decide (eb ≥ 1)`.  For a rational base, `lnRatBaseBracket b w` clamps the rational `ln`
bracket (`lnFloorBracket` of `⌊b⌋_w`) by `⌊⌊b − 1⌋_w / ⌈b⌉_w⌋_w ≤ (b − 1)/b ≤ ln b` for `b > 1`
(`b.den < b.num`) and `ln b ≤ b − 1 ≤ −⌊1 − b⌋_w` for `b < 1`, all rational roundings by
`ofAzRatRound`; the clamped end is at least `lnRatKappa b` (`(b − 1)/(6b)`, from
`⌈b⌉ ≤ 3b/2` and the floor errors, or `(1 − b)/2`).  `logBaseRatBaseApprox` divides the `ln x`
bracket by it, width `logBaseRatBaseEps ex Eb K A Ab w = divEps K A (lnEps ex w) (lnRatEps Eb Ab
w) w`.  Special values: `b = 0`/`b = 1` delegate to `logBaseFloatPrecRound x zero/one`, `b < 0`
is `NaN`, `x = ∞`/`x = 0` give `±∞` by `b.den < b.num` (`one_lt_toRat_iff`, with
`Spec.logBaseFloat_top_left`/`zero_left` and `b ≠ 1`), `x = 1` gives `0`.  Tests: specials with
the bases `0`, `1`, `2`, `2/3`; exact cases with odd denominators (`log_{1/3} 27 = −3`,
`log_{2/3} (9/4) = −2`, `log_{4/9} (3/2) = −1/2`, `log_{1/10} 1000 = −3`) and never-exact
`n, d > 1` bases; agreement with the natural, power-of-two and float-base versions; `log₃ 7`,
`log_{1/3} 7`, `log_{3/2} 2`, `log_{2/3} 2` at 150 bits and the base `1 + 2^(−20)` at 100 bits.

## `log_b (1 + x)` for a rational base (DONE 2026-10-25, fuel-free)

`AzFloat/LogBaseRatBaseP1.lean`, `Equiv/LogBaseRatBaseP1.lean`, `Tests/LogBaseRatBaseP1.lean`,
with the exactness forms in `Equiv/LogBaseExact` and `logBaseRatBaseP1Approx` in
`LogBaseFloatBracket`/`Equiv/`.  Pure recombination: `onePlusDyadic` (from the float-base P1
arc) gives the odd part and dyadic exponent of `1 + x`, `logBaseRatBaseExact?` decides
exactness, and the Ziv branch divides the `lnP1` bracket by `lnRatBaseBracket` through
`logBaseQuotWith` (width `logBaseRatBaseP1Eps E Eb K A Ab w = divEps K A (lnRatEps E A w)
(lnRatEps Eb Ab w) w`), started at `p + 64 + leadingZeroBits e`.  Special values: `b = 0`/`b = 1`
delegate to `logBaseFloatP1PrecRound x zero/one`; for `b > 0`, `b ≠ 1`: `x = ∞` gives `±∞`
and `x = −1` gives `∓∞` by `b.den < b.num`, `x = 0` gives `0`, below `−1` is `NaN`.  Spec
`= roundVal p mode (x.toVal.bind fun a => Spec.logBaseFloat (a + 1) (toRat b))`.  Tests:
specials, exact cases with odd-denominator bases (`log_{1/3} (1 + 26) = −3`,
`log_{2/3} (1 + 19/8) = −3`, `log_{4/9} (1 + 1/2) = −1/2`), agreement with the natural,
power-of-two and float-base `log_b (1 + x)` and with `logBaseRatBasePrecRound` on the exact
`1 + x`, `log₃ (1 + 6)`, `log_{3/2} (1 + 1)`, `log_{2/3} (1 + 1)`, the base `1 + 2^(−20)` and
the tiny argument `2^(−30)` at the bases `10` and `1/10`.
