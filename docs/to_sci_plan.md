# Plan: scientific-notation output for `AzRat` (`toSci`)

Status: implemented and proven through milestone 5 (2026-10-01); see the status log at the end. Port of the author's own `Rational::to_sci` from Malachite
(`malachite-q/src/rational/conversion/string/to_sci.rs` and the `ToSciOptions` /
`SciSizeOptions` types in `malachite-base`). That code was written entirely by the author,
so it may be used here under Apache-2.0; `docs/bibliography.md` records the provenance rule,
and the sentence there about Malachite material is to be extended to name `to_sci` when
the port lands.

## Behaviour to reproduce

`to_sci` renders a rational in base `b ∈ [2, 36]`, rounded to a chosen size, in either plain
or exponent notation:

| Option | Default | Meaning |
|---|---|---|
| `base` | 10 | digit base, `2 ≤ b ≤ 36` |
| `roundingMode` | `Nearest` | how the value is rounded to the chosen size (`Exact` is a *validity* request, see below) |
| `sizeOptions` | `Precision 16` | `Complete` (all digits; only for terminating expansions), `Precision p` (`p ≥ 1` significant digits), `Scale s` (`s` digits after the point) |
| `negExpThreshold` | `-6` | exponent notation is used when the base-`b` exponent is `≤` this (or when the point would fall left of all digits) |
| `lowercase`, `eLowercase` | `true`, `true` | digit letters and the exponent marker |
| `forceExponentPlusSign` | `false` | write `e+8`; also forced for `b ≥ 15` where `e` is a digit |
| `includeTrailingZeros` | `false` | keep zeros after the point (always kept for `Complete`) |

Malachite's `RoundingMode` has an `Exact` variant; Azurite's `RoundingMode` does not
(`Floor, Ceiling, Down, Up, Nearest`). We therefore keep `Exact` out of the mode and treat it
as a *validity predicate*: `toSciValid` is `true` iff the value needs no rounding at the chosen
size (and, for `Complete`, iff its expansion terminates). The user-facing `toSci` returns an
`Option`, `none` exactly when `toSciValid` is `false`.

Algorithm (Malachite `fmt_sci`), for `q ≠ 0`:

1. `log := ⌊log_b |q|⌋`.
2. From the size option: `Complete` → `scale := lengthAfterPoint b q`, `precision := scale + log + 1`;
   `Scale s` → `scale := s`, `precision := s + log + 1`; `Precision p` → `scale := p − 1 − log`,
   `precision := p`.  (`precision ≤ 0` can happen with `Scale`: the value rounds to `0` or to one
   unit at that scale.)
3. `n := |round(q · b^scale, mode)|` as an integer.  If `precision ≤ 0`: `n = 0` → print zero;
   `n = 1` → `precision := 1`, `log := −scale`.
4. Digits of `n` in base `b`.  If there are `precision + 1` digits, the value rounded up to a
   power of the base: `log += 1`; with `Precision` drop the trailing `0` and `scale −= 1`; with
   `Scale` accept `precision + 1` digits.
5. If `log ≤ negExpThreshold` or `scale < 0`: exponent form `d.ddd e±log` (trailing zeros
   trimmed unless `includeTrailingZeros`); else if `scale = 0`: the digits; else plain form
   with the point after `log + 1` digits (leading `0.000…` when `log < 0`), trailing zeros
   among the last `scale` digits trimmed unless `includeTrailingZeros`.

## Architecture: two stages and a proven middle

```
AzRat ──toSciNumber opts──▶ SciNumber ──render fmt──▶ String
                 │                                ▲
                 └── proven: value = round_S(mode, q) ┘ (digits only; no arithmetic)
```

* **Stage 1, numeric (`Azurite/AzRat/ToSci.lean`)**: `AzRat.toSciNumber (q : AzRat)
  (opts : SciOptions) : Option SciNumber`. All arithmetic lives here: the logarithm, the scale,
  the rounding of `q · b^scale` to an integer (`AzRat.round` on `q * b^scale`), the
  power-of-base adjustment. `none` iff `¬ toSciValid`.
* **`SciNumber` (`Azurite/Sci/Number.lean`)**: the exact rounded value in positional form:
  ```
  structure SciNumber where
    negative  : Bool
    base      : UInt64                -- 2 ≤ base ≤ 36
    digits    : Array UInt64          -- most significant first, each < base, no leading zero
                                      -- (empty array = zero)
    exponent  : ℤ                     -- value = ± 0.d₁d₂…dₖ × base^(exponent+1), i.e. the
                                      -- leading digit has weight base^exponent
    scale     : ℤ                     -- digits after the point in plain notation (= k − 1 − exponent)
  ```
  with `SciNumber.value : SciNumber → ℚ` (`± Σ dᵢ · b^(exponent − i)`), the specification the
  proofs talk about. Zero is `digits = #[]` (its string form depends only on the format options).
* **Stage 2, textual (`Azurite/Sci/Number.lean`)**: `SciNumber.toChars (x : SciNumber)
  (fmt : SciFormat) : List Char` and `toString`, following `AzRat.toChars`'s style: choose
  exponent vs plain form from `exponent`, `scale` and `negExpThreshold`, trim trailing zeros,
  place the point, write the exponent. No arithmetic beyond digit-to-character.
* **Glue**: `AzRat.toSci q opts := (q.toSciNumber opts).map (·.toString opts.format)`,
  `AzRat.toSciValid q opts : Bool`, and `toSci_isSome : (q.toSci opts).isSome ↔ toSciValid q opts`.

Options (`Azurite/Sci/Options.lean`), shared by any future `AzNat`/`AzInt` `toSci`:
```
inductive SciSizeOptions | complete | precision (p : ℕ) | scale (s : ℕ)      -- p ≥ 1 enforced by the smart constructor
structure SciFormat where negExpThreshold : ℤ := -6; lowercase := true; eLowercase := true;
                          forceExponentPlusSign := false; includeTrailingZeros := false
structure SciOptions where base : UInt64 := 10; mode : RoundingMode := .Nearest;
                           size : SciSizeOptions := .precision 16; format : SciFormat := {}
```
with `SciOptions.valid : 2 ≤ base ∧ base ≤ 36 ∧ negExpThreshold < 0 ∧ (size = precision p → p ≥ 1)`
(Malachite asserts these in setters; we carry them as a `Prop` field or a `Bool` check).

## The rounding targets (the proof's statement)

For the size options that round, the set of representable values is a `RoundingTarget`
(`Azurite/Rounding/Sci.lean`), so the correctness theorem is a statement about
`RoundingTarget.round`:

* `Scale s` in base `b`: `scaleSet b s := { m · b^(−s) : m ∈ ℤ }` in `EReal`. A scaled copy of
  `intSet`; its `RoundingTarget` instance is `intSet`'s transported by the order isomorphism
  `x ↦ x · b^s` (or proven directly, mirroring `Rounding/Int.lean`). Tiebreak: even `m`.
* `Precision p` in base `b`: `precisionSet b p := {0} ∪ { m · b^e : m ∈ ℤ, 0 < |m| < b^p, e ∈ ℤ }`,
  the numbers with at most `p` significant base-`b` digits. Order-closedness: for `x > 0` the
  elements `≤ x` have a maximum because above any positive threshold the set is locally a scaled
  integer lattice (scale `b^(⌊log_b x⌋ − p + 1)`), and `0` handles `x = 0` with the negatives by
  symmetry (`Rounding/Symmetric.lean`). Tiebreak: of the two neighbours, the one whose integer
  coordinate at the common finer scale is even (this is what rounding the scaled integer half-to-
  even does, including at the `b^p`-boundary where the upper neighbour renormalises to `m = 1`).
* `Complete`: the representable set would be the base-`b`-adic rationals, which is dense and not
  a `RoundingTarget` (compare `Rounding/Rat.lean`). No rounding happens; the theorem is exactness.

Theorems (`Azurite/AzRat/Equiv/ToSci.lean`), with `v := (toRat q : ℝ)`:

1. `toSciNumber_value_scale`: `opts.size = .scale s` → `toSciNumber q opts = some x` and
   `(x.value : EReal) = (RoundingTarget.round (scaleSet b s) opts.mode v).val`.
2. `toSciNumber_value_precision`: `opts.size = .precision p` → `some x` and
   `(x.value : EReal) = (RoundingTarget.round (precisionSet b p) opts.mode v).val`.
3. `toSciNumber_value_complete`: `opts.size = .complete` → `toSciNumber q opts = some x ↔
   lengthAfterPoint b q ≠ none`, and then `x.value = toRat q`.
4. `toSciNumber_wellFormed`: `digits` all `< base`, no leading zero, `scale = k − 1 − exponent`,
   and (for `Precision p`) `digits.size ≤ p`; (for `Scale s`) `scale = s` — the invariants stage 2
   relies on.
5. `toSciValid_iff`: `toSciValid q opts = true ↔ (opts.size = .complete → terminating) ∧
   (rounding at the chosen target is the identity on `v`)`; and `toSci_isSome`.
6. Later, optional: a round-trip through a `fromSci` parser (Malachite has `from_sci_string`;
   not in scope now).

The sign is handled as Malachite does: the *signed* value is rounded with the given mode
(`Floor` of `−22/7` at precision 3 is `−3.15`), then rendered as sign plus magnitude. Both
targets are symmetric sets, so the existing `round_neg` machinery applies.

## Supporting algorithms

### `lengthAfterPoint b q : Option ℕ` (`Azurite/AzRat/LengthAfterPoint.lean`)

How many base-`b` digits after the point the expansion of `q` has, `none` if it does not
terminate. Malachite: with `den` the (reduced) denominator, for each prime power `p^m ∥ b`
(a 35-entry table for `b ∈ [2, 36]`) count `v_p(den)` — the `2`-part via `AzNat.trailingZeros`,
odd primes by repeated `divModUInt64` until the remainder is nonzero — and take
`max ⌈v_p(den) / m⌉`; `some` iff what remains of `den` is `1`. Spec and proof:
`lengthAfterPoint b q = some L ↔ L` is the least `ℓ` with `den ∣ b^ℓ` (equivalently `q · b^ℓ ∈ ℤ`),
and `= none ↔ ∀ ℓ, ¬ den ∣ b^ℓ`. The proof goes through `Nat.factorization`
(`Nat.factorization_le_iff_dvd`), with the table verified by `decide`.

### `floorLogBaseAbs b q : ℤ` (`Azurite/AzRat/LogBase.lean`)

`⌊log_b |q|⌋` for `q ≠ 0`. Malachite estimates with `f64` logarithms and corrects by one
step; we must not. Design: when `b = 2^k`, reuse `floorLogBase2Abs` / `ceilingLogBase2Abs`
(Malachite's power-of-two branch, exact). Otherwise bracket: `ℓ₂ := floorLogBase2Abs q` gives
`e ∈ [⌊ℓ₂ / ⌈log₂ b⌉⌋ − 1, ⌊ℓ₂ / ⌊log₂ b⌋⌋ + 1]` (integers, from `⌊log₂ b⌋ ≤ log₂ b ≤ ⌈log₂ b⌉`),
then binary-search `e` in that bracket by comparing `b^e` with `|q|` (`AzRat.cmp` against
`(ofAzNat b).zpow e`, or cross-multiplication `num · b^(−e)` vs `den` to stay in `AzNat`). The
invariant `b^lo ≤ |q| < b^hi` is purely algebraic, so the proof needs no bounds on real
logarithms beyond `b^e ≤ x < b^(e+1) ↔ ⌊log_b x⌋ = e`. The bracket is `O(log ℓ₂)` wide only
through the crude bounds, so the search costs a handful of power comparisons; a tighter
rational estimate of `1/log₂ b` can be added later as a pure optimisation without touching
the proof. Spec: `floorLogBaseAbs_eq : q.num ≠ 0 → floorLogBaseAbs b q = ⌊Real.logb b |toRat q|⌋`
(mirroring `floorLogBase2Abs_eq`).

### Rounding to the scale

`q · b^scale` with `scale : ℤ`: multiply `num` or `den` by `b^|scale|` (`AzNat.pow` on the
single-limb base) and reduce through `ofAzNats`, then `AzRat.round · mode` gives the integer
and the `Ordering` tag. The tag is what `toSciValid` uses for the exactness check
(`.eq` ↔ no rounding happened), avoiding a second computation.

## Milestones

1. **Types and the textual stage.** `Sci/Options.lean`, `Sci/Number.lean` with `value`,
   `toChars`/`toString`. `#guard` tests for the renderer on hand-built `SciNumber`s.
2. **`lengthAfterPoint`** + proof (`Equiv/LengthAfterPoint.lean`).
3. **`floorLogBaseAbs`** + proof (`Equiv/LogBase.lean`).
4. **`toSciNumber`, `toSciValid`, `toSci`** with the `Scale` theorem first (simplest target:
   `scaleSet` is `intSet` rescaled), then `Precision` (new `RoundingTarget` instance in
   `Rounding/Sci.lean`), then `Complete`; `toSciValid_iff`, `toSci_isSome`, `wellFormed`.
5. **Tests**: port the author's Malachite test vectors
   (`malachite-q/tests/rational/conversion/string/to_sci.rs`, ~1000 lines of expected strings,
   including the `2^±1000000` cases and all option combinations) to
   `Azurite/AzRat/Tests/ToSci.lean` as `#guard`s on `toSci`.
6. **Housekeeping**: `Azurite.lean` imports, `docs/module_map.md`, blueprint chapter section
   (`azrat/to_sci.tex`), bibliography provenance sentence, memory.

## Decisions taken in this plan (say so if you want them changed)

* `Exact` is not a `RoundingMode`; it is `toSciValid`, and `toSci` returns `Option String`.
* Zero's representation is an empty digit array; its rendering depends only on the format.
* The targets are stated in `EReal` like the existing `intSet`, so `RoundingTarget.round`
  and `round_neg` apply unchanged.
* Nearest ties resolve to the even integer coordinate, as `AzInt.divRound`'s `Nearest` does;
  the proof relies on that being the `intSet` tiebreak already proven for `AzRat.round`.

## Status log

* **2026-10-01 — Milestones 1–5 done.**  `Sci/Options.lean`, `Sci/Number.lean` (with
  `value`, `toChars`, `toString`), `AzRat/LengthAfterPoint.lean`, `AzRat/LogBase.lean`,
  `AzRat/ToSci.lean` (`toSciNumber`, `toSciExact`, `toSci`, `toSciString`), the targets
  `Rounding/Sci.lean` (`scaleSet`) and `Rounding/SciPrecision.lean` (`precisionSet`), and the
  proofs `Equiv/LengthAfterPoint.lean`, `Equiv/LogBase.lean`, `Equiv/ToSci.lean`
  (`toInt_scaledRound`, `snd_scaledRound`, `toSciNumber_value_scale`,
  `toSciNumber_value_precision`, `toSciNumber_complete`).  Design changes against the plan:
  the scaled rounding is one signed division (`num · b^s / den` or `num / (den · b^(−s))`),
  not a product of reduced rationals — the gcd of million-bit operands made the latter
  unusable; the sign of a nonzero result is the rounded integer's sign (so no lemma about
  rounding preserving sign is needed), and a negative value that rounds to zero prints `-0`
  like Malachite; `SciNumber` stores `scale` and derives `exponent = digits.size − 1 − scale`
  (the two are redundant after the power-of-base adjustment, so no invariant is carried).
  Tests: `AzRat/Tests/ToSci.lean` ports the author's Malachite vectors (default options, every
  option, rounding modes, negatives, bases 2–36, complete expansions, the exponent threshold,
  the bankers' tie in base 3); the `2^±1000000` cases are run at `2^±100000` (a 12-minute
  interpreter run otherwise), with expected strings from an exact independent computation that
  reproduces Malachite's `2^±1000000` strings.  Not done: `toSciExact_iff` (exactness ↔ the
  value equals `toRat q`), the well-formedness lemma (digits below the base, no leading zero),
  the blueprint section, and a `fromSci` parser.
