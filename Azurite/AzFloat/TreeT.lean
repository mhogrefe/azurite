/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertW

/-!
## The tree function `T`

`T(x) = −W(−x)` (DLMF §4.13: a solution of `T e^(−T) = x`), with the two real branches named
after those of `W` (`treeTk` in `DLMF/Chapter4/Section13Branch.lean`):

* `T₀(x) = −W₀(−x)` for `x ≤ e⁻¹` (`treeT` in `DLMF/Chapter4/Section13Real.lean`): increasing,
  `T₀(x) ≤ 1`, `T₀(0) = 0`, `T₀(x) → −∞` as `x → −∞`;
* `T₋₁(x) = −W₋₁(−x)` for `0 < x ≤ e⁻¹`: decreasing, `T₋₁(x) ≥ 1`, `T₋₁(x) → +∞` as
  `x → 0⁺`.

`treeT0PrecRound x p mode` and `treeTm1PrecRound x p mode` are the values correctly rounded to
precision `p` in `mode`, with the comparison against the exact value: `W₀` or `W₋₁` of `−x`
rounded in the opposite mode, negated, the comparison swapped — so everything about `W`
carries over (no fuel, the tiny-argument path of `W₀`, the certified decision at the branch
point: a float or rational is never `e⁻¹`).  `T₀`: `NaN` above `e⁻¹` (and at `+∞`),
`T₀(−∞) = −∞`, `T₀(0) = 0`.  `T₋₁`: `NaN` outside `[0, e⁻¹]` (and at `±∞`), `T₋₁(0) = +∞` (the
limit from the right).  `treeT0Float x`, `treeTm1Float x` round to nearest at the precision of
`x`; `treeT0RatPrecRound`, `treeTm1RatPrecRound`, `treeT0Rat`, `treeTm1Rat` take an `AzRat`.

The specifications `treeT0PrecRound_eq`, `treeTm1PrecRound_eq`, `treeT0RatPrecRound_eq`,
`treeTm1RatPrecRound_eq` are in `Equiv/TreeT.lean`.
-/

namespace Azurite.AzFloat

/-- `T₀(x) = −W₀(−x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` unless the value is `0` or `−∞`). -/
def treeT0PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertW0PrecRound (-x) p (-mode)
  (-r.1, r.2.swap)

/-- `T₀(q) = −W₀(−q)` for an `AzRat`, rounded to precision `p` with `mode`, and the comparison
with the exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def treeT0RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertW0RatPrecRound (-q) p (-mode)
  (-r.1, r.2.swap)

/-- `T₀(x)` rounded to nearest at the precision of `x`. -/
def treeT0Float (x : AzFloat) : AzFloat :=
  (treeT0PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `T₀(q)` for an `AzRat`, rounded to nearest at precision `p`. -/
def treeT0Rat (q : AzRat) (p : Nat) : AzFloat := (treeT0RatPrecRound q p .Nearest).1

/-- `T₋₁(x) = −W₋₁(−x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` unless the value is `+∞`). -/
def treeTm1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertWm1PrecRound (-x) p (-mode)
  (-r.1, r.2.swap)

/-- `T₋₁(q) = −W₋₁(−q)` for an `AzRat`, rounded to precision `p` with `mode`, and the
comparison with the exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def treeTm1RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertWm1RatPrecRound (-q) p (-mode)
  (-r.1, r.2.swap)

/-- `T₋₁(x)` rounded to nearest at the precision of `x`. -/
def treeTm1Float (x : AzFloat) : AzFloat :=
  (treeTm1PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `T₋₁(q)` for an `AzRat`, rounded to nearest at precision `p`. -/
def treeTm1Rat (q : AzRat) (p : Nat) : AzFloat := (treeTm1RatPrecRound q p .Nearest).1

end Azurite.AzFloat
