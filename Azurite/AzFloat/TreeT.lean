/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertW

/-!
## The tree function `T`

`T(x) = −W₀(−x)` (DLMF §4.13: the solution of `T e^(−T) = x`, principal branch; `treeT` in
`DLMF/Chapter4/Section13Real.lean`), defined for `x ≤ e⁻¹`, increasing, with `T(x) ≤ 1`,
`T(0) = 0` and `T(x) → −∞` as `x → −∞`.

`treeTPrecRound x p mode` is `T(x)` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value: `W₀` of `−x` rounded in the opposite mode, negated, the
comparison swapped — so everything about `W₀` carries over (no fuel, the tiny-argument path,
the certified decision at the branch point: a float or rational is never `e⁻¹`).  `NaN` above
`e⁻¹` (and at `+∞`), `T(−∞) = −∞`, `T(0) = 0`.  `treeTFloat x` rounds to nearest at the
precision of `x`.  `treeTRatPrecRound q p mode` and `treeTRat q p` take an `AzRat`.

The specifications `treeTPrecRound_eq`, `treeTRatPrecRound_eq` are in `Equiv/TreeT.lean`.
-/

namespace Azurite.AzFloat

/-- `T(x) = −W₀(−x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` unless the value is `0` or `−∞`). -/
def treeTPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertW0PrecRound (-x) p (-mode)
  (-r.1, r.2.swap)

/-- `T(q) = −W₀(−q)` for an `AzRat`, rounded to precision `p` with `mode`, and the comparison
with the exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def treeTRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lambertW0RatPrecRound (-q) p (-mode)
  (-r.1, r.2.swap)

/-- `T(x)` rounded to nearest at the precision of `x`. -/
def treeTFloat (x : AzFloat) : AzFloat :=
  (treeTPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `T(q)` for an `AzRat`, rounded to nearest at precision `p`. -/
def treeTRat (q : AzRat) (p : Nat) : AzFloat := (treeTRatPrecRound q p .Nearest).1

end Azurite.AzFloat
