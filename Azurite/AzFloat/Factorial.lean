/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma

/-!
## The factorial as a float

`factorialPrecRound n p mode` is `n!` for an `AzNat` `n`, rounded to precision `p` in `mode`,
with the comparison against the exact value; `factorial n p` rounds to nearest.

* **`n ≤ gammaIntBound p = 8p + 2048`**: the exact `AzNat.factorial`, rounded once — the
  fastest way there, and the comparison is `.eq` whenever the factorial fits the precision.
* **Beyond**: `Γ(n + 1)` by `gammaPrecRound` at the exact float `n + 1` (Stirling's series,
  at a cost that does not grow with `n` but for the bits of its size).  There the odd part of
  `n!` has more than `p + 1` bits, so the value is no rounding boundary.
* **Contract** (`Equiv/Factorial.lean`): `factorialPrecRound_eq_or` — the correct rounding of
  `n!`, or `(nan, .eq)` when the fuel of the `Γ` loop runs out.
-/

namespace Azurite.AzFloat

/-- `n!` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`, or if the fuel runs out). -/
def factorialPrecRound (n : AzNat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if n ≤ AzNat.ofNat (gammaIntBound p) then
    setPrecRound (ofAzNat (AzNat.factorial n.toNat)) p mode
  else gammaPrecRound (ofAzNat (n + 1)) p mode

/-- `n!` rounded to nearest at precision `p`. -/
def factorial (n : AzNat) (p : Nat) : AzFloat := (factorialPrecRound n p .Nearest).1

end Azurite.AzFloat
