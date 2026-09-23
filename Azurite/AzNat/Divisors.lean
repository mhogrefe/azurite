/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Divisor enumeration by trial division to the square root.

  `divisors n` lists every positive divisor of `n` (in no particular
  order): the loop walks `d = 1, 2, …` while `d² ≤ n`, emitting both `d`
  and the complementary divisor `n / d` whenever `d ∣ n`.  Every divisor
  `k` of `n` satisfies `min(k, n/k)² ≤ n`, so each is reached either
  directly or as a complement (`divisors_complete`, in
  `Azurite/AzNat/Equiv/Divisors.lean`).  `divisors 0 = []`.

  The loop is fueled by `√n + 1` **as a unary recursion**, so this is for
  MODERATE `n` (the intended use: rational-root candidates from the
  trailing and leading coefficients of integer polynomials, per the
  rational root theorem) — trial division would be the runtime bottleneck
  long before the fuel is.
-/
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Div
import Azurite.AzNat.Mul
import Azurite.AzNat.Add
import Azurite.AzNat.Compare

namespace Azurite

namespace AzNat

/-- The trial-division loop: emit `d` and `n / d` for each divisor
`d ≥ start` with `d² ≤ n`. -/
def divisorsAux (n : AzNat) : ℕ → AzNat → List AzNat
  | 0, _ => []
  | fuel + 1, d =>
    if compare (d * d) n == .gt then []
    else if n % d = 0 then
      d :: n / d :: divisorsAux n fuel (d + 1)
    else divisorsAux n fuel (d + 1)

/-- **All positive divisors of `n`** (each at least once; `d` and `n / d`
coincide at `d = √n`, so perfect squares list their root twice), by trial
division to `√n`.  `divisors 0 = []`. -/
def divisors (n : AzNat) : List AzNat :=
  divisorsAux n (n.sqrt.toNat + 1) 1

end AzNat

end Azurite
