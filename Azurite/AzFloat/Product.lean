/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.SumProduct
import Azurite.AzInt.SumProduct

/-!
## Correctly rounded products

`productPrecRound xs p mode` is the exact product of the floats `xs`, rounded once to precision
`p` with `mode`, with the comparison of the result against the exact product — the
specification is the fold of the two-operand `Spec.mul` (so any `NaN`, or a zero together with
an infinity, give `NaN`; an infinity otherwise gives the infinity whose sign is the product of
the signs; a zero otherwise gives zero).

Unlike a sum, a product of finite floats is cheap to form exactly: the value of a finite float
is `±c · 2^w` with `c` its `p`-bit core significand, so the product is `±(∏ c) · 2^(Σ w)` — a
balanced product tree of the cores (`AzNat.product`), a sum of the scales, and one rounding
with `roundScaled`.  The exact product has `Σ p_i` bits, so the cost is that of the product
tree, `O(M(Σ p_i) log n)`; a correctly rounded result cannot be cheaper in general, since the
rounding may depend on the last bit.  The sign is the parity of the number of negative factors.

Correctness: `Equiv/Product.lean` (`productPrecRound_eq`).
-/

namespace Azurite.AzFloat

/-- The sign, core significand and scale of a finite nonzero float, whose value is
`±core · 2^scale`; `none` for `NaN`, the infinities and zero. -/
def coreParts : AzFloat → Option (Bool × AzNat × AzInt)
  | finite s e p m _ => some (s, coreSignificand p m, e - (AzNat.ofNat p).toAzInt)
  | _ => none

/-- The sign of a product: `true` (positive) when an even number of the floats is negative. -/
def productSign (xs : List AzFloat) : Bool := decide (xs.countP isNegative % 2 = 0)

/-- **The product** of a list of floats rounded to precision `p` with `mode`, and the comparison
of the result with the exact product.  `NaN` for a `NaN` factor or a zero together with an
infinity; otherwise an infinity with the sign of the product, or zero, or the rounding of the
exact finite product.  The empty product is `1`. -/
def productPrecRound (xs : List AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if xs.any isNaN then (nan, .eq)
  else
    let hasZero := xs.any isZero
    let hasInf := xs.any isInfinite
    if hasZero && hasInf then (nan, .eq)
    else if hasInf then (infinity (productSign xs), .eq)
    else if hasZero then (zero, .eq)
    else
      let parts := xs.filterMap coreParts
      roundScaled (productSign xs) (AzNat.product (parts.map fun t => t.2.1))
        (AzInt.sum (parts.map fun t => t.2.2)) p mode

end Azurite.AzFloat
