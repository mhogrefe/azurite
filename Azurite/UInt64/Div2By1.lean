/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.WideAdd
import Azurite.UInt64.WideMul

namespace UInt64

/-!
Formalization of Algorithm 4 (DIV2BY1) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund.
-/

/-- Algorithm 4 (DIV2BY1) of Möller–Granlund: given a normalized 64-bit divisor
`d` (i.e. `2^63 ≤ d < 2^64`), a 128-bit dividend `(hi, lo)` with `hi < d`, and the
precomputed reciprocal `inv = reciprocal d`, return the pair `(q, r)` where `q` is
the 64-bit quotient `⌊(hi · 2^64 + lo) / d⌋` and `r` is the 64-bit remainder. -/
@[inline]
def div2By1 (hi lo d inv : UInt64) : UInt64 × UInt64 :=
  let (q_hi, q_lo) := wideAdd (wideMul inv hi) (hi, lo)
  let q_hi := q_hi + 1
  let r := lo - q_hi * d
  let (q_hi, r) : UInt64 × UInt64 :=
    if r > q_lo then (q_hi - 1, r + d) else (q_hi, r)
  if r ≥ d then (q_hi + 1, r - d) else (q_hi, r)

end UInt64
