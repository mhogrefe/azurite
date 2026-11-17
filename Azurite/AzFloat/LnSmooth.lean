/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2Bracket

/-!
## The logarithm of an integer with no prime factor above `7`

The four numbers `251`, `449`, `4801`, `8749` have `(x + 1)/(x − 1)` built from the primes
`2, 3, 5, 7` only,

  `252/250 = 2·3²·7/5³`,  `450/448 = 3²·5²/(2⁵·7)`,  `4802/4800 = 7⁴/(2⁵·3·5²)`,
  `8750/8748 = 5⁴·7/(2·3⁷)`,

and the matrix of exponents has determinant `±1`.  With `A_x = atanh (1/x) =
½ ln ((x + 1)/(x − 1))`:

  `ln 2 = 2 (72 A₂₅₁ + 27 A₄₄₉ − 19 A₄₈₀₁ + 31 A₈₇₄₉)`,
  `ln 3 = 2 (114 A₂₅₁ + 43 A₄₄₉ − 30 A₄₈₀₁ + 49 A₈₇₄₉)`,
  `ln 5 = 2 (167 A₂₅₁ + 63 A₄₄₉ − 44 A₄₈₀₁ + 72 A₈₇₄₉)`,
  `ln 7 = 2 (202 A₂₅₁ + 76 A₄₄₉ − 53 A₄₈₀₁ + 87 A₈₇₄₉)`.

So `ln (2^a 3^b 5^c 7^d)` is an integer combination of four fast series (`16` to `26` bits per
term), whatever the exponents: `lnSmoothBracket a b c d k`.  The series are summed exactly by
binary splitting (`AzNat.atanhNumDen`) and bracketed by `seriesBracket` at
`k + ⌊lg (K₁ + K₂ + K₃ + K₄)⌋ + 8` bits, where the `K` are the coefficients; the combination uses
directed rounding.  The cost is about that of `ln2Bracket`, a fifth of the general logarithm at
`20000` bits.

`smoothExps n` divides the primes out of `n`; `nextSmooth n` is the least such integer from
`n` on (never far: the smooth integers near `10^4` are about `1 %` apart).

The proofs are in `Azurite/AzFloat/Equiv/LnSmooth.lean`.
-/

namespace Azurite.AzFloat

/-- Terms of `atanh (1/q)` for a tail below `2^(−k−5)`, with `b = ⌊lg q⌋ ≥ 1`:
`(2N + 1) b ≥ k + 6`. -/
def atanhInvTerms (b k : Nat) : Nat := (k + 6) / (2 * b) + 1

/-- The bracket of `atanh (1/q)` (`q ≥ 2`) at `k` bits: the exact partial sum bracketed by
`seriesBracket`, the upper end raised by the tail bound `2^(−k−5)`. -/
def atanhInvBracket (q k : Nat) : AzFloat × AzFloat :=
  let s := seriesBracket (AzNat.atanhNumDen q (atanhInvTerms q.log2 k)) k
  (s.1, (addPrecRound s.2 (powerOf2 (-(AzNat.ofNat (k + 5)).toAzInt)) k .Ceiling).1)

/-- Divide `p` out of `n` at most `fuel` times: the exponent and the cofactor. -/
def divOut (p : Nat) : Nat → Nat → Nat × Nat
  | 0, n => (0, n)
  | fuel + 1, n =>
    if 0 < n ∧ n % p = 0 then ((divOut p fuel (n / p)).1 + 1, (divOut p fuel (n / p)).2)
    else (0, n)

/-- The exponents `(a, b, c, d)` of `2, 3, 5, 7` in `n`, and the cofactor. -/
def smoothExps (n : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let f := n.log2 + 1
  let r₂ := divOut 2 f n
  let r₃ := divOut 3 f r₂.2
  let r₅ := divOut 5 f r₃.2
  let r₇ := divOut 7 f r₅.2
  (r₂.1, r₃.1, r₅.1, r₇.1, r₇.2)

/-- Whether `n` has no prime factor above `7`. -/
def isSmooth (n : Nat) : Bool := (smoothExps n).2.2.2.2 == 1

/-- The first integer from `n` on with no prime factor above `7`, among `fuel + 1`
candidates (`n + fuel` if there is none). -/
def nextSmoothFuel : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if isSmooth n then n else nextSmoothFuel fuel (n + 1)

/-- The least integer `≥ n` with no prime factor above `7` (a power of two is below `2 n`). -/
def nextSmooth (n : Nat) : Nat := nextSmoothFuel n n

/-- The bracket of `ln (2^a 3^b 5^c 7^d)` at `k` bits. -/
def lnSmoothBracket (a b c d k : Nat) : AzFloat × AzFloat :=
  let K₁ := 2 * (72 * a + 114 * b + 167 * c + 202 * d)
  let K₂ := 2 * (27 * a + 43 * b + 63 * c + 76 * d)
  let K₃ := 2 * (19 * a + 30 * b + 44 * c + 53 * d)
  let K₄ := 2 * (31 * a + 49 * b + 72 * c + 87 * d)
  let kk := k + (K₁ + K₂ + K₃ + K₄).log2 + 8
  let A₁ := atanhInvBracket 251 kk
  let A₂ := atanhInvBracket 449 kk
  let A₃ := atanhInvBracket 4801 kk
  let A₄ := atanhInvBracket 8749 kk
  let F₁ := ofAzNat (AzNat.ofNat K₁)
  let F₂ := ofAzNat (AzNat.ofNat K₂)
  let F₃ := ofAzNat (AzNat.ofNat K₃)
  let F₄ := ofAzNat (AzNat.ofNat K₄)
  ((subPrecRound
      (addPrecRound
        (addPrecRound (mulPrecRound F₁ A₁.1 kk .Floor).1 (mulPrecRound F₂ A₂.1 kk .Floor).1
          kk .Floor).1
        (mulPrecRound F₄ A₄.1 kk .Floor).1 kk .Floor).1
      (mulPrecRound F₃ A₃.2 kk .Ceiling).1 kk .Floor).1,
    (subPrecRound
      (addPrecRound
        (addPrecRound (mulPrecRound F₁ A₁.2 kk .Ceiling).1 (mulPrecRound F₂ A₂.2 kk .Ceiling).1
          kk .Ceiling).1
        (mulPrecRound F₄ A₄.2 kk .Ceiling).1 kk .Ceiling).1
      (mulPrecRound F₃ A₃.1 kk .Floor).1 kk .Ceiling).1)

end Azurite.AzFloat
