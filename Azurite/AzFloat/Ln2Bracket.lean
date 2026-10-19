/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Ziv
import Azurite.AzNat.AtanhSplit
import Azurite.AzNat.Pow
import Azurite.AzRat.Add
import Azurite.AzRat.Construct
import Azurite.AzRat.Div
import Azurite.AzRat.Mul
import Azurite.AzRat.Sub

/-!
## The exact bracket of `ln 2`

`ln 2 = 18 atanh(1/26) − 2 atanh(1/4801) + 8 atanh(1/8749)`, each `atanh(1/q) = ∑_k
1/((2k+1) q^(2k+1))` summed exactly by binary splitting (`AzNat.atanhNumDen`).  Truncating the
three series after `N₁, N₂, N₃` terms and adding the tail bounds `(4/3) t_N` on the appropriate
side gives exact rationals `lo ≤ ln 2 ≤ hi` (`ln2Bracket`), of width below `2^(−w)` when
`(2N_q+1)⌊lg q⌋ ≥ w + 6` (`ln2N₁`, `ln2N₂`, `ln2N₃`, with `⌊lg 26⌋ = 4`, `⌊lg 4801⌋ = 12`,
`⌊lg 8749⌋ = 13`).  `ln2Approx w` rounds the two ends at any requested precision — the bracket
Ziv's loop tests (`Azurite/AzFloat/Ln2.lean`).  One evaluation of the three series per level.
The reciprocal bracket `log2EBracket w = (1/hi, 1/lo)` encloses `log₂ e = 1/ln 2` at no extra
cost (`log2EApprox`).

The theory is `Azurite/BrentZimmermann/Chapter4/Ln2BinarySplitting.lean`; the proofs are in
`Azurite/AzFloat/Equiv/Ln2Bracket.lean`.
-/

namespace Azurite.AzFloat

/-- The rational `n/d` from a pair of naturals. -/
def ofAzNatPair (r : AzNat × AzNat) : AzRat := AzRat.ofAzNats r.1 r.2

/-- `∑_{k<N} 1/((2k+1) q^(2k+1))` as an exact rational, by binary splitting. -/
def atanhRat (q N : Nat) : AzRat := ofAzNatPair (AzNat.atanhNumDen q N)

/-- The term `t_N = 1/((2N+1) q^(2N+1))` as an exact rational. -/
def atanhTermRat (q N : Nat) : AzRat :=
  AzRat.ofAzNats (AzNat.ofNat 1) (AzNat.ofNat (2 * N + 1) * (AzNat.ofNat q).pow (2 * N + 1))

/-- The natural `n` as a rational. -/
def ratNat (n : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat n) (AzNat.ofNat 1)

/-- `4/3`, the tail factor. -/
def fourThirds : AzRat := AzRat.ofAzNats (AzNat.ofNat 4) (AzNat.ofNat 3)

/-- Terms for `atanh(1/26)` at working precision `w`: `(2N+1)·4 ≥ w + 6`. -/
def ln2N₁ (w : Nat) : Nat := (w + 6) / 8 + 1

/-- Terms for `atanh(1/4801)`: `(2N+1)·12 ≥ w + 6`. -/
def ln2N₂ (w : Nat) : Nat := (w + 6) / 24 + 1

/-- Terms for `atanh(1/8749)`: `(2N+1)·13 ≥ w + 6`. -/
def ln2N₃ (w : Nat) : Nat := (w + 6) / 26 + 1

/-- The exact rational bracket `[lo, hi] ∋ ln 2` at working precision `w`: the three truncated
series `S_q`, with the tail bounds `(4/3) t_q` added where they enlarge the bracket. -/
def ln2Bracket (w : Nat) : AzRat × AzRat :=
  let S₁ := atanhRat 26 (ln2N₁ w)
  let S₂ := atanhRat 4801 (ln2N₂ w)
  let S₃ := atanhRat 8749 (ln2N₃ w)
  let T₁ := fourThirds * atanhTermRat 26 (ln2N₁ w)
  let T₂ := fourThirds * atanhTermRat 4801 (ln2N₂ w)
  let T₃ := fourThirds * atanhTermRat 8749 (ln2N₃ w)
  (ratNat 18 * S₁ - ratNat 2 * (S₂ + T₂) + ratNat 8 * S₃,
    ratNat 18 * (S₁ + T₁) - ratNat 2 * S₂ + ratNat 8 * (S₃ + T₃))

/-- The two ends of the bracket, rounded at any requested precision. -/
def ln2Approx (w : Nat) : Roundable × Roundable :=
  let b := ln2Bracket w
  (fun p mode => ofAzRatRound b.1 p mode, fun p mode => ofAzRatRound b.2 p mode)

/-- The exact rational bracket `[1/hi, 1/lo] ∋ log₂ e = 1/ln 2`: the reciprocal of the bracket
of `ln 2`. -/
def log2EBracket (w : Nat) : AzRat × AzRat :=
  let b := ln2Bracket w
  ((1 : AzRat) / b.2, (1 : AzRat) / b.1)

/-- The two ends of the `log₂ e` bracket, rounded at any requested precision. -/
def log2EApprox (w : Nat) : Roundable × Roundable :=
  let b := log2EBracket w
  (fun p mode => ofAzRatRound b.1 p mode, fun p mode => ofAzRatRound b.2 p mode)

end Azurite.AzFloat
