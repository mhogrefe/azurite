import Azurite.UInt64.Reciprocal
import Azurite.UInt64.WideMul

namespace UInt64

/-!
Formalization of Algorithm 6 (RECIPROCAL_WORD_3BY2) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund.
-/

/-- Steps 5–7 of Algorithm 6: given adjusted `v` and `p`, compute the final
reciprocal. Factored out so proofs can reason about it by substitution rather
than kernel-reducing a nested tuple let-binding. -/
@[inline]
def reciprocal3By2Tail (d_hi d_lo v p : UInt64) : UInt64 :=
  let (t_hi, t_lo) := wideMul v d_lo
  let p := p + t_hi
  if p < t_hi then
    let v := v - 1
    if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
  else
    v

/-- Algorithm 6 (RECIPROCAL_WORD_3BY2) of Möller–Granlund: given a normalized
128-bit divisor `d = d_hi · 2^64 + d_lo` with `2^63 ≤ d_hi < 2^64`, return the
precomputed reciprocal `v = ⌊(2^{192} − 1) / d⌋ − 2^{64}` used by DIV3BY2. -/
@[inline]
def reciprocal3By2 (d_hi d_lo : UInt64) (hd : 2 ^ 63 ≤ d_hi.toNat) : UInt64 :=
  let v := reciprocal d_hi hd
  let p := d_hi * v + d_lo
  if p < d_lo then
    let v := v - 1
    if p ≥ d_hi then reciprocal3By2Tail d_hi d_lo (v - 1) (p - d_hi - d_hi)
    else reciprocal3By2Tail d_hi d_lo v (p - d_hi)
  else
    reciprocal3By2Tail d_hi d_lo v p

end UInt64
