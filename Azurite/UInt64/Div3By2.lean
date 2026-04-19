import Azurite.UInt64.Reciprocal3By2
import Azurite.UInt64.WideAdd
import Azurite.UInt64.WideMul
import Azurite.UInt64.WideSub

namespace UInt64

/-!
Formalization of Algorithm 5 (DIV3BY2) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund.
-/

/-- Tail of Algorithm 5 (final correction step): if `[r1, r0] ≥ [d1, d0]`, bump
the quotient and subtract the divisor from the remainder. Factored out so
proofs can reason about it by substitution rather than kernel-reducing a nested
tuple let-binding. -/
@[inline]
def div3By2Tail (q1 r1 r0 d1 d0 : UInt64) : UInt64 × UInt64 × UInt64 :=
  if r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0) then
    let (r1, r0) := wideSub (r1, r0) (d1, d0)
    (q1 + 1, r1, r0)
  else
    (q1, r1, r0)

/-- Algorithm 5 (DIV3BY2) of Möller–Granlund: given a normalized 128-bit
divisor `(d1, d0)` (i.e. `2^63 ≤ d1 < 2^64`), a 192-bit dividend `(u2, u1, u0)`
with `(u2, u1) < (d1, d0)`, and the precomputed reciprocal
`v = reciprocal3By2 d1 d0`, return `(q, r1, r0)` where `q` is the 64-bit
quotient and `(r1, r0)` is the 128-bit remainder. -/
@[inline]
def div3By2 (u2 u1 u0 d1 d0 v : UInt64) : UInt64 × UInt64 × UInt64 :=
  let (q1, q0) := wideAdd (wideMul v u2) (u2, u1)
  let r1 := u1 - q1 * d1
  let (t1, t0) := wideMul d0 q1
  let (r1, r0) := wideSub (wideSub (r1, u0) (t1, t0)) (d1, d0)
  let q1 := q1 + 1
  if r1 ≥ q0 then
    let (r1, r0) := wideAdd (r1, r0) (d1, d0)
    div3By2Tail (q1 - 1) r1 r0 d1 d0
  else
    div3By2Tail q1 r1 r0 d1 d0

end UInt64
