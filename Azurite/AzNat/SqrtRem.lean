import Azurite.AzNat.Add
import Azurite.AzNat.Basic
import Azurite.AzNat.Compare
import Azurite.AzNat.Conversion -- for UInt64.toAzNat / single-limb dispatch
import Azurite.AzNat.Div
import Azurite.AzNat.Mul
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Size
import Azurite.AzNat.Square
import Azurite.AzNat.Sub
import Azurite.AzNat.ToStringBase
import Azurite.UInt64.SqrtRem

namespace Azurite.AzNat

/-!
Integer square root with remainder for `AzNat`, base case for the
recursive Brent–Zimmermann sqrtRem.

Implements MCA Algorithm 1.13 (`SqrtInt`).  Works for arbitrary
limb counts; the recursive divide-and-conquer version (Algorithm
1.14) eventually delegates to this once the input is small enough
that the recursion no longer helps.

  - Initial guess `u₀ = 2^⌈b/2⌉`, where `b = AzNat.size m` is the
    exact bit length of `m`.  By the bound `⌊√m⌋ ≤ 2^⌈b/2⌉`, this
    is a strict upper bound on the answer, and within a factor of
    `√2` of optimal — so the iteration is in the
    quadratic-convergence regime from the start.

  - Loop body: `u ← ⌊(s + ⌊m/s⌋) / 2⌋`, terminating on `u ≥ s`.
    The division uses the specialised `AzNat.div`; the right shift
    by `1` uses `AzNat.shiftRight`.

  - Termination is bounded by fuel `64 · n + 1`, which exceeds the
    worst-case iteration count (a handful of quadratic-convergence
    iterations from a tight initial guess).
-/

/-- Initial guess `2^⌈b/2⌉` where `b = AzNat.size m` (the bit length).
    By the bit-length bound `⌊√m⌋ ≤ 2^⌈b/2⌉`, this is a strict upper
    bound on the answer; it is also within a factor of `√2` of
    optimal. -/
def basecaseSqrtRem.initialGuess (m : AzNat) : AzNat :=
  (1 : AzNat) <<< ((m.size + 1) / 2)

/-- Newton iteration loop. Iterates `u ← ⌊(s + ⌊m/s⌋) / 2⌋` until
    `u ≥ s` (the MCA termination), returning the previous `s` as
    `⌊√m⌋`.  `fuel` bounds the iteration count. -/
def basecaseSqrtRem.loop (m s : AzNat) (fuel : Nat) : AzNat :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s = 0 then s  -- unreachable from the entry point; defensive
    else
      let q := m / s
      let t := s + q
      let u := t >>> 1
      if u ≥ s then s
      else basecaseSqrtRem.loop m u fuel'

/-- Integer square root for arbitrary `AzNat` input, implementing
    MCA Algorithm 1.13.  Returns the unique `s` with
    `s² ≤ m < (s + 1)²`.

    This is the basecase for the recursive divide-and-conquer
    sqrt (MCA Algorithm 1.14); it's used directly on inputs small
    enough that the recursion doesn't help.

    Single-limb inputs delegate to `UInt64.sqrt` (Float guess +
    correction loops, much faster than an AzNat-level Newton
    iteration).  Larger inputs run MCA's Newton iteration with fuel
    `2^⌈b/2⌉ + 1 = initialGuess.toNat + 1`, which is always
    sufficient: the loop's iteration count is bounded by the
    initial guess (each step strictly decreases `s` until
    termination), so the fuel never runs out. -/
def basecaseSqrt (m : AzNat) : AzNat :=
  if m.limbs.size = 0 then 0
  else if h1 : m.limbs.size = 1 then
    have hpos : 0 < m.limbs.size := by omega
    (Azurite.UInt64.sqrt (m.limbs[0]'hpos)).toAzNat
  else
    let u₀ := basecaseSqrtRem.initialGuess m
    let fuel := (1 : Nat) <<< ((m.size + 1) / 2) + 1
    basecaseSqrtRem.loop m u₀ fuel

/-- Integer square root with remainder.  Returns `(s, r)` with
    `s * s + r = m`, `r ≤ 2 * s`.  Computes `r := m - s.square` —
    using the specialised `AzNat.square` since it's faster than
    `s * s`. -/
def basecaseSqrtRem (m : AzNat) : AzNat × AzNat :=
  let s := basecaseSqrt m
  (s, m - s.square)

/-!
Divide-and-conquer integer square root (MCA Algorithm 1.12).

The body splits `m = a₃ β^{3ℓ} + a₂ β^{2ℓ} + a₁ β^ℓ + a₀` with
`β = 2^64` the limb base and `ℓ = ⌊(n−1)/4⌋`.  The high half
`a₃ β^ℓ + a₂` is recursively rooted to get `(s', r')`, then one
divrem `(r' β^ℓ + a₁) / (2 s')` and one squaring `q²` combine to
the full result.  When `r` would go negative, a single
`s ← s − 1; r ← r + 2s − 1` adjustment restores the invariant.

Asymptotically `T(n) = T(n/2) + Θ(n²)` with schoolbook
multiplication and division, dominated by the `Θ(n²/2)` div and
`Θ(n²/4)` square at each level, giving `T(n) ≈ (2/3) n²` — better
than the basecase Newton iteration's `Θ(n² log log n)`.

Slice-style: the recursive core takes the limb array `a` plus
`(lo, len)` offsets, like `karatsubaMulLimbsRec`.  Recursive calls
on the top half simply pass new offsets — no `top` allocation.
Splits `a₀`/`a₁` are extracted via `Array.extract`, and the inner
operations (`<<<`, `+`, `divMod`, `square`, `-`) use the
`AzNat`-level machinery directly. -/

/-- Slice-style body of `sqrtRem`.  Operates on the slice
    `a[lo, lo + len)` representing the input number (LSB-first),
    returning `(s, r)` as fresh `AzNat`s. -/
def sqrtRem.aux (a : Array UInt64) (lo len : Nat) (h : lo + len ≤ a.size) :
    AzNat × AzNat :=
  let ℓ := (len - 1) / 4
  if ℓ = 0 then
    -- Basecase: copy the slice into an AzNat and delegate.
    basecaseSqrtRem (ofLimbs (a.extract lo (lo + len)))
  else
    let bℓ := 64 * ℓ
    -- Recurse on the top slice [lo + 2ℓ, lo + len) (length len − 2ℓ).
    have h_top : (lo + 2 * ℓ) + (len - 2 * ℓ) ≤ a.size := by omega
    let sr' := sqrtRem.aux a (lo + 2 * ℓ) (len - 2 * ℓ) h_top
    let s' := sr'.1
    let r' := sr'.2
    -- Extract a₀ and a₁ from the slice as AzNats (each ℓ limbs).
    let a₀ := ofLimbs (a.extract lo (lo + ℓ))
    let a₁ := ofLimbs (a.extract (lo + ℓ) (lo + 2 * ℓ))
    -- DivMod (r' β^ℓ + a₁) by (2 s').
    let dividend := (r' <<< bℓ) + a₁
    let divisor := s' <<< 1
    let qu := dividend.divMod divisor
    let q := qu.1
    let u := qu.2
    -- Combine: s := s' β^ℓ + q.
    let s := (s' <<< bℓ) + q
    -- r := u β^ℓ + a₀ − q²; adjust if it would underflow.
    let lhs := (u <<< bℓ) + a₀
    let rhs := q.square
    if lhs ≥ rhs then
      (s, lhs - rhs)
    else
      -- r is "negative" (lhs < rhs): apply the single
      -- adjustment `r ← r + 2s − 1; s ← s − 1`.
      -- Computed as `(2s − 1) − (rhs − lhs)`.
      (s - 1, (s <<< 1) - 1 - (rhs - lhs))
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Divide-and-conquer integer square root with remainder. -/
def sqrtRem (m : AzNat) : AzNat × AzNat :=
  sqrtRem.aux m.limbs 0 m.limbs.size (by omega)

/-- Divide-and-conquer integer square root. -/
def sqrt (m : AzNat) : AzNat := (sqrtRem m).1

end Azurite.AzNat

section Examples

open Azurite Azurite.AzNat

-- Tiny inputs: agree with `UInt64.sqrtRem` (where applicable).
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 0); AzNat.toString s == "0" && AzNat.toString r == "0")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 1); AzNat.toString s == "1" && AzNat.toString r == "0")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 2); AzNat.toString s == "1" && AzNat.toString r == "1")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 100); AzNat.toString s == "10" && AzNat.toString r == "0")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 9999); AzNat.toString s == "99" && AzNat.toString r == "198")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat 10000); AzNat.toString s == "100" && AzNat.toString r == "0")

-- 2-limb perfect squares: (2^32)² = 2^64.
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat (2 ^ 64));
  AzNat.toString s == "4294967296" && AzNat.toString r == "0")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat (2 ^ 64 + 1));
  AzNat.toString s == "4294967296" && AzNat.toString r == "1")

-- A non-square 2-limb input near 2^96.
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat (2 ^ 96));
  AzNat.toString s == "281474976710656" && AzNat.toString r == "0")

-- Larger: a perfect square at 4 limbs.
-- (2^120)² = 2^240, which lives in 4 limbs.
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat (2 ^ 240));
  AzNat.toString s == "1329227995784915872903807060280344576" && AzNat.toString r == "0")
#guard (let (s, r) := basecaseSqrtRem (AzNat.ofNat (2 ^ 240 + 1));
  AzNat.toString s == "1329227995784915872903807060280344576" && AzNat.toString r == "1")

-- Divide-and-conquer: small inputs delegate to basecase, so should match.
#guard (let (s, r) := sqrtRem (AzNat.ofNat 0); AzNat.toString s == "0" && AzNat.toString r == "0")
#guard (let (s, r) := sqrtRem (AzNat.ofNat 9999); AzNat.toString s == "99" && AzNat.toString r == "198")
#guard (let (s, r) := sqrtRem (AzNat.ofNat (2 ^ 240 + 1));
  AzNat.toString s == "1329227995784915872903807060280344576" && AzNat.toString r == "1")

-- D&C kicks in at ≥ 5 limbs. (2^192)² = 2^384, lives in 7 limbs.
#guard (let (s, r) := sqrtRem (AzNat.ofNat (2 ^ 384));
  AzNat.toString s == "6277101735386680763835789423207666416102355444464034512896" &&
  AzNat.toString r == "0")
#guard (let (s, r) := sqrtRem (AzNat.ofNat (2 ^ 384 + 1));
  AzNat.toString s == "6277101735386680763835789423207666416102355444464034512896" &&
  AzNat.toString r == "1")

-- A bigger perfect square: (2^320)² = 2^640, 11 limbs.
#guard (let (s, r) := sqrtRem (AzNat.ofNat (2 ^ 640));
  AzNat.toString s ==
    "2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576" &&
  AzNat.toString r == "0")

-- A non-trivial non-square: 2^384 + 2^192 (= roughly the next bit above a square).
#guard AzNat.toString (sqrtRem (AzNat.ofNat (2 ^ 384 + 2 ^ 192))).1 ==
  "6277101735386680763835789423207666416102355444464034512896"

end Examples
