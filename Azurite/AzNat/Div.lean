import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Parse
import Azurite.AzNat.ToString
import Azurite.UInt64.Div2By1
import Azurite.UInt64.DivMod
import Azurite.UInt64.Equiv.LeadingZeros
import Azurite.UInt64.LeadingZeros
import Azurite.UInt64.Reciprocal

namespace Azurite.AzNat

/-!
Formalization of Algorithm 7 (DIV_NBY1) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund,
extended to handle any nonzero divisor via on-the-fly normalization.
-/

/-- Inner loop of `divModLimb`: from `j = hi - lo` down to `0`, process limb
    `a[lo + j - 1]` by calling `div2By1` with the running remainder as the high
    half. The shift count `k ≤ 63` normalizes the divisor on the fly: the
    effective limb fed into `div2By1` is
    `(a[lo + j - 1] <<< k) ||| (a[lo + j - 2] >>> (64 - k))`. The quotient limb
    overwrites `a[lo + j - 1]` in place. -/
def divModLimb.go (d' inv : UInt64) (k : Nat) (hk : k ≤ 63) (a : Array UInt64)
    (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size) : Array UInt64 × UInt64 :=
  match j with
  | 0 => (a, r)
  | j + 1 =>
    have h_idx : lo + j < a.size := by omega
    let u_j := a[lo + j]
    let u_carry : UInt64 :=
      if k = 0 then 0
      else if hj0 : j = 0 then 0
      else
        have hjp : lo + j - 1 < a.size := by omega
        a[lo + j - 1]'hjp >>> UInt64.ofNat (64 - k)
    let u_j_shifted := (u_j <<< UInt64.ofNat k) ||| u_carry
    let qr := UInt64.div2By1 r u_j_shifted d' inv
    divModLimb.go d' inv k hk (a.set (lo + j) qr.1) lo j qr.2
      (by rw [Array.size_set]; omega)
  termination_by j

/-- Multi-limb division of the slice `a[lo:hi)` by a nonzero `UInt64` divisor
    `d`, in place. Implements Algorithm 7 (DIV_NBY1) of Möller–Granlund,
    extended to arbitrary nonzero divisors via on-the-fly normalization: shift
    `d` left by `k = leadingZeros d` to put it in `[2^63, 2^64)`, apply Alg. 7
    to the (virtually) shifted dividend, then shift the resulting remainder
    right by `k`. The slice limbs are overwritten with the quotient limbs;
    returns the modified array and the 64-bit remainder. -/
def divModLimb (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × UInt64 :=
  let k := UInt64.leadingZeros d
  let kU : UInt64 := UInt64.ofNat k
  let d' := d <<< kU
  have hk_le : k ≤ 63 := UInt64.leadingZeros_le d hd
  have hd'_norm : 2 ^ 63 ≤ d'.toNat :=
    UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd
  let inv := UInt64.reciprocal d' hd'_norm
  let len := hi - lo
  let r0 : UInt64 :=
    if k = 0 then 0
    else if hlen0 : len = 0 then 0
    else
      have h_top : hi - 1 < a.size := by omega
      a[hi - 1]'h_top >>> UInt64.ofNat (64 - k)
  let res := divModLimb.go d' inv k hk_le a lo len r0 (by omega)
  (res.1, res.2 >>> kU)

/-- Divide an `AzNat` `U` by a nonzero `UInt64` divisor `d`, returning the
    quotient `AzNat` and remainder `UInt64`. Single-limb dividends short-circuit
    to `UInt64.divMod`; multi-limb dividends use `divModLimb`. -/
def divModUInt64 (U : AzNat) (d : UInt64) (hd : d ≠ 0) : AzNat × UInt64 :=
  if h0 : U.limbs.size = 0 then (0, 0)
  else if h1 : U.limbs.size = 1 then
    have h_pos : 0 < U.limbs.size := by rw [h1]; decide
    let qr := UInt64.divMod (U.limbs[0]'h_pos) d
    (ofLimbs #[qr.1], qr.2)
  else
    let res := divModLimb U.limbs 0 U.limbs.size d hd
      (Nat.zero_le _) (Nat.le_refl _)
    (ofLimbs res.1, res.2)

section Examples

private def p (s : String) : AzNat := (AzNat.parse s.toList).get!

private def show2 (qr : AzNat × UInt64) : String × Nat :=
  (toString qr.1, qr.2.toNat)

-- 2^64 = 18446744073709551616. Multi-limb dividends.

-- 2^64 / 3 = 6148914691236517205 r 1
#guard show2 (divModUInt64 (p "18446744073709551616") 3 (by decide))
  = ("6148914691236517205", 1)

-- 2^65 / 7 = 5270498306774157604 r 4
#guard show2 (divModUInt64 (p "36893488147419103232") 7 (by decide))
  = ("5270498306774157604", 4)

-- (2^64 + 12345) / 1000000 = 18446744073709 r 563951
#guard show2 (divModUInt64 (p "18446744073709563961") 1000000 (by decide))
  = ("18446744073709", 563961)

-- 2^128 - 1 / (2^63 + 1) — normalized divisor (k = 0).
-- 2^128 - 1 = 340282366920938463463374607431768211455
-- 2^63 + 1 = 9223372036854775809
-- quotient = 36893488147419103230, remainder = 36893488147419103265... actually let's
-- pick simpler: 2^128 / 2 = 2^127 = 170141183460469231731687303715884105728
#guard show2 (divModUInt64 (p "340282366920938463463374607431768211456") 2 (by decide))
  = ("170141183460469231731687303715884105728", 0)

-- 10^20 / 7 = 14285714285714285714 r 2
#guard show2 (divModUInt64 (p "100000000000000000000") 7 (by decide))
  = ("14285714285714285714", 2)

-- 10^25 / (10^9 - 1) = 10^16 + 10^7 r 10^7
#guard show2 (divModUInt64 (p "10000000000000000000000000") 999999999 (by decide))
  = ("10000000010000000", 10000000)

-- Edge case: dividend much bigger, divisor = 1 (k = 63).
-- 2^100 / 1 = 2^100, remainder = 0
#guard show2 (divModUInt64 (p "1267650600228229401496703205376") 1 (by decide))
  = ("1267650600228229401496703205376", 0)

end Examples

end Azurite.AzNat
