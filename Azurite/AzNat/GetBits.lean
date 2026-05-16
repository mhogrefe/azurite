import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Parse
import Azurite.AzNat.ShiftRight

namespace Azurite

/-- `getBitsAsLimb n i j h` extracts bits `[i, j)` of `n` as a single `UInt64`,
    given a proof that the width `j - i` fits in 64 bits. Equivalent to
    `(n >>> i).modPow2 (j - i)`, but computed without constructing an
    intermediate shifted `AzNat`: at most two limbs of `n` are read.

    Returns `0` when `i ≥ j` or when bit `i` is beyond `n`'s representation. -/
def AzNat.getBitsAsLimb (n : AzNat) (i j : Nat) (_h : j - i ≤ 64) : UInt64 :=
  if i ≥ j then 0
  else
    let q := i / 64
    let r := i % 64
    let width := j - i
    if hq : q ≥ n.limbs.size then 0
    else
      have hq_lt : q < n.limbs.size := Nat.lt_of_not_le hq
      let lowBits := n.limbs[q] >>> UInt64.ofNat r
      -- When `r + width > 64`, the high `r + width - 64` bits live in limb `q + 1`.
      let combined : UInt64 :=
        if r + width > 64 then
          if hq1 : q + 1 < n.limbs.size then
            lowBits ||| (n.limbs[q + 1] <<< UInt64.ofNat (64 - r))
          else
            lowBits  -- limb `q + 1` is implicitly zero
        else
          lowBits
      if width = 64 then combined
      else combined &&& (((1 : UInt64) <<< UInt64.ofNat width) - 1)

/-- `getBits n i j` extracts bits `[i, j)` of `n` as a fresh `AzNat`,
    equivalent to `(n >>> i).modPow2 (j - i)` but built limb-by-limb via
    `getBitsAsLimb`, avoiding the intermediate shifted-`AzNat` allocation. -/
def AzNat.getBits (n : AzNat) (i j : Nat) : AzNat :=
  if i ≥ j then 0
  else
    let width := j - i
    let numLimbs := (width + 63) / 64
    AzNat.ofLimbs ((Array.range numLimbs).map fun k =>
      n.getBitsAsLimb (i + k * 64) (min (i + k * 64 + 64) j) (by omega))

-- Sanity checks.
-- `n = 0b...1010 1100 = 0xAC = 172`. Bits: [0,1,1,0,1,0,1,0, ...].
#guard (Azurite.AzNat.parse "172".toList).get!.getBitsAsLimb 0 4 (by omega) == 12  -- 0b1100
#guard (Azurite.AzNat.parse "172".toList).get!.getBitsAsLimb 4 8 (by omega) == 10  -- 0b1010
#guard (Azurite.AzNat.parse "172".toList).get!.getBitsAsLimb 0 8 (by omega) == 172
#guard (Azurite.AzNat.parse "172".toList).get!.getBitsAsLimb 2 6 (by omega) == 11  -- 0b1011

-- Single-limb extraction agrees with the spec on large `n`.
#guard (Azurite.AzNat.parse "123456789".toList).get!.getBitsAsLimb 0 64 (by omega) == 123456789
#guard (Azurite.AzNat.parse "123456789".toList).get!.getBitsAsLimb 0 0 (by omega) == 0
#guard (Azurite.AzNat.parse "123456789".toList).get!.getBitsAsLimb 100 164 (by omega) == 0

-- Cross-limb extraction: `n = 2^63 + 2^65 = 46116860184273879040`.
-- Bit 63 = 1, bit 64 = 0, bit 65 = 1, others 0.
-- Bits [60, 68) = 0b 0010 1000 = 40.
#guard (Azurite.AzNat.parse "46116860184273879040".toList).get!.getBitsAsLimb 60 68 (by omega)
       == 40

-- `getBits` parallels `getBitsAsLimb` but allows wide ranges.
#guard ((Azurite.AzNat.parse "172".toList).get!.getBits 0 8).toNat == 172
#guard ((Azurite.AzNat.parse "172".toList).get!.getBits 4 8).toNat == 10
#guard ((Azurite.AzNat.parse "172".toList).get!.getBits 0 0).toNat == 0

-- Wide extraction crossing the 64-bit boundary.
-- `n = 2^65 + 1 = 36893488147419103233`. Bits 0 and 65 set.
-- getBits 0 66: bits [0, 66) includes both 0 and 65 → value 2^65 + 1 = n.
#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.getBits 0 66).toNat
       == 36893488147419103233
-- getBits 1 66: bits [1, 66), bit 0 of result = bit 1 of n = 0, bit 64 of result = bit 65 of n = 1.
-- Value = 2^64 = 18446744073709551616.
#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.getBits 1 66).toNat
       == 18446744073709551616

-- getBits agrees with the naive spec `(n >>> i).modPow2 (j - i)` on a wider example.
#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.getBits 30 100)
       == (((Azurite.AzNat.parse "36893488147419103233".toList).get!.shiftRight 30).modPow2 70)

#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.getBits 0 200)
       == (Azurite.AzNat.parse "36893488147419103233".toList).get!

end Azurite
