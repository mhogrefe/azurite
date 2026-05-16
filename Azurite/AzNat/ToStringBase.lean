import Azurite.AzNat.LimbDigits

namespace Azurite

namespace AzNat

/-- Map a digit `d ∈ [0, 36)` to its character. Digits `0`–`9` map to
    `'0'`–`'9'`; digits `10`–`35` map to `'a'`–`'z'` when
    `uppercase = false`, or `'A'`–`'Z'` when `uppercase = true`. -/
def digitToChar (d : UInt64) (uppercase : Bool) : Char :=
  if d.toNat < 10 then
    Char.ofNat ('0'.toNat + d.toNat)
  else if uppercase then
    Char.ofNat ('A'.toNat + d.toNat - 10)
  else
    Char.ofNat ('a'.toNat + d.toNat - 10)

/-- Prefix string for the conventional bases: `"0b"`, `"0o"`, `"0x"`.
    Returns `""` for any other base, so the prefix flag at other bases
    is a no-op. -/
def basePrefixStr (b : UInt64) : String :=
  if b = 2 then "0b"
  else if b = 8 then "0o"
  else if b = 16 then "0x"
  else ""

/-- `n.toStringBaseWith b uppercase prefix` renders `n : AzNat` in base
    `b`, with explicit control over digit case and base prefix. The base
    must lie in `[2, 36]`; outside that range, returns `""`. The
    `uppercase` flag controls `a`–`z` vs `A`–`Z` for `b > 10` (no-op
    otherwise). The `prefix` flag prepends `"0b"`, `"0o"`, or `"0x"` for
    `b ∈ {2, 8, 16}` respectively (no-op for other bases).

    `n = 0` always renders as `"0"` (with the prefix when requested). -/
def toStringBaseWith (b : UInt64) (uppercase : Bool) (usePrefix : Bool) (n : AzNat) : String :=
  if b < 2 ∨ 36 < b then ""
  else
    let body :=
      if n.limbs.size = 0 then "0"
      else
        String.ofList ((n.limbDigits b).toList.reverse.map fun d =>
          digitToChar d uppercase)
    if usePrefix then basePrefixStr b ++ body else body

/-- `n.toStringBase b` renders `n : AzNat` in base `b ∈ [2, 36]` with
    lowercase digit letters and no base prefix. -/
def toStringBase (b : UInt64) (n : AzNat) : String :=
  toStringBaseWith b false false n

/-- `n.toString` renders `n : AzNat` in decimal. Replaces the
    `natToChars`-based path with the limb-level `limbDigits 10` pipeline:
    repeated `divMod10p19` produces base-`10^19` super-digits, each then
    expanded to its 19 decimal digits, with trailing zeros trimmed. -/
def toString (n : AzNat) : String :=
  toStringBase 10 n

end AzNat

/-- `ToString AzNat` instance using the limb-level decimal path
    (repeated `divMod10p19` + `digitsPaddedTo` 10). -/
instance : ToString AzNat where
  toString := AzNat.toString

-- Sanity checks.

-- Decimal path agrees with the underlying `parse` round-trip.
#guard (AzNat.ofLimbs #[12345]).toString = "12345"
#guard (0 : AzNat).toString = "0"
#guard (1 : AzNat).toString = "1"
#guard (AzNat.ofLimbs #[0, 1]).toString = "18446744073709551616"
#guard (AzNat.ofLimbs #[1, 2]).toString = "36893488147419103233"

-- Base 2 / 8 / 16 (no prefix).
#guard (AzNat.ofLimbs #[100]).toStringBase 16 = "64"
#guard (AzNat.ofLimbs #[0xDEADBEEF]).toStringBase 16 = "deadbeef"
#guard (AzNat.ofLimbs #[100]).toStringBase 2 = "1100100"
#guard (AzNat.ofLimbs #[0o755]).toStringBase 8 = "755"
#guard (0 : AzNat).toStringBase 16 = "0"

-- Base > 10: lowercase letters by default; uppercase via the explicit flag.
#guard (AzNat.ofLimbs #[35]).toStringBase 36 = "z"
#guard (AzNat.ofLimbs #[35]).toStringBaseWith 36 true false = "Z"
#guard (AzNat.ofLimbs #[0xDEADBEEF]).toStringBaseWith 16 true false = "DEADBEEF"

-- Prefix flag: applies only for b ∈ {2, 8, 16}.
#guard (AzNat.ofLimbs #[100]).toStringBaseWith 16 false true = "0x64"
#guard (AzNat.ofLimbs #[100]).toStringBaseWith 2 false true = "0b1100100"
#guard (AzNat.ofLimbs #[0o755]).toStringBaseWith 8 false true = "0o755"
#guard (AzNat.ofLimbs #[100]).toStringBaseWith 10 false true = "100" -- no prefix at b=10
#guard (AzNat.ofLimbs #[0xDEADBEEF]).toStringBaseWith 16 true true = "0xDEADBEEF"
#guard (0 : AzNat).toStringBaseWith 16 false true = "0x0"

-- Out-of-range bases: empty string.
#guard (AzNat.ofLimbs #[100]).toStringBase 1 = ""
#guard (AzNat.ofLimbs #[100]).toStringBase 37 = ""

end Azurite
