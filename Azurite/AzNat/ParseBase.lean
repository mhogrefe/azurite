import Azurite.AzNat.OfLimbDigits
import Azurite.AzNat.ToStringBase

namespace Azurite

namespace AzNat

/-- Convert a single character to its digit value (0–35), case-insensitive.
    Returns `none` for characters outside `0`–`9`, `a`–`z`, `A`–`Z`. -/
def charToDigit (c : Char) : Option UInt64 :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (UInt64.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some (UInt64.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c ∧ c ≤ 'Z' then
    some (UInt64.ofNat (c.toNat - 'A'.toNat + 10))
  else none

/-- Strip the conventional base prefix (`"0b"`, `"0o"`, `"0x"`) if
    present; return the detected base together with the remaining
    string. Returns `none` if no prefix is recognised. The prefix is
    matched case-sensitively (lowercase only), matching the convention
    in Lean, C, Rust, and most modern languages — and matching what
    `toString` emits. -/
def stripPrefix (s : String) : Option (UInt64 × String) :=
  if s.startsWith "0b" then some (2, (s.drop 2).copy)
  else if s.startsWith "0o" then some (8, (s.drop 2).copy)
  else if s.startsWith "0x" then some (16, (s.drop 2).copy)
  else none

/-- Parse a character list in base `b` into an MSB-first digit array.
    Rejects (returns `none`) on any character that is not a valid digit
    in base `b`. -/
def parseDigitsInto (b : UInt64) (cs : List Char) : Option (Array UInt64) :=
  cs.foldl (init := some #[]) fun acc c =>
    match acc with
    | none => none
    | some arr =>
      match charToDigit c with
      | none => none
      | some d => if d < b then some (arr.push d) else none

/-- Build an `AzNat` from a digit-character list in base `b`. The list is
    parsed MSB-first; we reverse to feed `ofLimbDigits` (LSB-first). -/
def buildFromChars (b : UInt64) (cs : List Char) : Option AzNat :=
  match parseDigitsInto b cs with
  | none => none
  | some arr => some (AzNat.ofLimbDigits b arr.reverse)

/-- `parseBase b s` parses `s` in base `b ∈ [2, 36]`. A leading
    `"0b"`/`"0o"`/`"0x"` prefix is **ignored** (stripped before parsing
    in the user-supplied base). Returns `none` on empty input, an
    invalid digit character, a digit `≥ b`, or `b` outside `[2, 36]`. -/
def parseBase (b : UInt64) (s : String) : Option AzNat :=
  if b < 2 ∨ 36 < b then none
  else
    let rest := match stripPrefix s with
      | some (_, r) => r
      | none => s
    if rest.isEmpty then none
    else buildFromChars b rest.toList

/-- `parse s` parses `s`, using the conventional prefix to pick the base
    (default decimal):
    * `"0b"`/`"0B"` → base 2;
    * `"0o"`/`"0O"` → base 8;
    * `"0x"`/`"0X"` → base 16;
    * otherwise → base 10.
    Returns `none` on empty input, just-prefix input, or any invalid
    digit character. -/
def parse (s : String) : Option AzNat :=
  match stripPrefix s with
  | some (b, rest) =>
    if rest.isEmpty then none
    else buildFromChars b rest.toList
  | none =>
    if s.isEmpty then none
    else buildFromChars 10 s.toList

end AzNat

-- Sanity checks.

-- Default decimal.
#guard AzNat.parse "123" = some (AzNat.ofLimbs #[123])
#guard AzNat.parse "0" = some (0 : AzNat)
#guard AzNat.parse "12345" = some (AzNat.ofLimbs #[12345])

-- Empty / malformed input.
#guard AzNat.parse "" = none
#guard AzNat.parse "12abc" = none
#guard AzNat.parse "0x" = none
#guard AzNat.parse "0b" = none

-- Auto-detected prefix (lowercase only).
#guard AzNat.parse "0b101" = some (AzNat.ofLimbs #[5])
#guard AzNat.parse "0xff" = some (AzNat.ofLimbs #[255])
#guard AzNat.parse "0o17" = some (AzNat.ofLimbs #[15])
#guard AzNat.parse "0xDEADBEEF" = some (AzNat.ofLimbs #[0xDEADBEEF])

-- Uppercase prefixes are not recognised (matches Lean / C / Rust convention).
-- "0X" / "0B" / "0O" fall through to decimal parsing and fail on the second char.
#guard AzNat.parse "0XFF" = none
#guard AzNat.parse "0B101" = none

-- Mixed case in hex digits is fine.
#guard AzNat.parse "0xDeAdBeEf" = some (AzNat.ofLimbs #[0xDEADBEEF])

-- Base given, prefix ignored.
#guard AzNat.parseBase 10 "123" = some (AzNat.ofLimbs #[123])
#guard AzNat.parseBase 16 "ff" = some (AzNat.ofLimbs #[255])
#guard AzNat.parseBase 16 "FF" = some (AzNat.ofLimbs #[255])
#guard AzNat.parseBase 2 "101" = some (AzNat.ofLimbs #[5])
#guard AzNat.parseBase 8 "755" = some (AzNat.ofLimbs #[0o755])

-- Prefix stripped regardless of match with the user-supplied base.
#guard AzNat.parseBase 16 "0xff" = some (AzNat.ofLimbs #[255])
-- "0x10" with parseBase 10 strips the "0x" and parses "10" in decimal.
#guard AzNat.parseBase 10 "0x10" = some (AzNat.ofLimbs #[10])

-- Up-to base 36, both cases.
#guard AzNat.parseBase 36 "z" = some (AzNat.ofLimbs #[35])
#guard AzNat.parseBase 36 "Z" = some (AzNat.ofLimbs #[35])
#guard AzNat.parseBase 36 "10" = some (AzNat.ofLimbs #[36])

-- Out-of-range bases.
#guard AzNat.parseBase 1 "0" = none
#guard AzNat.parseBase 37 "0" = none

-- Invalid digit (digit ≥ base).
#guard AzNat.parseBase 10 "12a" = none
#guard AzNat.parseBase 2 "012" = none
#guard AzNat.parseBase 10 "12A" = none

-- Leading zeros allowed.
#guard AzNat.parse "007" = some (AzNat.ofLimbs #[7])
#guard AzNat.parseBase 16 "0000ff" = some (AzNat.ofLimbs #[255])

-- Round-trip via `parse` and `toString`.
#guard AzNat.parse (AzNat.ofLimbs #[12345]).toString = some (AzNat.ofLimbs #[12345])
#guard AzNat.parse (AzNat.ofLimbs #[0xDEADBEEF]).toString = some (AzNat.ofLimbs #[0xDEADBEEF])

-- Multi-limb values.
#guard AzNat.parse "18446744073709551616" = some (AzNat.ofLimbs #[0, 1])
#guard AzNat.parse "36893488147419103233" = some (AzNat.ofLimbs #[1, 2])
#guard AzNat.parse "0xffffffffffffffff" = some (AzNat.ofLimbs #[0xffffffffffffffff])
#guard AzNat.parse "0x10000000000000000" = some (AzNat.ofLimbs #[0, 1])

end Azurite
