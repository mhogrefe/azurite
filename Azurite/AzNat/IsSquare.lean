/-
  Perfect-square test for `AzNat`, with a fast quadratic-residue filter.

  Only 44 of the 256 residues mod `256` are squares, so checking the low
  8 bits of the lowest limb against a bitpacked table of squares mod 256
  rejects ~83% of non-squares with two limb operations and one table
  probe.  Survivors fall back to the exact test: compute `⌊√n⌋` (the
  limb-level `sqrtRem`) and compare its square with `n`.

  The table is four inline `UInt64` words (bit `j` of word `w` is set
  iff `64w + j` is a square mod 256); the constants are inlined rather
  than bound globally, and the function is not recursive, so the
  kernel-reduction hazard around global numeric constants does not
  arise.  Correctness — `isSquare n = true ↔ IsSquare n.toNat` — is
  `Azurite.AzNat.isSquare_eq_true_iff` in
  `Azurite/AzNat/Equiv/IsSquare.lean`.
-/
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Square
import Azurite.AzNat.ParseBase

namespace Azurite

namespace AzNat

/-- Is the byte `b` (assumed `< 256`) a square modulo `256`?  One probe
into a bitpacked table of the 44 square residues. -/
def squareResidueTest (b : UInt64) : Bool :=
  let word : UInt64 :=
    if b < 64 then 0x0202021202030213
    else if b < 128 then 0x0202021202020213
    else if b < 192 then 0x0202021202030212
    else 0x0202021202020212
  (word >>> (b &&& 63)) &&& 1 == 1

/-- **Perfect-square test**: reject fast unless the low byte is a square
mod 256; otherwise compare `⌊√n⌋²` with `n` (via the fast three-way `square`). -/
def isSquare (n : AzNat) : Bool :=
  let b : UInt64 := if _ : n.limbs.size > 0 then n.limbs[0] &&& 255 else 0
  if squareResidueTest b then
    square (sqrt n) == n
  else false

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def parse' (s : String) : AzNat := (AzNat.parse s).get!

#guard isSquare (parse' "0") == true
#guard isSquare (parse' "1") == true
#guard isSquare (parse' "4") == true
#guard isSquare (parse' "144") == true
#guard isSquare (parse' "2") == false
#guard isSquare (parse' "3") == false
#guard isSquare (parse' "5") == false

-- residues that PASS the mod-256 filter but fail the exact fallback
#guard isSquare (parse' "17") == false
#guard isSquare (parse' "257") == false

-- multi-limb: 10²⁴ = (10¹²)², and its neighbors
#guard isSquare (parse' "1000000000000000000000000") == true
#guard isSquare (parse' "1000000000000000000000001") == false
#guard isSquare (parse' "999999999999999999999999") == false

-- a 40-digit square: (12345678901234567890)²
#guard isSquare (parse' "152415787532388367501905199875019052100") == true
#guard isSquare (parse' "152415787532388367501905199875019052101") == false

end Tests
