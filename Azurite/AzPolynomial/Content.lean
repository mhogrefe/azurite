import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzNat.Gcd
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzNat.ParseBase

/-!
# Content of an integer polynomial

BPR §10.1: for `P ∈ ℤ[X]`, `cont(P)` is the content of `P`, the greatest
common divisor of its coefficients. (The abstract notion exists over any GCD
domain — Mathlib's `Polynomial.content` — and the correctness statement is
against it; computably, `AzNat` has a binary gcd, so the `AzInt` content is
computed magnitude-wise.)

`content p` is a single `O(n)` fold of `AzNat.gcd` over the coefficient
magnitudes; the result is the canonical nonnegative representative, as an
`AzNat` (matching Mathlib's normalized content over `ℤ`). The content of the
zero polynomial is `0`.

Correctness (`content_toPoly`) is in `Azurite.AzPolynomial.Equiv.Content`.
-/

namespace Azurite.AzPolynomial

/-- **Content** of an integer polynomial: the (nonnegative) gcd of the
coefficients, `cont(P)` of BPR §10.1. -/
def content (p : AzPolynomial AzInt) : AzNat :=
  p.coeffs.foldl (fun acc a => AzNat.gcd acc a.abs) 0

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!
private def nn (s : String) : AzNat := (AzNat.parse s).get!

-- cont(6x² − 4x + 10) = 2
#guard content (pp "6*x^2-4*x+10") == nn "2"
-- cont(3x² + 5) = 1 (coprime coefficients)
#guard content (pp "3*x^2+5") == nn "1"
-- cont(−12x³ − 18x) = 6 (sign-independent)
#guard content (pp "-12*x^3-18*x") == nn "6"
-- constant polynomial: cont(−7) = 7
#guard content (pp "-7") == nn "7"
-- zero polynomial: cont(0) = 0
#guard content (pp "0") == nn "0"
-- larger-than-word-size coefficients
#guard content (pp "36893488147419103232*x-55340232221128654848") == nn "18446744073709551616"

end Tests

end Azurite.AzPolynomial
