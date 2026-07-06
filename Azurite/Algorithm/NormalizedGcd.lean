/-
  Typeclass `NormalizedGcd D` for types with a computable gcd returning a
  *canonical* (normalized) representative of the associate class.

  ## The canonical-form convention

  `ngcd a b` is intended to be the gcd of `a` and `b` normalized exactly as
  Mathlib's `NormalizedGCDMonoid` gcd:

  * over `AzInt` (`ℤ`), the normalized representative of an associate class
    is the **nonnegative** one;
  * over `AzPolynomial R` (with `R` itself carrying a `NormalizedGcd`), a
    polynomial is normalized iff its **leading coefficient is normalized in
    `R`** (this matches Mathlib's `Polynomial.normUnit`, which is
    `C (normUnit leadingCoeff)`). Unfolding the recursion through a nested
    tower `AzPolynomial (AzPolynomial (… AzInt))`, a nested polynomial is
    normalized iff the innermost leading coefficient — the `AzInt`
    coefficient reached by repeatedly taking leading coefficients — is
    positive.

  Phase-2 correctness (see `Azurite/AzPolynomial/GcdTower.lean` for the
  polynomial-level recursion) will prove instances against Mathlib's
  `gcd`/`normalize`; the intended laws are:

  * `ngcd a b` is a gcd of `a` and `b`, and is normalized;
  * `ngcd a 0 = ngcd 0 a = norm a` (so `norm` below is *the* normalization);
  * `norm` is multiplicative on nonzero elements (Mathlib: `normUnit` is a
    `MonoidHom`), so normalized elements are closed under multiplication
    and under exact division by normalized divisors;
  * `ngcd 0 0 = 0`.

  Only the operation itself is bundled in this phase — no lawfulness field
  yet, mirroring how Phase 1 of the ℤ-case shipped `gcdNormalizedInt`
  before `Equiv/GcdInt` proved it.
-/
import Azurite.Algorithm.ExactDiv

namespace Azurite

/-- `NormalizedGcd D` bundles a computable **normalized** gcd: `ngcd a b` is
    a gcd of `a` and `b`, canonicalized to the normalized representative of
    its associate class (nonnegative over `AzInt`; recursively-normalized
    leading coefficient over `AzPolynomial`). See the module docstring for
    the full canonical-form convention. -/
class NormalizedGcd (D : Type _) [CommRing D] [DecidableEq D] where
  /-- The normalized gcd (canonical associate-class representative). -/
  ngcd : D → D → D

namespace NormalizedGcd

variable {D : Type _} [CommRing D] [DecidableEq D] [NormalizedGcd D]

/-- The canonical (normalized) representative of the associate class of
    `a`, computed as `ngcd a 0`. Over `AzInt` this is `|a|`; over a
    polynomial ring it is `a` divided by the unit part of its leading
    coefficient. -/
def norm (a : D) : D := ngcd a 0

/-- The unit factor of `a` relative to its normalization: the unit `u` with
    `a = u * norm a`, computed by exact division. Unspecified junk at
    `a = 0` — callers must guard. -/
def unitPart [Azurite.ExactDiv D] (a : D) : D :=
  Azurite.ExactDiv.exactDiv a (norm a)

end NormalizedGcd

end Azurite
