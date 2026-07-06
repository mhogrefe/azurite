/-
  Normalized polynomial gcd, recursively over a nested coefficient tower.

  This generalizes the SHAPE of `gcdNormalizedInt` (`AzPolynomial/Gcd.lean`,
  the `ℤ`-coefficient case) from `AzInt` coefficients to any coefficient
  ring `R` with `[Azurite.ExactDiv R]` and `[Azurite.NormalizedGcd R]`, and
  closes the loop with an instance

    `NormalizedGcd R → NormalizedGcd (AzPolynomial R)`,

  so the whole nested tower `AzPolynomial (AzPolynomial (… AzInt))` gets a
  normalized gcd by typeclass recursion. Together with the existing
  `ExactDiv (AzPolynomial R)` instance (`Equiv/ExactDiv.lean`, over a
  domain) every tower level also has exact division, which is what the
  subresultant machinery (`subresGcd`, `preStep`, `divByRingElt`,
  `exactDivQuoRem`) needs one level down.

  ## Canonical form (the Phase-2 correctness target)

  See `Azurite/Algorithm/NormalizedGcd.lean` for the convention. At the
  polynomial level: `ngcdPoly P Q` is intended to be Mathlib's normalized
  gcd of the represented polynomials, i.e.

    `ngcd(cont P, cont Q) · (primitive gcd, leading coefficient normalized)`

  where the content is the `R`-normalized gcd of the coefficients
  (`contentGen`), the primitive part is extracted by exact scalar division
  (`primNormalized`), and "leading coefficient normalized" recurses through
  the tower (positive innermost `AzInt` leading coefficient). The branch
  structure below is kept **identical** to `gcdNormalizedInt` so that the
  Phase-2 proof can generalize `Equiv/GcdInt` branch-for-branch; on
  `R = AzInt` each generalized building block agrees definitionally-in-value
  with its `ℤ`-specific counterpart:

    `contentGen        ↦ azNatToAzInt ∘ content`
    `leadNormalize     ↦ signNorm`
    `primNormalized    ↦ primPos`
    `contentGcdGen     ↦ contentGcdInt`
    `ngcdPoly          ↦ gcdNormalizedInt`

  (the last agreement is exercised by the guards at the bottom).
-/
import Azurite.Algorithm.NormalizedGcd
import Azurite.AzInt.NormalizedGcd
import Azurite.AzPolynomial.Gcd
import Azurite.AzPolynomial.Equiv.ExactDiv

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]
  [NormalizedGcd R]

/-- **Generalized content**: the `R`-normalized gcd of the coefficients
    (fold of `NormalizedGcd.ngcd`, starting at `0`). Over `AzInt` this is
    `content` (as a nonnegative `AzInt`); the result is always normalized
    in `R`. Content of the zero polynomial is `0`. -/
def contentGen (p : AzPolynomial R) : R :=
  p.coeffs.foldl (fun acc a => NormalizedGcd.ngcd acc a) 0

/-- **Generalized sign normalization** (`signNorm` over `AzInt`): divide
    out the unit part of the leading coefficient, producing the normalized
    representative of the associate class of `p` — Mathlib's
    `normalize p`. -/
def leadNormalize (p : AzPolynomial R) : AzPolynomial R :=
  if p = 0 then 0
  else divByRingElt (NormalizedGcd.unitPart p.leadingCoeff) p

/-- **Generalized primitive-positive part** (`primPos` over `AzInt`): the
    primitive part of `g` with normalized leading coefficient, extracted by
    a single exact scalar division by `content · unitPart(leadingCoeff)`. -/
def primNormalized (g : AzPolynomial R) : AzPolynomial R :=
  if g = 0 then 0
  else divByRingElt (contentGen g * NormalizedGcd.unitPart g.leadingCoeff) g

/-- The normalized gcd of the contents (`contentGcdInt` over `AzInt`). -/
def contentGcdGen (P Q : AzPolynomial R) : R :=
  NormalizedGcd.ngcd (contentGen P) (contentGen Q)

/-- **Normalized polynomial gcd over a `NormalizedGcd` coefficient ring** —
    the tower-generic generalization of `gcdNormalizedInt`, with the same
    branch structure: `gcd(cont P, cont Q)` times the primitive gcd of the
    primitive parts (via the fraction-free subresultant chain `subresGcd`,
    with the `p = q` pre-step), leading coefficient normalized. Total in
    `P, Q` (zero, constant and swapped-degree inputs included). -/
def ngcdPoly (P Q : AzPolynomial R) : AzPolynomial R :=
  if P = 0 then leadNormalize Q
  else if Q = 0 then leadNormalize P
  else if P.natDegree = 0 ∨ Q.natDegree = 0 then
    contentGcdGen P Q • (1 : AzPolynomial R)
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then contentGcdGen P Q • primNormalized P
    else if (preStep P Q).natDegree = 0 then
      contentGcdGen P Q • (1 : AzPolynomial R)
    else contentGcdGen P Q • primNormalized (subresGcd P (preStep P Q))
  else if P.natDegree < Q.natDegree then
    contentGcdGen P Q • primNormalized (subresGcd Q P)
  else contentGcdGen P Q • primNormalized (subresGcd P Q)

/-- The tower step: a normalized gcd on `R` induces one on
    `AzPolynomial R`. Combined with `NormalizedGcd AzInt` this equips every
    level of `AzPolynomial (AzPolynomial (… AzInt))` by typeclass
    recursion. -/
instance instNormalizedGcdAzPolynomial : NormalizedGcd (AzPolynomial R) :=
  ⟨ngcdPoly⟩

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!

/-! ### Level 1: `AzPolynomial AzInt` — `ngcdPoly` must agree with the
`ℤ`-specific `gcdNormalizedInt` (same inputs as `Gcd.lean`'s test suite). -/

private def agreesInt (p q : String) : Bool :=
  ngcdPoly (pp p) (pp q) == gcdNormalizedInt (pp p) (pp q)

#guard agreesInt "x^3+3*x^2-4" "x^3-2*x^2-5*x+6"      -- equal-degree pre-step
#guard agreesInt "2*x^3+6*x^2-8" "x^3-2*x^2-5*x+6"    -- content in one input
#guard agreesInt "2*x^3+6*x^2-8" "2*x^3-4*x^2-10*x+12" -- content in both
#guard agreesInt "2*x+2" "4*x+4"                       -- proportional
#guard agreesInt "-3*x-3" "6"                          -- constant argument
#guard agreesInt "0" "-2*x"                            -- zero + sign
#guard agreesInt "-2*x" "0"
#guard agreesInt "0" "0"
#guard agreesInt "x-1" "x^2-1"                         -- swapped degrees
#guard agreesInt "x^2+1" "x-1"                         -- coprime
-- and the absolute values, for good measure
#guard toChars (ngcdPoly (pp "x^3+3*x^2-4") (pp "x^3-2*x^2-5*x+6")) == "x^2+x-2"
#guard toChars (ngcdPoly (pp "2*x^3+6*x^2-8") (pp "2*x^3-4*x^2-10*x+12"))
        == "2*x^2+2*x-4"
#guard toChars (ngcdPoly (pp "0") (pp "-2*x")) == "2*x"

/-! ### Level 2: `AzPolynomial (AzPolynomial AzInt)` = `ℤ[x][T]`.

`N l` builds the outer polynomial with ascending `ℤ[x]` coefficients parsed
from `l`; the tower `NormalizedGcd`/`ExactDiv` instances resolve by
typeclass recursion. -/

private def N (l : List String) : AzPolynomial (AzPolynomial AzInt) :=
  normalize ((l.map (fun s => pp s)).toArray)

-- (T−x)(T+x) vs (T+x)²: gcd = T+x (equal degrees, pre-step path)
#guard NormalizedGcd.ngcd (N ["-x^2", "0", "1"]) (N ["x^2", "2*x", "1"])
        == N ["x", "1"]
-- content-only gcd: gcd(2x·T, 4x²) = 2x (constant branch)
#guard NormalizedGcd.ngcd (N ["0", "2*x"]) (N ["4*x^2"]) == N ["2*x"]
-- polynomial content: gcd(x·T + x², x·T) = x (pre-step degenerates to a constant)
#guard NormalizedGcd.ngcd (N ["x^2", "x"]) (N ["0", "x"]) == N ["x"]
-- sign normalization through the tower: gcd(−T−x, T+x) = T+x
#guard NormalizedGcd.ngcd (N ["-x", "-1"]) (N ["x", "1"]) == N ["x", "1"]
-- gcd P 0 = normalize P (unit part of the leading ℤ[x]-coefficient divided out)
#guard NormalizedGcd.ngcd (N ["-x", "-2"]) (N []) == N ["x", "2"]
#guard NormalizedGcd.ngcd (N []) (N []) == N []
-- the tower `ExactDiv` (bundled instance, two levels up from `AzInt`):
-- (T²−x²) /ₑ (T+x) = T−x
#guard Azurite.ExactDiv.exactDiv (N ["-x^2", "0", "1"]) (N ["x", "1"])
        == N ["-x", "1"]

end Tests

end Azurite.AzPolynomial
