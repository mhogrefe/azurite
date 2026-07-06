/-
  Multivariate polynomial gcd over `AzInt` (`ℤ[x_0, …, x_{n-1}]`), via full
  descent to the nested univariate tower.

  ## Architecture

  `AzMvPolynomial n AzInt ord` is converted **once** to the nested tower

    `NestedPoly n = AzPolynomial (AzPolynomial (… AzInt))`   (`n` levels),

  where the recursive `NormalizedGcd` machinery
  (`Azurite/AzPolynomial/GcdTower.lean`) and the tower `ExactDiv` instances
  apply level-by-level; the normalized gcd is computed there and converted
  back. Each descent step peels off the **first** variable: `x_0` becomes
  the *outer* univariate indeterminate and `x_{k+1} ↦ x_k` in the
  coefficients — exactly the orientation of `AzMvPolynomial.finSuccEquiv`
  and of Mathlib's `MvPolynomial.finSuccEquiv`, so the Phase-3 correctness
  proof can transport along the existing
  `Equiv/FinSuccEquiv`/`MvPolynomial.finSuccEquiv` bridges. Reading the
  tower inside-out, `NestedPoly n = ℤ[x_{n-1}][x_{n-2}]…[x_0]`. The `n = 0`
  collapse is the constant-extraction of `finZeroAlgEquiv` (forward:
  `eval₂ (RingHom.id) Fin.elim0`; back: `C`).

  Because typeclass resolution cannot recurse over a `ℕ` index by itself,
  the tower carrier is packaged as a bundled structure `GcdRing` (carrier +
  `CommRing`/`DecidableEq`/`IsDomain`/`ExactDiv`/`NormalizedGcd`), built by
  recursion (`intTower`), with the fields registered as instances.

  ## Canonical form

  `AzMvPolynomial.gcd P Q` returns the gcd normalized per the convention of
  `Azurite/Algorithm/NormalizedGcd.lean`: content = normalized gcd of
  contents, and the leading coefficient of the nested representation —
  i.e. the iterated leading coefficient with respect to `x_0`, then `x_1`,
  … — is positive. In particular `gcd P 0` is the normalized `P` and
  `gcd 0 0 = 0`.
-/
import Azurite.AzMvPolynomial.Derivative
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.FinSuccEquiv
import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzPolynomial.GcdTower

namespace Azurite

/-- A carrier bundled with every instance the nested-tower gcd needs. The
    fields are registered as instances, so `NestedPoly n` below picks them
    up by projection. -/
structure GcdRing where
  /-- The carrier type of this tower level. -/
  carrier : Type
  [commRing : CommRing carrier]
  [decEq : DecidableEq carrier]
  [isDomain : IsDomain carrier]
  [exactDiv : Azurite.ExactDiv carrier]
  [normalizedGcd : NormalizedGcd carrier]

attribute [instance] GcdRing.commRing GcdRing.decEq GcdRing.isDomain
  GcdRing.exactDiv GcdRing.normalizedGcd

/-- One tower step: adjoin one (outer) polynomial variable. All five
    instance fields are inherited from the coefficient level by the
    `AzPolynomial` instance chain. -/
def GcdRing.step (S : GcdRing) : GcdRing :=
  { carrier := AzPolynomial S.carrier
    commRing := inferInstance
    decEq := inferInstance
    isDomain := inferInstance
    exactDiv := inferInstance
    normalizedGcd := inferInstance }

/-- The `AzInt`-based nested polynomial tower: `ℤ`, `ℤ[x]`, `ℤ[x][T]`, … -/
def intTower : ℕ → GcdRing
  | 0 =>
    { carrier := AzInt
      commRing := inferInstance
      decEq := inferInstance
      isDomain := inferInstance
      exactDiv := inferInstance
      normalizedGcd := inferInstance }
  | n + 1 => (intTower n).step

/-- The `n`-level nested tower carrier,
    `AzPolynomial (AzPolynomial (… AzInt))` — inside-out,
    `ℤ[x_{n-1}][x_{n-2}]…[x_0]` (variable `x_0` outermost). -/
abbrev NestedPoly (n : ℕ) : Type := (intTower n).carrier

/-- Definitional repackaging: view an `(n+1)`-level nested polynomial as a
    univariate polynomial over the `n`-level carrier. `NestedPoly (n+1)`
    *is* `AzPolynomial (NestedPoly n)` definitionally, but instance search
    does not unfold the tower, so statements mixing the two spellings (e.g.
    products of a `C`-embedded scalar with a nested polynomial) need this
    seam made explicit. -/
def nestedDown {n : ℕ} (q : NestedPoly (n + 1)) :
    AzPolynomial (NestedPoly n) := q

namespace AzMvPolynomial

variable {ord : MonomialOrder}

/-- Descend a flat `n`-variable polynomial over `AzInt` to the nested tower
    `NestedPoly n`, peeling the first variable at each step
    (`finSuccEquiv` orientation: `x_0` outermost). -/
def toNested : (n : ℕ) → AzMvPolynomial n AzInt ord → NestedPoly n
  | 0, p => p.eval₂ (RingHom.id AzInt) Fin.elim0
  | n + 1, p =>
    (AzPolynomial.normalize ((finSuccEquiv p).coeffs.map (toNested n)) :
      AzPolynomial (NestedPoly n))

/-- Ascend from the nested tower back to the flat `n`-variable polynomial
    (inverse orientation of `toNested`: the outer indeterminate becomes
    `x_0`, coefficient variables shift up by one). -/
def ofNested : (n : ℕ) → NestedPoly n → AzMvPolynomial n AzInt ord
  | 0, a => AzMvPolynomial.C a
  | n + 1, q =>
    finSuccEquivSymm
      (AzPolynomial.normalize
        ((q : AzPolynomial (NestedPoly n)).coeffs.map (ofNested n)))

/-- **Multivariate normalized gcd over `AzInt`**: descend both inputs to
    the nested univariate tower once, take the recursive normalized gcd
    there (`NormalizedGcd (NestedPoly n)`, i.e. `ngcdPoly` at every level
    over the `AzInt` base), and ascend back. Canonical form: see the module
    docstring. -/
def gcd {n : ℕ} (P Q : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n AzInt ord :=
  ofNested n (NormalizedGcd.ngcd (toNested n P) (toNested n Q))

/-- **The normalized representative** of the associate class of `P`
(canonical form: iterated leading coefficient positive — see the module
docstring). `gcd P 0 = normalized P` and `gcd P P = normalized P`
(`Equiv/Gcd`). -/
def normalized {n : ℕ} (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n AzInt ord :=
  ofNested n (NormalizedGcd.norm (toNested n P))

/-- **Content with respect to the first variable** `x_0`: the normalized
gcd (in `ℤ[x_1, …, x_n]`, i.e. as an `n`-variable polynomial with the
variables *shifted down by one*) of the coefficients of `P` viewed as a
univariate polynomial in `x_0` — the `finSuccEquiv` orientation, matching
`toNested`. The content of `0` is `0`; the content is always normalized. -/
def content {n : ℕ} (P : AzMvPolynomial (n + 1) AzInt ord) :
    AzMvPolynomial n AzInt ord :=
  ofNested n (Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P)))

/-- **Primitive part with respect to the first variable** `x_0`: `P`
divided (exactly) by its content — the *sign-keeping* convention of
Mathlib's `Polynomial.primPart` and BPR's `pp(P)`, so that
`C(content P) · primitivePart P = P` holds exactly (`Equiv/Gcd`,
`toNested_content_mul_primitivePart`). Unlike Mathlib (where
`primPart 0 = 1`), `primitivePart 0 = 0`. -/
def primitivePart {n : ℕ} (P : AzMvPolynomial (n + 1) AzInt ord) :
    AzMvPolynomial (n + 1) AzInt ord :=
  ofNested (n + 1)
    (Azurite.AzPolynomial.divByRingElt
      (Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P)))
      (nestedDown (toNested (n + 1) P)))

/-- **Primitivity test** (with respect to the first variable): whether the
content is `1`. Since the content is normalized, this is equivalent to the
content being a unit — i.e. `Polynomial.IsPrimitive` of the represented
nested polynomial (`Equiv/Gcd`, `isPrimitive_iff`). -/
def isPrimitive {n : ℕ} (P : AzMvPolynomial (n + 1) AzInt ord) : Bool :=
  content P == 1

/-- **Coprimality test** over the fraction field `ℚ(x_0, …, x_{n-1})`
(i.e. after clearing the integer content): the normalized gcd is a
*nonzero constant*, so `P` and `Q` share no common factor of positive
total degree. This is the faithful multivariate analogue of the univariate
`AzPolynomial.coprime` — lifting a univariate polynomial does not affect it
(`Equiv/Gcd`, `coprime_toAzMvPolynomial`) — and, like the univariate
test, it is exactly what squarefreeness requires. In particular
`coprime (2x) (2) = true` and `coprime (2x) (2y) = true`: the shared
content `2` is a unit over `ℚ`. (Whether the contents themselves are
coprime is the separate concern of `content` / `isPrimitive`.) The nonzero
guard makes `coprime 0 0 = false`. Decides that `gcd P Q` becomes a **unit**
over `ℚ[x⃗]` (`Equiv/Gcd`, `coprime_iff`) — the content-cleared /
fraction-field coprimality (equivalent to `IsRelPrime` of the `ℚ[x⃗]`
images, whose easy direction is `coprime_of_isRelPrime`). -/
def coprime {n : ℕ} (P Q : AzMvPolynomial n AzInt ord) : Bool :=
  gcd P Q != 0 && (gcd P Q).totalDegree == 0

/-- **Gcd and gcd-free part** (the univariate `GcdImpl.gcdGcdFreePart`
convention): the pair `(g, P / g)` where `g = gcd P Q` is the normalized
gcd and the second component is the exact quotient of `P` by `g` — the
*canonical* gcd-free part, the single cofactor of `P` by the gcd (`0` when
`g = 0`, i.e. when `P = Q = 0`). Satisfies
`g · (P/g)-image = P-image` unconditionally (`Equiv/Gcd`,
`gcdGcdFreePart_spec`). -/
def gcdGcdFreePart {n : ℕ} (P Q : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n AzInt ord × AzMvPolynomial n AzInt ord :=
  let g := gcd P Q
  (g, if g = 0 then 0 else Azurite.ExactDiv.exactDiv P g)

/-- **The gradient gcd**: the normalized gcd of `P` together with *all* its
partial derivatives `∂P/∂x_j` (`j : Fin n`) — computed by folding
`AzMvPolynomial.gcd` over `P` and the whole gradient. The full gradient is
essential: a single partial misses squares in the other variables (e.g.
`∂(x₁²)/∂x₀ = 0`). Named so the squarefreeness spec can refer to it. -/
def squarefreeGradientGcd {n : ℕ} (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n AzInt ord :=
  (List.finRange n).foldl
    (fun acc j => AzMvPolynomial.gcd acc (AzMvPolynomial.pderivGeneral j P)) P

/-- **Squarefreeness test** (fraction-field / characteristic-`0` notion,
consistent with `coprime`): `P` is squarefree iff the gcd of `P` with its
whole gradient is a **nonzero constant**, i.e. `P` shares no factor of
positive total degree with any partial derivative. For `n = 1` this is
`gcd(P, ∂₀P)` nonzero-constant (the univariate `AzPolynomial.isSquarefree`);
for `n = 0` it is `P ≠ 0 ∧ totalDegree = 0`. Like `coprime`, the integer
content is ignored (it is a unit over `ℚ`): `4·x` is squarefree. The zero
polynomial is not squarefree. -/
def isSquarefree {n : ℕ} (P : AzMvPolynomial n AzInt ord) : Bool :=
  let g := squarefreeGradientGcd P
  g != 0 && (g.totalDegree == 0)

end AzMvPolynomial

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance fact1Le26 : Fact (1 ≤ 26) := ⟨by omega⟩
private instance fact2Le26 : Fact (2 ≤ 26) := ⟨by omega⟩
private instance fact3Le26 : Fact (3 ≤ 26) := ⟨by omega⟩

/-- Parse a 1-variable (`x`) integer polynomial. -/
private def p1 (s : String) : AzMvPolynomial 1 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 1) s).getD 0
/-- Parse a 2-variable (`x`, `y`) integer polynomial. -/
private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 2) s).getD 0
/-- Parse a 3-variable (`x`, `y`, `z`) integer polynomial. -/
private def p3 (s : String) : AzMvPolynomial 3 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 3) s).getD 0

/-- Render the gcd of two parsed 2-variable polynomials. -/
private def g2 (p q : String) : String :=
  (AzMvPolynomial.gcd (p2 p) (p2 q)).toStrWith (XyzVar 2)

-- gcd((x−y)(x+y), (x+y)²) = x+y (equal x-degrees: pre-step path)
#guard g2 "x^2-y^2" "x^2+2*x*y+y^2" == "x+y"
-- monomials with content: gcd(2xy, 4x²) = 2x
#guard g2 "2*x*y" "4*x^2" == "2*x"
-- content-only gcd (no common variable part): gcd(6x, 4y) = 2
#guard g2 "6*x" "4*y" == "2"
-- coprime pair: gcd(x+1, y+1) = 1
#guard g2 "x+1" "y+1" == "1"
-- equal inputs: gcd(P, P) = normalized P (content kept)
#guard g2 "2*x+2*y" "2*x+2*y" == "2*x+2*y"
-- sign normalization: gcd(−x−y, x+y) = x+y (positively normalized)
#guard g2 "-x-y" "x+y" == "x+y"
-- content × primitive both nontrivial: gcd(4(x−y)(x+y), 6(x+y)²) = 2(x+y)
#guard g2 "4*x^2-4*y^2" "6*x^2+12*x*y+6*y^2" == "2*x+2*y"
-- equal x-degrees with non-proportional leading coefficients
#guard g2 "x^2+x*y" "x^2-y^2" == "x+y"
-- gcd P 0 = normalized P; gcd 0 0 = 0
#guard g2 "-2*x-4*y" "0" == "2*x+4*y"
#guard g2 "0" "0" == "0"
-- three variables: gcd((x+y+z)(x−z), (x+y+z)(y+z)) = x+y+z
#guard (AzMvPolynomial.gcd (p3 "x^2+x*y-y*z-z^2")
        (p3 "x*y+x*z+y^2+2*y*z+z^2")).toStrWith (XyzVar 3) == "x+y+z"
-- one variable: agrees with the univariate normalized gcd
#guard (AzMvPolynomial.gcd (p1 "x^2-1") (p1 "x^2+2*x+1")).toStrWith (XyzVar 1)
        == "x+1"
-- zero variables: the `AzInt` collapse
#guard AzMvPolynomial.gcd
        (AzMvPolynomial.C (-6 : AzInt) : AzMvPolynomial 0 AzInt .Degrevlex)
        (AzMvPolynomial.C (4 : AzInt))
        == AzMvPolynomial.C (2 : AzInt)
-- boundary conversions round-trip
#guard AzMvPolynomial.ofNested 2 (AzMvPolynomial.toNested 2
        (p2 "3*x^2*y-2*x+5")) == p2 "3*x^2*y-2*x+5"
#guard AzMvPolynomial.ofNested 3 (AzMvPolynomial.toNested 3
        (p3 "x*y*z-7*z^3+y")) == p3 "x*y*z-7*z^3+y"

/-! Normalized representative; gcd symmetry sanity. -/

#guard (AzMvPolynomial.normalized (p2 "-2*x-4*y")).toStrWith (XyzVar 2)
        == "2*x+4*y"
#guard (AzMvPolynomial.normalized (p2 "0")).toStrWith (XyzVar 2) == "0"
#guard AzMvPolynomial.gcd (p2 "2*x*y") (p2 "4*x^2")
        == AzMvPolynomial.gcd (p2 "4*x^2") (p2 "2*x*y")

/-! Content and primitive part (with respect to `x`; the content's
variables shift down, so the old `y` prints as `x` via `XyzVar 1`). -/

-- cont(6x² + 4xy) = 2, pp = 3x² + 2xy
#guard (AzMvPolynomial.content (p2 "6*x^2+4*x*y")).toStrWith (XyzVar 1) == "2"
#guard (AzMvPolynomial.primitivePart (p2 "6*x^2+4*x*y")).toStrWith (XyzVar 2)
        == "3*x^2+2*x*y"
-- polynomial content: cont(2xy + 4y²) = 2y (prints as `2*x` after the shift)
#guard (AzMvPolynomial.content (p2 "2*x*y+4*y^2")).toStrWith (XyzVar 1)
        == "2*x"
#guard (AzMvPolynomial.primitivePart (p2 "2*x*y+4*y^2")).toStrWith (XyzVar 2)
        == "x+2*y"
-- sign-keeping primitive part: cont(−2x − 4y) = 2, pp = −x − 2y
#guard (AzMvPolynomial.content (p2 "-2*x-4*y")).toStrWith (XyzVar 1) == "2"
#guard (AzMvPolynomial.primitivePart (p2 "-2*x-4*y")).toStrWith (XyzVar 2)
        == "-x-2*y"
-- constants and zero
#guard (AzMvPolynomial.content (p2 "5")).toStrWith (XyzVar 1) == "5"
#guard (AzMvPolynomial.content (p2 "0")).toStrWith (XyzVar 1) == "0"
#guard (AzMvPolynomial.primitivePart (p2 "0")).toStrWith (XyzVar 2) == "0"

/-! Primitivity. -/

#guard AzMvPolynomial.isPrimitive (p2 "3*x+2*y") == true
#guard AzMvPolynomial.isPrimitive (p2 "6*x+4*y") == false      -- content 2
#guard AzMvPolynomial.isPrimitive (p2 "-x-y") == true          -- content 1
#guard AzMvPolynomial.isPrimitive (p2 "0") == false

/-! Coprimality (fraction-field sense: shared content is a unit over ℚ). -/

#guard AzMvPolynomial.coprime (p2 "x+1") (p2 "y+1") == true
#guard AzMvPolynomial.coprime (p2 "2*x") (p2 "2*y") == true    -- content 2 is a unit over ℚ
#guard AzMvPolynomial.coprime (p2 "2*x") (p2 "2") == true
#guard AzMvPolynomial.coprime (p2 "x*y") (p2 "x+y") == true
-- a shared factor of positive degree still makes them non-coprime
#guard AzMvPolynomial.coprime (p2 "x^2-y^2") (p2 "x^2+2*x*y+y^2") == false
#guard AzMvPolynomial.coprime (p2 "x*y") (p2 "x") == false
-- zero handling matches the univariate test
#guard AzMvPolynomial.coprime (p2 "0") (p2 "5") == true
#guard AzMvPolynomial.coprime (p2 "0") (p2 "x") == false
#guard AzMvPolynomial.coprime (p2 "0") (p2 "0") == false

/-! Gcd and gcd-free part: the canonical pair `(g, P/g)`. -/

#guard (let (g, f) := AzMvPolynomial.gcdGcdFreePart
          (p2 "x^2-y^2") (p2 "x^2+2*x*y+y^2");
        g.toStrWith (XyzVar 2) == "x+y" && f.toStrWith (XyzVar 2) == "x-y")
-- content-scaled: the free part keeps `P`'s remaining content and sign
#guard (let (g, f) := AzMvPolynomial.gcdGcdFreePart
          (p2 "4*x^2-4*y^2") (p2 "6*x^2+12*x*y+6*y^2");
        g.toStrWith (XyzVar 2) == "2*x+2*y"
          && f.toStrWith (XyzVar 2) == "2*x-2*y")
-- gcd P 0 = normalized P, free part carries the unit: (−2x)/(2x) = −1
#guard (let (g, f) := AzMvPolynomial.gcdGcdFreePart (p2 "-2*x") (p2 "0");
        g.toStrWith (XyzVar 2) == "2*x" && f.toStrWith (XyzVar 2) == "-1")
#guard (let (g, f) := AzMvPolynomial.gcdGcdFreePart (p2 "0") (p2 "0");
        g.toStrWith (XyzVar 2) == "0" && f.toStrWith (XyzVar 2) == "0")

/-! Squarefreeness (gradient-gcd is a nonzero constant; content ignored). -/

#guard AzMvPolynomial.isSquarefree (p2 "x^2-y^2") == true
#guard AzMvPolynomial.isSquarefree (p2 "x*y+1") == true
#guard AzMvPolynomial.isSquarefree (p2 "5") == true              -- nonzero constant
#guard AzMvPolynomial.isSquarefree (p2 "4*x") == true            -- content 4 is a unit over ℚ
#guard AzMvPolynomial.isSquarefree (p2 "x^2") == false           -- perfect square
#guard AzMvPolynomial.isSquarefree (p2 "x^2+2*x*y+y^2") == false -- (x+y)²
#guard AzMvPolynomial.isSquarefree (p2 "x^2*y") == false         -- square factor x²
#guard AzMvPolynomial.isSquarefree (p2 "0") == false
-- n = 1 agrees with the univariate test
#guard AzMvPolynomial.isSquarefree (p1 "x^2-1") == true
#guard AzMvPolynomial.isSquarefree (p1 "x^2-2*x+1") == false     -- (x-1)²

/-! Lifting a univariate polynomial into `AzMvPolynomial` (via variable `x`)
preserves coprimality (`coprime_toAzMvPolynomial`). -/

private def up (s : String) : AzPolynomial AzInt :=
  (AzPolynomial.parseAzPolynomial s).getD 0
private def lift2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (up s).toAzMvPolynomial (0 : Fin 2) .Degrevlex

-- coprime univariate ⟺ coprime lifts, on the same inputs
#guard AzMvPolynomial.coprime (lift2 "x^2+1") (lift2 "x-1")
        == AzPolynomial.coprime (up "x^2+1") (up "x-1")           -- true = true
#guard AzMvPolynomial.coprime (lift2 "x^2-1") (lift2 "x-1")
        == AzPolynomial.coprime (up "x^2-1") (up "x-1")           -- false = false (share x−1)
#guard AzMvPolynomial.coprime (lift2 "2*x") (lift2 "2")
        == AzPolynomial.coprime (up "2*x") (up "2")               -- true = true (content cleared)
#guard AzMvPolynomial.coprime (lift2 "6*x^2-6") (lift2 "4*x-4")
        == AzPolynomial.coprime (up "6*x^2-6") (up "4*x-4")       -- false = false (share x−1)
-- and the concrete values
#guard AzMvPolynomial.coprime (lift2 "x^2+1") (lift2 "x-1") == true
#guard AzMvPolynomial.coprime (lift2 "x^2-1") (lift2 "x-1") == false

end Tests

end Azurite
