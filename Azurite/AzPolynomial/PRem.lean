import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.SMul
import Azurite.AzPolynomial.MulXPow
import Azurite.AzPolynomial.Parse

/-!
# Signed Pseudo-Remainder `PRem(P, Q)` for Univariate Polynomials

This module implements the **signed pseudo-remainder** from Basu, Pollack,
Roy, *Algorithms in Real Algebraic Geometry* (2006), Section 1.3.

Given polynomials `P, Q ∈ D[X]` over a commutative ring `D` with `Q ≠ 0`,
the pseudo-remainder `pRem P Q` is the remainder `R ∈ D[X]` of the
Euclidean division of `b_q^d · P` by `Q`, where `b_q = Q.leadingCoeff` and
`d = pRemExp P Q` is the smallest even natural number ≥ `deg P - deg Q + 1`
(with `d = 0` when `deg P < deg Q`). It satisfies
  `b_q^d · P = A · Q + R`
for some `A ∈ D[X]` and with `deg R < deg Q`.

The key property is that the computation stays entirely inside `D[X]`:
no fraction field is required. This is why `pRem` is useful over rings
that are not fields — in particular `ℤ` and `AzMvPolynomial σ ℤ ord`.

## Algorithm

Classical pseudo-division (Knuth TAOCP Vol. 2, Algorithm R). At each
reduction step we maintain the invariant that after `i` iterations the
running remainder `R_i` satisfies `b_q^i · P = A_i · Q + R_i`, by
performing:

  `R_{i+1} := b_q · R_i - lead(R_i) · X^{deg R_i - deg Q} · Q`

when `deg R_i ≥ deg Q`, and simply `R_{i+1} := b_q · R_i` otherwise. After
`p - q + 1` iterations (where `p = deg P`, `q = deg Q`) the remainder
has `deg R < deg Q`. A final multiplication by `b_q` is applied when
`p - q + 1` is odd, to reach the smallest even exponent `d ≥ p - q + 1`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- The exponent `d` used to scale `P` in the signed pseudo-remainder:
    the smallest even natural number `≥ natDegree P - natDegree Q + 1`,
    with the convention that `d = 0` when `natDegree P < natDegree Q`. -/
def pRemExp (P Q : AzPolynomial R) : ℕ :=
  let k := if P.coeffs.size < Q.coeffs.size then 0
           else P.coeffs.size - Q.coeffs.size + 1
  k + k % 2

/-- One reduction step in the pseudo-division loop. Given the running
    remainder `rem`, the natural degree `q` of `Q`, the leading coefficient
    `b` of `Q`, and `Q` itself, either subtract the leading term of `rem`
    (scaled through by `b` to stay in `D[X]`) or simply scale `rem` by `b`
    when it already has degree below `q`. -/
def pRemStep (q : ℕ) (b : R) (Q : AzPolynomial R)
    (rem : AzPolynomial R) : AzPolynomial R :=
  if rem.coeffs.size > q then
    let t := rem.leadingCoeff
    let e := rem.coeffs.size - 1 - q
    b • rem - mulXPow e (t • Q)
  else
    b • rem

/-- **Signed pseudo-remainder** `pRem P Q`: returns `R : AzPolynomial R`
    such that `Q.leadingCoeff ^ (pRemExp P Q) · P = A · Q + R` for some
    `A`, with `deg R < deg Q` (when `Q ≠ 0`).

    When `Q = 0` we return `P` by convention (the pseudo-remainder is
    undefined in this case). When `deg P < deg Q`, `pRemExp P Q = 0` so
    the identity is `P = 0 · Q + P` and we return `P` directly.

    Works over any commutative ring; no divisions are performed. -/
def pRem (P Q : AzPolynomial R) : AzPolynomial R :=
  if Q.coeffs.size = 0 then P  -- Q = 0: undefined, return P
  else if P.coeffs.size < Q.coeffs.size then P  -- deg P < deg Q: d = 0
  else
    let q := Q.coeffs.size - 1
    let b := Q.leadingCoeff
    let numSteps := P.coeffs.size - Q.coeffs.size + 1
    let R := (List.range numSteps).foldl (fun rem _ => pRemStep q b Q rem) P
    if numSteps % 2 = 1 then b • R else R

/-! ### Tests over `ℤ` -/

-- `(x^2 + 1)` mod `(x + 1)`:
--   Euclidean division in ℚ gives remainder 2.
--   d = pRemExp = smallestEvenGe(2 - 1 + 1) = smallestEvenGe(2) = 2.
--   b = 1, so b^d * P = P, and the remainder is the same as the normal one: 2.
#guard pRem (parseAzPolynomial (R := ℤ) "x^2+1").get!
             (parseAzPolynomial (R := ℤ) "x+1").get!
  == (parseAzPolynomial (R := ℤ) "2").get!

-- `(2*x^2 + 3*x + 1)` mod `(2*x + 1)`:
--   d = smallestEvenGe(2 - 1 + 1) = 2. b = 2. b^d * P = 4 * P.
--   4*P = (4x + 4)*(2x + 1), so remainder = 0.
#guard pRem (parseAzPolynomial (R := ℤ) "2*x^2+3*x+1").get!
             (parseAzPolynomial (R := ℤ) "2*x+1").get!
  == (0 : AzPolynomial ℤ)

-- `(x^3 + 1)` mod `(2*x^2 + 3*x + 1)`:
--   d = smallestEvenGe(3 - 2 + 1) = 2. b = 2.
--   4*(x^3 + 1) = (2x - 3)*(2x^2 + 3x + 1) + (7x + 7).
#guard pRem (parseAzPolynomial (R := ℤ) "x^3+1").get!
             (parseAzPolynomial (R := ℤ) "2*x^2+3*x+1").get!
  == (parseAzPolynomial (R := ℤ) "7*x+7").get!

-- deg P < deg Q ⇒ pRem = P (with d = 0).
#guard pRem (parseAzPolynomial (R := ℤ) "x+1").get!
             (parseAzPolynomial (R := ℤ) "x^2+1").get!
  == (parseAzPolynomial (R := ℤ) "x+1").get!

-- P = 0: pseudo-remainder is 0.
#guard pRem (0 : AzPolynomial ℤ) (parseAzPolynomial (R := ℤ) "x+1").get!
  == (0 : AzPolynomial ℤ)

-- Q = 0: by convention return P.
#guard pRem (parseAzPolynomial (R := ℤ) "x+1").get! (0 : AzPolynomial ℤ)
  == (parseAzPolynomial (R := ℤ) "x+1").get!

-- Exponent computations:
#guard pRemExp (parseAzPolynomial (R := ℤ) "x^3+1").get!
               (parseAzPolynomial (R := ℤ) "x+1").get! == 4  -- smallestEvenGe 3 = 4
#guard pRemExp (parseAzPolynomial (R := ℤ) "x^2+1").get!
               (parseAzPolynomial (R := ℤ) "x+1").get! == 2  -- smallestEvenGe 2 = 2
#guard pRemExp (parseAzPolynomial (R := ℤ) "x").get!
               (parseAzPolynomial (R := ℤ) "x^2+1").get! == 0  -- deg P < deg Q

end Azurite.AzPolynomial
