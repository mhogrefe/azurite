/-
  Examples demonstrating that `AzPolynomial` works over coefficient rings
  that are themselves built by Azurite: `AzPolynomial AzInt` and `AzMatrix AzInt n n`.

  These tests exercise the typeclass machinery: building an
  `AzPolynomial` over either coefficient ring requires `Semiring`,
  `DecidableEq`, and (for arithmetic) the full `Ring`/`CommRing` instance
  on the coefficient type to be **computable**.

  The companion file `MvCoeffExamples.lean` covers the
  `AzMvPolynomial` coefficient case.
-/
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzMatrix.Basic
import Azurite.AzMatrix.Operations
import Azurite.AzMatrix.Mul
import Azurite.AzMatrix.Parse
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzZMod.Instances
import Azurite.AzZMod.Pow
import Azurite.AzZMod.ParsableElement

namespace Azurite.AzPolynomial.NestedCoeffExamples

open Azurite

/-! ## Part 1: `AzPolynomial (AzPolynomial AzInt)`

The outer indeterminate is written `T`; the inner indeterminate is `x`.
Inner coefficients are built via `parseAzPolynomial`. -/

/-- Inner coefficient ring: `AzInt[x]`. -/
abbrev IntPoly := AzPolynomial AzInt

/-- Helper: parse a string as an element of `IntPoly`. -/
private def i (s : String) : IntPoly :=
  (AzPolynomial.parseAzPolynomial (R := AzInt) s).getD 0

/-! ### Constructing values -/

/-- The zero polynomial. -/
private def pz : AzPolynomial IntPoly := 0
#guard pz.coeffs.size == 0

/-- The one polynomial. -/
private def po : AzPolynomial IntPoly := 1
#guard po.coeffs.size == 1
#guard toChars (po.coeff 0) == "1"

/-- A constant polynomial whose coefficient is `x + 1`. -/
private def pc : AzPolynomial IntPoly := AzPolynomial.C (i "x+1")
#guard pc.coeffs.size == 1
#guard toChars (pc.coeff 0) == "x+1"

/-- The polynomial `x * T + (x + 1)` in `AzInt[x][T]`. -/
private def pl : AzPolynomial IntPoly :=
  AzPolynomial.monomial 1 (i "x") + AzPolynomial.C (i "x+1")
#guard pl.coeffs.size == 2
#guard toChars (pl.coeff 0) == "x+1"
#guard toChars (pl.coeff 1) == "x"

/-- The polynomial `x^2 * T^2 + (-x) * T + 1`. -/
private def pq : AzPolynomial IntPoly :=
  AzPolynomial.monomial 2 (i "x^2") + AzPolynomial.monomial 1 (i "-x")
    + AzPolynomial.C (i "1")
#guard pq.coeffs.size == 3
#guard toChars (pq.coeff 0) == "1"
#guard toChars (pq.coeff 1) == "-x"
#guard toChars (pq.coeff 2) == "x^2"

/-! ### Ring operations -/

-- Addition: `(x*T + (x+1)) + ((-x)*T + 1) = (x+2)`
#guard
  toChars ((pl + (AzPolynomial.monomial 1 (i "-x") + AzPolynomial.C (i "1"))).coeff 0)
    == "x+2"

-- Subtraction collapses to zero.
#guard (pl - pl).coeffs.size == 0

-- Negation through subtraction: `0 - C(x) = C(-x)`.
#guard toChars (((0 : AzPolynomial IntPoly) - AzPolynomial.C (i "x")).coeff 0) == "-x"

-- Multiplication: `(T + x) * (T - x) = T^2 - x^2`.
private def pa : AzPolynomial IntPoly :=
  AzPolynomial.monomial 1 (i "1") + AzPolynomial.C (i "x")
private def pb : AzPolynomial IntPoly :=
  AzPolynomial.monomial 1 (i "1") + AzPolynomial.C (i "-x")
private def pab : AzPolynomial IntPoly := pa * pb

#guard pab.coeffs.size == 3
#guard toChars (pab.coeff 0) == "-x^2"
#guard toChars (pab.coeff 1) == "0"
#guard toChars (pab.coeff 2) == "1"

-- The leading coefficient of `pq` is `x^2`.
#guard toChars (pq.leadingCoeff) == "x^2"

-- Squaring `(T + (x+1))` gives `T^2 + 2*(x+1)*T + (x+1)^2`,
-- i.e. `T^2 + (2x+2)*T + (x^2+2x+1)`.
private def pT_plus : AzPolynomial IntPoly :=
  AzPolynomial.monomial 1 (i "1") + AzPolynomial.C (i "x+1")
private def psq : AzPolynomial IntPoly := pT_plus * pT_plus

#guard psq.coeffs.size == 3
#guard toChars (psq.coeff 0) == "x^2+2*x+1"
#guard toChars (psq.coeff 1) == "2*x+2"
#guard toChars (psq.coeff 2) == "1"

-- Power via `^` (exercises the computable `npow`/`Semiring` machinery).
#guard (pT_plus ^ 2) == psq
#guard ((pT_plus : AzPolynomial IntPoly) ^ 0) == 1
#guard ((pT_plus : AzPolynomial IntPoly) ^ 1) == pT_plus

/-! ## Part 2: `AzPolynomial (AzMatrix AzInt 2 2)`

The coefficient ring is the (non-commutative) ring of `2 × 2` integer matrices.
The outer indeterminate is again written `T`. -/

/-- Coefficient ring: `M₂(AzInt)`. -/
abbrev Mat22 := AzMatrix AzInt 2 2

/-- The identity `2 × 2` matrix. -/
private def I2 : Mat22 := 1

/-- A non-trivial integer matrix. -/
private def A : Mat22 := AzMatrix.ofLists [[1, 2], [3, 4]]

/-- Another non-trivial integer matrix. -/
private def B : Mat22 := AzMatrix.ofLists [[0, 1], [-1, 0]]

/-! ### Constructing values -/

private def qz : AzPolynomial Mat22 := 0
#guard qz.coeffs.size == 0

private def qo : AzPolynomial Mat22 := 1
#guard qo.coeffs.size == 1
#guard toString (qo.coeff 0) = "[1, 0; 0, 1]"

/-- The polynomial `A * T + B`. -/
private def ql : AzPolynomial Mat22 :=
  AzPolynomial.monomial 1 A + AzPolynomial.C B
#guard ql.coeffs.size == 2
#guard toString (ql.coeff 0) = "[0, 1; -1, 0]"
#guard toString (ql.coeff 1) = "[1, 2; 3, 4]"

/-! ### Ring operations -/

-- Addition: `(A*T + B) + (A*T + B) = 2A*T + 2B`.
#guard toString ((ql + ql).coeff 0) = "[0, 2; -2, 0]"
#guard toString ((ql + ql).coeff 1) = "[2, 4; 6, 8]"

-- Subtraction collapses to zero.
#guard (ql - ql).coeffs.size == 0

-- `(I*T + A) * (I*T - A) = T^2 - A*T + A*T - A^2 = T^2 - A^2`,
-- because `I` commutes with `A` (and the cross terms cancel).
private def qa : AzPolynomial Mat22 :=
  AzPolynomial.monomial 1 I2 + AzPolynomial.C A
private def qb : AzPolynomial Mat22 :=
  AzPolynomial.monomial 1 I2 + AzPolynomial.C (-A)
private def qab : AzPolynomial Mat22 := qa * qb

#guard qab.coeffs.size == 3
#guard toString (qab.coeff 0) = "[-7, -10; -15, -22]"
#guard toString (qab.coeff 1) = "[0, 0; 0, 0]"
#guard toString (qab.coeff 2) = "[1, 0; 0, 1]"

-- Squaring `(I*T + A)` gives `I*T^2 + 2A*T + A^2`.
private def qsq : AzPolynomial Mat22 := qa * qa
#guard qsq.coeffs.size == 3
#guard toString (qsq.coeff 0) = "[7, 10; 15, 22]"
#guard toString (qsq.coeff 1) = "[2, 4; 6, 8]"
#guard toString (qsq.coeff 2) = "[1, 0; 0, 1]"

-- Power via `^`.
#guard (qa ^ 2) == qsq
#guard ((qa : AzPolynomial Mat22) ^ 0) == 1
#guard ((qa : AzPolynomial Mat22) ^ 1) == qa

-- Non-commutativity of the coefficient ring is visible: `A * B ≠ B * A`.
#guard toString (A * B) ≠ toString (B * A)

-- A polynomial built from `B` (a non-symmetric matrix) multiplied by its negation.
private def qc : AzPolynomial Mat22 :=
  AzPolynomial.monomial 1 B + AzPolynomial.C I2
#guard toString ((qc * qc).coeff 0) = "[1, 0; 0, 1]"
#guard toString ((qc * qc).coeff 2) = "[-1, 0; 0, -1]"

/-! ## Part 3: Constant `AzPolynomial (AzMatrix (ZMod p) 2 2)` raised to a huge power

This mirrors the Fibonacci-matrix test in `AzMatrix/Pow.lean`. By wrapping the
Fibonacci matrix in a *constant* polynomial we keep the outer backing array of
size 1, while the inner exponentiation still has to perform ~60 matrix
multiplications mod `10^9 + 7`. This exercises:

  * the computable `npow` on `AzPolynomial`,
  * the computable `npow` on `AzMatrix (ZMod p) 2 2` — invoked once per outer
    multiplication via `(C a) * (C b) = C (a * b)`,
  * the `DecidableEq` instances on both layers.

If the outer or inner `^` were not the binary-exponentiation version, raising
to `10^18` would not terminate. -/

/-- The Fibonacci matrix `[[1,1],[1,0]]` over `ZMod (10^9 + 7)`. -/
private def fibMat : AzMatrix (AzZMod (AzNat.ofNat 1000000007)) 2 2 :=
  AzMatrix.ofLists [[1, 1], [1, 0]]

/-- The constant polynomial whose unique coefficient is `fibMat`. -/
private def fibMatPoly : AzPolynomial (AzMatrix (AzZMod (AzNat.ofNat 1000000007)) 2 2) :=
  AzPolynomial.C fibMat

-- Constant polynomial → backing array stays size 1 throughout.
#guard (fibMatPoly ^ 1000000000000000000).coeffs.size == 1

-- Same Fibonacci-mod result as the bare-matrix test in `AzMatrix/Pow.lean`.
#guard toString ((fibMatPoly ^ 1000000000000000000).coeff 0) =
  "[680057396, 209783453; 209783453, 470273943]"

end Azurite.AzPolynomial.NestedCoeffExamples
