/-
  Conversion from `AzMvPolynomialNew` to `AzPolynomial` (univariate).
-/
import Azurite.AzMvPolynomial.New.Basic
import Azurite.AzMvPolynomial.New.Vars
import Azurite.AzPolynomial.Basic

namespace Azurite
open AzMvPolynomialNew MonomialOrder

variable {R : Type _} [Semiring R] [DecidableEq R] {ord : MonomialOrder}

/-! ### MonicMonomialNew.degree -/

/-- The degree of a monic monomial in a single-variable setting (`n = 1`). -/
def MonicMonomialNew.degree (m : MonicMonomialNew 1 ord) : ℕ :=
  m.exponent ⟨0, by omega⟩

/-! ### Coefficient array construction -/

/-- Build a dense coefficient array from the terms (single variable case). -/
def buildCoeffsFromTermsNew (terms : Array (MonomialNew 1 R ord)) (size : ℕ) : Array R :=
  terms.foldl (fun (acc : Array R) m =>
    let deg := m.monic.degree
    if h : deg < acc.size then acc.set deg m.coeff.val
    else acc) (Array.replicate size (0 : R))

/-- Convert an `AzMvPolynomialNew 1 R ord` to an `AzPolynomial R`. -/
def AzMvPolynomialNew.toAzPolynomial
    (p : AzMvPolynomialNew 1 R ord) : AzPolynomial R :=
  if h : p.terms.size = 0 then AzPolynomial.zero
  else
    let leadTerm := p.terms[0]'(by omega)
    let maxDeg := leadTerm.monic.degree
    let coeffs := buildCoeffsFromTermsNew p.terms (maxDeg + 1)
    AzPolynomial.normalize coeffs

/-! ### Variant: arbitrary `n`, given a designated variable index `i : Fin n` -/

variable {n : ℕ}

/-- Build a dense coefficient array using the exponent at index `i`. -/
def buildCoeffsFromTermsAtNew (i : Fin n) (terms : Array (MonomialNew n R ord))
    (size : ℕ) : Array R :=
  terms.foldl (fun (acc : Array R) m =>
    let deg := m.monic.exponent i
    if h : deg < acc.size then acc.set deg m.coeff.val
    else acc) (Array.replicate size (0 : R))

/-- Convert to univariate given a proof that the polynomial uses at most
    variable index `i`. -/
def AzMvPolynomialNew.toAzPolynomialAt
    (p : AzMvPolynomialNew n R ord) {i : Fin n} (_hv : p.vars ⊆ {i}) : AzPolynomial R :=
  if h : p.terms.size = 0 then AzPolynomial.zero
  else
    let leadTerm := p.terms[0]'(by omega)
    let maxDeg := leadTerm.monic.exponent i
    let coeffs := buildCoeffsFromTermsAtNew i p.terms (maxDeg + 1)
    AzPolynomial.normalize coeffs

end Azurite
