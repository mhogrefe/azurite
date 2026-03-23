/-
  Multivariate polynomials represented as sorted arrays of monomials.
-/
import Azurite.AzMvPolynomial.Monomial

namespace Azurite

open MonicMonomial Monomial

/-- A multivariate polynomial: a sorted array of monomials.
    The monic parts of the monomials are required to be in strictly
    descending order (which implies they are distinct).  An empty
    array represents the zero polynomial. -/
structure AzMvPolynomial (R : Type _) [Semiring R] (σ : Type _)
    {n : ℕ} [LinearOrder σ] [Var σ n]
    (ord : MonomialOrder := .Degrevlex) where
  /-- The array of monomials, sorted so that leading terms come first. -/
  terms : Array (Monomial R σ ord)
  /-- Adjacent monic parts are strictly decreasing:
      `compare terms[i].monic terms[i+1].monic = .gt`. -/
  sorted : terms.toList.IsChain (fun a b => compare a.monic b.monic = .gt)

namespace AzMvPolynomial

variable {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- The zero polynomial (empty term list). -/
def zero : AzMvPolynomial R σ ord := ⟨#[], List.isChain_nil⟩

instance : Zero (AzMvPolynomial R σ ord) := ⟨zero⟩

/-- A polynomial is zero iff its term array is empty. -/
@[simp] theorem zero_terms : (0 : AzMvPolynomial R σ ord).terms = #[] := rfl

/-- Number of terms in the polynomial. -/
def numTerms (p : AzMvPolynomial R σ ord) : ℕ := p.terms.size

/-- The leading monomial (largest monic part), if the polynomial is nonzero. -/
def leadTerm (p : AzMvPolynomial R σ ord) : Option (Monomial R σ ord) :=
  p.terms[0]?

/-- The leading monic monomial, if the polynomial is nonzero. -/
def leadMonic (p : AzMvPolynomial R σ ord) : Option (MonicMonomial σ ord) :=
  p.leadTerm.map Monomial.monic

/-- The leading coefficient, if the polynomial is nonzero. -/
def leadCoeff (p : AzMvPolynomial R σ ord) : Option {c : R // c ≠ 0} :=
  p.leadTerm.map Monomial.coeff

/-- Construct a polynomial from a single monomial. -/
def ofMonomial (m : Monomial R σ ord) : AzMvPolynomial R σ ord :=
  ⟨#[m], List.isChain_singleton _⟩

/-- The total degree of the polynomial (maximum total degree among its terms),
    or 0 for the zero polynomial. -/
def totalDegree (p : AzMvPolynomial R σ ord) : ℕ :=
  p.terms.foldl (fun acc m => max acc m.totalDegree) 0

end AzMvPolynomial

end Azurite
