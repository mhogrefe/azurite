/-
  Multivariate polynomials represented as sorted arrays of monomials.
-/
import Azurite.AzMvPolynomial.Monomial
import Azurite.AzMvPolynomial.MonicMonomialOrder

namespace Azurite

open MonicMonomial Monomial

/-- A multivariate polynomial: a sorted array of monomials.
    The monic parts of the monomials are required to be in strictly
    descending order (which implies they are distinct).  An empty
    array represents the zero polynomial. -/
structure AzMvPolynomial (σ : Type _)
    {n : ℕ} [LinearOrder σ] [Var σ n]
    (R : Type _) [Semiring R]
    (ord : MonomialOrder := .Degrevlex) where
  /-- The array of monomials, sorted so that leading terms come first. -/
  terms : Array (Monomial σ R ord)
  /-- All pairs of monic parts are strictly decreasing (descending order). -/
  sorted : terms.toList.Pairwise (fun a b => a.monic > b.monic)

namespace AzMvPolynomial

variable {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- The zero polynomial (empty term list). -/
def zero : AzMvPolynomial σ R ord := ⟨#[], List.Pairwise.nil⟩

instance : Zero (AzMvPolynomial σ R ord) := ⟨zero⟩

/-- A polynomial is zero iff its term array is empty. -/
@[simp] theorem zero_terms : (0 : AzMvPolynomial σ R ord).terms = #[] := rfl

/-- Number of terms in the polynomial. -/
def numTerms (p : AzMvPolynomial σ R ord) : ℕ := p.terms.size

/-- The leading monomial (largest monic part), if the polynomial is nonzero. -/
def leadTerm (p : AzMvPolynomial σ R ord) : Option (Monomial σ R ord) :=
  p.terms[0]?

/-- The leading monic monomial, if the polynomial is nonzero. -/
def leadMonic (p : AzMvPolynomial σ R ord) : Option (MonicMonomial σ ord) :=
  p.leadTerm.map Monomial.monic

/-- The leading coefficient, if the polynomial is nonzero. -/
def leadCoeff (p : AzMvPolynomial σ R ord) : Option {c : R // c ≠ 0} :=
  p.leadTerm.map Monomial.coeff

/-- Construct a polynomial from a single monomial. -/
def ofMonomial (m : Monomial σ R ord) : AzMvPolynomial σ R ord :=
  ⟨#[m], List.pairwise_singleton _ _⟩

/-- The constant polynomial `1`.  Returns `0` when `1 = 0` in the
    coefficient ring (trivial ring). -/
def one [DecidableEq R] : AzMvPolynomial σ R ord :=
  if h : (1 : R) = 0 then 0
  else ofMonomial (Monomial.one h)

instance [DecidableEq R] : One (AzMvPolynomial σ R ord) := ⟨one⟩

/-- The total degree of the polynomial (maximum total degree among its terms),
    or 0 for the zero polynomial. -/
def totalDegree (p : AzMvPolynomial σ R ord) : ℕ :=
  p.terms.foldl (fun acc m => max acc m.totalDegree) 0

end AzMvPolynomial

end Azurite
