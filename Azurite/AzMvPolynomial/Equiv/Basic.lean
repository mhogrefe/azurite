/-
  Equivalence between AzMvPolynomial and Mathlib's MvPolynomial.
-/
import Azurite.AzMvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic

namespace Azurite

open MvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Convert a monic monomial's exponent vector to a finitely-supported function `σ →₀ ℕ`.
    Each variable `Var.ofFin i` is mapped to `exponents[i]`; all other values (if any)
    are `0` by construction. -/
noncomputable def MonicMonomial.toFinsupp [DecidableEq σ]
    (m : MonicMonomial σ ord) : σ →₀ ℕ :=
  Finsupp.onFinset (Finset.image Var.ofFin Finset.univ)
    (fun v => m.exponents[Var.toFin v])
    (fun v hv => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Var.toFin v, Var.ofFin_toFin v⟩)

/-- Convert a single monomial to a Mathlib `MvPolynomial`. -/
noncomputable def Monomial.toMvPoly [DecidableEq σ]
    (m : Monomial R σ ord) : MvPolynomial σ R :=
  MvPolynomial.monomial m.monic.toFinsupp m.coeff.val

/-- Convert an `AzMvPolynomial` to a Mathlib `MvPolynomial` by summing
    the contributions of each monomial term. -/
noncomputable def AzMvPolynomial.toMvPoly [DecidableEq σ]
    (p : AzMvPolynomial R σ ord) : MvPolynomial σ R :=
  p.terms.foldl (· + ·.toMvPoly) 0

end Azurite
