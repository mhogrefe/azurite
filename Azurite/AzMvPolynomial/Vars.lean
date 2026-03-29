/-
  Variables occurring in AzMvPolynomial terms.
  Matches MvPolynomial.vars from Mathlib.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-! ### MonicMonomial.vars -/

/-- The set of variables with nonzero exponent in a monic monomial. -/
def MonicMonomial.vars (m : MonicMonomial σ ord) : Finset σ :=
  (Finset.univ.filter (fun i : Fin n => m.exponents[i] ≠ 0)).image Var.ofFin

/-! ### Monomial.vars -/

/-- The set of variables occurring in a monomial (from its monic part). -/
def Monomial.vars (m : Monomial σ R ord) : Finset σ :=
  m.monic.vars

/-! ### AzMvPolynomial.vars -/

/-- The set of variables occurring in any term of the polynomial. -/
def AzMvPolynomial.vars (p : AzMvPolynomial σ R ord) : Finset σ :=
  p.terms.foldl (init := ∅) fun acc m => acc ∪ m.vars

/-! ### Guards -/

section Guards

-- Use AbcVar 3 (variables a, b, c) with ℤ coefficients
private def mkMonic (v : Vector ℕ 3) : MonicMonomial (AbcVar 3) := ⟨v⟩
private def mkMon (c : ℤ) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial (AbcVar 3) ℤ :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- MonicMonomial.vars
-- 1 (all zeros) has no variables
#guard (mkMonic (Vector.mk #[0, 0, 0] rfl)).vars.card = 0
-- a has 1 variable
#guard (mkMonic (Vector.mk #[1, 0, 0] rfl)).vars.card = 1
-- a^2*b has 2 variables
#guard (mkMonic (Vector.mk #[2, 1, 0] rfl)).vars.card = 2
-- a*b*c has 3 variables
#guard (mkMonic (Vector.mk #[1, 1, 1] rfl)).vars.card = 3

-- AzMvPolynomial.vars
-- 0 has no variables
#guard (0 : AzMvPolynomial (AbcVar 3) ℤ).vars.card = 0
-- constant 5 has no variables
#guard (AzMvPolynomial.ofMonomial (mkMon 5 (by omega) (Vector.mk #[0, 0, 0] rfl))).vars.card = 0
-- 3*a*b has 2 variables
#guard (AzMvPolynomial.ofMonomial (mkMon 3 (by omega) (Vector.mk #[1, 1, 0] rfl))).vars.card = 2

end Guards

end Azurite

