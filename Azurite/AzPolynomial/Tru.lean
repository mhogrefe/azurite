import Azurite.AzPolynomial.Truncate
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.MvCoeffParse

/-!
# Set of truncations `tru(p)` for `AzPolynomial`

Computable version of BPR's recursive *set of truncations* `Tru(Q)` for
a polynomial `Q ∈ D[Y_1, …, Y_k][X]`, represented as
`AzPolynomial (AzMvPolynomial k D ord)`.

The result is a `List` (naturally ordered by decreasing degree) rather
than a `Set`, making it fully computable.  The equivalence to the
noncomputable `Azurite.BPR.Tru` is proved in `Equiv/Tru.lean`.
-/

namespace Azurite.AzPolynomial

open AzMvPolynomial

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-- Computable **set of truncations** of
`p ∈ D[Y_1, …, Y_k][X]`, matching BPR's `Tru(Q)`:

* `p = 0` → `[]`
* `lcof(p)` is constant in `D`, or `deg(p) = 0` → `[p]`
* otherwise → `p :: tru (truncate (natDegree p − 1) p)` -/
def tru (p : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) :=
  if p == 0 then []
  else if p.leadingCoeff.isConstant || p.natDegree == 0 then [p]
  else p :: tru (truncate (p.natDegree - 1) p)
termination_by p.natDegree
decreasing_by
  have hQpos : 0 < p.natDegree := by
    simp only [Bool.or_eq_true, beq_iff_eq] at *
    omega
  have h := natDegree_truncate_le (p.natDegree - 1) p
  omega

/-! ### Tests -/

section Tests

open AzMvPolynomial

-- Trivial: zero → empty
#guard tru (0 : AzPolynomial (AzMvPolynomial 0 AzInt .Degrevlex)) == []

-- Constant polynomial (degree 0) → singleton
#guard (tru (AzPolynomial.C (AzMvPolynomial.C (1 : AzInt) :
    AzMvPolynomial 0 AzInt .Degrevlex))).length == 1

-- Nontrivial: `(a)*x^2 + (b)*x + (1)` has non-constant leading coefficients
-- at each level, so tru recurses down to the constant term.
private abbrev MvInt3 := AzMvPolynomial 3 AzInt .Degrevlex
private instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def p (s : String) : AzPolynomial MvInt3 :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := AzInt)
    (ord := .Degrevlex) s).getD 0
private def s (q : AzPolynomial MvInt3) : String :=
  q.toStrMvCoeffWith (AbcVar 3)

#guard (tru (p "(a)*x^2+(b)*x+(1)")).map s ==
  ["(a)*x^2+(b)*x+(1)", "(b)*x+(1)", "(1)"]

-- Constant leading coefficient stops recursion early:
-- `x^2 + (a)*x + (1)` has leading coeff `1` (constant), so tru = [p].
#guard (tru (p "x^2+(a)*x+(1)")).map s == ["x^2+(a)*x+(1)"]

end Tests

end Azurite.AzPolynomial
