/-
  Computable version of BPR's `leafFormula` (Lemma 1.19).

  Operates on `AzPolynomial (AzMvPolynomial k D ord)` and produces
  `Formula (Fin k) (AzFieldAtom k D ord)`, using smart constructors
  (`azSmartAnd`) to absorb trivial atoms during construction.
-/
import Azurite.AzFormula.DegFormula
import Azurite.AzFormula.ToString
import Azurite.AzPolynomial.PRem
import Azurite.AzPolynomial.TRems
import Azurite.AzPolynomial.MvCoeffParse

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-- Auxiliary for `azLeafFormula`: conjoins degree formulas along the
interior of a path in `TRems(P, Q)`. Mirrors BPR's `leafFormulaAux`
but uses `pRem` (computable) and `azSmartAnd` (trivial-atom absorbing). -/
def azLeafFormulaAux
    (parent cur : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) →
    Formula (Fin k) (AzFieldAtom k D ord)
  | [] => azDegFormula (-(AzPolynomial.pRem parent cur)) ⊥
  | next :: rest =>
    if next == 0 then
      azDegFormula (-(AzPolynomial.pRem parent cur)) ⊥
    else
      azSmartAnd
        (azDegFormula (-(AzPolynomial.pRem parent cur)) (↑next.natDegree))
        (azLeafFormulaAux cur next rest)

/-- BPR's leaf formula `C_L` for a root-to-leaf path in `TRems(P, Q)`.
Computable version using smart constructors to absorb trivial atoms.

`path` is the list of node polynomials on the path **after the root**
(starting from a child of `P`). When the first element is `0`, the
formula is just `azDegFormula Q ⊥` (i.e. `Q_y = 0`). -/
def azLeafFormula
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (path : List (AzPolynomial (AzMvPolynomial k D ord))) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  match path with
  | [] => azDegFormula Q ⊥
  | q :: rest =>
    if q == 0 then azDegFormula Q ⊥
    else azSmartAnd (azDegFormula Q (↑q.natDegree)) (azLeafFormulaAux P q rest)

/-! ### Tests -/

section Tests

private abbrev MvInt3 := AzMvPolynomial 3 ℤ .Degrevlex
private instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def p (s : String) : AzPolynomial MvInt3 :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := ℤ)
    (ord := .Degrevlex) s).getD 0
private def s (q : AzPolynomial MvInt3) : String :=
  q.toStrMvCoeffWith (AbcVar 3)

-- Helper: leaf paths of a rose tree
private def rtLeafPaths {α : Type*} : AzPolynomial.RoseTree α → List (List α)
  | .node _ [] => [[]]
  | .node _ cs => cs.flatMap fun c =>
      (rtLeafPaths c).map (c.root :: ·)

-- Path [0]: Q_y = 0
#guard toString (azLeafFormula (p "x+(a)") (p "x+(b)") [p "0"]) ==
  toString (azDegFormula (p "x+(b)") (⊥ : WithBot ℕ))

-- Path []: same as [0]
#guard toString (azLeafFormula (p "x+(a)") (p "x+(b)") []) ==
  toString (azDegFormula (p "x+(b)") (⊥ : WithBot ℕ))

-- Q = (1) (constant), path = [(1)]:
-- degFormula((1), 0): coeff 0 = 1 is a nonzero constant, so azNeZero 1
-- is trivially true and azSmartAnd absorbs → azTrueFormula.
-- pRem(x+(a), (1)) = 0, so azLeafFormulaAux gives degFormula(0, ⊥) = azTrueFormula.
-- azSmartAnd (true) (true) → azTrueFormula.
#guard toString (azLeafFormula (p "x+(a)") (p "(1)") [p "(1)"]) == "0 = 0"

-- BPR Example 1.17: P = x^4+(a)*x^2+(b)*x+(c), Q = (4)*x^3+(2*a)*x+(b)
private def ex117P := p "x^4+(a)*x^2+(b)*x+(c)"
private def ex117Q := p "(4)*x^3+(2*a)*x+(b)"
private def ex117tree := AzPolynomial.tremsTree ex117P ex117Q

-- Extract leaf paths (rtLeafPaths gives paths starting from root's children)
private def ex117paths : List (List (AzPolynomial MvInt3)) :=
  rtLeafPaths ex117tree

-- 9 leaf paths (matching the nine 0-sentinel leaves from TRems tests)
#guard ex117paths.length == 9

-- Path [Q, t3, 0]: through (-16c)
#guard s (ex117paths.getD 6 [] |>.getD 0 0) == "(4)*x^3+(2*a)*x+(b)"
#guard s (ex117paths.getD 6 [] |>.getD 1 0) == "(-16*c)"

-- All nine leaf formulas are well-formed
#guard (ex117paths.map (azLeafFormula ex117P ex117Q)).length == 9

-- Simplified by construction
#guard (ex117paths.map (azLeafFormula ex117P ex117Q)).all isAzSimplified

end Tests

end Azurite
