/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Computable versions of BPR's `degFormula` and `degEqFormula` (Notation 1.18).

  These operate on `AzPolynomial (AzMvPolynomial k D ord)` and produce
  `Formula (Fin k) (AzFieldAtom k D ord)`.
-/
import Azurite.AzFormula.Basic
import Azurite.AzFormula.ToString
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.MvCoeffParse
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### List combinators -/

/-- Conjunction of a list of formulas with trivial-atom absorption.
    Empty list gives `azTrueFormula` (0 = 0). Singleton list returns
    the element directly. Uses `azSmartAnd` to absorb trivially
    true/false atoms during construction. -/
def azConjList :
    List (Formula (Fin k) (AzFieldAtom k D ord)) →
    Formula (Fin k) (AzFieldAtom k D ord)
  | [] => azTrueFormula
  | [Φ] => Φ
  | Φ :: Φs => azSmartAnd Φ (azConjList Φs)

/-- Disjunction of a list of formulas with trivial-atom absorption.
    Empty list gives `azFalseFormula` (0 ≠ 0). Singleton list returns
    the element directly. Uses `azSmartOr` to absorb trivially
    true/false atoms during construction. -/
def azDisjList :
    List (Formula (Fin k) (AzFieldAtom k D ord)) →
    Formula (Fin k) (AzFieldAtom k D ord)
  | [] => azFalseFormula
  | [Φ] => Φ
  | Φ :: Φs => azSmartOr Φ (azDisjList Φs)

/-! ### Degree formulas -/

/-- BPR Notation 1.18 (computable): `deg_X(Q) = i` as a formula.

For `Q ∈ D[Y₁,…,Yₖ][X]`:
- `i = ⊥`: all coefficients vanish (degree = −∞, i.e., `Q_y = 0`)
- `i = some n`: `coeff Q n ≠ 0` and all higher coefficients vanish -/
def azDegFormula
    (Q : AzPolynomial (AzMvPolynomial k D ord)) (i : WithBot ℕ) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  match i with
  | ⊥ => azConjList ((List.range (Q.natDegree + 1)).map fun j =>
      azEqZero (Q.coeff j))
  | some n => azSmartAnd
      (azNeZero (Q.coeff n))
      (azConjList ((List.range (Q.natDegree - n)).map fun j =>
        azEqZero (Q.coeff (n + 1 + j))))

/-- BPR Notation 1.18 (computable): `deg_X(Q₁) = deg_X(Q₂)` as a formula.

This is the finite disjunction over all possible degree values
`i ∈ {⊥, 0, 1, …, max(natDeg Q₁, natDeg Q₂)}` of
`azDegFormula Q₁ i ∧ azDegFormula Q₂ i`. -/
def azDegEqFormula
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  let m := max Q₁.natDegree Q₂.natDegree
  azDisjList (
    (azSmartAnd (azDegFormula Q₁ ⊥) (azDegFormula Q₂ ⊥)) ::
    (List.range (m + 1)).map fun i =>
      azSmartAnd (azDegFormula Q₁ (some i)) (azDegFormula Q₂ (some i)))

/-- BPR Notation 1.18 (computable): `deg_X(Q₁) ≠ deg_X(Q₂)` as a formula.

Defined as the negation of `azDegEqFormula Q₁ Q₂`. Mirrors BPR's
`degNeqFormula`. -/
def azDegNeqFormula
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  .not (azDegEqFormula Q₁ Q₂)

private abbrev MvInt3 := AzMvPolynomial 3 AzInt .Degrevlex
private instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def p (s : String) : AzPolynomial MvInt3 :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := AzInt)
    (ord := .Degrevlex) s).getD 0

#guard toString (azDegEqFormula (p "(3*a+b)*x^2+(-c)*x+(a+b)") (p "(-a*b)*x^2+(a^2-b^2)*x+(a*b)")) == "((x₀+x₁ = 0 ∧ (-x₂ = 0 ∧ 3*x₀+x₁ = 0)) ∧ (x₀*x₁ = 0 ∧ (x₀^2-x₁^2 = 0 ∧ -x₀*x₁ = 0))) ∨ (((x₀+x₁ ≠ 0 ∧ (-x₂ = 0 ∧ 3*x₀+x₁ = 0)) ∧ (x₀*x₁ ≠ 0 ∧ (x₀^2-x₁^2 = 0 ∧ -x₀*x₁ = 0))) ∨ (((-x₂ ≠ 0 ∧ 3*x₀+x₁ = 0) ∧ (x₀^2-x₁^2 ≠ 0 ∧ -x₀*x₁ = 0)) ∨ (3*x₀+x₁ ≠ 0 ∧ -x₀*x₁ ≠ 0)))"

-- Simplified by construction — no post-processing needed
#guard isAzSimplified (azDegEqFormula (p "(3*a+b)*x^2+(-c)*x+(a+b)") (p "(-a*b)*x^2+(a^2-b^2)*x+(a*b)"))

-- `azDegNeqFormula` is just the negation of `azDegEqFormula`.
#guard toString (azDegNeqFormula (p "(3*a+b)*x^2+(-c)*x+(a+b)") (p "(-a*b)*x^2+(a^2-b^2)*x+(a*b)")) == "¬(" ++ toString (azDegEqFormula (p "(3*a+b)*x^2+(-c)*x+(a+b)") (p "(-a*b)*x^2+(a^2-b^2)*x+(a*b)")) ++ ")"

end Azurite
