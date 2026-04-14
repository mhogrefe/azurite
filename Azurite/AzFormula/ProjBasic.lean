/-
  Computable version of BPR's `projBasic` (Section 1.3).

  Given two finite lists `Ps, Qs ⊂ D[X₀, Y₁, …, Y_k]`, produces a
  quantifier-free formula in `Fin k` variables whose realization equals
  the projection (over `X₀`) of the basic constructible set defined by
  `∀ P ∈ Ps, P = 0` and `∀ Q ∈ Qs, Q ≠ 0`.

  The variable being projected is `Fin 0` (the "first" variable, to match
  `AzMvPolynomial.finSuccEquiv`). For projection of an arbitrary variable,
  see `azProjBasicAt`.
-/
import Azurite.AzFormula.LeafFormula
import Azurite.AzFormula.Posgcd
import Azurite.AzMvPolynomial.FinSuccEquiv

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-- Extract a DNF of an `AzFieldAtom` quantifier-free formula as a
list of basic-constructible shape. Each clause `(eqs, neqs)` means
`(∀ P ∈ eqs, P = 0) ∧ (∀ Q ∈ neqs, Q ≠ 0)`. The disjunction of these
clauses is equivalent to the input formula (assuming QF input). -/
def azToConjDisjForms {n : ℕ}
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    List (List (AzMvPolynomial n D ord) × List (AzMvPolynomial n D ord)) :=
  (toDNF Φ).map fun cl =>
    cl.foldr (init := (([] : List (AzMvPolynomial n D ord)),
                       ([] : List (AzMvPolynomial n D ord))))
      (fun a (eqs, neqs) =>
        if a.isEq then (a.poly :: eqs, neqs) else (eqs, a.poly :: neqs))

/-- Computable version of BPR's `projBasic`: the quantifier-free
formula whose realization is the projection (over the first variable
`Fin 0`) of the basic constructible set defined by `Ps, Qs`.

Uses `AzMvPolynomial.finSuccEquiv` to split off the first variable,
then follows BPR's algorithm: for each element `(G₁, 𝒞₁)` of
`posgcd(Ps')`, and each leaf path of `TRems(extra, G₁)` where
`extra = (∏ Qs')^d`, build the conjunct
`𝒞₁ ∧ leafFormula extra G₁ path ∧ degNeqFormula (pathLeafParent extra path) G₁`
and disjoin them all. -/
def azProjBasic
    (Ps Qs : List (AzMvPolynomial (k+1) D ord)) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  let Ps' : List (AzPolynomial (AzMvPolynomial k D ord)) :=
    Ps.map AzMvPolynomial.finSuccEquiv
  let Qs' : List (AzPolynomial (AzMvPolynomial k D ord)) :=
    Qs.map AzMvPolynomial.finSuccEquiv
  let d : ℕ := 1 + (Ps'.map AzPolynomial.natDegree).foldr max 0
  let extra : AzPolynomial (AzMvPolynomial k D ord) := Qs'.prod ^ d
  azDisjList <|
    (azPosgcd Ps').flatMap fun QC₁ =>
      (AzPolynomial.tremsTree extra QC₁.1).leafPaths.map fun path =>
        azSmartAnd QC₁.2 (azSmartAnd
          (azLeafFormula extra QC₁.1 path)
          (azDegNeqFormula (azPathLeafParent extra path) QC₁.1))

/-- Computable variant of `azProjBasic` that projects an arbitrary
variable `i : Fin (k+1)` rather than the first. Renames variable `i`
to position `0` before applying `azProjBasic`. -/
def azProjBasicAt
    (i : Fin (k+1))
    (Ps Qs : List (AzMvPolynomial (k+1) D ord)) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  let e : Fin (k+1) ≃ Fin (k+1) := Equiv.swap (0 : Fin (k+1)) i
  let rename : AzMvPolynomial (k+1) D ord → AzMvPolynomial (k+1) D ord :=
    fun P => P.renameInjective e e.injective ord
  azProjBasic (Ps.map rename) (Qs.map rename)

/-! ### Projection of quantifier-free formulas -/

/-- Project a quantifier-free formula `Φ` over the first variable
(`Fin 0`): returns a quantifier-free formula in `Fin k` variables
whose realization equals `{ y : Fin k → C | ∃ x, Fin.snoc' y x ∈
Φ.realization }`, where `Fin.snoc'` prepends `x` as the `Fin 0`
component. Requires `Φ.IsQuantifierFree` as a correctness invariant.

The output is post-processed with `toNNF` (pushing `¬(P = 0)` into
`P ≠ 0`) and `azSimplify` (absorbing trivially true/false atoms). -/
def azProjectQF
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (_hqf : Φ.IsQuantifierFree) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  azSimplify <| toNNF <|
    azDisjList ((azToConjDisjForms Φ).map fun (Ps, Qs) => azProjBasic Ps Qs)

/-- Project a quantifier-free formula `Φ` over an arbitrary variable
`i : Fin (k+1)`. Renames variable `i` to position `0` first, then
applies `azProjectQF`. -/
def azProjectQFAt
    (i : Fin (k+1))
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    Formula (Fin k) (AzFieldAtom k D ord) :=
  let e : Fin (k+1) ≃ Fin (k+1) := Equiv.swap (0 : Fin (k+1)) i
  let Φ' := renameFormulaEquiv e Φ
  azProjectQF Φ' (Formula.rename_isQF _ _ Φ hqf)

/-! ### Tests -/

section Tests

open AzMvPolynomial

-- Projection of the empty system: `Ps = [], Qs = []` ⇒ the basic set
-- is all of `C^{k+1}`, and its projection over any variable is `C^k`,
-- which is logically true. With smart constructors the formula comes
-- out as the degree-comparison `deg(1) ≠ deg(0)`, serialized as
-- `¬(1 = 0)` — a logical tautology in the ambient field atoms.
#guard toString
    (azProjBasic (k := 2) (D := ℤ) (ord := .Degrevlex) [] []) ==
  "¬(1 = 0)"

-- `Qs ≠ []` with `Ps = []`: same structural result as the empty system,
-- because posgcd on an empty `Ps` still gives `[(0, true)]` and the
-- outer posgcd only changes via `extra` which is `1^d`-capped on `Qs.prod`.
#guard toString
    (azProjBasic (k := 2) (D := ℤ) (ord := .Degrevlex) [] [X 0]) ==
  "¬(1 = 0)"

-- DNF extraction: single atom ⇒ 1 clause with one equality.
#guard
  let clauses := azToConjDisjForms (D := ℤ) (ord := .Degrevlex) (n := 3)
    (azEqZero (X 0))
  clauses.length == 1 ∧ clauses == [([X (0 : Fin 3)], [])]

-- DNF extraction: disjunction ⇒ 2 clauses.
#guard
  let clauses := azToConjDisjForms (D := ℤ) (ord := .Degrevlex) (n := 3)
    (Formula.or (azEqZero (X 0)) (azEqZero (X 1)))
  clauses.length == 2

-- DNF extraction: conjunction ⇒ 1 clause with both atoms.
#guard
  let clauses := azToConjDisjForms (D := ℤ) (ord := .Degrevlex) (n := 3)
    (Formula.and (azEqZero (X 0)) (azNeZero (X 1)))
  clauses == [([X (0 : Fin 3)], [X (1 : Fin 3)])]

-- DNF extraction: distribute `and` over `or` ⇒ 2 clauses.
#guard
  let clauses := azToConjDisjForms (D := ℤ) (ord := .Degrevlex) (n := 3)
    (Formula.and (azEqZero (X 0))
      (Formula.or (azNeZero (X 1)) (azEqZero (X 2))))
  clauses.length == 2

-- DNF extraction: negation absorbs into atom flip via toNNF.
#guard
  let clauses := azToConjDisjForms (D := ℤ) (ord := .Degrevlex) (n := 3)
    (Formula.not (azEqZero (X 0)))
  clauses == [([], [X (0 : Fin 3)])]

-- `azProjectQF` normalizes its output with `toNNF` and `azSimplify`,
-- so `¬(P = 0)` atoms are pushed into `P ≠ 0` atoms. The result
-- should contain no residual `¬` characters.
#guard
  let s := toString (azProjectQF (k := 2) (D := ℤ) (ord := .Degrevlex)
    (azEqZero (n := 3) (X 0)) trivial)
  !s.contains '¬'

#guard
  let s := toString (azProjectQF (k := 2) (D := ℤ) (ord := .Degrevlex)
    (Formula.not (azEqZero (n := 3) (X 0))) trivial)
  !s.contains '¬'

-- `azProjectQFAt i` projects variable `i` by renaming it to `0` first.
-- Projecting variable `1` of `X₁ = 0` agrees (after renaming) with
-- projecting variable `0` of `X₀ = 0`.
#guard toString (azProjectQFAt (k := 2) (D := ℤ) (ord := .Degrevlex)
    (1 : Fin 3) (azEqZero (n := 3) (X 1)) trivial) ==
  toString (azProjectQF (k := 2) (D := ℤ) (ord := .Degrevlex)
    (azEqZero (n := 3) (X 0)) trivial)

end Tests

end Azurite
