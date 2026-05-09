import Azurite.BasuPollackRoy.Chapter1.Section1_3.DegFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems

/-! # BPR Section 1.3 — The leaf formula `C_L`

Given a leaf `L` of `TRems(P, Q)`, let `B_L` be the unique path from the
root `R` to `L`. Every path ends with the `0` polynomial (the explicit
leaf). For each non-leaf node `N` on `B_L`, let `c(N)` be the unique
child of `N` in `B_L`. The **leaf formula** `C_L` is
```
  deg_X(Q) = natDeg(Pol(c(R)))
  ∧ ⋀_{N ∈ B_L, N ≠ R, c(N) ≠ 0}
      deg_X(−PRem(Pol(p(N)), Pol(N))) = natDeg(Pol(c(N)))
  ∧ deg_X(−PRem(Pol(p(L)), Pol(L's parent))) = ⊥
```
where the last conjunct says the remainder at the leaf vanishes.

We represent the path as a list of node polynomials (excluding the root `P`),
so a path `[q₁, q₂, …, qₘ, 0]` encodes:
- `q₁` is a child of the root (an element of `Tru(Q)` or `0`),
- `qᵢ₊₁` is a child of `qᵢ` (an element of `Tru(−PRem(p(qᵢ), qᵢ))` or `0`),
- `0` at the end is the explicit leaf (with `Pol = 0`).

Using `degFormula R (↑n)` (which pins the degree of `R_y` to exactly `n`)
instead of `degEqFormula R next` ensures disjointness across branches,
since the `degFormula` family partitions `C^k` by `degFormula_disjoint`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

section LeafFormula

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Auxiliary: conjoin `degFormula` instances along the interior of the path.
`parent` and `cur` are consecutive nodes; `rest` is the remainder of the path.
When `next = 0` (the explicit leaf), use `degFormula R ⊥` (remainder vanishes).
When `next ≠ 0`, use `degFormula R (↑next.natDegree)` and recurse. -/
noncomputable def leafFormulaAux
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (rest : List (Polynomial (MvPolynomial (Fin k) D))) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match rest with
  | [] => degFormula (-(pRemMv parent cur)) ⊥
  | next :: rest' =>
    if next = 0 then
      degFormula (-(pRemMv parent cur)) ⊥
    else
      (degFormula (-(pRemMv parent cur)) (↑next.natDegree)).and
        (leafFormulaAux cur next rest')

/-- BPR's leaf formula `C_L` for a root-to-leaf path in `TRems(P, Q)`.

`path` is the list of node polynomials on the path **after the root**
(i.e., starting from a child of `P`). With the explicit `0` leaf,
every valid path is non-empty and ends with `0`. When the first element
is `0`, the formula is just `degFormula Q ⊥` (i.e. `Q_y = 0`). -/
noncomputable def leafFormula
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D))) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match path with
  | [] => degFormula Q ⊥
  | q :: rest =>
    if q = 0 then degFormula Q ⊥
    else (degFormula Q (↑q.natDegree)).and (leafFormulaAux P q rest)

end LeafFormula

end Azurite.BPR
