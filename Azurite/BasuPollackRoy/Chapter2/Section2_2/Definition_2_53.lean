import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Jumps

/-!
# BPR Definition 2.53: Cauchy index

For `a < b` in `R ∪ {−∞, +∞}` and `P, Q ∈ R[X]`, the **Cauchy index** of
`Q/P` on `(a, b)`, denoted `Ind(Q/P; a, b)`, is the number of jumps of
`Q/P` from `−∞` to `+∞` minus the number of jumps from `+∞` to `−∞` on the
open interval `(a, b)`.

The Cauchy index of `Q/P` on `R`, written `Ind(Q/P)`, is `Ind(Q/P; −∞, +∞)`.

We expose two names:

* `cauchyIndexOn Q P a b` for the interval form, with `a, b : ExtendedPoint R`.
* `cauchyIndex Q P` for the full-line form, equal to
  `cauchyIndexOn Q P .negInf .posInf`.

The jumps occur only at roots of `P` (the predicates `JumpsFromNegInfToPosInf`
and `JumpsFromPosInfToNegInf` already force `P.rootMultiplicity x > 0`), so we
range over the (finitely many) elements of `P.roots.toFinset`. The predicates
themselves are not decidable in general, so the definition is `noncomputable`
and uses classical decidability for the filter.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The open interval `(a, b) ⊆ R` for extended endpoints
    `a, b : ExtendedPoint R`. Empty when `a = +∞` or `b = −∞`. -/
def ExtendedPoint.openInterval : ExtendedPoint R → ExtendedPoint R → Set R
  | .posInf,   _           => ∅
  | .negInf,   .negInf     => ∅
  | .finite _, .negInf     => ∅
  | .negInf,   .posInf     => Set.univ
  | .finite a, .posInf     => Set.Ioi a
  | .negInf,   .finite b   => Set.Iio b
  | .finite a, .finite b   => Set.Ioo a b

open Classical in
/-- **BPR Definition 2.53.** The Cauchy index of `Q/P` on the open interval
    `(a, b)`, for `a, b : ExtendedPoint R`. The number of jumps of `Q/P`
    from `−∞` to `+∞` minus the number of jumps from `+∞` to `−∞` on
    `(a, b)`. -/
noncomputable def cauchyIndexOn (Q P : R[X]) (a b : ExtendedPoint R) : ℤ :=
  let I := ExtendedPoint.openInterval a b
  ((P.roots.toFinset.filter
    (fun x => x ∈ I ∧ JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
  ((P.roots.toFinset.filter
    (fun x => x ∈ I ∧ JumpsFromPosInfToNegInf Q P x)).card : ℤ)

/-- **BPR Definition 2.53.** The Cauchy index of `Q/P` on all of `R`,
    `Ind(Q/P) := Ind(Q/P; −∞, +∞)`. -/
noncomputable def cauchyIndex (Q P : R[X]) : ℤ :=
  cauchyIndexOn Q P .negInf .posInf

omit [IsStrictOrderedRing R] in
@[simp] theorem cauchyIndex_eq_cauchyIndexOn_negInf_posInf (Q P : R[X]) :
    cauchyIndex Q P = cauchyIndexOn Q P .negInf .posInf := rfl

end Azurite.BPR
