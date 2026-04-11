import Azurite.AzMvPolynomial.Eval2
import Azurite.AzMvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# `optionEquivRight` for AzMvPolynomial

Converts a polynomial in `n + 1` variables (indexed by `Fin (n+1)`) into a
multivariate polynomial in the last `n` variables whose coefficients are
themselves univariate polynomials:

```
AzMvPolynomial (n+1) R ord →  AzMvPolynomial n (AzPolynomial R) ord
```

The variable `Fin.0` is replaced by `C AzPolynomial.X` (a constant polynomial
in `Fin n` whose coefficient is the outer variable `X`), and each
`Fin.succ k` is replaced by `AzMvPolynomial.X k`.

This is the Fin-only counterpart of Mathlib's
`MvPolynomial.optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X]`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward direction -/

/-- Convert a polynomial in `n + 1` variables into a multivariate polynomial
    in the last `n` variables whose coefficients are univariate polynomials.

    Matches `MvPolynomial.optionEquivRight` from Mathlib (forward direction). -/
def AzMvPolynomial.optionEquivRight {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (n+1) R ord) :
    AzMvPolynomial n (AzPolynomial R) ord :=
  p.eval₂ ((AzMvPolynomial.CHom (n := n) (ord := ord)).comp AzPolynomial.CHom)
    (fun i => Fin.cases
      (AzMvPolynomial.C (ord := ord) (AzPolynomial.X : AzPolynomial R))
      (fun k => AzMvPolynomial.X (ord := ord) k) i)

/-! ### Computable Horner evaluation of an `AzPolynomial R`

We need a ring homomorphism `AzPolynomial R →+* AzMvPolynomial (n+1) R ord`
sending `X ↦ X 0` and `C r ↦ C r` to define the reverse direction. The
underlying function is a computable Horner fold, with ring-hom axioms proved
by bridging through `Polynomial.eval₂`.
-/

/-- Evaluate an `AzPolynomial R` at `x : S` via the coefficient embedding
    `φ : R →+* S`, computed directly by Horner's method. -/
def AzPolynomial.eval₂Fn {S : Type _} [CommSemiring S]
    (φ : R →+* S) (x : S) (p : AzPolynomial R) : S :=
  p.coeffs.foldr (init := 0) fun r acc => φ r + acc * x

omit [NoZeroDivisors R] [DecidableEq R] in
private lemma AzPolynomial.eval₂Fn_list {S : Type _} [CommSemiring S]
    (φ : R →+* S) (x : S) (l : List R) :
    l.foldr (init := (0 : S)) (fun r acc => φ r + acc * x) =
    Polynomial.eval₂ φ x (List.toPoly l) := by
  induction l with
  | nil => simp [List.toPoly]
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.toPoly, Polynomial.eval₂_add,
               Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, ih]
    ring

omit [NoZeroDivisors R] [DecidableEq R] in
private lemma AzPolynomial.eval₂Fn_eq_polynomial_eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (x : S) (p : AzPolynomial R) :
    AzPolynomial.eval₂Fn φ x p = Polynomial.eval₂ φ x (AzPolynomial.toPoly p) := by
  unfold AzPolynomial.eval₂Fn
  rw [← Array.foldr_toList]
  exact AzPolynomial.eval₂Fn_list φ x p.coeffs.toList

/-- Computable ring hom `AzPolynomial R →+* S` evaluating `X` at `x : S`
    via `φ : R →+* S`. Underlying function is a Horner fold; ring-hom
    axioms proved via the bridge to `Polynomial.eval₂`. -/
def AzPolynomial.eval₂Hom {S : Type _} [CommSemiring S]
    (φ : R →+* S) (x : S) : AzPolynomial R →+* S where
  toFun := AzPolynomial.eval₂Fn φ x
  map_zero' := by
    rw [AzPolynomial.eval₂Fn_eq_polynomial_eval₂,
        show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R)
          from toPoly_zero,
        Polynomial.eval₂_zero]
  map_one' := by
    rw [AzPolynomial.eval₂Fn_eq_polynomial_eval₂,
        show AzPolynomial.toPoly (1 : AzPolynomial R) = (1 : Polynomial R)
          from toPoly_one,
        Polynomial.eval₂_one]
  map_add' := fun p q => by
    rw [AzPolynomial.eval₂Fn_eq_polynomial_eval₂, toPoly_add, Polynomial.eval₂_add,
        ← AzPolynomial.eval₂Fn_eq_polynomial_eval₂,
        ← AzPolynomial.eval₂Fn_eq_polynomial_eval₂]
  map_mul' := fun p q => by
    rw [AzPolynomial.eval₂Fn_eq_polynomial_eval₂, toPoly_mul, Polynomial.eval₂_mul,
        ← AzPolynomial.eval₂Fn_eq_polynomial_eval₂,
        ← AzPolynomial.eval₂Fn_eq_polynomial_eval₂]

omit [NoZeroDivisors R] in
/-- Bridge lemma: `AzPolynomial.eval₂Hom` factors through the Mathlib bridge
    `AzPolynomial.toPoly` followed by `Polynomial.eval₂`. -/
theorem AzPolynomial.eval₂Hom_eq_polynomial_eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (x : S) (p : AzPolynomial R) :
    AzPolynomial.eval₂Hom φ x p = Polynomial.eval₂ φ x (AzPolynomial.toPoly p) :=
  AzPolynomial.eval₂Fn_eq_polynomial_eval₂ φ x p

/-! ### Reverse direction -/

/-- Inverse direction of `optionEquivRight`: convert a multivariate polynomial
    in `Fin n` with `AzPolynomial R` coefficients back into a multivariate
    polynomial in `Fin (n+1)` with `R` coefficients. The outer `AzPolynomial.X`
    becomes `AzMvPolynomial.X 0`, and each inner variable `k` is shifted up to
    `Fin.succ k`. -/
def AzMvPolynomial.optionEquivRightSymm {n : ℕ} {ord : MonomialOrder}
    (q : AzMvPolynomial n (AzPolynomial R) ord) :
    AzMvPolynomial (n+1) R ord :=
  q.eval₂
    (AzPolynomial.eval₂Hom (AzMvPolynomial.CHom (n := n+1) (ord := ord))
      (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1))))
    (fun k => AzMvPolynomial.X (ord := ord) (k.succ : Fin (n+1)))

end Azurite
