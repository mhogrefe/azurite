import Azurite.AzMvPolynomial.Pow
import Azurite.AzMvPolynomial.Equiv.Mul

/-!
# Equivalence: AzMvPolynomial.pow ↔ MvPolynomial.pow

Proves that `AzMvPolynomial.pow p k` (computable, with single-monomial optimization
and binary exponentiation fallback) agrees with Mathlib's `MvPolynomial` power.

## Main Theorems

- `toMvPoly_pow`: `toMvPoly (p.pow k) = toMvPoly p ^ k`
- `ofMvPoly_pow`: `(ofMvPoly q).pow k = ofMvPoly (q ^ k)`

## Proof Strategy

The proof avoids relying on the noncomputable `Monoid` instance on `AzMvPolynomial`.
Instead, it uses direct strong induction on `fastPowAux`, applying `toMvPoly_mul`
at each step, and handles the single-monomial fast path via `Monomial.toMvPoly_pow`.
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- `toMvPoly` distributes over `fastPowAux` (the tail-recursive binary
    exponentiation helper). -/
private theorem toMvPoly_fastPowAux
    (acc base : AzMvPolynomial σ R ord) (k : ℕ) :
    toMvPoly (fastPowAux acc base k) =
    toMvPoly acc * toMvPoly base ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | _ k ih =>
    unfold fastPowAux; split
    · rename_i h; subst h; simp
    · rename_i h; split
      · rename_i heven
        rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)),
            toMvPoly_mul, ← sq, ← pow_mul]; congr 2; omega
      · rename_i hodd
        rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)),
            toMvPoly_mul, toMvPoly_mul, mul_assoc,
            ← sq, ← pow_mul, ← pow_succ']; congr 2; omega

omit [DecidableEq R] in
/-- Exponentiating a single monomial and wrapping gives the correct `toMvPoly`. -/
private theorem toMvPoly_pow_monomial (m : Monomial σ R ord) (k : ℕ) :
    toMvPoly (ofMonomial (Monomial.pow m k)) =
    toMvPoly (ofMonomial m) ^ k := by
  simp only [toMvPoly_eq_list_sum, ofMonomial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  exact Monomial.toMvPoly_pow m k

omit [NoZeroDivisors R] [DecidableEq R] in
/-- For a single-term polynomial, `toMvPoly (ofMonomial p.terms[0]) = toMvPoly p`. -/
private theorem toMvPoly_ofMonomial_first (p : AzMvPolynomial σ R ord)
    (h : p.terms.size = 1) :
    toMvPoly (ofMonomial (p.terms[0]'(by omega))) = toMvPoly p := by
  simp only [toMvPoly_eq_list_sum, ofMonomial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  symm
  have hterms : p.terms.toList = [p.terms[0]'(by omega)] := by
    apply List.ext_getElem
    · simp [h]
    · intro i hi1 hi2; simp at hi2; subst hi2; simp
  rw [hterms]; simp

/-- Forward direction: `toMvPoly` preserves `AzMvPolynomial.pow`. -/
@[simp] theorem toMvPoly_pow (p : AzMvPolynomial σ R ord) (k : ℕ) :
    toMvPoly (AzMvPolynomial.pow p k) = toMvPoly p ^ k := by
  unfold AzMvPolynomial.pow
  split
  · next h =>
    rw [toMvPoly_pow_monomial, toMvPoly_ofMonomial_first p h]
  · next _ =>
    show toMvPoly (fastPowAux 1 p k) = _
    rw [toMvPoly_fastPowAux,
        show toMvPoly (1 : AzMvPolynomial σ R ord) = 1 from toMvPoly_one, one_mul]

/-- Backward direction: `ofMvPoly` preserves `pow`. -/
@[simp] theorem ofMvPoly_pow (q : MvPolynomial σ R) (k : ℕ) :
    AzMvPolynomial.pow (AzMvPolynomial.ofMvPoly q : AzMvPolynomial σ R ord) k =
    AzMvPolynomial.ofMvPoly (q ^ k) :=
  toMvPoly_injective (by rw [toMvPoly_pow, toMvPoly_ofMvPoly, toMvPoly_ofMvPoly])

end Azurite
