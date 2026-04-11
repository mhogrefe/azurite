import Azurite.AzMvPolynomial.New.Pow
import Azurite.AzMvPolynomial.New.Equiv.Mul

/-!
# Equivalence: `AzMvPolynomialNew.pow` ↔ `MvPolynomial.pow`

Proves that `AzMvPolynomialNew.pow p k` (computable, with single-monomial
optimization and binary exponentiation fallback) agrees with Mathlib's
`MvPolynomial` power.
-/

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level `toFinsupp` / `toMvPoly` preservation of `pow` -/

/-- `toFinsupp` preserves `MonicMonomialNew.pow`:
    `toFinsupp (m.pow k) = k • toFinsupp m`. -/
theorem MonicMonomialNew.toFinsupp_pow (m : MonicMonomialNew n ord) (k : ℕ) :
    (m.pow k).toFinsupp = k • m.toFinsupp := by
  rw [MonicMonomialNew.pow_eq_npow]
  induction k with
  | zero =>
    simp only [pow_zero, zero_smul]
    show MonicMonomialNew.toFinsupp (1 : MonicMonomialNew n ord) = 0
    ext v
    simp [MonicMonomialNew.toFinsupp, Finsupp.onFinset_apply,
          MonicMonomialNew.one_exponents, Vector.getElem_replicate]
  | succ k ih => rw [pow_succ, MonicMonomialNew.toFinsupp_mul, ih, succ_nsmul]

omit [DecidableEq R] in
/-- `toMvPoly` preserves `MonomialNew.pow`:
    `(m.pow k).toMvPoly = m.toMvPoly ^ k`. -/
theorem MonomialNew.toMvPoly_pow (m : MonomialNew n R ord) (k : ℕ) :
    (m.pow k).toMvPoly = m.toMvPoly ^ k := by
  simp only [MonomialNew.toMvPoly, MonomialNew.pow, MonicMonomialNew.toFinsupp_pow,
             MvPolynomial.monomial_pow]

/-! ### AzMvPolynomialNew.pow equivalence -/

/-- `toMvPoly` distributes over `fastPowAux` (the tail-recursive binary
    exponentiation helper). -/
private theorem toMvPoly_fastPowAux_new
    (acc base : AzMvPolynomialNew n R ord) (k : ℕ) :
    (fastPowAux acc base k).toMvPoly =
    acc.toMvPoly * base.toMvPoly ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | _ k ih =>
    unfold fastPowAux; split
    · rename_i h; subst h; simp
    · rename_i h; split
      · rename_i heven
        rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)),
            toMvPoly_mul_new, ← sq, ← pow_mul]; congr 2; omega
      · rename_i hodd
        rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)),
            toMvPoly_mul_new, toMvPoly_mul_new, mul_assoc,
            ← sq, ← pow_mul, ← pow_succ']; congr 2; omega

omit [DecidableEq R] in
/-- Exponentiating a single monomial and wrapping gives the correct `toMvPoly`. -/
private theorem toMvPoly_pow_monomial_new (m : MonomialNew n R ord) (k : ℕ) :
    (AzMvPolynomialNew.ofMonomial (MonomialNew.pow m k)).toMvPoly =
    (AzMvPolynomialNew.ofMonomial m).toMvPoly ^ k := by
  simp only [AzMvPolynomialNew.toMvPoly_eq_list_sum, AzMvPolynomialNew.ofMonomial,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact MonomialNew.toMvPoly_pow m k

omit [NoZeroDivisors R] [DecidableEq R] in
/-- For a single-term polynomial, `toMvPoly (ofMonomial p.terms[0]) = toMvPoly p`. -/
private theorem toMvPoly_ofMonomial_first_new (p : AzMvPolynomialNew n R ord)
    (h : p.terms.size = 1) :
    (AzMvPolynomialNew.ofMonomial (p.terms[0]'(by omega))).toMvPoly = p.toMvPoly := by
  simp only [AzMvPolynomialNew.toMvPoly_eq_list_sum, AzMvPolynomialNew.ofMonomial,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  symm
  have hterms : p.terms.toList = [p.terms[0]'(by omega)] := by
    apply List.ext_getElem
    · simp [h]
    · intro i hi1 hi2; simp at hi2; subst hi2; simp
  rw [hterms]; simp

/-- Forward direction: `toMvPoly` preserves `AzMvPolynomialNew.pow`. -/
@[simp] theorem toMvPoly_pow_new (p : AzMvPolynomialNew n R ord) (k : ℕ) :
    (AzMvPolynomialNew.pow p k).toMvPoly = p.toMvPoly ^ k := by
  unfold AzMvPolynomialNew.pow
  split
  · next h =>
    rw [toMvPoly_pow_monomial_new, toMvPoly_ofMonomial_first_new p h]
  · next _ =>
    show (fastPowAux 1 p k).toMvPoly = _
    rw [toMvPoly_fastPowAux_new,
        show (1 : AzMvPolynomialNew n R ord).toMvPoly = 1 from toMvPoly_one_new, one_mul]

/-- Backward direction: `ofMvPoly` preserves `pow`. -/
@[simp] theorem ofMvPoly_pow_new (q : MvPolynomial (Fin n) R) (k : ℕ) :
    AzMvPolynomialNew.pow (AzMvPolynomialNew.ofMvPoly q : AzMvPolynomialNew n R ord) k =
    AzMvPolynomialNew.ofMvPoly (q ^ k) :=
  toMvPoly_injective_new
    (by rw [toMvPoly_pow_new, toMvPoly_ofMvPoly_new, toMvPoly_ofMvPoly_new])

end Azurite
