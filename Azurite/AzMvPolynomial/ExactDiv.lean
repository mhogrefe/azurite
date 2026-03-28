/-
  Algorithm 8.6. [Exact Division of Multivariate Polynomials]

  Given multivariate polynomials P and Q over a field K in k variables,
  where Q divides P, compute C such that P = C * Q.

  Procedure:
  - Initialization: C := 0, R := P.
  - While R ≠ 0:
      Let m, n be the leading monomials of R and Q.
      Since Q | P, n divides m.
      Let a_m, b_n be the coefficients of m and n in R and Q.
        C := C + (a_m / b_n) · (m / n)
        R := R − (a_m / b_n) · (m / n) · Q
  - Output C.

  Proof of correctness (informal):
    The equality P = C * Q + R is maintained throughout.
    Since Q divides P, Q divides R.
    The algorithm terminates with R = 0, because the leading monomial of R
    decreases strictly for the monomial ordering in each iteration.
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Sub
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.CompareEmbed

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial MonomialOrder

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-! ### Monic monomial division -/

/-- Divide two monic monomials (subtract exponents pointwise).
    Assumes `d` divides `m`, i.e. each exponent of `d` is `≤` the
    corresponding exponent of `m`. Uses saturating subtraction. -/
def MonicMonomial.div (m d : MonicMonomial σ ord) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => m.exponents[i] - d.exponents[i])⟩

@[simp] theorem MonicMonomial.div_exponents (m d : MonicMonomial σ ord) :
    (MonicMonomial.div m d).exponents =
      Vector.ofFn (fun i => m.exponents[i] - d.exponents[i]) := rfl

/-- `(m * d) / d = m`. -/
theorem MonicMonomial.mul_div_cancel (m d : MonicMonomial σ ord) :
    MonicMonomial.div (m * d) d = m := by
  ext1; simp only [MonicMonomial.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]; omega

/-- `d * (m / d) = m` when `d` divides `m`. -/
theorem MonicMonomial.div_mul_cancel {m d : MonicMonomial σ ord}
    (h : ∀ i : Fin n, d.exponents[i] ≤ m.exponents[i]) :
    d * MonicMonomial.div m d = m := by
  ext1; simp only [MonicMonomial.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  have := h ⟨i, hi⟩; simp only [Fin.getElem_fin] at this; omega

/-! ### Monomial × Polynomial product -/

variable {R : Type _} [Field R] [DecidableEq R]

/-- Multiply a polynomial by a single monomial from the left.
    Since left-multiplication preserves the ordering of monic parts,
    the result is already sorted.  This is more efficient than full
    polynomial multiplication. -/
def AzMvPolynomial.monomialMul (m : Monomial σ R ord) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  let terms' := p.terms.toList.map (fun t => m * t)
  ⟨terms'.toArray,
   by rw [List.toList_toArray, List.pairwise_map]
      exact p.sorted.imp (fun {a b} hab =>
        MonicMonomial.mul_gt_mul_left m.monic a.monic b.monic hab)⟩

/-! ### Exact division -/

/-- Divide a monomial by another (coefficients and monic parts).
    Over a field, division of nonzero coefficients is always nonzero. -/
def Monomial.exactDiv (a b : Monomial σ R ord) : Monomial σ R ord :=
  ⟨⟨a.coeff.val / b.coeff.val,
    div_ne_zero a.coeff.property b.coeff.property⟩,
   MonicMonomial.div a.monic b.monic⟩

/-- One step of exact division: given remainder `r` and divisor `q`
    (both nonzero), compute the quotient monomial
    `t = leadTerm(r) / leadTerm(q)` and the new remainder `r - t * q`. -/
def exactDivStep (r q : AzMvPolynomial σ R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0) :
    Monomial σ R ord × AzMvPolynomial σ R ord :=
  let leadR := r.terms[0]'(by omega)
  let leadQ := q.terms[0]'(by omega)
  let t := Monomial.exactDiv leadR leadQ
  (t, r - AzMvPolynomial.monomialMul t q)

/-- Exact division loop with fuel.

    Maintains the invariant `P = C * Q + R` and terminates when `R = 0`.
    Fuel should be at least `P.numTerms` (the leading monomial of `R`
    strictly decreases at each step). -/
def AzMvPolynomial.exactDivAux
    (q : AzMvPolynomial σ R ord)
    (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomial σ R ord → AzMvPolynomial σ R ord → AzMvPolynomial σ R ord
  | 0, c, _ => c  -- fuel exhausted
  | fuel + 1, c, r =>
    if hr : r.terms.size > 0 then
      let (t, r') := exactDivStep r q hr hq
      exactDivAux q hq fuel (c + AzMvPolynomial.ofMonomial t) r'
    else c  -- R = 0; done

/-- **Algorithm 8.6 (BPR §8.1). Exact Division of Multivariate Polynomials.**

    Given `P` and nonzero `Q` where `Q ∣ P` in `K[X₁, …, Xₖ]`,
    computes `C` such that `P = C * Q`.

    Uses as fuel `P.numTerms + 1`, since each iteration strictly
    decreases the leading monomial of the remainder. -/
def AzMvPolynomial.exactDiv
    (p q : AzMvPolynomial σ R ord) (hq : q.terms.size > 0) :
    AzMvPolynomial σ R ord :=
  exactDivAux q hq (p.numTerms + 1) 0 p

end Azurite
