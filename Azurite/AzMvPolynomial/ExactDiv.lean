/-
  Exact division for `AzMvPolynomial` (Algorithm 8.6, BPR §8.1).
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Sub
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.CompareEmbed

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial MonomialOrder

variable {n : ℕ} {ord : MonomialOrder}

/-! ### Monic monomial division -/

/-- Divide two monic monomials (subtract exponents pointwise, saturating). -/
def MonicMonomial.div (m d : MonicMonomial n ord) : MonicMonomial n ord :=
  ⟨Vector.ofFn (fun i => m.exponents[i] - d.exponents[i])⟩

@[simp] theorem MonicMonomial.div_exponents (m d : MonicMonomial n ord) :
    (MonicMonomial.div m d).exponents =
      Vector.ofFn (fun i => m.exponents[i] - d.exponents[i]) := rfl

theorem MonicMonomial.mul_div_cancel (m d : MonicMonomial n ord) :
    MonicMonomial.div (m * d) d = m := by
  ext1; simp only [MonicMonomial.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]; omega

theorem MonicMonomial.div_mul_cancel {m d : MonicMonomial n ord}
    (h : ∀ i : Fin n, d.exponents[i] ≤ m.exponents[i]) :
    d * MonicMonomial.div m d = m := by
  ext1; simp only [MonicMonomial.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  have := h ⟨i, hi⟩; simp only [Fin.getElem_fin] at this; omega

/-! ### Monomial × Polynomial product -/

variable {R : Type _} [Field R] [DecidableEq R]

/-- Multiply a polynomial by a single monomial from the left. -/
def AzMvPolynomial.monomialMul (m : Monomial n R ord) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  let terms' := p.terms.toList.map (fun t => m * t)
  ⟨terms'.toArray,
   by rw [List.toList_toArray, List.pairwise_map]
      exact p.sorted.imp (fun {a b} hab =>
        MonicMonomial.mul_gt_mul_left m.monic a.monic b.monic hab)⟩

/-! ### Exact division -/

/-- Divide a monomial by another. -/
def Monomial.exactDiv (a b : Monomial n R ord) : Monomial n R ord :=
  ⟨⟨a.coeff.val / b.coeff.val,
    div_ne_zero a.coeff.property b.coeff.property⟩,
   MonicMonomial.div a.monic b.monic⟩

/-- One step of exact division. -/
def exactDivStep (r q : AzMvPolynomial n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0) :
    Monomial n R ord × AzMvPolynomial n R ord :=
  let leadR := r.terms[0]'(by omega)
  let leadQ := q.terms[0]'(by omega)
  let t := Monomial.exactDiv leadR leadQ
  (t, r - AzMvPolynomial.monomialMul t q)

/-- Exact division loop with fuel. -/
def AzMvPolynomial.exactDivAux
    (q : AzMvPolynomial n R ord)
    (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomial n R ord → AzMvPolynomial n R ord → AzMvPolynomial n R ord
  | 0, c, _ => c
  | fuel + 1, c, r =>
    if hr : r.terms.size > 0 then
      let (t, r') := exactDivStep r q hr hq
      exactDivAux q hq fuel (c + AzMvPolynomial.ofMonomial t) r'
    else c

/-- **Algorithm 8.6 (BPR §8.1). Exact Division of Multivariate Polynomials.** -/
def AzMvPolynomial.exactDiv
    (p q : AzMvPolynomial n R ord) (hq : q.terms.size > 0) :
    AzMvPolynomial n R ord :=
  exactDivAux q hq ((p.totalDegree + 1) ^ n) 0 p

end Azurite
