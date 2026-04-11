/-
  Exact division for `AzMvPolynomialNew` (Algorithm 8.6, BPR §8.1).
-/
import Azurite.AzMvPolynomial.New.Add
import Azurite.AzMvPolynomial.New.Sub
import Azurite.AzMvPolynomial.New.Mul
import Azurite.AzMvPolynomial.New.CompareEmbed

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew MonomialOrder

variable {n : ℕ} {ord : MonomialOrder}

/-! ### Monic monomial division -/

/-- Divide two monic monomials (subtract exponents pointwise, saturating). -/
def MonicMonomialNew.div (m d : MonicMonomialNew n ord) : MonicMonomialNew n ord :=
  ⟨Vector.ofFn (fun i => m.exponents[i] - d.exponents[i])⟩

@[simp] theorem MonicMonomialNew.div_exponents (m d : MonicMonomialNew n ord) :
    (MonicMonomialNew.div m d).exponents =
      Vector.ofFn (fun i => m.exponents[i] - d.exponents[i]) := rfl

theorem MonicMonomialNew.mul_div_cancel (m d : MonicMonomialNew n ord) :
    MonicMonomialNew.div (m * d) d = m := by
  ext1; simp only [MonicMonomialNew.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]; omega

theorem MonicMonomialNew.div_mul_cancel {m d : MonicMonomialNew n ord}
    (h : ∀ i : Fin n, d.exponents[i] ≤ m.exponents[i]) :
    d * MonicMonomialNew.div m d = m := by
  ext1; simp only [MonicMonomialNew.div, mul_exponents]
  ext i hi; simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  have := h ⟨i, hi⟩; simp only [Fin.getElem_fin] at this; omega

/-! ### Monomial × Polynomial product -/

variable {R : Type _} [Field R] [DecidableEq R]

/-- Multiply a polynomial by a single monomial from the left. -/
def AzMvPolynomialNew.monomialMul (m : MonomialNew n R ord) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  let terms' := p.terms.toList.map (fun t => m * t)
  ⟨terms'.toArray,
   by rw [List.toList_toArray, List.pairwise_map]
      exact p.sorted.imp (fun {a b} hab =>
        MonicMonomialNew.mul_gt_mul_left m.monic a.monic b.monic hab)⟩

/-! ### Exact division -/

/-- Divide a monomial by another. -/
def MonomialNew.exactDiv (a b : MonomialNew n R ord) : MonomialNew n R ord :=
  ⟨⟨a.coeff.val / b.coeff.val,
    div_ne_zero a.coeff.property b.coeff.property⟩,
   MonicMonomialNew.div a.monic b.monic⟩

/-- One step of exact division. -/
def exactDivStepNew (r q : AzMvPolynomialNew n R ord)
    (hr : r.terms.size > 0) (hq : q.terms.size > 0) :
    MonomialNew n R ord × AzMvPolynomialNew n R ord :=
  let leadR := r.terms[0]'(by omega)
  let leadQ := q.terms[0]'(by omega)
  let t := MonomialNew.exactDiv leadR leadQ
  (t, r - AzMvPolynomialNew.monomialMul t q)

/-- Exact division loop with fuel. -/
def AzMvPolynomialNew.exactDivAux
    (q : AzMvPolynomialNew n R ord)
    (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomialNew n R ord → AzMvPolynomialNew n R ord → AzMvPolynomialNew n R ord
  | 0, c, _ => c
  | fuel + 1, c, r =>
    if hr : r.terms.size > 0 then
      let (t, r') := exactDivStepNew r q hr hq
      exactDivAux q hq fuel (c + AzMvPolynomialNew.ofMonomial t) r'
    else c

/-- **Algorithm 8.6 (BPR §8.1). Exact Division of Multivariate Polynomials.** -/
def AzMvPolynomialNew.exactDiv
    (p q : AzMvPolynomialNew n R ord) (hq : q.terms.size > 0) :
    AzMvPolynomialNew n R ord :=
  exactDivAux q hq ((p.totalDegree + 1) ^ n) 0 p

end Azurite
