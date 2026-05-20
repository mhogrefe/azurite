import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_18

/-!
# BPR Theorem 4.17: resultant as a product of root differences

For polynomials `P, Q : K[X]` over a field `K` that both split over `K`,
with factorizations

  `P = a_p · ∏_{i=1}^p (X - x_i)`,
  `Q = b_q · ∏_{j=1}^q (X - y_j)`,

the resultant is the (signed, scaled) product of all root differences:

  `Res(P, Q) = a_p^q · b_q^p · ∏_{i, j} (x_i - y_j)`.

Combined with the BPR definition `Θ(P, Q) := a_p^q b_q^p ∏(x_i - y_j)`
(introduced in Lemma 4.18), this is exactly `Res(P, Q) = Θ(P, Q)`.

## Strategy

The Mathlib lemma `Polynomial.resultant_eq_prod_eval` already gives the
asymmetric form
`resultant P Q P.natDegree q = P.leadingCoeff^q · ∏_{x ∈ P.roots} Q.eval x`
(for `P.Splits` and `Q.natDegree ≤ q`). We bridge our `Res` to Mathlib's
`resultant` and then expand each `Q.eval x = b_q · ∏_y (x - y)` (using
`Polynomial.Splits.eval_eq_prod_roots`), then collapse the resulting
double product over `P.roots × Q.roots` with
`Multiset.prod_map_product_eq_prod_prod`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K]

/-- Helper: when `Q` splits, the product `∏_{x ∈ P.roots} Q.eval x`
    expands as `Q.leadingCoeff^|P.roots| · ∏_{(x, y)} (x - y)` over
    `P.roots ×ˢ Q.roots`. -/
private lemma prod_eval_eq_leadingCoeff_pow_mul_prod_root_diffs
    (P Q : K[X]) (hQ : Q.Splits) :
    (P.roots.map Q.eval).prod =
      Q.leadingCoeff ^ P.roots.card *
        ((P.roots ×ˢ Q.roots).map fun pr => pr.1 - pr.2).prod := by
  -- Replace `Q.eval x` with the split form `Q.leadingCoeff · ∏_y (x - y)`.
  conv_lhs => rw [show P.roots.map Q.eval =
      P.roots.map (fun x => Q.leadingCoeff * (Q.roots.map (fun y => x - y)).prod) from
      Multiset.map_congr rfl (fun x _ => hQ.eval_eq_prod_roots x)]
  -- Pull the constant out of the outer product.
  rw [Multiset.prod_map_mul]
  rw [show P.roots.map (fun (_ : K) => Q.leadingCoeff) =
      P.roots.map (Function.const K Q.leadingCoeff) from rfl]
  rw [Multiset.map_const, Multiset.prod_replicate]
  -- Collapse the nested product over `P.roots × Q.roots` to a single product.
  congr 1
  exact (Multiset.prod_map_product_eq_prod_prod P.roots Q.roots
    (fun pr : K × K => pr.1 - pr.2)).symm

/-- **BPR Theorem 4.17.** For polynomials `P, Q : K[X]` that both split
    over a field `K`, with factorizations `P = a_p · ∏ (X - x_i)` and
    `Q = b_q · ∏ (X - y_j)`,

      `Res(P, Q) = a_p^q · b_q^p · ∏_{i, j} (x_i - y_j)`,

    where the products run over `P.roots × Q.roots`. -/
theorem Theorem_4_17 (P Q : K[X]) (hP : P.Splits) (hQ : Q.Splits) :
    Res P P.natDegree Q Q.natDegree =
      P.leadingCoeff ^ Q.natDegree * Q.leadingCoeff ^ P.natDegree *
        ((P.roots ×ˢ Q.roots).map fun pr => pr.1 - pr.2).prod := by
  rw [Res_eq_resultant P Q P.natDegree Q.natDegree le_rfl le_rfl]
  rw [Polynomial.resultant_eq_prod_eval P Q Q.natDegree le_rfl hP]
  rw [prod_eval_eq_leadingCoeff_pow_mul_prod_root_diffs P Q hQ]
  rw [hP.natDegree_eq_card_roots]
  ring

/-- **Corollary:** `Res = Θ` once `P` splits.
    With `Θ(P, Q) = a_p^q · ∏_{x ∈ P.roots} Q.eval(x)` (Lemma 4.18's
    asymmetric definition), the BPR-promised identification `Res = Θ`
    holds as soon as `P` splits over `K` — `Q` need not split, because
    the asymmetric form only references roots of the first argument. -/
theorem Res_eq_Θ_of_splits (P Q : K[X]) (hP : P.Splits) :
    Res P P.natDegree Q Q.natDegree = Θ P Q Q.natDegree := by
  rw [Res_eq_resultant P Q P.natDegree Q.natDegree le_rfl le_rfl,
      ← Θ_eq_resultant P Q Q.natDegree hP le_rfl]

end Azurite.BPR.Chapter4
