/-
  `MonicMonomialNew`-specific strict-monotonicity and multiplication-preservation
  lemmas, built on top of the vector-level lemmas from the old
  `Azurite.AzMvPolynomial.CompareEmbed` (those are variable-type independent).
-/
import Azurite.AzMvPolynomial.CompareEmbed
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open MonomialOrder

variable {n₁ n₂ : ℕ} {ord : MonomialOrder}

/-- The exponents of a renamed `MonicMonomialNew` match `embedVec g`. -/
theorem MonicMonomialNew.rename_exponents_eq
    (m : MonicMonomialNew n₁ ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).exponents = embedVec f m.exponents := rfl

/-- If `f : Fin n₁ → Fin n₂` is strictly monotone, renaming preserves the
    monomial comparison. -/
theorem MonicMonomialNew.rename_compare
    (m₁ m₂ : MonicMonomialNew n₁ ord) (f : Fin n₁ → Fin n₂)
    (hg : StrictMono f) :
    compare (m₁.rename f ord) (m₂.rename f ord) = compare m₁ m₂ := by
  show ord.compareExponents (m₁.rename f ord).exponents (m₂.rename f ord).exponents =
    ord.compareExponents m₁.exponents m₂.exponents
  simp only [rename_exponents_eq]
  exact compareExponents_embedVec _ hg ord _ _

/-- `MonicMonomialNew.rename f` is strictly monotone if `f` is. -/
theorem MonicMonomialNew.rename_strictMono (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    StrictMono (fun m : MonicMonomialNew n₁ ord => m.rename f ord) := by
  intro m₁ m₂ hlt
  show compare (m₁.rename f ord) (m₂.rename f ord) = .lt
  rw [rename_compare m₁ m₂ f hg]
  exact hlt

variable {n : ℕ}

/-- Left multiplication by a fixed monic monomial preserves strict ordering. -/
theorem MonicMonomialNew.mul_lt_mul_left (c a b : MonicMonomialNew n ord)
    (h : a < b) : c * a < c * b := by
  show compareExponents ord (c * a).exponents (c * b).exponents = .lt
  simp only [MonicMonomialNew.mul_exponents]
  rw [show (Vector.ofFn fun i => c.exponents[i] + a.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + a.exponents[↑i]) from rfl,
      show (Vector.ofFn fun i => c.exponents[i] + b.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + b.exponents[↑i]) from rfl]
  rw [MonomialOrder.compareExponents_add_left]; exact h

/-- Left multiplication by a fixed monic monomial preserves strict ordering (gt). -/
theorem MonicMonomialNew.mul_gt_mul_left (c a b : MonicMonomialNew n ord)
    (h : a > b) : c * a > c * b :=
  mul_lt_mul_left c b a h

end Azurite
