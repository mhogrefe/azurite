/-
  `MonicMonomial σ` wrappers for the vector-level embedding and
  translation-invariance lemmas.  The vector-level content now lives in
  `Azurite.AzMvPolynomial.New.CompareEmbed`; this file only lifts it to
  the legacy `[Var σ n]`-polymorphic `MonicMonomial σ`.
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.New.CompareEmbed

namespace Azurite
open MonomialOrder

section RenameStrictMono

variable {σ₁ : Type _} {n₁' : ℕ} [LinearOrder σ₁] [v₁ : Var σ₁ n₁']
variable {σ₂ : Type _} {n₂' : ℕ} [LinearOrder σ₂] [v₂ : Var σ₂ n₂']
variable {ord : MonomialOrder}

/-- The exponents of a renamed monomial are `embedVec g` of the original exponents,
    where `g i = Var.toFin (f (Var.ofFin i))`. -/
theorem MonicMonomial.rename_exponents_eq
    (m : MonicMonomial σ₁ ord) (f : σ₁ → σ₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).exponents =
    embedVec (fun i : Fin n₁' => v₂.toFin (f (v₁.ofFin i))) m.exponents := rfl

/-- If the Fin-level map `toFin ∘ f ∘ ofFin` is strictly monotone, renaming
    preserves the monomial comparison (with the same ordering on both sides). -/
theorem MonicMonomial.rename_compare
    (m₁ m₂ : MonicMonomial σ₁ ord) (f : σ₁ → σ₂)
    (hg : StrictMono (fun i : Fin n₁' => v₂.toFin (f (v₁.ofFin i)))) :
    compare (m₁.rename f ord) (m₂.rename f ord) = compare m₁ m₂ := by
  show ord.compareExponents (m₁.rename f ord).exponents (m₂.rename f ord).exponents =
    ord.compareExponents m₁.exponents m₂.exponents
  simp only [rename_exponents_eq]
  exact compareExponents_embedVec _ hg ord _ _

/-- If the Fin-level map induced by `f` is strictly monotone,
    `MonicMonomial.rename f` is strictly monotone. -/
theorem MonicMonomial.rename_strictMono
    (f : σ₁ → σ₂)
    (hg : StrictMono (fun i : Fin n₁' => v₂.toFin (f (v₁.ofFin i)))) :
    StrictMono (fun m : MonicMonomial σ₁ ord => m.rename f ord) := by
  intro m₁ m₂ hlt
  show compare (m₁.rename f ord) (m₂.rename f ord) = .lt
  rw [rename_compare m₁ m₂ f hg]
  exact hlt

end RenameStrictMono

section MulLeft

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Left multiplication by a fixed monic monomial preserves strict ordering. -/
theorem MonicMonomial.mul_lt_mul_left (c a b : MonicMonomial σ ord)
    (h : a < b) : c * a < c * b := by
  show compareExponents ord (c * a).exponents (c * b).exponents = .lt
  simp only [mul_exponents]
  rw [show (Vector.ofFn fun i => c.exponents[i] + a.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + a.exponents[↑i]) from rfl,
      show (Vector.ofFn fun i => c.exponents[i] + b.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + b.exponents[↑i]) from rfl]
  rw [MonomialOrder.compareExponents_add_left]; exact h

/-- Left multiplication by a fixed monic monomial preserves strict ordering (gt). -/
theorem MonicMonomial.mul_gt_mul_left (c a b : MonicMonomial σ ord)
    (h : a > b) : c * a > c * b :=
  mul_lt_mul_left c b a h

end MulLeft

end Azurite
