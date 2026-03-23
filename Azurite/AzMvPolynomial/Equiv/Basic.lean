/-
  Equivalence between AzMvPolynomial and Mathlib's MvPolynomial.
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.MonicMonomialOrder
import Mathlib.Algebra.MvPolynomial.Basic

namespace Azurite

open MvPolynomial MonicMonomial Monomial MonomialOrder

variable {R : Type _} [CommSemiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Convert a monic monomial's exponent vector to a finitely-supported function `σ →₀ ℕ`.
    Each variable `Var.ofFin i` is mapped to `exponents[i]`; all other values (if any)
    are `0` by construction. -/
noncomputable def MonicMonomial.toFinsupp [DecidableEq σ]
    (m : MonicMonomial σ ord) : σ →₀ ℕ :=
  Finsupp.onFinset (Finset.image Var.ofFin Finset.univ)
    (fun v => m.exponents[Var.toFin v])
    (fun v hv => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Var.toFin v, Var.ofFin_toFin v⟩)

/-- Convert `σ →₀ ℕ` to a `MonicMonomial` by reading off each variable's exponent. -/
noncomputable def MonicMonomial.ofFinsupp [DecidableEq σ]
    (f : σ →₀ ℕ) : MonicMonomial σ ord :=
  ⟨Vector.ofFn fun i => f (Var.ofFin i)⟩

/-- Round-trip: `toFinsupp (ofFinsupp f) = f`. -/
theorem MonicMonomial.toFinsupp_ofFinsupp [DecidableEq σ] (f : σ →₀ ℕ) :
    (MonicMonomial.ofFinsupp f : MonicMonomial σ ord).toFinsupp = f := by
  ext v; simp only [toFinsupp, ofFinsupp, Finsupp.onFinset_apply]
  simp [Vector.getElem_ofFn, Var.ofFin_toFin]

/-- Convert a single monomial to a Mathlib `MvPolynomial`. -/
noncomputable def Monomial.toMvPoly [DecidableEq σ]
    (m : Monomial σ R ord) : MvPolynomial σ R :=
  MvPolynomial.monomial m.monic.toFinsupp m.coeff.val

/-- Convert an `AzMvPolynomial` to a Mathlib `MvPolynomial` by summing
    the contributions of each monomial term. -/
noncomputable def AzMvPolynomial.toMvPoly [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) : MvPolynomial σ R :=
  p.terms.foldl (· + ·.toMvPoly) 0

/-! ### Helpers for ofMvPoly -/

private theorem pairwise_gt_of_ge_nodup [LinearOrder α]
    {l : List α} (hp : l.Pairwise (· ≥ ·)) (hnd : l.Nodup) :
    l.Pairwise (· > ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp ⊢; rw [List.nodup_cons] at hnd
    exact ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (fun h => hnd.1 (h ▸ hb)),
           ih hp.2 hnd.2⟩

private theorem pairwise_attach {α : Type _} {r : α → α → Prop} {l : List α}
    (h : l.Pairwise r) : l.attach.Pairwise (fun a b => r a.val b.val) := by
  rw [List.pairwise_iff_getElem] at h ⊢
  intro i j hi hj hij
  simp only [List.length_attach] at hi hj
  simp only [List.getElem_attach]
  exact h i j hi hj hij

/-- Convert a Mathlib `MvPolynomial` to an `AzMvPolynomial` by extracting
    the support monomials, sorting them in descending monomial order,
    and pairing each with its coefficient. -/
noncomputable def AzMvPolynomial.ofMvPoly [DecidableEq σ]
    (p : MvPolynomial σ R) : AzMvPolynomial σ R ord := by
  let monics : Finset (MonicMonomial σ ord) :=
    p.support.image MonicMonomial.ofFinsupp
  let sorted := monics.sort (· ≥ ·)
  have hsorted_gt : sorted.Pairwise (· > ·) :=
    pairwise_gt_of_ge_nodup
      (Finset.pairwise_sort monics (· ≥ ·))
      (Finset.sort_nodup monics (· ≥ ·))
  let f : { m // m ∈ sorted } → Monomial σ R ord := fun ⟨m, hm⟩ =>
    ⟨⟨MvPolynomial.coeff m.toFinsupp p, by
        obtain ⟨g, hgs, hgm⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hm)
        rw [← hgm, MonicMonomial.toFinsupp_ofFinsupp]
        exact Finsupp.mem_support_iff.mp hgs⟩, m⟩
  let terms := sorted.attach.map f
  refine ⟨terms.toArray, ?_⟩
  rw [List.toList_toArray]
  show terms.Pairwise (fun a b => a.monic > b.monic)
  rw [List.pairwise_map]
  exact (pairwise_attach hsorted_gt).imp (fun h => h)

end Azurite
