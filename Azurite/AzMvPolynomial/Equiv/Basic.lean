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

/-! ### Conversion between MonicMonomial and σ →₀ ℕ -/

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

/-- `ofFinsupp` is injective (since `toFinsupp` is a left inverse). -/
theorem MonicMonomial.ofFinsupp_injective [DecidableEq σ] :
    Function.Injective (MonicMonomial.ofFinsupp (σ := σ) (ord := ord)) := by
  intro f g h
  exact (toFinsupp_ofFinsupp f).symm.trans
    ((congrArg toFinsupp h).trans (toFinsupp_ofFinsupp g))

/-! ### Conversion between AzMvPolynomial and MvPolynomial -/

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

private theorem coeff_ne_zero_of_mem_sort [DecidableEq σ]
    (p : MvPolynomial σ R) (m : MonicMonomial σ ord)
    (hm : m ∈ (p.support.image MonicMonomial.ofFinsupp : Finset _).sort (· ≥ ·)) :
    MvPolynomial.coeff m.toFinsupp p ≠ 0 := by
  obtain ⟨g, hgs, hgm⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hm)
  rw [← hgm, MonicMonomial.toFinsupp_ofFinsupp]
  exact Finsupp.mem_support_iff.mp hgs

/-- Convert a Mathlib `MvPolynomial` to an `AzMvPolynomial` by extracting
    the support monomials, sorting them in descending monomial order,
    and pairing each with its coefficient. -/
noncomputable def AzMvPolynomial.ofMvPoly [DecidableEq σ]
    (p : MvPolynomial σ R) : AzMvPolynomial σ R ord :=
  let monics := p.support.image MonicMonomial.ofFinsupp
  let sorted := monics.sort (· ≥ ·)
  let terms := sorted.attach.map fun ⟨m, hm⟩ =>
    (⟨⟨MvPolynomial.coeff m.toFinsupp p,
       coeff_ne_zero_of_mem_sort p m hm⟩, m⟩ : Monomial σ R ord)
  ⟨terms.toArray, List.toList_toArray ▸
    List.pairwise_map.mpr ((pairwise_attach
      (pairwise_gt_of_ge_nodup (Finset.pairwise_sort monics (· ≥ ·))
        (Finset.sort_nodup monics (· ≥ ·)))).imp fun h => h)⟩

/-! ### Round-trip: toMvPoly (ofMvPoly p) = p -/

private theorem foldl_add_map_eq_sum {M α : Type _} [AddCommMonoid M]
    (f : α → M) (l : List α) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  rw [List.sum_eq_foldl, ← List.foldl_map]

/-- Summing `f` over `l.attach` is the same as summing `g` over `l`, provided
    `f ⟨x, hx⟩ = g x` for every element. -/
private theorem sum_map_attach_eq {α M : Type _} [AddCommMonoid M]
    {l : List α} (f : { x // x ∈ l } → M) (g : α → M)
    (h : ∀ (x : α) (hx : x ∈ l), f ⟨x, hx⟩ = g x) :
    (l.attach.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.attach_cons, List.map_cons, List.sum_cons]
    congr 1
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · rw [List.map_map]
      exact ih _ (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- The round-trip `toMvPoly (ofMvPoly p) = p` holds for every `MvPolynomial`. -/
theorem toMvPoly_ofMvPoly [DecidableEq σ] (p : MvPolynomial σ R) :
    AzMvPolynomial.toMvPoly (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ R ord) = p := by
  -- Unfold definitions, convert Array.foldl to List sum
  simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray, List.map_map]
  -- Convert sorted.attach.map (toMvPoly ∘ mkMonomial) sum → sorted.map sum
  rw [sum_map_attach_eq _
    (fun m => (MvPolynomial.monomial m.toFinsupp) (MvPolynomial.coeff m.toFinsupp p))
    (fun _ _ => rfl)]
  -- Convert sorted list sum → finset sum via Multiset
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  -- Switch to Finset.sum notation
  show (p.support.image MonicMonomial.ofFinsupp).sum
    (fun m => (MvPolynomial.monomial m.toFinsupp) (MvPolynomial.coeff m.toFinsupp p)) = p
  -- Push sum through image via injectivity of ofFinsupp
  rw [Finset.sum_image (fun a _ b _ h => MonicMonomial.ofFinsupp_injective h)]
  -- Simplify toFinsupp ∘ ofFinsupp = id
  simp only [MonicMonomial.toFinsupp_ofFinsupp]
  -- Conclude: ∑ v ∈ p.support, monomial v (coeff v p) = p
  exact MvPolynomial.support_sum_monomial_coeff p

end Azurite
