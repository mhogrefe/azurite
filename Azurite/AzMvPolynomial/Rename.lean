/-
  Renaming variables in multivariate polynomials.

  Renaming can merge monomials (when the map is not injective on the
  variables that appear), so the result must be re-sorted and collapsed.

  This implementation is fully computable (no noncomputable or sorry).
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.CompareEmbed
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Rename

namespace Azurite

open MonicMonomial Monomial MonomialOrder

/-! ### Sorting comparator -/

section Comparator

variable {R : Type _} [Semiring R]
    {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Descending comparator by monic part using `compareExponents`. -/
def monicGeq (a b : Monomial σ R ord) : Bool :=
  !(ord.compareExponents a.monic.exponents b.monic.exponents == Ordering.lt)

theorem monicGeq_iff_ge (a b : Monomial σ R ord) :
    monicGeq a b = true ↔ a.monic ≥ b.monic := by
  unfold monicGeq
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, ge_iff_le]
  constructor
  · intro h; by_contra hlt; exact h (not_le.mp hlt)
  · intro h hlt; exact absurd hlt (not_lt.mpr h)

theorem monicGeq_trans (a b c : Monomial σ R ord) :
    monicGeq a b = true → monicGeq b c = true → monicGeq a c = true := by
  rw [monicGeq_iff_ge, monicGeq_iff_ge, monicGeq_iff_ge]
  exact fun hab hbc => le_trans hbc hab

theorem monicGeq_total (a b : Monomial σ R ord) :
    (monicGeq a b || monicGeq b a) = true := by
  simp only [Bool.or_eq_true, monicGeq_iff_ge]
  exact le_total b.monic a.monic

end Comparator

/-! ### Collapsing adjacent duplicates -/

section Collapse

variable {R : Type _} [Semiring R]
    {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Process a sorted-descending list of monomials, collapsing adjacent monomials
    with equal monic parts by summing their coefficients.
    `cur` is the monic/coeff pair being accumulated, `acc` is the result so far
    (in reverse order), `rest` is the remaining input. -/
def collapseAux (cur : MonicMonomial σ ord × R)
    (acc : List (MonicMonomial σ ord × R))
    (rest : List (Monomial σ R ord)) : List (MonicMonomial σ ord × R) :=
  match rest with
  | [] => (cur :: acc).reverse
  | m :: rest' =>
    if m.monic = cur.1 then
      collapseAux (cur.1, cur.2 + m.coeff.val) acc rest'
    else
      collapseAux (m.monic, m.coeff.val) (cur :: acc) rest'
termination_by rest.length

/-- Collapse adjacent monomials with equal monic parts in a sorted list. -/
def collapseMonics (l : List (Monomial σ R ord)) :
    List (MonicMonomial σ ord × R) :=
  match l with
  | [] => []
  | m :: rest => collapseAux (m.monic, m.coeff.val) [] rest

/-! ### Proofs for collapse -/

/-- Pairwise on `.1` depends only on `.1` values, not `.2`. -/
theorem pairwise_fst_cons_update_snd
    {α β : Type _} {r : α → α → Prop}
    {a : α} {b₁ b₂ : β} {l : List (α × β)}
    (h : ((a, b₁) :: l).Pairwise (fun x y => r x.1 y.1)) :
    ((a, b₂) :: l).Pairwise (fun x y => r x.1 y.1) := by
  rw [List.pairwise_cons] at h ⊢; exact ⟨h.1, h.2⟩

/-- `collapseAux` produces a pairwise strictly-decreasing list on `.1`
    when the input satisfies the collapse invariant. -/
theorem collapseAux_pairwise
    (curM : MonicMonomial σ ord) (curC : R)
    (acc : List (MonicMonomial σ ord × R))
    (rest : List (Monomial σ R ord))
    (hacc_lt : ((curM, curC) :: acc).Pairwise (fun a b => a.1 < b.1))
    (hrest_le : ∀ m ∈ rest, m.monic ≤ curM)
    (hrest_sorted : rest.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (collapseAux (curM, curC) acc rest).Pairwise (fun a b => a.1 > b.1) := by
  induction rest generalizing curM curC acc with
  | nil =>
    simp only [collapseAux]; rwa [List.pairwise_reverse]
  | cons m rest' ih =>
    simp only [collapseAux]
    rw [List.pairwise_cons] at hrest_sorted
    split
    · next heq =>
      exact ih curM (curC + m.coeff.val) acc
        (pairwise_fst_cons_update_snd hacc_lt)
        (fun m' hm' => le_trans (hrest_sorted.1 m' hm') (heq ▸ le_refl _))
        hrest_sorted.2
    · next hne =>
      have hlt : m.monic < curM :=
        lt_of_le_of_ne (hrest_le m (List.mem_cons_self ..)) hne
      exact ih m.monic m.coeff.val ((curM, curC) :: acc)
        (by rw [List.pairwise_cons]
            exact ⟨fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hlt
              · exact lt_trans hlt ((List.pairwise_cons.mp hacc_lt).1 p hp),
              hacc_lt⟩)
        (fun m' hm' => hrest_sorted.1 m' hm')
        hrest_sorted.2

/-- `collapseMonics` on a pairwise-≥ list produces a pairwise-> list. -/
theorem collapseMonics_pairwise_gt
    {l : List (Monomial σ R ord)}
    (hsorted : l.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (collapseMonics l).Pairwise (fun a b => a.1 > b.1) := by
  match l, hsorted with
  | [], _ => exact List.Pairwise.nil
  | m :: rest, hsorted =>
    rw [List.pairwise_cons] at hsorted
    exact collapseAux_pairwise m.monic m.coeff.val [] rest
      (List.pairwise_singleton ..)
      hsorted.1
      hsorted.2

/-- `filterMap` that drops zero coefficients preserves pairwise on monic parts. -/
theorem pairwise_filterMap_gt [DecidableEq R]
    {l : List (MonicMonomial σ ord × R)}
    (hp : l.Pairwise (fun a b => a.1 > b.1)) :
    (l.filterMap (fun p =>
      if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)).Pairwise
      (fun (a : Monomial σ R ord) (b : Monomial σ R ord) => a.monic > b.monic) :=
  hp.filterMap _ (fun a a' (h : a.1 > a'.1) b hb b' hb' => by
    split at hb <;> split at hb' <;> try contradiction
    have := Option.some_injective _ hb
    have := Option.some_injective _ hb'
    subst_vars
    exact h)

end Collapse

/-! ### Sum-preservation lemmas for the pipeline -/

section SumPreservation

variable {R : Type _} [CommSemiring R] [DecidableEq R]
    {σ : Type _} {n : ℕ} [DecidableEq σ] [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- Convert a (MonicMonomial, coefficient) pair to MvPolynomial. -/
noncomputable def pairToMvPoly (p : MonicMonomial σ ord × R) :
    MvPolynomial σ R :=
  MvPolynomial.monomial p.1.toFinsupp p.2

omit [DecidableEq R] in
theorem pairToMvPoly_eq_toMvPoly (m : Monomial σ R ord) :
    pairToMvPoly (m.monic, m.coeff.val) = m.toMvPoly := by
  simp [pairToMvPoly, Monomial.toMvPoly]

omit [DecidableEq R] in
/-- `collapseAux` preserves the MvPolynomial sum:
    sum(result) = sum(acc.reverse) + pair(cur) + sum(rest). -/
theorem collapseAux_sum
    (curM : MonicMonomial σ ord) (curC : R)
    (acc : List (MonicMonomial σ ord × R))
    (rest : List (Monomial σ R ord)) :
    ((collapseAux (curM, curC) acc rest).map pairToMvPoly).sum =
    (acc.reverse.map pairToMvPoly).sum + pairToMvPoly (curM, curC) +
    (rest.map Monomial.toMvPoly).sum := by
  induction rest generalizing curM curC acc with
  | nil =>
    simp [collapseAux, List.reverse_cons, List.map_append, List.sum_append]
  | cons m rest' ih =>
    simp only [collapseAux, List.map_cons, List.sum_cons]
    split
    · next heq =>
      rw [ih]
      simp only [pairToMvPoly, Monomial.toMvPoly, heq, map_add]
      ring
    · next hne =>
      rw [ih]
      simp only [List.reverse_cons, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        pairToMvPoly_eq_toMvPoly]
      ring

omit [DecidableEq R] in
/-- `collapseMonics` preserves the MvPolynomial sum. -/
theorem collapseMonics_sum (l : List (Monomial σ R ord)) :
    ((collapseMonics l).map pairToMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  match l with
  | [] => simp [collapseMonics]
  | m :: rest =>
    simp only [collapseMonics, List.map_cons, List.sum_cons]
    rw [collapseAux_sum]
    simp [pairToMvPoly_eq_toMvPoly]

/-- Filtering out zero-coefficient pairs preserves the MvPolynomial sum
    (since `monomial s 0 = 0`). -/
theorem filterMap_sum_eq (l : List (MonicMonomial σ ord × R)) :
    ((l.filterMap (fun p =>
      if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)).map
      Monomial.toMvPoly).sum =
    (l.map pairToMvPoly).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h : p.2 = 0
    · simp [h, pairToMvPoly, MvPolynomial.monomial_zero, ih]
    · simp only [dif_neg h, List.map_cons, List.sum_cons, ← ih]
      simp [Monomial.toMvPoly, pairToMvPoly]



/-! ### The rename function -/

section Rename

variable {R : Type _} [Semiring R]
    {σ₁ : Type _} {n₁ : ℕ} [LinearOrder σ₁] [Var σ₁ n₁]
    {σ₂ : Type _} {n₂ : ℕ} [LinearOrder σ₂] [Var σ₂ n₂]
    {ord ord₂ : MonomialOrder}

/-- Rename the variables of a polynomial via a map `f : σ₁ → σ₂`.
    Non-injective maps may merge monomials (summing their coefficients)
    and cancel terms.  The result is re-sorted under `ord₂`.

    This function is fully computable: O(n log n) sort + O(n) collapse. -/
def AzMvPolynomial.rename [DecidableEq R]
    (p : AzMvPolynomial σ₁ R ord) (f : σ₁ → σ₂)
    (ord₂ : MonomialOrder := ord) : AzMvPolynomial σ₂ R ord₂ :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord₂)
  let sorted := renamed.mergeSort monicGeq
  let collapsed := collapseMonics sorted
  let terms := collapsed.filterMap (fun p =>
    if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)
  ⟨terms.toArray, by
    rw [List.toList_toArray]
    have hsorted : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
      (List.pairwise_mergeSort monicGeq_trans monicGeq_total renamed).imp
        (fun h => (monicGeq_iff_ge _ _).mp h)
    exact pairwise_filterMap_gt (collapseMonics_pairwise_gt hsorted)⟩

/-- `MonicMonomial.rename` is injective when the variable map `f` is injective.
    Since `toFin ∘ f ∘ ofFin` is injective, each source exponent maps to a
    unique target slot, so distinct exponent vectors stay distinct. -/
theorem MonicMonomial.rename_injective
    (f : σ₁ → σ₂) (hf : Function.Injective f) (ord₂ : MonomialOrder) :
    Function.Injective (fun m : MonicMonomial σ₁ ord => m.rename f ord₂) := by
  intro a b hab
  have hvec : a.exponents = b.exponents := by
    apply Vector.ext; intro idx hidx
    let i : Fin n₁ := ⟨idx, hidx⟩
    have h := congrArg (fun m : MonicMonomial σ₂ ord₂ =>
      m.exponents[Var.toFin (f (Var.ofFin i))]) hab
    simp only [MonicMonomial.rename, Vector.getElem_ofFn, Fin.getElem_fin] at h
    simp_rw [show ∀ j : Fin n₁,
      (Var.toFin (f (Var.ofFin j)) = Var.toFin (f (Var.ofFin i))) =
      (j = i) from fun j => propext ⟨
        fun h => Var.ofFin_injective (hf (Var.toFin_injective h)),
        fun h => h ▸ rfl⟩] at h
    simpa using h
  exact MonicMonomial.ext hvec

/-- Pairwise ≥ on monic parts + Nodup on monic parts → pairwise > on monic parts. -/
private theorem pairwise_gt_of_ge_monic_nodup
    {l : List (Monomial σ₂ R ord₂)}
    (hge : l.Pairwise (fun a b => a.monic ≥ b.monic))
    (hnd : (l.map Monomial.monic).Nodup) :
    l.Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hge ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    exact ⟨fun b hb => lt_of_le_of_ne (hge.1 b hb) (fun heq =>
      hnd.1 (List.mem_map.mpr ⟨b, hb, heq⟩)),
      ih hge.2 hnd.2⟩

/-- Rename variables using an injective map `f : σ₁ → σ₂`.

    Since `f` is injective, no two distinct monic monomials can merge,
    so the pipeline simplifies to just `map rename → mergeSort`
    (no collapse or zero-coefficient filter needed).

    This is more efficient than `rename` when the map is known to be injective. -/
def AzMvPolynomial.renameInjective
    (p : AzMvPolynomial σ₁ R ord) (f : σ₁ → σ₂) (hf : Function.Injective f)
    (ord₂ : MonomialOrder := ord) : AzMvPolynomial σ₂ R ord₂ :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord₂)
  let sorted := renamed.mergeSort monicGeq
  ⟨sorted.toArray, by
    rw [List.toList_toArray]
    have hge : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
      (List.pairwise_mergeSort monicGeq_trans monicGeq_total renamed).imp
        (fun h => (monicGeq_iff_ge _ _).mp h)
    -- Original monics are Nodup (pairwise > → pairwise ≠)
    have horig_monic_nodup : (p.terms.toList.map Monomial.monic).Nodup :=
      (List.pairwise_map.mpr (p.sorted.imp (fun h => ne_of_gt h)))
    -- Renamed monics are Nodup (monic ∘ rename f = rename f ∘ monic, rename f is injective)
    have hrenamed_monic_nodup : (renamed.map Monomial.monic).Nodup := by
      simp only [renamed, List.map_map, Function.comp_def, Monomial.rename]
      rw [show (fun m : Monomial σ₁ R ord => m.monic.rename f ord₂) =
            ((fun m => m.rename f ord₂) ∘ Monomial.monic) from rfl, ← List.map_map]
      exact horig_monic_nodup.map (MonicMonomial.rename_injective f hf ord₂)
    -- mergeSort preserves Nodup (it's a permutation)
    have hsorted_monic_nodup : (sorted.map Monomial.monic).Nodup :=
      ((List.mergeSort_perm _ monicGeq).map Monomial.monic).nodup_iff.mpr
        hrenamed_monic_nodup
    exact pairwise_gt_of_ge_monic_nodup hge hsorted_monic_nodup⟩

/-- Rename variables using a strictly-monotone map `f : σ₁ → σ₂`
    (at the `Fin` level: `toFin ∘ f ∘ ofFin` is `StrictMono`).

    Since the map is order-preserving, the renamed monomials are already
    in the correct order, so no merging, filtering, or sorting is needed.
    This is the most efficient rename variant. -/
def AzMvPolynomial.renameMonotone
    (p : AzMvPolynomial σ₁ R ord) (f : σ₁ → σ₂)
    (hg : StrictMono (fun i : Fin n₁ => Var.toFin (f (Var.ofFin i)))) :
    AzMvPolynomial σ₂ R ord :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord)
  ⟨renamed.toArray, by
    rw [List.toList_toArray]
    exact List.pairwise_map.mpr (p.sorted.imp (fun h =>
      MonicMonomial.rename_strictMono (ord := ord) f hg h))⟩

end Rename

variable {σ₁ : Type _} {n₁ : ℕ} [DecidableEq σ₁] [LinearOrder σ₁] [Var σ₁ n₁]
    {σ₂ : Type _} {n₂ : ℕ} [DecidableEq σ₂] [LinearOrder σ₂] [Var σ₂ n₂]

omit [DecidableEq σ₁] in
/-- The rename pipeline preserves the MvPolynomial sum:
    `toMvPoly (rename p f) = sum of (renamed monomial toMvPoly's)`. -/
theorem AzMvPolynomial.rename_toMvPoly_eq_sum
    (p : AzMvPolynomial σ₁ R ord) (f : σ₁ → σ₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly =
    (p.terms.toList.map (fun m => (m.rename f ord₂).toMvPoly)).sum := by
  -- Convert LHS toMvPoly from Array.foldl to List.sum
  simp only [AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum]
  -- Unfold rename to expose the pipeline
  unfold AzMvPolynomial.rename
  dsimp only
  -- Step 1: filterMap preserves sum (drops zero coefficients)
  rw [filterMap_sum_eq]
  -- Step 2: collapseMonics preserves sum (merges equal monic parts)
  rw [collapseMonics_sum]
  -- Step 3: mergeSort is a permutation → same sum
  rw [((List.mergeSort_perm _ monicGeq).map
    (Monomial.toMvPoly (σ := σ₂) (R := R) (ord := ord₂))).sum_eq]
  -- Compose map toMvPoly ∘ map rename into map (toMvPoly ∘ rename)
  simp only [List.map_map, Function.comp_def]

end SumPreservation

end Azurite
