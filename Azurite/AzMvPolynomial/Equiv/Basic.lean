/-
  Equivalence between AzMvPolynomial and Mathlib's MvPolynomial.
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.MonicMonomialOrder
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Fold

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

/-- The finitely-supported function representation of a `MonicMonomial` is
    independent of the monomial ordering. -/
@[simp] theorem MonicMonomial.toFinsupp_withOrder [DecidableEq σ]
    (m : MonicMonomial σ ord) (ord' : MonomialOrder) :
    (m.withOrder ord').toFinsupp = m.toFinsupp := by
  ext v; simp [MonicMonomial.toFinsupp, MonicMonomial.withOrder]

/-- Converting a monomial to `MvPolynomial` is independent of the monomial ordering. -/
@[simp] theorem Monomial.toMvPoly_withOrder [DecidableEq σ]
    (m : Monomial σ R ord) (ord' : MonomialOrder) :
    (m.withOrder ord').toMvPoly = m.toMvPoly := by
  simp [Monomial.toMvPoly, Monomial.withOrder]

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

theorem foldl_add_map_eq_sum {M α : Type _} [AddCommMonoid M]
    (f : α → M) (l : List α) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  rw [List.sum_eq_foldl, ← List.foldl_map]

/-- `toMvPoly` expressed as the sum of `toMvPoly` over the term list.
    Useful as a bridge between the `Array.foldl` definition and `List.sum`. -/
theorem AzMvPolynomial.toMvPoly_eq_list_sum
    (p : AzMvPolynomial σ R ord) :
    p.toMvPoly = (p.terms.toList.map Monomial.toMvPoly).sum := by
  simp only [AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum]

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


/-! ### Reverse round-trip helpers -/

theorem MonicMonomial.ofFinsupp_toFinsupp [DecidableEq σ] (m : MonicMonomial σ ord) :
    MonicMonomial.ofFinsupp (m.toFinsupp) = m := by
  ext; simp only [ofFinsupp, toFinsupp, Finsupp.onFinset_apply, Vector.getElem_ofFn,
    Var.toFin_ofFin]; simp

theorem MonicMonomial.toFinsupp_injective [DecidableEq σ] :
    Function.Injective (MonicMonomial.toFinsupp (σ := σ) (ord := ord)) := by
  intro a b h
  exact (ofFinsupp_toFinsupp a).symm.trans
    ((congrArg ofFinsupp h).trans (ofFinsupp_toFinsupp b))

/-- `toFinsupp` distributes over monic monomial multiplication. -/
theorem MonicMonomial.toFinsupp_mul [DecidableEq σ] (a b : MonicMonomial σ ord) :
    (a * b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  ext v; simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Finsupp.add_apply,
    MonicMonomial.mul_exponents]; simp

private theorem toMvPoly_eq_sum [DecidableEq σ] (p : AzMvPolynomial σ R ord) :
    p.toMvPoly = (p.terms.toList.map Monomial.toMvPoly).sum := by
  simp only [AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, List.sum_eq_foldl, ← List.foldl_map]

private theorem sum_map_eq_zero₂ {α M : Type _} [AddCommMonoid M]
    (l : List α) (g : α → M) (h : ∀ x ∈ l, g x = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (by simp), ih (fun x hx => h x (.tail _ hx))]

theorem list_sum_ite_eq_of_nodup_map {α β M : Type _} [AddCommMonoid M]
    [DecidableEq β] (l : List α) (g : α → β) (hnd : (l.map g).Nodup)
    (t : α) (ht : t ∈ l) (f : α → M) :
    (l.map (fun x => if g x = g t then f x else 0)).sum = f t := by
  induction l with
  | nil => simp at ht
  | cons b s ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, List.mem_cons] at ht ⊢
    obtain rfl | ht := ht
    · simp only [ite_true]
      suffices (s.map (fun x => if g x = g t then f x else 0)).sum = 0 by
        rw [this, add_zero]
      apply List.sum_eq_zero; intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [if_neg]
      exact fun heq => hnd.1
        (show g t ∈ s.map g from heq ▸ List.mem_map.mpr ⟨y, hy, rfl⟩)
    · rw [if_neg (show g b ≠ g t from fun h => hnd.1
        (show g b ∈ s.map g from h ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)),
        zero_add]
      exact ih hnd.2 ht

theorem toFinsupp_nodup [DecidableEq σ] (p : AzMvPolynomial σ R ord) :
    (p.terms.toList.map
      (fun t : Monomial σ R ord => t.monic.toFinsupp)).Nodup := by
  show (p.terms.toList.map _).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  exact p.sorted.imp fun h heq =>
    absurd (MonicMonomial.toFinsupp_injective heq) (ne_of_gt h)

theorem coeff_toMvPoly [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) (f : σ →₀ ℕ) :
    MvPolynomial.coeff f p.toMvPoly =
    (p.terms.toList.map (fun m : Monomial σ R ord =>
      if m.monic.toFinsupp = f then m.coeff.val else 0)).sum := by
  rw [toMvPoly_eq_sum]
  have h := map_list_sum (MvPolynomial.coeffAddMonoidHom (σ := σ) f)
    (p.terms.toList.map Monomial.toMvPoly)
  simp only [MvPolynomial.coeffAddMonoidHom_apply] at h
  rw [h, List.map_map]; congr 1; ext m
  simp [Monomial.toMvPoly, MvPolynomial.coeff_monomial]

theorem support_toMvPoly [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) :
    p.toMvPoly.support =
    (p.terms.toList.map
      (fun m : Monomial σ R ord => m.monic.toFinsupp)).toFinset := by
  ext f; rw [MvPolynomial.mem_support_iff, List.mem_toFinset, List.mem_map]
  constructor
  · intro hne; by_contra hall; push Not at hall
    apply hne; rw [coeff_toMvPoly]
    exact sum_map_eq_zero₂ _ _ (fun m hm => if_neg (hall m hm))
  · rintro ⟨m, hm, rfl⟩
    rw [coeff_toMvPoly,
      list_sum_ite_eq_of_nodup_map _ _ (toFinsupp_nodup p) m hm]
    exact m.coeff.property

private theorem image_ofFinsupp_support [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) :
    (p.toMvPoly.support.image MonicMonomial.ofFinsupp :
      Finset (MonicMonomial σ ord)) =
    (p.terms.toList.map
      (fun m : Monomial σ R ord => m.monic)).toFinset := by
  rw [support_toMvPoly]
  ext m; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨f, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (MonicMonomial.ofFinsupp_toFinsupp t.monic).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.monic.toFinsupp, ⟨t, ht, rfl⟩,
      MonicMonomial.ofFinsupp_toFinsupp t.monic⟩

private theorem sort_eq_of_pairwise_gt [LinearOrder α] [DecidableEq α]
    (l : List α) (hl : l.Pairwise (· > ·)) :
    l.toFinset.sort (· ≥ ·) = l := by
  have hnd : l.Nodup := hl.imp ne_of_gt
  have hsf : (l.toFinset.sort (· ≥ ·)).toFinset = l.toFinset :=
    Finset.sort_toFinset l.toFinset (· ≥ ·)
  have hsnd : (l.toFinset.sort (· ≥ ·)).Nodup :=
    Finset.sort_nodup l.toFinset (· ≥ ·)
  have hperm : (l.toFinset.sort (· ≥ ·)).Perm l := by
    rwa [List.toFinset_eq_iff_perm_dedup,
      List.Nodup.dedup hsnd, List.Nodup.dedup hnd] at hsf
  exact hperm.eq_of_pairwise
    (fun _ _ _ _ h1 h2 => le_antisymm h2 h1)
    (Finset.pairwise_sort l.toFinset (· ≥ ·))
    (hl.imp le_of_lt)

/-- `toMvPoly` is injective: the sorted representation uniquely determines
    the `MvPolynomial`. -/
theorem toMvPoly_injective [DecidableEq σ] :
    Function.Injective
      (AzMvPolynomial.toMvPoly (R := R) (σ := σ) (ord := ord)) := by
  intro ⟨at_, as_⟩ ⟨bt_, bs_⟩ hab
  simp only [AzMvPolynomial.mk.injEq]
  -- Monic lists are equal: both are the sort of the same finset
  have hmonic_eq : at_.toList.map (fun t : Monomial σ R ord => t.monic) =
      bt_.toList.map (fun t : Monomial σ R ord => t.monic) := by
    rw [← sort_eq_of_pairwise_gt _ (List.pairwise_map.mpr as_),
        ← sort_eq_of_pairwise_gt _ (List.pairwise_map.mpr bs_)]
    congr 1
    rw [← image_ofFinsupp_support ⟨at_, as_⟩,
        ← image_ofFinsupp_support ⟨bt_, bs_⟩]
    exact congr_arg _ (congr_arg _ hab)
  have hlen : at_.toList.length = bt_.toList.length := by
    have := congr_arg List.length hmonic_eq
    simpa using this
  ext1
  · simpa using hlen
  · rename_i i hi _
    rw [← Array.getElem_toList, ← Array.getElem_toList]
    have hi₂ : i < bt_.toList.length := by
      simp [Array.length_toList] at hlen ⊢; omega
    have hmi : at_.toList[i].monic = bt_.toList[i].monic := by
      have h1 : (at_.toList.map (fun t : Monomial σ R ord => t.monic))[i]'(by simp; exact hi) =
          at_.toList[i].monic := List.getElem_map ..
      have h2 : (bt_.toList.map (fun t : Monomial σ R ord => t.monic))[i]'(by simp; exact hi₂) =
          bt_.toList[i].monic := List.getElem_map ..
      rw [← h1, ← h2]; congr 1
    have ha : MvPolynomial.coeff at_.toList[i].monic.toFinsupp
        (⟨at_, as_⟩ : AzMvPolynomial σ R ord).toMvPoly =
        at_.toList[i].coeff.val := by
      rw [coeff_toMvPoly]; exact list_sum_ite_eq_of_nodup_map _ _
        (toFinsupp_nodup ⟨at_, as_⟩) _ (List.getElem_mem ..) _
    have hb : MvPolynomial.coeff bt_.toList[i].monic.toFinsupp
        (⟨bt_, bs_⟩ : AzMvPolynomial σ R ord).toMvPoly =
        bt_.toList[i].coeff.val := by
      rw [coeff_toMvPoly]; exact list_sum_ite_eq_of_nodup_map _ _
        (toFinsupp_nodup ⟨bt_, bs_⟩) _ (List.getElem_mem ..) _
    have hci : at_.toList[i].coeff = bt_.toList[i].coeff :=
      Subtype.val_injective (ha.symm.trans (by rw [hmi, hab]; exact hb))
    exact Monomial.mk.injEq .. |>.mpr ⟨hci, hmi⟩

/-- The reverse round-trip: `ofMvPoly (toMvPoly p) = p`. -/
theorem ofMvPoly_toMvPoly [DecidableEq σ] (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.ofMvPoly (AzMvPolynomial.toMvPoly p) = p :=
  toMvPoly_injective (toMvPoly_ofMvPoly p.toMvPoly)

@[simp] theorem toMvPoly_zero :
    AzMvPolynomial.toMvPoly (0 : AzMvPolynomial σ R ord) = 0 := by
  simp [AzMvPolynomial.toMvPoly]

@[simp] theorem ofMvPoly_zero [DecidableEq σ] :
    (AzMvPolynomial.ofMvPoly (ord := ord) (0 : MvPolynomial σ R)) = 0 := by
  rw [show (0 : MvPolynomial σ R) =
    AzMvPolynomial.toMvPoly (0 : AzMvPolynomial σ R ord) from toMvPoly_zero.symm]
  exact ofMvPoly_toMvPoly _

theorem one_toFinsupp :
    (MonicMonomial.one : MonicMonomial σ ord).toFinsupp = 0 := by
  ext v
  simp only [MonicMonomial.toFinsupp, MonicMonomial.one,
    Finsupp.onFinset_apply, Finsupp.zero_apply]
  exact Vector.getElem_replicate ..

@[simp] theorem toMvPoly_one [DecidableEq R] [DecidableEq σ] :
    AzMvPolynomial.toMvPoly (AzMvPolynomial.one : AzMvPolynomial σ R ord) =
      (1 : MvPolynomial σ R) := by
  simp only [AzMvPolynomial.one]
  split
  · next h =>
    simp [AzMvPolynomial.toMvPoly]
    have : (1 : MvPolynomial σ R) = 0 := by
      rw [← MvPolynomial.C_1, ← MvPolynomial.C_0, h]
    exact this.symm
  · next h =>
    simp [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMonomial,
      Monomial.toMvPoly, Monomial.one]
    have hf : (MonicMonomial.one : MonicMonomial σ ord).toFinsupp = 0 := by
      ext v; simp [MonicMonomial.toFinsupp, MonicMonomial.one, Finsupp.onFinset_apply]
    rw [show (MonicMonomial.one : MonicMonomial σ ord).toFinsupp = 0 from hf]
    exact MvPolynomial.one_def.symm

@[simp] theorem toMvPoly_C [DecidableEq R] [DecidableEq σ] (c : R) :
    AzMvPolynomial.toMvPoly (AzMvPolynomial.C c : AzMvPolynomial σ R ord) =
      MvPolynomial.C c := by
  simp only [AzMvPolynomial.C]
  split
  · next h => simp [AzMvPolynomial.toMvPoly, h]
  · next h =>
    simp [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMonomial,
          Monomial.toMvPoly]
    rw [show (MonicMonomial.one : MonicMonomial σ ord).toFinsupp = 0 from by
      ext v; simp [MonicMonomial.toFinsupp, MonicMonomial.one, Finsupp.onFinset_apply]]
    exact MvPolynomial.C_apply.symm

/-- `MonicMonomial.ofVar v` corresponds to the `Finsupp` with a single entry `v ↦ 1`. -/
theorem MonicMonomial.toFinsupp_ofVar [DecidableEq σ] (v : σ) :
    (MonicMonomial.ofVar v : MonicMonomial σ ord).toFinsupp = Finsupp.single v 1 := by
  ext w
  simp only [MonicMonomial.toFinsupp, MonicMonomial.ofVar, Finsupp.onFinset_apply,
    Finsupp.single_apply]
  simp [Vector.getElem_ofFn, Var.toFin_injective.eq_iff]

@[simp] theorem toMvPoly_X [DecidableEq R] [DecidableEq σ] (v : σ) :
    AzMvPolynomial.toMvPoly (AzMvPolynomial.X v : AzMvPolynomial σ R ord) =
      MvPolynomial.X v := by
  simp only [AzMvPolynomial.X]
  split
  · next h =>
    -- When `1 = 0` in `R`, `R` is a subsingleton and so is `MvPolynomial σ R`.
    have hR : Subsingleton R :=
      ⟨fun a b => by rw [← one_mul a, ← one_mul b, h, zero_mul, zero_mul]⟩
    exact Subsingleton.elim _ _
  · next h =>
    show (0 : MvPolynomial σ R) +
        (⟨⟨1, h⟩, MonicMonomial.ofVar v⟩ : Monomial σ R ord).toMvPoly = MvPolynomial.X v
    rw [zero_add]
    show MvPolynomial.monomial (MonicMonomial.ofVar v).toFinsupp (1 : R) = MvPolynomial.X v
    rw [MonicMonomial.toFinsupp_ofVar,
        show (MvPolynomial.X v : MvPolynomial σ R) = MvPolynomial.X v ^ 1 from (pow_one _).symm]
    exact MvPolynomial.X_pow_eq_monomial.symm

@[simp] theorem ofMvPoly_one [DecidableEq R] [DecidableEq σ] :
    (AzMvPolynomial.ofMvPoly (ord := ord) (1 : MvPolynomial σ R)) =
    (AzMvPolynomial.one : AzMvPolynomial σ R ord) := by
  rw [show (1 : MvPolynomial σ R) =
    AzMvPolynomial.toMvPoly (AzMvPolynomial.one : AzMvPolynomial σ R ord)
    from toMvPoly_one.symm]
  exact ofMvPoly_toMvPoly _

/-- The equivalence between `AzMvPolynomial σ R ord` and `MvPolynomial σ R`. -/
noncomputable def equivMvPolynomial [DecidableEq σ] :
    AzMvPolynomial σ R ord ≃ MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  invFun := AzMvPolynomial.ofMvPoly
  left_inv := ofMvPoly_toMvPoly
  right_inv := toMvPoly_ofMvPoly

/-- The number of terms equals the cardinality of the MvPolynomial support. -/
theorem numTerms_eq_support_card [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) :
    p.numTerms = p.toMvPoly.support.card := by
  rw [AzMvPolynomial.numTerms, support_toMvPoly]
  rw [List.toFinset_card_of_nodup (toFinsupp_nodup p)]
  simp [Array.length_toList]

/-- The number of terms of `ofMvPoly p` equals the cardinality of `p.support`. -/
theorem numTerms_ofMvPoly_eq_support_card [DecidableEq σ]
    (p : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ R ord).numTerms = p.support.card := by
  rw [numTerms_eq_support_card, toMvPoly_ofMvPoly]

noncomputable instance varFintype : Fintype σ :=
  Fintype.ofBijective Var.ofFin ⟨Var.ofFin_injective, fun v => ⟨Var.toFin v, Var.ofFin_toFin v⟩⟩

private def varEquiv : σ ≃ Fin n where
  toFun := Var.toFin; invFun := Var.ofFin
  left_inv := Var.ofFin_toFin; right_inv := Var.toFin_ofFin

private theorem vector_toList_sum_eq (v : Vector ℕ n) :
    v.toList.sum = ∑ i : Fin n, v[i] := by
  conv_lhs => rw [show v = Vector.ofFn (fun i => v[i]) from by ext i; simp]
  rw [Vector.toList_ofFn, List.sum_ofFn]

private theorem totalDegree_eq_toFinsupp_sum [DecidableEq σ]
    (m : MonicMonomial σ ord) :
    m.totalDegree = m.toFinsupp.sum fun _ e => e := by
  simp only [MonicMonomial.totalDegree, MonomialOrder.totalDeg, MonicMonomial.toFinsupp]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Finsupp.onFinset_apply]
  rw [Fintype.sum_equiv varEquiv _ (fun i => m.exponents[i]) (fun v => by simp [varEquiv])]
  rw [← Array.foldl_toList, ← List.sum_eq_foldl, Vector.toList_toArray]
  exact vector_toList_sum_eq m.exponents

/-- The total degree of an AzMvPolynomial equals the total degree of the
    corresponding MvPolynomial. -/
theorem totalDegree_toMvPoly [DecidableEq σ] [DecidableEq R]
    (p : AzMvPolynomial σ R ord) :
    p.totalDegree = p.toMvPoly.totalDegree := by
  simp only [AzMvPolynomial.totalDegree, MvPolynomial.totalDegree]
  rw [support_toMvPoly, ← Array.foldl_toList]
  rw [show List.foldl (fun acc (m : Monomial σ R ord) => max acc m.totalDegree) 0 p.terms.toList =
    List.foldl max 0 (p.terms.toList.map (fun m : Monomial σ R ord => m.totalDegree))
    from by rw [List.foldl_map]]
  rw [List.foldl_eq_foldr]
  rw [show (0 : ℕ) = ⊥ from rfl, show (max : ℕ → ℕ → ℕ) = (· ⊔ ·) from rfl]
  rw [List.foldr_sup_eq_sup_toFinset]
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [id]
    show m.monic.totalDegree ≤ _
    rw [totalDegree_eq_toFinsupp_sum]
    exact Finset.le_sup (f := fun s => Finsupp.sum s fun _ e => e)
      (show m.monic.toFinsupp ∈ _ by rw [List.mem_toFinset, List.mem_map]; exact ⟨m, hm, rfl⟩)
  · apply Finset.sup_le
    intro s hs
    rw [List.mem_toFinset, List.mem_map] at hs
    obtain ⟨m, hm, rfl⟩ := hs
    show (m.monic.toFinsupp.sum fun _ e => e) ≤ _
    rw [← totalDegree_eq_toFinsupp_sum]
    exact Finset.le_sup (f := @id ℕ)
      (show m.monic.totalDegree ∈ _ by rw [List.mem_toFinset, List.mem_map]; exact ⟨m, hm, rfl⟩)

/-- The total degree of `ofMvPoly p` equals the total degree of `p`. -/
theorem totalDegree_ofMvPoly [DecidableEq σ] [DecidableEq R]
    (p : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ R ord).totalDegree = p.totalDegree := by
  rw [totalDegree_toMvPoly, toMvPoly_ofMvPoly]

/-! ### withOrder preserves conversion to MvPolynomial -/

/-- Converting to `MvPolynomial` is invariant under monomial order changes:
    `withOrder` only re-sorts terms, preserving the underlying polynomial. -/
theorem toMvPoly_withOrder [DecidableEq σ]
    (p : AzMvPolynomial σ R ord) (ord' : MonomialOrder) :
    (p.withOrder ord').toMvPoly = p.toMvPoly := by
  unfold AzMvPolynomial.withOrder
  split
  · next h => subst h; rfl
  · next h =>
    simp only [AzMvPolynomial.toMvPoly]
    rw [← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray]
    set mapped := p.terms.toList.map (fun m => m.withOrder ord')
    set sorted := mapped.mergeSort _
    have hperm : sorted.Perm mapped := List.mergeSort_perm mapped _
    calc List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 sorted
        = List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 mapped :=
          hperm.foldl_eq (rcomm := ⟨fun b a₁ a₂ => by ring⟩) 0
      _ = List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 p.terms.toList := by
          simp only [mapped, List.foldl_map, Monomial.toMvPoly_withOrder]
/-- `toMvPoly` of `ofMonomials` is just the sum of the individual monomial
    conversions. Sorting doesn't affect the polynomial-level identity. -/
theorem toMvPoly_ofMonomials [DecidableEq σ]
    (ms : Array (Monomial σ R ord))
    (hdistinct : ms.toList.Pairwise (fun a b => a.monic ≠ b.monic)) :
    (AzMvPolynomial.ofMonomials ms hdistinct).toMvPoly =
      (ms.toList.map Monomial.toMvPoly).sum := by
  simp only [AzMvPolynomial.ofMonomials, AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray]
  have hperm := List.mergeSort_perm ms.toList AzMvPolynomial.monicGeq
  exact hperm.map Monomial.toMvPoly |>.sum_eq

end Azurite
