/-
  Equivalence between `AzMvPolynomialNew` and Mathlib's `MvPolynomial (Fin n) R`.
-/
import Azurite.AzMvPolynomial.New.Basic
import Azurite.AzMvPolynomial.New.MonicMonomialProofs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Fold

namespace Azurite

open MvPolynomial MonicMonomialNew MonomialNew MonomialOrder AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

/-! ### Conversion between MonicMonomialNew and `Fin n →₀ ℕ` -/

/-- Convert a monic monomial's exponent vector to a finitely-supported
    function `Fin n →₀ ℕ`. -/
noncomputable def MonicMonomialNew.toFinsupp
    (m : MonicMonomialNew n ord) : Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => m.exponents[i]) (fun _ _ => Finset.mem_univ _)

/-- Convert `Fin n →₀ ℕ` to a `MonicMonomialNew`. -/
noncomputable def MonicMonomialNew.ofFinsupp
    (f : Fin n →₀ ℕ) : MonicMonomialNew n ord :=
  ⟨Vector.ofFn fun i => f i⟩

/-- Round-trip: `toFinsupp (ofFinsupp f) = f`. -/
theorem MonicMonomialNew.toFinsupp_ofFinsupp (f : Fin n →₀ ℕ) :
    (MonicMonomialNew.ofFinsupp f : MonicMonomialNew n ord).toFinsupp = f := by
  ext i; simp [toFinsupp, ofFinsupp]

/-- `ofFinsupp` is injective (since `toFinsupp` is a left inverse). -/
theorem MonicMonomialNew.ofFinsupp_injective :
    Function.Injective (MonicMonomialNew.ofFinsupp (n := n) (ord := ord)) := by
  intro f g h
  exact (toFinsupp_ofFinsupp f).symm.trans
    ((congrArg toFinsupp h).trans (toFinsupp_ofFinsupp g))

/-! ### Conversion between AzMvPolynomialNew and MvPolynomial -/

/-- Convert a single monomial to a Mathlib `MvPolynomial`. -/
noncomputable def MonomialNew.toMvPoly
    (m : MonomialNew n R ord) : MvPolynomial (Fin n) R :=
  MvPolynomial.monomial m.monic.toFinsupp m.coeff.val

/-- The finsupp representation of a `MonicMonomialNew` is independent of ordering. -/
@[simp] theorem MonicMonomialNew.toFinsupp_withOrder
    (m : MonicMonomialNew n ord) (ord' : MonomialOrder) :
    (m.withOrder ord').toFinsupp = m.toFinsupp := by
  ext v; simp [MonicMonomialNew.toFinsupp, MonicMonomialNew.withOrder]

/-- Converting a monomial to `MvPolynomial` is independent of the monomial ordering. -/
@[simp] theorem MonomialNew.toMvPoly_withOrder
    (m : MonomialNew n R ord) (ord' : MonomialOrder) :
    (m.withOrder ord').toMvPoly = m.toMvPoly := by
  simp [MonomialNew.toMvPoly, MonomialNew.withOrder]

/-- Convert an `AzMvPolynomialNew` to a Mathlib `MvPolynomial` by summing
    the contributions of each monomial term. -/
noncomputable def AzMvPolynomialNew.toMvPoly
    (p : AzMvPolynomialNew n R ord) : MvPolynomial (Fin n) R :=
  p.terms.foldl (· + ·.toMvPoly) 0

/-! ### Helpers for ofMvPoly -/

private theorem pairwise_gt_of_ge_nodup_new [LinearOrder α]
    {l : List α} (hp : l.Pairwise (· ≥ ·)) (hnd : l.Nodup) :
    l.Pairwise (· > ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp ⊢; rw [List.nodup_cons] at hnd
    exact ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (fun h => hnd.1 (h ▸ hb)),
           ih hp.2 hnd.2⟩

private theorem pairwise_attach_new {α : Type _} {r : α → α → Prop} {l : List α}
    (h : l.Pairwise r) : l.attach.Pairwise (fun a b => r a.val b.val) := by
  rw [List.pairwise_iff_getElem] at h ⊢
  intro i j hi hj hij
  simp only [List.length_attach] at hi hj
  simp only [List.getElem_attach]
  exact h i j hi hj hij

private theorem coeff_ne_zero_of_mem_sort_new
    (p : MvPolynomial (Fin n) R) (m : MonicMonomialNew n ord)
    (hm : m ∈ (p.support.image MonicMonomialNew.ofFinsupp : Finset _).sort (· ≥ ·)) :
    MvPolynomial.coeff m.toFinsupp p ≠ 0 := by
  obtain ⟨g, hgs, hgm⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hm)
  rw [← hgm, MonicMonomialNew.toFinsupp_ofFinsupp]
  exact Finsupp.mem_support_iff.mp hgs

/-- Convert a Mathlib `MvPolynomial` to an `AzMvPolynomialNew`. -/
noncomputable def AzMvPolynomialNew.ofMvPoly
    (p : MvPolynomial (Fin n) R) : AzMvPolynomialNew n R ord :=
  let monics := p.support.image MonicMonomialNew.ofFinsupp
  let sorted := monics.sort (· ≥ ·)
  let terms := sorted.attach.map fun ⟨m, hm⟩ =>
    (⟨⟨MvPolynomial.coeff m.toFinsupp p,
       coeff_ne_zero_of_mem_sort_new p m hm⟩, m⟩ : MonomialNew n R ord)
  ⟨terms.toArray, List.toList_toArray ▸
    List.pairwise_map.mpr ((pairwise_attach_new
      (pairwise_gt_of_ge_nodup_new (Finset.pairwise_sort monics (· ≥ ·))
        (Finset.sort_nodup monics (· ≥ ·)))).imp fun h => h)⟩

/-! ### Round-trip: toMvPoly (ofMvPoly p) = p -/

theorem foldl_add_map_eq_sum_new {M α : Type _} [AddCommMonoid M]
    (f : α → M) (l : List α) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  rw [List.sum_eq_foldl, ← List.foldl_map]

/-- `toMvPoly` expressed as the sum of `toMvPoly` over the term list. -/
theorem AzMvPolynomialNew.toMvPoly_eq_list_sum
    (p : AzMvPolynomialNew n R ord) :
    p.toMvPoly = (p.terms.toList.map MonomialNew.toMvPoly).sum := by
  simp only [AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new]

private theorem sum_map_attach_eq_new {α M : Type _} [AddCommMonoid M]
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
theorem toMvPoly_ofMvPoly_new (p : MvPolynomial (Fin n) R) :
    AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord) = p := by
  simp only [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.ofMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new, List.toList_toArray, List.map_map]
  rw [sum_map_attach_eq_new _
    (fun m => (MvPolynomial.monomial m.toFinsupp) (MvPolynomial.coeff m.toFinsupp p))
    (fun _ _ => rfl)]
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  show (p.support.image MonicMonomialNew.ofFinsupp).sum
    (fun m => (MvPolynomial.monomial m.toFinsupp) (MvPolynomial.coeff m.toFinsupp p)) = p
  rw [Finset.sum_image (fun a _ b _ h => MonicMonomialNew.ofFinsupp_injective h)]
  simp only [MonicMonomialNew.toFinsupp_ofFinsupp]
  exact MvPolynomial.support_sum_monomial_coeff p

/-! ### Reverse round-trip helpers -/

theorem MonicMonomialNew.ofFinsupp_toFinsupp (m : MonicMonomialNew n ord) :
    MonicMonomialNew.ofFinsupp (m.toFinsupp) = m := by
  ext; simp [ofFinsupp, toFinsupp]

theorem MonicMonomialNew.toFinsupp_injective :
    Function.Injective (MonicMonomialNew.toFinsupp (n := n) (ord := ord)) := by
  intro a b h
  exact (ofFinsupp_toFinsupp a).symm.trans
    ((congrArg ofFinsupp h).trans (ofFinsupp_toFinsupp b))

/-- `toFinsupp` distributes over monic monomial multiplication. -/
theorem MonicMonomialNew.toFinsupp_mul (a b : MonicMonomialNew n ord) :
    (a * b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  ext v; simp [MonicMonomialNew.toFinsupp, MonicMonomialNew.mul_exponents]

private theorem toMvPoly_eq_sum_new (p : AzMvPolynomialNew n R ord) :
    p.toMvPoly = (p.terms.toList.map MonomialNew.toMvPoly).sum := by
  simp only [AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, List.sum_eq_foldl, ← List.foldl_map]

private theorem sum_map_eq_zero₂_new {α M : Type _} [AddCommMonoid M]
    (l : List α) (g : α → M) (h : ∀ x ∈ l, g x = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (by simp), ih (fun x hx => h x (.tail _ hx))]

theorem list_sum_ite_eq_of_nodup_map_new {α β M : Type _} [AddCommMonoid M]
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

theorem toFinsupp_nodup_new (p : AzMvPolynomialNew n R ord) :
    (p.terms.toList.map
      (fun t : MonomialNew n R ord => t.monic.toFinsupp)).Nodup := by
  show (p.terms.toList.map _).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  exact p.sorted.imp fun h heq =>
    absurd (MonicMonomialNew.toFinsupp_injective heq) (ne_of_gt h)

theorem coeff_toMvPoly_new
    (p : AzMvPolynomialNew n R ord) (f : Fin n →₀ ℕ) :
    MvPolynomial.coeff f p.toMvPoly =
    (p.terms.toList.map (fun m : MonomialNew n R ord =>
      if m.monic.toFinsupp = f then m.coeff.val else 0)).sum := by
  rw [toMvPoly_eq_sum_new]
  have h := map_list_sum (MvPolynomial.coeffAddMonoidHom (σ := Fin n) f)
    (p.terms.toList.map MonomialNew.toMvPoly)
  simp only [MvPolynomial.coeffAddMonoidHom_apply] at h
  rw [h, List.map_map]; congr 1; ext m
  simp [MonomialNew.toMvPoly, MvPolynomial.coeff_monomial]

theorem support_toMvPoly_new
    (p : AzMvPolynomialNew n R ord) :
    p.toMvPoly.support =
    (p.terms.toList.map
      (fun m : MonomialNew n R ord => m.monic.toFinsupp)).toFinset := by
  ext f; rw [MvPolynomial.mem_support_iff, List.mem_toFinset, List.mem_map]
  constructor
  · intro hne; by_contra hall; push Not at hall
    apply hne; rw [coeff_toMvPoly_new]
    exact sum_map_eq_zero₂_new _ _ (fun m hm => if_neg (hall m hm))
  · rintro ⟨m, hm, rfl⟩
    rw [coeff_toMvPoly_new,
      list_sum_ite_eq_of_nodup_map_new _ _ (toFinsupp_nodup_new p) m hm]
    exact m.coeff.property

private theorem image_ofFinsupp_support_new
    (p : AzMvPolynomialNew n R ord) :
    (p.toMvPoly.support.image MonicMonomialNew.ofFinsupp :
      Finset (MonicMonomialNew n ord)) =
    (p.terms.toList.map
      (fun m : MonomialNew n R ord => m.monic)).toFinset := by
  rw [support_toMvPoly_new]
  ext m; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨f, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (MonicMonomialNew.ofFinsupp_toFinsupp t.monic).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.monic.toFinsupp, ⟨t, ht, rfl⟩,
      MonicMonomialNew.ofFinsupp_toFinsupp t.monic⟩

private theorem sort_eq_of_pairwise_gt_new [LinearOrder α] [DecidableEq α]
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

/-- `toMvPoly` is injective. -/
theorem toMvPoly_injective_new :
    Function.Injective
      (AzMvPolynomialNew.toMvPoly (R := R) (n := n) (ord := ord)) := by
  intro ⟨at_, as_⟩ ⟨bt_, bs_⟩ hab
  simp only [AzMvPolynomialNew.mk.injEq]
  have hmonic_eq : at_.toList.map (fun t : MonomialNew n R ord => t.monic) =
      bt_.toList.map (fun t : MonomialNew n R ord => t.monic) := by
    rw [← sort_eq_of_pairwise_gt_new _ (List.pairwise_map.mpr as_),
        ← sort_eq_of_pairwise_gt_new _ (List.pairwise_map.mpr bs_)]
    congr 1
    rw [← image_ofFinsupp_support_new ⟨at_, as_⟩,
        ← image_ofFinsupp_support_new ⟨bt_, bs_⟩]
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
      have h1 : (at_.toList.map (fun t : MonomialNew n R ord => t.monic))[i]'(by simp; exact hi) =
          at_.toList[i].monic := List.getElem_map ..
      have h2 : (bt_.toList.map (fun t : MonomialNew n R ord => t.monic))[i]'(by simp; exact hi₂) =
          bt_.toList[i].monic := List.getElem_map ..
      rw [← h1, ← h2]; congr 1
    have ha : MvPolynomial.coeff at_.toList[i].monic.toFinsupp
        (⟨at_, as_⟩ : AzMvPolynomialNew n R ord).toMvPoly =
        at_.toList[i].coeff.val := by
      rw [coeff_toMvPoly_new]; exact list_sum_ite_eq_of_nodup_map_new _ _
        (toFinsupp_nodup_new ⟨at_, as_⟩) _ (List.getElem_mem ..) _
    have hb : MvPolynomial.coeff bt_.toList[i].monic.toFinsupp
        (⟨bt_, bs_⟩ : AzMvPolynomialNew n R ord).toMvPoly =
        bt_.toList[i].coeff.val := by
      rw [coeff_toMvPoly_new]; exact list_sum_ite_eq_of_nodup_map_new _ _
        (toFinsupp_nodup_new ⟨bt_, bs_⟩) _ (List.getElem_mem ..) _
    have hci : at_.toList[i].coeff = bt_.toList[i].coeff :=
      Subtype.val_injective (ha.symm.trans (by rw [hmi, hab]; exact hb))
    exact MonomialNew.mk.injEq .. |>.mpr ⟨hci, hmi⟩

/-- The reverse round-trip: `ofMvPoly (toMvPoly p) = p`. -/
theorem ofMvPoly_toMvPoly_new (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew.ofMvPoly (AzMvPolynomialNew.toMvPoly p) = p :=
  toMvPoly_injective_new (toMvPoly_ofMvPoly_new p.toMvPoly)

@[simp] theorem toMvPoly_zero_new :
    AzMvPolynomialNew.toMvPoly (0 : AzMvPolynomialNew n R ord) = 0 := by
  simp [AzMvPolynomialNew.toMvPoly]

@[simp] theorem ofMvPoly_zero_new :
    (AzMvPolynomialNew.ofMvPoly (ord := ord) (0 : MvPolynomial (Fin n) R)) =
      (0 : AzMvPolynomialNew n R ord) := by
  rw [show (0 : MvPolynomial (Fin n) R) =
    AzMvPolynomialNew.toMvPoly (0 : AzMvPolynomialNew n R ord) from toMvPoly_zero_new.symm]
  exact ofMvPoly_toMvPoly_new _

theorem one_toFinsupp_new :
    (MonicMonomialNew.one : MonicMonomialNew n ord).toFinsupp = 0 := by
  ext v
  simp only [MonicMonomialNew.toFinsupp, MonicMonomialNew.one,
    Finsupp.onFinset_apply, Finsupp.zero_apply]
  exact Vector.getElem_replicate ..

@[simp] theorem toMvPoly_one_new [DecidableEq R] :
    AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.one : AzMvPolynomialNew n R ord) =
      (1 : MvPolynomial (Fin n) R) := by
  simp only [AzMvPolynomialNew.one]
  split
  · next h =>
    simp [AzMvPolynomialNew.toMvPoly]
    have : (1 : MvPolynomial (Fin n) R) = 0 := by
      rw [← MvPolynomial.C_1, ← MvPolynomial.C_0, h]
    exact this.symm
  · next h =>
    simp [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.ofMonomial,
      MonomialNew.toMvPoly, MonomialNew.one]
    rw [show (MonicMonomialNew.one : MonicMonomialNew n ord).toFinsupp = 0
          from one_toFinsupp_new]
    exact MvPolynomial.one_def.symm

@[simp] theorem toMvPoly_C_new [DecidableEq R] (c : R) :
    AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.C c : AzMvPolynomialNew n R ord) =
      MvPolynomial.C c := by
  simp only [AzMvPolynomialNew.C]
  split
  · next h => simp [AzMvPolynomialNew.toMvPoly, h]
  · next h =>
    simp [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.ofMonomial,
          MonomialNew.toMvPoly]
    rw [show (MonicMonomialNew.one : MonicMonomialNew n ord).toFinsupp = 0
          from one_toFinsupp_new]
    exact MvPolynomial.C_apply.symm

/-- `MonicMonomialNew.ofVar i` corresponds to `Finsupp.single i 1`. -/
theorem MonicMonomialNew.toFinsupp_ofVar (i : Fin n) :
    (MonicMonomialNew.ofVar i : MonicMonomialNew n ord).toFinsupp = Finsupp.single i 1 := by
  ext j
  simp only [MonicMonomialNew.toFinsupp, MonicMonomialNew.ofVar, Finsupp.onFinset_apply,
    Finsupp.single_apply, Vector.getElem_ofFn, Fin.getElem_fin]

@[simp] theorem toMvPoly_X_new [DecidableEq R] (i : Fin n) :
    AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.X i : AzMvPolynomialNew n R ord) =
      MvPolynomial.X i := by
  simp only [AzMvPolynomialNew.X]
  split
  · next h =>
    have hR : Subsingleton R :=
      ⟨fun a b => by rw [← one_mul a, ← one_mul b, h, zero_mul, zero_mul]⟩
    exact Subsingleton.elim _ _
  · next h =>
    show (0 : MvPolynomial (Fin n) R) +
        (⟨⟨1, h⟩, MonicMonomialNew.ofVar i⟩ : MonomialNew n R ord).toMvPoly = MvPolynomial.X i
    rw [zero_add]
    show MvPolynomial.monomial (MonicMonomialNew.ofVar i).toFinsupp (1 : R) = MvPolynomial.X i
    rw [MonicMonomialNew.toFinsupp_ofVar,
        show (MvPolynomial.X i : MvPolynomial (Fin n) R) = MvPolynomial.X i ^ 1 from (pow_one _).symm]
    exact MvPolynomial.X_pow_eq_monomial.symm

@[simp] theorem ofMvPoly_one_new [DecidableEq R] :
    (AzMvPolynomialNew.ofMvPoly (ord := ord) (1 : MvPolynomial (Fin n) R)) =
    (AzMvPolynomialNew.one : AzMvPolynomialNew n R ord) := by
  rw [show (1 : MvPolynomial (Fin n) R) =
    AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.one : AzMvPolynomialNew n R ord)
    from toMvPoly_one_new.symm]
  exact ofMvPoly_toMvPoly_new _

/-- The equivalence between `AzMvPolynomialNew n R ord` and `MvPolynomial (Fin n) R`. -/
noncomputable def equivMvPolynomialNew :
    AzMvPolynomialNew n R ord ≃ MvPolynomial (Fin n) R where
  toFun := AzMvPolynomialNew.toMvPoly
  invFun := AzMvPolynomialNew.ofMvPoly
  left_inv := ofMvPoly_toMvPoly_new
  right_inv := toMvPoly_ofMvPoly_new

/-- The number of terms equals the cardinality of the MvPolynomial support. -/
theorem numTerms_eq_support_card_new
    (p : AzMvPolynomialNew n R ord) :
    p.numTerms = p.toMvPoly.support.card := by
  rw [AzMvPolynomialNew.numTerms, support_toMvPoly_new]
  rw [List.toFinset_card_of_nodup (toFinsupp_nodup_new p)]
  simp [Array.length_toList]

/-- The number of terms of `ofMvPoly p` equals the cardinality of `p.support`. -/
theorem numTerms_ofMvPoly_eq_support_card_new
    (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord).numTerms = p.support.card := by
  rw [numTerms_eq_support_card_new, toMvPoly_ofMvPoly_new]

private theorem vector_toList_sum_eq_new (v : Vector ℕ n) :
    v.toList.sum = ∑ i : Fin n, v[i] := by
  conv_lhs => rw [show v = Vector.ofFn (fun i => v[i]) from by ext i; simp]
  rw [Vector.toList_ofFn, List.sum_ofFn]

private theorem totalDegree_eq_toFinsupp_sum_new
    (m : MonicMonomialNew n ord) :
    m.totalDegree = m.toFinsupp.sum fun _ e => e := by
  simp only [MonicMonomialNew.totalDegree, MonomialOrder.totalDeg, MonicMonomialNew.toFinsupp]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Finsupp.onFinset_apply]
  rw [← Array.foldl_toList, ← List.sum_eq_foldl, Vector.toList_toArray]
  exact vector_toList_sum_eq_new m.exponents

/-- The total degree of an AzMvPolynomialNew equals the total degree of the
    corresponding MvPolynomial. -/
theorem totalDegree_toMvPoly_new [DecidableEq R]
    (p : AzMvPolynomialNew n R ord) :
    p.totalDegree = p.toMvPoly.totalDegree := by
  simp only [AzMvPolynomialNew.totalDegree, MvPolynomial.totalDegree]
  rw [support_toMvPoly_new, ← Array.foldl_toList]
  rw [show List.foldl (fun acc (m : MonomialNew n R ord) => max acc m.totalDegree) 0 p.terms.toList =
    List.foldl max 0 (p.terms.toList.map (fun m : MonomialNew n R ord => m.totalDegree))
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
    rw [totalDegree_eq_toFinsupp_sum_new]
    exact Finset.le_sup (f := fun s => Finsupp.sum s fun _ e => e)
      (show m.monic.toFinsupp ∈ _ by rw [List.mem_toFinset, List.mem_map]; exact ⟨m, hm, rfl⟩)
  · apply Finset.sup_le
    intro s hs
    rw [List.mem_toFinset, List.mem_map] at hs
    obtain ⟨m, hm, rfl⟩ := hs
    show (m.monic.toFinsupp.sum fun _ e => e) ≤ _
    rw [← totalDegree_eq_toFinsupp_sum_new]
    exact Finset.le_sup (f := @id ℕ)
      (show m.monic.totalDegree ∈ _ by rw [List.mem_toFinset, List.mem_map]; exact ⟨m, hm, rfl⟩)

/-- The total degree of `ofMvPoly p` equals the total degree of `p`. -/
theorem totalDegree_ofMvPoly_new [DecidableEq R]
    (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord).totalDegree = p.totalDegree := by
  rw [totalDegree_toMvPoly_new, toMvPoly_ofMvPoly_new]

/-! ### withOrder preserves conversion to MvPolynomial -/

/-- Converting to `MvPolynomial` is invariant under monomial order changes. -/
theorem toMvPoly_withOrder_new [DecidableEq R]
    (p : AzMvPolynomialNew n R ord) (ord' : MonomialOrder) :
    (p.withOrder ord').toMvPoly = p.toMvPoly := by
  unfold AzMvPolynomialNew.withOrder
  split
  · next h => subst h; rfl
  · next h =>
    simp only [AzMvPolynomialNew.toMvPoly]
    rw [← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray]
    set mapped := p.terms.toList.map (fun m => m.withOrder ord')
    set sorted := mapped.mergeSort _
    have hperm : sorted.Perm mapped := List.mergeSort_perm mapped _
    calc List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 sorted
        = List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 mapped :=
          hperm.foldl_eq (rcomm := ⟨fun b a₁ a₂ => by ring⟩) 0
      _ = List.foldl (fun x1 x2 => x1 + x2.toMvPoly) 0 p.terms.toList := by
          simp only [mapped, List.foldl_map, MonomialNew.toMvPoly_withOrder]

/-- `toMvPoly` of `ofMonomials` is just the sum of the individual monomial
    conversions. -/
theorem toMvPoly_ofMonomials_new [DecidableEq R]
    (ms : Array (MonomialNew n R ord))
    (hdistinct : ms.toList.Pairwise (fun a b => a.monic ≠ b.monic)) :
    (AzMvPolynomialNew.ofMonomials ms hdistinct).toMvPoly =
      (ms.toList.map MonomialNew.toMvPoly).sum := by
  simp only [AzMvPolynomialNew.ofMonomials, AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new, List.toList_toArray]
  have hperm := List.mergeSort_perm ms.toList AzMvPolynomialNew.monicGeq
  exact hperm.map MonomialNew.toMvPoly |>.sum_eq

end Azurite
