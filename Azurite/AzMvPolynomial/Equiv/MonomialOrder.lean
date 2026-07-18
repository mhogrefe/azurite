/-
  Bridge from `AzMvPolynomial` to Mathlib's `MonomialOrder`.

  Constructs a Mathlib `MonomialOrder (Fin n)` from our ordering schemes and
  proves well-foundedness via Dickson's lemma.  Mirrors the old
  `Azurite.AzMvPolynomial.Equiv.MonomialOrder`, with proofs re-done on top of
  `MonicMonomial`.
-/
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.CompareEmbed
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Order.WellFounded

namespace Azurite

open MonicMonomial _root_.Azurite.MonomialOrder

/-! ### Auxiliary lemmas on `List.foldl (· + ·)` -/

section FoldlLemmas

private theorem foldl_add_le_init {init : ℕ} {l : List ℕ} :
    init ≤ l.foldl (· + ·) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons a t ih => exact Nat.le_trans (Nat.le_add_right _ _) (ih (init := init + a))

private theorem foldl_add_ge {init : ℕ} {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    init + a ≤ l.foldl (· + ·) init := by
  induction l generalizing init with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ht
    · exact foldl_add_le_init
    · calc init + a ≤ (init + b) + a := by omega
        _ ≤ t.foldl (· + ·) (init + b) := ih ht

private theorem list_foldl_zero_replicate : ∀ m,
    List.foldl (· + ·) 0 (List.replicate m (0 : ℕ)) = 0 := by
  intro m; induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ih]

end FoldlLemmas

/-! ### Vector entry / totalDeg lemmas -/

section TotalDegLemmas
variable {n : ℕ}

private theorem vec_entry_le_totalDeg (v : Vector ℕ n) (i : Fin n) :
    v[i] ≤ totalDeg v := by
  unfold totalDeg; rw [← Array.foldl_toList]
  have hmem : v[i] ∈ v.toArray.toList := List.getElem_mem (by simp)
  have := foldl_add_ge (init := 0) hmem; omega

private theorem vec_zero_of_totalDeg_zero (v : Vector ℕ n)
    (h : totalDeg v = 0) (i : Fin n) : v[i] = 0 := by
  have := vec_entry_le_totalDeg v i; omega

private theorem totalDeg_zero_vec :
    totalDeg (Vector.ofFn (n := n) fun _ => 0) = 0 := by
  simp only [totalDeg]
  rw [← Array.foldl_toList]
  change List.foldl (· + ·) 0 (Vector.ofFn (fun _ : Fin n => (0 : ℕ))).toList = 0
  rw [Vector.toList_ofFn, List.ofFn_const]
  exact list_foldl_zero_replicate n

end TotalDegLemmas

/-! ### 1 is the minimum element -/

section OneMin
variable {n : ℕ}

private theorem lexCompareAux_ge_zero (v : Vector ℕ n) (i : ℕ) :
    lexCompareAux v (Vector.ofFn fun _ => 0) i ≠ .lt := by
  unfold lexCompareAux; split
  · next hi =>
    simp only [Vector.getElem_ofFn]
    cases h : compare (v[i]'hi) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq => exact lexCompareAux_ge_zero v (i + 1)
    | gt => exact Ordering.noConfusion
  · exact Ordering.noConfusion

private theorem revlexCompareAux_ge_zero_of_tdz
    (v : Vector ℕ n) (hv : totalDeg v = 0) (i : ℕ) :
    revlexCompareAux v (Vector.ofFn fun _ => 0) i ≠ .lt := by
  unfold revlexCompareAux; split
  · next hi =>
    simp only [Vector.getElem_ofFn]
    have hvi : v[n - 1 - i] = 0 :=
      vec_zero_of_totalDeg_zero v hv ⟨n - 1 - i, by omega⟩
    rw [hvi]; simp
    exact revlexCompareAux_ge_zero_of_tdz v hv (i + 1)
  · exact Ordering.noConfusion

private theorem compareExponents_ge_zero (ord : MonomialOrder) (v : Vector ℕ n) :
    compareExponents ord v (Vector.ofFn fun _ => 0) ≠ .lt := by
  unfold compareExponents; cases ord with
  | Lex => exact lexCompareAux_ge_zero v 0
  | Deglex =>
    simp only [totalDeg_zero_vec]
    cases h : compare (totalDeg v) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq => exact lexCompareAux_ge_zero v 0
    | gt => exact Ordering.noConfusion
  | Degrevlex =>
    simp only [totalDeg_zero_vec]
    cases h : compare (totalDeg v) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq =>
      have htdz : totalDeg v = 0 := by
        rwa [Nat.compare_eq_eq] at h
      exact revlexCompareAux_ge_zero_of_tdz v htdz 0
    | gt => exact Ordering.noConfusion

end OneMin

/-! ### MonicMonomial properties -/

section MonicProps
variable {n : ℕ} {ord : MonomialOrder}

/-- The identity monomial `1` is the minimum in any monomial ordering. -/
theorem MonicMonomial.one_le' (m : MonicMonomial n ord) : 1 ≤ m := by
  rw [not_lt.symm]
  intro (h : compareExponents ord m.exponents (1 : MonicMonomial n ord).exponents = .lt)
  have h1 : (1 : MonicMonomial n ord).exponents = Vector.ofFn (fun _ => 0) := by
    ext i hi; simp [one_exponents]
  rw [h1] at h
  exact compareExponents_ge_zero ord m.exponents h

theorem MonicMonomial.mul_le_mul_left' (c : MonicMonomial n ord)
    {a b : MonicMonomial n ord} (h : a ≤ b) : c * a ≤ c * b := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (MonicMonomial.mul_lt_mul_left c a b hlt)
  · rw [heq]

theorem MonicMonomial.le_of_mul_le_mul_left (c a b : MonicMonomial n ord)
    (h : c * a ≤ c * b) : a ≤ b := by
  by_contra hba; push Not at hba
  exact absurd h (not_le_of_gt (MonicMonomial.mul_lt_mul_left c b a hba))

end MonicProps

/-! ### Monotonicity of `ofFinsupp` -/

section Monotone
variable {n : ℕ} {ord : MonomialOrder}

theorem ofFinsupp_monotone (f g : Fin n →₀ ℕ) (h : f ≤ g) :
    MonicMonomial.ofFinsupp (ord := ord) f ≤ MonicMonomial.ofFinsupp g := by
  have hfg : f + (g - f) = g := add_tsub_cancel_of_le h
  have hmul : MonicMonomial.ofFinsupp (ord := ord) (f + (g - f)) =
      MonicMonomial.ofFinsupp f * MonicMonomial.ofFinsupp (g - f) := by
    apply MonicMonomial.toFinsupp_injective
    rw [MonicMonomial.toFinsupp_ofFinsupp, MonicMonomial.toFinsupp_mul,
        MonicMonomial.toFinsupp_ofFinsupp, MonicMonomial.toFinsupp_ofFinsupp]
  calc MonicMonomial.ofFinsupp (ord := ord) f
      = MonicMonomial.ofFinsupp f * 1 := (MonicMonomial.mul_one _).symm
    _ ≤ MonicMonomial.ofFinsupp f * MonicMonomial.ofFinsupp (g - f) := by
        rcases lt_or_eq_of_le
          (MonicMonomial.one_le' (MonicMonomial.ofFinsupp (g - f))) with hlt | heq
        · exact le_of_lt (MonicMonomial.mul_lt_mul_left _ _ _ hlt)
        · rw [← heq]
    _ = MonicMonomial.ofFinsupp (f + (g - f)) := hmul.symm
    _ = MonicMonomial.ofFinsupp g := by rw [hfg]

end Monotone

/-! ### Well-foundedness via Dickson's lemma -/

section WellFounded
variable {n : ℕ} {ord : MonomialOrder}

private theorem chain_antitone {α : Type _} [Preorder α] {f : ℕ → α}
    (hf : ∀ n, f (n + 1) < f n) : ∀ i j, i < j → f j < f i := by
  intro i j hij; induction hij with
  | refl => exact hf _
  | step _ ih => exact lt_trans (hf _) ih

/-- `MonicMonomial` with any ordering is well-founded. -/
instance wellFoundedLT_monicMonomial : WellFoundedLT (MonicMonomial n ord) where
  wf := by
    rw [wellFounded_iff_isEmpty_descending_chain]
    by_contra h; rw [not_isEmpty_iff] at h
    obtain ⟨f, hf⟩ := h
    have hpwo := Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set (Fin n →₀ ℕ))
    obtain ⟨g, hg_mono⟩ := hpwo.exists_monotone_subseq
      (f := fun i => (f i).toFinsupp) (fun i => Set.mem_univ _)
    have h01 : (f (g 0)).toFinsupp ≤ (f (g 1)).toFinsupp :=
      hg_mono (Nat.zero_le 1)
    have h_le : f (g 0) ≤ f (g 1) := by
      have := ofFinsupp_monotone (ord := ord) _ _ h01
      rwa [MonicMonomial.ofFinsupp_toFinsupp, MonicMonomial.ofFinsupp_toFinsupp] at this
    exact absurd h_le (not_le_of_gt
      (chain_antitone hf (g 0) (g 1) (g.strictMono Nat.zero_lt_one)))

end WellFounded

/-! ### Constructing a Mathlib `MonomialOrder (Fin n)` -/

section Bridge
variable {n : ℕ}

/-- Construct a Mathlib `MonomialOrder (Fin n)` from our ordering. -/
noncomputable def toMathlibMonomialOrder (ord : MonomialOrder) :
    _root_.MonomialOrder (Fin n) where
  syn := Additive (MonicMonomial n ord)
  addCommMonoidSyn := Additive.addCommMonoid
  linearOrderSyn := Additive.linearOrder
  isOrderedAddMonoid_syn := {
    add_le_add_left := fun a b hab c => by
      show Additive.ofMul (Additive.toMul a * Additive.toMul c) ≤
           Additive.ofMul (Additive.toMul b * Additive.toMul c)
      rw [MonicMonomial.mul_comm (Additive.toMul a),
          MonicMonomial.mul_comm (Additive.toMul b)]
      exact MonicMonomial.mul_le_mul_left' (Additive.toMul c) hab
  }
  toSyn := {
    toEquiv := {
      toFun := fun f => Additive.ofMul (MonicMonomial.ofFinsupp f)
      invFun := fun m => (Additive.toMul m).toFinsupp
      left_inv := fun f => MonicMonomial.toFinsupp_ofFinsupp f
      right_inv := fun m => by
        show Additive.ofMul (MonicMonomial.ofFinsupp (Additive.toMul m).toFinsupp) = m
        simp [MonicMonomial.ofFinsupp_toFinsupp]
    }
    map_add' := fun f g => by
      show Additive.ofMul (MonicMonomial.ofFinsupp (f + g)) =
           Additive.ofMul (MonicMonomial.ofFinsupp f) +
           Additive.ofMul (MonicMonomial.ofFinsupp g)
      suffices h : MonicMonomial.ofFinsupp (ord := ord) (f + g) =
          MonicMonomial.ofFinsupp f * MonicMonomial.ofFinsupp g from
        congrArg Additive.ofMul h
      apply MonicMonomial.toFinsupp_injective
      rw [MonicMonomial.toFinsupp_ofFinsupp, MonicMonomial.toFinsupp_mul,
          MonicMonomial.toFinsupp_ofFinsupp, MonicMonomial.toFinsupp_ofFinsupp]
  }
  toSyn_monotone := fun {_ _} h => ofFinsupp_monotone _ _ h
  wellFoundedLT_syn := ⟨wellFoundedLT_monicMonomial.wf⟩

end Bridge

/-! ### Connecting sorted representation to Mathlib degree -/

section DegreeBridge
variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

private theorem toSyn_toFinsupp (m : MonomialOrder) (a : MonicMonomial n m) :
    (toMathlibMonomialOrder (n := n) m).toSyn a.toFinsupp = Additive.ofMul a :=
  congrArg Additive.ofMul (MonicMonomial.ofFinsupp_toFinsupp a)

private theorem terms_monic_le_zero [DecidableEq R] (p : AzMvPolynomial n R ord)
    (hp : p.terms.size > 0) (i : ℕ) (hi : i < p.terms.size) :
    (p.terms[i]'(by omega)).monic ≤ (p.terms[0]'(by omega)).monic := by
  by_cases h : i = 0
  · subst h; exact le_refl _
  · have h0i := List.pairwise_iff_getElem.mp p.sorted 0 i
      (by simp; omega) (by simp; omega) (by omega)
    simp only [Array.getElem_toList] at h0i; exact le_of_lt h0i

theorem terms_zero_mem_support [DecidableEq R] (p : AzMvPolynomial n R ord)
    (hp : p.terms.size > 0) :
    (p.terms[0]'(by omega)).monic.toFinsupp ∈ p.toMvPoly.support := by
  rw [support_toMvPoly, List.mem_toFinset, List.mem_map]
  exact ⟨p.terms[0]'(by omega), List.getElem_mem (by simp; omega), rfl⟩

/-- The leading term in our sorted representation equals Mathlib's `MonomialOrder.degree`. -/
theorem degree_eq_terms_zero [DecidableEq R] (p : AzMvPolynomial n R ord)
    (hp : p.terms.size > 0) :
    (toMathlibMonomialOrder (n := n) ord).degree p.toMvPoly =
    (p.terms[0]'(by omega)).monic.toFinsupp := by
  set mo := toMathlibMonomialOrder (n := n) ord
  simp only [_root_.MonomialOrder.degree]
  suffices h : p.toMvPoly.support.sup (⇑mo.toSyn) =
      mo.toSyn (p.terms[0]'(by omega)).monic.toFinsupp by
    rw [h, AddEquiv.symm_apply_apply]
  apply le_antisymm
  · apply Finset.sup_le; intro s hs
    rw [support_toMvPoly, List.mem_toFinset, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [toSyn_toFinsupp, toSyn_toFinsupp]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    simp only [Array.getElem_toList]
    exact terms_monic_le_zero p hp i (by simp at hi; exact hi)
  · exact Finset.le_sup (terms_zero_mem_support p hp)

/-- The leading coefficient in our representation equals Mathlib's `MonomialOrder.leadingCoeff`. -/
theorem leadingCoeff_eq_terms_zero [DecidableEq R] (p : AzMvPolynomial n R ord)
    (hp : p.terms.size > 0) :
    (toMathlibMonomialOrder (n := n) ord).leadingCoeff p.toMvPoly =
    (p.terms[0]'(by omega)).coeff.val := by
  rw [_root_.MonomialOrder.leadingCoeff, degree_eq_terms_zero p hp, coeff_toMvPoly]
  exact list_sum_ite_eq_of_nodup_map (M := R) _ _ (toFinsupp_nodup p) _
    (List.getElem_mem (by simp; omega)) (fun m => m.coeff.val)

end DegreeBridge

end Azurite
