/-
  Bridge from `AzMvPolynomialNew` to Mathlib's `MonomialOrder`.

  Constructs a Mathlib `MonomialOrder (Fin n)` from our ordering schemes and
  proves well-foundedness via Dickson's lemma.  Mirrors the old
  `Azurite.AzMvPolynomial.Equiv.MonomialOrder`, with proofs re-done on top of
  `MonicMonomialNew`.
-/
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Azurite.AzMvPolynomial.New.CompareEmbed
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Order.WellFounded

namespace Azurite

open MonicMonomialNew MonomialOrder

/-! ### Auxiliary lemmas on `List.foldl (· + ·)` -/

section FoldlLemmas

private theorem foldl_add_le_init_new {init : ℕ} {l : List ℕ} :
    init ≤ l.foldl (· + ·) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons a t ih => exact Nat.le_trans (Nat.le_add_right _ _) (ih (init := init + a))

private theorem foldl_add_ge_new {init : ℕ} {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    init + a ≤ l.foldl (· + ·) init := by
  induction l generalizing init with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ht
    · exact foldl_add_le_init_new
    · calc init + a ≤ (init + b) + a := by omega
        _ ≤ t.foldl (· + ·) (init + b) := ih ht

private theorem list_foldl_zero_replicate_new : ∀ m,
    List.foldl (· + ·) 0 (List.replicate m (0 : ℕ)) = 0 := by
  intro m; induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ih]

end FoldlLemmas

/-! ### Vector entry / totalDeg lemmas -/

section TotalDegLemmas
variable {n : ℕ}

private theorem vec_entry_le_totalDeg_new (v : Vector ℕ n) (i : Fin n) :
    v[i] ≤ totalDeg v := by
  unfold totalDeg; rw [← Array.foldl_toList]
  have hmem : v[i] ∈ v.toArray.toList := List.getElem_mem (by simp)
  have := foldl_add_ge_new (init := 0) hmem; omega

private theorem vec_zero_of_totalDeg_zero_new (v : Vector ℕ n)
    (h : totalDeg v = 0) (i : Fin n) : v[i] = 0 := by
  have := vec_entry_le_totalDeg_new v i; omega

private theorem totalDeg_zero_vec_new :
    totalDeg (Vector.ofFn (n := n) fun _ => 0) = 0 := by
  simp only [totalDeg]
  rw [← Array.foldl_toList]
  change List.foldl (· + ·) 0 (Vector.ofFn (fun _ : Fin n => (0 : ℕ))).toList = 0
  rw [Vector.toList_ofFn, List.ofFn_const]
  exact list_foldl_zero_replicate_new n

end TotalDegLemmas

/-! ### 1 is the minimum element -/

section OneMin
variable {n : ℕ}

private theorem lexCompareAux_ge_zero_new (v : Vector ℕ n) (i : ℕ) :
    lexCompareAux v (Vector.ofFn fun _ => 0) i ≠ .lt := by
  unfold lexCompareAux; split
  · next hi =>
    simp only [Vector.getElem_ofFn]
    cases h : compare (v[i]'hi) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq => exact lexCompareAux_ge_zero_new v (i + 1)
    | gt => exact Ordering.noConfusion
  · exact Ordering.noConfusion

private theorem revlexCompareAux_ge_zero_of_tdz_new
    (v : Vector ℕ n) (hv : totalDeg v = 0) (i : ℕ) :
    revlexCompareAux v (Vector.ofFn fun _ => 0) i ≠ .lt := by
  unfold revlexCompareAux; split
  · next hi =>
    simp only [Vector.getElem_ofFn]
    have hvi : v[n - 1 - i] = 0 :=
      vec_zero_of_totalDeg_zero_new v hv ⟨n - 1 - i, by omega⟩
    rw [hvi]; simp
    exact revlexCompareAux_ge_zero_of_tdz_new v hv (i + 1)
  · exact Ordering.noConfusion

private theorem compareExponents_ge_zero_new (ord : MonomialOrder) (v : Vector ℕ n) :
    compareExponents ord v (Vector.ofFn fun _ => 0) ≠ .lt := by
  unfold compareExponents; cases ord with
  | Lex => exact lexCompareAux_ge_zero_new v 0
  | Deglex =>
    simp only [totalDeg_zero_vec_new]
    cases h : compare (totalDeg v) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq => exact lexCompareAux_ge_zero_new v 0
    | gt => exact Ordering.noConfusion
  | Degrevlex =>
    simp only [totalDeg_zero_vec_new]
    cases h : compare (totalDeg v) 0 with
    | lt => simp [Nat.compare_eq_lt] at h
    | eq =>
      have htdz : totalDeg v = 0 := by
        rwa [Nat.compare_eq_eq] at h
      exact revlexCompareAux_ge_zero_of_tdz_new v htdz 0
    | gt => exact Ordering.noConfusion

end OneMin

/-! ### MonicMonomialNew properties -/

section MonicProps
variable {n : ℕ} {ord : MonomialOrder}

/-- The identity monomial `1` is the minimum in any monomial ordering. -/
theorem MonicMonomialNew.one_le' (m : MonicMonomialNew n ord) : 1 ≤ m := by
  rw [not_lt.symm]
  intro (h : compareExponents ord m.exponents (1 : MonicMonomialNew n ord).exponents = .lt)
  have h1 : (1 : MonicMonomialNew n ord).exponents = Vector.ofFn (fun _ => 0) := by
    ext i hi; simp [one_exponents]
  rw [h1] at h
  exact compareExponents_ge_zero_new ord m.exponents h

theorem MonicMonomialNew.mul_le_mul_left' (c : MonicMonomialNew n ord)
    {a b : MonicMonomialNew n ord} (h : a ≤ b) : c * a ≤ c * b := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (MonicMonomialNew.mul_lt_mul_left c a b hlt)
  · rw [heq]

theorem MonicMonomialNew.le_of_mul_le_mul_left (c a b : MonicMonomialNew n ord)
    (h : c * a ≤ c * b) : a ≤ b := by
  by_contra hba; push Not at hba
  exact absurd h (not_le_of_gt (MonicMonomialNew.mul_lt_mul_left c b a hba))

end MonicProps

/-! ### Monotonicity of `ofFinsupp` -/

section Monotone
variable {n : ℕ} {ord : MonomialOrder}

theorem ofFinsupp_monotone_new (f g : Fin n →₀ ℕ) (h : f ≤ g) :
    MonicMonomialNew.ofFinsupp (ord := ord) f ≤ MonicMonomialNew.ofFinsupp g := by
  have hfg : f + (g - f) = g := add_tsub_cancel_of_le h
  have hmul : MonicMonomialNew.ofFinsupp (ord := ord) (f + (g - f)) =
      MonicMonomialNew.ofFinsupp f * MonicMonomialNew.ofFinsupp (g - f) := by
    apply MonicMonomialNew.toFinsupp_injective
    rw [MonicMonomialNew.toFinsupp_ofFinsupp, MonicMonomialNew.toFinsupp_mul,
        MonicMonomialNew.toFinsupp_ofFinsupp, MonicMonomialNew.toFinsupp_ofFinsupp]
  calc MonicMonomialNew.ofFinsupp (ord := ord) f
      = MonicMonomialNew.ofFinsupp f * 1 := (MonicMonomialNew.mul_one _).symm
    _ ≤ MonicMonomialNew.ofFinsupp f * MonicMonomialNew.ofFinsupp (g - f) := by
        rcases lt_or_eq_of_le
          (MonicMonomialNew.one_le' (MonicMonomialNew.ofFinsupp (g - f))) with hlt | heq
        · exact le_of_lt (MonicMonomialNew.mul_lt_mul_left _ _ _ hlt)
        · rw [← heq]
    _ = MonicMonomialNew.ofFinsupp (f + (g - f)) := hmul.symm
    _ = MonicMonomialNew.ofFinsupp g := by rw [hfg]

end Monotone

/-! ### Well-foundedness via Dickson's lemma -/

section WellFounded
variable {n : ℕ} {ord : MonomialOrder}

private theorem chain_antitone_new {α : Type _} [Preorder α] {f : ℕ → α}
    (hf : ∀ n, f (n + 1) < f n) : ∀ i j, i < j → f j < f i := by
  intro i j hij; induction hij with
  | refl => exact hf _
  | step _ ih => exact lt_trans (hf _) ih

/-- `MonicMonomialNew` with any ordering is well-founded. -/
instance wellFoundedLT_monicMonomialNew : WellFoundedLT (MonicMonomialNew n ord) where
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
      have := ofFinsupp_monotone_new (ord := ord) _ _ h01
      rwa [MonicMonomialNew.ofFinsupp_toFinsupp, MonicMonomialNew.ofFinsupp_toFinsupp] at this
    exact absurd h_le (not_le_of_gt
      (chain_antitone_new hf (g 0) (g 1) (g.strictMono Nat.zero_lt_one)))

end WellFounded

/-! ### Constructing a Mathlib `MonomialOrder (Fin n)` -/

section Bridge
variable {n : ℕ}

/-- Construct a Mathlib `MonomialOrder (Fin n)` from our ordering. -/
noncomputable def toMathlibMonomialOrderNew (ord : MonomialOrder) :
    _root_.MonomialOrder (Fin n) where
  syn := Additive (MonicMonomialNew n ord)
  acm := Additive.addCommMonoid
  lo := Additive.linearOrder
  iocam := {
    add_le_add_left := fun a b hab c => by
      show Additive.ofMul (Additive.toMul a * Additive.toMul c) ≤
           Additive.ofMul (Additive.toMul b * Additive.toMul c)
      rw [MonicMonomialNew.mul_comm (Additive.toMul a),
          MonicMonomialNew.mul_comm (Additive.toMul b)]
      exact MonicMonomialNew.mul_le_mul_left' (Additive.toMul c) hab
    le_of_add_le_add_left := fun a b c h =>
      MonicMonomialNew.le_of_mul_le_mul_left (Additive.toMul a) b c h
  }
  toSyn := {
    toEquiv := {
      toFun := fun f => Additive.ofMul (MonicMonomialNew.ofFinsupp f)
      invFun := fun m => (Additive.toMul m).toFinsupp
      left_inv := fun f => MonicMonomialNew.toFinsupp_ofFinsupp f
      right_inv := fun m => by
        show Additive.ofMul (MonicMonomialNew.ofFinsupp (Additive.toMul m).toFinsupp) = m
        simp [MonicMonomialNew.ofFinsupp_toFinsupp]
    }
    map_add' := fun f g => by
      show Additive.ofMul (MonicMonomialNew.ofFinsupp (f + g)) =
           Additive.ofMul (MonicMonomialNew.ofFinsupp f) +
           Additive.ofMul (MonicMonomialNew.ofFinsupp g)
      suffices h : MonicMonomialNew.ofFinsupp (ord := ord) (f + g) =
          MonicMonomialNew.ofFinsupp f * MonicMonomialNew.ofFinsupp g from
        congrArg Additive.ofMul h
      apply MonicMonomialNew.toFinsupp_injective
      rw [MonicMonomialNew.toFinsupp_ofFinsupp, MonicMonomialNew.toFinsupp_mul,
          MonicMonomialNew.toFinsupp_ofFinsupp, MonicMonomialNew.toFinsupp_ofFinsupp]
  }
  toSyn_monotone := fun {_ _} h => ofFinsupp_monotone_new _ _ h
  wf := ⟨wellFoundedLT_monicMonomialNew.wf⟩

end Bridge

/-! ### Connecting sorted representation to Mathlib degree -/

section DegreeBridge
variable {R : Type _} [Field R] {n : ℕ} {ord : MonomialOrder}

private theorem toSyn_toFinsupp_new (m : MonomialOrder) (a : MonicMonomialNew n m) :
    (toMathlibMonomialOrderNew (n := n) m).toSyn a.toFinsupp = Additive.ofMul a :=
  congrArg Additive.ofMul (MonicMonomialNew.ofFinsupp_toFinsupp a)

private theorem terms_monic_le_zero_new [DecidableEq R] (p : AzMvPolynomialNew n R ord)
    (hp : p.terms.size > 0) (i : ℕ) (hi : i < p.terms.size) :
    (p.terms[i]'(by omega)).monic ≤ (p.terms[0]'(by omega)).monic := by
  by_cases h : i = 0
  · subst h; exact le_refl _
  · have h0i := List.pairwise_iff_getElem.mp p.sorted 0 i
      (by simp; omega) (by simp; omega) (by omega)
    simp only [Array.getElem_toList] at h0i; exact le_of_lt h0i

theorem terms_zero_mem_support_new [DecidableEq R] (p : AzMvPolynomialNew n R ord)
    (hp : p.terms.size > 0) :
    (p.terms[0]'(by omega)).monic.toFinsupp ∈ p.toMvPoly.support := by
  rw [support_toMvPoly_new, List.mem_toFinset, List.mem_map]
  exact ⟨p.terms[0]'(by omega), List.getElem_mem (by simp; omega), rfl⟩

/-- The leading term in our sorted representation equals Mathlib's `MonomialOrder.degree`. -/
theorem degree_eq_terms_zero_new [DecidableEq R] (p : AzMvPolynomialNew n R ord)
    (hp : p.terms.size > 0) :
    (toMathlibMonomialOrderNew (n := n) ord).degree p.toMvPoly =
    (p.terms[0]'(by omega)).monic.toFinsupp := by
  set mo := toMathlibMonomialOrderNew (n := n) ord
  simp only [_root_.MonomialOrder.degree]
  suffices h : p.toMvPoly.support.sup (⇑mo.toSyn) =
      mo.toSyn (p.terms[0]'(by omega)).monic.toFinsupp by
    rw [h, AddEquiv.symm_apply_apply]
  apply le_antisymm
  · apply Finset.sup_le; intro s hs
    rw [support_toMvPoly_new, List.mem_toFinset, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [toSyn_toFinsupp_new, toSyn_toFinsupp_new]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    simp only [Array.getElem_toList]
    exact terms_monic_le_zero_new p hp i (by simp at hi; exact hi)
  · exact Finset.le_sup (terms_zero_mem_support_new p hp)

/-- The leading coefficient in our representation equals Mathlib's `MonomialOrder.leadingCoeff`. -/
theorem leadingCoeff_eq_terms_zero_new [DecidableEq R] (p : AzMvPolynomialNew n R ord)
    (hp : p.terms.size > 0) :
    (toMathlibMonomialOrderNew (n := n) ord).leadingCoeff p.toMvPoly =
    (p.terms[0]'(by omega)).coeff.val := by
  rw [_root_.MonomialOrder.leadingCoeff, degree_eq_terms_zero_new p hp, coeff_toMvPoly_new]
  exact list_sum_ite_eq_of_nodup_map_new (M := R) _ _ (toFinsupp_nodup_new p) _
    (List.getElem_mem (by simp; omega)) (fun m => m.coeff.val)

end DegreeBridge

end Azurite
