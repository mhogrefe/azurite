import Azurite.AzMvPolynomial.Equiv.Compare
import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzPolynomial.Equiv.Compare

/-!
# Order-preservation of the univariate embedding

The canonical map `AzPolynomial.toAzMvPolynomial i ord : AzPolynomial R →
AzMvPolynomial n R ord` (sending `Σ aₖ Xᵏ ↦ Σ aₖ xᵢᵏ`) is **strictly
monotone** for the two degree-then-top-down-coefficient orders.

The proof shows the two comparisons agree term-for-term.  The image's
descending monomial scan (`xᵢ^{deg}, xᵢ^{deg−1}, …`, descending because
`MonicMonomial.ofVarPow_strictMono`) matches the univariate top-down
coefficient scan, with an absent monomial and an out-of-range coefficient
both contributing `0`.  Concretely:

* `degreeKey (toAzMvPolynomial i ord p) = p.coeffs.size` — the image's degree
  key is exactly the univariate order's primary key;
* `compareTerms` of the two images' term lists equals `compareTopDown` of the
  coefficient arrays (`compareTerms_termsBelow`);

so `AzMvPolynomial.compare` of the images equals `AzPolynomial.compare`,
whence `StrictMono`.
-/

namespace Azurite

variable {R : Type _} [Semiring R] [LinearOrder R] {n : ℕ} {ord : MonomialOrder}

/-! ### `foldl max` helpers -/

private theorem foldl_max_le {α : Type _} (l : List α) (g : α → ℕ) (init B : ℕ)
    (hi : init ≤ B) (hg : ∀ m ∈ l, g m ≤ B) :
    l.foldl (fun a m => max a (g m)) init ≤ B := by
  induction l generalizing init with
  | nil => simpa using hi
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact max_le hi (hg x List.mem_cons_self)
    · intro m hm; exact hg m (List.mem_cons_of_mem _ hm)

private theorem le_foldl_max_init {α : Type _} (l : List α) (g : α → ℕ) (init : ℕ) :
    init ≤ l.foldl (fun a m => max a (g m)) init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left init (g x)) (ih (max init (g x)))

private theorem le_foldl_max {α : Type _} (l : List α) (g : α → ℕ) (init : ℕ)
    {m : α} (hm : m ∈ l) :
    g m ≤ l.foldl (fun a m => max a (g m)) init := by
  induction l generalizing init with
  | nil => exact absurd hm List.not_mem_nil
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact le_trans (le_max_right _ _) (le_foldl_max_init xs g _)
    · exact ih (max init (g x)) hm'

/-! ### The descending term list of an embedded polynomial -/

/-- The descending list of nonzero terms `coeffs[k] · xᵢ^k` for `k < N`, in
strictly descending monomial order (exponents `N-1, N-2, …, 0`, zeros skipped).
This is the explicit spec of the array produced by `buildTermsDesc`. -/
def termsBelow (i : Fin n) (coeffs : Array R) : ℕ → List (Monomial n R ord)
  | 0 => []
  | k + 1 =>
    if h : (coeffs[k]?).getD 0 = 0 then termsBelow i coeffs k
    else ⟨⟨(coeffs[k]?).getD 0, h⟩, MonicMonomial.ofVarPow i k⟩ :: termsBelow i coeffs k

@[simp] theorem termsBelow_zero (i : Fin n) (coeffs : Array R) :
    termsBelow i coeffs (ord := ord) 0 = [] := rfl

theorem termsBelow_succ (i : Fin n) (coeffs : Array R) (k : ℕ) :
    termsBelow i coeffs (ord := ord) (k + 1) =
      if h : (coeffs[k]?).getD 0 = 0 then termsBelow i coeffs k
      else ⟨⟨(coeffs[k]?).getD 0, h⟩, MonicMonomial.ofVarPow i k⟩ :: termsBelow i coeffs k := rfl

omit [LinearOrder R] in
private theorem term_totalDegree (i : Fin n) (c : {c : R // c ≠ 0}) (k : ℕ) :
    (⟨c, MonicMonomial.ofVarPow i k⟩ : Monomial n R ord).totalDegree = k := by
  simp only [Monomial.totalDegree, MonicMonomial.totalDegree, totalDeg_ofVarPow]

private theorem termsBelow_monic_lt (i : Fin n) (coeffs : Array R) (N : ℕ) :
    ∀ m ∈ termsBelow i coeffs (ord := ord) N, m.monic < MonicMonomial.ofVarPow i N := by
  induction N with
  | zero => intro m hm; exact absurd hm List.not_mem_nil
  | succ k ih =>
    intro m hm
    rw [termsBelow_succ] at hm
    have hstep : (MonicMonomial.ofVarPow i k : MonicMonomial n ord) <
        MonicMonomial.ofVarPow i (k + 1) :=
      MonicMonomial.ofVarPow_strictMono i (Nat.lt_succ_self k)
    by_cases hc : (coeffs[k]?).getD 0 = 0
    · rw [dif_pos hc] at hm; exact lt_trans (ih m hm) hstep
    · rw [dif_neg hc] at hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hstep
      · exact lt_trans (ih m hm') hstep

private theorem termsBelow_totalDegree_lt (i : Fin n) (coeffs : Array R) (N : ℕ) :
    ∀ m ∈ termsBelow i coeffs (ord := ord) N, m.totalDegree < N := by
  induction N with
  | zero => intro m hm; exact absurd hm List.not_mem_nil
  | succ k ih =>
    intro m hm
    rw [termsBelow_succ] at hm
    by_cases hc : (coeffs[k]?).getD 0 = 0
    · rw [dif_pos hc] at hm; exact lt_trans (ih m hm) (Nat.lt_succ_self k)
    · rw [dif_neg hc] at hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · rw [term_totalDegree]; exact Nat.lt_succ_self k
      · exact lt_trans (ih m hm') (Nat.lt_succ_self k)

private theorem termsBelow_mem_top (i : Fin n) (coeffs : Array R) (k : ℕ)
    (hk : (coeffs[k]?).getD 0 ≠ 0) :
    (⟨⟨(coeffs[k]?).getD 0, hk⟩, MonicMonomial.ofVarPow i k⟩ : Monomial n R ord)
      ∈ termsBelow i coeffs (ord := ord) (k + 1) := by
  rw [termsBelow_succ, dif_neg hk]; exact List.mem_cons_self

/-! ### `buildTermsDesc` produces `termsBelow` -/

private theorem buildTermsDesc_toList_base (i : Fin n) (coeffs : Array R)
    (acc : Array (Monomial n R ord)) (fuel : ℕ) :
    (buildTermsDesc i coeffs (fuel + 1) 0 acc).toList =
      acc.toList ++ termsBelow i coeffs 1 := by
  change (if hc : (coeffs[0]?).getD 0 = 0 then acc
    else acc.push ⟨⟨(coeffs[0]?).getD 0, hc⟩, MonicMonomial.ofVarPow i 0⟩).toList = _
  rw [termsBelow_succ]
  split
  · next _ => simp
  · next _ => rw [Array.toList_push]; simp

private theorem buildTermsDesc_toList (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord)) (hfuel : idx < fuel + 1) :
    (buildTermsDesc i coeffs (fuel + 1) idx acc).toList =
      acc.toList ++ termsBelow i coeffs (idx + 1) := by
  match fuel with
  | 0 =>
    have hidx : idx = 0 := by omega
    subst hidx; exact buildTermsDesc_toList_base i coeffs acc 0
  | fuel + 1 =>
    by_cases hidx : idx = 0
    · subst hidx; exact buildTermsDesc_toList_base i coeffs acc (fuel + 1)
    · have hidx' : idx - 1 < fuel + 1 := by omega
      show (buildTermsDesc i coeffs (fuel + 2) idx acc).toList = _
      unfold buildTermsDesc
      simp only [hidx, ↓reduceIte]
      split
      · next hc =>
        rw [buildTermsDesc_toList i coeffs fuel (idx - 1) acc hidx',
          show idx - 1 + 1 = idx from by omega, termsBelow_succ]
        simp only [dif_pos hc]
      · next hc =>
        rw [buildTermsDesc_toList i coeffs fuel (idx - 1)
            (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩) hidx',
          Array.toList_push, show idx - 1 + 1 = idx from by omega, termsBelow_succ]
        simp only [dif_neg hc, List.append_assoc, List.cons_append, List.nil_append]

theorem image_terms_toList (i : Fin n) (p : AzPolynomial R) :
    (AzPolynomial.toAzMvPolynomial i ord p).terms.toList =
      termsBelow i p.coeffs p.coeffs.size := by
  unfold AzPolynomial.toAzMvPolynomial
  split
  · next h => rw [h]; rfl
  · next h =>
    show (buildTermsDesc i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]).toList =
      termsBelow i p.coeffs p.coeffs.size
    have key := buildTermsDesc_toList (ord := ord) i p.coeffs (p.coeffs.size - 1) (p.coeffs.size - 1) #[]
      (by omega)
    rw [Nat.sub_add_cancel (show 1 ≤ p.coeffs.size by omega)] at key
    simpa using key

/-! ### Leading coefficient is nonzero -/

omit [LinearOrder R] in
private theorem coeff_top_ne_zero {p : AzPolynomial R} (h : 0 < p.coeffs.size) :
    (p.coeffs[p.coeffs.size - 1]?).getD 0 ≠ 0 := by
  have hb := p.last_ne_zero
  rw [Array.back?_eq_getElem?,
    Array.getElem?_eq_getElem (show p.coeffs.size - 1 < p.coeffs.size by omega)] at hb
  rw [Array.getElem?_eq_getElem (show p.coeffs.size - 1 < p.coeffs.size by omega)]
  simp only [Option.getD_some]
  intro heq; exact hb (by rw [heq])

/-! ### `degreeKey` of an embedded polynomial is the coefficient size -/

theorem totalDegree_image (i : Fin n) (p : AzPolynomial R) (h : 0 < p.coeffs.size) :
    (AzPolynomial.toAzMvPolynomial i ord p).totalDegree = p.coeffs.size - 1 := by
  rw [AzMvPolynomial.totalDegree, ← Array.foldl_toList, image_terms_toList]
  apply le_antisymm
  · apply foldl_max_le _ _ _ _ (by omega)
    intro m hm
    have := termsBelow_totalDegree_lt i p.coeffs p.coeffs.size m hm
    omega
  · have hmem := termsBelow_mem_top (ord := ord) i p.coeffs (p.coeffs.size - 1)
      (coeff_top_ne_zero h)
    rw [Nat.sub_add_cancel h] at hmem
    have hle := le_foldl_max (termsBelow i p.coeffs p.coeffs.size)
      (fun m => m.totalDegree) 0 hmem
    rwa [term_totalDegree] at hle

theorem degreeKey_image (i : Fin n) (p : AzPolynomial R) :
    AzMvPolynomial.degreeKey (AzPolynomial.toAzMvPolynomial i ord p) = p.coeffs.size := by
  rcases Nat.eq_zero_or_pos p.coeffs.size with h | h
  · have himg : AzPolynomial.toAzMvPolynomial i ord p = (0 : AzMvPolynomial n R ord) := by
      unfold AzPolynomial.toAzMvPolynomial; rw [dif_pos h]; rfl
    rw [himg, h]; rfl
  · have hnil : (AzPolynomial.toAzMvPolynomial i ord p).terms.toList ≠ [] := by
      rw [image_terms_toList]
      have hmem := termsBelow_mem_top (ord := ord) i p.coeffs (p.coeffs.size - 1)
        (coeff_top_ne_zero h)
      rw [Nat.sub_add_cancel h] at hmem
      exact List.ne_nil_of_mem hmem
    have hne : (AzPolynomial.toAzMvPolynomial i ord p).terms.isEmpty = false := by
      cases hb : (AzPolynomial.toAzMvPolynomial i ord p).terms.isEmpty
      · rfl
      · exact absurd (Array.toList_eq_nil_iff.mpr (Array.isEmpty_iff.mp hb)) hnil
    rw [AzMvPolynomial.degreeKey, if_neg (by rw [hne]; decide), totalDegree_image i p h]
    omega

/-! ### The two term scans agree -/

private theorem ct_cons_cons (x : Monomial n R ord) (xs : List (Monomial n R ord))
    (y : Monomial n R ord) (ys : List (Monomial n R ord)) :
    AzMvPolynomial.compareTerms (x :: xs) (y :: ys) =
      match Ord.compare x.monic y.monic with
      | .gt => Ord.compare x.coeff.val (0 : R)
      | .lt => Ord.compare (0 : R) y.coeff.val
      | .eq =>
        match Ord.compare x.coeff.val y.coeff.val with
        | .eq => AzMvPolynomial.compareTerms xs ys
        | o => o := rfl

private theorem compareTerms_cons_lt_all (x : Monomial n R ord)
    (ta tb : List (Monomial n R ord)) (h : ∀ m ∈ tb, m.monic < x.monic) :
    AzMvPolynomial.compareTerms (x :: ta) tb = Ord.compare x.coeff.val (0 : R) := by
  cases tb with
  | nil => rfl
  | cons y ys => rw [ct_cons_cons, compare_gt_iff_gt.mpr (h y List.mem_cons_self)]

private theorem compareTerms_lt_all_cons (ta : List (Monomial n R ord))
    (y : Monomial n R ord) (tb : List (Monomial n R ord))
    (h : ∀ m ∈ ta, m.monic < y.monic) :
    AzMvPolynomial.compareTerms ta (y :: tb) = Ord.compare (0 : R) y.coeff.val := by
  cases ta with
  | nil => rfl
  | cons x xs => rw [ct_cons_cons, compare_lt_iff_lt.mpr (h x List.mem_cons_self)]

/-- The heart: `compareTerms` on the two descending term lists equals the
univariate top-down coefficient scan. -/
theorem compareTerms_termsBelow (i : Fin n) (a b : Array R) (N : ℕ) :
    AzMvPolynomial.compareTerms (termsBelow i a (ord := ord) N) (termsBelow i b (ord := ord) N) =
      AzPolynomial.compareTopDown a b N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [AzPolynomial.compareTopDown, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    by_cases hca : (a[k]?).getD 0 = 0 <;> by_cases hcb : (b[k]?).getD 0 = 0
    · rw [termsBelow_succ, termsBelow_succ, dif_pos hca, dif_pos hcb, ih, hca, hcb,
        compare_eq_iff_eq.mpr (rfl : (0 : R) = 0)]
    · rw [termsBelow_succ, termsBelow_succ, dif_pos hca, dif_neg hcb,
        compareTerms_lt_all_cons _ _ _ (termsBelow_monic_lt i a k), hca]
      rcases hX : Ord.compare (0 : R) ((b[k]?).getD 0) with _ | _ | _
      · rfl
      · exact absurd (compare_eq_iff_eq.mp hX).symm hcb
      · rfl
    · rw [termsBelow_succ, termsBelow_succ, dif_neg hca, dif_pos hcb,
        compareTerms_cons_lt_all _ _ _ (termsBelow_monic_lt i b k), hcb]
      rcases hX : Ord.compare ((a[k]?).getD 0) (0 : R) with _ | _ | _
      · rfl
      · exact absurd (compare_eq_iff_eq.mp hX) hca
      · rfl
    · rw [termsBelow_succ, termsBelow_succ, dif_neg hca, dif_neg hcb, ct_cons_cons,
        compare_eq_iff_eq.mpr
          (rfl : (MonicMonomial.ofVarPow i k : MonicMonomial n ord) = MonicMonomial.ofVarPow i k)]
      rcases hX : Ord.compare ((a[k]?).getD 0) ((b[k]?).getD 0) with _ | _ | _
      · rfl
      · exact ih
      · rfl

/-! ### `compare` agreement and strict monotonicity -/

theorem compare_image_eq (i : Fin n) (p q : AzPolynomial R) :
    AzMvPolynomial.compare (AzPolynomial.toAzMvPolynomial i ord p)
      (AzPolynomial.toAzMvPolynomial i ord q) = AzPolynomial.compare p q := by
  rw [AzMvPolynomial.compare, AzPolynomial.compare, degreeKey_image, degreeKey_image,
    image_terms_toList, image_terms_toList]
  rcases lt_trichotomy p.coeffs.size q.coeffs.size with hs | hs | hs
  · rw [compare_lt_iff_lt.mpr hs, if_pos hs]
  · rw [compare_eq_iff_eq.mpr hs, if_neg (by omega), if_neg (by omega), ← hs,
      compareTerms_termsBelow]
  · rw [compare_gt_iff_gt.mpr hs, if_neg (by omega), if_pos hs]

/-- The univariate embedding is strictly monotone. -/
theorem toAzMvPolynomial_strictMono (i : Fin n) :
    StrictMono (fun p : AzPolynomial R => AzPolynomial.toAzMvPolynomial i ord p) := by
  intro p q hpq
  show AzMvPolynomial.compare (AzPolynomial.toAzMvPolynomial i ord p)
    (AzPolynomial.toAzMvPolynomial i ord q) = .lt
  rw [compare_image_eq]; exact hpq

theorem toAzMvPolynomial_lt_iff (i : Fin n) (p q : AzPolynomial R) :
    AzPolynomial.toAzMvPolynomial i ord p < AzPolynomial.toAzMvPolynomial i ord q ↔ p < q :=
  (toAzMvPolynomial_strictMono i).lt_iff_lt

theorem toAzMvPolynomial_le_iff (i : Fin n) (p q : AzPolynomial R) :
    AzPolynomial.toAzMvPolynomial i ord p ≤ AzPolynomial.toAzMvPolynomial i ord q ↔ p ≤ q :=
  (toAzMvPolynomial_strictMono i).le_iff_le

/-! ### Tests -/

section Tests

private def upoly (s : String) : AzPolynomial AzInt := (AzPolynomial.parseAzPolynomial s).getD 0
private def emb (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (upoly s).toAzMvPolynomial (0 : Fin 2) .Degrevlex

-- the embedding preserves the univariate order term-for-term
#guard emb "x" < emb "x^2"
#guard emb "0" < emb "-5"
#guard emb "x^2+x+1" < emb "x^2+x+2"
#guard AzMvPolynomial.compare (emb "x^3-1") (emb "x^2+50*x") == .gt

end Tests

end Azurite
