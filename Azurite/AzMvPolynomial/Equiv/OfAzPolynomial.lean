import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.IntContent
import Azurite.AzPolynomial.Equiv.Content
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Gcd
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzPolynomial.toAzMvPolynomial` ↔ `Polynomial.eval₂ C (X i)`

We prove that converting a univariate `AzPolynomial` to an `AzMvPolynomial`
via `toAzMvPolynomial i` agrees with Mathlib's embedding via `eval₂ C (X i)`.

```
toMvPoly (p.toAzMvPolynomial i) =
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (toPoly p)
```
-/

namespace Azurite
open AzMvPolynomial MvPolynomial Polynomial _root_.Azurite.MonomialOrder

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### ofVarPow to Finsupp.single -/

theorem ofVarPow_toFinsupp (i : Fin n) (k : ℕ) :
    (MonicMonomial.ofVarPow i k : MonicMonomial n ord).toFinsupp =
    Finsupp.single i k := by
  classical
  ext w
  simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Finsupp.single_apply,
    MonicMonomial.ofVarPow]
  by_cases h : i = w
  · subst h; simp
  · have h' : (i : Fin n) ≠ ⟨(w : Fin n).val, w.isLt⟩ := by
      intro heq; apply h; ext; exact Fin.val_eq_of_eq heq
    simp [h']

/-! ### buildTermsDesc loop invariant -/

/-- Base case: when `idx = 0`, `buildTermsDesc` produces exactly one monomial term
    (or none if the coefficient is zero). -/
private theorem buildTermsDesc_base (i : Fin n) (coeffs : Array R)
    (acc : Array (Monomial n R ord)) (fuel : ℕ) :
    ((buildTermsDesc i coeffs (fuel + 1) 0 acc).toList.map Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    (MvPolynomial.monomial (Finsupp.single i 0)) ((coeffs[0]?).getD 0) := by
  classical
  change ((if hc : (coeffs[0]?).getD 0 = 0 then acc
    else acc.push ⟨⟨(coeffs[0]?).getD 0, hc⟩, MonicMonomial.ofVarPow i 0⟩).toList.map
    Monomial.toMvPoly).sum = _
  split
  · next hc => simp [hc]
  · next hc =>
    rw [Array.toList_push, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    congr 1; unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]

/-- Loop invariant: the sum of `Monomial.toMvPoly` over the output of
    `buildTermsDesc` equals the accumulator sum plus the polynomial sum
    `∑ k ∈ range (idx + 1), monomial (single i k) (coeffs[k])`. -/
theorem buildTermsDesc_toMvPoly_sum (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord))
    (hfuel : idx < fuel + 1) :
    ((buildTermsDesc i coeffs (fuel + 1) idx acc).toList.map
      Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    ∑ k ∈ Finset.range (idx + 1),
      (MvPolynomial.monomial (Finsupp.single i k)) ((coeffs[k]?).getD 0) := by
  classical
  match fuel with
  | 0 =>
    have hidx : idx = 0 := by omega
    subst hidx
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    exact buildTermsDesc_base i coeffs acc 0
  | fuel + 1 =>
    by_cases hidx : idx = 0
    · subst hidx
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      exact buildTermsDesc_base i coeffs acc (fuel + 1)
    · have hidx' : idx - 1 < fuel + 1 := by omega
      show ((buildTermsDesc i coeffs (fuel + 2) idx acc).toList.map
        Monomial.toMvPoly).sum = _
      unfold buildTermsDesc
      simp only [hidx, ↓reduceIte]
      split
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum i coeffs fuel (idx - 1) acc hidx']
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        simp [hc]
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum i coeffs fuel (idx - 1)
            (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩) hidx']
        rw [Array.toList_push, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton]
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        conv_lhs =>
          rw [show Monomial.toMvPoly (⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩ :
            Monomial n R ord) =
            (MvPolynomial.monomial (Finsupp.single i idx)) ((coeffs[idx]?).getD 0) from by
            unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]]
        ring

/-! ### Main equivalence -/

/-- Converting via `toAzMvPolynomial i` then `toMvPoly` equals
    embedding via `Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i)`. -/
theorem toMvPoly_toAzMvPolynomial (i : Fin n)
    (p : AzPolynomial R) :
    toMvPoly (p.toAzMvPolynomial i (ord := ord)) =
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (AzPolynomial.toPoly p) := by
  classical
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, Polynomial.eval₂_eq_sum_range]
  simp only [AzPolynomial.toAzMvPolynomial]
  split
  · -- p.coeffs.size = 0 (zero polynomial)
    next h =>
    simp only [List.map_nil, List.sum_nil]
    have hnd : (AzPolynomial.toPoly p).natDegree = 0 := by
      rw [AzPolynomial.natDegree_toPoly]
      simp [Azurite.AzPolynomial.natDegree, h]
    rw [hnd, Finset.sum_range_one, pow_zero, mul_one]
    have : (AzPolynomial.toPoly p).coeff 0 = 0 := by
      rw [coeff_toPoly_eq]; simp [Azurite.AzPolynomial.coeff, h]
    rw [this, map_zero]
  · -- p.coeffs.size > 0
    next h =>
    change ((buildTermsDesc i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]).toList.map
      Monomial.toMvPoly).sum = _
    set m := p.coeffs.size - 1 with hm_def
    have hm : m + 1 = p.coeffs.size := Nat.succ_pred (by omega)
    rw [show p.coeffs.size = m + 1 from hm.symm]
    rw [buildTermsDesc_toMvPoly_sum i p.coeffs m m #[] (by omega)]
    simp only [List.map_nil, List.sum_nil, zero_add]
    rw [show (AzPolynomial.toPoly p).natDegree + 1 = m + 1 from by
      rw [AzPolynomial.natDegree_toPoly]
      unfold Azurite.AzPolynomial.natDegree; omega]
    congr 1; ext k
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, coeff_toPoly_eq]
    simp only [Azurite.AzPolynomial.coeff]

/-! ### Leading coefficient and content of the lift -/

section OfAzPolynomialContent

variable {R : Type _} [Semiring R] [DecidableEq R] {n : ℕ} {ord : MonomialOrder}

/-- `buildTermsDesc` only appends to `acc`, so the head of the resulting term
    list is unchanged when `acc` is already nonempty. -/
private theorem buildTermsDesc_toList_head? (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord)) (hacc : acc.toList ≠ []) :
    (buildTermsDesc i coeffs fuel idx acc).toList.head? = acc.toList.head? := by
  have push_head : ∀ (a : Array (Monomial n R ord)) (t : Monomial n R ord),
      a.toList ≠ [] → (a.push t).toList.head? = a.toList.head? := by
    intro a t ha
    rw [Array.toList_push]
    cases h : a.toList with
    | nil => exact absurd h ha
    | cons x xs => simp
  induction fuel generalizing idx acc with
  | zero => rfl
  | succ fuel ih =>
    show (buildTermsDesc i coeffs (fuel + 1) idx acc).toList.head? = acc.toList.head?
    unfold buildTermsDesc
    simp only
    split
    · -- idx = 0
      split
      · rfl
      · exact push_head acc _ hacc
    · -- idx ≠ 0, recurse
      split
      · -- c = 0, acc unchanged
        exact ih (idx - 1) acc hacc
      · -- c ≠ 0, pushed
        next hc =>
        have hne : (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩).toList ≠ [] := by
          rw [Array.toList_push]; exact List.append_ne_nil_of_left_ne_nil hacc _
        rw [ih (idx - 1) _ hne, push_head acc _ hacc]

/-- Every term produced by `buildTermsDesc` either was already in `acc` or has a
    coefficient that appears in `coeffs`. -/
private theorem buildTermsDesc_coeff_mem (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord)) :
    ∀ m ∈ (buildTermsDesc i coeffs fuel idx acc).toList,
      m ∈ acc.toList ∨ m.coeff.val ∈ coeffs.toList := by
  have step : ∀ (j : ℕ) (m : Monomial n R ord)
      (hc : (coeffs[j]?).getD 0 ≠ 0),
      m = (⟨⟨_, hc⟩, MonicMonomial.ofVarPow i j⟩ : Monomial n R ord) →
      m.coeff.val ∈ coeffs.toList := by
    intro j m hc hm
    subst hm
    have hsome : coeffs[j]? = some ((coeffs[j]?).getD 0) := by
      cases hcj : coeffs[j]? with
      | none => rw [hcj] at hc; simp at hc
      | some v => rfl
    have hlt : j < coeffs.size := by
      rw [Array.getElem?_eq_some_iff] at hsome; exact hsome.1
    have : coeffs.toList[j]? = some ((coeffs[j]?).getD 0) := by
      rw [Array.getElem?_toList]; exact hsome
    exact List.mem_of_getElem? this
  induction fuel generalizing idx acc with
  | zero => intro m hm; left; exact hm
  | succ fuel ih =>
    intro m hm
    rw [show buildTermsDesc i coeffs (fuel + 1) idx acc =
      (if idx = 0 then
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)
      else buildTermsDesc i coeffs fuel (idx - 1)
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)) from rfl] at hm
    split at hm
    · -- idx = 0
      split at hm
      · left; exact hm
      · next hc =>
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · left; exact hm
        · right; exact step idx _ hc rfl
    · -- idx ≠ 0
      rcases ih (idx - 1) _ m hm with hm' | hm'
      · split at hm'
        · left; exact hm'
        · next hc =>
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
          rcases hm' with hm' | rfl
          · left; exact hm'
          · right; exact step idx _ hc rfl
      · right; exact hm'

/-- Every term already in `acc` remains in the output of `buildTermsDesc`. -/
private theorem buildTermsDesc_subset (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord)) :
    ∀ x ∈ acc.toList, x ∈ (buildTermsDesc i coeffs fuel idx acc).toList := by
  induction fuel generalizing idx acc with
  | zero => intro x hx; exact hx
  | succ fuel ih =>
    intro x hx
    rw [show buildTermsDesc i coeffs (fuel + 1) idx acc =
      (if idx = 0 then
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)
      else buildTermsDesc i coeffs fuel (idx - 1)
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)) from rfl]
    have hxacc' : x ∈ (if hc : (coeffs[idx]?).getD 0 = 0 then acc
        else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩).toList := by
      split
      · exact hx
      · rw [Array.toList_push, List.mem_append]; left; exact hx
    split
    · exact hxacc'
    · exact ih (idx - 1) _ x hxacc'

/-- If `coeffs[k]` is a nonzero coefficient reached by `buildTermsDesc` (i.e.
    `k ≤ idx` and it is processed before the fuel runs out), then some output
    term carries that coefficient. -/
private theorem buildTermsDesc_mem_of_coeff (i : Fin n) (coeffs : Array R)
    (fuel idx k : ℕ) (acc : Array (Monomial n R ord))
    (c : R) (hc : coeffs[k]? = some c) (hc0 : c ≠ 0)
    (hk : k ≤ idx) (hfuel : idx - k < fuel) :
    ∃ m ∈ (buildTermsDesc i coeffs fuel idx acc).toList, m.coeff.val = c := by
  induction fuel generalizing idx acc with
  | zero => omega
  | succ fuel ih =>
    rw [show buildTermsDesc i coeffs (fuel + 1) idx acc =
      (if idx = 0 then
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)
      else buildTermsDesc i coeffs fuel (idx - 1)
        (if hc : (coeffs[idx]?).getD 0 = 0 then acc
         else acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩)) from rfl]
    by_cases hki : k = idx
    · -- current step processes k; push the term (coeff nonzero) and it survives
      subst hki
      have hcv : (coeffs[k]?).getD 0 = c := by rw [hc]; rfl
      have hcne : (coeffs[k]?).getD 0 ≠ 0 := by rw [hcv]; exact hc0
      simp only [dif_neg hcne]
      have htmem :
          (⟨⟨(coeffs[k]?).getD 0, hcne⟩, MonicMonomial.ofVarPow i k⟩ : Monomial n R ord) ∈
          (acc.push ⟨⟨(coeffs[k]?).getD 0, hcne⟩, MonicMonomial.ofVarPow i k⟩).toList := by
        rw [Array.toList_push, List.mem_append, List.mem_singleton]; right; rfl
      refine ⟨⟨⟨(coeffs[k]?).getD 0, hcne⟩, MonicMonomial.ofVarPow i k⟩, ?_, hcv⟩
      split
      · exact htmem
      · exact buildTermsDesc_subset i coeffs fuel (k - 1) _ _ htmem
    · -- k < idx, recurse
      have hklt : k < idx := lt_of_le_of_ne hk hki
      have hidx0 : idx ≠ 0 := by omega
      rw [if_neg hidx0]
      exact ih (idx - 1) _ (by omega) (by omega)

end OfAzPolynomialContent

/-- The leading coefficient of the multivariate lift equals the univariate
    leading coefficient. -/
theorem AzMvPolynomial.leadingCoeff_toAzMvPolynomial {n : ℕ} (i : Fin n)
    {ord : MonomialOrder} (p : AzPolynomial AzInt) :
    AzMvPolynomial.leadingCoeff (p.toAzMvPolynomial i ord) = p.leadingCoeff := by
  simp only [AzPolynomial.toAzMvPolynomial]
  split
  · -- p.coeffs.size = 0
    next h =>
    have hc : p.coeffs = #[] := Array.eq_empty_of_size_eq_zero h
    simp [AzMvPolynomial.leadingCoeff, AzMvPolynomial.leadCoeff, AzMvPolynomial.leadTerm,
      AzPolynomial.leadingCoeff, AzPolynomial.coeff, hc]
  · -- p.coeffs.size > 0
    next h =>
    set m := p.coeffs.size - 1 with hm
    have hsz : p.coeffs.size = m + 1 := by omega
    -- the leading (index m) coefficient is nonzero
    have hlt : m < p.coeffs.size := by omega
    have hlast : (p.coeffs[m]?).getD 0 ≠ 0 := by
      intro hz
      apply p.last_ne_zero
      have hb : p.coeffs.back? = p.coeffs[m]? := by simp [Array.back?, hm]
      rw [Array.getElem?_eq_getElem hlt, Option.getD_some] at hz
      rw [hb, Array.getElem?_eq_getElem hlt, hz]
    -- head of the built term list
    have hhead : (buildTermsDesc i p.coeffs p.coeffs.size m #[]).toList.head?
        = some (⟨⟨(p.coeffs[m]?).getD 0, hlast⟩, MonicMonomial.ofVarPow i m⟩
            : Monomial n AzInt ord) := by
      rw [hsz]
      show (buildTermsDesc i p.coeffs (m + 1) m #[]).toList.head? = _
      rw [show buildTermsDesc i p.coeffs (m + 1) m #[] =
        (if m = 0 then
          (if hc : (p.coeffs[m]?).getD 0 = 0 then #[]
           else (#[] : Array (Monomial n AzInt ord)).push
             ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i m⟩)
        else buildTermsDesc i p.coeffs m (m - 1)
          (if hc : (p.coeffs[m]?).getD 0 = 0 then #[]
           else (#[] : Array (Monomial n AzInt ord)).push
             ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i m⟩)) from rfl]
      rw [dif_neg hlast]
      by_cases hm0 : m = 0
      · rw [if_pos hm0]; rfl
      · rw [if_neg hm0, buildTermsDesc_toList_head? i p.coeffs m (m - 1) _ (by simp)]
        rfl
    -- conclude
    have hzero0 : (buildTermsDesc i p.coeffs p.coeffs.size m #[])[0]? =
        some (⟨⟨(p.coeffs[m]?).getD 0, hlast⟩, MonicMonomial.ofVarPow i m⟩
            : Monomial n AzInt ord) := by
      rw [← Array.getElem?_toList, ← List.head?_eq_getElem?]
      exact hhead
    simp only [AzMvPolynomial.leadingCoeff, AzMvPolynomial.leadCoeff,
      AzMvPolynomial.leadTerm]
    rw [hzero0, AzPolynomial.leadingCoeff, AzPolynomial.coeff, AzPolynomial.natDegree, ← hm]
    rfl

/-- The integer content of the multivariate lift equals the univariate content. -/
theorem AzMvPolynomial.intContent_toAzMvPolynomial {n : ℕ} (i : Fin n)
    {ord : MonomialOrder} (p : AzPolynomial AzInt) :
    AzMvPolynomial.intContent (p.toAzMvPolynomial i ord) = p.content := by
  apply Azurite.AzNat.toNat_injective
  -- content descends to a `Nat.gcd` fold over coefficient magnitudes
  have hcontent : p.content.toNat
      = (p.coeffs.toList.map (fun z => z.abs.toNat)).foldl Nat.gcd 0 :=
    Azurite.AzPolynomial.toNat_content p
  -- intContent likewise, over term-coefficient magnitudes
  have hintContent : (AzMvPolynomial.intContent (p.toAzMvPolynomial i ord)).toNat
      = ((p.toAzMvPolynomial i ord).terms.toList.map
          (fun m => m.coeff.val.abs.toNat)).foldl Nat.gcd 0 := by
    rw [AzMvPolynomial.intContent, ← Array.foldl_toList]
    have aux : ∀ (l : List (Monomial n AzInt ord)) (acc : AzNat),
        (l.foldl (fun acc m => AzNat.gcd acc m.coeff.val.abs) acc).toNat
          = (l.map (fun m => m.coeff.val.abs.toNat)).foldl Nat.gcd acc.toNat := by
      intro l
      induction l with
      | nil => intro acc; rfl
      | cons m l ih =>
        intro acc
        rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, Azurite.AzNat.toNat_gcd]
    rw [aux]; rfl
  rw [hcontent, hintContent]
  set L1 := p.coeffs.toList.map (fun z : AzInt => z.abs.toNat) with hL1
  set L2 := (p.toAzMvPolynomial i ord).terms.toList.map
    (fun m => m.coeff.val.abs.toNat) with hL2
  -- membership correspondence between term coefficients and nonzero coefficients
  by_cases hpz : p.coeffs.size = 0
  · have hc : p.coeffs = #[] := Array.eq_empty_of_size_eq_zero hpz
    have hlift : p.toAzMvPolynomial i ord = 0 := by
      simp only [AzPolynomial.toAzMvPolynomial, hpz, ↓reduceDIte]; rfl
    rw [hL1, hL2, hc, hlift]; rfl
  · have hlift_terms : (p.toAzMvPolynomial i ord).terms =
        buildTermsDesc i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[] := by
      simp only [AzPolynomial.toAzMvPolynomial, hpz, ↓reduceDIte]
    -- L2 ⊆ magnitudes of coefficients (Direction: content ∣ intContent)
    have hA : (L1.foldl Nat.gcd 0) ∣ (L2.foldl Nat.gcd 0) := by
      apply Azurite.AzPolynomial.dvd_foldl_gcd L2 0 (dvd_zero _)
      intro a ha
      rw [hL2, List.mem_map] at ha
      obtain ⟨mo, hmo, rfl⟩ := ha
      rw [hlift_terms] at hmo
      rcases buildTermsDesc_coeff_mem i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]
        mo hmo with h0 | h0
      · simp at h0
      · have : mo.coeff.val.abs.toNat ∈ L1 := by
          rw [hL1, List.mem_map]; exact ⟨mo.coeff.val, h0, rfl⟩
        exact Azurite.AzPolynomial.foldl_gcd_dvd_mem L1 0 this
    -- magnitudes of coefficients ⊆ L2 ∪ {0} (Direction: intContent ∣ content)
    have hB : (L2.foldl Nat.gcd 0) ∣ (L1.foldl Nat.gcd 0) := by
      apply Azurite.AzPolynomial.dvd_foldl_gcd L1 0 (dvd_zero _)
      intro a ha
      rw [hL1, List.mem_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
      by_cases hz0 : p.coeffs.toList[k] = 0
      · rw [hz0, show (0 : AzInt).abs.toNat = 0 from Azurite.AzNat.toNat_zero]
        exact dvd_zero _
      · have hkc : p.coeffs[k]? = some p.coeffs.toList[k] := by
          rw [← Array.getElem?_toList]
          exact List.getElem?_eq_getElem hk
        have hkm : k ≤ p.coeffs.size - 1 := by
          have : k < p.coeffs.size := by simpa using hk
          omega
        obtain ⟨mo, hmo, hmoc⟩ := buildTermsDesc_mem_of_coeff i p.coeffs
          p.coeffs.size (p.coeffs.size - 1) k #[] _ hkc hz0 hkm (by omega)
        have hmem : p.coeffs.toList[k].abs.toNat ∈ L2 := by
          rw [hL2, hlift_terms, List.mem_map]
          exact ⟨mo, hmo, by rw [hmoc]⟩
        exact Azurite.AzPolynomial.foldl_gcd_dvd_mem L2 0 hmem
    exact Nat.dvd_antisymm hB hA

end Azurite
