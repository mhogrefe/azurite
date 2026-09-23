import Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminant

/-!
# BPR Proposition 8.27: normalization and uniqueness of `pdet`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.3.2.1.

The construction `pdet` and its multilinearity / alternation are in
`PolynomialDeterminant.lean`. This file adds the **monomial normalization** of
`pdet` (its defining values on strictly-decreasing monomial tuples) and the
**uniqueness** of a multilinear alternating map with those values, completing
Proposition 8.27.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- The monomial family `(X^{e 0}, …, X^{e (m-1)})` as elements of `𝓕_n`. -/
noncomputable def monoFamily (e : Fin m → ℕ) (he : ∀ r, e r < n) :
    Fin m → degreeLT K n :=
  fun r => ⟨X ^ (e r), by rw [mem_degreeLT, degree_X_pow]; exact_mod_cast he r⟩

/-- The column-index map `pdetColIdx n i` is injective on `Fin m` when
    `m ≤ n` and `i ≤ n - m` (the last column `i` is distinct from the top
    columns `n-1, …, n-m+1`). -/
theorem pdetColIdx_injective (hmn : m ≤ n) (i : ℕ) (hi : i ≤ n - m) :
    Function.Injective (fun c : Fin m => pdetColIdx n i c) := by
  intro c c' h
  have hc := c.isLt
  have hc' := c'.isLt
  simp only [pdetColIdx] at h
  apply Fin.ext
  by_cases h1 : (c : ℕ) + 1 < m <;> by_cases h2 : (c' : ℕ) + 1 < m <;>
    simp only [h1, h2, ite_true, ite_false] at h <;> omega

/-- **Positive normalization (BPR Proposition 8.27).** On the top-monomial tuple
    `(X^{n-1}, …, X^{n-m+1}, X^i)` (so `e r = n-1-r` for `r < m-1`),
    `pdet` returns `X^i` where `i = e (m-1)`. -/
theorem normalization_pdet_pos (e : Fin m → ℕ) (hmn : m ≤ n)
    (last : Fin m) (hlast : (last : ℕ) + 1 = m)
    (he : ∀ r, e r < n)
    (hcond : ∀ r : Fin m, (r : ℕ) + 1 < m → e r = n - 1 - (r : ℕ))
    (hi : e last ≤ n - m) :
    pdet (monoFamily e he) = pdetMono (K := K) ⟨e last, by omega⟩ := by
  -- The exponents are exactly the column indices for the last column `e last`.
  have he_val : ∀ s : Fin m, e s = pdetColIdx n (e last) s := by
    intro s
    simp only [pdetColIdx]
    by_cases hs : (s : ℕ) + 1 < m
    · rw [ite_eq_left hs, hcond s hs]
    · rw [ite_eq_right hs]
      congr 1
      apply Fin.ext
      have := s.isLt
      omega
  -- The minor matrix at `k = e last` is the identity.
  have hIdent : pdetMinorMat (monoFamily (K := K) e he) (e last) = 1 := by
    ext r c
    rw [pdetMinorMat]
    show (X ^ (e r) : K[X]).coeff (pdetColIdx n (e last) c) = _
    rw [coeff_X_pow, Matrix.one_apply]
    by_cases hrc : r = c
    · subst hrc; rw [ite_eq_left (he_val r).symm, ite_eq_left rfl]
    · rw [ite_eq_right hrc, ite_eq_right]
      intro hcon
      exact hrc ((pdetColIdx_injective hmn (e last) hi (hcon.trans (he_val r))).symm)
  -- Each minor: `1` at `k = e last`, `0` elsewhere (the last row vanishes).
  have minorval : ∀ k : Fin (n - m + 1),
      pdetMinor (monoFamily (K := K) e he) (k : ℕ) = if (k : ℕ) = e last then 1 else 0 := by
    intro k
    by_cases hk : (k : ℕ) = e last
    · rw [ite_eq_left hk, pdetMinor, hk, hIdent, Matrix.det_one]
    · rw [ite_eq_right hk, pdetMinor]
      apply Matrix.det_eq_zero_of_row_eq_zero last
      intro c
      rw [pdetMinorMat]
      show (X ^ (e last) : K[X]).coeff (pdetColIdx n (k : ℕ) c) = 0
      rw [coeff_X_pow, ite_eq_right]
      intro hcon
      have hkle := k.isLt
      have hcc := c.isLt
      simp only [pdetColIdx] at hcon
      by_cases hc1 : (c : ℕ) + 1 < m <;> simp only [hc1, ite_true, ite_false] at hcon <;> omega
  -- Assemble the sum.
  unfold pdet
  rw [Finset.sum_congr rfl (fun k _ => by rw [minorval k])]
  rw [Finset.sum_eq_single ⟨e last, by omega⟩]
  · simp
  · intro b _ hb
    rw [ite_eq_right, zero_smul]
    intro hbi; exact hb (Fin.ext hbi)
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-- Two strictly-decreasing functions `Fin m → ℕ` with the same image are equal. -/
theorem fin_strictAnti_eq {m : ℕ} {f g : Fin m → ℕ} (hf : StrictAnti f) (hg : StrictAnti g)
    (himg : ∀ r, ∃ s, g s = f r) : f = g := by
  -- The reverse inclusion of images, by finiteness.
  have hsub : Finset.univ.image f ⊆ Finset.univ.image g := by
    intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨r, _, rfl⟩ := hx
    obtain ⟨s, hs⟩ := himg r
    exact ⟨s, Finset.mem_univ s, hs⟩
  have hcard : (Finset.univ.image f).card = (Finset.univ.image g).card := by
    rw [Finset.card_image_of_injective _ hf.injective,
      Finset.card_image_of_injective _ hg.injective]
  have himg_eq : Finset.univ.image f = Finset.univ.image g :=
    Finset.eq_of_subset_of_card_le hsub hcard.symm.le
  have himg' : ∀ s, ∃ r, f r = g s := by
    intro s
    have hmem : g s ∈ Finset.univ.image f := by
      rw [himg_eq]; exact Finset.mem_image_of_mem g (Finset.mem_univ s)
    rw [Finset.mem_image] at hmem
    obtain ⟨r, _, hr⟩ := hmem
    exact ⟨r, hr⟩
  -- Pointwise equality by strong induction on the index.
  have key : ∀ N : ℕ, ∀ r : Fin m, (r : ℕ) = N → f r = g r := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro r hrN
      have ihlt : ∀ s : Fin m, (s : ℕ) < (r : ℕ) → f s = g s := fun s hs =>
        ih (s : ℕ) (by omega) s rfl
      obtain ⟨s₀, hs₀⟩ := himg r
      obtain ⟨r₁, hr₁⟩ := himg' r
      have h1 : f r ≤ g r := by
        rcases lt_trichotomy (s₀ : ℕ) (r : ℕ) with h | h | h
        · exact absurd (hf.injective ((ihlt s₀ h).trans hs₀)) (Fin.ne_of_val_ne (by omega))
        · exact le_of_eq (by rw [← hs₀, Fin.ext h])
        · rw [← hs₀]; exact hg.antitone (Fin.le_def.mpr h.le)
      have h2 : g r ≤ f r := by
        rcases lt_trichotomy (r₁ : ℕ) (r : ℕ) with h | h | h
        · exact absurd (hg.injective ((ihlt r₁ h).symm.trans hr₁)) (Fin.ne_of_val_ne (by omega))
        · exact le_of_eq (by rw [← hr₁, Fin.ext h])
        · rw [← hr₁]; exact hf.antitone (Fin.le_def.mpr h.le)
      omega
  funext r
  exact key (r : ℕ) r rfl

/-- `pdetColIdx n k` is strictly decreasing on `Fin m` when `m ≤ n` and `k ≤ n-m`
    (the columns read `n-1 > n-2 > ⋯ > n-m+1 > k`). -/
theorem pdetColIdx_strictAnti (hmn : m ≤ n) (k : ℕ) (hk : k ≤ n - m) :
    StrictAnti (fun c : Fin m => pdetColIdx n k c) := by
  intro c c' hcc
  have h0 := c.isLt
  have h0' := c'.isLt
  have hlt : (c : ℕ) < (c' : ℕ) := hcc
  simp only [pdetColIdx]
  by_cases h1 : (c' : ℕ) + 1 < m <;> by_cases h2 : (c : ℕ) + 1 < m <;>
    simp only [h1, h2, ite_true, ite_false] <;> omega

/-- **Vanishing normalization (BPR Proposition 8.27).** On a strictly-decreasing
    monomial tuple that is *not* `(X^{n-1}, …, X^{n-m+1}, X^i)` (some `e r` with
    `r < m-1` differs from `n-1-r`), `pdet` returns `0`. -/
theorem normalization_pdet_zero (e : Fin m → ℕ) (hmn : m ≤ n)
    (he : ∀ r, e r < n) (hAnti : StrictAnti e)
    (hne : ∃ r₀ : Fin m, (r₀ : ℕ) + 1 < m ∧ e r₀ ≠ n - 1 - (r₀ : ℕ)) :
    pdet (monoFamily (K := K) e he) = 0 := by
  have hminor : ∀ k : Fin (n - m + 1), pdetMinor (monoFamily (K := K) e he) (k : ℕ) = 0 := by
    intro k
    have hke : (k : ℕ) ≤ n - m := by have := k.isLt; omega
    -- Some row is zero: an exponent missing from the column indices.
    have hmiss : ∃ r : Fin m, ∀ c : Fin m, pdetColIdx n (k : ℕ) c ≠ e r := by
      by_contra hall
      push Not at hall
      have heq : e = (fun c : Fin m => pdetColIdx n (k : ℕ) c) :=
        fin_strictAnti_eq hAnti (pdetColIdx_strictAnti hmn (k : ℕ) hke) hall
      obtain ⟨r₀, hr₀lt, hr₀ne⟩ := hne
      apply hr₀ne
      have hval := congrFun heq r₀
      simp only [pdetColIdx, ite_eq_left hr₀lt] at hval
      exact hval
    obtain ⟨r, hr⟩ := hmiss
    rw [pdetMinor]
    apply Matrix.det_eq_zero_of_row_eq_zero r
    intro c
    rw [pdetMinorMat]
    show (X ^ (e r) : K[X]).coeff (pdetColIdx n (k : ℕ) c) = 0
    rw [coeff_X_pow, ite_eq_right (hr c)]
  unfold pdet
  apply Finset.sum_eq_zero
  intro k _
  rw [hminor, zero_smul]

/-- **BPR Proposition 8.27 (existence).** There exists a multilinear alternating
    mapping `(𝓕_n)^m → 𝓕_{n-m+1}` with the normalization values of Proposition
    8.27, namely `pdet`: it is multilinear and alternating, returns `X^{e last}`
    on the top-monomial tuple `(X^{n-1}, …, X^{n-m+1}, X^{e last})`, and `0` on any
    other strictly-decreasing monomial tuple. -/
theorem proposition_8_27_existence (hmn : m ≤ n) :
    ∃ Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1),
      IsMultilinear Φ ∧ IsAlternating Φ ∧
      (∀ (e : Fin m → ℕ) (he : ∀ r, e r < n) (last : Fin m), (last : ℕ) + 1 = m →
        (∀ r : Fin m, (r : ℕ) + 1 < m → e r = n - 1 - (r : ℕ)) → ∀ (hi : e last ≤ n - m),
        Φ (monoFamily e he) = pdetMono ⟨e last, by omega⟩) ∧
      (∀ (e : Fin m → ℕ) (he : ∀ r, e r < n), StrictAnti e →
        (∃ r₀ : Fin m, (r₀ : ℕ) + 1 < m ∧ e r₀ ≠ n - 1 - (r₀ : ℕ)) →
        Φ (monoFamily e he) = 0) :=
  ⟨pdet, isMultilinear_pdet, isAlternating_pdet,
    fun e he last hlast hcond hi => normalization_pdet_pos e hmn last hlast he hcond hi,
    fun e he hAnti hne => normalization_pdet_zero e hmn he hAnti hne⟩

end Azurite.BPR.Chapter8
