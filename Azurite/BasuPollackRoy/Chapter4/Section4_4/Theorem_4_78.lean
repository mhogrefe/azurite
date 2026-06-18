import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Mathlib.RingTheory.Localization.FractionRing

/-!
# BPR Theorem 4.78: Hilbert's Nullstellensatz

Let `𝒫 ⊂ K[X₁, …, X_k]` be finite (with `K` of characteristic zero and `C` algebraically closed).
If a polynomial `P` vanishes on `Zer(𝒫, C^k)`, then `P^n ∈ Ideal(𝒫, K)` for some `n`.

Proof (Rabinowitsch): `𝒫 ∪ {T·P - 1}` (in `X₁, …, X_k, T`) has no common zero in `C^{k+1}`, so by
the weak Nullstellensatz (Theorem 4.72) `1 = ∑ Aᵢ Pᵢ + A·(T·P - 1)` in `K[X₁, …, X_k, T]`.
Substituting `T = 1/P` (over the fraction field of `K[X₁, …, X_k]`) kills the last term, and
clearing denominators by a power of `P` shows a power of `P` lies in `Ideal(𝒫, K)`.

We single out `T = X₀` (the original variables `X₁, …, X_k` embed via `rename Fin.succ`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- Clearing-denominators lemma for the Rabinowitsch trick. With `R := MvPolynomial (Fin k) K`,
`F := FractionRing R`, and `g : Fin (k+1) → F` the substitution `X₀ ↦ (P)⁻¹`, `X_{i+1} ↦ X_i`,
every value `aeval g Q` becomes a genuine element of `R` after multiplying by a suitable power of
`P`. -/
private lemma clear_denom {k : ℕ} (P : MvPolynomial (Fin k) K)
    (g : Fin (k + 1) → FractionRing (MvPolynomial (Fin k) K))
    (hg0 : g 0 = (algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K)) P)⁻¹)
    (hgs : ∀ i : Fin k, g i.succ
      = algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K)) (X i))
    (hPne : algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K)) P ≠ 0)
    (Q : MvPolynomial (Fin (k + 1)) K) :
    ∃ (N : ℕ) (B : MvPolynomial (Fin k) K),
      (algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K)) P) ^ N
        * aeval g Q
        = algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K)) B := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, MvPolynomial.C c, ?_⟩
      rw [pow_zero, one_mul, aeval_C,
        IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k) K)
          (FractionRing (MvPolynomial (Fin k) K)) c,
        MvPolynomial.algebraMap_eq]
  | add Q₁ Q₂ h₁ h₂ =>
      obtain ⟨N₁, B₁, hB₁⟩ := h₁
      obtain ⟨N₂, B₂, hB₂⟩ := h₂
      refine ⟨max N₁ N₂, P ^ (max N₁ N₂ - N₁) * B₁ + P ^ (max N₁ N₂ - N₂) * B₂, ?_⟩
      rw [map_add, mul_add]
      have e₁ : algebraMap _ (FractionRing (MvPolynomial (Fin k) K)) P ^ (max N₁ N₂)
          * aeval g Q₁ = algebraMap _ _ (P ^ (max N₁ N₂ - N₁) * B₁) := by
        rw [map_mul, map_pow, ← hB₁, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have e₂ : algebraMap _ (FractionRing (MvPolynomial (Fin k) K)) P ^ (max N₁ N₂)
          * aeval g Q₂ = algebraMap _ _ (P ^ (max N₁ N₂ - N₂) * B₂) := by
        rw [map_mul, map_pow, ← hB₂, ← mul_assoc, ← pow_add]
        congr 2
        omega
      rw [e₁, e₂, map_add]
  | mul_X Q j h =>
      obtain ⟨N, B, hB⟩ := h
      refine j.cases ?_ ?_
      · -- j = 0
        refine ⟨N + 1, B, ?_⟩
        rw [map_mul, aeval_X, hg0, pow_succ]
        calc algebraMap _ (FractionRing (MvPolynomial (Fin k) K)) P ^ N
              * algebraMap _ _ P * (aeval g Q * (algebraMap _ _ P)⁻¹)
            = (algebraMap _ _ P ^ N * aeval g Q)
              * (algebraMap _ _ P * (algebraMap _ _ P)⁻¹) := by ring
          _ = algebraMap _ _ B * 1 := by rw [hB, mul_inv_cancel₀ hPne]
          _ = algebraMap _ _ B := by rw [mul_one]
      · -- j = i.succ
        intro i
        refine ⟨N, B * X i, ?_⟩
        rw [map_mul, aeval_X, hgs i, ← mul_assoc, hB, ← map_mul]

/-- **BPR Theorem 4.78 (Hilbert's Nullstellensatz).** If `P` vanishes on `Zer(𝒫, C^k)` (with `K`
of characteristic zero and `C` algebraically closed), then some power of `P` lies in
`Ideal(𝒫, K)`. -/
theorem theorem_4_78 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) (P : MvPolynomial (Fin k) K)
    (hP : ∀ x ∈ zerOfFinset C Ps, MvPolynomial.aeval x P = 0) :
    ∃ n : ℕ, P ^ n ∈ idealOfPolys Ps := by
  by_cases hP0 : P = 0
  · exact ⟨1, by simpa only [hP0, pow_one] using Submodule.zero_mem _⟩
  -- Main case
  let R := MvPolynomial (Fin k) K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hφinj : Function.Injective φ := IsFractionRing.injective R F
  have hPne : φ P ≠ 0 := fun h => hP0 (hφinj (h.trans (map_zero φ).symm))
  -- Step 1: Rabinowitsch set
  let ι : R →ₐ[K] MvPolynomial (Fin (k + 1)) K := rename Fin.succ
  have hι : ι = rename Fin.succ := rfl
  let Ps' : Finset (MvPolynomial (Fin (k + 1)) K) :=
    insert (X 0 * ι P - 1) (Ps.image ι)
  have hPs' : Ps' = insert (X 0 * ι P - 1) (Ps.image ι) := rfl
  -- Step 2: no common zero
  have hzer : zerOfFinset C Ps' = ∅ := by
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have hyP : aeval y (ι P) = 0 := by
      have htail : (y ∘ Fin.succ) ∈ zerOfFinset C Ps := by
        intro q hq
        have : aeval y (ι q) = 0 := hy (ι q) (by
          rw [hPs']; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq))
        rwa [hι, aeval_rename] at this
      have := hP _ htail
      rw [hι, aeval_rename]
      exact this
    have hmem0 : aeval y (X 0 * ι P - 1) = 0 :=
      hy _ (by rw [hPs']; exact Finset.mem_insert_self _ _)
    rw [map_sub, map_mul, aeval_X, hyP, mul_zero, map_one, zero_sub] at hmem0
    exact one_ne_zero (neg_eq_zero.mp hmem0)
  -- Step 3: weak Nullstellensatz
  obtain ⟨A, hA⟩ := (theorem_4_72 (C := C) Ps').mp hzer
  -- Step 4: substitution g
  let g : Fin (k + 1) → F := Fin.cons (φ P)⁻¹ (fun i => φ (X i))
  have hg0 : g 0 = (φ P)⁻¹ := Fin.cons_zero _ _
  have hgs : ∀ i : Fin k, g i.succ = φ (X i) := fun i => Fin.cons_succ _ _ i
  -- aeval_g_rename helper
  have aeval_g_rename : ∀ q : R, aeval g (ι q) = φ q := by
    intro q
    rw [hι, aeval_rename]
    have hcomp : g ∘ Fin.succ = fun i => φ (X i) := by
      funext i; simp only [Function.comp_apply]; exact hgs i
    rw [hcomp]
    -- aeval (fun i => φ (X i)) = φ as ring homs
    have : (aeval (fun i => φ (X i)) : R →ₐ[K] F).toRingHom = φ := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
        rw [IsScalarTower.algebraMap_apply K R F a, MvPolynomial.algebraMap_eq]
      · intro i
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    calc aeval (fun i => φ (X i)) q
        = (aeval (fun i => φ (X i)) : R →ₐ[K] F).toRingHom q := rfl
      _ = φ q := by rw [this]
  -- Apply aeval g to hA
  have hAg : ∑ p ∈ Ps', aeval g (A p) * aeval g p = 1 := by
    have := congrArg (aeval g) hA
    rw [map_sum, map_one] at this
    simp only [map_mul] at this
    exact this
  -- The inserted element vanishes under aeval g
  have hins : aeval g (X 0 * ι P - 1) = 0 := by
    rw [map_sub, map_mul, aeval_X, hg0, map_one, aeval_g_rename P]
    rw [inv_mul_cancel₀ hPne, sub_self]
  -- Step 5: split the sum
  have hnotmem : (X 0 * ι P - 1) ∉ Ps.image ι := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨q, _, hq⟩ := hmem
    -- Two evaluations `X 0 ↦ c`, `X_{i+1} ↦ X i` distinguish.
    have eval_rename : ∀ (c : K) (r : R),
        (aeval (Fin.cons (MvPolynomial.C c) (fun i => (X i : R)))) (ι r) = r := by
      intro c r
      rw [hι, aeval_rename]
      have : (Fin.cons (MvPolynomial.C c) (fun i => (X i : R))) ∘ Fin.succ
          = fun i => (X i : R) := by funext i; simp [Fin.cons_succ]
      rw [this]
      exact aeval_X_left_apply r
    -- Apply with c = 0 to the equation `ι q = X 0 * ι P - 1`.
    have h0 := congrArg (aeval (Fin.cons (MvPolynomial.C (0 : K)) (fun i => (X i : R)))) hq
    rw [eval_rename 0 q, map_sub, map_mul, aeval_X, eval_rename 0 P, Fin.cons_zero,
      map_one, map_zero, zero_mul, zero_sub] at h0
    -- Apply with c = 1.
    have h1 := congrArg (aeval (Fin.cons (MvPolynomial.C (1 : K)) (fun i => (X i : R)))) hq
    rw [eval_rename 1 q, map_sub, map_mul, aeval_X, eval_rename 1 P, Fin.cons_zero,
      map_one, one_mul, map_one] at h1
    -- h0 : q = -1, h1 : q = P - 1, hence P = 0.
    apply hP0
    linear_combination h0 - h1
  rw [hPs', Finset.sum_insert hnotmem] at hAg
  rw [hins, mul_zero, zero_add] at hAg
  rw [Finset.sum_image (fun a _ b _ h => rename_injective _ (Fin.succ_injective k) h)] at hAg
  -- Now: ∑ q ∈ Ps, aeval g (A (ι q)) * aeval g (ι q) = 1
  rw [← hι] at hAg
  simp only [aeval_g_rename] at hAg
  -- Step 6/7: clear denominators
  choose Nf Bf hNB using
    (fun q => clear_denom P g hg0 hgs hPne (A (ι q)))
  let N := Ps.sup Nf
  -- Multiply hAg by φ P ^ N
  have key : φ (P ^ N) = φ (∑ q ∈ Ps, (P ^ (N - Nf q) * Bf q) * q) := by
    rw [map_pow]
    have : φ P ^ N = φ P ^ N * 1 := (mul_one _).symm
    rw [this, ← hAg, Finset.mul_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hle : Nf q ≤ N := Finset.le_sup hq
    have step : φ P ^ N * aeval g (A (ι q)) = φ (P ^ (N - Nf q) * Bf q) := by
      rw [map_mul, map_pow, ← hNB q, ← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [map_mul, ← mul_assoc, step]
  have hReq : P ^ N = ∑ q ∈ Ps, (P ^ (N - Nf q) * Bf q) * q := hφinj key
  refine ⟨N, ?_⟩
  rw [mem_idealOfPolys_iff]
  exact ⟨fun q => P ^ (N - Nf q) * Bf q, hReq.symm⟩

end Azurite.BPR.Chapter4
