import Azurite.BasuPollackRoy.Chapter2.Section2_1.Archimedean
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_10
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosedField
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Integral

/-!
# BPR Exercise 2.11: The real algebraic numbers are real closed

**Exercise 2.11 (BPR).** Prove that `ℝ_alg` (the real algebraic numbers) is real closed.

**Proof strategy.**
1. Work with `algebraicClosure ℚ ℝ` as an `IntermediateField` (field for free).
2. `IsSemireal`: sums of squares map to sums of squares in ℝ via the embedding;
   use `IsSumSq.nonneg` to rule out `−1`.
3. `isSquare_or_isSquare_neg`: for `x` with `x.val ≥ 0`, `Real.sqrt x.val` is
   algebraic over `ℚ` (witness: `p.comp (X²)` where `p` witnesses `x`). For
   `x.val ≤ 0`, apply the same to `−x`.
4. `exists_isRoot_of_odd_natDegree`: map to `ℝ[X]`, find a root via
   `Irreducible.degree_le_two` (induction on degree), then show the root is
   algebraic over `ℚ` via `Algebra.IsAlgebraic.trans`.
-/

namespace Azurite.BPR.Exercise2_11

open Polynomial

/-- The real algebraic numbers, as an intermediate field. -/
noncomputable abbrev R_alg : IntermediateField ℚ ℝ := algebraicClosure ℚ ℝ

/-! ### Step 1: IsSemireal — sums of squares transfer along the embedding -/

/-- Sums of squares in `R_alg` map to sums of squares in `ℝ`. -/
private lemma isSumSq_coe_of_isSumSq {x : R_alg} (h : IsSumSq x) :
    IsSumSq (x.val : ℝ) := by
  induction h with
  | zero =>
    simp only [ZeroMemClass.coe_zero]
    exact .zero
  | sq_add a _ ih =>
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul]
    exact .sq_add a.val ih

instance : IsSemireal R_alg := IsSemireal.of_not_isSumSq_neg_one (by
    intro h
    have h' := isSumSq_coe_of_isSumSq h
    have : (-1 : R_alg).val = (-1 : ℝ) := by simp
    rw [this] at h'
    exact absurd (IsSumSq.nonneg h') (by norm_num))

/-! ### Step 2: isSquare_or_isSquare_neg — via Real.sqrt and explicit polynomial -/

/-- If `p ≠ 0` is a polynomial over `ℚ`, then `p.comp (X ^ 2) ≠ 0`. -/
private lemma comp_X_sq_ne_zero {p : ℚ[X]} (hp : p ≠ 0) :
    p.comp (X ^ 2 : ℚ[X]) ≠ 0 := by
  have hnd : (X ^ 2 : ℚ[X]).natDegree ≠ 0 := by simp
  have hlc := leadingCoeff_comp hnd (p := p)
  simp at hlc
  exact leadingCoeff_ne_zero.mp (hlc ▸ leadingCoeff_ne_zero.mpr hp)

/-- The square root of a nonneg algebraic real is algebraic:
    if `p(a) = 0` for nonzero `p ∈ ℚ[X]`, then `p(X²)` has `√a` as a root. -/
private lemma isAlgebraic_sqrt {a : ℝ} (ha : 0 ≤ a) (halg : IsAlgebraic ℚ a) :
    IsAlgebraic ℚ (Real.sqrt a) := by
  obtain ⟨p, hp, hpa⟩ := halg
  exact ⟨p.comp (X ^ 2), comp_X_sq_ne_zero hp, by
    rw [aeval_comp, aeval_X_pow, Real.sq_sqrt ha, hpa]⟩

/-- Every element of `R_alg` or its negation is a square. -/
theorem isSquare_or_isSquare_neg_R_alg (x : R_alg) :
    IsSquare x ∨ IsSquare (-x) := by
  rcases le_total 0 x.val with hx | hx
  · -- x.val ≥ 0, so √(x.val) exists and is algebraic
    left
    have halg : IsAlgebraic ℚ x.val := mem_algebraicClosure_iff.mp x.2
    have hsqrt_alg := isAlgebraic_sqrt hx halg
    have hsqrt_mem : Real.sqrt x.val ∈ R_alg :=
      mem_algebraicClosure_iff.mpr hsqrt_alg
    exact ⟨⟨Real.sqrt x.val, hsqrt_mem⟩,
      Subtype.val_injective (by
        show x.val = Real.sqrt x.val * Real.sqrt x.val
        rw [← sq, Real.sq_sqrt hx])⟩
  · -- x.val ≤ 0, apply to -x
    right
    have hx' : 0 ≤ (-x).val := by simp; linarith
    have halg : IsAlgebraic ℚ (-x).val := by
      have := mem_algebraicClosure_iff.mp x.2
      exact (show (-x).val = -(x.val) by simp) ▸ this.neg
    have hsqrt_alg := isAlgebraic_sqrt hx' halg
    have hsqrt_mem : Real.sqrt (-x).val ∈ R_alg :=
      mem_algebraicClosure_iff.mpr hsqrt_alg
    exact ⟨⟨Real.sqrt (-x).val, hsqrt_mem⟩,
      Subtype.val_injective (by
        show (-x).val = Real.sqrt (-x).val * Real.sqrt (-x).val
        rw [← sq, Real.sq_sqrt hx'])⟩

/-! ### Step 3: exists_isRoot_of_odd_natDegree — odd-degree polys have roots -/

/-- Over `ℝ`, every polynomial of odd degree ≥ 1 has a root.
    Uses `Irreducible.degree_le_two` and strong induction. -/
private lemma natDegree_pos_of_not_isUnit {f : ℝ[X]} (hf : f ≠ 0) (hu : ¬IsUnit f) :
    0 < f.natDegree := by
  rcases Nat.eq_zero_or_pos f.natDegree with h | h
  · exfalso; apply hu
    rw [isUnit_iff]
    have hc : f.coeff 0 ≠ 0 := by
      intro hc; exact hf (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero])
    exact ⟨f.coeff 0, Ne.isUnit hc, (eq_C_of_natDegree_eq_zero h).symm⟩
  · exact h

private theorem exists_root_real_of_odd_natDegree (f : ℝ[X]) (hf : f ≠ 0)
    (hodd : Odd f.natDegree) : ∃ r : ℝ, f.IsRoot r := by
  suffices ∀ n, ∀ g : ℝ[X], g ≠ 0 → g.natDegree = n → Odd n → ∃ r, g.IsRoot r from
    this _ f hf rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg0 hgn hodd_n
    have hnu : ¬IsUnit g := by
      intro hu
      have := natDegree_eq_zero_of_isUnit hu
      rw [hgn] at this; exact Nat.not_odd_zero (this ▸ hodd_n)
    rcases irreducible_or_factor hnu with hirr | ⟨a, b, ha, hb, hab⟩
    · -- Irreducible of degree ≤ 2 and odd → degree = 1
      have hle2 := hirr.natDegree_le_two
      obtain ⟨k, hk⟩ := hodd_n
      have h1 : n = 1 := by omega
      exact exists_root_of_degree_eq_one (by
        rw [degree_eq_natDegree hg0, hgn, h1]; norm_cast)
    · -- g = a * b, both non-units
      have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hg0)
      have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hg0)
      have hdeg : n = a.natDegree + b.natDegree := by
        rw [← hgn, hab, natDegree_mul ha0 hb0]
      have ha_pos := natDegree_pos_of_not_isUnit ha0 ha
      have hb_pos := natDegree_pos_of_not_isUnit hb0 hb
      by_cases hoa : Odd a.natDegree
      · have hlt : a.natDegree < n := by omega
        obtain ⟨r, hr⟩ := ih _ hlt a ha0 rfl hoa
        exact ⟨r, hab ▸ root_mul_right_of_isRoot b hr⟩
      · have hob : Odd b.natDegree := by
          rw [hdeg, Nat.odd_add] at hodd_n
          exact Nat.not_even_iff_odd.mp (fun heb => hoa (hodd_n.mpr heb))
        have hlt : b.natDegree < n := by omega
        obtain ⟨r, hr⟩ := ih _ hlt b hb0 rfl hob
        exact ⟨r, hab ▸ root_mul_left_of_isRoot a hr⟩

/-- An element of `ℝ` that is a root of a nonzero polynomial with coefficients
    in `R_alg` is itself in `R_alg`. -/
private theorem mem_R_alg_of_root {f : R_alg[X]} (hf : f ≠ 0) {r : ℝ}
    (hr : (f.map (algebraMap ↥R_alg ℝ)).IsRoot r) : r ∈ R_alg := by
  rw [mem_algebraicClosure_iff]
  haveI : Algebra.IsAlgebraic ℚ ↥R_alg := algebraicClosure.isAlgebraic ℚ ℝ
  have halg_r : IsAlgebraic (↥R_alg) r := ⟨f, hf, by rwa [aeval_def, ← eval_map]⟩
  exact (isAlgebraic_iff_isIntegral.mp halg_r).trans_isAlgebraic ℚ

/-- Every odd-degree polynomial over `R_alg` has a root in `R_alg`. -/
theorem exists_isRoot_of_odd_natDegree_R_alg (f : R_alg[X]) (hf : Odd f.natDegree) :
    ∃ r : R_alg, f.IsRoot r := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hinj : Function.Injective (algebraMap ↥R_alg ℝ) := Subtype.val_injective
  set g := f.map (algebraMap ↥R_alg ℝ) with hg_def
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf0
  have hdeg : g.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  obtain ⟨r, hr⟩ := exists_root_real_of_odd_natDegree g hg0 (hdeg ▸ hf)
  have hmem := mem_R_alg_of_root hf0 hr
  refine ⟨⟨r, hmem⟩, ?_⟩
  rw [IsRoot]
  apply Subtype.val_injective
  simp only [ZeroMemClass.coe_zero]
  change (algebraMap ↥R_alg ℝ) (eval ⟨r, hmem⟩ f) = 0
  rw [show eval ⟨r, hmem⟩ f = eval₂ (RingHom.id _) ⟨r, hmem⟩ f from rfl,
      hom_eval₂ f (RingHom.id _) (algebraMap ↥R_alg ℝ) ⟨r, hmem⟩]
  simp only [RingHom.comp_id]
  rw [← eval_map, ← hg_def]
  exact hr

/-! ### Conclusion -/

instance : IsRealClosed R_alg where
  isSquare_or_isSquare_neg := isSquare_or_isSquare_neg_R_alg
  exists_isRoot_of_odd_natDegree := fun hf => exists_isRoot_of_odd_natDegree_R_alg _ hf

/-- `ℝ_alg` is archimedean (as an intermediate field of `ℝ`). -/
instance : Archimedean R_alg :=
  Archimedean.comap R_alg.subtype.toAddMonoidHom (fun _ _ h => h)

end Azurite.BPR.Exercise2_11
