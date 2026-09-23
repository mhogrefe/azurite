import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_11
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-! # BPR §3.2 — connected ≠ semialgebraically connected (the `ℝ_alg` example)

The field `ℝ_alg` of real algebraic numbers is real closed but **not connected**: for a real number
`t ∉ ℝ_alg`, the set `(−∞, t) ∩ ℝ_alg` is open and closed in `ℝ_alg`. BPR takes `t = π`. The point
of the example is that this clopen set is **not semialgebraic** over `ℝ_alg`, because `t` is not a
root of any polynomial over `ℝ_alg`; so it does not witness a *semialgebraic* disconnection, and
`ℝ_alg` will turn out to be semialgebraically connected.

We formalize the non-semialgebraicity (the substantive claim). Since the transcendence of `π` is not
yet in Mathlib, we use a **Liouville number** as the explicit transcendental threshold
(`transcendental_liouvilleNumber`); the general lemma works for any `t ∉ ℝ_alg`.

A semialgebraic subset of the line over a real closed field is *constant on the gaps* between
finitely many algebraic breakpoints (`isSemialgebraicSet_sect_constOnGaps`, from Proposition 3.4).
But membership in `(−∞, t)` flips exactly at `t`, which lies strictly inside one of those gaps
(`ℝ_alg` is dense in `ℝ`) — a contradiction. -/

namespace Azurite.BPR

open Azurite.BPR.Exercise2_11

/-- **The lower threshold by a non-algebraic real is not semialgebraic.** For every real `t ∉ ℝ_alg`,
the set `{x ∈ ℝ_alg : x < t}` (as a subset of `ℝ_alg^1`) is not a semialgebraic set over `ℝ_alg`. -/
theorem lt_threshold_not_isSemialgebraicSet {t : ℝ} (ht : t ∉ R_alg) :
    ¬ IsSemialgebraicSet {v : Fin 1 → R_alg | (↑(v 0) : ℝ) < t} := by
  intro hS
  obtain ⟨F, hF⟩ := isSemialgebraicSet_sect_constOnGaps hS
  have hcoe_ne : ∀ z : R_alg, (↑z : ℝ) ≠ t := fun z hz => ht (hz ▸ z.2)
  have hsect : ∀ x : R_alg,
      x ∈ constPt ⁻¹' {v : Fin 1 → R_alg | (↑(v 0) : ℝ) < t} ↔ (↑x : ℝ) < t := by
    intro x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, constPt]
  -- Pick `ε > 0` so that `(t − ε, t + ε)` avoids every coordinate of `F` (none equals `t`).
  obtain ⟨ε, hε, hεF⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ F, ε ≤ |(↑z : ℝ) - t| := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, fun z hz => absurd hz (by simp [hFe])⟩
    · refine ⟨F.inf' hFne (fun z => |(↑z : ℝ) - t|), ?_, fun z hz => Finset.inf'_le _ hz⟩
      rw [Finset.lt_inf'_iff]
      exact fun z _ => abs_pos.mpr (sub_ne_zero.mpr (hcoe_ne z))
  -- Rational breakpoints `a < t < b` inside that gap.
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show t - ε < t by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show t < t + ε by linarith)
  have hca : (↑((a : ℚ) : R_alg) : ℝ) = (a : ℝ) := by push_cast; ring
  have hcb : (↑((b : ℚ) : R_alg) : ℝ) = (b : ℝ) := by push_cast; ring
  have hxy : ((a : ℚ) : R_alg) < ((b : ℚ) : R_alg) := by
    rw [← Subtype.coe_lt_coe, hca, hcb]; exact_mod_cast (by linarith : (a : ℝ) < (b : ℝ))
  have hgap : ∀ z ∈ F, z < ((a : ℚ) : R_alg) ∨ ((b : ℚ) : R_alg) < z := by
    intro z hz
    have hzε := hεF z hz
    rcases abs_cases ((↑z : ℝ) - t) with ⟨heq, _⟩ | ⟨heq, _⟩
    · right
      rw [heq] at hzε
      rw [← Subtype.coe_lt_coe, hcb]
      linarith
    · left
      rw [heq] at hzε
      rw [← Subtype.coe_lt_coe, hca]
      linarith
  have hiff := hF _ _ hxy hgap
  rw [hsect, hsect, hca, hcb] at hiff
  exact absurd (hiff.mp ha2) (not_lt.mpr hb1.le)

/-- **`ℝ_alg` has a clopen, non-semialgebraic lower set.** With a Liouville number as an explicit
transcendental real `∉ ℝ_alg`, the set `(−∞, t) ∩ ℝ_alg` is not semialgebraic. This is BPR's `ℝ_alg`
example (BPR uses `π`; we substitute a Liouville number since `π`'s transcendence is not in
Mathlib). -/
theorem exists_lt_threshold_not_isSemialgebraicSet :
    ∃ t : ℝ, t ∉ R_alg ∧ ¬ IsSemialgebraicSet {v : Fin 1 → R_alg | (↑(v 0) : ℝ) < t} := by
  have ht : liouvilleNumber ((2 : ℕ) : ℝ) ∉ R_alg := by
    rw [mem_R_alg_iff_isAlgebraic_int]
    exact transcendental_liouvilleNumber (by norm_num)
  exact ⟨_, ht, lt_threshold_not_isSemialgebraicSet ht⟩

end Azurite.BPR
