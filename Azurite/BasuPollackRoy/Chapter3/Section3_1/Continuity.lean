import Azurite.BasuPollackRoy.Chapter3.Section3_1.ClosureInterior
import Mathlib.Topology.ContinuousOn

/-! # BPR §3.1 — continuity; polynomial maps are continuous

A function `f : R^k → R^ℓ` is **continuous** if the inverse image of every open set is open — Mathlib's
`Continuous` for the euclidean topology (`continuous_iff_isOpen_preimage`). We record the ε–δ form
(`continuous_iff_ball`), prove the standard building blocks (constants, coordinate projections, sums,
products of real-valued maps are continuous; composition is Mathlib's `Continuous.comp`), and
conclude that **polynomial maps `R^k → R^ℓ` are continuous** (`continuous_polynomialMap`), exactly as
BPR sketches. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Continuity = inverse image of open is open; ε–δ form -/

/-- **BPR's definition.** A map is continuous iff the inverse image of every open set is open.
(Mathlib's `Continuous`, for the euclidean topology.) -/
theorem continuous_iff_isOpen_preimage {f : (Fin k → R) → (Fin ℓ → R)} :
    Continuous f ↔ ∀ V, IsOpen V → IsOpen (f ⁻¹' V) := continuous_def

theorem mem_nhds_iff_openBall {x : Fin k → R} {s : Set (Fin k → R)} :
    s ∈ nhds x ↔ ∃ r, 0 < r ∧ openBall x r ⊆ s := by
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, hts, htopen, hxt⟩
    obtain ⟨c, r, hr, hxc, hsub⟩ := (isOpen_iff.mp htopen) x hxt
    rw [mem_openBall_iff_norm hr] at hxc
    exact ⟨r - euclideanNorm (x - c), by linarith,
      (openBall_subset_openBall hr (by linarith) (by linarith)).trans (hsub.trans hts)⟩
  · rintro ⟨r, hr, hsub⟩
    exact ⟨openBall x r, hsub, isOpen_openBall x hr, mem_openBall_self x hr⟩

theorem nhds_hasBasis_openBall (x : Fin k → R) :
    (nhds x).HasBasis (fun r => 0 < r) (openBall x) :=
  ⟨fun _ => mem_nhds_iff_openBall⟩

/-- **ε–δ characterization of continuity** of a map `R^k → R^ℓ`. -/
theorem continuous_iff_ball {f : (Fin k → R) → (Fin ℓ → R)} :
    Continuous f ↔ ∀ x ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ y, euclideanNorm (y - x) < δ → euclideanNorm (f y - f x) < ε := by
  rw [continuous_iff_continuousAt]
  refine forall_congr' (fun x => ?_)
  rw [ContinuousAt, (nhds_hasBasis_openBall x).tendsto_iff (nhds_hasBasis_openBall (f x))]
  refine forall_congr' (fun ε => forall_congr' (fun _ => ?_))
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy => ?_⟩
    exact (mem_openBall_iff_norm (by assumption)).mp (h y ((mem_openBall_iff_norm hδ).mpr hy))
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy => ?_⟩
    exact (mem_openBall_iff_norm (by assumption)).mpr (h y ((mem_openBall_iff_norm hδ).mp hy))

/-- **ε–δ characterization of continuity on a set `S`** (BPR's "continuous at every point of `S`"):
a map `f : S → T` is continuous (`ContinuousOn f S`, the subspace topology) iff for every `x ∈ S`
and `r > 0` there is `δ > 0` with `‖f(y) − f(x)‖ < r` for all `y ∈ S` with `‖y − x‖ < δ`. -/
theorem continuousOn_iff_ball {f : (Fin k → R) → (Fin ℓ → R)} {S : Set (Fin k → R)} :
    ContinuousOn f S ↔ ∀ x ∈ S, ∀ r, 0 < r → ∃ δ, 0 < δ ∧
      ∀ y ∈ S, euclideanNorm (y - x) < δ → euclideanNorm (f y - f x) < r := by
  refine forall₂_congr (fun x _ => ?_)
  have hb : (nhdsWithin x S).HasBasis (fun δ => 0 < δ) (fun δ => openBall x δ ∩ S) :=
    (nhds_hasBasis_openBall x).inf_principal S
  rw [ContinuousWithinAt, hb.tendsto_iff (nhds_hasBasis_openBall (f x))]
  refine forall_congr' (fun r => forall_congr' (fun _ => ?_))
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hyS hy => ?_⟩
    exact (mem_openBall_iff_norm (by assumption)).mp
      (h y ⟨(mem_openBall_iff_norm hδ).mpr hy, hyS⟩)
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy => ?_⟩
    exact (mem_openBall_iff_norm (by assumption)).mpr
      (h y hy.2 ((mem_openBall_iff_norm hδ).mp hy.1))

/-! ### Real-valued continuity and its closure properties -/

/-- A single coordinate is bounded by the norm: `|aᵢ| ≤ ‖a‖`. -/
theorem abs_coord_le_norm (a : Fin k → R) (i : Fin k) : |a i| ≤ euclideanNorm a := by
  refine le_of_sq_le_sq ?_ (euclideanNorm_nonneg a)
  rw [sq_abs, euclideanNorm_sq, euclideanNormSq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)

/-- A real-valued function `R^k → R` is **continuous** (ε–δ form). -/
def ContinuousR (g : (Fin k → R) → R) : Prop :=
  ∀ x ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ y, euclideanNorm (y - x) < δ → |g y - g x| < ε

theorem continuousR_const (c : R) : ContinuousR (fun _ : Fin k → R => c) :=
  fun _ ε hε => ⟨1, one_pos, fun _ _ => by rw [sub_self, abs_zero]; exact hε⟩

theorem continuousR_coord (i : Fin k) : ContinuousR (fun y : Fin k → R => y i) := by
  intro x ε hε
  refine ⟨ε, hε, fun y hy => ?_⟩
  calc |y i - x i| = |(y - x) i| := by rw [Pi.sub_apply]
    _ ≤ euclideanNorm (y - x) := abs_coord_le_norm _ i
    _ < ε := hy

theorem ContinuousR.add {g h : (Fin k → R) → R} (hg : ContinuousR g) (hh : ContinuousR h) :
    ContinuousR (fun y => g y + h y) := by
  intro x ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hg x (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, h2⟩ := hh x (ε / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy => ?_⟩
  have b1 := h1 y (lt_of_lt_of_le hy (min_le_left _ _))
  have b2 := h2 y (lt_of_lt_of_le hy (min_le_right _ _))
  calc |(g y + h y) - (g x + h x)| = |(g y - g x) + (h y - h x)| := by ring_nf
    _ ≤ |g y - g x| + |h y - h x| := abs_add_le _ _
    _ < ε := by linarith

theorem ContinuousR.mul {g h : (Fin k → R) → R} (hg : ContinuousR g) (hh : ContinuousR h) :
    ContinuousR (fun y => g y * h y) := by
  intro x ε hε
  obtain ⟨δ0, hδ0, hg0⟩ := hg x 1 one_pos
  obtain ⟨δ1, hδ1, hg1⟩ := hg x (ε / (2 * (|h x| + 1))) (by positivity)
  obtain ⟨δ2, hδ2, hh2⟩ := hh x (ε / (2 * (|g x| + 1))) (by positivity)
  refine ⟨min δ0 (min δ1 δ2), lt_min hδ0 (lt_min hδ1 hδ2), fun y hy => ?_⟩
  have hy0 : euclideanNorm (y - x) < δ0 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : euclideanNorm (y - x) < δ1 :=
    lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hy2 : euclideanNorm (y - x) < δ2 :=
    lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_right _ _))
  have b0 : |g y - g x| < 1 := hg0 y hy0
  have b1 : |h y - h x| < ε / (2 * (|g x| + 1)) := hh2 y hy2
  have b2 : |g y - g x| < ε / (2 * (|h x| + 1)) := hg1 y hy1
  have hgx1 : (0 : R) < |g x| + 1 := by positivity
  have hhx1 : (0 : R) < |h x| + 1 := by positivity
  have hgy : |g y| < |g x| + 1 := by
    calc |g y| = |g x + (g y - g x)| := by ring_nf
      _ ≤ |g x| + |g y - g x| := abs_add_le _ _
      _ < |g x| + 1 := by linarith
  have key : |g y * h y - g x * h x| ≤ |g y| * |h y - h x| + |g y - g x| * |h x| := by
    calc |g y * h y - g x * h x| = |g y * (h y - h x) + (g y - g x) * h x| := by ring_nf
      _ ≤ |g y * (h y - h x)| + |(g y - g x) * h x| := abs_add_le _ _
      _ = |g y| * |h y - h x| + |g y - g x| * |h x| := by rw [abs_mul, abs_mul]
  have e1 : (|g x| + 1) * (ε / (2 * (|g x| + 1))) = ε / 2 := by field_simp
  have e2 : (ε / (2 * (|h x| + 1))) * (|h x| + 1) = ε / 2 := by field_simp
  have t1 : |g y| * |h y - h x| < ε / 2 := by
    rw [← e1]; exact mul_lt_mul' hgy.le b1 (abs_nonneg _) hgx1
  have t2 : |g y - g x| * |h x| < ε / 2 := by
    calc |g y - g x| * |h x| ≤ |g y - g x| * (|h x| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < (ε / (2 * (|h x| + 1))) * (|h x| + 1) := mul_lt_mul_of_pos_right b2 hhx1
      _ = ε / 2 := e2
  linarith [key, t1, t2]

/-- Polynomial evaluation `y ↦ P(y)` is continuous. -/
theorem continuousR_eval (P : MvPolynomial (Fin k) R) : ContinuousR (fun y => eval y P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : (fun y : Fin k → R => eval y (C a)) = fun _ => a := by funext y; rw [eval_C]
    rw [h]; exact continuousR_const a
  | add p q hp hq =>
    have h : (fun y : Fin k → R => eval y (p + q)) = fun y => eval y p + eval y q := by
      funext y; rw [eval_add]
    rw [h]; exact hp.add hq
  | mul_X p i hp =>
    have h : (fun y : Fin k → R => eval y (p * X i)) = fun y => eval y p * y i := by
      funext y; rw [eval_mul, eval_X]
    rw [h]; exact hp.mul (continuousR_coord i)

/-! ### Component criterion and polynomial maps -/

/-- A map `R^k → R^ℓ` is continuous iff each of its `ℓ` real-valued components is. -/
theorem continuous_iff_components {f : (Fin k → R) → (Fin ℓ → R)} :
    Continuous f ↔ ∀ j, ContinuousR (fun x => f x j) := by
  rw [continuous_iff_ball]
  constructor
  · intro hf j x ε hε
    obtain ⟨δ, hδ, h⟩ := hf x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    calc |f y j - f x j| = |(f y - f x) j| := by rw [Pi.sub_apply]
      _ ≤ euclideanNorm (f y - f x) := abs_coord_le_norm _ j
      _ < ε := h y hy
  · intro hf x ε hε
    set t := ε / ((ℓ : R) + 1) with ht_def
    have ht : 0 < t := by positivity
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · subst hℓ
      refine ⟨1, one_pos, fun y _ => ?_⟩
      have h0 : euclideanNormSq (f y - f x) = 0 := by simp [euclideanNormSq]
      have : euclideanNorm (f y - f x) = 0 := by
        have := euclideanNorm_sq (f y - f x); rw [h0] at this; nlinarith [euclideanNorm_nonneg (f y - f x)]
      rw [this]; exact hε
    · have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
      choose δ hδ0 hδ using fun j => hf j x t ht
      refine ⟨Finset.univ.inf' Finset.univ_nonempty δ,
        (Finset.lt_inf'_iff _).2 (fun j _ => hδ0 j), fun y hy => ?_⟩
      have hcomp : ∀ j, |f y j - f x j| < t := fun j =>
        hδ j y (lt_of_lt_of_le hy (Finset.inf'_le _ (Finset.mem_univ j)))
      have hsq : euclideanNormSq (f y - f x) < ε ^ 2 := by
        rw [euclideanNormSq]
        calc ∑ j, (f y - f x) j ^ 2 = ∑ j, |f y j - f x j| ^ 2 := by
              refine Finset.sum_congr rfl (fun j _ => ?_); rw [Pi.sub_apply, sq_abs]
          _ ≤ ∑ _j : Fin ℓ, t ^ 2 :=
              Finset.sum_le_sum (fun j _ => by nlinarith [hcomp j, abs_nonneg (f y j - f x j)])
          _ = (ℓ : R) * t ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ < ε ^ 2 := by
              rw [ht_def, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
              nlinarith [show (0:R) ≤ (ℓ : R) by positivity, mul_pos hε hε, sq_nonneg ((ℓ : R))]
      refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
      rw [euclideanNorm_sq]; exact hsq

/-- A **polynomial map** `R^k → R^ℓ`, `x ↦ (P₁(x), …, P_ℓ(x))`. -/
noncomputable def polynomialMap (P : Fin ℓ → MvPolynomial (Fin k) R) :
    (Fin k → R) → (Fin ℓ → R) := fun x j => eval x (P j)

/-- **Polynomial maps `R^k → R^ℓ` are continuous.** -/
theorem continuous_polynomialMap (P : Fin ℓ → MvPolynomial (Fin k) R) :
    Continuous (polynomialMap P) :=
  continuous_iff_components.mpr (fun j => continuousR_eval (P j))

end Azurite.BPR
