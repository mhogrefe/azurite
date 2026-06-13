import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicSets
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR §3.1 — Euclidean norm, balls and spheres over a real closed field

Let `R` be a real closed field. Since `R` is an ordered field, the topology on `R^k` is defined via
open balls just as on `ℝ^k`. We define the euclidean norm, open and closed balls, and spheres, and
record that the balls and spheres are semialgebraic sets.

For `x = (x₁, …, x_k) ∈ R^k` and `r ∈ R` we set
* `‖x‖ = √(x₁² + ⋯ + x_k²)` — the euclidean norm (`euclideanNorm`),
* `B_k(x,r) = {y | ‖y − x‖² < r²}` — open ball (`openBall`),
* `B̄_k(x,r) = {y | ‖y − x‖² ≤ r²}` — closed ball (`closedBall`),
* `S^{k−1}(x,r) = {y | ‖y − x‖² = r²}` — `(k−1)`-sphere (`sphere`).

The square root needed for the norm exists because in a real closed field every non-negative element
is a square (`IsRealClosed.isSquare_of_nonneg`, an order-free consequence of
`isSquare_or_isSquare_neg`). The unit ball and sphere centred at the origin (`x = 0`, `r = 1`) get the
shorthands `unitOpenBall`, `unitClosedBall`, `unitSphere`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Non-negative square root in a real closed field -/

/-- In a real closed field every non-negative element is a square. (Order-free `IsRealClosed`
gives `IsSquare x ∨ IsSquare (-x)`; combined with `0 ≤ x` the second case forces `x = 0`.) -/
theorem IsRealClosed.isSquare_of_nonneg {a : R} (ha : 0 ≤ a) : IsSquare a := by
  rcases IsRealClosed.isSquare_or_isSquare_neg a with h | h
  · exact h
  · obtain ⟨b, hb⟩ := h
    have hna : 0 ≤ -a := hb ▸ mul_self_nonneg b
    exact (le_antisymm (by linarith) ha) ▸ ⟨0, by ring⟩

/-- The non-negative square root `√a` in a real closed field (junk value `0` for `a < 0`). -/
noncomputable def sqrt (a : R) : R :=
  if h : 0 ≤ a then |(IsRealClosed.isSquare_of_nonneg h).choose| else 0

theorem sqrt_nonneg (a : R) : 0 ≤ sqrt a := by
  rw [sqrt]; split <;> [exact abs_nonneg _; exact le_refl 0]

theorem sq_sqrt {a : R} (ha : 0 ≤ a) : sqrt a ^ 2 = a := by
  rw [sqrt, dif_pos ha, sq_abs, sq]
  exact (IsRealClosed.isSquare_of_nonneg ha).choose_spec.symm

@[simp] theorem sqrt_zero : sqrt (0 : R) = 0 :=
  pow_eq_zero_iff (two_ne_zero) |>.mp (sq_sqrt (le_refl (0 : R)))

/-! ### Euclidean norm -/

/-- The squared euclidean norm `‖x‖² = x₁² + ⋯ + x_k²`. -/
def euclideanNormSq (x : Fin k → R) : R := ∑ i, x i ^ 2

omit [IsRealClosed R] in
theorem euclideanNormSq_nonneg (x : Fin k → R) : 0 ≤ euclideanNormSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- The euclidean norm `‖x‖ = √(x₁² + ⋯ + x_k²)`. -/
noncomputable def euclideanNorm (x : Fin k → R) : R := sqrt (euclideanNormSq x)

theorem euclideanNorm_nonneg (x : Fin k → R) : 0 ≤ euclideanNorm x := sqrt_nonneg _

/-- `‖x‖² = x₁² + ⋯ + x_k²` (the defining property of the norm). -/
theorem euclideanNorm_sq (x : Fin k → R) : euclideanNorm x ^ 2 = euclideanNormSq x :=
  sq_sqrt (euclideanNormSq_nonneg x)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem euclideanNormSq_zero : euclideanNormSq (0 : Fin k → R) = 0 := by
  simp [euclideanNormSq]

@[simp] theorem euclideanNorm_zero : euclideanNorm (0 : Fin k → R) = 0 := by
  rw [euclideanNorm, euclideanNormSq_zero, sqrt_zero]

/-! ### Balls and spheres -/

/-- **Open ball** `B_k(x,r) = {y ∈ R^k | ‖y − x‖² < r²}`. -/
def openBall (x : Fin k → R) (r : R) : Set (Fin k → R) :=
  {y | euclideanNorm (y - x) ^ 2 < r ^ 2}

/-- **Closed ball** `B̄_k(x,r) = {y ∈ R^k | ‖y − x‖² ≤ r²}`. -/
def closedBall (x : Fin k → R) (r : R) : Set (Fin k → R) :=
  {y | euclideanNorm (y - x) ^ 2 ≤ r ^ 2}

/-- **`(k−1)`-sphere** `S^{k−1}(x,r) = {y ∈ R^k | ‖y − x‖² = r²}`. -/
def sphere (x : Fin k → R) (r : R) : Set (Fin k → R) :=
  {y | euclideanNorm (y - x) ^ 2 = r ^ 2}

theorem mem_openBall {x : Fin k → R} {r : R} {y : Fin k → R} :
    y ∈ openBall x r ↔ euclideanNormSq (y - x) < r ^ 2 := by
  rw [openBall, Set.mem_setOf_eq, euclideanNorm_sq]

theorem mem_closedBall {x : Fin k → R} {r : R} {y : Fin k → R} :
    y ∈ closedBall x r ↔ euclideanNormSq (y - x) ≤ r ^ 2 := by
  rw [closedBall, Set.mem_setOf_eq, euclideanNorm_sq]

theorem mem_sphere {x : Fin k → R} {r : R} {y : Fin k → R} :
    y ∈ sphere x r ↔ euclideanNormSq (y - x) = r ^ 2 := by
  rw [sphere, Set.mem_setOf_eq, euclideanNorm_sq]

/-! ### The balls and spheres are semialgebraic -/

/-- Defining polynomial `∑ᵢ (Xᵢ − xᵢ)² − r²`; its value at `y` is `‖y − x‖² − r²`. -/
noncomputable def ballPoly (x : Fin k → R) (r : R) : MvPolynomial (Fin k) R :=
  (∑ i, (X i - C (x i)) ^ 2) - C (r ^ 2)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem eval_ballPoly (x : Fin k → R) (r : R) (y : Fin k → R) :
    eval y (ballPoly x r) = euclideanNormSq (y - x) - r ^ 2 := by
  simp only [ballPoly, euclideanNormSq, map_sub, map_sum, map_pow, eval_X, eval_C, Pi.sub_apply]

/-- **The open ball is semialgebraic.** -/
theorem isSemialgebraicSet_openBall (x : Fin k → R) (r : R) :
    IsSemialgebraicSet (openBall x r) := by
  have h : openBall x r = {y | eval y (ballPoly x r) < 0} := by
    ext y; simp only [Set.mem_setOf_eq, mem_openBall, eval_ballPoly, sub_lt_zero]
  rw [h]; exact IsSemialgebraicSet.ltZero _

/-- **The closed ball is semialgebraic.** -/
theorem isSemialgebraicSet_closedBall (x : Fin k → R) (r : R) :
    IsSemialgebraicSet (closedBall x r) := by
  have h : closedBall x r = {y | eval y (ballPoly x r) ≤ 0} := by
    ext y; simp only [Set.mem_setOf_eq, mem_closedBall, eval_ballPoly, sub_nonpos]
  rw [h]; exact IsSemialgebraicSet.leZero _

/-- **The sphere is semialgebraic.** -/
theorem isSemialgebraicSet_sphere (x : Fin k → R) (r : R) :
    IsSemialgebraicSet (sphere x r) := by
  have h : sphere x r = {y | eval y (ballPoly x r) = 0} := by
    ext y; simp only [Set.mem_setOf_eq, mem_sphere, eval_ballPoly, sub_eq_zero]
  rw [h]; exact IsSemialgebraicSet.eqZero _

/-! ### Unit ball and sphere centred at the origin -/

/-- The **unit open ball** `B = B_k(0,1)`. -/
def unitOpenBall (k : ℕ) (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Set (Fin k → R) := openBall (0 : Fin k → R) 1

/-- The **unit closed ball** `B̄ = B̄_k(0,1)`. -/
def unitClosedBall (k : ℕ) (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Set (Fin k → R) := closedBall (0 : Fin k → R) 1

/-- The **unit sphere** `S = S^{k−1}(0,1)`. -/
def unitSphere (k : ℕ) (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Set (Fin k → R) := sphere (0 : Fin k → R) 1

end Azurite.BPR
