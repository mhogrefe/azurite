import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-! # The even root function is semialgebraic on `[0, ∞)`

(Not in BPR.) For `k` even (hence `k ≥ 2`), a negative element of a real closed field has no
`k`-th root, but every `x ≥ 0` has a unique nonnegative `k`-th root (`y ↦ y^k` is strictly
monotone on `[0, ∞)`, and surjective onto `[0, ∞)` by the intermediate value property). The
`k`-th root `x ↦ x^{1/k}` is thus a function `[0, ∞) → R` whose graph
`{(x, y) | 0 ≤ y ∧ y^k = x}` is semialgebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Every `x ≥ 0` in a real closed field has a nonnegative `k`-th root (`k ≠ 0`): `Y^k - x`
is `≤ 0` at `0` and `> 0` at `M = x + 1`, so the intermediate value property gives a root
in `[0, M]`. -/
theorem exists_nonneg_pow {k : ℕ} (hk0 : k ≠ 0) (x : R) (hx : 0 ≤ x) :
    ∃ y : R, 0 ≤ y ∧ y ^ k = x := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · exact ⟨0, le_refl 0, by rw [zero_pow hk0]; exact hx0⟩
  · set M : R := x + 1 with hM
    have hM1 : (1 : R) ≤ M := by rw [hM]; linarith
    have hMk : M ≤ M ^ k := le_self_pow₀ hM1 hk0
    set P : Polynomial R := Polynomial.X ^ k - Polynomial.C x with hP
    have hPeval : ∀ t : R, Polynomial.eval t P = t ^ k - x := by intro t; rw [hP]; simp
    have hP0 : Polynomial.eval 0 P < 0 := by rw [hPeval, zero_pow hk0]; linarith
    have hPM : 0 < Polynomial.eval M P := by rw [hPeval]; linarith
    obtain ⟨y, hy0, _, hy⟩ :=
      hasIVP_of_isRealClosed P 0 M (by linarith) (mul_neg_of_neg_of_pos hP0 hPM)
    rw [hPeval] at hy
    exact ⟨y, le_of_lt hy0, sub_eq_zero.mp hy⟩

/-- A total choice of nonnegative `k`-th root: the genuine one for `x ≥ 0`, junk otherwise. -/
theorem exists_root_total {k : ℕ} (hk0 : k ≠ 0) (x : R) :
    ∃ y : R, 0 ≤ x → (0 ≤ y ∧ y ^ k = x) := by
  by_cases hx : 0 ≤ x
  · obtain ⟨y, hy⟩ := exists_nonneg_pow hk0 x hx; exact ⟨y, fun _ => hy⟩
  · exact ⟨0, fun h => absurd h hx⟩

/-- The nonnegative `k`-th root function `[0, ∞) → R` (`k ≠ 0`), valued in `Fin 1 → R`. -/
noncomputable def evenRoot {k : ℕ} (hk0 : k ≠ 0) : (Fin 1 → R) → (Fin 1 → R) :=
  fun x _ => (exists_root_total hk0 (x 0)).choose

/-- **The even-root function `x ↦ x^{1/k}` on `[0, ∞)` is semialgebraic.** Its graph is
`{(x, y) | 0 ≤ y ∧ y^k = x}`. -/
theorem evenRoot_isSemialgebraicFunction {k : ℕ} (_heven : Even k) (hk : 2 ≤ k) :
    IsSemialgebraicFunction {x : Fin 1 → R | 0 ≤ x 0} (evenRoot (R := R) (by omega : k ≠ 0)) := by
  have hk0 : k ≠ 0 := by omega
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph {x : Fin 1 → R | 0 ≤ x 0} (evenRoot hk0)
      = {z : Fin 2 → R | (0 : R) ≤ z 1 ∧ z 1 ^ k = z 0} := by
    ext z
    rw [mem_funGraph]
    constructor
    · rintro ⟨ha, hb⟩
      have ha0 : (0 : R) ≤ z 0 := by
        have h : (0 : R) ≤ (z ∘ Fin.castAdd 1) 0 := ha
        rwa [Function.comp_apply, hcidx] at h
      have hspec := (exists_root_total hk0 ((z ∘ Fin.castAdd 1) 0)).choose_spec
        (by rw [Function.comp_apply, hcidx]; exact ha0)
      have hb0 : z 1 = (exists_root_total hk0 ((z ∘ Fin.castAdd 1) 0)).choose := by
        have h := congrFun hb 0
        rwa [Function.comp_apply, hnidx] at h
      rw [Function.comp_apply, hcidx] at hspec
      rw [Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · rw [hb0]; exact hspec.1
      · rw [hb0]; exact hspec.2
    · rintro ⟨hz1, hz1k⟩
      have hz0 : (0 : R) ≤ z 0 := by rw [← hz1k]; exact pow_nonneg hz1 k
      have hspec := (exists_root_total hk0 ((z ∘ Fin.castAdd 1) 0)).choose_spec
        (by rw [Function.comp_apply, hcidx]; exact hz0)
      rw [Function.comp_apply, hcidx] at hspec
      refine ⟨by show (0 : R) ≤ (z ∘ Fin.castAdd 1) 0; rwa [Function.comp_apply, hcidx], ?_⟩
      funext i; rw [Subsingleton.elim i 0]
      show (z ∘ Fin.natAdd 1) 0 = (exists_root_total hk0 ((z ∘ Fin.castAdd 1) 0)).choose
      rw [Function.comp_apply, hnidx]
      exact (pow_left_inj₀ hz1 hspec.1 hk0).mp (by rw [hz1k, hspec.2])
  have hsemialg : IsSemialgebraicSet {z : Fin 2 → R | (0 : R) ≤ z 1 ∧ z 1 ^ k = z 0} := by
    have heq : {z : Fin 2 → R | (0 : R) ≤ z 1 ∧ z 1 ^ k = z 0}
        = {z | MvPolynomial.eval z (X 1) ≥ 0} ∩ {z | MvPolynomial.eval z (X 1 ^ k - X 0) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, MvPolynomial.eval_X, map_sub,
        MvPolynomial.eval_pow, sub_eq_zero, ge_iff_le]
    rw [heq]
    exact (IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.eqZero _)
  show IsSemialgebraicSet (funGraph {x : Fin 1 → R | 0 ≤ x 0} (evenRoot hk0))
  rw [hgraph]; exact hsemialg

end Azurite.BPR
