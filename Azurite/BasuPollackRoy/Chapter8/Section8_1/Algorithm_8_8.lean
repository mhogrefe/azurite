import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeBounds
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvMul
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# BPR §8.1 Algorithm 8.8: Special evaluation of a univariate polynomial

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ ℤ[X]` and `b/c ∈ ℚ` with `b, c ∈ ℤ`,
compute `cᵖ · P(b/c)` without leaving `ℤ`. The algorithm is a variant
of Horner's method (Algorithm 8.7) that keeps track of a running
power `d = cⁱ`:

  - Initialize `HorSpecial₀(P, b) := aₚ`,  `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `HorSpecialᵢ(P, b) := b · HorSpecialᵢ₋₁(P, b) + d · aₚ₋ᵢ`
  - Output `HorSpecialₚ(P, b) = cᵖ · P(b/c)`.

We define `Polynomial.horSpecial` (outside `Azurite.BPR`, extending
Mathlib's `Polynomial` namespace), prove the recurrence, closed form,
and the main evaluation identity over a field. The bitsize bound on
`horSpecial` over `ℤ` is recorded as `Polynomial.bitsize_horSpecial_le`.
-/

section HorSpecial

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.8 (Special Horner evaluation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, computes
    `cᵖ · P(b/c)` without division:
    - `horSpecial P b c 0 = aₚ`
    - `horSpecial P b c (i+1) = b · horSpecial P b c i + c^{i+1} · aₚ₋ᵢ₋₁` -/
noncomputable def Polynomial.horSpecial (P : R[X]) (b c : R) : ℕ → R
  | 0 => P.coeff P.natDegree
  | i + 1 => b * P.horSpecial b c i + c ^ (i + 1) * P.coeff (P.natDegree - (i + 1))

/-- The base case: `horSpecial P b c 0 = leadingCoeff P`. -/
theorem Polynomial.horSpecial_zero (P : R[X]) (b c : R) :
    P.horSpecial b c 0 = P.leadingCoeff := by
  unfold Polynomial.horSpecial; rw [leadingCoeff]

/-- The recurrence for `horSpecial`. -/
theorem Polynomial.horSpecial_succ (P : R[X]) (b c : R) (i : ℕ) :
    P.horSpecial b c (i + 1) =
      b * P.horSpecial b c i + c ^ (i + 1) * P.coeff (P.natDegree - (i + 1)) :=
  rfl

/-- **Closed-form characterization.**
    `horSpecial P b c i = ∑ j ∈ range (i+1), aₚ₋ⱼ · b^{i−j} · c^j`. -/
theorem Polynomial.horSpecial_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.horSpecial b c i = ∑ j ∈ range (i + 1),
      P.coeff (P.natDegree - j) * b ^ (i - j) * c ^ j := by
  induction i with
  | zero => simp [Polynomial.horSpecial]
  | succ n ih =>
    rw [Polynomial.horSpecial, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro j hj; rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 from by omega, pow_succ]; ring
    · ring

/-- **Reindexed closed form at `i = natDegree P`.**
    `horSpecial P b c p = ∑ k ∈ range (p+1), aₖ · bᵏ · c^{p−k}`. -/
theorem Polynomial.horSpecial_natDegree_eq_sum (P : R[X]) (b c : R) :
    P.horSpecial b c P.natDegree = ∑ k ∈ range (P.natDegree + 1),
      P.coeff k * b ^ k * c ^ (P.natDegree - k) := by
  rw [horSpecial_eq_sum, ← Finset.sum_flip]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega]

/-- **BPR Algorithm 8.8 (main result, over a field).**
    `horSpecial P b c p = cᵖ · P.eval(b · c⁻¹)` when `c ≠ 0`. -/
theorem Polynomial.horSpecial_natDegree_eq_eval {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) :
    P.horSpecial b c P.natDegree = c ^ P.natDegree * P.eval (b * c⁻¹) := by
  rw [horSpecial_natDegree_eq_sum, eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  rw [mul_pow, inv_pow]
  calc P.coeff k * b ^ k * c ^ (P.natDegree - k)
      = P.coeff k * (b ^ k * c ^ (P.natDegree - k)) := by ring
    _ = P.coeff k * (c ^ P.natDegree * (b ^ k * (c ^ k)⁻¹)) := by
        congr 1; rw [pow_sub₀ c hc (by omega : k ≤ P.natDegree)]; ring
    _ = c ^ P.natDegree * (P.coeff k * (b ^ k * (c ^ k)⁻¹)) := by ring

end HorSpecial

/-! ### Bitsize bound on HorSpecial -/

section HorSpecialBitsize

open Polynomial Finset

-- Each summand `a_{p-j} · b^{i-j} · c^j` has bitsize ≤ τ + i · τ'.
-- This is the product of one coefficient (bitsize ≤ τ) with i factors
-- (b or c, each of bitsize ≤ τ').
private theorem bitsize_coeff_mul_pow_le (a b c : ℤ) (i j τ τ' : ℕ)
    (hj : j ≤ i) (ha : a.natAbs.size ≤ τ)
    (hb : b.natAbs.size ≤ τ') (hc : c.natAbs.size ≤ τ') :
    (a * b ^ (i - j) * c ^ j).natAbs.size ≤ τ + i * τ' := by
  by_cases hi : i = 0
  · simp [show j = 0 from by omega, hi, ha]
  · -- The product b^{i-j} * c^j is a product of i integers each of bitsize ≤ τ'
    set L := List.replicate (i - j) b ++ List.replicate j c with hL_def
    have hne : L ≠ [] := by simp [hL_def]; omega
    have hlen : L.length = i := by simp [hL_def]; omega
    have heq : L.prod = b ^ (i - j) * c ^ j := by simp [hL_def, List.prod_replicate]
    have hprod : L.prod.natAbs.size ≤ i * τ' := by
      have := Azurite.BPR.Int.size_list_prod_le L τ' hne
        (by intro x hx; simp [hL_def, List.mem_append, List.mem_replicate] at hx
            rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
      simp [hlen, Azurite.BPR.Int.size] at this; exact this
    rw [mul_assoc, ← heq]
    exact Azurite.BPR.Int.size_mul_le a _ τ (i * τ') ha hprod

/-- **BPR §8.1 (bitsize of HorSpecial).**
    Let `P ∈ ℤ[X]` with `p = natDegree P` and coefficient bitsizes bounded by `τ`.
    Let `b, c ∈ ℤ` with `bitsize(b), bitsize(c) ≤ τ'`. Then for `i ≤ p`:

      `bitsize(horSpecial P b c i) ≤ τ + i · τ' + bitsize(p + 1)`.

    The bound comes from the closed-form sum
    `horSpecial P b c i = ∑_{j=0}^{i} a_{p-j} · b^{i-j} · c^j`:
    each summand has bitsize `≤ τ + i · τ'` (product of one coefficient of
    bitsize `τ` and `i` factors of bitsize `τ'`), and the sum of `i + 1 ≤ p + 1`
    terms adds `bitsize(p + 1)`. -/
theorem Polynomial.bitsize_horSpecial_le (P : ℤ[X]) (b c : ℤ) (i τ τ' : ℕ)
    (hi : i ≤ P.natDegree)
    (hτ : ∀ k, (P.coeff k).natAbs.size ≤ τ)
    (hb : b.natAbs.size ≤ τ') (hc : c.natAbs.size ≤ τ') :
    (P.horSpecial b c i).natAbs.size ≤ τ + i * τ' + Nat.size (P.natDegree + 1) := by
  -- Unfold horSpecial to the closed-form sum
  rw [Polynomial.horSpecial_eq_sum]
  -- Each summand has bitsize ≤ τ + i*τ'
  have hB : ∀ j ∈ range (i + 1),
      (P.coeff (P.natDegree - j) * b ^ (i - j) * c ^ j).natAbs.size ≤ τ + i * τ' := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact bitsize_coeff_mul_pow_le _ b c i j τ τ' (by omega) (hτ _) hb hc
  -- Sum of i+1 terms each of bitsize ≤ B adds Nat.size(i+1)
  have h1 := Azurite.BPR.Int.size_finset_sum_le hB
  rw [Finset.card_range] at h1
  -- Since i ≤ p, Nat.size(i+1) ≤ Nat.size(p+1)
  exact le_trans h1 (Nat.add_le_add_left (Nat.size_le_size (by omega)) _)

end HorSpecialBitsize
