import Azurite.BasuPollackRoy.Chapter2.Section2_6.Proposition_2_99

/-! # BPR §2.6 Notation 2.100 — the limit `lim_ε`

The ring homomorphism `lim_ε : K⟨ε⟩_b → K` sends a bounded Puiseux series `∑_{i} aᵢ ε^{i/q}` (an
element of non-negative order) to its constant coefficient `a₀` — it "replaces `ε` by `0`".

Additivity is automatic (the coefficient at `0` is additive), but multiplicativity needs the
non-negative order: in `(x·y).coeff 0 = ∑_{a+b=0} x.coeff a · y.coeff b`, the supports lie in
`[0, ∞)`, so the only contributing pair is `(0, 0)`. -/

namespace Azurite.BPR

open HahnSeries

variable {K : Type*} [Field K]

/-- **The constant coefficient is multiplicative on non-negative-order series.** When both factors
have support in `[0, ∞)`, the only antidiagonal pair summing to `0` is `(0, 0)`. -/
theorem coeff_mul_zero_of_nonneg {x y : HahnSeries ℚ K}
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  rw [HahnSeries.coeff_mul, Finset.sum_subset (s₂ := {((0 : ℚ), (0 : ℚ))}) ?_ ?_]
  · simp
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨hi, hj, hsum⟩ := hp
    have hi0 : (0 : ℚ) ≤ p.1 := by
      have h2 := le_trans hx (orderTop_le_of_coeff_ne_zero (Function.mem_support.mp hi))
      exact_mod_cast h2
    have hj0 : (0 : ℚ) ≤ p.2 := by
      have h2 := le_trans hy (orderTop_le_of_coeff_ne_zero (Function.mem_support.mp hj))
      exact_mod_cast h2
    have hp00 : p.1 = 0 ∧ p.2 = 0 := ⟨by linarith, by linarith⟩
    simp [Prod.ext_iff, hp00.1, hp00.2]
  · intro p hp hpn
    rw [Finset.mem_singleton] at hp; subst hp
    have hx0 : x.coeff 0 = 0 ∨ y.coeff 0 = 0 := by
      by_contra hcon
      rw [not_or] at hcon
      exact hpn (Finset.mem_antidiagonal.mpr
        ⟨Function.mem_support.mpr hcon.1, Function.mem_support.mpr hcon.2, add_zero 0⟩)
    rcases hx0 with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]

/-- The underlying Hahn series of an element of `K⟨ε⟩_b`. -/
private noncomputable def limHahn (x : puiseuxBounded K) : HahnSeries ℚ K :=
  ((x : algebraicPuiseux K) : PuiseuxSeries K)

private theorem limHahn_orderTop_nonneg (x : puiseuxBounded K) : 0 ≤ (limHahn x).orderTop :=
  mem_puiseuxBounded.mp x.2

/-- **Notation 2.100.** The limit map `lim_ε : K⟨ε⟩_b → K`, sending a bounded Puiseux series
`∑_i aᵢ ε^{i/q}` to its constant term `a₀` (i.e. it replaces `ε` by `0`). It is a ring
homomorphism. -/
noncomputable def puiseuxLim (K : Type*) [Field K] : puiseuxBounded K →+* K where
  toFun x := (limHahn x).coeff 0
  map_one' := by
    have h : limHahn (1 : puiseuxBounded K) = 1 := by simp only [limHahn, OneMemClass.coe_one]
    show (limHahn 1).coeff 0 = 1
    rw [h, coeff_one, ite_eq_left rfl]
  map_mul' x y := by
    have h : limHahn (x * y) = limHahn x * limHahn y := by simp only [limHahn, MulMemClass.coe_mul]
    show (limHahn (x * y)).coeff 0 = (limHahn x).coeff 0 * (limHahn y).coeff 0
    rw [h, coeff_mul_zero_of_nonneg (limHahn_orderTop_nonneg x) (limHahn_orderTop_nonneg y)]
  map_zero' := by
    have h : limHahn (0 : puiseuxBounded K) = 0 := by simp only [limHahn, ZeroMemClass.coe_zero]
    show (limHahn 0).coeff 0 = 0
    rw [h, coeff_zero]
  map_add' x y := by
    have h : limHahn (x + y) = limHahn x + limHahn y := by simp only [limHahn, AddMemClass.coe_add]
    show (limHahn (x + y)).coeff 0 = (limHahn x).coeff 0 + (limHahn y).coeff 0
    rw [h, coeff_add]

/-- `lim_ε` of a bounded series is its Hahn coefficient at exponent `0` (its constant term). -/
theorem puiseuxLim_apply (x : puiseuxBounded K) :
    puiseuxLim K x
      = (((x : algebraicPuiseux K) : PuiseuxSeries K) : HahnSeries ℚ K).coeff 0 := rfl

end Azurite.BPR
