import Azurite.BasuPollackRoy.Chapter3.Section3_5.Derivative
import Azurite.BasuPollackRoy.Chapter3.Section3_5.ExtremeValue

/-! # BPR §3.5, Exercise 3.4 — Rolle's Theorem and the Mean Value Theorem

**Rolle's Theorem and the Mean Value Theorem hold for semialgebraic differentiable
functions** over a real closed field `R`.

The classical proofs go through verbatim once the extreme value property is available
(the unnumbered consequence of Theorem 3.20 in `ExtremeValue.lean`):

* *Rolle* (`exercise_3_4_rolle`): `f` attains its extrema on `[a, b]`. If either extremum is
  attained at an interior point, the derivative vanishes there
  (`HasDerivAtIn.eq_zero_of_interior_max`/`_min`). Otherwise both extrema sit at the
  endpoints, where `f(a) = f(b)` forces `f` to be constant — and then the hypothesized
  derivative at the midpoint must be `0` by uniqueness of limits (`HasDerivAtIn.unique`).
* *MVT* (`exercise_3_4_mvt`): apply Rolle to `f` minus the chord
  `t ↦ m·(t − a) + f(a)`, `m = (f(b) − f(a))/(b − a)`; the correction is a polynomial map,
  so semialgebraicity and continuity persist, and the derivative shifts by exactly `m`
  (`HasDerivAtIn.sub_linear`). -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Exercise 3.4, Rolle's Theorem.** A semialgebraic function continuous on `[a, b]`,
differentiable on `(a, b)`, with `f(a) = f(b)`, has a critical point in `(a, b)`. -/
theorem exercise_3_4_rolle {f : (Fin 1 → R) → (Fin 1 → R)} {f' : R → R} {a b : R}
    (hab : a < b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b)))
    (hdiff : ∀ x, a < x → x < b →
      HasDerivAtIn (fun t => f (constPt t) 0) (Set.Ioo a b) x (f' x))
    (heq : f (constPt a) 0 = f (constPt b) 0) :
    ∃ x, a < x ∧ x < b ∧ f' x = 0 := by
  obtain ⟨c, d, hc, hd, hbounds⟩ := exists_min_max_Icc hab.le hSf hcont
  by_cases hdint : a < d ∧ d < b
  · -- the maximum is interior
    refine ⟨d, hdint.1, hdint.2, ?_⟩
    exact (hdiff d hdint.1 hdint.2).eq_zero_of_interior_max hdint.1 hdint.2
      (fun t ht => (hbounds t ht.1.le ht.2.le).2)
  · by_cases hcint : a < c ∧ c < b
    · -- the minimum is interior
      refine ⟨c, hcint.1, hcint.2, ?_⟩
      exact (hdiff c hcint.1 hcint.2).eq_zero_of_interior_min hcint.1 hcint.2
        (fun t ht => (hbounds t ht.1.le ht.2.le).1)
    · -- both extrema at the endpoints: `f` is constant on `[a, b]`
      have hends : ∀ e : R, (a ≤ e ∧ e ≤ b) → ¬(a < e ∧ e < b) →
          f (constPt e) 0 = f (constPt a) 0 := by
        rintro e ⟨he1, he2⟩ hnot
        rcases not_and_or.mp hnot with h | h
        · rw [le_antisymm (not_lt.mp h) he1]
        · rw [le_antisymm he2 (not_lt.mp h), ← heq]
      have hdval := hends d hd hdint
      have hcval := hends c hc hcint
      have hconst : ∀ t, a ≤ t → t ≤ b → f (constPt t) 0 = f (constPt a) 0 := by
        intro t ht1 ht2
        have hb1 := (hbounds t ht1 ht2).1
        have hb2 := (hbounds t ht1 ht2).2
        rw [hcval] at hb1
        rw [hdval] at hb2
        exact le_antisymm hb2 hb1
      set x₀ := (a + b) / 2 with hx₀d
      have hax₀ : a < x₀ := by rw [hx₀d]; linarith
      have hx₀b : x₀ < b := by rw [hx₀d]; linarith
      refine ⟨x₀, hax₀, hx₀b, ?_⟩
      have hzero : HasDerivAtIn (fun t => f (constPt t) 0) (Set.Ioo a b) x₀ 0 :=
        hasDerivAtIn_of_constOn (fun t ht => hconst t ht.1.le ht.2.le)
          (hconst x₀ hax₀.le hx₀b.le)
      exact (hdiff x₀ hax₀ hx₀b).unique (accPt'_Ioo hax₀ hx₀b) hzero

/-- **Exercise 3.4, Mean Value Theorem.** A semialgebraic function continuous on `[a, b]` and
differentiable on `(a, b)` has a point in `(a, b)` where the derivative equals the slope of
the chord. -/
theorem exercise_3_4_mvt {f : (Fin 1 → R) → (Fin 1 → R)} {f' : R → R} {a b : R}
    (hab : a < b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b)))
    (hdiff : ∀ x, a < x → x < b →
      HasDerivAtIn (fun t => f (constPt t) 0) (Set.Ioo a b) x (f' x)) :
    ∃ x, a < x ∧ x < b ∧ f' x = (f (constPt b) 0 - f (constPt a) 0) / (b - a) := by
  set m := (f (constPt b) 0 - f (constPt a) 0) / (b - a) with hmd
  -- the chord correction, as a polynomial map on the line
  set p : MvPolynomial (Fin 1) R := C m * (X 0 - C a) with hpd
  have hpoly_eval : ∀ t : R, polyFun p (constPt t) 0 = m * (t - a) := by
    intro t
    show eval (constPt t) (C m * (X 0 - C a)) = m * (t - a)
    simp [constPt]
  set h : (Fin 1 → R) → (Fin 1 → R) := f + -polyFun p with hhd
  have hval : ∀ t : R, h (constPt t) 0 = f (constPt t) 0 - m * (t - a) := by
    intro t
    show f (constPt t) 0 + -(polyFun p) (constPt t) 0 = _
    rw [hpoly_eval t]
    ring
  -- Rolle hypotheses for `h`
  have hSh : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) h :=
    hSf.add (polyFun_isSemialgebraicFunction_on (isSemialgebraicSet_Icc a b) p).neg
  have hconth : ContinuousOn h (Set.Icc (constPt a) (constPt b)) := by
    refine ContinuousOn.fin_one_add hcont (ContinuousOn.fin_one_neg ?_)
    have hpc : Continuous (polyFun p) :=
      continuous_iff_components.mpr (fun _ => continuousR_eval p)
    exact hpc.continuousOn
  have hdiffh : ∀ x, a < x → x < b →
      HasDerivAtIn (fun t => h (constPt t) 0) (Set.Ioo a b) x (f' x - m) := by
    intro x hax hxb
    have hfun : (fun t => h (constPt t) 0)
        = fun t => f (constPt t) 0 - (m * t + -(m * a)) := by
      funext t
      rw [hval t]
      ring
    rw [hfun]
    exact (hdiff x hax hxb).sub_linear m (-(m * a))
  have heqh : h (constPt a) 0 = h (constPt b) 0 := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    rw [hval a, hval b, hmd, sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hba]
    ring
  obtain ⟨x, hax, hxb, hx⟩ := exercise_3_4_rolle hab hSh hconth hdiffh heqh
  exact ⟨x, hax, hxb, by linarith⟩

end Azurite.BPR
