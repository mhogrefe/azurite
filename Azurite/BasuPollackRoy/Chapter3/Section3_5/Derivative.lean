import Azurite.BasuPollackRoy.Chapter3.Section3_5.Limits

/-! # BPR §3.5 — first properties of the one-variable derivative

The toolkit for Exercise 3.4 (Rolle, MVT) and the later development:

* `LimitAtInR.unique` — limits along `M` are unique at an accumulation point of `M`;
* `HasDerivAtIn.unique` — hence so are derivatives;
* `HasDerivAtIn.neg`, `HasDerivAtIn.sub_linear` — derivative arithmetic (the difference
  quotients transform *exactly*, no estimates needed);
* `hasDerivAtIn_of_constOn` — a function constant on `M ∪ {x₀}` has derivative `0`;
* `HasDerivAtIn.eq_zero_of_interior_max` / `eq_zero_of_interior_min` — at an interior
  extremum on `(a, b)` the derivative vanishes (the one-sided difference quotients have
  opposite signs).

Everything is a first-order ε–δ argument over the real closed field `R`. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Uniqueness of limits -/

/-- A point `x₀` is an **accumulation point** of `M ⊆ R` if `M` has points other than `x₀`
arbitrarily close to `x₀`. (E.g. any point of `[a, b]` for `M = (a, b)`, `a < b`.) -/
def AccPt' (M : Set R) (x₀ : R) : Prop :=
  ∀ δ, 0 < δ → ∃ t ∈ M, t ≠ x₀ ∧ |t - x₀| < δ

theorem accPt'_Ioo {a b x₀ : R} (hax : a < x₀) (hxb : x₀ < b) : AccPt' (Set.Ioo a b) x₀ := by
  intro δ hδ
  have hmin : 0 < min (δ / 2) ((b - x₀) / 2) := lt_min (by linarith) (by linarith)
  have hminr := min_le_right (δ / 2) ((b - x₀) / 2)
  have hminl := min_le_left (δ / 2) ((b - x₀) / 2)
  refine ⟨x₀ + min (δ / 2) ((b - x₀) / 2), ⟨by linarith, by linarith⟩,
    ne_of_gt (by linarith), ?_⟩
  rw [add_sub_cancel_left, abs_of_pos hmin]
  linarith

/-- **Limits along `M` are unique at an accumulation point of `M`.** -/
theorem LimitAtInR.unique {g : R → R} {M : Set R} {x₀ y₀ y₁ : R} (hacc : AccPt' M x₀)
    (h₀ : LimitAtInR g M x₀ y₀) (h₁ : LimitAtInR g M x₀ y₁) : y₀ = y₁ := by
  by_contra hne
  have hr : 0 < |y₀ - y₁| / 2 := by
    have : y₀ - y₁ ≠ 0 := sub_ne_zero.mpr hne
    have := abs_pos.mpr this
    linarith
  obtain ⟨δ₀, hδ₀, hb₀⟩ := h₀ _ hr
  obtain ⟨δ₁, hδ₁, hb₁⟩ := h₁ _ hr
  obtain ⟨t, htM, htne, htδ⟩ := hacc (min δ₀ δ₁) (lt_min hδ₀ hδ₁)
  have e₀ := hb₀ t htM htne (htδ.trans_le (min_le_left _ _))
  have e₁ := hb₁ t htM htne (htδ.trans_le (min_le_right _ _))
  have hcontra : |y₀ - y₁| < |y₀ - y₁| := by
    calc |y₀ - y₁| = |(y₀ - g t) + (g t - y₁)| := by ring_nf
      _ ≤ |y₀ - g t| + |g t - y₁| := abs_add_le _ _
      _ = |g t - y₀| + |g t - y₁| := by rw [abs_sub_comm]
      _ < |y₀ - y₁| / 2 + |y₀ - y₁| / 2 := add_lt_add e₀ e₁
      _ = |y₀ - y₁| := by ring
  exact absurd hcontra (lt_irrefl _)

/-- **Derivatives are unique** at an accumulation point of `M`. -/
theorem HasDerivAtIn.unique {g : R → R} {M : Set R} {x₀ d₀ d₁ : R} (hacc : AccPt' M x₀)
    (h₀ : HasDerivAtIn g M x₀ d₀) (h₁ : HasDerivAtIn g M x₀ d₁) : d₀ = d₁ :=
  LimitAtInR.unique hacc h₀ h₁

/-! ### Derivative arithmetic -/

omit [IsStrictOrderedRing R] in
/-- The derivative of a negation: the difference quotient negates exactly. -/
theorem HasDerivAtIn.neg {g : R → R} {M : Set R} {x₀ d : R} (hd : HasDerivAtIn g M x₀ d) :
    HasDerivAtIn (fun t => -(g t)) M x₀ (-d) := by
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := hd r hr
  refine ⟨δ, hδ, fun t htM htne htδ => ?_⟩
  have hq : |(g t - g x₀) / (t - x₀) - d| < r := hb t htM htne htδ
  show |(-(g t) - -(g x₀)) / (t - x₀) - -d| < r
  have heq : (-(g t) - -(g x₀)) / (t - x₀) - -d = -((g t - g x₀) / (t - x₀) - d) := by ring
  rw [heq, abs_neg]
  exact hq

omit [IsStrictOrderedRing R] in
/-- Subtracting an affine function shifts the derivative by its slope: the difference
quotient of `g(t) − (mt + q)` is exactly that of `g` minus `m`. -/
theorem HasDerivAtIn.sub_linear {g : R → R} {M : Set R} {x₀ d : R} (m q : R)
    (hd : HasDerivAtIn g M x₀ d) :
    HasDerivAtIn (fun t => g t - (m * t + q)) M x₀ (d - m) := by
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := hd r hr
  refine ⟨δ, hδ, fun t htM htne htδ => ?_⟩
  have hq : |(g t - g x₀) / (t - x₀) - d| < r := hb t htM htne htδ
  show |(g t - (m * t + q) - (g x₀ - (m * x₀ + q))) / (t - x₀) - (d - m)| < r
  have hne : t - x₀ ≠ 0 := sub_ne_zero.mpr htne
  have hident : (g t - (m * t + q) - (g x₀ - (m * x₀ + q))) / (t - x₀)
      = (g t - g x₀) / (t - x₀) - m := by
    field_simp
    ring
  rw [hident]
  have heq : (g t - g x₀) / (t - x₀) - m - (d - m) = (g t - g x₀) / (t - x₀) - d := by ring
  rw [heq]
  exact hq

/-- A function constant on `M ∪ {x₀}` has derivative `0` at `x₀` within `M`. -/
theorem hasDerivAtIn_of_constOn {g : R → R} {M : Set R} {x₀ c : R}
    (hM : ∀ t ∈ M, g t = c) (hx₀ : g x₀ = c) : HasDerivAtIn g M x₀ 0 :=
  fun r hr => ⟨1, one_pos, fun t htM _ _ => by
    show |(g t - g x₀) / (t - x₀) - 0| < r
    rw [hM t htM, hx₀, sub_self, zero_div, sub_zero, abs_zero]
    exact hr⟩

/-! ### Interior extrema -/

/-- **At an interior maximum the derivative vanishes**: the difference quotient is `≤ 0` on
the right of `x₀` and `≥ 0` on the left. -/
theorem HasDerivAtIn.eq_zero_of_interior_max {g : R → R} {a b x₀ d : R}
    (hax : a < x₀) (hxb : x₀ < b) (hmax : ∀ t ∈ Set.Ioo a b, g t ≤ g x₀)
    (hd : HasDerivAtIn g (Set.Ioo a b) x₀ d) : d = 0 := by
  refine le_antisymm ?_ ?_
  · -- `d ≤ 0`, approaching from the right
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨δ, hδ, hb⟩ := hd (d / 2) (by linarith)
    set t := x₀ + min (δ / 2) ((b - x₀) / 2) with htd
    have hmin : 0 < min (δ / 2) ((b - x₀) / 2) := lt_min (by linarith) (by linarith)
    have hxt : x₀ < t := by rw [htd]; linarith
    have htb : t < b := by
      have := min_le_right (δ / 2) ((b - x₀) / 2); rw [htd]; linarith
    have htδ : |t - x₀| < δ := by
      rw [htd, add_sub_cancel_left, abs_of_pos hmin]
      have := min_le_left (δ / 2) ((b - x₀) / 2); linarith
    have hq : |(g t - g x₀) / (t - x₀) - d| < d / 2 := hb t ⟨by linarith, htb⟩ (ne_of_gt hxt) htδ
    have hqle : (g t - g x₀) / (t - x₀) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hmax t ⟨by linarith, htb⟩)) (by linarith)
    have := (abs_lt.mp hq).1
    linarith
  · -- `0 ≤ d`, approaching from the left
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨δ, hδ, hb⟩ := hd (-d / 2) (by linarith)
    set t := x₀ - min (δ / 2) ((x₀ - a) / 2) with htd
    have hmin : 0 < min (δ / 2) ((x₀ - a) / 2) := lt_min (by linarith) (by linarith)
    have htx : t < x₀ := by rw [htd]; linarith
    have hat : a < t := by
      have := min_le_right (δ / 2) ((x₀ - a) / 2); rw [htd]; linarith
    have htδ : |t - x₀| < δ := by
      rw [htd, sub_sub_cancel_left, abs_neg, abs_of_pos hmin]
      have := min_le_left (δ / 2) ((x₀ - a) / 2); linarith
    have hq : |(g t - g x₀) / (t - x₀) - d| < -d / 2 := hb t ⟨hat, by linarith⟩ (ne_of_lt htx) htδ
    have hqge : 0 ≤ (g t - g x₀) / (t - x₀) :=
      div_nonneg_of_nonpos
        (sub_nonpos.mpr (hmax t ⟨hat, by linarith⟩)) (by linarith)
    have := (abs_lt.mp hq).2
    linarith

/-- **At an interior minimum the derivative vanishes** (the maximum case for `−g`). -/
theorem HasDerivAtIn.eq_zero_of_interior_min {g : R → R} {a b x₀ d : R}
    (hax : a < x₀) (hxb : x₀ < b) (hmin : ∀ t ∈ Set.Ioo a b, g x₀ ≤ g t)
    (hd : HasDerivAtIn g (Set.Ioo a b) x₀ d) : d = 0 := by
  have h := hd.neg.eq_zero_of_interior_max hax hxb
    (fun t ht => neg_le_neg (hmin t ht))
  linarith

end Azurite.BPR
