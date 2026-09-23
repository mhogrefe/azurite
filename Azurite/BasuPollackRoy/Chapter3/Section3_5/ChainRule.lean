import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_24

/-! # BPR §3.5 — the chain rule and the reciprocal rule for partial derivatives

Two pieces of differential calculus needed for the `𝒮^ℓ`-smoothness of the inverse in
Proposition 3.24 ("we easily get..."):

* **the chain rule** (`hasPartialDerivAtIn_comp`): if `c` is `𝒮¹` on an open `U ⊆ R^p`
  (partial derivatives `gc` exist and are continuous, and `c` is semialgebraic — needed
  because the first-order approximation `isLittleO_sub_totalDeriv` rests on the
  semialgebraic mean value theorem) and `h : V → U` has `j`-th partial derivatives
  `dh m` at `x₀`, then `c ∘ h` has `j`-th partial derivative
  `∑ m, ∂c/∂u_m(h x₀) · dh m` at `x₀`;

* **the reciprocal rule** (`HasPartialDerivAtIn.inv`, via the one-variable
  `HasDerivAtIn.inv` and the limit lemma `LimitAtInR.inv`): where `c` is nonvanishing,
  `(1/c)' = -c'/c²`.

The chain-rule proof is the standard ε–δ argument: write
`c(h(t)) - c(u₀) = Σ_m ∂c/∂u_m(u₀)(h(t)_m - u₀_m) + E(h(t))` with `E = o(‖·- u₀‖)`,
divide by `t - t₀`, and control the error using the coordinatewise displacement bound
`‖h(t) - u₀‖ ≤ C |t - t₀|` extracted from the difference quotients of `h`. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Limits and derivatives of reciprocals -/

omit [IsRealClosed R] in
/-- The reciprocal of a limit: if `g → L ≠ 0` then `1/g → 1/L`. -/
theorem LimitAtInR.inv {g : R → R} {M : Set R} {x₀ L : R}
    (h : LimitAtInR g M x₀ L) (hL : L ≠ 0) :
    LimitAtInR (fun t => (g t)⁻¹) M x₀ L⁻¹ := by
  intro r hr
  have hLpos : 0 < |L| := abs_pos.mpr hL
  obtain ⟨δ₁, hδ₁, h₁⟩ := h (|L| / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := h (r * (|L| / 2) * |L|) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht htne htδ => ?_⟩
  have hg1 := h₁ t ht htne (htδ.trans_le (min_le_left _ _))
  have hg2 := h₂ t ht htne (htδ.trans_le (min_le_right _ _))
  -- `|g t| > |L|/2`, in particular `g t ≠ 0`
  have hgt : |L| / 2 < |g t| := by
    have h3 := abs_sub_abs_le_abs_sub L (g t)
    have h4 : |L - g t| = |g t - L| := abs_sub_comm _ _
    linarith
  have hgne : g t ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgt
    linarith
  rw [inv_sub_inv' hgne hL, abs_mul, abs_mul, abs_inv, abs_inv]
  -- `|g t|⁻¹ |g t - L| |L|⁻¹ < r ⟸ |g t - L| < r (|L|/2) |L| ≤ r |g t| |L|`
  have hgtpos : 0 < |g t| := by linarith
  rw [show (|g t|)⁻¹ * |L - g t| * (|L|)⁻¹
      = |L - g t| / (|g t| * |L|) by rw [div_eq_mul_inv, mul_inv]; ring]
  rw [div_lt_iff₀ (by positivity)]
  have h5 : r * (|L| / 2) ≤ r * |g t| := mul_le_mul_of_nonneg_left hgt.le hr.le
  calc |L - g t| = |g t - L| := abs_sub_comm _ _
    _ < r * (|L| / 2) * |L| := hg2
    _ ≤ r * |g t| * |L| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
    _ = r * (|g t| * |L|) := mul_assoc _ _ _

omit [IsRealClosed R] in
/-- **The reciprocal rule** (one variable): where `φ` is nonvanishing on `M` and at the
base point, `(1/φ)' = -φ'/φ²`. -/
theorem HasDerivAtIn.inv {φ : R → R} {M : Set R} {t₀ d : R}
    (h : HasDerivAtIn φ M t₀ d) (hne : ∀ t ∈ M, φ t ≠ 0) (h0 : φ t₀ ≠ 0) :
    HasDerivAtIn (fun t => (φ t)⁻¹) M t₀ (-d * (φ t₀ * φ t₀)⁻¹) := by
  have hsq : φ t₀ * φ t₀ ≠ 0 := mul_ne_zero h0 h0
  -- the product `φ t * φ t₀` tends to `φ t₀ * φ t₀`
  have hprod : LimitAtInR (fun t => φ t * φ t₀) M t₀ (φ t₀ * φ t₀) :=
    LimitAtInR.mul h.limitAtInR_self (limitAtInR_const M t₀ (φ t₀))
  have hrec : LimitAtInR (fun t => (φ t * φ t₀)⁻¹) M t₀ (φ t₀ * φ t₀)⁻¹ :=
    hprod.inv hsq
  have hmain : LimitAtInR
      (fun t => -((φ t - φ t₀) / (t - t₀)) * (φ t * φ t₀)⁻¹) M t₀
      (-d * (φ t₀ * φ t₀)⁻¹) :=
    LimitAtInR.mul (LimitAtInR.neg h) hrec
  refine LimitAtInR.congr (fun t htM htne => ?_) hmain
  -- the algebraic identity for `t ∈ M`, `t ≠ t₀`
  have hφt : φ t ≠ 0 := hne t htM
  have htt : t - t₀ ≠ 0 := sub_ne_zero.mpr htne
  field_simp
  ring

omit [IsRealClosed R] in
/-- **The reciprocal rule** for partial derivatives: where `c` is nonvanishing on `U`,
`∂(1/c)/∂xᵢ = -(∂c/∂xᵢ)/c²`. -/
theorem HasPartialDerivAtIn.inv {k : ℕ} {c : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d : R}
    (h : HasPartialDerivAtIn c U i x d) (hne : ∀ y ∈ U, c y ≠ 0) (hx : x ∈ U) :
    HasPartialDerivAtIn (fun y => (c y)⁻¹) U i x (-d * (c x * c x)⁻¹) := by
  have h0 : c (Function.update x i (x i)) ≠ 0 := by
    rw [Function.update_eq_self]
    exact hne x hx
  have h1 : HasDerivAtIn (fun t => (c (Function.update x i t))⁻¹)
      {t : R | Function.update x i t ∈ U} (x i)
      (-d * (c (Function.update x i (x i)) * c (Function.update x i (x i)))⁻¹) :=
    HasDerivAtIn.inv h (fun t ht => hne _ ht) h0
  rw [Function.update_eq_self] at h1
  exact h1

/-! ### The chain rule -/

/-- **The chain rule.** Let `U ⊆ R^p` be open, `c : U → R` semialgebraic with partial
derivatives `gc m` existing on `U` and continuous (i.e. `c ∈ 𝒮¹(U, R)`), and let
`h : V → U` have `j`-th partial derivatives `dh m` at `x₀ ∈ V` (componentwise). Then
`c ∘ h` has `j`-th partial derivative `∑ m, gc m (h x₀) · dh m` at `x₀`. -/
theorem hasPartialDerivAtIn_comp {k p : ℕ} {V : Set (Fin k → R)} {U : Set (Fin p → R)}
    {h : (Fin k → R) → (Fin p → R)} {c : (Fin p → R) → R}
    {gc : Fin p → (Fin p → R) → R} {dh : Fin p → R}
    (hUopen : IsOpen U) (hmaps : Set.MapsTo h V U)
    (hcsa : IsSemialgebraicFunction U (scalarFun c))
    (hcdiff : ∀ m, ∀ u ∈ U, HasPartialDerivAtIn c U m u (gc m u))
    (hgccont : ∀ m, ContinuousOn (scalarFun (gc m)) U)
    {x₀ : Fin k → R} (hx₀V : x₀ ∈ V) {j : Fin k}
    (hh : ∀ m, HasPartialDerivAtIn (fun w => h w m) V j x₀ (dh m)) :
    HasPartialDerivAtIn (fun w => c (h w)) V j x₀ (∑ m, gc m (h x₀) * dh m) := by
  classical
  -- the degenerate case `p = 0`: `c ∘ h` is constant
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0
    have hconst : ∀ w, c (h w) = c (h x₀) := fun w => congrArg c (Subsingleton.elim _ _)
    have hzero : (∑ m : Fin 0, gc m (h x₀) * dh m) = 0 := by simp
    rw [hzero]
    show HasDerivAtIn (fun t => c (h (Function.update x₀ j t)))
      {t : R | Function.update x₀ j t ∈ V} (x₀ j) 0
    exact hasDerivAtIn_of_constOn (fun t _ => hconst _) (hconst _)
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  set u₀ : Fin p → R := h x₀ with hu₀
  have hu₀U : u₀ ∈ U := hmaps hx₀V
  -- the first-order approximation of `c` at `u₀` (through the scalar view `p' = 1`)
  have hlo : IsLittleO (fun y => scalarFun c y - scalarFun c u₀
      - totalDeriv (fun _ : Fin 1 => gc) u₀ (y - u₀)) U u₀ := by
    refine isLittleO_sub_totalDeriv hUopen (fun l => ?_) (fun l m y hy => ?_)
      (fun _ m => hgccont m) hu₀U
    · have heq : (fun y : Fin p → R => scalarFun c y l) = c := rfl
      rw [heq]
      exact hcsa
    · have heq : (fun y : Fin p → R => scalarFun c y l) = c := rfl
      rw [heq]
      exact hcdiff m y hy
  -- extracted scalar form of the little-o bound
  have hloS : ∀ r, 0 < r → ∃ δ, 0 < δ ∧ ∀ y ∈ U, y ≠ u₀ →
      euclideanNorm (y - u₀) < δ →
      |c y - c u₀ - ∑ m, gc m u₀ * (y - u₀) m| ≤ r * euclideanNorm (y - u₀) := by
    intro r hr
    obtain ⟨δ, hδ, hb⟩ := hlo r hr
    refine ⟨δ, hδ, fun y hy hyne hyδ => ?_⟩
    have hq := hb y hy hyne hyδ
    rw [sub_zero] at hq
    have hnpos : 0 < euclideanNorm (y - u₀) := euclideanNorm_pos_of_ne hyne
    have hq2 : (euclideanNorm (y - u₀))⁻¹
        * euclideanNorm (scalarFun c y - scalarFun c u₀
            - totalDeriv (fun _ : Fin 1 => gc) u₀ (y - u₀)) < r := by
      have h3 := hq
      rw [euclideanNorm_smul, abs_inv, abs_of_nonneg (euclideanNorm_nonneg _)] at h3
      exact h3
    have hcomp : euclideanNorm (scalarFun c y - scalarFun c u₀
        - totalDeriv (fun _ : Fin 1 => gc) u₀ (y - u₀))
        = |c y - c u₀ - ∑ m, gc m u₀ * (y - u₀) m| := by
      rw [euclideanNorm_fin_one]
      rfl
    rw [hcomp] at hq2
    have h4 := mul_lt_mul_of_pos_left hq2 hnpos
    rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul, mul_comm] at h4
    exact h4.le
  -- abbreviations for the slice
  set t₀ : R := x₀ j with ht₀
  set M : Set R := {t : R | Function.update x₀ j t ∈ V} with hM
  set φ : R → (Fin p → R) := fun t => h (Function.update x₀ j t) with hφ
  have hφt₀ : φ t₀ = u₀ := by
    show h (Function.update x₀ j (x₀ j)) = h x₀
    rw [Function.update_eq_self]
  have hφU : ∀ t ∈ M, φ t ∈ U := fun t ht => hmaps ht
  -- the constants
  set C : R := ∑ m, (|dh m| + 1) with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun m _ => by positivity
  set Q : R := ∑ m, |gc m u₀| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun m _ => abs_nonneg _
  -- the ε–δ proof
  intro r hr
  set r' : R := r / (2 * (C + 1)) with hr'
  have hr'pos : 0 < r' := by positivity
  set ε' : R := r / (2 * (Q + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δo, hδo, hbo⟩ := hloS r' hr'pos
  -- per-coordinate difference-quotient bounds
  have hper : ∀ m, ∃ δ, 0 < δ ∧ ∀ t ∈ M, t ≠ t₀ → |t - t₀| < δ →
      |(φ t m - u₀ m) / (t - t₀) - dh m| < min ε' 1 := by
    intro m
    obtain ⟨δ, hδ, hb⟩ := hh m (min ε' 1) (lt_min hε'pos one_pos)
    refine ⟨δ, hδ, fun t ht htne htδ => ?_⟩
    have hb' : |(h (Function.update x₀ j t) m - h (Function.update x₀ j (x₀ j)) m)
        / (t - x₀ j) - dh m| < min ε' 1 := hb t ht htne htδ
    rw [Function.update_eq_self] at hb'
    exact hb'
  choose δm hδmpos hbm using hper
  set δq : R := Finset.univ.inf' Finset.univ_nonempty δm with hδq
  have hδqpos : 0 < δq := by
    rw [hδq, Finset.lt_inf'_iff]
    exact fun m _ => hδmpos m
  refine ⟨min δq (δo / (C + 1)), lt_min hδqpos (by positivity), fun t htM htne htδ => ?_⟩
  have htq : |t - t₀| < δq := lt_of_lt_of_le htδ (min_le_left _ _)
  have hto : |t - t₀| < δo / (C + 1) := lt_of_lt_of_le htδ (min_le_right _ _)
  have htne' : t - t₀ ≠ 0 := sub_ne_zero.mpr htne
  have htabs : 0 < |t - t₀| := abs_pos.mpr htne'
  -- quotient bounds at `t`
  have hquot : ∀ m, |(φ t m - u₀ m) / (t - t₀) - dh m| < min ε' 1 := fun m =>
    hbm m t htM htne (lt_of_lt_of_le htq (by
      rw [hδq]
      exact Finset.inf'_le _ (Finset.mem_univ m)))
  -- coordinate displacement bound
  have hcoord : ∀ m, |φ t m - u₀ m| ≤ (|dh m| + 1) * |t - t₀| := by
    intro m
    have h6 : |φ t m - u₀ m| = |(φ t m - u₀ m) / (t - t₀)| * |t - t₀| := by
      rw [← abs_mul, div_mul_cancel₀ _ htne']
    have h8 := abs_add_le ((φ t m - u₀ m) / (t - t₀) - dh m) (dh m)
    rw [sub_add_cancel] at h8
    have h9 := (hquot m).trans_le (min_le_right ε' 1)
    have h7 : |(φ t m - u₀ m) / (t - t₀)| ≤ |dh m| + 1 := by linarith
    rw [h6]
    exact mul_le_mul_of_nonneg_right h7 (abs_nonneg _)
  -- norm displacement bound: `‖φ t - u₀‖ ≤ C |t - t₀|`
  have hnorm : euclideanNorm (φ t - u₀) ≤ C * |t - t₀| := by
    rw [euclideanNorm_le_iff_normSq_le (by positivity)]
    have h10 : euclideanNormSq (φ t - u₀) ≤ ∑ m, ((|dh m| + 1) * |t - t₀|) ^ 2 := by
      refine Finset.sum_le_sum fun m _ => ?_
      have h11 : (φ t - u₀) m = φ t m - u₀ m := rfl
      rw [h11, ← sq_abs (φ t m - u₀ m), pow_two, pow_two]
      exact mul_self_le_mul_self (abs_nonneg _) (hcoord m)
    have h12 : (∑ m, ((|dh m| + 1) * |t - t₀|) ^ 2)
        = (∑ m, (|dh m| + 1) ^ 2) * |t - t₀| ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by rw [mul_pow]
    have h13 : (∑ m, (|dh m| + 1) ^ 2) ≤ C ^ 2 := by
      rw [hC]
      exact Finset.sum_sq_le_sq_sum_of_nonneg fun m _ => by positivity
    calc euclideanNormSq (φ t - u₀) ≤ (∑ m, (|dh m| + 1) ^ 2) * |t - t₀| ^ 2 := by
          rw [← h12]; exact h10
      _ ≤ C ^ 2 * |t - t₀| ^ 2 := mul_le_mul_of_nonneg_right h13 (sq_nonneg _)
      _ = (C * |t - t₀|) ^ 2 := by rw [mul_pow]
  have hnormlt : euclideanNorm (φ t - u₀) < δo := by
    have h11 : C * |t - t₀| ≤ C * (δo / (C + 1)) := mul_le_mul_of_nonneg_left hto.le hC0
    have h12 : C * (δo / (C + 1)) < δo := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- the bounded pieces of the error budget
  have hQbound : (∑ m, |gc m u₀| * |(φ t m - u₀ m) / (t - t₀) - dh m|) ≤ Q * ε' := by
    rw [hQ, Finset.sum_mul]
    refine Finset.sum_le_sum fun m _ => ?_
    exact mul_le_mul_of_nonneg_left
      ((hquot m).le.trans (min_le_left _ _)) (abs_nonneg _)
  have hQfinal : Q * ε' < r / 2 := by
    rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hCfinal : r' * C ≤ r / 2 := by
    rw [hr', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- the goal, in slice form
  show |(c (φ t) - c (φ t₀)) / (t - t₀) - ∑ m, gc m u₀ * dh m| < r
  rw [hφt₀]
  by_cases hsame : φ t = u₀
  · -- the curve returns to `u₀`: every `|dh m|` is below `ε'`, so the sum is small
    rw [hsame, sub_self, zero_div, zero_sub, abs_neg]
    have hdh : ∀ m, |dh m| ≤ ε' := by
      intro m
      have h14 := hquot m
      rw [hsame] at h14
      rw [sub_self, zero_div, zero_sub, abs_neg] at h14
      exact h14.le.trans (min_le_left _ _)
    calc |∑ m, gc m u₀ * dh m| ≤ ∑ m, |gc m u₀ * dh m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, |gc m u₀| * ε' := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hdh m) (abs_nonneg _)
      _ = Q * ε' := by rw [hQ, Finset.sum_mul]
      _ < r / 2 := hQfinal
      _ < r := by linarith
  · -- the main estimate
    have hErr := hbo (φ t) (hφU t htM) hsame hnormlt
    -- the decomposition of the difference quotient
    set E : R := c (φ t) - c u₀ - ∑ m, gc m u₀ * (φ t - u₀) m with hE
    set S : R := ∑ m, gc m u₀ * ((φ t m - u₀ m) / (t - t₀) - dh m) with hS
    have hiden : (c (φ t) - c u₀) / (t - t₀) - ∑ m, gc m u₀ * dh m
        = E / (t - t₀) + S := by
      have h2 : (∑ m, gc m u₀ * (φ t - u₀) m) / (t - t₀)
          = ∑ m, gc m u₀ * ((φ t m - u₀ m) / (t - t₀)) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        show gc m u₀ * (φ t m - u₀ m) * (t - t₀)⁻¹
            = gc m u₀ * ((φ t m - u₀ m) / (t - t₀))
        rw [div_eq_mul_inv, mul_assoc]
      have h3 : S = (∑ m, gc m u₀ * ((φ t m - u₀ m) / (t - t₀)))
          - ∑ m, gc m u₀ * dh m := by
        rw [hS, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => mul_sub _ _ _
      rw [hE, sub_div, sub_div, h2, h3]
      ring
    rw [hiden]
    -- bound the two pieces
    have hEbound : |E / (t - t₀)| ≤ r' * C := by
      rw [abs_div]
      rw [div_le_iff₀ htabs]
      calc |E| ≤ r' * euclideanNorm (φ t - u₀) := hErr
        _ ≤ r' * (C * |t - t₀|) := mul_le_mul_of_nonneg_left hnorm hr'pos.le
        _ = r' * C * |t - t₀| := by ring
    have hSbound : |S| ≤ Q * ε' := by
      calc |S| ≤ ∑ m, |gc m u₀ * ((φ t m - u₀ m) / (t - t₀) - dh m)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ m, |gc m u₀| * |(φ t m - u₀ m) / (t - t₀) - dh m| := by
            exact Finset.sum_congr rfl fun m _ => abs_mul _ _
        _ ≤ Q * ε' := hQbound
    calc |E / (t - t₀) + S| ≤ |E / (t - t₀)| + |S| := abs_add_le _ _
      _ ≤ r' * C + Q * ε' := add_le_add hEbound hSbound
      _ < r / 2 + r / 2 := by
          have := hCfinal
          have := hQfinal
          linarith
      _ = r := by ring

end Azurite.BPR
