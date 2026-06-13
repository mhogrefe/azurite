import Azurite.BasuPollackRoy.Chapter3.Section3_5.Exercise_3_4
import Azurite.BasuPollackRoy.Chapter3.Section3_5.PartialDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # BPR §3.5 — the derivative, the Jacobian, and first-order approximation

For `f : U → R^p` with partial derivatives `g l j = ∂f_l/∂X_j` on `U`, **the derivative
`df(x₀)`** is the linear map `R^k → R^p` sending `h` to
`(∑_j ∂f_1/∂X_j(x₀) h_j, …, ∑_j ∂f_p/∂X_j(x₀) h_j)` (`totalDeriv`; linearity is
`totalDeriv_add`/`totalDeriv_smul`). Its matrix is the **Jacobian matrix**
(`jacobianMatrix`) and, for `p = k`, its determinant is the **Jacobian** (`jacobian`).

Following the usual arguments from a calculus course, **when the partial derivatives exist
on the open `U` and are continuous**,

  `f(x) − f(x₀) − df(x₀)(x − x₀) = o(‖x − x₀‖)`

(`isLittleO_sub_totalDeriv`). The proof is the classical one, made semialgebraic: moving
from `x₀` to `x` one coordinate at a time, each increment is governed by the Mean Value
Theorem (Exercise 3.4 — whose extreme-value input is where semialgebraicity of `f` enters:
over a general real closed field the MVT is a theorem about *definable* functions), so

  `f_l(x) − f_l(x₀) − ∑_j ∂_j f_l(x₀) Δ_j = ∑_j (∂_j f_l(w_{lj}) − ∂_j f_l(x₀)) Δ_j`

with each intermediate point `w_{lj}` in the coordinate box between `x₀` and `x`; continuity
of the partials at `x₀` then bounds each bracket. As in the univariate case, one can iterate
the definition of `HasPartialDerivAtIn` to define higher derivatives. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### The derivative as a linear map; Jacobian matrix and Jacobian -/

/-- **BPR's derivative `df(x₀)`**: given the partial derivatives `g l j = ∂f_l/∂X_j`, the
linear map `R^k → R^p` sending `(h_1, …, h_k)` to
`(∑_j ∂f_1/∂X_j(x₀) h_j, …, ∑_j ∂f_p/∂X_j(x₀) h_j)`. -/
def totalDeriv {k p : ℕ} (g : Fin p → Fin k → (Fin k → R) → R) (x₀ : Fin k → R)
    (h : Fin k → R) : Fin p → R :=
  fun l => ∑ j, g l j x₀ * h j

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem totalDeriv_add {k p : ℕ} [Field R] (g : Fin p → Fin k → (Fin k → R) → R)
    (x₀ : Fin k → R) (h₁ h₂ : Fin k → R) :
    totalDeriv g x₀ (h₁ + h₂) = totalDeriv g x₀ h₁ + totalDeriv g x₀ h₂ := by
  funext l
  simp only [totalDeriv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem totalDeriv_smul {k p : ℕ} [Field R] (g : Fin p → Fin k → (Fin k → R) → R)
    (x₀ : Fin k → R) (a : R) (h : Fin k → R) :
    totalDeriv g x₀ (a • h) = a • totalDeriv g x₀ h := by
  funext l
  simp only [totalDeriv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Jacobian matrix** of `f` at `x₀`: the matrix of `df(x₀)`. -/
def jacobianMatrix {k p : ℕ} (g : Fin p → Fin k → (Fin k → R) → R) (x₀ : Fin k → R) :
    Matrix (Fin p) (Fin k) R :=
  Matrix.of fun l j => g l j x₀

/-- **The Jacobian** of `f` at `x₀` (for `p = k`): the determinant of the Jacobian matrix. -/
def jacobian {k : ℕ} (g : Fin k → Fin k → (Fin k → R) → R) (x₀ : Fin k → R) : R :=
  (jacobianMatrix g x₀).det

/-! ### Squared-norm toolkit -/

omit [IsRealClosed R] in
theorem abs_le_of_sq_le_sq {a b : R} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  nlinarith [sq_abs a, abs_nonneg a]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanNormSq_smul {k : ℕ} (a : R) (w : Fin k → R) :
    euclideanNormSq (a • w) = a ^ 2 * euclideanNormSq w := by
  simp only [euclideanNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

omit [IsRealClosed R] in
theorem sq_coord_le_normSq {k : ℕ} (w : Fin k → R) (j : Fin k) :
    w j ^ 2 ≤ euclideanNormSq w :=
  Finset.single_le_sum (fun i _ => sq_nonneg (w i)) (Finset.mem_univ j)

omit [IsRealClosed R] in
theorem euclideanNormSq_pos_of_ne {k : ℕ} {u v : Fin k → R} (h : u ≠ v) :
    0 < euclideanNormSq (u - v) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have h1 : 0 < (u - v) j ^ 2 := by
    have : (u - v) j ≠ 0 := sub_ne_zero.mpr hj
    positivity
  exact lt_of_lt_of_le h1 (sq_coord_le_normSq _ j)

theorem euclideanNorm_lt_iff {k : ℕ} {w : Fin k → R} {r : R} (hr : 0 < r) :
    euclideanNorm w < r ↔ euclideanNormSq w < r ^ 2 := by
  rw [← euclideanNorm_sq]
  constructor
  · intro h
    have h0 := euclideanNorm_nonneg w
    nlinarith
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith

theorem euclideanNorm_pos_of_ne {k : ℕ} {u v : Fin k → R} (h : u ≠ v) :
    0 < euclideanNorm (u - v) := by
  have h1 := euclideanNormSq_pos_of_ne h
  have h2 := euclideanNorm_nonneg (u - v)
  rcases h2.lt_or_eq with h3 | h3
  · exact h3
  · exfalso
    have := euclideanNorm_sq (u - v)
    rw [← h3] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    rw [← this] at h1
    exact lt_irrefl 0 h1

/-! ### Scalar derivative consequences -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem LimitAtInR.mono {g : R → R} {M N : Set R} {x₀ y₀ : R} (hMN : N ⊆ M)
    (h : LimitAtInR g M x₀ y₀) : LimitAtInR g N x₀ y₀ := fun r hr =>
  let ⟨δ, hδ, hb⟩ := h r hr
  ⟨δ, hδ, fun t ht => hb t (hMN ht)⟩

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem HasDerivAtIn.mono {g : R → R} {M N : Set R} {x₀ d : R} (hMN : N ⊆ M)
    (h : HasDerivAtIn g M x₀ d) : HasDerivAtIn g N x₀ d :=
  LimitAtInR.mono hMN h

omit [IsRealClosed R] in
/-- **Differentiability implies continuity** (within the same set): the function values
converge to `g x₀` along `M`. -/
theorem HasDerivAtIn.limitAtInR_self {g : R → R} {M : Set R} {x₀ d : R}
    (h : HasDerivAtIn g M x₀ d) : LimitAtInR g M x₀ (g x₀) := by
  intro r hr
  obtain ⟨δ₁, hδ₁, hb⟩ := h 1 one_pos
  have hd1 : 0 < |d| + 1 := by positivity
  refine ⟨min δ₁ (r / (|d| + 1)), lt_min hδ₁ (by positivity), fun t htM htne htδ => ?_⟩
  have hq := hb t htM htne (htδ.trans_le (min_le_left _ _))
  have hts : t - x₀ ≠ 0 := sub_ne_zero.mpr htne
  have hval : g t - g x₀ = (g t - g x₀) / (t - x₀) * (t - x₀) := by
    field_simp
  have habs := abs_lt.mp hq
  have hqabs : |(g t - g x₀) / (t - x₀)| ≤ |d| + 1 :=
    abs_le.mpr ⟨by linarith [neg_abs_le d, habs.1], by linarith [le_abs_self d, habs.2]⟩
  have htr : |t - x₀| < r / (|d| + 1) := htδ.trans_le (min_le_right _ _)
  calc |g t - g x₀| = |(g t - g x₀) / (t - x₀)| * |t - x₀| := by
        rw [← abs_mul, ← hval]
    _ ≤ (|d| + 1) * |t - x₀| := by
        exact mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
    _ < (|d| + 1) * (r / (|d| + 1)) := by
        exact mul_lt_mul_of_pos_left htr hd1
    _ = r := by field_simp

/-- The scalar-to-line continuity bridge on a closed interval: pointwise scalar limits give
`ContinuousOn` for the `constPt`-composite. -/
theorem continuousOn_constPt_slice {h : R → R} {a b : R}
    (hlim : ∀ s, a ≤ s → s ≤ b → LimitAtInR h (Set.Icc a b) s (h s)) :
    ContinuousOn (fun w : Fin 1 → R => constPt (h (w 0)))
      (Set.Icc (constPt a) (constPt b)) := by
  rw [continuousOn_iff_ball]
  intro y hy r hr
  have hy' := mem_Icc_fin_one.mp hy
  obtain ⟨δ, hδ, hb⟩ := hlim (y 0) hy'.1 hy'.2 r hr
  refine ⟨δ, hδ, fun z hz hnorm => ?_⟩
  have hz' := mem_Icc_fin_one.mp hz
  have h1 : euclideanNorm (z - y) = |z 0 - y 0| := by
    rw [euclideanNorm_fin_one]
    rfl
  have h2 : euclideanNorm (constPt (h (z 0)) - constPt (h (y 0)))
      = |h (z 0) - h (y 0)| := by
    rw [euclideanNorm_fin_one]
    rfl
  show euclideanNorm (constPt (h (z 0)) - constPt (h (y 0))) < r
  rw [h2]
  rcases eq_or_ne (z 0) (y 0) with heq | hne
  · rw [heq, sub_self, abs_zero]
    exact hr
  · exact hb (z 0) ⟨hz'.1, hz'.2⟩ hne (by rw [← h1]; exact hnorm)

/-! ### The Mean Value Theorem along a coordinate slice -/

omit [IsRealClosed R] in
theorem sq_sub_le_of_between {s e t : R} (h1 : min s e ≤ t) (h2 : t ≤ max s e) :
    (t - s) ^ 2 ≤ (e - s) ^ 2 := by
  rcases le_total s e with hse | hse
  · rw [min_eq_left hse] at h1
    rw [max_eq_right hse] at h2
    nlinarith
  · rw [min_eq_right hse] at h1
    rw [max_eq_left hse] at h2
    nlinarith

/-- **The MVT along the `j`-th coordinate slice** (Exercise 3.4, applied to the slice): if
`c` is semialgebraic on `U`, has `j`-th partial derivative `gj` on `U`, and the coordinate
segment from `s` to `e` through `v` lies in `U`, then the increment of `c` along it is
`gj` at an intermediate point times the increment of the coordinate. -/
theorem exists_slice_mvt {k : ℕ} {U : Set (Fin k → R)} {c gj : (Fin k → R) → R} {j : Fin k}
    (hSc : IsSemialgebraicFunction U (scalarFun c))
    (hdiff : ∀ x ∈ U, HasPartialDerivAtIn c U j x (gj x))
    (v : Fin k → R) (s e : R)
    (hseg : ∀ t, min s e ≤ t → t ≤ max s e → Function.update v j t ∈ U) :
    ∃ ξ, min s e ≤ ξ ∧ ξ ≤ max s e ∧
      c (Function.update v j e) - c (Function.update v j s)
        = gj (Function.update v j ξ) * (e - s) := by
  -- the strict case `a < b`, stated symmetrically in the endpoints
  have key : ∀ a b : R, a < b → (∀ t, a ≤ t → t ≤ b → Function.update v j t ∈ U) →
      ∃ ξ, a ≤ ξ ∧ ξ ≤ b ∧
        c (Function.update v j b) - c (Function.update v j a)
          = gj (Function.update v j ξ) * (b - a) := by
    intro a b hab hseg'
    have hupd : ∀ u, a ≤ u → u ≤ b →
        HasDerivAtIn (fun t => c (Function.update v j t))
          {t : R | Function.update v j t ∈ U} u (gj (Function.update v j u)) := by
      intro u hau hub
      have hu : Function.update v j u ∈ U := hseg' u hau hub
      have h := hdiff _ hu
      rw [HasPartialDerivAtIn] at h
      simp only [Function.update_idem, Function.update_self] at h
      exact h
    have hsub : Set.Icc a b ⊆ {t : R | Function.update v j t ∈ U} :=
      fun t ht => hseg' t ht.1 ht.2
    -- semialgebraicity of the slice
    have hSσ : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b))
        (fun w : Fin 1 → R => constPt (c (Function.update v j (w 0)))) := by
      haveI : Nonempty (Fin k) := ⟨j⟩
      have humap : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b))
          (fun w : Fin 1 → R => Function.update v j (w 0)) := by
        refine isSemialgebraicFunction_of_coords fun idx => ?_
        have hcoord : scalarFun (fun w : Fin 1 → R => Function.update v j (w 0) idx)
            = polyFun (if idx = j then (X 0 : MvPolynomial (Fin 1) R) else C (v idx)) := by
          funext w m
          by_cases hidx : idx = j
          · simp [scalarFun, polyFun, constPt, hidx, Function.update_self]
          · simp [scalarFun, polyFun, constPt, Function.update_of_ne hidx, if_neg hidx]
        show IsSemialgebraicFunction _
          (scalarFun (fun w : Fin 1 → R => Function.update v j (w 0) idx))
        rw [hcoord]
        exact polyFun_isSemialgebraicFunction_on (isSemialgebraicSet_Icc a b) _
      have hmaps : Set.MapsTo (fun w : Fin 1 → R => Function.update v j (w 0))
          (Set.Icc (constPt a) (constPt b)) U := by
        intro w hw
        have hw' := mem_Icc_fin_one.mp hw
        exact hseg' (w 0) hw'.1 hw'.2
      exact proposition_2_84 humap hSc hmaps
    -- continuity of the slice on `[a, b]`
    have hcontσ : ContinuousOn
        (fun w : Fin 1 → R => constPt (c (Function.update v j (w 0))))
        (Set.Icc (constPt a) (constPt b)) := by
      refine continuousOn_constPt_slice
        (h := fun t => c (Function.update v j t)) fun u hau hub => ?_
      exact ((hupd u hau hub).mono hsub).limitAtInR_self
    -- differentiability of the slice on `(a, b)`
    have hdiffσ : ∀ u, a < u → u < b →
        HasDerivAtIn (fun t =>
            (fun w : Fin 1 → R => constPt (c (Function.update v j (w 0)))) (constPt t) 0)
          (Set.Ioo a b) u (gj (Function.update v j u)) := by
      intro u hau hub
      have h := (hupd u hau.le hub.le).mono
        (fun t (ht : t ∈ Set.Ioo a b) => hsub ⟨ht.1.le, ht.2.le⟩)
      exact h
    obtain ⟨ξ, haξ, hξb, hξ⟩ := exercise_3_4_mvt hab hSσ hcontσ hdiffσ
    refine ⟨ξ, haξ.le, hξb.le, ?_⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    exact ((eq_div_iff hba).mp hξ).symm
  rcases lt_trichotomy s e with hse | hse | hse
  · obtain ⟨ξ, h1, h2, h3⟩ := key s e hse (by
      intro t h1 h2
      exact hseg t (by rw [min_eq_left hse.le]; exact h1)
        (by rw [max_eq_right hse.le]; exact h2))
    exact ⟨ξ, by rw [min_eq_left hse.le]; exact h1,
      by rw [max_eq_right hse.le]; exact h2, h3⟩
  · subst hse
    exact ⟨s, (min_self s).le, (max_self s).ge, by rw [sub_self, sub_self, mul_zero]⟩
  · obtain ⟨ξ, h1, h2, h3⟩ := key e s hse (by
      intro t h1 h2
      exact hseg t (by rw [min_eq_right hse.le]; exact h1)
        (by rw [max_eq_left hse.le]; exact h2))
    refine ⟨ξ, by rw [min_eq_right hse.le]; exact h1,
      by rw [max_eq_left hse.le]; exact h2, ?_⟩
    linarith [h3]

/-! ### First-order approximation -/

/-- The coordinate chain from `x₀` to `x`: `vchain x₀ x m` agrees with `x` on coordinates
`< m` and with `x₀` on the rest. -/
def vchain {k : ℕ} (x₀ x : Fin k → R) (m : ℕ) : Fin k → R :=
  fun i => if (i : ℕ) < m then x i else x₀ i

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem vchain_zero {k : ℕ} [Field R] (x₀ x : Fin k → R) : vchain x₀ x 0 = x₀ :=
  funext fun i => by simp [vchain]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem vchain_last {k : ℕ} [Field R] (x₀ x : Fin k → R) : vchain x₀ x k = x :=
  funext fun i => by simp [vchain, i.isLt]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem vchain_succ {k : ℕ} [Field R] (x₀ x : Fin k → R) {m : ℕ} (hm : m < k) :
    Function.update (vchain x₀ x m) ⟨m, hm⟩ (x ⟨m, hm⟩) = vchain x₀ x (m + 1) := by
  funext i
  rcases eq_or_ne i ⟨m, hm⟩ with rfl | hne
  · rw [Function.update_self]
    show x ⟨m, hm⟩ = if m < m + 1 then x ⟨m, hm⟩ else x₀ ⟨m, hm⟩
    rw [if_pos (Nat.lt_succ_self m)]
  · rw [Function.update_of_ne hne]
    have : (i : ℕ) ≠ m := fun h => hne (Fin.ext h)
    simp only [vchain]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem vchain_self {k : ℕ} [Field R] (x₀ x : Fin k → R) {m : ℕ} (hm : m < k) :
    Function.update (vchain x₀ x m) ⟨m, hm⟩ (x₀ ⟨m, hm⟩) = vchain x₀ x m := by
  refine Function.update_eq_self_iff.mpr ?_
  show x₀ ⟨m, hm⟩ = if m < m then x ⟨m, hm⟩ else x₀ ⟨m, hm⟩
  rw [if_neg (lt_irrefl m)]

omit [IsRealClosed R] in
/-- Points obtained by updating a chain stage inside the coordinate box between `x₀` and
`x` stay normSq-dominated by `x − x₀`. -/
theorem vchain_update_normSq_le {k : ℕ} (x₀ x : Fin k → R) {m : ℕ} {jF : Fin k} {t : R}
    (h1 : min (x₀ jF) (x jF) ≤ t) (h2 : t ≤ max (x₀ jF) (x jF)) :
    euclideanNormSq (Function.update (vchain x₀ x m) jF t - x₀)
      ≤ euclideanNormSq (x - x₀) := by
  rw [euclideanNormSq, euclideanNormSq]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases eq_or_ne i jF with rfl | hne
  · rw [Pi.sub_apply, Function.update_self, Pi.sub_apply]
    exact sq_sub_le_of_between h1 h2
  · rw [Pi.sub_apply, Function.update_of_ne hne, Pi.sub_apply]
    simp only [vchain]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [if_pos h]
    · rw [if_neg (by omega), sub_self]
      simpa using sq_nonneg (x i - x₀ i)

/-- **BPR §3.5 (unnumbered): first-order approximation.** Following the usual arguments
from a calculus course: if `f` is semialgebraic (coordinatewise) on the open `U` and its
partial derivatives `g l j = ∂f_l/∂X_j` exist on `U` and are continuous, then

  `f(x) − f(x₀) − df(x₀)(x − x₀) = o(‖x − x₀‖)`  at every `x₀ ∈ U`.

The proof moves from `x₀` to `x` one coordinate at a time; each increment is controlled by
the Mean Value Theorem (Exercise 3.4, where semialgebraicity enters), and continuity of the
partials bounds the error. -/
theorem isLittleO_sub_totalDeriv {k p : ℕ} {U : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin p → R)} {g : Fin p → Fin k → (Fin k → R) → R}
    (hUopen : IsOpen U)
    (hSf : ∀ l, IsSemialgebraicFunction U (scalarFun (fun y => f y l)))
    (hdiff : ∀ l j, ∀ x ∈ U, HasPartialDerivAtIn (fun y => f y l) U j x (g l j x))
    (hcont : ∀ l j, ContinuousOn (scalarFun (g l j)) U)
    {x₀ : Fin k → R} (hx₀ : x₀ ∈ U) :
    IsLittleO (fun x => f x - f x₀ - totalDeriv g x₀ (x - x₀)) U x₀ := by
  classical
  intro r hr
  -- degenerate dimensions
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact ⟨1, one_pos, fun x hxU hne _ => absurd (funext fun i => i.elim0) hne⟩
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    refine ⟨1, one_pos, fun x hxU hne hxδ => ?_⟩
    have hz : euclideanNormSq ((euclideanNorm (x - x₀))⁻¹ •
        (f x - f x₀ - totalDeriv g x₀ (x - x₀)) - 0) = 0 := by
      simp [euclideanNormSq]
    show euclideanNorm _ < r
    rw [euclideanNorm, hz, sqrt_zero]
    exact hr
  -- a ball inside `U`, and the tolerance for the partials
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff_ball_self.mp hUopen x₀ hx₀
  set P : R := (p : R) with hPd
  set K : R := (k : R) with hKd
  have hP1 : (1 : R) ≤ P := by rw [hPd]; exact_mod_cast hppos
  have hK1 : (1 : R) ≤ K := by rw [hKd]; exact_mod_cast hkpos
  set ε : R := r / (P * K + 1) with hεd
  have hPK : (0 : R) < P * K + 1 := by nlinarith
  have hε : 0 < ε := div_pos hr hPK
  -- a continuity radius for each partial derivative
  have hδc : ∀ (l : Fin p) (j : Fin k), ∃ δ, 0 < δ ∧ ∀ y ∈ U,
      euclideanNormSq (y - x₀) < δ ^ 2 → |g l j y - g l j x₀| < ε := by
    intro l j
    obtain ⟨δ, hδ, hb⟩ := (continuousOn_iff_ball.mp (hcont l j)) x₀ hx₀ ε hε
    refine ⟨δ, hδ, fun y hyU hy => ?_⟩
    have hy' := hb y hyU ((euclideanNorm_lt_iff hδ).mpr hy)
    have heq : euclideanNorm (scalarFun (g l j) y - scalarFun (g l j) x₀)
        = |g l j y - g l j x₀| := by
      rw [euclideanNorm_fin_one]
      rfl
    rwa [heq] at hy'
  choose δc hδcpos hδcball using hδc
  haveI : Nonempty (Fin p) := ⟨⟨0, hppos⟩⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
  set δ₀ : R := Finset.univ.inf' Finset.univ_nonempty
    (fun lj : Fin p × Fin k => δc lj.1 lj.2) with hδ₀d
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀d, Finset.lt_inf'_iff]
    exact fun lj _ => hδcpos lj.1 lj.2
  refine ⟨min ρ δ₀, lt_min hρ hδ₀pos, fun x hxU hne hxδ => ?_⟩
  set N : R := euclideanNorm (x - x₀) with hNd
  have hN : 0 < N := euclideanNorm_pos_of_ne hne
  have hN2 : N ^ 2 = euclideanNormSq (x - x₀) := euclideanNorm_sq _
  have hSρ : euclideanNormSq (x - x₀) < ρ ^ 2 :=
    (euclideanNorm_lt_iff hρ).mp (lt_of_lt_of_le hxδ (min_le_left _ _))
  have hSδc : ∀ (l : Fin p) (j : Fin k),
      euclideanNormSq (x - x₀) < δc l j ^ 2 := by
    intro l j
    refine (euclideanNorm_lt_iff (hδcpos l j)).mp
      (lt_of_lt_of_le hxδ ((min_le_right _ _).trans ?_))
    rw [hδ₀d]
    exact Finset.inf'_le _ (Finset.mem_univ (l, j))
  -- points of the coordinate box lie in `U` and within all continuity radii
  have hboxU : ∀ (m : ℕ) (jF : Fin k) (t : R),
      min (x₀ jF) (x jF) ≤ t → t ≤ max (x₀ jF) (x jF) →
      Function.update (vchain x₀ x m) jF t ∈ U := by
    intro m jF t h1 h2
    refine hball ?_
    rw [mem_openBall]
    exact lt_of_le_of_lt (vchain_update_normSq_le x₀ x h1 h2) hSρ
  -- the goal, in squared form
  show euclideanNorm (N⁻¹ • (f x - f x₀ - totalDeriv g x₀ (x - x₀)) - 0) < r
  rw [sub_zero, euclideanNorm_lt_iff hr, euclideanNormSq_smul, inv_pow]
  have hN2pos : (0 : R) < N ^ 2 := by positivity
  suffices hgoal : euclideanNormSq (f x - f x₀ - totalDeriv g x₀ (x - x₀))
      < r ^ 2 * N ^ 2 by
    calc (N ^ 2)⁻¹ * euclideanNormSq (f x - f x₀ - totalDeriv g x₀ (x - x₀))
        < (N ^ 2)⁻¹ * (r ^ 2 * N ^ 2) :=
          mul_lt_mul_of_pos_left hgoal (by positivity)
      _ = r ^ 2 := by field_simp
  -- the per-coordinate bound
  have key : ∀ l : Fin p, |f x l - f x₀ l - totalDeriv g x₀ (x - x₀) l| ≤ K * ε * N := by
    intro l
    set cl : (Fin k → R) → R := fun y => f y l with hcld
    -- the ℕ-indexed summands
    set G : ℕ → R := fun jn => if h : jn < k then
      g l ⟨jn, h⟩ x₀ * (x ⟨jn, h⟩ - x₀ ⟨jn, h⟩) else 0 with hGd
    have hTD : totalDeriv g x₀ (x - x₀) l = ∑ jn ∈ Finset.range k, G jn := by
      rw [totalDeriv]
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hGd]
      rw [dif_pos j.isLt]
      rfl
    have htele : f x l - f x₀ l
        = ∑ jn ∈ Finset.range k, (cl (vchain x₀ x (jn + 1)) - cl (vchain x₀ x jn)) := by
      rw [Finset.sum_range_sub (fun m => cl (vchain x₀ x m)) k]
      rw [vchain_zero, vchain_last]
    have hsplit : f x l - f x₀ l - totalDeriv g x₀ (x - x₀) l
        = ∑ jn ∈ Finset.range k,
            ((cl (vchain x₀ x (jn + 1)) - cl (vchain x₀ x jn)) - G jn) := by
      rw [htele, hTD, ← Finset.sum_sub_distrib]
    rw [hsplit]
    calc |∑ jn ∈ Finset.range k,
          ((cl (vchain x₀ x (jn + 1)) - cl (vchain x₀ x jn)) - G jn)|
        ≤ ∑ jn ∈ Finset.range k,
          |(cl (vchain x₀ x (jn + 1)) - cl (vchain x₀ x jn)) - G jn| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _jn ∈ Finset.range k, ε * N := by
          refine Finset.sum_le_sum fun jn hjn => ?_
          have hjnk : jn < k := Finset.mem_range.mp hjn
          set jF : Fin k := ⟨jn, hjnk⟩ with hjFd
          -- the MVT along coordinate `jF`
          obtain ⟨ξ, hξ1, hξ2, hξ⟩ := exists_slice_mvt (hSf l)
            (fun y hy => hdiff l jF y hy) (vchain x₀ x jn) (x₀ jF) (x jF)
            (fun t h1 h2 => hboxU jn jF t h1 h2)
          rw [vchain_succ x₀ x hjnk, vchain_self x₀ x hjnk] at hξ
          -- the intermediate point obeys the continuity bound
          have hwU : Function.update (vchain x₀ x jn) jF ξ ∈ U :=
            hboxU jn jF ξ hξ1 hξ2
          have hwnear : |g l jF (Function.update (vchain x₀ x jn) jF ξ) - g l jF x₀|
              < ε := by
            refine hδcball l jF _ hwU ?_
            exact lt_of_le_of_lt (vchain_update_normSq_le x₀ x hξ1 hξ2) (hSδc l jF)
          have hG : G jn = g l jF x₀ * (x jF - x₀ jF) := by
            simp only [hGd]
            rw [dif_pos hjnk]
          have hterm : (cl (vchain x₀ x (jn + 1)) - cl (vchain x₀ x jn)) - G jn
              = (g l jF (Function.update (vchain x₀ x jn) jF ξ) - g l jF x₀)
                * (x jF - x₀ jF) := by
            rw [hG, hξ]
            ring
          rw [hterm, abs_mul]
          have hΔ : |x jF - x₀ jF| ≤ N := by
            refine abs_le_of_sq_le_sq ?_ hN.le
            rw [hN2]
            exact sq_coord_le_normSq (x - x₀) jF
          exact mul_le_mul hwnear.le hΔ (abs_nonneg _) hε.le
      _ = K * ε * N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKd]
          ring
  -- assemble the squared bound
  have hsum : euclideanNormSq (f x - f x₀ - totalDeriv g x₀ (x - x₀))
      ≤ P * (K * ε * N) ^ 2 := by
    rw [euclideanNormSq]
    calc ∑ l, ((f x - f x₀ - totalDeriv g x₀ (x - x₀)) l) ^ 2
        ≤ ∑ _l : Fin p, (K * ε * N) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          have hl := key l
          have habs : ((f x - f x₀ - totalDeriv g x₀ (x - x₀)) l) ^ 2
              = |f x l - f x₀ l - totalDeriv g x₀ (x - x₀) l| ^ 2 := by
            rw [sq_abs]
            rfl
          rw [habs]
          nlinarith [hl, abs_nonneg (f x l - f x₀ l - totalDeriv g x₀ (x - x₀) l)]
        _ = P * (K * ε * N) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hPd]
  refine lt_of_le_of_lt hsum ?_
  -- `P K² ε² < r²`, then multiply through by `N² > 0`
  have h0P : (0 : R) ≤ P := le_trans zero_le_one hP1
  have h0K : (0 : R) ≤ K := le_trans zero_le_one hK1
  have hPKε : P * K ^ 2 * ε ^ 2 < r ^ 2 := by
    rw [hεd, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    have hPP : P * K ^ 2 ≤ (P * K) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg h0P (sq_nonneg K)) (sub_nonneg.mpr hP1)]
    have h2 : P * K ^ 2 < (P * K + 1) ^ 2 := by
      nlinarith [hPP, mul_nonneg h0P h0K]
    nlinarith [mul_lt_mul_of_pos_left h2 (mul_pos hr hr)]
  have hrearrange : P * (K * ε * N) ^ 2 = (P * K ^ 2 * ε ^ 2) * N ^ 2 := by ring
  rw [hrearrange]
  exact mul_lt_mul_of_pos_right hPKε hN2pos

end Azurite.BPR
