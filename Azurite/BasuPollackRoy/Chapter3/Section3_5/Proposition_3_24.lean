import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_23

/-! # BPR §3.5, Proposition 3.24 — the Inverse Function Theorem

**Let `U′` be a semialgebraic open neighborhood of the origin of `R^k`,
`f ∈ 𝒮^ℓ(U′, R^k)`, `ℓ ≥ 1`, with `f(0) = 0` and `df(0)` invertible. Then there exist
semialgebraic open neighborhoods `U, V` of `0`, `U ⊆ U′`, such that `f|_U` is a
homeomorphism onto `V` and `(f|_U)⁻¹ ∈ 𝒮^ℓ(V, U)`.**

This file proves the theorem through the homeomorphism and the `𝒮⁰` (semialgebraic
continuous) inverse; BPR's final sentence `d(f⁻¹)(x) = (df(f⁻¹(x)))⁻¹` and the
`𝒮^ℓ`-smoothness of the inverse are the separate result `isSFunction_inverse` /
`proposition_3_24_sClass` (`InverseSmoothness.lean`), for which this theorem's conclusion
exposes the pointwise invertibility of `df` on `U` and the Lipschitz bound on the inverse.
Instead of normalizing `df(0)` to the identity, the proof carries `A = df(0)` through the
estimates, using the lower bound `m‖v‖ ≤ ‖A·v‖` furnished by invertibility
(`exists_mulVec_lower_bound`):

* a radius where all entries of `df(x) − A` are small makes `‖df(x) − A‖ ≤ ε` via the
  Frobenius bound (`opNorm_le_of_entries_sq_le`), with `ε := min(m_A, m_{Aᵀ})/2`;
* Proposition 3.23 applied to `g = f − A·x` on segments in the ball gives
  `‖f(x) − f(y) − A(x − y)‖ ≤ ε ‖x − y‖`, hence the two-sided bounds and injectivity;
* the same smallness makes every `df(x)ᵀ = Aᵀ + (df(x) − A)ᵀ` injective by perturbation
  (no determinant continuity needed), which is exactly what the vanishing-gradient step
  consumes;
* for `‖y⁰‖` small, `h(x) = ‖f(x) − y⁰‖²` attains its minimum on the closed ball
  (the general extreme-value lemma), not on the boundary, so at an interior point all
  partials of `h` vanish: `(f(x⁰) − y⁰) ᵥ* df(x⁰) = 0`, and injectivity of `df(x⁰)ᵀ`
  forces `f(x⁰) = y⁰`;
* `V` is a small ball, `U = B ∩ f⁻¹(V)`, and the inverse is `2/m_A`-Lipschitz, hence
  continuous, and semialgebraic since its graph is the transpose of the graph of `f|_U`. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Ball and segment helpers -/

theorem isClosed_closedBall {k : ℕ} (x : Fin k → R) (r : R) :
    IsClosed (closedBall x r) := by
  rw [isClosed_iff, isOpen_iff]
  intro y hy
  rw [Set.mem_compl_iff, mem_closedBall, not_le] at hy
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  set N : R := euclideanNorm (y - x) with hNd
  have hN2 : N ^ 2 = euclideanNormSq (y - x) := euclideanNorm_sq _
  have hN0' : 0 ≤ N := euclideanNorm_nonneg _
  have hNr : |r| < N := by
    have h1 : |r| ^ 2 < N ^ 2 := by rw [sq_abs, hN2]; exact hy
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [abs_nonneg r]
  have hN0 : 0 < N := lt_of_le_of_lt (abs_nonneg r) hNr
  refine ⟨y, N - |r|, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
  rw [mem_openBall] at hz
  have hzN : euclideanNorm (z - y) < N - |r| := by
    rw [euclideanNorm_lt_iff (by linarith)]
    exact hz
  rw [Set.mem_compl_iff, mem_closedBall, not_le]
  -- reverse triangle: `‖z − x‖ ≥ ‖y − x‖ − ‖z − y‖ > |r|`
  have htri : euclideanNorm (y - x) ≤ euclideanNorm (y - z) + euclideanNorm (z - x) :=
    euclideanNorm_sub_le y z x
  have hsym : euclideanNorm (y - z) = euclideanNorm (z - y) := euclideanNorm_sub_symm y z
  have hzx : |r| < euclideanNorm (z - x) := by
    rw [hsym] at htri
    linarith
  have := sq_lt_sq' (by linarith [abs_nonneg r, euclideanNorm_nonneg (z - x)]) hzx
  calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    _ < euclideanNorm (z - x) ^ 2 := by nlinarith [abs_nonneg r]
    _ = euclideanNormSq (z - x) := euclideanNorm_sq _

theorem isBoundedSet_closedBall {k : ℕ} (r : R) :
    IsBoundedSet (closedBall (0 : Fin k → R) r) := by
  refine ⟨|r| + 1, by positivity, fun y hy => ?_⟩
  rw [mem_closedBall, sub_zero] at hy
  rw [mem_closedBall, sub_zero]
  nlinarith [sq_abs r, abs_nonneg r]

/-- Open balls about the origin are convex along `segPath`. -/
theorem segPath_mem_openBall {k : ℕ} {x y : Fin k → R} {r : R} (hr : 0 < r)
    (hx : x ∈ openBall (0 : Fin k → R) r) (hy : y ∈ openBall (0 : Fin k → R) r)
    {t : R} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segPath x y t ∈ openBall (0 : Fin k → R) r := by
  have hxn : euclideanNorm x < r := by
    rw [euclideanNorm_lt_iff hr]
    have := mem_openBall.mp hx
    rwa [sub_zero] at this
  have hyn : euclideanNorm y < r := by
    rw [euclideanNorm_lt_iff hr]
    have := mem_openBall.mp hy
    rwa [sub_zero] at this
  suffices hlt : euclideanNorm (segPath x y t) < r by
    rw [mem_openBall, sub_zero]
    exact (euclideanNorm_lt_iff hr).mp hlt
  have hsplit : segPath x y t = (1 - t) • x + t • y := by
    funext i
    simp only [segPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit]
  calc euclideanNorm ((1 - t) • x + t • y)
      ≤ euclideanNorm ((1 - t) • x) + euclideanNorm (t • y) := euclideanNorm_add_le _ _
    _ = (1 - t) * euclideanNorm x + t * euclideanNorm y := by
        rw [euclideanNorm_smul, euclideanNorm_smul, abs_of_nonneg (by linarith),
          abs_of_nonneg ht0]
    _ < r := by
        rcases eq_or_lt_of_le ht1 with rfl | ht1'
        · simpa using hyn
        · nlinarith [euclideanNorm_nonneg x, euclideanNorm_nonneg y]

/-! ### Matrix helpers: Frobenius bound, lower bound, transpose injectivity -/

omit [IsRealClosed R] in
/-- The squared Frobenius bound: `‖B·v‖² ≤ (∑ entries²) ‖v‖²` (Cauchy–Schwarz per row). -/
theorem normSq_mulVec_le_frobenius {k p : ℕ} (B : Matrix (Fin p) (Fin k) R)
    (v : Fin k → R) :
    euclideanNormSq (B.mulVec v)
      ≤ (∑ l, ∑ j, B l j ^ 2) * euclideanNormSq v := by
  rw [euclideanNormSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  have h := euclideanInner_sq_le (fun j => B l j) v
  have hexp : (B.mulVec v) l = euclideanInner (fun j => B l j) v := rfl
  rw [hexp]
  calc euclideanInner (fun j => B l j) v ^ 2
      ≤ euclideanNormSq (fun j => B l j) * euclideanNormSq v := h
    _ = (∑ j, B l j ^ 2) * euclideanNormSq v := by rw [euclideanNormSq]

/-- If the entries of `B` are square-summed below `ε²`, then `‖B‖ ≤ ε`. -/
theorem opNorm_le_of_entries_sq_le {k p : ℕ} (hk : 0 < k) {B : Matrix (Fin p) (Fin k) R}
    {ε : R} (hε : 0 ≤ ε) (h : (∑ l, ∑ j, B l j ^ 2) ≤ ε ^ 2) : opNorm B ≤ ε := by
  obtain ⟨⟨v₀, hv₀, hval⟩, -⟩ := opNorm_isGreatest hk B
  rw [hval]
  rw [euclideanNorm_le_iff_normSq_le hε]
  calc euclideanNormSq (B.mulVec v₀)
      ≤ (∑ l, ∑ j, B l j ^ 2) * euclideanNormSq v₀ := normSq_mulVec_le_frobenius B v₀
    _ = ∑ l, ∑ j, B l j ^ 2 := by rw [hv₀, mul_one]
    _ ≤ ε ^ 2 := h

/-- An invertible matrix is bounded below: there is `m > 0` with `m‖v‖ ≤ ‖A·v‖`. -/
theorem exists_mulVec_lower_bound {k : ℕ} (hk : 0 < k) {A : Matrix (Fin k) (Fin k) R}
    (hA : IsUnit A.det) : ∃ m, 0 < m ∧ ∀ v, m * euclideanNorm v ≤
      euclideanNorm (A.mulVec v) := by
  have hop : 0 < opNorm A⁻¹ + 1 := by
    have := opNorm_nonneg hk A⁻¹
    linarith
  refine ⟨(opNorm A⁻¹ + 1)⁻¹, by positivity, fun v => ?_⟩
  have hAv : A⁻¹.mulVec (A.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  have h1 : euclideanNorm v ≤ opNorm A⁻¹ * euclideanNorm (A.mulVec v) := by
    calc euclideanNorm v = euclideanNorm (A⁻¹.mulVec (A.mulVec v)) := by rw [hAv]
      _ ≤ opNorm A⁻¹ * euclideanNorm (A.mulVec v) := norm_mulVec_le hk _ _
  rw [inv_mul_le_iff₀ hop]
  calc euclideanNorm v ≤ opNorm A⁻¹ * euclideanNorm (A.mulVec v) := h1
    _ ≤ (opNorm A⁻¹ + 1) * euclideanNorm (A.mulVec v) := by
        refine mul_le_mul_of_nonneg_right (by linarith) (euclideanNorm_nonneg _)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `v ᵥ* M` is `Mᵀ.mulVec v`. -/
theorem vecMul_eq_mulVec_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (v : Fin k → R) : Matrix.vecMul v M = M.transpose.mulVec v := by
  funext i
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Perturbation injectivity: if `m‖v‖ ≤ ‖A·v‖` and `‖E‖ ≤ ε < m`, then
`(A + E)·v = 0` forces `v = 0`. -/
theorem mulVec_add_eq_zero {k : ℕ} (hk : 0 < k) {A E : Matrix (Fin k) (Fin k) R}
    {m ε : R} (hlow : ∀ v, m * euclideanNorm v ≤ euclideanNorm (A.mulVec v))
    (hE : opNorm E ≤ ε) (hεm : ε < m) {v : Fin k → R}
    (h : (A + E).mulVec v = 0) : v = 0 := by
  by_contra hne
  have hv : 0 < euclideanNorm v := by
    have := euclideanNorm_pos_of_ne (u := v) (v := 0) hne
    rwa [sub_zero] at this
  have hAv : A.mulVec v = -(E.mulVec v) := by
    have hadd : A.mulVec v + E.mulVec v = 0 := by
      rw [← Matrix.add_mulVec]
      exact h
    funext i
    have := congrFun hadd i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.neg_apply]
    linarith
  have h1 : m * euclideanNorm v ≤ euclideanNorm (E.mulVec v) := by
    have h2 := hlow v
    rw [hAv] at h2
    have hneg : euclideanNorm (-(E.mulVec v)) = euclideanNorm (E.mulVec v) := by
      have : -(E.mulVec v) = (0 : Fin k → R) - E.mulVec v := by
        funext i
        simp
      rw [this, euclideanNorm_sub_symm, sub_zero]
    rwa [hneg] at h2
  have h2 : euclideanNorm (E.mulVec v) ≤ ε * euclideanNorm v :=
    le_trans (norm_mulVec_le hk E v)
      (mul_le_mul_of_nonneg_right hE (euclideanNorm_nonneg v))
  nlinarith

/-! ### Sum rule for partial derivatives over a `Finset` -/

omit [IsRealClosed R] in
theorem hasPartialDerivAtIn_sum {k : ℕ} {U : Set (Fin k → R)} {i : Fin k}
    {x : Fin k → R} {ι : Type*} (s : Finset ι) {c : ι → (Fin k → R) → R} {d : ι → R}
    (h : ∀ l ∈ s, HasPartialDerivAtIn (c l) U i x (d l)) :
    HasPartialDerivAtIn (fun z => ∑ l ∈ s, c l z) U i x (∑ l ∈ s, d l) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact hasPartialDerivAtIn_const 0 U i x
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact HasPartialDerivAtIn.add (h a (Finset.mem_cons_self a s))
      (ih fun l hl => h l (Finset.mem_cons_of_mem hl))

/-! ### Restriction of semialgebraic functions -/

omit [IsRealClosed R] in
/-- A semialgebraic function on `S` is semialgebraic on a semialgebraic `T ⊆ S`. -/
theorem IsSemialgebraicFunction.mono {k ℓ : ℕ} {S T : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} (hf : IsSemialgebraicFunction S f)
    (hT : IsSemialgebraicSet T) (hTS : T ⊆ S) : IsSemialgebraicFunction T f := by
  show IsSemialgebraicSet (funGraph T f)
  have heq : funGraph T f = funGraph S f ∩ {z | z ∘ Fin.castAdd ℓ ∈ T} := by
    ext z
    rw [Set.mem_inter_iff, mem_funGraph, mem_funGraph, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hTS h1, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  rw [heq]
  exact hf.inter (IsSemialgebraicSet.comap _ hT)

/-! ### Coordinate-update norm splitting and affine derivatives -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanNormSq_update {k : ℕ} (z : Fin k → R) (i : Fin k) (t : R) :
    euclideanNormSq (Function.update z i t)
      = euclideanNormSq z - z i ^ 2 + t ^ 2 := by
  classical
  rw [euclideanNormSq, euclideanNormSq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => z j ^ 2) (Finset.mem_univ i)]
  rw [Function.update_self]
  have hsum : ∑ j ∈ Finset.univ.erase i, Function.update z i t j ^ 2
      = ∑ j ∈ Finset.univ.erase i, z j ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsum]
  ring

omit [IsRealClosed R] in
/-- The derivative of an affine scalar function. -/
theorem hasDerivAtIn_affine (a b : R) (M : Set R) (x₀ : R) :
    HasDerivAtIn (fun t => a * t + b) M x₀ a := by
  refine LimitAtInR.congr (g₁ := fun _ => a) ?_ (limitAtInR_const M x₀ a)
  intro t _ htne
  have hts : t - x₀ ≠ 0 := sub_ne_zero.mpr htne
  field_simp
  ring

/-- At an interior minimum of `z ↦ ∑ (f z − y⁰)²` on a closed ball inside the domain, the
gradient equations `∑_l (f_l − y⁰_l) ∂f_l/∂x_i = 0` hold (BPR's vanishing-partials step). -/
private theorem grad_eq_zero_at_interior_min {k : ℕ} {U' : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hdiff : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => f w l) U' j z (g l j z))
    {y0 zmin : Fin k → R} {rr : R}
    (hBsub : closedBall (0 : Fin k → R) rr ⊆ U')
    (hzminB : zmin ∈ closedBall (0 : Fin k → R) rr)
    (hzmin_int : euclideanNormSq zmin < rr ^ 2)
    (hmin : ∀ z ∈ closedBall (0 : Fin k → R) rr,
      (∑ l, (f zmin l - y0 l) * (f zmin l - y0 l))
        ≤ ∑ l, (f z l - y0 l) * (f z l - y0 l))
    (i : Fin k) : (∑ l, (f zmin l - y0 l) * g l i zmin) = 0 := by
  classical
  have hzminU' : zmin ∈ U' := hBsub hzminB
  -- partials of the components and of the squared objective
  have hcomp_pd : ∀ l, HasPartialDerivAtIn (fun z => f z l - y0 l) U' i zmin
      (g l i zmin) := by
    intro l
    have h1 := HasPartialDerivAtIn.add (hdiff l i zmin hzminU')
      (hasPartialDerivAtIn_const (-(y0 l)) U' i zmin)
    have heqf : (fun y => f y l + (fun _ : Fin k → R => -(y0 l)) y)
        = fun z => f z l - y0 l := by
      funext z
      show f z l + -(y0 l) = f z l - y0 l
      ring
    rw [heqf, add_zero] at h1
    exact h1
  have hsq_pd : ∀ l, HasPartialDerivAtIn
      (fun z => (f z l - y0 l) * (f z l - y0 l)) U' i zmin
      ((f zmin l - y0 l) * g l i zmin + (f zmin l - y0 l) * g l i zmin) := by
    intro l
    have h1 := HasPartialDerivAtIn.mul (hcomp_pd l) (hcomp_pd l)
    have h2 : Function.update zmin i (zmin i) = zmin := Function.update_eq_self i zmin
    rw [h2] at h1
    exact h1
  have hsum_pd : HasPartialDerivAtIn
      (fun z => ∑ l, (f z l - y0 l) * (f z l - y0 l)) U' i zmin
      (∑ l, ((f zmin l - y0 l) * g l i zmin
        + (f zmin l - y0 l) * g l i zmin)) :=
    hasPartialDerivAtIn_sum Finset.univ (fun l _ => hsq_pd l)
  -- the slice interval inside the closed ball
  set D : R := rr ^ 2 - euclideanNormSq zmin with hDd
  have hD : 0 < D := by rw [hDd]; linarith [hzmin_int]
  set ss : R := min 1 (D / (2 * |zmin i| + 2)) with hssd
  have hss : 0 < ss := lt_min one_pos (by positivity)
  have hss1 : ss ≤ 1 := min_le_left _ _
  have hss2 : ss * (2 * |zmin i| + 2) ≤ D := by
    have h1 : ss ≤ D / (2 * |zmin i| + 2) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    exact h1
  have hupd_mem : ∀ t, zmin i - ss < t → t < zmin i + ss →
      Function.update zmin i t ∈ closedBall (0 : Fin k → R) rr := by
    intro t ht1 ht2
    rw [mem_closedBall, sub_zero, euclideanNormSq_update]
    have habs : |t| ≤ |zmin i| + ss := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (zmin i)]
      · linarith [le_abs_self (zmin i)]
    have ht2' : t ^ 2 ≤ (|zmin i| + ss) ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t, abs_nonneg (zmin i)]
    have hsexp : (|zmin i| + ss) ^ 2 ≤ zmin i ^ 2 + D := by
      nlinarith [sq_abs (zmin i), abs_nonneg (zmin i)]
    rw [hDd] at hsexp
    linarith
  have hIoo_sub : Set.Ioo (zmin i - ss) (zmin i + ss)
      ⊆ {t | Function.update zmin i t ∈ U'} :=
    fun t ht => hBsub (hupd_mem t ht.1 ht.2)
  have hminIoo : ∀ t ∈ Set.Ioo (zmin i - ss) (zmin i + ss),
      (fun t => ∑ l, (f (Function.update zmin i t) l - y0 l)
        * (f (Function.update zmin i t) l - y0 l)) (zmin i)
        ≤ (fun t => ∑ l, (f (Function.update zmin i t) l - y0 l)
          * (f (Function.update zmin i t) l - y0 l)) t := by
    intro t ht
    show (∑ l, (f (Function.update zmin i (zmin i)) l - y0 l)
        * (f (Function.update zmin i (zmin i)) l - y0 l)) ≤ _
    rw [Function.update_eq_self]
    exact hmin _ (hupd_mem t ht.1 ht.2)
  have hd0 := HasDerivAtIn.eq_zero_of_interior_min
    (show zmin i - ss < zmin i by linarith)
    (show zmin i < zmin i + ss by linarith)
    hminIoo (HasDerivAtIn.mono hIoo_sub hsum_pd)
  have hsum2 : (∑ l, ((f zmin l - y0 l) * g l i zmin
      + (f zmin l - y0 l) * g l i zmin))
      = (∑ l, (f zmin l - y0 l) * g l i zmin)
        + ∑ l, (f zmin l - y0 l) * g l i zmin := by
    rw [← Finset.sum_add_distrib]
  rw [hsum2] at hd0
  linarith

/-! ### Proposition 3.24 -/

set_option maxHeartbeats 800000 in
/-- **BPR Proposition 3.24 (Inverse Function Theorem)** — existence, homeomorphism, and
semialgebraicity of the inverse. Let `U′` be a semialgebraic open neighborhood of the
origin of `R^k` and `f ∈ 𝒮¹(U′, R^k)` (coordinatewise data: `f_l` semialgebraic continuous,
partial derivatives `g l j` existing and semialgebraic continuous), with `f(0) = 0` and
`df(0)` invertible. Then there are semialgebraic open neighborhoods `U, V` of `0` with
`U ⊆ U′` such that `f|_U` is a (semialgebraic) homeomorphism onto `V`; in particular the
inverse is semialgebraic and continuous, i.e. `(f|_U)⁻¹ ∈ 𝒮⁰(V, U)`. The conclusion also
exposes the Jacobian's pointwise invertibility on `U` and a Lipschitz bound for the
inverse — the inputs needed to bootstrap the `𝒮^ℓ`-smoothness of the inverse
(`proposition_3_24_sClass`). -/
theorem proposition_3_24 {k : ℕ} {U' : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hU'open : IsOpen U') (hU'sa : IsSemialgebraicSet U') (h0U' : (0 : Fin k → R) ∈ U')
    (hf : ∀ l, IsSemialgContinuousOn U' (fun z => f z l))
    (hdiff : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => f w l) U' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn U' (g l j))
    (hf0 : f 0 = 0)
    (hdet : IsUnit (jacobianMatrix g 0).det) :
    ∃ U V : Set (Fin k → R),
      IsSemialgebraicSet U ∧ IsOpen U ∧ (0 : Fin k → R) ∈ U ∧ U ⊆ U' ∧
      IsSemialgebraicSet V ∧ IsOpen V ∧ (0 : Fin k → R) ∈ V ∧
      ∃ finv : (Fin k → R) → (Fin k → R),
        IsSemialgebraicHomeomorphism U V f finv ∧ IsSemialgebraicFunction V finv ∧
        (∀ z ∈ U, IsUnit (jacobianMatrix g z).det) ∧
        ∃ C : R, 0 < C ∧ ∀ y ∈ V, ∀ y' ∈ V,
          euclideanNorm (finv y - finv y') ≤ C * euclideanNorm (y - y') := by
  classical
  -- the singleton space: `f` is the identity
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hU'univ : U' = Set.univ :=
      Set.eq_univ_of_forall fun z => (Subsingleton.elim z 0) ▸ h0U'
    have hfid : f = id := by
      funext z
      rw [Subsingleton.elim z 0, hf0]
      rfl
    have hsa : IsSemialgebraicSet (Set.univ : Set (Fin 0 → R)) := by
      have heq : (Set.univ : Set (Fin 0 → R))
          = {z | eval z (C 1 : MvPolynomial (Fin 0) R) > 0} := by
        ext z
        simp
      rw [heq]
      exact IsSemialgebraicSet.gtZero _
    subst hfid
    refine ⟨Set.univ, Set.univ, hsa, isOpen_univ, Set.mem_univ _, by rw [hU'univ],
      hsa, isOpen_univ, Set.mem_univ _, id,
      IsSemialgebraicHomeomorphism.refl hsa, isSemialgebraicFunction_id hsa,
      fun z _ => by rw [Matrix.det_fin_zero]; exact isUnit_one,
      ⟨1, one_pos, fun y _ y' _ => le_of_eq (by simp only [id_eq, one_mul])⟩⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- the derivative at the origin, its transpose, and their lower bounds
  set A : Matrix (Fin k) (Fin k) R := jacobianMatrix g 0 with hAd
  have hdetT : IsUnit A.transpose.det := by rwa [Matrix.det_transpose]
  obtain ⟨mA, hmA, hlowA⟩ := exists_mulVec_lower_bound hk hdet
  obtain ⟨mT, hmT, hlowT⟩ := exists_mulVec_lower_bound hk hdetT
  set ε : R := min mA mT / 2 with hεd
  have hε : 0 < ε := by
    rw [hεd]
    have := lt_min hmA hmT
    linarith
  have hεA : ε < mA := by
    rw [hεd]
    have := min_le_left mA mT
    linarith
  have hεT : ε < mT := by
    rw [hεd]
    have := min_le_right mA mT
    linarith
  -- a ball inside `U′`
  obtain ⟨ρ₀, hρ₀, hballU'⟩ := isOpen_iff_ball_self.mp hU'open 0 h0U'
  -- entrywise closeness of the Jacobian to `A`
  set η : R := ε / ((k : R) + 1) with hηd
  have hk1 : (1 : R) ≤ (k : R) := by exact_mod_cast hk
  have hη : 0 < η := by
    rw [hηd]
    positivity
  have hδc : ∀ l j : Fin k, ∃ δ, 0 < δ ∧ ∀ z ∈ U',
      euclideanNormSq (z - 0) < δ ^ 2 → |g l j z - g l j 0| < η := by
    intro l j
    obtain ⟨δ, hδ, hb⟩ := (continuousOn_iff_ball.mp (hgsc l j).2) 0 h0U' η hη
    refine ⟨δ, hδ, fun z hzU hz => ?_⟩
    have hz' := hb z hzU ((euclideanNorm_lt_iff hδ).mpr hz)
    have heq : euclideanNorm (scalarFun (g l j) z - scalarFun (g l j) 0)
        = |g l j z - g l j 0| := by
      rw [euclideanNorm_fin_one]
      rfl
    rwa [heq] at hz'
  choose δc hδcpos hδcball using hδc
  set δ₀ : R := Finset.univ.inf' Finset.univ_nonempty
    (fun lj : Fin k × Fin k => δc lj.1 lj.2) with hδ₀d
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀d, Finset.lt_inf'_iff]
    exact fun lj _ => hδcpos lj.1 lj.2
  set ρ : R := min ρ₀ δ₀ with hρd
  have hρ : 0 < ρ := lt_min hρ₀ hδ₀pos
  have hballρ : openBall (0 : Fin k → R) ρ ⊆ U' := fun z hz => by
    refine hballU' ?_
    rw [mem_openBall] at hz ⊢
    have : ρ ^ 2 ≤ ρ₀ ^ 2 := by
      have h1 := min_le_left ρ₀ δ₀
      nlinarith
    linarith
  -- the Jacobian difference is `ε`-small in operator norm on the ball, on both sides
  have hEntries : ∀ z ∈ openBall (0 : Fin k → R) ρ, ∀ l j : Fin k,
      |g l j z - g l j 0| < η := by
    intro z hz l j
    refine hδcball l j z (hballρ hz) ?_
    rw [mem_openBall] at hz
    have h1 : ρ ≤ δc l j := le_trans (min_le_right ρ₀ δ₀)
      (by rw [hδ₀d]; exact Finset.inf'_le _ (Finset.mem_univ (l, j)))
    nlinarith [hδcpos l j]
  have hFrob : ∀ z ∈ openBall (0 : Fin k → R) ρ,
      (∑ l, ∑ j, (jacobianMatrix g z - A) l j ^ 2) ≤ ε ^ 2 := by
    intro z hz
    have hone : ∀ l j : Fin k, (jacobianMatrix g z - A) l j ^ 2 ≤ η ^ 2 := by
      intro l j
      have h1 := hEntries z hz l j
      have h2 : (jacobianMatrix g z - A) l j = g l j z - g l j 0 := rfl
      rw [h2]
      nlinarith [abs_nonneg (g l j z - g l j 0), sq_abs (g l j z - g l j 0)]
    calc (∑ l, ∑ j, (jacobianMatrix g z - A) l j ^ 2)
        ≤ ∑ l : Fin k, ∑ j : Fin k, η ^ 2 := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hone l j
      _ = (k : R) * ((k : R) * η ^ 2) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ ε ^ 2 := by
          rw [hηd]
          rw [div_pow]
          rw [mul_div_assoc']
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hε]
  have hE : ∀ z ∈ openBall (0 : Fin k → R) ρ,
      opNorm (jacobianMatrix g z - A) ≤ ε := fun z hz =>
    opNorm_le_of_entries_sq_le hk hε.le (hFrob z hz)
  have hET : ∀ z ∈ openBall (0 : Fin k → R) ρ,
      opNorm (jacobianMatrix g z - A).transpose ≤ ε := by
    intro z hz
    refine opNorm_le_of_entries_sq_le hk hε.le ?_
    have hswap : (∑ l, ∑ j, (jacobianMatrix g z - A).transpose l j ^ 2)
        = ∑ l, ∑ j, (jacobianMatrix g z - A) l j ^ 2 := by
      simp only [Matrix.transpose_apply]
      exact Finset.sum_comm
    rw [hswap]
    exact hFrob z hz
  -- the transposed Jacobian is injective on the ball
  have hTinj : ∀ z ∈ openBall (0 : Fin k → R) ρ, ∀ v : Fin k → R,
      Matrix.vecMul v (jacobianMatrix g z) = 0 → v = 0 := by
    intro z hz v hv
    rw [vecMul_eq_mulVec_transpose] at hv
    have hsplit : (jacobianMatrix g z).transpose
        = A.transpose + (jacobianMatrix g z - A).transpose := by
      rw [← Matrix.transpose_add]
      congr 1
      exact (add_sub_cancel A (jacobianMatrix g z)).symm
    rw [hsplit] at hv
    exact mulVec_add_eq_zero hk hlowT (hET z hz) hεT hv
  -- the key estimate from Proposition 3.23, with the difference function `f − A·`
  have hkey : ∀ x' ∈ openBall (0 : Fin k → R) ρ, ∀ y' ∈ openBall (0 : Fin k → R) ρ,
      euclideanNorm (f x' - f y' - A.mulVec (x' - y'))
        ≤ ε * euclideanNorm (x' - y') := by
    intro x' hx' y' hy'
    -- the data of `f − A·`
    set ft : (Fin k → R) → (Fin k → R) := fun z => f z - A.mulVec z with hftd
    set gt : Fin k → Fin k → (Fin k → R) → R := fun l j z => g l j z - A l j with hgtd
    have hlin : ∀ l : Fin k, IsSemialgContinuousOn U'
        (fun z : Fin k → R => (A.mulVec z) l) := by
      intro l
      have hco : scalarFun (fun z : Fin k → R => (A.mulVec z) l)
          = polyFun (∑ j, C (A l j) * X j) := by
        funext z m
        simp [scalarFun, polyFun, constPt, Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine ⟨?_, ?_⟩
      · rw [hco]
        exact polyFun_isSemialgebraicFunction_on hU'sa _
      · rw [hco]
        exact (continuous_iff_components.mpr fun _ =>
          continuousR_eval _).continuousOn
    have hft : ∀ l, IsSemialgContinuousOn U' (fun z => ft z l) := by
      intro l
      have heq : (fun z => ft z l)
          = (fun z => f z l) + -(fun z : Fin k → R => (A.mulVec z) l) := by
        funext z
        rw [hftd]
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      rw [heq]
      exact IsSemialgContinuousOn.add hU'sa (hf l)
        (IsSemialgContinuousOn.neg hU'sa (hlin l))
    have hgtsc : ∀ l j, IsSemialgContinuousOn U' (gt l j) := by
      intro l j
      have heq : gt l j = (fun z => g l j z) + -(fun _ : Fin k → R => A l j) := by
        funext z
        rw [hgtd]
        simp only [Pi.add_apply, Pi.neg_apply]
        ring
      rw [heq]
      exact IsSemialgContinuousOn.add hU'sa (hgsc l j)
        (IsSemialgContinuousOn.neg hU'sa (isSemialgContinuousOn_constFun hU'sa _))
    have hdifft : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => ft w l) U' j z
        (gt l j z) := by
      intro l j z hz
      -- partial of the linear part is the matrix entry
      have hlinpd : HasPartialDerivAtIn (fun w : Fin k → R => -((A.mulVec w) l))
          U' j z (-(A l j)) := by
        refine HasPartialDerivAtIn.neg ?_
        show HasDerivAtIn (fun t => (A.mulVec (Function.update z j t)) l) _ _ _
        have hslice : (fun t => (A.mulVec (Function.update z j t)) l)
            = fun t => A l j * t + (∑ i ∈ Finset.univ.erase j, A l i * z i) := by
          funext t
          show (∑ i, A l i * Function.update z j t i) = _
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        rw [hslice]
        exact hasDerivAtIn_affine _ _ _ _
      have hadd := HasPartialDerivAtIn.add (hdiff l j z hz) hlinpd
      have heq : (fun y => f y l + -((A.mulVec y) l)) = fun w => ft w l := by
        funext w
        rw [hftd]
        simp only [Pi.sub_apply]
        ring
      rw [heq] at hadd
      have hval : g l j z + -(A l j) = gt l j z := by
        rw [hgtd]
        ring
      rwa [hval] at hadd
    -- the Jacobian of the difference data
    have hJt : ∀ z, jacobianMatrix gt z = jacobianMatrix g z - A := by
      intro z
      ext l j
      rfl
    have h323 := proposition_3_23 (f := ft) (g := gt) (x := x') (y := y') (M := ε)
      hU'open (fun t ht0 ht1 => hballρ (segPath_mem_openBall hρ hx' hy' ht0 ht1))
      hft hdifft hgtsc
      (fun t ht0 ht1 => by
        rw [hJt]
        exact hE _ (segPath_mem_openBall hρ hx' hy' ht0 ht1))
      hε.le
    have heqd : ft x' - ft y' = f x' - f y' - A.mulVec (x' - y') := by
      rw [hftd, Matrix.mulVec_sub]
      funext i
      simp only [Pi.sub_apply]
      ring
    rwa [heqd] at h323
  -- the lower bound and injectivity on the ball
  have hlower : ∀ x' ∈ openBall (0 : Fin k → R) ρ, ∀ y' ∈ openBall (0 : Fin k → R) ρ,
      (mA - ε) * euclideanNorm (x' - y') ≤ euclideanNorm (f x' - f y') := by
    intro x' hx' y' hy'
    have h1 := hkey x' hx' y' hy'
    have h2 := hlowA (x' - y')
    have htri : euclideanNorm (A.mulVec (x' - y'))
        ≤ euclideanNorm (A.mulVec (x' - y') - (f x' - f y'))
          + euclideanNorm (f x' - f y') := by
      have h := euclideanNorm_add_le (A.mulVec (x' - y') - (f x' - f y')) (f x' - f y')
      have heq : A.mulVec (x' - y') - (f x' - f y') + (f x' - f y')
          = A.mulVec (x' - y') := by
        funext i
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rwa [heq] at h
    have hsym : euclideanNorm (A.mulVec (x' - y') - (f x' - f y'))
        = euclideanNorm (f x' - f y' - A.mulVec (x' - y')) :=
      euclideanNorm_sub_symm _ _
    rw [hsym] at htri
    nlinarith [euclideanNorm_nonneg (x' - y')]
  have hmAε : 0 < mA - ε := by linarith
  have hinj : Set.InjOn f (openBall (0 : Fin k → R) ρ) := by
    intro x' hx' y' hy' hfeq
    by_contra hne
    have h1 := hlower x' hx' y' hy'
    rw [hfeq, sub_self, euclideanNorm_zero] at h1
    have h2 : 0 < euclideanNorm (x' - y') := euclideanNorm_pos_of_ne hne
    nlinarith
  -- radii for the surjectivity argument
  set rr : R := ρ / 2 with hrrd
  have hrr : 0 < rr := by rw [hrrd]; linarith
  have hrrρ : ∀ z : Fin k → R, z ∈ closedBall (0 : Fin k → R) rr →
      z ∈ openBall (0 : Fin k → R) ρ := by
    intro z hz
    rw [mem_closedBall, sub_zero] at hz
    rw [mem_openBall, sub_zero]
    nlinarith
  set vrad : R := (mA - ε) * rr / 2 with hvradd
  have hvrad : 0 < vrad := by
    rw [hvradd]
    exact div_pos (mul_pos hmAε hrr) two_pos
  set V : Set (Fin k → R) := openBall 0 vrad with hVd
  have hBsa : IsSemialgebraicSet (closedBall (0 : Fin k → R) rr) :=
    isSemialgebraicSet_closedBall 0 rr
  have hBcl : IsClosed (closedBall (0 : Fin k → R) rr) := isClosed_closedBall 0 rr
  have hBsub : closedBall (0 : Fin k → R) rr ⊆ U' := fun z hz => hballρ (hrrρ z hz)
  have h0B : (0 : Fin k → R) ∈ closedBall (0 : Fin k → R) rr := by
    rw [mem_closedBall, sub_zero, euclideanNormSq_zero]
    positivity
  -- surjectivity: every point of `V` is attained from the open ball of radius `rr`
  have hsurj : ∀ y0 ∈ V, ∃ z, z ∈ openBall (0 : Fin k → R) rr ∧ f z = y0 := by
    intro y0 hy0
    rw [hVd, mem_openBall, sub_zero] at hy0
    set h : (Fin k → R) → R := fun z => ∑ l, (f z l - y0 l) * (f z l - y0 l) with hhd
    have hnormSq : ∀ z, h z = euclideanNormSq (f z - y0) := by
      intro z
      rw [hhd, euclideanNormSq]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Pi.sub_apply]
      ring
    have hcomp : ∀ l, IsSemialgContinuousOn (closedBall (0 : Fin k → R) rr)
        (fun z => f z l) := fun l =>
      ⟨(hf l).1.mono hBsa hBsub, (hf l).2.mono hBsub⟩
    have hobj : IsSemialgContinuousOn (closedBall (0 : Fin k → R) rr)
        (fun z => -(h z)) := by
      rw [isSemialgContinuousOn_iff_mem hBsa]
      have heq : scalarFun (fun z => -(h z))
          = -(∑ l : Fin k, (scalarFun (fun z => f z l)
                - scalarFun (fun _ : Fin k → R => y0 l))
              * (scalarFun (fun z => f z l)
                - scalarFun (fun _ : Fin k → R => y0 l))) := by
        funext z m
        simp only [hhd, scalarFun, constPt, Pi.neg_apply, Finset.sum_apply,
          Pi.mul_apply, Pi.sub_apply]
      rw [heq]
      refine neg_mem (Subring.sum_mem _ fun l _ => ?_)
      have hmem := (isSemialgContinuousOn_iff_mem hBsa _).mp (hcomp l)
      have hconst := (isSemialgContinuousOn_iff_mem hBsa _).mp
        (isSemialgContinuousOn_constFun hBsa (y0 l))
      exact mul_mem (sub_mem hmem hconst) (sub_mem hmem hconst)
    obtain ⟨zmin, hzminB, hzminmax⟩ := exists_max_of_closed_bounded hBsa hBcl
      (isBoundedSet_closedBall rr) ⟨0, h0B⟩ hobj.1 hobj.2
    have hmin : ∀ z ∈ closedBall (0 : Fin k → R) rr, h zmin ≤ h z := by
      intro z hz
      have h1 : -(h z) ≤ -(h zmin) := hzminmax z hz
      linarith
    have hmin0 : h zmin ≤ h 0 := hmin 0 h0B
    have hh0 : h 0 = euclideanNormSq y0 := by
      rw [hnormSq, hf0]
      rw [euclideanNormSq, euclideanNormSq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.sub_apply, Pi.zero_apply]
      ring
    -- the minimum is interior
    have hzminB' : euclideanNormSq zmin ≤ rr ^ 2 := by
      have := hzminB
      rwa [mem_closedBall, sub_zero] at this
    have hzmin_int : euclideanNormSq zmin < rr ^ 2 := by
      rcases lt_or_eq_of_le hzminB' with hlt | heqb
      · exact hlt
      · exfalso
        have hzn : euclideanNorm zmin = rr := by
          refine eq_of_sq_eq_sq (euclideanNorm_nonneg _) hrr.le ?_
          rw [euclideanNorm_sq]
          exact heqb
        have hzball : zmin ∈ openBall (0 : Fin k → R) ρ := hrrρ _ hzminB
        have h0ball : (0 : Fin k → R) ∈ openBall (0 : Fin k → R) ρ :=
          mem_openBall_self _ hρ
        have hlow := hlower zmin hzball 0 h0ball
        rw [hf0] at hlow
        have hz0 : zmin - 0 = zmin := by funext i; simp
        have hfz0 : f zmin - 0 = f zmin := by funext i; simp
        rw [hz0, hfz0, hzn] at hlow
        have hy0n : euclideanNorm y0 < vrad := by
          rw [euclideanNorm_lt_iff hvrad]
          exact hy0
        have htri : euclideanNorm (f zmin)
            ≤ euclideanNorm (f zmin - y0) + euclideanNorm y0 := by
          have h1 := euclideanNorm_add_le (f zmin - y0) y0
          have heq2 : f zmin - y0 + y0 = f zmin := by
            funext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
          rwa [heq2] at h1
        have hfy : vrad ≤ euclideanNorm (f zmin - y0) := by
          have hveq := hvradd
          linarith
        have h1 : vrad ^ 2 ≤ h zmin := by
          rw [hnormSq, ← euclideanNorm_sq, pow_two, pow_two]
          exact mul_self_le_mul_self hvrad.le hfy
        have h2 : h 0 < vrad ^ 2 := by
          rw [hh0]
          exact hy0
        linarith
    have hzminU' : zmin ∈ U' := hBsub hzminB
    have hzminρ : zmin ∈ openBall (0 : Fin k → R) ρ := hrrρ _ hzminB
    -- the partials of `h` vanish at the interior minimum
    have hgrad : ∀ i : Fin k, (∑ l, (f zmin l - y0 l) * g l i zmin) = 0 := by
      intro i
      refine grad_eq_zero_at_interior_min hdiff hBsub hzminB hzmin_int ?_ i
      intro z hz
      have h1 : -(h z) ≤ -(h zmin) := hzminmax z hz
      have h2 : h zmin ≤ h z := by linarith
      exact h2
    -- the gradient equations are `(f(zmin) − y0) ᵥ* df(zmin) = 0`
    have hvm : Matrix.vecMul (f zmin - y0) (jacobianMatrix g zmin) = 0 := by
      funext i
      show (∑ l, (f zmin - y0) l * jacobianMatrix g zmin l i) = 0
      have hterm : ∀ l, (f zmin - y0) l * jacobianMatrix g zmin l i
          = (f zmin l - y0 l) * g l i zmin := fun l => rfl
      rw [Finset.sum_congr rfl fun l _ => hterm l]
      exact hgrad i
    have hfz : f zmin - y0 = 0 := hTinj zmin hzminρ _ hvm
    refine ⟨zmin, ?_, sub_eq_zero.mp hfz⟩
    rw [mem_openBall, sub_zero]
    exact hzmin_int
  -- the neighborhoods, and the inverse
  set U : Set (Fin k → R) := openBall (0 : Fin k → R) rr ∩ f ⁻¹' V with hUd
  have hballrr_subρ : openBall (0 : Fin k → R) rr ⊆ openBall (0 : Fin k → R) ρ := by
    intro z hz
    rw [mem_openBall] at hz ⊢
    have : rr ^ 2 ≤ ρ ^ 2 := by nlinarith
    linarith
  have hballrr_subU' : openBall (0 : Fin k → R) rr ⊆ U' :=
    fun z hz => hballρ (hballrr_subρ hz)
  have hfU' : IsSemialgebraicFunction U' f :=
    isSemialgebraicFunction_of_coords fun l => (hf l).1
  have hfcont : ContinuousOn f U' := by
    refine continuousOn_of_components fun l => ?_
    show ContinuousOn (scalarFun (fun z => f z l)) U'
    exact (hf l).2
  have hVsa : IsSemialgebraicSet V := isSemialgebraicSet_openBall 0 vrad
  have hVopen : IsOpen V := isOpen_openBall 0 hvrad
  have hballrr_sa : IsSemialgebraicSet (openBall (0 : Fin k → R) rr) :=
    isSemialgebraicSet_openBall 0 rr
  have hUsa : IsSemialgebraicSet U :=
    (proposition_2_83 (hfU'.mono hballrr_sa hballrr_subU')).2 hVsa
  have hUopen : IsOpen U :=
    ContinuousOn.isOpen_inter_preimage (hfcont.mono hballrr_subU')
      (isOpen_openBall 0 hrr) hVopen
  have h0U : (0 : Fin k → R) ∈ U := by
    refine ⟨mem_openBall_self 0 hrr, ?_⟩
    show f 0 ∈ V
    rw [hf0]
    exact mem_openBall_self 0 hvrad
  have hUsubU' : U ⊆ U' := fun z hz => hballrr_subU' hz.1
  have hUsubρ : U ⊆ openBall (0 : Fin k → R) ρ := fun z hz => hballrr_subρ hz.1
  -- the bijection
  have hbij : Set.BijOn f U V := by
    refine ⟨fun z hz => hz.2, hinj.mono hUsubρ, fun y hy => ?_⟩
    obtain ⟨z, hzball, hfz⟩ := hsurj y hy
    exact ⟨z, ⟨hzball, by rw [Set.mem_preimage, hfz]; exact hy⟩, hfz⟩
  set finv : (Fin k → R) → (Fin k → R) := Function.invFunOn f U with hfinvd
  have hright : ∀ y ∈ V, f (finv y) = y := by
    intro y hy
    obtain ⟨z, hzU, hfz⟩ := hbij.surjOn hy
    exact Function.invFunOn_eq ⟨z, hzU, hfz⟩
  have hmemU : ∀ y ∈ V, finv y ∈ U := by
    intro y hy
    obtain ⟨z, hzU, hfz⟩ := hbij.surjOn hy
    exact Function.invFunOn_mem ⟨z, hzU, hfz⟩
  have hleft : ∀ x ∈ U, finv (f x) = x := by
    intro x hx
    have hfx : f x ∈ V := hx.2
    exact hinj.mono hUsubρ (hmemU _ hfx) hx (hright _ hfx)
  have hinvOn : Set.InvOn finv f U V := ⟨hleft, hright⟩
  -- the inverse is Lipschitz, hence continuous
  have hfinv_cont : ContinuousOn finv V := by
    rw [continuousOn_iff_ball]
    intro y hy r hr
    refine ⟨(mA - ε) * r, mul_pos hmAε hr, fun z hz hnorm => ?_⟩
    have h1 := hlower (finv z) (hUsubρ (hmemU _ hz)) (finv y) (hUsubρ (hmemU _ hy))
    rw [hright _ hz, hright _ hy] at h1
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : (mA - ε) * r ≤ (mA - ε) * euclideanNorm (finv z - finv y) :=
      mul_le_mul_of_nonneg_left hcon hmAε.le
    exact lt_irrefl ((mA - ε) * r) (lt_of_le_of_lt (h2.trans h1) hnorm)
  -- package everything
  have hfUsa : IsSemialgebraicFunction U f := hfU'.mono hUsa hUsubU'
  refine ⟨U, V, hUsa, hUopen, h0U, hUsubU', hVsa, hVopen,
    mem_openBall_self 0 hvrad, finv, ?_, ?_, ?_, ?_⟩
  · exact ⟨hfUsa, hbij, hfcont.mono hUsubU', hinvOn, hfinv_cont⟩
  · exact inverse_isSemialgebraicFunction hfUsa hbij hinvOn
  · -- pointwise invertibility of the Jacobian on `U` (via transpose injectivity)
    intro z hz
    have hzρ : z ∈ openBall (0 : Fin k → R) ρ := hUsubρ hz
    have hinj_mulVec : Function.Injective ((jacobianMatrix g z).transpose.mulVec) := by
      intro u w huw
      have hsub0 : (jacobianMatrix g z).transpose.mulVec (u - w) = 0 := by
        rw [Matrix.mulVec_sub, huw, sub_self]
      have hvm : Matrix.vecMul (u - w) (jacobianMatrix g z) = 0 := by
        rw [vecMul_eq_mulVec_transpose]; exact hsub0
      exact sub_eq_zero.mp (hTinj z hzρ (u - w) hvm)
    have hUnitT : IsUnit (jacobianMatrix g z).transpose :=
      Matrix.mulVec_injective_iff_isUnit.mp hinj_mulVec
    rw [Matrix.isUnit_iff_isUnit_det] at hUnitT
    rwa [Matrix.det_transpose] at hUnitT
  · -- the inverse is Lipschitz with constant `(mA − ε)⁻¹`
    refine ⟨(mA - ε)⁻¹, inv_pos.mpr hmAε, fun y hy y' hy' => ?_⟩
    have h1 := hlower (finv y) (hUsubρ (hmemU _ hy)) (finv y') (hUsubρ (hmemU _ hy'))
    rw [hright _ hy, hright _ hy'] at h1
    calc euclideanNorm (finv y - finv y')
        = (mA - ε)⁻¹ * ((mA - ε) * euclideanNorm (finv y - finv y')) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmAε), one_mul]
      _ ≤ (mA - ε)⁻¹ * euclideanNorm (y - y') :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hmAε.le)

end Azurite.BPR
