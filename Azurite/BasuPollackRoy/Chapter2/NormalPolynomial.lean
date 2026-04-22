import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree

/-!
# BPR Definition: Normal polynomial

A polynomial `A = a_p X^p + ⋯ + a_0` with non-negative coefficients is *normal* if:
(a) `a_p > 0`,
(b) `a_k² ≥ a_{k-1} · a_{k+1}` for all indices `k` (log-concavity),
(c) `a_j > 0` and `a_h > 0` with `j < h` imply `a_{j+1}, …, a_{h-1}` are all `> 0`
    (contiguous positive support),
with the convention `a_i = 0` for `i < 0` or `i > p`.

Under this convention the log-concavity condition at `k = 0` reads
`a_0² ≥ 0 · a_1 = 0` and at `k = p` reads `a_p² ≥ a_{p-1} · 0 = 0`, both automatic;
the substantive content is `1 ≤ k ≤ p - 1`. We state it as
`a_k · a_{k+2} ≤ a_{k+1}²` for all `k : ℕ` — equivalent, and avoids `ℕ`-subtraction.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*}

/-- **BPR Definition (normal polynomial).**
`P` is *normal* if every coefficient is non-negative, the leading coefficient is
strictly positive, the coefficient sequence is log-concave, and its positive support
is contiguous (no interior zeros between two positive coefficients). -/
structure IsNormal [CommSemiring R] [PartialOrder R] (P : R[X]) : Prop where
  /-- (BPR prefix) All coefficients are non-negative. -/
  coeff_nonneg : ∀ i, 0 ≤ P.coeff i
  /-- (BPR condition a) The leading coefficient is strictly positive. -/
  leading_pos : 0 < P.leadingCoeff
  /-- (BPR condition b) Log-concavity: `a_k · a_{k+2} ≤ a_{k+1}²` for all `k`.
      Equivalent to BPR's `a_k² ≥ a_{k-1} · a_{k+1}` for `1 ≤ k ≤ p - 1`; the
      boundary cases `k = 0` and `k = p` are automatic under the convention
      `a_i = 0` for `i < 0` or `i > p`. -/
  log_concave : ∀ k, P.coeff k * P.coeff (k + 2) ≤ P.coeff (k + 1) ^ 2
  /-- (BPR condition c) Contiguous positive support: no interior gaps. -/
  no_gap : ∀ {j h : ℕ}, j < h → 0 < P.coeff j → 0 < P.coeff h →
    ∀ {i : ℕ}, j < i → i < h → 0 < P.coeff i

/-! ## Lemma 2.41: linear factors -/

section LinearFactor

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma coeff_X_sub_C_eq (x : R) (i : ℕ) :
    ((X : R[X]) - C x).coeff i =
      if i = 0 then -x else if i = 1 then 1 else 0 := by
  rw [coeff_sub, coeff_X, coeff_C]
  split_ifs with h0 h1 <;> simp_all

/-- **BPR Lemma 2.41.** The linear polynomial `X - x` is normal iff `x ≤ 0`. -/
lemma isNormal_X_sub_C_iff {x : R} : IsNormal ((X : R[X]) - C x) ↔ x ≤ 0 := by
  constructor
  · intro h
    have h0 := h.coeff_nonneg 0
    rw [coeff_X_sub_C_eq] at h0
    simpa using neg_nonneg.mp h0
  · intro hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_X_sub_C_eq]
      split_ifs
      · exact neg_nonneg.mpr hx
      · exact zero_le_one
      · exact le_refl 0
    · rw [leadingCoeff, natDegree_X_sub_C, coeff_X_sub_C_eq]
      simp
    · intro k
      simp only [coeff_X_sub_C_eq]
      rcases k with _ | _ | k <;> simp
    · rintro j h hjh hj hh i hji hih
      rw [coeff_X_sub_C_eq] at hj hh
      split_ifs at hj with hj0 hj1
      · subst hj0
        split_ifs at hh with hh0 hh1
        · subst hh0; exact absurd hjh (lt_irrefl 0)
        · subst hh1; omega
        · exact absurd hh (lt_irrefl 0)
      · subst hj1
        split_ifs at hh with hh0 hh1
        · subst hh0; omega
        · subst hh1; omega
        · exact absurd hh (lt_irrefl 0)
      · exact absurd hj (lt_irrefl 0)

end LinearFactor

/-! ## Lemma 2.42: quadratic factors with complex conjugate roots -/

section QuadraticFactor

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR cone 𝓑.** Pairs `(a, b) : R × R` representing the "complex numbers"
    `a + ib ∈ R[i]` that satisfy `|b| ≤ -√3 · a`. We formulate it via the squared
    form `b² ≤ 3·a²` together with `a ≤ 0` — equivalent (given `a ≤ 0`) to the
    `√3` form, and stateable without requiring `√3 ∈ R`. -/
def ConeB : Set (R × R) :=
  {p | p.1 ≤ 0 ∧ p.2 ^ 2 ≤ 3 * p.1 ^ 2}

/-- The monic quadratic with complex conjugate roots `a ± ib`:
    `X² − 2aX + (a² + b²)`. -/
noncomputable def quadFromRoots (a b : R) : R[X] :=
  X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma coeff_quadFromRoots (a b : R) (i : ℕ) :
    (quadFromRoots a b).coeff i =
      if i = 0 then a ^ 2 + b ^ 2
      else if i = 1 then -(2 * a)
      else if i = 2 then 1
      else 0 := by
  unfold quadFromRoots
  rw [coeff_add, coeff_sub, coeff_C, coeff_X_pow, coeff_C_mul, coeff_X]
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | _ + 3 => simp

private lemma natDegree_quadFromRoots (a b : R) :
    (quadFromRoots a b).natDegree = 2 := by
  unfold quadFromRoots
  compute_degree!

/-- **BPR Lemma 2.42.** The monic quadratic `X² − 2aX + (a² + b²)` with complex
    conjugate roots `a ± ib` is normal iff `(a, b) ∈ 𝓑`. -/
lemma isNormal_quadFromRoots_iff (a b : R) :
    IsNormal (quadFromRoots a b) ↔ (a, b) ∈ ConeB := by
  unfold ConeB
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h.coeff_nonneg 1
      rw [coeff_quadFromRoots] at h1
      simp at h1
      linarith
    · have hlog := h.log_concave 0
      simp only [coeff_quadFromRoots] at hlog
      simp at hlog
      nlinarith [hlog]
  · rintro ⟨ha, hab⟩
    have hsumsq : (0 : R) ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
    have hneg2a : (0 : R) ≤ -(2 * a) := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_quadFromRoots]
      split_ifs
      · exact hsumsq
      · exact hneg2a
      · exact zero_le_one
      · exact le_refl 0
    · rw [leadingCoeff, natDegree_quadFromRoots, coeff_quadFromRoots]
      simp
    · intro k
      simp only [coeff_quadFromRoots]
      match k with
      | 0 => simp; nlinarith [hab]
      | 1 => simp
      | 2 => simp
      | _ + 3 => simp
    · rintro j h hjh hj hh i hji hih
      rw [coeff_quadFromRoots] at hj hh
      split_ifs at hj with hj0 hj1 hj2
      · subst hj0
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; exact absurd hjh (lt_irrefl 0)
        · subst hh1; omega
        · subst hh2
          have hi : i = 1 := by omega
          subst hi
          rw [coeff_quadFromRoots]
          simp only [show (1 : ℕ) ≠ 0 from by decide, if_false, if_true]
          by_contra hnot
          push Not at hnot
          have ha_eq : a = 0 := le_antisymm ha (by linarith)
          rw [ha_eq] at hj hab
          nlinarith [sq_nonneg b]
        · exact absurd hh (lt_irrefl 0)
      · subst hj1
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; omega
        · subst hh1; omega
        · subst hh2; omega
        · exact absurd hh (lt_irrefl 0)
      · subst hj2
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; omega
        · subst hh1; omega
        · subst hh2; omega
        · exact absurd hh (lt_irrefl 0)
      · exact absurd hj (lt_irrefl 0)

end QuadraticFactor

/-! ## Lemma 2.43: product of normal polynomials

The main tool is BPR's algebraic identity expressing `c_{k+1}² − c_k · c_{k+2}` (for the
convolution coefficients `c_m = (A*B).coeff m`) as a sum of products of two kinds of
"interchange" differences, both of which are ≥ 0 by the *interchange inequality*
`a_{h-1} a_{j+1} ≤ a_h a_j` (valid for `h ≤ j` under normality, with the convention
`a_i = 0` for `i < 0`).

We use a padded coefficient function `padCoeff P : ℤ → R` so that indices can range
over all of `ℤ` in the sum.
-/

section Product

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Padded coefficient: returns `P.coeff i.toNat` for `i ≥ 0` and `0` otherwise.
    Allows stating BPR's identity as a sum over `ℤ × ℤ`. -/
private def padCoeff (P : R[X]) (i : ℤ) : R :=
  if 0 ≤ i then P.coeff i.toNat else 0

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma padCoeff_of_nonneg (P : R[X]) {i : ℤ} (hi : 0 ≤ i) :
    padCoeff P i = P.coeff i.toNat := if_pos hi

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma padCoeff_of_neg (P : R[X]) {i : ℤ} (hi : i < 0) :
    padCoeff P i = 0 := if_neg (not_le.mpr hi)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma padCoeff_natCast (P : R[X]) (n : ℕ) : padCoeff P (n : ℤ) = P.coeff n := by
  rw [padCoeff_of_nonneg _ (Int.natCast_nonneg n), Int.toNat_natCast]

omit [IsStrictOrderedRing R] in
private lemma padCoeff_nonneg {P : R[X]} (hP : IsNormal P) (i : ℤ) :
    0 ≤ padCoeff P i := by
  unfold padCoeff; split_ifs
  · exact hP.coeff_nonneg _
  · exact le_refl 0

omit [IsStrictOrderedRing R] in
/-- Positivity propagation from `no_gap`: if `P.coeff k > 0` and `P.coeff l > 0` with
    `k ≤ l`, then every coefficient on `[k, l]` is positive. -/
lemma isNormal_pos_between {P : R[X]} (hP : IsNormal P)
    {k l i : ℕ} (hki : k ≤ i) (hil : i ≤ l)
    (hk : 0 < P.coeff k) (hl : 0 < P.coeff l) : 0 < P.coeff i := by
  rcases eq_or_lt_of_le hki with rfl | hki'
  · exact hk
  rcases eq_or_lt_of_le hil with rfl | hil'
  · exact hl
  exact hP.no_gap (Nat.lt_of_lt_of_le hki' hil) hk hl hki' hil'

/-! ### Interchange inequality -/

/-- **Interchange inequality (ℕ form).** For a normal polynomial `P` and indices
    `1 ≤ h ≤ j` with `j + 1 ≤ natDegree P`:
    `a_{h-1} a_{j+1} ≤ a_h a_j`.

    Proof by induction on `j - h`, using log-concavity to extend the base case.
    The induction step relies on `a_{h+d+1} > 0` (from positivity propagation)
    to cancel. The alternative case `a_{h-1} = 0` makes the LHS zero directly. -/
private lemma isNormal_interchange_nat {P : R[X]} (hP : IsNormal P) {h j : ℕ}
    (hh : 1 ≤ h) (hhj : h ≤ j) (hj1 : j + 1 ≤ P.natDegree) :
    P.coeff (h - 1) * P.coeff (j + 1) ≤ P.coeff h * P.coeff j := by
  by_cases hh1 : P.coeff (h - 1) = 0
  · rw [hh1, zero_mul]
    exact mul_nonneg (hP.coeff_nonneg _) (hP.coeff_nonneg _)
  have hh1_pos : 0 < P.coeff (h - 1) :=
    lt_of_le_of_ne (hP.coeff_nonneg _) (Ne.symm hh1)
  obtain ⟨d, rfl⟩ : ∃ d, j = h + d := ⟨j - h, by omega⟩
  clear hhj
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    have lc := hP.log_concave (h - 1)
    rw [Nat.sub_add_cancel hh, show h - 1 + 2 = h + 1 from by omega, sq] at lc
    exact lc
  | succ d ih =>
    have hndd : h + d + 1 ≤ P.natDegree := by omega
    have hih := ih hndd
    have hlc := hP.log_concave (h + d)
    have hleading : 0 < P.coeff P.natDegree := hP.leading_pos
    have hpos : 0 < P.coeff (h + d + 1) := by
      apply isNormal_pos_between hP (k := h - 1) (l := P.natDegree) _ _ hh1_pos hleading
      · omega
      · omega
    have hpnn1 : 0 ≤ P.coeff (h + d + 2) := hP.coeff_nonneg _
    have hpnnh : 0 ≤ P.coeff h := hP.coeff_nonneg _
    have key : P.coeff (h - 1) * P.coeff (h + d + 2) * P.coeff (h + d + 1) ≤
               P.coeff h * P.coeff (h + d + 1) * P.coeff (h + d + 1) := by
      have step1 : P.coeff (h - 1) * P.coeff (h + d + 1) * P.coeff (h + d + 2) ≤
                   P.coeff h * P.coeff (h + d) * P.coeff (h + d + 2) :=
        mul_le_mul_of_nonneg_right hih hpnn1
      have step2 : P.coeff h * P.coeff (h + d) * P.coeff (h + d + 2) ≤
                   P.coeff h * P.coeff (h + d + 1)^2 := by
        have := mul_le_mul_of_nonneg_left hlc hpnnh
        linarith
      rw [sq] at step2
      nlinarith [step1, step2]
    show P.coeff (h - 1) * P.coeff (h + (d + 1) + 1) ≤ P.coeff h * P.coeff (h + (d + 1))
    rw [show h + (d + 1) + 1 = h + d + 2 from by omega,
        show h + (d + 1) = h + d + 1 from by omega]
    exact le_of_mul_le_mul_right key hpos

/-- **Interchange inequality (ℤ form).** Same as `isNormal_interchange_nat` but with
    `padCoeff`, handling all boundary cases automatically. -/
private lemma isNormal_interchange {P : R[X]} (hP : IsNormal P) {h j : ℤ} (hhj : h ≤ j) :
    padCoeff P (h - 1) * padCoeff P (j + 1) ≤ padCoeff P h * padCoeff P j := by
  by_cases hh1 : h - 1 < 0
  · rw [padCoeff_of_neg _ hh1, zero_mul]
    exact mul_nonneg (padCoeff_nonneg hP _) (padCoeff_nonneg hP _)
  push Not at hh1
  have hh : (1 : ℤ) ≤ h := by linarith
  have hj : (0 : ℤ) ≤ j := by linarith
  have hj1 : (0 : ℤ) ≤ j + 1 := by linarith
  have hh0 : (0 : ℤ) ≤ h := by linarith
  set H := h.toNat with hH_def
  set J := j.toNat with hJ_def
  have hH_eq : h = (H : ℤ) := (Int.toNat_of_nonneg hh0).symm
  have hJ_eq : j = (J : ℤ) := (Int.toNat_of_nonneg hj).symm
  have hHpos : 1 ≤ H := by
    have : (1 : ℤ) ≤ (H : ℤ) := hH_eq ▸ hh
    exact_mod_cast this
  have hHJ : H ≤ J := by
    have : (H : ℤ) ≤ (J : ℤ) := hH_eq ▸ hJ_eq ▸ hhj
    exact_mod_cast this
  have e1 : padCoeff P (h - 1) = P.coeff (H - 1) := by
    rw [padCoeff_of_nonneg _ hh1, hH_eq]
    congr 1; omega
  have e2 : padCoeff P (j + 1) = P.coeff (J + 1) := by
    rw [padCoeff_of_nonneg _ hj1, hJ_eq]
    congr 1
  have e3 : padCoeff P h = P.coeff H := by
    rw [padCoeff_of_nonneg _ hh0, hH_eq, Int.toNat_natCast]
  have e4 : padCoeff P j = P.coeff J := by
    rw [padCoeff_of_nonneg _ hj, hJ_eq, Int.toNat_natCast]
  rw [e1, e2, e3, e4]
  by_cases hjd : P.natDegree < J + 1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hjd, mul_zero]
    exact mul_nonneg (hP.coeff_nonneg _) (hP.coeff_nonneg _)
  push Not at hjd
  exact isNormal_interchange_nat hP hHpos hHJ hjd

/-! ### Easy parts of Lemma 2.43: coefficient non-negativity, leading positivity -/

/-- The product of polynomials with non-negative coefficients has non-negative
    coefficients. -/
private lemma coeff_mul_nonneg {A B : R[X]}
    (hA : ∀ i, 0 ≤ A.coeff i) (hB : ∀ i, 0 ≤ B.coeff i) (k : ℕ) :
    0 ≤ (A * B).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hA _) (hB _))

/-- The product of normal polynomials has strictly positive leading coefficient. -/
private lemma leadingCoeff_mul_pos {A B : R[X]}
    (hA : 0 < A.leadingCoeff) (hB : 0 < B.leadingCoeff) :
    0 < (A * B).leadingCoeff := by
  rw [Polynomial.leadingCoeff_mul]
  exact mul_pos hA hB

/-- Characterization of positive coefficients of the product: `(A*B).coeff k > 0` iff
    there exist `a + b = k` with both `A.coeff a > 0` and `B.coeff b > 0`. -/
private lemma coeff_mul_pos_iff {A B : R[X]}
    (hAnn : ∀ i, 0 ≤ A.coeff i) (hBnn : ∀ i, 0 ≤ B.coeff i) (k : ℕ) :
    0 < (A * B).coeff k ↔
      ∃ a b, a + b = k ∧ 0 < A.coeff a ∧ 0 < B.coeff b := by
  rw [coeff_mul]
  constructor
  · intro hpos
    by_contra hne
    push Not at hne
    have : ∀ x ∈ Finset.antidiagonal k, A.coeff x.1 * B.coeff x.2 = 0 := by
      intro ⟨a, b⟩ hab
      rw [Finset.mem_antidiagonal] at hab
      rcases lt_or_eq_of_le (hAnn a) with ha | ha
      · rcases lt_or_eq_of_le (hBnn b) with hb | hb
        · exact absurd hb (not_lt.mpr (hne a b hab ha))
        · simp [← hb]
      · simp [← ha]
    rw [Finset.sum_eq_zero this] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨a, b, hab, ha, hb⟩
    refine Finset.sum_pos' (fun x _ => mul_nonneg (hAnn _) (hBnn _)) ⟨(a, b), ?_, mul_pos ha hb⟩
    rw [Finset.mem_antidiagonal]; exact hab

/-- **No-gap for products** (BPR condition c for Lemma 2.43). The positive support of
    `A * B` is contiguous, inherited from the contiguity of the positive supports of
    `A` and `B`.

    Construction: given witnesses `(a₀, b₀)`, `(a₁, b₁)` of positivity at `j, h`, the
    "sliding" witness at `i` is `a := max(min(a₀, a₁), i - max(b₀, b₁))`, `b := i - a`,
    shown to lie in the positive boxes of both polynomials. -/
private lemma coeff_mul_no_gap {A B : R[X]} (hA : IsNormal A) (hB : IsNormal B) :
    ∀ {j h : ℕ}, j < h → 0 < (A * B).coeff j → 0 < (A * B).coeff h →
      ∀ {i : ℕ}, j < i → i < h → 0 < (A * B).coeff i := by
  intro j h hjh hjpos hhpos i hji hih
  obtain ⟨a0, b0, habj, ha0, hb0⟩ :=
    (coeff_mul_pos_iff hA.coeff_nonneg hB.coeff_nonneg j).mp hjpos
  obtain ⟨a1, b1, habh, ha1, hb1⟩ :=
    (coeff_mul_pos_iff hA.coeff_nonneg hB.coeff_nonneg h).mp hhpos
  -- Unified construction.
  set Amin := min a0 a1 with hAmin
  set Amax := max a0 a1 with hAmax
  set Bmin := min b0 b1 with hBmin
  set Bmax := max b0 b1 with hBmax
  set a := max Amin (i - Bmax) with ha_def
  set b := i - a with hb_def
  -- Bounds: Amin + Bmin ≤ j ≤ i ≤ h ≤ Amax + Bmax.
  have bound_lo : Amin + Bmin ≤ i := by
    have h1 : Amin + Bmin ≤ a0 + b0 := by
      simp only [hAmin, hBmin]
      exact Nat.add_le_add (min_le_left _ _) (min_le_left _ _)
    omega
  have bound_hi : i ≤ Amax + Bmax := by
    have h1 : a1 + b1 ≤ Amax + Bmax := by
      simp only [hAmax, hBmax]
      exact Nat.add_le_add (le_max_right _ _) (le_max_right _ _)
    omega
  -- Key: a ≤ i, so b = i - a with a + b = i.
  have a_le_i : a ≤ i := by
    rw [ha_def]
    refine max_le ?_ (Nat.sub_le _ _)
    have : Amin ≤ a0 := min_le_left _ _
    omega
  have hab_eq : a + b = i := by rw [hb_def]; omega
  -- a ∈ [Amin, Amax].
  have a_ge_Amin : Amin ≤ a := le_max_left _ _
  have a_le_Amax : a ≤ Amax := by
    rw [ha_def]
    refine max_le ?_ ?_
    · exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_of_eq_of_le rfl (le_trans (min_le_left _ _) (le_max_left _ _))))
    · -- i - Bmax ≤ Amax
      omega
  -- b ∈ [Bmin, Bmax].
  have b_ge_Bmin : Bmin ≤ b := by
    rw [hb_def]
    rw [ha_def]
    -- b = i - max(Amin, i - Bmax)
    -- Case i - Bmax ≤ Amin: a = Amin, b = i - Amin. Need Bmin ≤ i - Amin, i.e., Amin + Bmin ≤ i. ✓
    -- Case i - Bmax > Amin: a = i - Bmax, b = Bmax ≥ Bmin. ✓
    omega
  have b_le_Bmax : b ≤ Bmax := by
    rw [hb_def, ha_def]
    -- Case i - Bmax ≤ Amin: a = Amin, b = i - Amin. Need ≤ Bmax, i.e., i ≤ Amin + Bmax. ✓ (from a = Amin means i - Bmax ≤ Amin)
    -- Case i - Bmax > Amin: a = i - Bmax, b = Bmax. ✓
    omega
  -- Positivity of A at Amin, Amax.
  have hAmin_pos : 0 < A.coeff Amin := by
    rcases le_total a0 a1 with h1 | h1
    · rw [hAmin, min_eq_left h1]; exact ha0
    · rw [hAmin, min_eq_right h1]; exact ha1
  have hAmax_pos : 0 < A.coeff Amax := by
    rcases le_total a0 a1 with h1 | h1
    · rw [hAmax, max_eq_right h1]; exact ha1
    · rw [hAmax, max_eq_left h1]; exact ha0
  have hBmin_pos : 0 < B.coeff Bmin := by
    rcases le_total b0 b1 with h1 | h1
    · rw [hBmin, min_eq_left h1]; exact hb0
    · rw [hBmin, min_eq_right h1]; exact hb1
  have hBmax_pos : 0 < B.coeff Bmax := by
    rcases le_total b0 b1 with h1 | h1
    · rw [hBmax, max_eq_right h1]; exact hb1
    · rw [hBmax, max_eq_left h1]; exact hb0
  -- Positivity propagation.
  have ha_pos : 0 < A.coeff a :=
    isNormal_pos_between hA a_ge_Amin a_le_Amax hAmin_pos hAmax_pos
  have hb_pos : 0 < B.coeff b :=
    isNormal_pos_between hB b_ge_Bmin b_le_Bmax hBmin_pos hBmax_pos
  -- Conclude.
  exact (coeff_mul_pos_iff hA.coeff_nonneg hB.coeff_nonneg i).mpr
    ⟨a, b, hab_eq, ha_pos, hb_pos⟩

/-! ### BPR's algebraic identity for log-concavity of the product

Following BPR, we prove `(A*B).coeff (k+1)² − (A*B).coeff k · (A*B).coeff (k+2)`
equals a sum of nonneg products, each a product of two interchange-type differences
`α(h, j) := a_h a_j − a_{h−1} a_{j+1}` and
`β(h, j, k) := b_{k+1−j} b_{k+1−h} − b_{k−j} b_{k+2−h}`, each ≥ 0 for `h ≤ j`
by the interchange inequality. -/

/-- BPR's summand for the log-concavity identity (Lemma 2.43).
    Uses ℤ-indexed `padCoeff` so indices can go negative cleanly. -/
private noncomputable def bprSummand (A B : R[X]) (h j : ℤ) (k : ℕ) : R :=
  (padCoeff A h * padCoeff A j - padCoeff A (h - 1) * padCoeff A (j + 1)) *
  (padCoeff B (↑k + 1 - j) * padCoeff B (↑k + 1 - h) -
    padCoeff B (↑k - j) * padCoeff B (↑k + 2 - h))

/-- Each BPR summand is non-negative for `h ≤ j`, by the interchange inequality
    applied to both factors. -/
private lemma bprSummand_nonneg {A B : R[X]} (hA : IsNormal A) (hB : IsNormal B)
    {h j : ℤ} (hhj : h ≤ j) (k : ℕ) : 0 ≤ bprSummand A B h j k := by
  refine mul_nonneg ?_ ?_
  · linarith [isNormal_interchange hA hhj]
  · have hhj' : (↑k + 1 - j : ℤ) ≤ ↑k + 1 - h := by linarith
    have := isNormal_interchange hB hhj'
    have e1 : (↑k + 1 - j - 1 : ℤ) = ↑k - j := by ring
    have e2 : (↑k + 1 - h + 1 : ℤ) = ↑k + 2 - h := by ring
    rw [e1, e2] at this
    linarith

/-- BPR sum for the log-concavity identity: sum of `bprSummand` over `0 ≤ h ≤ j ≤ k+1`. -/
private noncomputable def bprSum (A B : R[X]) (k : ℕ) : R :=
  ∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range (j + 1),
    bprSummand A B (h : ℤ) (j : ℤ) k

/-- `bprSum` is non-negative, as a sum of non-negative terms. -/
private lemma bprSum_nonneg {A B : R[X]} (hA : IsNormal A) (hB : IsNormal B) (k : ℕ) :
    0 ≤ bprSum A B k := by
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun h hh => ?_
  rw [Finset.mem_range] at hh
  have hhj : (h : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hh
  exact bprSummand_nonneg hA hB hhj k

/-! ### The algebraic identity `c_{k+1}² − c_k · c_{k+2} = bprSum` -/

/-- The "F-kernel": the symmetric B-part used in expanding LHS as a double sum. -/
private noncomputable def fkern (B : R[X]) (k : ℕ) (h j : ℤ) : R :=
  padCoeff B (↑k + 1 - h) * padCoeff B (↑k + 1 - j) -
    padCoeff B (↑k - h) * padCoeff B (↑k + 2 - j)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `β(h, j, k) = F(j, h, k)`: BPR's β factor equals fkern with swapped arguments. -/
private lemma bpr_beta_eq_fkern_swap (B : R[X]) (k : ℕ) (h j : ℤ) :
    padCoeff B (↑k + 1 - j) * padCoeff B (↑k + 1 - h) -
      padCoeff B (↑k - j) * padCoeff B (↑k + 2 - h) = fkern B k j h := by
  unfold fkern; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The "off-diagonal by 1" fkern vanishes: F(j-1, j, k) = 0. -/
private lemma fkern_diag_pred_eq_zero (B : R[X]) (k : ℕ) (j : ℤ) :
    fkern B k (j - 1) j = 0 := by
  unfold fkern
  have e1 : (↑k + 1 - (j - 1) : ℤ) = ↑k + 2 - j := by ring
  have e2 : (↑k - (j - 1) : ℤ) = ↑k + 1 - j := by ring
  rw [e1, e2]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Shift identity for β: β(h+1, j-1, k) = -F(h, j, k). -/
private lemma bpr_beta_shift (B : R[X]) (k : ℕ) (h j : ℤ) :
    padCoeff B (↑k + 1 - (j - 1)) * padCoeff B (↑k + 1 - (h + 1)) -
      padCoeff B (↑k - (j - 1)) * padCoeff B (↑k + 2 - (h + 1)) = -fkern B k h j := by
  unfold fkern
  have e1 : (↑k + 1 - (j - 1) : ℤ) = ↑k + 2 - j := by ring
  have e2 : (↑k + 1 - (h + 1) : ℤ) = ↑k - h := by ring
  have e3 : (↑k - (j - 1) : ℤ) = ↑k + 1 - j := by ring
  have e4 : (↑k + 2 - (h + 1) : ℤ) = ↑k + 1 - h := by ring
  rw [e1, e2, e3, e4]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Expand `(A * B).coeff m` as a sum over `Finset.range N` for any `N > m`,
    using `padCoeff B` to handle negative indices automatically. -/
private lemma coeff_mul_eq_padSum (A B : R[X]) (m N : ℕ) (hN : m < N) :
    (A * B).coeff m = ∑ i ∈ Finset.range N, A.coeff i * padCoeff B ((m : ℤ) - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => A.coeff i * B.coeff j) m]
  rw [show N = (m + 1) + (N - (m + 1)) by omega, Finset.sum_range_add]
  have tail_zero : ∑ i ∈ Finset.range (N - (m + 1)),
      A.coeff (m + 1 + i) * padCoeff B ((m : ℤ) - (↑(m + 1 + i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : ((m : ℤ) - (↑(m + 1 + i))) < 0 := by push_cast; linarith
    rw [padCoeff_of_neg _ this, mul_zero]
  rw [tail_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  show A.coeff i * B.coeff (m - i) = A.coeff i * padCoeff B ((m : ℤ) - i)
  congr 1
  rw [padCoeff_of_nonneg _ (by omega : (0 : ℤ) ≤ (m : ℤ) - i)]
  congr 1
  rw [show ((m : ℤ) - i) = ((m - i : ℕ) : ℤ) by omega]
  exact Int.toNat_natCast _

/-- The double sum expressing `c_{k+1}² − c_k · c_{k+2}`. -/
private noncomputable def fsum (A B : R[X]) (k N : ℕ) : R :=
  ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range N,
    A.coeff h * A.coeff j * fkern B k (h : ℤ) (j : ℤ)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- LHS equals the double sum `fsum` for N large enough. -/
private lemma fsum_eq_lhs (A B : R[X]) (k N : ℕ) (hN : k + 2 < N) :
    fsum A B k N = (A * B).coeff (k + 1) ^ 2 - (A * B).coeff k * (A * B).coeff (k + 2) := by
  unfold fsum fkern
  have hk : k < N := by omega
  have hk1 : k + 1 < N := by omega
  have hk2 : k + 2 < N := hN
  have expand_sq : (A * B).coeff (k + 1) ^ 2 =
      ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range N,
        A.coeff h * A.coeff j *
          (padCoeff B ((k + 1 : ℤ) - h) * padCoeff B ((k + 1 : ℤ) - j)) := by
    rw [sq, coeff_mul_eq_padSum A B (k + 1) N hk1,
        Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  have expand_cross : (A * B).coeff k * (A * B).coeff (k + 2) =
      ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range N,
        A.coeff h * A.coeff j *
          (padCoeff B ((k : ℤ) - h) * padCoeff B ((k + 2 : ℤ) - j)) := by
    rw [coeff_mul_eq_padSum A B k N hk,
        coeff_mul_eq_padSum A B (k + 2) N hk2,
        Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [expand_sq, expand_cross, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Auxiliary: bprSum expanded using fkern via the swap identity. -/
private lemma bprSum_eq_triangle_fkern (A B : R[X]) (k : ℕ) :
    bprSum A B k = ∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range (j + 1),
      (A.coeff h * A.coeff j - padCoeff A ((h : ℤ) - 1) * padCoeff A ((j : ℤ) + 1)) *
      fkern B k (j : ℤ) (h : ℤ) := by
  unfold bprSum bprSummand
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun h _ => ?_
  rw [bpr_beta_eq_fkern_swap, padCoeff_natCast, padCoeff_natCast]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- fkern vanishes for h = k+2 (out of range), so high-h rows contribute nothing. -/
private lemma fkern_high_h_zero (B : R[X]) (k : ℕ) (j : ℤ) :
    fkern B k (↑(k + 2)) j = 0 := by
  unfold fkern
  have e1 : (↑k + 1 - (↑(k + 2) : ℤ)) = -1 := by push_cast; ring
  have e2 : (↑k - (↑(k + 2) : ℤ)) = -2 := by push_cast; ring
  rw [e1, e2]
  rw [padCoeff_of_neg _ (by norm_num : (-1 : ℤ) < 0)]
  rw [padCoeff_of_neg _ (by norm_num : (-2 : ℤ) < 0)]
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- fkern vanishes for j = k+2 in the off-diagonal-by-1 case: F(h, h+1, k) = 0. -/
private lemma fkern_diag_succ_eq_zero (B : R[X]) (k h : ℕ) :
    fkern B k (h : ℤ) ((h : ℤ) + 1) = 0 := by
  have := fkern_diag_pred_eq_zero B k ((h : ℤ) + 1)
  have e : ((h : ℤ) + 1 - 1) = h := by ring
  rwa [e] at this

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Triangular "j ≤ h" region (over range(k+3)²) equals bprSum's first part:
    obtained by swapping variable names and noting h = k+2 terms vanish. -/
private lemma triangleA_eq_bprFirst (A B : R[X]) (k : ℕ) :
    (∑ h ∈ Finset.range (k + 3), ∑ j ∈ Finset.range (h + 1),
        A.coeff h * A.coeff j * fkern B k (h : ℤ) (j : ℤ)) =
    ∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range (j + 1),
      A.coeff h * A.coeff j * fkern B k (j : ℤ) (h : ℤ) := by
  -- Split off h = k+2 (which contributes 0) and swap names.
  rw [show k + 3 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
  have high_zero : ∑ j ∈ Finset.range (k + 2 + 1),
      A.coeff (k + 2) * A.coeff j * fkern B k (↑(k + 2)) (j : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [fkern_high_h_zero]; ring
  rw [high_zero, add_zero]
  -- Now rename outer h → j, inner j → h, using a_h a_j = a_j a_h.
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Shift identity in fkern form: `F(j, h+1) = -F(h, j+1)`. -/
private lemma fkern_shift (B : R[X]) (k : ℕ) (h j : ℤ) :
    fkern B k j (h + 1) = -fkern B k h (j + 1) := by
  unfold fkern
  have e1 : (↑k + 1 - (h + 1) : ℤ) = ↑k - h := by ring
  have e2 : (↑k + 2 - (h + 1) : ℤ) = ↑k + 1 - h := by ring
  have e3 : (↑k + 1 - (j + 1) : ℤ) = ↑k - j := by ring
  have e4 : (↑k + 2 - (j + 1) : ℤ) = ↑k + 1 - j := by ring
  rw [e1, e2, e3, e4]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Upper triangle (h + 2 ≤ j) in range(k+3)² equals -(bprSum's second part).
    Obtained by the shift bijection h ↦ h-1, j ↦ j+1. -/
private lemma triangleB_eq_neg_bprSecond (A B : R[X]) (k : ℕ) :
    (∑ h ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 3 - (h + 2)),
        A.coeff h * A.coeff (h + 2 + j) *
          fkern B k (h : ℤ) ((h + 2 + j : ℕ) : ℤ)) =
    -∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range (j + 1),
      padCoeff A ((h : ℤ) - 1) * padCoeff A ((j : ℤ) + 1) * fkern B k (j : ℤ) (h : ℤ) := by
  -- Step 1: Transform LHS — normalize range, apply fkern_shift, factor the minus.
  have lhs_eq :
      (∑ h ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 3 - (h + 2)),
        A.coeff h * A.coeff (h + 2 + j) *
          fkern B k (h : ℤ) ((h + 2 + j : ℕ) : ℤ)) =
      -(∑ h ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - h),
        A.coeff h * A.coeff (h + 2 + j) *
          fkern B k ((h + 1 + j : ℕ) : ℤ) ((h + 1 : ℕ) : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show k + 3 - (h + 2) = k + 1 - h from by omega]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have cast1 : ((h + 2 + j : ℕ) : ℤ) = ((h + 1 + j : ℕ) : ℤ) + 1 := by push_cast; ring
    have cast2 : ((h + 1 : ℕ) : ℤ) = (h : ℤ) + 1 := by push_cast; ring
    rw [cast1, fkern_shift, ← cast2]; ring
  rw [lhs_eq, neg_inj]
  -- Step 2: Transform the double sum — split h = 0 (zero term) and reindex.
  have ds_eq :
      (∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range (j + 1),
        padCoeff A ((h : ℤ) - 1) * padCoeff A ((j : ℤ) + 1) *
          fkern B k (j : ℤ) (h : ℤ)) =
      (∑ j ∈ Finset.range (k + 2), ∑ h ∈ Finset.range j,
        A.coeff h * A.coeff (j + 1) *
          fkern B k ((j : ℕ) : ℤ) ((h + 1 : ℕ) : ℤ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range_succ']
    have h0_zero :
        padCoeff A ((((0 : ℕ)) : ℤ) - 1) * padCoeff A ((j : ℤ) + 1) *
          fkern B k (j : ℤ) ((((0 : ℕ)) : ℤ)) = 0 := by
      have hz : padCoeff A ((((0 : ℕ)) : ℤ) - 1) = 0 := by
        rw [Nat.cast_zero]; exact padCoeff_of_neg _ (by norm_num)
      rw [hz, zero_mul, zero_mul]
    rw [h0_zero, add_zero]
    refine Finset.sum_congr rfl fun h _ => ?_
    have e1 : (((h + 1 : ℕ) : ℤ) - 1) = (h : ℤ) := by push_cast; ring
    have e2 : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, padCoeff_natCast, padCoeff_natCast]
  rw [ds_eq]
  -- Step 3: Bijection (h_L, j_L) ↔ (j = h_L+1+j_L, h = h_L) via sigma.
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun p => ⟨p.1 + 1 + p.2, p.1⟩)
    (fun p => ⟨p.2, p.1 - p.2 - 1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    refine ⟨?_, ?_⟩ <;> omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    refine ⟨?_, ?_⟩ <;> omega
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    omega
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only [Sigma.mk.injEq, heq_eq_eq]
    refine ⟨?_, trivial⟩
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have e : p.1 + 1 + p.2 + 1 = p.1 + 2 + p.2 := by ring
    simp only
    rw [e]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Key splitting lemma: `fsum A B k (k+3)` splits as the lower triangle (including
    diagonal) plus the upper-upper triangle (`j ≥ h + 2`); the "line" `j = h + 1`
    contributes zero since `fkern B k h (h+1) = 0`. -/
private lemma fsum_split (A B : R[X]) (k : ℕ) :
    fsum A B k (k + 3) =
    (∑ h ∈ Finset.range (k + 3), ∑ j ∈ Finset.range (h + 1),
        A.coeff h * A.coeff j * fkern B k (h : ℤ) (j : ℤ)) +
    (∑ h ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 3 - (h + 2)),
        A.coeff h * A.coeff (h + 2 + j) *
          fkern B k (h : ℤ) ((h + 2 + j : ℕ) : ℤ)) := by
  unfold fsum
  -- Split inner sums: range(k+3) = range(h+1) + range(k+2-h) (shifted by h+1)
  trans (∑ h ∈ Finset.range (k + 3),
      ((∑ j ∈ Finset.range (h + 1),
          A.coeff h * A.coeff j * fkern B k (h : ℤ) (j : ℤ)) +
       (∑ j ∈ Finset.range (k + 2 - h),
          A.coeff h * A.coeff (h + 1 + j) *
            fkern B k (h : ℤ) ((h + 1 + j : ℕ) : ℤ))))
  · refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_range] at hh
    rw [show (k + 3 : ℕ) = (h + 1) + (k + 2 - h) from by omega,
        Finset.sum_range_add]
  rw [Finset.sum_add_distrib]
  refine congr_arg₂ (· + ·) rfl ?_
  -- Remaining: ∑ h ∈ range(k+3), ∑ j ∈ range(k+2-h), F(h, h+1+j)
  --   = ∑ h ∈ range(k+1), ∑ j ∈ range(k+3-(h+2)), F(h, h+2+j)
  -- Peel off h = k+2 (inner sum empty).
  rw [show (k + 3 : ℕ) = (k + 2) + 1 from by omega, Finset.sum_range_succ]
  have tail_zero1 :
      (∑ j ∈ Finset.range (k + 2 - (k + 2)),
        A.coeff (k + 2) * A.coeff ((k + 2) + 1 + j) *
          fkern B k ((k + 2 : ℕ) : ℤ) ((((k + 2) + 1 + j : ℕ)) : ℤ)) = 0 := by
    rw [show k + 2 - (k + 2) = 0 from by omega, Finset.sum_range_zero]
  rw [tail_zero1, add_zero]
  -- Now: ∑ h ∈ range(k+2), ∑ j ∈ range(k+2-h), F(h, h+1+j)
  --    = ∑ h ∈ range(k+1), ∑ j ∈ range(k+3-(h+2)), F(h, h+2+j)
  -- Peel off h = k+1 (inner F(k+1, k+2) = 0 via fkern_diag_succ).
  rw [show (k + 2 : ℕ) = (k + 1) + 1 from by omega, Finset.sum_range_succ]
  have tail_zero2 :
      (∑ j ∈ Finset.range (k + 2 - (k + 1)),
        A.coeff (k + 1) * A.coeff ((k + 1) + 1 + j) *
          fkern B k ((k + 1 : ℕ) : ℤ) ((((k + 1) + 1 + j : ℕ)) : ℤ)) = 0 := by
    rw [show k + 2 - (k + 1) = 1 from by omega, Finset.sum_range_one]
    have e : ((((k + 1) + 1 + 0 : ℕ)) : ℤ) = ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e]
    rw [fkern_diag_succ_eq_zero]
    ring
  rw [tail_zero2, add_zero]
  -- Now: ∑ h ∈ range(k+1), ∑ j ∈ range(k+2-h), F(h, h+1+j)
  --    = ∑ h ∈ range(k+1), ∑ j ∈ range(k+3-(h+2)), F(h, h+2+j)
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_range] at hh
  rw [show (k + 2 - h : ℕ) = 1 + (k + 1 - h) from by omega, Finset.sum_range_add]
  -- LHS now: ∑ j ∈ range(1), F(h, h+1+j) + ∑ j ∈ range(k+1-h), F(h, h+1+(1+j))
  have head_zero :
      (∑ j ∈ Finset.range 1,
        A.coeff h * A.coeff (h + 1 + j) *
          fkern B k (h : ℤ) ((h + 1 + j : ℕ) : ℤ)) = 0 := by
    rw [Finset.sum_range_one]
    have e : ((h + 1 + 0 : ℕ) : ℤ) = (h : ℤ) + 1 := by push_cast; ring
    rw [e]
    rw [fkern_diag_succ_eq_zero]
    ring
  rw [head_zero, zero_add]
  rw [show k + 3 - (h + 2) = k + 1 - h from by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (h + 1 + (1 + j) : ℕ) = h + 2 + j from by omega]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The algebraic identity: `c_{k+1}² − c_k · c_{k+2} = bprSum A B k`. -/
private lemma bpr_identity {A B : R[X]} (k : ℕ) :
    (A * B).coeff (k + 1) ^ 2 - (A * B).coeff k * (A * B).coeff (k + 2) = bprSum A B k := by
  rw [← fsum_eq_lhs A B k (k + 3) (by omega),
      fsum_split,
      triangleA_eq_bprFirst,
      triangleB_eq_neg_bprSecond,
      bprSum_eq_triangle_fkern]
  -- Goal: (bprFirst expression) + (-bprSecond expression) = ∑ j, ∑ h, (diff) * fkern
  simp_rw [sub_mul]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]

/-- **Log-concavity for the product.** -/
private lemma coeff_mul_log_concave {A B : R[X]} (hA : IsNormal A) (hB : IsNormal B) (k : ℕ) :
    (A * B).coeff k * (A * B).coeff (k + 2) ≤ (A * B).coeff (k + 1) ^ 2 := by
  have h1 := bprSum_nonneg hA hB k
  have h2 := bpr_identity (A := A) (B := B) k
  linarith

/-! ### Conclusion: BPR Lemma 2.43 -/

/-- **BPR Lemma 2.43.** The product of normal polynomials is normal. -/
theorem isNormal_mul {A B : R[X]} (hA : IsNormal A) (hB : IsNormal B) :
    IsNormal (A * B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact coeff_mul_nonneg hA.coeff_nonneg hB.coeff_nonneg
  · exact leadingCoeff_mul_pos hA.leading_pos hB.leading_pos
  · exact coeff_mul_log_concave hA hB
  · exact coeff_mul_no_gap hA hB

end Product

end Azurite.BPR
