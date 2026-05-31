import Azurite.BasuPollackRoy.Chapter2.Section2_1.HasNoNontrivialRealAlgebraicExtension
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_7
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# BPR Theorem 2.11 d) => a): No Non-trivial Real Algebraic Extension => Real Closed

**Theorem 2.11 (d => a) (BPR).** If R is a real field with no non-trivial real algebraic
extension, then R is real closed.

**Proof strategy.**
1. Show every nonzero sum of squares is a square (via AdjoinRoot(X²−c) being real).
2. Show `IsSquare a ∨ IsSquare (−a)` for all a (decompose −1 in AdjoinRoot(X²−a)).
3. Show every odd-degree polynomial has a root (strong induction, lifting from AdjoinRoot).
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial

variable {R : Type*} [Field R]

/-! ## Infrastructure: AdjoinRoot (X² - C a) -/

noncomputable def sqSubC (a : R) : R[X] := (X : R[X]) ^ 2 - C a

theorem irred_X_sq_sub_C {a : R} (ha : ¬ IsSquare a) :
    Irreducible (sqSubC a) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b; rw [sq]; exact fun h => ha ⟨b, h.symm⟩

theorem monic_sq_sub_C (a : R) : (sqSubC a).Monic :=
  monic_X_pow_sub_C a (by norm_num : (2 : ℕ) ≠ 0)

private theorem natDegree_sq_sub_C (a : R) : (sqSubC a).natDegree = 2 :=
  natDegree_X_pow_sub_C (R := R)

theorem adjoinRoot_isAlgebraic {p : R[X]} (hp : p.Monic) :
    Algebra.IsAlgebraic R (AdjoinRoot p) :=
  haveI : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  Algebra.IsAlgebraic.of_finite R _

theorem adjoinRoot_algebraMap_not_surjective {p : R[X]} (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) :
    ¬ Function.Surjective (algebraMap R (AdjoinRoot p)) := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj (AdjoinRoot.root p)
  have hpr : p.IsRoot r := by
    rw [Polynomial.IsRoot.def]
    have h1 : (algebraMap R (AdjoinRoot p)) (Polynomial.aeval r p) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply, hr, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    exact (algebraMap R (AdjoinRoot p)).injective (h1.trans (map_zero _).symm)
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hpr
  rcases hp.isUnit_or_isUnit hpq with h | h
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit h) (by simp)
  · have : p.natDegree = (X - C r).natDegree + q.natDegree := by
      rw [hpq]; exact Polynomial.natDegree_mul (monic_X_sub_C r).ne_zero (IsUnit.ne_zero h)
    rw [natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit h] at this; omega

/-! ## IsSumSq tools -/

theorem isSumSq_map_ringHom {S : Type*} [Semiring S] (f : R →+* S)
    {s : R} (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => simp [IsSumSq.zero]
  | sq_add a _ ih => simp [map_add, map_mul]; exact IsSumSq.sq_add (f a) ih

theorem isSumSq_inv_of_isSumSq [IsSemireal R]
    {c : R} (hc : IsSumSq c) (_ : c ≠ 0) : IsSumSq (c⁻¹) := by
  have : c⁻¹ = c * (c⁻¹ * c⁻¹) := by field_simp
  rw [this]; exact IsSumSq.mul hc (IsSumSq.mul_self c⁻¹)

/-! ## Core decomposition lemma -/

/-- `(root (X²−a))² = algebraMap a` -/
theorem root_sq_sub_C (a : R) [Fact (Irreducible (sqSubC a))] :
    (AdjoinRoot.root (sqSubC a)) ^ 2 = algebraMap R _ a := by
  have h : Polynomial.aeval (AdjoinRoot.root (sqSubC a)) (sqSubC a) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  unfold sqSubC at h ⊢
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  exact sub_eq_zero.mp h

/-- Every element of AdjoinRoot(X²−a) decomposes as x + y * root. -/
theorem repr_exists_sq_sub (a : R) [Fact (Irreducible (sqSubC a))]
    (z : AdjoinRoot (sqSubC a)) :
    ∃ x y : R, z = algebraMap R _ x + algebraMap R _ y * AdjoinRoot.root (sqSubC a) := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    set f := sqSubC a
    have hfm : f.Monic := monic_sq_sub_C a
    set r := p %ₘ f
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f r := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero (Fact.out : Irreducible f)),
          natDegree_sq_sub_C a]; norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    rw [hmk, show AdjoinRoot.mk f r = Polynomial.aeval (AdjoinRoot.root f) r from
      (AdjoinRoot.aeval_eq r).symm, hr_decomp]
    simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    exact ⟨r.coeff 0, r.coeff 1, by ring⟩

/-- The decomposition x + y * root is unique (injectivity of algebraMap + linear independence). -/
theorem repr_unique_sq_sub (a : R) [Fact (Irreducible (sqSubC a))]
    {x y : R} (h : algebraMap R _ x + algebraMap R _ y * AdjoinRoot.root (sqSubC a) = 0) :
    x = 0 ∧ y = 0 := by
  set f := sqSubC a
  have hmk : AdjoinRoot.mk f (C x + C y * X) = 0 := by
    have : AdjoinRoot.mk f (C x + C y * X) =
        AdjoinRoot.mk f (C x) + AdjoinRoot.mk f (C y) * AdjoinRoot.mk f X := by
      simp [map_add, map_mul]
    rw [this]; exact h
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hg_eq_zero : C x + C y * X = 0 := by
    by_contra hne
    have h1 : f.natDegree ≤ (C x + C y * X).natDegree :=
      Polynomial.natDegree_le_of_dvd hmk hne
    have h2 : (C x + C y * X).natDegree ≤ 1 := by
      apply le_trans (natDegree_add_le _ _)
      simp only [natDegree_C, Nat.zero_max]
      by_cases hy : y = 0
      · simp [hy]
      · rw [natDegree_C_mul_X y hy]
    rw [natDegree_sq_sub_C] at h1; omega
  constructor
  · have := congr_arg (Polynomial.coeff · 0) hg_eq_zero
    simp at this; exact this
  · have := congr_arg (Polynomial.coeff · 1) hg_eq_zero
    simp at this; exact this

/-- If −1 is a SoS in AdjoinRoot(X²−a), then −1 = Σ aᵢ² + a * Σ bᵢ² in R. -/
theorem decompose_neg_one_in_adjoinRoot {a : R} (ha : ¬ IsSquare a)
    (hns : ¬ IsSemireal (AdjoinRoot (sqSubC a))) :
    ∃ (n : ℕ) (xs ys : Fin n → R),
      -1 = ∑ i, xs i * xs i + a * ∑ i, ys i * ys i := by
  haveI : Fact (Irreducible (sqSubC a)) := ⟨irred_X_sq_sub_C ha⟩
  -- -1 is a sum of squares in AdjoinRoot
  have hss : IsSumSq (-1 : AdjoinRoot (sqSubC a)) := by
    rwa [← not_not (a := IsSumSq _), ← isSemireal_iff_not_isSumSq_neg_one]
  obtain ⟨n, z, hz⟩ := Azurite.BPR.isSumSq_exists_vector hss
  -- Decompose each zᵢ = algebraMap (xᵢ) + algebraMap (yᵢ) * root
  choose xs ys hzy using fun i => repr_exists_sq_sub a (z i)
  -- Compute ∑ zᵢ² = ∑(xᵢ² + a·yᵢ²) + (2·∑(xᵢ·yᵢ))·root
  set rt := AdjoinRoot.root (sqSubC a)
  have hrt2 : rt ^ 2 = algebraMap R _ a := root_sq_sub_C a
  have hsq : ∀ i, z i * z i = algebraMap R _ (xs i * xs i + a * (ys i * ys i)) +
      algebraMap R _ (2 * (xs i * ys i)) * rt := by
    intro i; rw [hzy i]
    have step1 : (algebraMap R (AdjoinRoot (sqSubC a)) (xs i) +
        algebraMap R (AdjoinRoot (sqSubC a)) (ys i) * rt) *
        (algebraMap R (AdjoinRoot (sqSubC a)) (xs i) +
        algebraMap R (AdjoinRoot (sqSubC a)) (ys i) * rt) =
        algebraMap R _ (xs i) * algebraMap R _ (xs i) +
        algebraMap R _ (ys i) * algebraMap R _ (ys i) * (rt * rt) +
        (algebraMap R _ (xs i) * algebraMap R _ (ys i) +
         algebraMap R _ (xs i) * algebraMap R _ (ys i)) * rt := by ring
    rw [step1, show rt * rt = rt ^ 2 from (sq rt).symm, hrt2]
    simp only [map_add, map_mul, map_ofNat]; ring
  have hsum : ∑ i, z i * z i =
      algebraMap R _ (∑ i, (xs i * xs i + a * (ys i * ys i))) +
      algebraMap R _ (∑ i, 2 * (xs i * ys i)) * rt := by
    simp_rw [hsq, map_sum, Finset.sum_add_distrib, Finset.sum_mul]
  have hm1 : algebraMap R (AdjoinRoot (sqSubC a)) (-1) +
      algebraMap R (AdjoinRoot (sqSubC a)) 0 * rt =
      algebraMap R _ (∑ i, (xs i * xs i + a * (ys i * ys i))) +
      algebraMap R _ (∑ i, 2 * (xs i * ys i)) * rt := by
    simp [hz, hsum]
  have hdiff : algebraMap R _ (-1 - ∑ i, (xs i * xs i + a * (ys i * ys i))) +
      algebraMap R _ (0 - ∑ i, 2 * (xs i * ys i)) * rt = 0 := by
    have h1 : algebraMap R (AdjoinRoot (sqSubC a)) (-1 - ∑ i, (xs i * xs i + a * (ys i * ys i))) =
        algebraMap R _ (-1) - algebraMap R _ (∑ i, (xs i * xs i + a * (ys i * ys i))) := map_sub _ _ _
    have h2 : algebraMap R (AdjoinRoot (sqSubC a)) (0 - ∑ i, 2 * (xs i * ys i)) =
        algebraMap R _ 0 - algebraMap R _ (∑ i, 2 * (xs i * ys i)) := map_sub _ _ _
    rw [h1, h2]; linear_combination hm1
  obtain ⟨heq1, _⟩ := repr_unique_sq_sub a hdiff
  refine ⟨n, xs, ys, ?_⟩
  have h1 : -1 = ∑ i, (xs i * xs i + a * (ys i * ys i)) := sub_eq_zero.mp heq1
  rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## Part 1: isSquare_or_isSquare_neg -/

/-- If c is a nonzero SoS, then AdjoinRoot(X²−c) is semireal. -/
private theorem adjoinRoot_sq_sub_isSemireal_of_isSumSq
    {c : R} (hc : IsSumSq c) (hc_sq : ¬ IsSquare c) (hR_real : Azurite.BPR.IsRealField R) :
    IsSemireal (AdjoinRoot (sqSubC c)) := by
  rw [isSemireal_iff_not_isSumSq_neg_one]
  intro hss
  have hns : ¬ IsSemireal (AdjoinRoot (sqSubC c)) :=
    fun h => (isSemireal_iff_not_isSumSq_neg_one.mp h) hss
  obtain ⟨n, xs, ys, hdecomp⟩ := decompose_neg_one_in_adjoinRoot hc_sq hns
  have h1 : IsSumSq (∑ i : Fin n, xs i * xs i : R) := IsSumSq.sum_mul_self Finset.univ _
  have h2 : IsSumSq (c * ∑ i : Fin n, ys i * ys i : R) :=
    IsSumSq.mul hc (IsSumSq.sum_mul_self Finset.univ _)
  have : IsSumSq (-1 : R) := hdecomp ▸ IsSumSq.add h1 h2
  exact (Azurite.BPR.isRealField_iff R).mp hR_real this

/-- Every nonzero SoS is a square. -/
theorem sum_sq_isSquare (hR : Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R)
    {c : R} (hc : IsSumSq c) (_hc_ne : c ≠ 0) : IsSquare c := by
  obtain ⟨hR1, hR2⟩ := hR
  by_contra hns
  have hirr := irred_X_sq_sub_C hns
  haveI : Fact (Irreducible (sqSubC c)) := ⟨hirr⟩
  have halg := adjoinRoot_isAlgebraic (monic_sq_sub_C c)
  have hnsurj := adjoinRoot_algebraMap_not_surjective hirr
    (by rw [natDegree_sq_sub_C]; norm_num)
  have hreal : IsSemireal (AdjoinRoot (sqSubC c)) :=
    adjoinRoot_sq_sub_isSemireal_of_isSumSq hc hns hR1
  exact hnsurj (hR2 (AdjoinRoot (sqSubC c)) halg hreal)

/-- Every element or its negation is a square. -/
theorem isSquare_or_isSquare_neg_of_noext
    (hR : Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R)
    (x : R) : IsSquare x ∨ IsSquare (-x) := by
  obtain ⟨hR1, hR2⟩ := hR
  by_cases hx : IsSquare x
  · exact Or.inl hx
  · right
    have hx_ne : x ≠ 0 := fun h => hx ⟨0, by simp [h]⟩
    have hirr := irred_X_sq_sub_C hx
    haveI : Fact (Irreducible (sqSubC x)) := ⟨hirr⟩
    have halg := adjoinRoot_isAlgebraic (monic_sq_sub_C x)
    have hnsurj := adjoinRoot_algebraMap_not_surjective hirr
      (by rw [natDegree_sq_sub_C]; norm_num)
    have hns : ¬ IsSemireal (AdjoinRoot (sqSubC x)) :=
      fun hsem => hnsurj (hR2 (AdjoinRoot (sqSubC x)) halg hsem)
    obtain ⟨n, xs, ys, hdecomp⟩ := decompose_neg_one_in_adjoinRoot hx hns
    have hy_ne : ∑ i : Fin n, ys i * ys i ≠ 0 := by
      intro h; rw [h, mul_zero, add_zero] at hdecomp
      exact (Azurite.BPR.isRealField_iff R).mp hR1
        (hdecomp ▸ IsSumSq.sum_mul_self Finset.univ _)
    have hIsSumSq_neg_x : IsSumSq (-x) := by
      have heq : -x = (1 + ∑ i : Fin n, xs i * xs i) *
          (∑ i : Fin n, ys i * ys i)⁻¹ := by
        rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hy_ne]; linear_combination -hdecomp
      rw [heq]
      haveI : IsSemireal R := hR1
      apply IsSumSq.mul
      · have := IsSumSq.sq_add 1 (IsSumSq.sum_mul_self Finset.univ xs)
        simpa [one_mul] using this
      · exact isSumSq_inv_of_isSumSq (IsSumSq.sum_mul_self Finset.univ _) hy_ne
    exact sum_sq_isSquare ⟨hR1, hR2⟩ hIsSumSq_neg_x (neg_ne_zero.mpr hx_ne)

/-! ## Part 2: Every odd-degree polynomial has a root -/

/-- In a semireal field, a² + (sum of squares) ≠ 0 when a ≠ 0. -/
private theorem sq_add_isSumSq_ne_zero [IsSemireal R] {a : R} (ha : a ≠ 0)
    {s : R} (hs : IsSumSq s) : a * a + s ≠ 0 := by
  intro h
  have hs_neg : IsSumSq (-(a * a)) := by
    have : -(a * a) = s := neg_eq_of_add_eq_zero_right h; rw [this]; exact hs
  have hinv : IsSumSq ((a * a)⁻¹) := by
    rw [show (a * a)⁻¹ = (a * a) * ((a * a)⁻¹ * (a * a)⁻¹) from by field_simp]
    exact IsSumSq.mul (IsSumSq.mul_self a) (IsSumSq.mul_self _)
  exact (isSemireal_iff_not_isSumSq_neg_one.mp ‹IsSemireal R›) (by
    rw [show (-1 : R) = -(a * a) * (a * a)⁻¹ from by field_simp]
    exact IsSumSq.mul hs_neg hinv)

/-- A nonzero sum of squares in R[X] has even degree (when R is semireal). -/
private theorem even_natDegree_isSumSq [IsSemireal R]
    {S : R[X]} (hS : IsSumSq S) (hne : S ≠ 0) :
    Even S.natDegree ∧ IsSumSq S.leadingCoeff := by
  induction hS with
  | zero => exact absurd rfl hne
  | sq_add a hS' ih =>
    rename_i S'
    by_cases ha : a = 0
    · simp only [ha, zero_mul, zero_add] at hne ⊢; exact ih hne
    by_cases hS'_ne : S' = 0
    · subst hS'_ne; simp only [add_zero]
      refine ⟨⟨a.natDegree, natDegree_mul ha ha⟩, ?_⟩
      show IsSumSq (a * a).leadingCoeff
      rw [leadingCoeff_mul]; exact IsSumSq.mul_self _
    · obtain ⟨heven', hlc'⟩ := ih hS'_ne
      rcases lt_trichotomy (a * a).natDegree S'.natDegree with hlt | heq | hgt
      · rw [show a * a + S' = S' + a * a from add_comm _ _]
        refine ⟨natDegree_add_eq_left_of_natDegree_lt hlt ▸ heven', ?_⟩
        rw [Polynomial.leadingCoeff, natDegree_add_eq_left_of_natDegree_lt hlt,
            coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hlt, add_zero]
        exact hlc'
      · have hlc_ne : (a * a + S').coeff (a * a).natDegree ≠ 0 := by
          rw [coeff_add, ← Polynomial.leadingCoeff, leadingCoeff_mul]
          rw [show S'.coeff (a * a).natDegree = S'.leadingCoeff from by
            rw [Polynomial.leadingCoeff, heq]]
          exact sq_add_isSumSq_ne_zero (leadingCoeff_ne_zero.mpr ha) hlc'
        have hnd : (a * a + S').natDegree = (a * a).natDegree :=
          le_antisymm (le_trans (natDegree_add_le _ _) (by omega))
            (Polynomial.le_natDegree_of_ne_zero hlc_ne)
        refine ⟨hnd ▸ ⟨a.natDegree, natDegree_mul ha ha⟩, ?_⟩
        rw [Polynomial.leadingCoeff, hnd, coeff_add,
            ← Polynomial.leadingCoeff, leadingCoeff_mul]
        rw [show S'.coeff (a * a).natDegree = S'.leadingCoeff from by
          rw [Polynomial.leadingCoeff, heq]]
        exact IsSumSq.sq_add _ hlc'
      · refine ⟨natDegree_add_eq_left_of_natDegree_lt hgt ▸ ⟨a.natDegree, natDegree_mul ha ha⟩, ?_⟩
        rw [Polynomial.leadingCoeff, natDegree_add_eq_left_of_natDegree_lt hgt,
            coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hgt, add_zero,
            ← Polynomial.leadingCoeff, leadingCoeff_mul]
        exact IsSumSq.mul_self _

/-- R[X] is semireal when R is semireal. -/
private theorem polynomial_isSemireal [IsSemireal R] : IsSemireal R[X] := by
  rw [isSemireal_iff_not_isSumSq_neg_one]
  intro hss
  have key : ∀ (s : R[X]), IsSumSq s → IsSumSq (eval (0 : R) s) := by
    intro s hs; induction hs with
    | zero => simp [IsSumSq.zero]
    | sq_add a _ ih => simp [eval_add, eval_mul]; exact IsSumSq.sq_add _ ih
  have heval := key _ hss
  simp at heval
  exact (isSemireal_iff_not_isSumSq_neg_one.mp ‹IsSemireal R›) heval

/-- AdjoinRoot of a nonzero polynomial is algebraic. -/
private theorem adjoinRoot_isAlgebraic' {p : R[X]} (hp : p ≠ 0) :
    Algebra.IsAlgebraic R (AdjoinRoot p) := by
  haveI : Module.Finite R (AdjoinRoot p) := (AdjoinRoot.powerBasis hp).finite
  exact Algebra.IsAlgebraic.of_finite R _

/-- Every polynomial of odd degree has a root. -/
theorem exists_isRoot_of_odd_natDegree_of_noext
    (hR : Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R)
    {P : R[X]} (hodd : Odd P.natDegree) : ∃ x, P.IsRoot x := by
  obtain ⟨hR1, hR2⟩ := hR
  -- Strong induction on degree
  suffices ∀ n, ∀ (Q : R[X]), Q.natDegree = n → Odd n → ∃ x, Q.IsRoot x from
    this P.natDegree P rfl hodd
  intro n; exact Nat.strong_induction_on n fun d ih Q hQd hodd_d => by
    have hQ_ne : Q ≠ 0 := by
      intro h; subst h; simp at hQd; subst hQd; exact Nat.not_odd_zero hodd_d
    have hdeg_pos : 0 < d := Nat.pos_of_ne_zero (by intro h; subst h; exact Nat.not_odd_zero hodd_d)
    -- Degree 1: linear polynomial
    rcases eq_or_lt_of_le (Nat.one_le_of_lt hdeg_pos) with hd1 | hd1
    · have hd_eq : Q.natDegree = 1 := by omega
      exact ⟨-(Q.coeff 0) * (Q.coeff 1)⁻¹, by
        have hc1 : Q.coeff 1 ≠ 0 := by
          rw [show (1 : ℕ) = Q.natDegree from hd_eq.symm]
          exact leadingCoeff_ne_zero.mpr hQ_ne
        have hP := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hd_eq)
        rw [Polynomial.IsRoot.def, hP]; simp [eval_add, eval_mul, eval_C, eval_X]; field_simp; ring⟩
    · -- Degree ≥ 2
      by_cases hirr : Irreducible Q
      · -- IRREDUCIBLE CASE: derive contradiction
        exfalso
        haveI : Fact (Irreducible Q) := ⟨hirr⟩
        have halg := adjoinRoot_isAlgebraic' hirr.ne_zero
        have hnsurj := adjoinRoot_algebraMap_not_surjective hirr (by omega)
        have hns : ¬ IsSemireal (AdjoinRoot Q) :=
          fun hsem => hnsurj (hR2 _ halg hsem)
        have hss : IsSumSq (-1 : AdjoinRoot Q) := by
          rwa [← not_not (a := IsSumSq _), ← isSemireal_iff_not_isSumSq_neg_one]
        obtain ⟨m, z, hz⟩ := Azurite.BPR.isSumSq_exists_vector hss
        -- Choose polynomial representatives and reduce mod Q
        choose g hg using fun i => (AdjoinRoot.mk_surjective (z i))
        set g' : Fin m → R[X] := fun i => (g i) % Q
        have hg'_mk : ∀ i, AdjoinRoot.mk Q (g' i) = z i := by
          intro i
          have hdiv : AdjoinRoot.mk Q (Q * ((g i) / Q)) = 0 := by
            simp [map_mul, AdjoinRoot.mk_self]
          have heq := EuclideanDomain.div_add_mod (g i) Q
          have : AdjoinRoot.mk Q (g' i) = AdjoinRoot.mk Q (g i) := by
            have : AdjoinRoot.mk Q (g i) = AdjoinRoot.mk Q (Q * ((g i) / Q) + g' i) := by
              congr 1; exact heq.symm
            rw [this, map_add, hdiv, zero_add]
          rw [this, hg i]
        have hg'_deg : ∀ i, (g' i).degree < Q.degree :=
          fun i => Polynomial.degree_mod_lt (g i) hQ_ne
        -- Build sum of squares + 1
        set S := ∑ i : Fin m, g' i * g' i
        have hS_sos : IsSumSq S := IsSumSq.sum_mul_self Finset.univ g'
        -- AdjoinRoot.mk Q (S + 1) = 0
        have hS1_mk : AdjoinRoot.mk Q (S + 1) = 0 := by
          rw [map_add, map_one]
          have : AdjoinRoot.mk Q S = ∑ i, (z i * z i) := by
            simp only [S, map_sum, map_mul, hg'_mk]
          rw [this, ← hz]; ring
        -- Q | (S + 1)
        rw [AdjoinRoot.mk_eq_zero] at hS1_mk
        obtain ⟨T, hST⟩ := hS1_mk
        -- S + 1 ≠ 0 (R[X] is semireal)
        haveI : IsSemireal R := hR1
        have hS1_ne : S + 1 ≠ 0 := by
          intro h
          have hS_eq : S = -1 := by linear_combination h
          exact (isSemireal_iff_not_isSumSq_neg_one.mp polynomial_isSemireal) (hS_eq ▸ hS_sos)
        -- T ≠ 0
        have hT_ne : T ≠ 0 := right_ne_zero_of_mul (hST ▸ hS1_ne)
        -- S ≠ 0 (if S = 0 then S+1 = 1 = Q*T, but deg Q ≥ 3)
        have hS_ne : S ≠ 0 := by
          intro h; rw [h, zero_add] at hST
          have : Q.natDegree + T.natDegree = 0 := by
            rw [← natDegree_mul hQ_ne hT_ne, ← hST, natDegree_one]
          omega
        -- S has even degree
        obtain ⟨hS_even, _⟩ := even_natDegree_isSumSq hS_sos hS_ne
        -- S.natDegree > 0 (if 0, then S+1 is constant but Q*T has deg ≥ 3)
        have hS_deg_pos : 0 < S.natDegree := by
          by_contra h; simp only [not_lt, Nat.le_zero] at h
          have : (S + 1).natDegree ≤ 0 :=
            le_trans (natDegree_add_le _ _) (by simp [h])
          rw [hST, natDegree_mul hQ_ne hT_ne] at this; omega
        -- natDegree(S + 1) = natDegree(S)
        have hS1_deg : (S + 1).natDegree = S.natDegree :=
          natDegree_add_eq_left_of_natDegree_lt (by simp; exact hS_deg_pos)
        -- S.natDegree = Q.natDegree + T.natDegree
        have hQT_deg : S.natDegree = Q.natDegree + T.natDegree := by
          rw [← hS1_deg, hST, natDegree_mul hQ_ne hT_ne]
        -- Bound: S.natDegree ≤ 2*(d-1)
        have hS_deg_bound : S.natDegree ≤ 2 * (d - 1) := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i _
          by_cases hgi : g' i = 0
          · simp [hgi]
          · have hgi_nd : (g' i).natDegree < Q.natDegree := by
              have := hg'_deg i
              rwa [Polynomial.degree_eq_natDegree hgi,
                   Polynomial.degree_eq_natDegree hQ_ne,
                   Nat.cast_lt (α := WithBot ℕ)] at this
            rw [hQd] at hgi_nd
            have := natDegree_mul hgi hgi
            omega
        -- T has odd degree and T.natDegree < d
        have hT_odd : Odd T.natDegree := by
          obtain ⟨k, hk⟩ := hS_even
          obtain ⟨j, hj⟩ := hodd_d
          rw [hQd] at hQT_deg
          exact ⟨k - j - 1, by omega⟩
        have hT_lt : T.natDegree < d := by omega
        -- Apply IH to T to get a root x
        obtain ⟨x, hx⟩ := ih T.natDegree hT_lt T rfl hT_odd
        -- Evaluate: (S + 1)(x) = (Q * T)(x) = Q(x) * T(x) = Q(x) * 0 = 0
        have heval : (S + 1).eval x = 0 := by
          rw [hST, eval_mul, hx, mul_zero]
        -- But (S+1)(x) = ∑ g'ᵢ(x)² + 1, so -1 = ∑ g'ᵢ(x)²
        have : IsSumSq (-1 : R) := by
          have hS_eval : S.eval x = ∑ i : Fin m, (g' i).eval x * (g' i).eval x := by
            simp [S, eval_finsetSum, eval_mul]
          have hS1_eval : (S + 1).eval x = 0 := heval
          rw [eval_add, eval_one] at hS1_eval
          have hSx : S.eval x = -1 := by linear_combination hS1_eval
          have h1 : (-1 : R) = ∑ i : Fin m, (g' i).eval x * (g' i).eval x := by
            rw [← hSx, hS_eval]
          rw [h1]; exact IsSumSq.sum_mul_self Finset.univ _
        exact (Azurite.BPR.isRealField_iff R).mp hR1 this
      · -- REDUCIBLE CASE: factor and find odd-degree factor
        have hQ_not_unit : ¬ IsUnit Q := by
          intro h; exact absurd (Polynomial.natDegree_eq_zero_of_isUnit h) (by omega)
        have hirr' : ∃ a b : R[X], Q = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
          by_contra hall
          apply hirr
          constructor
          · exact hQ_not_unit
          · intro a b hab
            by_contra hnor
            rw [not_or] at hnor
            exact hall ⟨a, b, hab, hnor.1, hnor.2⟩
        obtain ⟨a, b, hab, ha_nu, hb_nu⟩ := hirr'
        have ha_ne : a ≠ 0 := fun h => hQ_ne (by rw [hab, h, zero_mul])
        have hb_ne : b ≠ 0 := fun h => hQ_ne (by rw [hab, h, mul_zero])
        have hab_deg : a.natDegree + b.natDegree = d := by
          rw [← hQd, hab, natDegree_mul ha_ne hb_ne]
        have ha_deg : 0 < a.natDegree := by
          by_contra h; simp only [not_lt, Nat.le_zero] at h
          exact ha_nu (Polynomial.isUnit_iff.mpr ⟨a.coeff 0,
            Ne.isUnit (fun hc => ha_ne (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero])),
            (eq_C_of_natDegree_eq_zero h).symm⟩)
        have hb_deg : 0 < b.natDegree := by
          by_contra h; simp only [not_lt, Nat.le_zero] at h
          exact hb_nu (Polynomial.isUnit_iff.mpr ⟨b.coeff 0,
            Ne.isUnit (fun hc => hb_ne (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero])),
            (eq_C_of_natDegree_eq_zero h).symm⟩)
        -- One factor has odd degree (sum of two positives is odd → one is odd)
        rcases Nat.even_or_odd a.natDegree with ha_even | ha_odd
        · -- a even → b odd (since sum is odd)
          have hb_odd : Odd b.natDegree := by
            obtain ⟨k, hk⟩ := ha_even
            obtain ⟨j, hj⟩ := hodd_d
            exact ⟨j - k, by omega⟩
          obtain ⟨x, hx⟩ := ih b.natDegree (by omega) b rfl hb_odd
          exact ⟨x, by rw [hab, Polynomial.IsRoot.def, eval_mul, hx, mul_zero]⟩
        · -- a odd
          obtain ⟨x, hx⟩ := ih a.natDegree (by omega) a rfl ha_odd
          exact ⟨x, by rw [hab, Polynomial.IsRoot.def, eval_mul, hx, zero_mul]⟩

/-! ## Main theorem -/

/-- **BPR Theorem 2.11 (d => a).** If R has no non-trivial real algebraic extension,
    then R is real closed. -/
theorem theorem_2_11_d_a (hR : Azurite.BPR.HasNoNontrivialRealAlgebraicExtension R) :
    IsRealClosed R where
  toIsSemireal := hR.1
  isSquare_or_isSquare_neg := isSquare_or_isSquare_neg_of_noext hR
  exists_isRoot_of_odd_natDegree := fun hf => exists_isRoot_of_odd_natDegree_of_noext hR hf

end Azurite.BPR.Theorem2_11
