import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Lagrange
import Azurite.BasuPollackRoy.Chapter2.Section2_1

/-!
# BPR Theorem 2.11 a) ⇒ b): Real Closed ⟹ R[i] Algebraically Closed

**Theorem 2.11 (BPR).** If R is a real closed field, then
R[i] := R[X]/(X² + 1) is an algebraically closed field.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial

/-! ### R[i] = R[X]/(X² + 1) -/

/-- R[i] := R[X]/(X² + 1), the "complex numbers" over a real closed field R. -/
noncomputable abbrev Ri (R : Type*) [CommRing R] :=
  AdjoinRoot (X ^ 2 + 1 : R[X])

/-- The imaginary unit `i` in R[i], i.e., the image of X in R[X]/(X² + 1). -/
noncomputable def Ri.i (R : Type*) [CommRing R] : Ri R :=
  AdjoinRoot.root (X ^ 2 + 1 : R[X])

/-- Conjugation on R[i]: the R-algebra automorphism sending i ↦ −i. -/
noncomputable def Ri.conj (R : Type*) [CommRing R] : Ri R →ₐ[R] Ri R :=
  { AdjoinRoot.lift (AdjoinRoot.of (X ^ 2 + 1 : R[X])) (-Ri.i R)
      (by
        simp only [Ri.i, eval₂_add, eval₂_pow, eval₂_one, eval₂_X, neg_sq]
        have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : R[X])
        simpa [eval₂_add, eval₂_pow, eval₂_one, eval₂_X] using h) with
    commutes' := fun r => by simp [AdjoinRoot.lift_of] }

/-- Apply conjugation to the coefficients of a polynomial over R[i]. -/
noncomputable def conjPoly (R : Type*) [CommRing R] : (Ri R)[X] → (Ri R)[X] :=
  Polynomial.map (Ri.conj R)

/-! ### Combinatorial indexing -/

/-- The set of ordered pairs (i, j) with i < j from Fin p. -/
def strictPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-! ### The polynomials Q, D, F, G, H -/

variable {L : Type*} [Field L] {p : ℕ}

/-- γ_{ij}(Z) = x_i + x_j + Z · x_i · x_j ∈ L[Z].
    Here Z is the polynomial indeterminate. -/
noncomputable def gammaPoly (x : Fin p → L) (i j : Fin p) : L[X] :=
  Polynomial.C (x i + x j) + Polynomial.X * Polynomial.C (x i * x j)

/-- Q(Z, Y) = ∏_{i < j} (Y − γ_{ij}(Z)) ∈ L[Z][Y].
    The outer polynomial ring is in Y; coefficients are polynomials in Z. -/
noncomputable def QPolynomial (x : Fin p → L) : (L[X])[X] :=
  ∏ ij ∈ strictPairs p,
    (Polynomial.X - Polynomial.C (gammaPoly x ij.1 ij.2))

/-- D(Z) = ∏_{a ≠ b in strictPairs} (γ_a(Z) − γ_b(Z)) ∈ L[Z].
    This is (up to sign) the square of the standard discriminant of Q w.r.t. Y.
    D(z) ≠ 0 iff all γ_{ij}(z) are distinct. -/
noncomputable def discPoly (x : Fin p → L) : L[X] :=
  ∏ ab ∈ (strictPairs p).offDiag,
    (gammaPoly x ab.1.1 ab.1.2 - gammaPoly x ab.2.1 ab.2.2)

/-- F(Z, Y) = ∂Q/∂Y, the formal derivative of Q with respect to Y. -/
noncomputable def FPoly (x : Fin p → L) : (L[X])[X] :=
  Polynomial.derivative (QPolynomial x)

/-- G(Z, Y) = ∑_{i<j} (x_i + x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i + x_j. -/
noncomputable def GPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 + x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-- H(Z, Y) = ∑_{i<j} (x_i · x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i · x_j. -/
noncomputable def HPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 * x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-! ### Infrastructure lemmas -/

variable {R : Type*} [Field R]

/-- In a real closed field, −1 is not a square. -/
theorem not_isSquare_neg_one [IsRealClosed R] : ¬ IsSquare (-1 : R) := by
  intro h
  exact IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- X² + 1 is irreducible over a real closed field R. -/
theorem irred_X_sq_add_one [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
    simp [this, Finset.mem_Icc]
  · intro x
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    intro h
    have : (-1 : R) = x * x := by linear_combination -h
    exact not_isSquare_neg_one ⟨x, this⟩

/-- X² + 1 is irreducible (as a Fact, for AdjoinRoot.instField). -/
instance [IsRealClosed R] : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irred_X_sq_add_one⟩

/-- The defining relation: i² = −1 in R[i]. -/
theorem Ri.i_sq (R : Type*) [CommRing R] :
    (Ri.i R) ^ 2 = -(1 : Ri R) := by
  have h : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1 : R[X]) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  unfold Ri.i
  linear_combination h

/-- For any a ∈ R, there exists v ∈ R[i] with v² = a. -/
theorem sqrt_of_R_in_Ri [IsRealClosed R] (a : R) :
    ∃ v : Ri R, v ^ 2 = algebraMap R (Ri R) a := by
  rcases IsRealClosed.isSquare_or_isSquare_neg a with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨algebraMap R (Ri R) c, by
      rw [sq]; simp only [← map_mul, hc]⟩
  · refine ⟨algebraMap R (Ri R) c * Ri.i R, ?_⟩
    rw [mul_pow, Ri.i_sq]
    simp only [sq, ← map_mul, mul_neg, mul_one, ← map_neg]
    have : -(c * c) = a := by rw [← hc, neg_neg]
    simp only [this]

/-! ### Degree arithmetic -/

/-- If p = 2^m · n with m ≥ 1 and n odd, then p(p−1)/2 = 2^{m−1} · n' with n' odd. -/
theorem half_degree_odd_factor {m n : ℕ} (hm : 1 ≤ m) (hn : Odd n) (hp : 0 < n) :
    ∃ n' : ℕ, Odd n' ∧ 2 ^ m * n * (2 ^ m * n - 1) / 2 = 2 ^ (m - 1) * n' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst hk
  simp only [Nat.succ_sub_one]
  refine ⟨n * (2 ^ (k + 1) * n - 1), ?_, ?_⟩
  · apply Odd.mul hn
    refine Nat.Even.sub_odd ?_ ?_ odd_one
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact Even.mul_right ⟨2 ^ k, by ring⟩ n
  · rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by ring]
    rw [show 2 * 2 ^ k * n * (2 * 2 ^ k * n - 1) =
        2 * (2 ^ k * n * (2 * 2 ^ k * n - 1)) from by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    ring

/-! ### Conjugation properties -/

variable {R : Type*} [Field R]

/-- Conjugation is an involution: conj (conj z) = z. -/
theorem Ri.conj_conj [IsRealClosed R] (z : Ri R) :
    (Ri.conj R) ((Ri.conj R) z) = z := by
  have h : (Ri.conj R).comp (Ri.conj R) = AlgHom.id R (Ri R) := by
    apply AdjoinRoot.algHom_ext
    simp only [Ri.conj, AlgHom.comp_apply, AlgHom.coe_mk, Ri.i,
      AdjoinRoot.lift_root, map_neg, neg_neg, AlgHom.id_apply]
  exact AlgHom.congr_fun h z

/-- Conjugation fixes elements of R: conj (algebraMap R (Ri R) r) = algebraMap R (Ri R) r. -/
theorem Ri.conj_algebraMap [IsRealClosed R] (r : R) :
    (Ri.conj R) (algebraMap R (Ri R) r) = algebraMap R (Ri R) r :=
  (Ri.conj R).commutes r

/-- Polynomial evaluation commutes with conjugation:
    If P ∈ Ri[X] and z ∈ Ri, then conj(P(z)) = P̄(conj(z)). -/
theorem conj_eval_eq_eval_conj_map [IsRealClosed R]
    (P : (Ri R)[X]) (z : Ri R) :
    (Ri.conj R) (P.eval z) = (conjPoly R P).eval ((Ri.conj R) z) := by
  simp only [conjPoly, Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, eval₂_add]
    rw [hp, hq]
  | monomial n a =>
    simp only [eval_monomial, map_mul, map_pow, eval₂_monomial, RingHom.coe_coe]

/-- If P ∈ R[i][X] has coefficients in R, then conjPoly(P) = P.
    (Since conj fixes R.) -/
theorem conjPoly_eq_self_of_mem_R [IsRealClosed R] (P : R[X]) :
    conjPoly R (P.map (algebraMap R (Ri R))) = P.map (algebraMap R (Ri R)) := by
  simp only [conjPoly, Polynomial.map_map]
  congr 1
  ext r
  exact Ri.conj_algebraMap r

/-- conjPoly is an involution: applying conjugation to coefficients twice gives back the original. -/
theorem conjPoly_conjPoly [IsRealClosed R] (P : (Ri R)[X]) :
    conjPoly R (conjPoly R P) = P := by
  simp only [conjPoly, Polynomial.map_map]
  have h : ((Ri.conj R : Ri R →+* Ri R).comp (Ri.conj R)) = RingHom.id (Ri R) :=
    RingHom.ext (fun z => Ri.conj_conj z)
  rw [h, Polynomial.map_id]

/-- P · conjPoly(P) is fixed by conjPoly. -/
theorem conjPoly_mul_conjPoly_eq [IsRealClosed R] (P : (Ri R)[X]) :
    conjPoly R (P * conjPoly R P) = conjPoly R P * P := by
  simp only [conjPoly, Polynomial.map_mul, Polynomial.map_map]
  congr 1
  have h : ((Ri.conj R : Ri R →+* Ri R).comp (Ri.conj R)) = RingHom.id (Ri R) :=
    RingHom.ext (fun z => Ri.conj_conj z)
  rw [h, Polynomial.map_id]

/-- Each coefficient of P · conjPoly(P) is fixed by conj. -/
theorem conj_coeff_mul_conjPoly [IsRealClosed R] (P : (Ri R)[X]) (n : ℕ) :
    (Ri.conj R) ((P * conjPoly R P).coeff n) = (P * conjPoly R P).coeff n := by
  have key : conjPoly R (P * conjPoly R P) = P * conjPoly R P := by
    rw [conjPoly_mul_conjPoly_eq, mul_comm]
  have := congr_arg (fun q => q.coeff n) key
  simp only [conjPoly, Polynomial.coeff_map] at this
  exact this

/-! ### Nonzero polynomial evaluation -/

/-- A nonzero polynomial over an infinite integral domain has a non-root.
    This is used to find z with D(z) ≠ 0. -/
theorem exists_eval_ne_zero {K : Type*} [CommRing K] [IsDomain K] [Infinite K]
    (P : K[X]) (hP : P ≠ 0) : ∃ x : K, P.eval x ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (Polynomial.zero_of_eval_zero P h)

/-! ### Symmetric polynomial membership (Q, G, H ∈ R[Z][Y])

These use `proposition_2_16` from Section2_1: if P ∈ R[X] splits as ∏(X − xᵢ)
over C, then any symmetric polynomial in the xᵢ with coefficients in R
evaluates to an element of R.

The γ_{ij}(Z) = xᵢ + xⱼ + Z·xᵢxⱼ are symmetric in the roots; products and
sums of symmetric expressions remain symmetric. Therefore the coefficients of
Q, G, H (as polynomials in Y) lie in R[Z]. -/

variable {R : Type*} [Field R] {L : Type*} [Field L] [Algebra R L]

/-- A polynomial f ∈ L[X] lies in the image of R[X] → L[X] if and only if
    all its coefficients are in the image of algebraMap R L. -/
theorem poly_in_image_iff_coeffs_in_range
    (f : L[X]) :
    (∃ g : R[X], g.map (algebraMap R L) = f) ↔
    ∀ n : ℕ, f.coeff n ∈ Set.range (algebraMap R L) := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨g.coeff n, (Polynomial.coeff_map _ n).symm⟩
  · intro h
    choose c hc using h
    refine ⟨⟨⟨f.support, c, fun n => ?_⟩⟩, ?_⟩
    · simp only [Polynomial.mem_support_iff]
      constructor
      · intro hn
        rwa [← hc n, ← map_zero (algebraMap R L),
          (algebraMap R L).injective.ne_iff] at hn
      · intro hn
        rwa [← hc n, map_ne_zero_iff _ (algebraMap R L).injective]
    · ext n; simp [Polynomial.coeff_map, hc n]

/-- If a polynomial f ∈ L[X] evaluates into the range of `algebraMap R L` at every
    R-point, then each coefficient of f lies in the range.
    Requires R to be an infinite integral domain. -/
theorem eval_range_implies_coeff_range [Infinite R] [IsDomain R]
    (f : L[X])
    (hf : ∀ r : R, f.eval (algebraMap R L r) ∈ Set.range (algebraMap R L))
    (n : ℕ) : f.coeff n ∈ Set.range (algebraMap R L) := by
  classical
  -- Choose preimages: for each r, φ(r) ∈ R with algebraMap(φ(r)) = f.eval(algebraMap r)
  choose φ hφ using hf
  set d := f.natDegree
  -- Pick d+1 distinct R-elements via Infinite.natEmbedding
  set v : Fin (d + 1) → R := (Infinite.natEmbedding R) ∘ Fin.val
  have hv_inj : Set.InjOn v ↑(Finset.univ : Finset (Fin (d + 1))) := by
    intro i _ j _ hij
    exact Fin.ext ((Infinite.natEmbedding R).injective hij)
  -- Build Lagrange interpolant h ∈ R[X]
  set h := (Lagrange.interpolate Finset.univ v) (φ ∘ v)
  -- h has degree < d+1
  have hdeg_h : h.degree < ↑(d + 1) := by
    have := Lagrange.degree_interpolate_lt (φ ∘ v) hv_inj
    rwa [Finset.card_univ, Fintype.card_fin] at this
  -- h.eval(vᵢ) = φ(vᵢ)
  have heval_h : ∀ i : Fin (d + 1), eval (v i) h = φ (v i) :=
    fun i => Lagrange.eval_interpolate_at_node _ hv_inj (Finset.mem_univ i)
  -- Injectivity for the image finset
  have hav_inj : Set.InjOn (algebraMap R L ∘ v) ↑(Finset.univ : Finset (Fin (d + 1))) := by
    intro i _ j _ hij
    exact hv_inj (Finset.mem_univ i) (Finset.mem_univ j) ((algebraMap R L).injective hij)
  have hcard :
      ((Finset.univ : Finset (Fin (d + 1))).image (algebraMap R L ∘ v)).card = d + 1 := by
    rw [Finset.card_image_of_injOn hav_inj, Finset.card_univ, Fintype.card_fin]
  -- Degree bounds
  have hdf : f.degree < ↑(d + 1) :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le le_rfl)
  have hdmh : (map (algebraMap R L) h).degree < ↑(d + 1) :=
    lt_of_le_of_lt degree_map_le hdeg_h
  -- Show f = h.map(algebraMap) via finite polynomial identity
  have heq : f = map (algebraMap R L) h := by
    suffices f - map (algebraMap R L) h = 0 from sub_eq_zero.mp this
    apply eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((Finset.univ : Finset (Fin (d + 1))).image (algebraMap R L ∘ v))
    · rw [hcard]
      exact lt_of_le_of_lt (degree_sub_le _ _) (sup_lt_iff.mpr ⟨hdf, hdmh⟩)
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp only [Function.comp_apply, eval_sub, eval_map, sub_eq_zero]
      -- eval₂ (algebraMap R L) (algebraMap R L (v i)) h = algebraMap R L (eval (v i) h)
      rw [show eval₂ (algebraMap R L) (algebraMap R L (v i)) h =
        algebraMap R L (eval (v i) h) from by
          rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rfl]
      rw [heval_h i, hφ]
  -- Conclude: f.coeff n = algebraMap(h.coeff n) ∈ range
  rw [heq]; exact ⟨h.coeff n, (coeff_map _ n).symm⟩

/-- For a product ∏(Y − C(f_i)), each Y-coefficient (an element of L[Z]) has all
    its Z-coefficients expressible as elementary symmetric polynomials of
    the f_i's Z-coefficients. When those are symmetric in roots of P ∈ R[X],
    they lie in R by Prop 2.16.

    This is the core evaluation lemma: for fixed z ∈ R, the n-th Y-coefficient
    of ∏(Y − γ_{ij}(z)) is a symmetric function of x₁,…,xₚ. -/
theorem Q_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((QPolynomial x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  -- Define the MvPolynomial version of γ with z = r baked in as a constant
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  -- Define QMv: the product over strictPairs in (MvPolynomial R)[Y]
  set QMv : (MvPolynomial (Fin p) R)[X] :=
    ∏ ij ∈ strictPairs p,
      (Polynomial.X - Polynomial.C (γMv ij)) with QMv_def
  -- Key fact: aeval x ∘ γMv = eval (algebraMap r) ∘ gammaPoly x
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  -- Map (aeval x) QMv = map (eval z) (QPolynomial x) as polynomials in Y over L
  have hQ : Polynomial.map (MvPolynomial.aeval x).toRingHom QMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (QPolynomial x) := by
    simp only [QMv_def, QPolynomial]
    rw [Polynomial.map_prod, Polynomial.map_prod]
    apply Finset.prod_congr rfl; intro ij hij
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
    rw [hγ ij hij]
  -- Coefficients agree: eval z (coeff n Q) = aeval x (coeff n QMv)
  have hcoeff : Polynomial.eval (algebraMap R L r) ((QPolynomial x).coeff n) =
      (MvPolynomial.aeval x) (QMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hQ
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  -- coeff n QMv is a symmetric MvPolynomial
  have hsymm : (QMv.coeff n).IsSymmetric := by
    intro σ
    have hrename_coeff : MvPolynomial.rename σ (QMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom QMv).coeff n :=
      (Polynomial.coeff_map _ _).symm
    rw [hrename_coeff]
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom QMv = QMv by rw [hpoly]
    simp only [QMv_def]
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    simp_rw [hγ_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    apply Finset.prod_nbij (fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1))
    · -- Maps into strictPairs
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    · -- Injective
      intro ij₁ hij₁ ij₂ hij₂ heq
      simp only [strictPairs, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hij₁ hij₂
      have heq' : (if σ ij₁.1 < σ ij₁.2 then (σ ij₁.1, σ ij₁.2) else (σ ij₁.2, σ ij₁.1)) =
                  (if σ ij₂.1 < σ ij₂.2 then (σ ij₂.1, σ ij₂.2) else (σ ij₂.2, σ ij₂.1)) := heq
      split_ifs at heq' with h₁ h₂ h₂
      all_goals (obtain ⟨ha, hb⟩ := Prod.mk.inj heq')
      · exact Prod.ext (σ.injective ha) (σ.injective hb)
      · exfalso
        exact absurd (show ij₁.2 < ij₁.1 from σ.injective ha ▸ σ.injective hb ▸ hij₂) (not_lt.mpr hij₁.le)
      · exfalso
        exact absurd (show ij₂.2 < ij₂.1 from σ.injective ha ▸ σ.injective hb ▸ hij₁) (not_lt.mpr hij₂.le)
      · exact Prod.ext (σ.injective hb) (σ.injective ha)
    · -- Surjective onto strictPairs
      intro ij hij
      simp only [strictPairs, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image,
        Finset.mem_univ, true_and] at hij ⊢
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2), hord, ?_⟩
        simp only [Equiv.apply_symm_apply]
        rw [if_pos hij]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1), hord', ?_⟩
        simp only [Equiv.apply_symm_apply]
        rw [if_neg (not_lt.mpr hij.le)]
    · -- Values agree after sorting
      intro ij hij
      split_ifs with h
      · rfl
      · simp only [sub_right_inj]; exact congr_arg Polynomial.C (hγ_comm _ _)
  -- Apply proposition_2_16 from Section2_1
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of Q(Z,Y) (viewed as a polynomial in Y whose coefficients
    are in L[Z]) actually belongs to R[Z], provided the xᵢ are roots of a
    polynomial P ∈ R[X]. -/
theorem Q_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (QPolynomial x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]
  intro m
  -- We need each Z-coefficient of f := (QPolynomial x).coeff n to be in R.
  -- Q_eval_coeff_in_R shows f.eval(algebraMap r) ∈ range for all r.
  -- eval_range_implies_coeff_range then gives all f.coeff in range.
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (Q_eval_coeff_in_R P x hx n) m

/-- The n-th Y-coefficient of G(Z,Y), evaluated at z = algebraMap r, lies in R.
    Proof mirrors Q_eval_coeff_in_R: MvPolynomial lifting + symmetry + proposition_2_16. -/
theorem G_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((GPoly x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  set sMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 with sMv_def
  set GMv : (MvPolynomial (Fin p) R)[X] :=
    ∑ ij ∈ strictPairs p,
      Polynomial.C (sMv ij) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (Polynomial.X - Polynomial.C (γMv kl)) with GMv_def
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hs_aeval : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (sMv ij) = x ij.1 + x ij.2 := by
    intro ij _; simp only [sMv_def, map_add, MvPolynomial.aeval_X]
  have hG : Polynomial.map (MvPolynomial.aeval x).toRingHom GMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (GPoly x) := by
    simp only [GMv_def, GPoly]
    rw [Polynomial.map_sum, Polynomial.map_sum]
    apply Finset.sum_congr rfl; intro ij hij
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C]
    congr 1
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, hs_aeval ij hij]
    · rw [Polynomial.map_prod, Polynomial.map_prod]
      apply Finset.prod_congr rfl; intro kl hkl
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
      rw [hγ kl (Finset.mem_of_mem_erase hkl)]
  have hcoeff : Polynomial.eval (algebraMap R L r) ((GPoly x).coeff n) =
      (MvPolynomial.aeval x) (GMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hG
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  -- Symmetry: rename σ GMv = GMv. Strategy: show the polynomial (in Y) is invariant.
  have hsymm : (GMv.coeff n).IsSymmetric := by
    intro σ
    rw [show MvPolynomial.rename σ (GMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom GMv).coeff n from
      (Polynomial.coeff_map _ _).symm]
    -- Suffices to show rename σ GMv = GMv as polynomials in Y
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom GMv = GMv by rw [hpoly]
    -- GMv = Q.derivative * Lagrange_interpolant, but simpler: direct reindexing
    -- Key: σ acts on strictPairs via the "sort" bijection
    simp only [GMv_def]
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    have hs_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (sMv ij) = sMv (σ ij.1, σ ij.2) := by
      intro ij; simp only [sMv_def, map_add, MvPolynomial.rename_X]
    simp_rw [hγ_rename, hs_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    have hs_comm : ∀ i j : Fin p, sMv (i, j) = sMv (j, i) := by
      intro i j; simp only [sMv_def]; ring
    -- Sort bijection: map (σ i, σ j) to the strictly-ordered version
    set φ : Fin p × Fin p → Fin p × Fin p :=
      fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1) with φ_def
    -- φ maps strictPairs to strictPairs
    have hφ_mem : ∀ ij ∈ strictPairs p, φ ij ∈ strictPairs p := by
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      simp only [φ]; split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    -- φ is injective on strictPairs
    have hφ_inj : ∀ ij₁ ∈ strictPairs p, ∀ ij₂ ∈ strictPairs p,
        φ ij₁ = φ ij₂ → ij₁ = ij₂ := by
      intro ij₁ hij₁ ij₂ hij₂ heq
      have h₁ : ij₁.1 < ij₁.2 := (Finset.mem_filter.mp hij₁).2
      have h₂ : ij₂.1 < ij₂.2 := (Finset.mem_filter.mp hij₂).2
      simp only [φ] at heq
      split_ifs at heq with ha hb hb
      all_goals (obtain ⟨hc, hd⟩ := Prod.mk.inj heq)
      · exact Prod.ext (σ.injective hc) (σ.injective hd)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₂ :
          ij₁.2 < ij₁.1) (not_lt.mpr h₁.le)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₁ :
          ij₂.2 < ij₂.1) (not_lt.mpr h₂.le)
      · exact Prod.ext (σ.injective hd) (σ.injective hc)
    -- φ is surjective onto strictPairs
    have hφ_surj : ∀ ij ∈ strictPairs p, ∃ ij' ∈ strictPairs p, φ ij' = ij := by
      intro ij hij
      have hij_lt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_pos hij_lt]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij_lt.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord'⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_neg (not_lt.mpr hij_lt.le)]
    -- φ preserves γMv values (up to commutativity)
    have hφ_γ : ∀ ij, γMv (σ ij.1, σ ij.2) = γMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hγ_comm _ _]
    -- φ preserves sMv values (up to commutativity)
    have hφ_s : ∀ ij, sMv (σ ij.1, σ ij.2) = sMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hs_comm _ _]
    -- Reindex the sum
    apply Finset.sum_nbij φ hφ_mem
      (fun ij₁ hij₁ ij₂ hij₂ heq => hφ_inj ij₁ hij₁ ij₂ hij₂ heq)
      (fun ij hij => hφ_surj ij hij)
    -- Value equality for each summand
    intro ij hij
    rw [hφ_s ij]
    suffices hprod : ∏ kl ∈ (strictPairs p).erase ij, (Polynomial.X - Polynomial.C (γMv (σ kl.1, σ kl.2))) =
        ∏ kl ∈ (strictPairs p).erase (φ ij), (Polynomial.X - Polynomial.C (γMv kl)) by
      rw [hprod]
    -- Product over erase'd set: same reindexing
    apply Finset.prod_nbij φ
    · -- Maps into SP.erase (φ ij)
      intro kl hkl
      refine Finset.mem_erase.mpr ⟨?_, hφ_mem kl (Finset.mem_of_mem_erase hkl)⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl)
        (hφ_inj kl (Finset.mem_of_mem_erase hkl) ij hij heq)
    · -- Injective
      intro kl₁ hkl₁ kl₂ hkl₂ heq
      exact hφ_inj kl₁ (Finset.mem_of_mem_erase hkl₁) kl₂ (Finset.mem_of_mem_erase hkl₂) heq
    · -- Surjective
      intro kl hkl
      obtain ⟨kl', hkl'_mem, hkl'_eq⟩ := hφ_surj kl (Finset.mem_of_mem_erase hkl)
      refine ⟨kl', Finset.mem_erase.mpr ⟨?_, hkl'_mem⟩, hkl'_eq⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl) (hkl'_eq ▸ congr_arg φ heq)
    · -- Values
      intro kl _
      simp only [sub_right_inj]
      exact congr_arg Polynomial.C (hφ_γ kl)
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of G(Z,Y) belongs to R[Z]. -/
theorem G_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (GPoly x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]; intro m
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (G_eval_coeff_in_R P x hx n) m

/-- The n-th Y-coefficient of H(Z,Y), evaluated at z = algebraMap r, lies in R.
    Same structure as G: MvPolynomial lifting + symmetry + proposition_2_16. -/
theorem H_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((HPoly x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  -- Identical structure to G_eval_coeff_in_R with sMv replaced by pMv (product)
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  set pMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with pMv_def
  set HMv : (MvPolynomial (Fin p) R)[X] :=
    ∑ ij ∈ strictPairs p,
      Polynomial.C (pMv ij) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (Polynomial.X - Polynomial.C (γMv kl)) with HMv_def
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hp_aeval : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (pMv ij) = x ij.1 * x ij.2 := by
    intro ij _; simp only [pMv_def, map_mul, MvPolynomial.aeval_X]
  have hH : Polynomial.map (MvPolynomial.aeval x).toRingHom HMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (HPoly x) := by
    simp only [HMv_def, HPoly]
    rw [Polynomial.map_sum, Polynomial.map_sum]
    apply Finset.sum_congr rfl; intro ij hij
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C]
    congr 1
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, hp_aeval ij hij]
    · rw [Polynomial.map_prod, Polynomial.map_prod]
      apply Finset.prod_congr rfl; intro kl hkl
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
      rw [hγ kl (Finset.mem_of_mem_erase hkl)]
  have hcoeff : Polynomial.eval (algebraMap R L r) ((HPoly x).coeff n) =
      (MvPolynomial.aeval x) (HMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hH
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  have hsymm : (HMv.coeff n).IsSymmetric := by
    intro σ
    rw [show MvPolynomial.rename σ (HMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom HMv).coeff n from
      (Polynomial.coeff_map _ _).symm]
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom HMv = HMv by rw [hpoly]
    simp only [HMv_def]
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    have hp_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (pMv ij) = pMv (σ ij.1, σ ij.2) := by
      intro ij; simp only [pMv_def, map_mul, MvPolynomial.rename_X]
    simp_rw [hγ_rename, hp_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    have hp_comm : ∀ i j : Fin p, pMv (i, j) = pMv (j, i) := by
      intro i j; simp only [pMv_def]; ring
    set φ : Fin p × Fin p → Fin p × Fin p :=
      fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1) with φ_def
    have hφ_mem : ∀ ij ∈ strictPairs p, φ ij ∈ strictPairs p := by
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      simp only [φ]; split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    have hφ_inj : ∀ ij₁ ∈ strictPairs p, ∀ ij₂ ∈ strictPairs p,
        φ ij₁ = φ ij₂ → ij₁ = ij₂ := by
      intro ij₁ hij₁ ij₂ hij₂ heq
      have h₁ : ij₁.1 < ij₁.2 := (Finset.mem_filter.mp hij₁).2
      have h₂ : ij₂.1 < ij₂.2 := (Finset.mem_filter.mp hij₂).2
      simp only [φ] at heq
      split_ifs at heq with ha hb hb
      all_goals (obtain ⟨hc, hd⟩ := Prod.mk.inj heq)
      · exact Prod.ext (σ.injective hc) (σ.injective hd)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₂ :
          ij₁.2 < ij₁.1) (not_lt.mpr h₁.le)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₁ :
          ij₂.2 < ij₂.1) (not_lt.mpr h₂.le)
      · exact Prod.ext (σ.injective hd) (σ.injective hc)
    have hφ_surj : ∀ ij ∈ strictPairs p, ∃ ij' ∈ strictPairs p, φ ij' = ij := by
      intro ij hij
      have hij_lt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_pos hij_lt]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij_lt.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord'⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_neg (not_lt.mpr hij_lt.le)]
    have hφ_γ : ∀ ij, γMv (σ ij.1, σ ij.2) = γMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hγ_comm _ _]
    have hφ_p : ∀ ij, pMv (σ ij.1, σ ij.2) = pMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hp_comm _ _]
    apply Finset.sum_nbij φ hφ_mem
      (fun ij₁ hij₁ ij₂ hij₂ heq => hφ_inj ij₁ hij₁ ij₂ hij₂ heq)
      (fun ij hij => hφ_surj ij hij)
    intro ij hij
    rw [hφ_p ij]
    suffices hprod : ∏ kl ∈ (strictPairs p).erase ij, (Polynomial.X - Polynomial.C (γMv (σ kl.1, σ kl.2))) =
        ∏ kl ∈ (strictPairs p).erase (φ ij), (Polynomial.X - Polynomial.C (γMv kl)) by
      rw [hprod]
    apply Finset.prod_nbij φ
    · intro kl hkl
      refine Finset.mem_erase.mpr ⟨?_, hφ_mem kl (Finset.mem_of_mem_erase hkl)⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl)
        (hφ_inj kl (Finset.mem_of_mem_erase hkl) ij hij heq)
    · intro kl₁ hkl₁ kl₂ hkl₂ heq
      exact hφ_inj kl₁ (Finset.mem_of_mem_erase hkl₁) kl₂ (Finset.mem_of_mem_erase hkl₂) heq
    · intro kl hkl
      obtain ⟨kl', hkl'_mem, hkl'_eq⟩ := hφ_surj kl (Finset.mem_of_mem_erase hkl)
      refine ⟨kl', Finset.mem_erase.mpr ⟨?_, hkl'_mem⟩, hkl'_eq⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl) (hkl'_eq ▸ congr_arg φ heq)
    · intro kl _
      simp only [sub_right_inj]
      exact congr_arg Polynomial.C (hφ_γ kl)
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of H(Z,Y) belongs to R[Z]. -/
theorem H_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (HPoly x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]; intro m
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (H_eval_coeff_in_R P x hx n) m

end Azurite.BPR.Theorem2_11
