import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_54
import Azurite.BasuPollackRoy.Chapter4.Section4_3.Corollary_4_45
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp
import Mathlib.LinearAlgebra.Vandermonde

/-!
# BPR Theorem 4.58 (Hermite)

The capstone of §4.3.2. Over a real closed field `R`, with `C = R[i]`, the rank and
signature of the Hermite quadratic form `Her(P, Q)` (realized by the symmetric matrix
`HerMatR P Q` over `R`) compute:

* `rank(Her(P,Q)) = #{ distinct roots x of P in C with Q(x) ≠ 0 }`;
* `Sign(Her(P,Q)) = TaQ(Q, P)` (the Tarski query).

Both follow from a single `DiagonalExpression` of `quadraticForm (HerMatR P Q)`, built by
decomposing `Her(P,Q)` over the roots of `P` in `C` and grouping conjugate pairs.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix
open Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Hermite's matrix over `R`.** The `p × p` matrix whose `(i,j)` entry is the trace of
multiplication by `Q · X^{i+j}` on `A = R[X]/(P)`; this is `HerMatR P Q`, a symmetric
(Hankel) matrix with entries in `R`. -/
noncomputable def HerMatR (P Q : R[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) R :=
  Matrix.of fun i j => Algebra.trace R (AdjoinRoot P) (AdjoinRoot.mk P (Q * X ^ ((i : ℕ) + (j : ℕ))))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The Hermite matrix is symmetric (its entries depend only on `i + j`). -/
theorem HerMatR_isSymm (P Q : R[X]) : (HerMatR P Q).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, HerMatR, Matrix.of_apply]
  rw [Nat.add_comm]

/-- Bridge: `HerMatR P Q`, mapped into `C = Ri R`, is the `C`-valued Hermite matrix
`HerMatrix P Q`. This is `herMatrix_eq_trace` instantiated at `K := R`, `C := Ri R`. -/
theorem HerMatR_map_eq (P Q : R[X]) (hP : P.Monic) (i j : Fin P.natDegree) :
    algebraMap R (Ri R) (HerMatR P Q i j) = HerMatrix P Q i j := by
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  rw [HerMatR, Matrix.of_apply, herMatrix_eq_trace (C := Ri R) P Q hP i j]

/-! ## Root data over `C = Ri R` -/

/-- The finset of distinct roots of `P` in `C = Ri R` at which `Q` does not vanish. -/
noncomputable def herRoots (P Q : R[X]) : Finset (Ri R) :=
  ((P.aroots (Ri R)).toFinset).filter (fun x => aeval x Q ≠ 0)

/-- The weight `μ(x)·Q(x)` of a root `x` (multiplicity times the value of `Q`). -/
noncomputable def herWeight (P Q : R[X]) (x : Ri R) : Ri R :=
  (Multiset.count x (P.aroots (Ri R))) • aeval x Q

set_option linter.unusedSectionVars false in
/-- The `C`-valued Hermite matrix entry, grouped by distinct roots: a weighted Newton sum
`∑_{x ∈ herRoots} μ(x)·Q(x)·x^{i+j}` (terms with `Q(x)=0` drop out). -/
theorem herMatrix_eq_sum_herRoots (P Q : R[X]) (i j : Fin P.natDegree) :
    HerMatrix P Q i j
      = ∑ x ∈ herRoots P Q, herWeight P Q x * x ^ ((i : ℕ) + (j : ℕ)) := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  rw [HerMatrix, Matrix.of_apply, Finset.sum_multiset_map_count]
  -- group, then drop the `Q(x) = 0` terms
  rw [herRoots]
  symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hQ
  · show ((Multiset.count x (P.aroots (Ri R))) • aeval x Q) * x ^ ((i:ℕ)+(j:ℕ)) = _
    rw [smul_mul_assoc]
  · rw [not_not.mp hQ]; simp

set_option linter.unusedSectionVars false in
/-- Membership in `herRoots`: `x` is a root of `P` over `C` (so `0 < μ(x)`) and `Q(x) ≠ 0`. -/
theorem mem_herRoots_iff (P Q : R[X]) (x : Ri R) :
    x ∈ herRoots P Q ↔ x ∈ P.aroots (Ri R) ∧ aeval x Q ≠ 0 := by
  rw [herRoots, Finset.mem_filter, Multiset.mem_toFinset]

/-- The weight `μ(x)·Q(x)` is nonzero for `x ∈ herRoots P Q`. -/
theorem herWeight_ne_zero (P Q : R[X]) {x : Ri R} (hx : x ∈ herRoots P Q) :
    herWeight P Q x ≠ 0 := by
  rw [mem_herRoots_iff] at hx
  rw [herWeight, nsmul_eq_mul]
  refine mul_ne_zero ?_ hx.2
  have hpos : 0 < Multiset.count x (P.aroots (Ri R)) := Multiset.count_pos.mpr hx.1
  have hne : (Multiset.count x (P.aroots (Ri R)) : R) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have : ((Multiset.count x (P.aroots (Ri R)) : ℕ) : Ri R)
      = algebraMap R (Ri R) (Multiset.count x (P.aroots (Ri R)) : R) := by
    rw [map_natCast]
  rw [this]
  exact fun h => hne ((algebraMap R (Ri R)).injective (by rw [h, map_zero]))

set_option linter.unusedSectionVars false in
/-- A conjugation-fixed element of `C = Ri R` has vanishing imaginary part and equals
`algebraMap R (Ri R) (Ri.reL z)`. -/
theorem algebraMap_reL_of_conj_fixed {z : Ri R} (hz : Ri.conj R z = z) :
    algebraMap R (Ri R) (Ri.reL z) = z := by
  obtain ⟨a, hra⟩ := Ri.conj_fixed_mem_range_ordered z hz
  have hreL : Ri.reL z = a := by
    rw [← hra]
    rw [show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl]
    exact Ri.reL_of a
  rw [hreL, hra]

/-- **LHS bridge.** Applying `algebraMap R (Ri R)` to `quadraticForm (HerMatR P Q) f`
gives the weighted sum of squares over the roots:
`∑_{x ∈ herRoots} μ(x)·Q(x)·(∑ₖ f_k x^k)²`. -/
theorem algebraMap_quadraticForm_eq (P Q : R[X]) (hP : P.Monic) (f : Fin P.natDegree → R) :
    algebraMap R (Ri R) (quadraticForm (HerMatR P Q) f)
      = ∑ x ∈ herRoots P Q,
          herWeight P Q x * (∑ k : Fin P.natDegree, algebraMap R (Ri R) (f k) * x ^ (k : ℕ)) ^ 2 := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  -- quadraticForm M f = ∑ i ∑ j, M i j * f i * f j
  have hqf : quadraticForm (HerMatR P Q) f
      = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree, HerMatR P Q i j * f i * f j := by
    rw [quadraticForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hqf, map_sum]
  -- map each entry into C, identify with Her P Q (algebraMap ∘ f)
  have hstep : ∀ i : Fin P.natDegree,
      algebraMap R (Ri R) (∑ j : Fin P.natDegree, HerMatR P Q i j * f i * f j)
        = ∑ j : Fin P.natDegree,
            HerMatrix P Q i j * algebraMap R (Ri R) (f i) * algebraMap R (Ri R) (f j) := by
    intro i
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, HerMatR_map_eq P Q hP]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- this is Her P Q (algebraMap ∘ f) by Her_apply
  rw [← Her_apply P Q (fun k => algebraMap R (Ri R) (f k)), Her]
  -- group by roots
  rw [Finset.sum_multiset_map_count]
  rw [herRoots]
  symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hQ
  · rw [herWeight, smul_mul_assoc]
  · rw [not_not.mp hQ]; simp

/-! ## The diagonal expression -/

/-- A chosen square root in `C = Ri R` of the weight `μ(x)·Q(x)` (exists since `C` is
algebraically closed). For real `x` we will not use it; for a conjugate pair it produces
the `±` linear forms. -/
noncomputable def herSqrt (P Q : R[X]) (x : Ri R) : Ri R :=
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  (IsAlgClosed.exists_pow_nat_eq (herWeight P Q x) (n := 2) (by norm_num)).choose

theorem herSqrt_sq (P Q : R[X]) (x : Ri R) :
    herSqrt P Q x ^ 2 = herWeight P Q x := by
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact (IsAlgClosed.exists_pow_nat_eq (herWeight P Q x) (n := 2) (by norm_num)).choose_spec

/-- The coefficient attached to a root `x ∈ herRoots P Q`:
* a real root `x` contributes `Ri.reL (μ(x)·Q(x))` (the real weight);
* a non-real root with positive imaginary part contributes `+2`;
* a non-real root with negative imaginary part contributes `-2`. -/
noncomputable def herCoeff (P Q : R[X]) (x : Ri R) : R :=
  if Ri.conj R x = x then Ri.reL (herWeight P Q x)
  else if 0 < Ri.imL x then 2 else -2

/-- The coefficient vector (in `R^p`) of the linear form attached to a root `x`.
* real `x`: `(reL(xᵏ))ₖ = (x₀ᵏ)ₖ`, giving `L(f) = ∑ₖ fₖ x₀ᵏ`;
* non-real `x` with positive imaginary part (`z`): with `w² = μ(z)Q(z)`, the vector
  `(Re(w)·Re(zᵏ) − Im(w)·Im(zᵏ))ₖ`, i.e. `L₁(f) = Re(w·∑ fₖ zᵏ)`;
* non-real `x` with negative imaginary part: taking the conjugate `z = conj x` as the
  pos-im representative, the vector `(Re(w)·Im(zᵏ) + Im(w)·Re(zᵏ))ₖ`, i.e.
  `L₂(f) = Im(w·∑ fₖ zᵏ)`. -/
noncomputable def herFormVec (P Q : R[X]) (p : ℕ) (x : Ri R) : Fin p → R :=
  if Ri.conj R x = x then fun k => Ri.reL (x ^ (k : ℕ))
  else if 0 < Ri.imL x then
    (fun k => Ri.reL (herSqrt P Q x) * Ri.reL (x ^ (k : ℕ))
                - Ri.imL (herSqrt P Q x) * Ri.imL (x ^ (k : ℕ)))
  else
    (fun k => Ri.reL (herSqrt P Q (Ri.conj R x)) * Ri.imL ((Ri.conj R x) ^ (k : ℕ))
                + Ri.imL (herSqrt P Q (Ri.conj R x)) * Ri.reL ((Ri.conj R x) ^ (k : ℕ)))

/-- The linear form `f ↦ v ⬝ᵥ f` with coefficient vector `v` (local copy of the
`Corollary_4_44` `dotLM`). -/
def herDotLM {p : ℕ} (v : Fin p → R) : (Fin p → R) →ₗ[R] R where
  toFun f := v ⬝ᵥ f
  map_add' := dotProduct_add v
  map_smul' c f := by simp [dotProduct_smul]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem herDotLM_apply {p : ℕ} (v f : Fin p → R) : herDotLM v f = v ⬝ᵥ f := rfl

/-! ### Real/imaginary arithmetic in `Ri R` (helpers for `apply_eq`) -/

set_option linter.unusedSectionVars false in
/-- Real part of a product in `Ri R`. -/
private theorem reL_mul (c d : Ri R) :
    Ri.reL (c * d) = Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c)
            + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL d)
            + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL c)
          * AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL d)) * hi2]
  rw [Ri.reL_lin]

set_option linter.unusedSectionVars false in
/-- Imaginary part of a product in `Ri R`. -/
private theorem imL_mul (c d : Ri R) :
    Ri.imL (c * d) = Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c)
            + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL d)
            + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL c)
          * AdjoinRoot.of (X ^ 2 + 1 : R[X]) (Ri.imL d)) * hi2]
  rw [Ri.imL_lin]

set_option linter.unusedSectionVars false in
/-- `c + conj c = algebraMap (2 · reL c)`. -/
private theorem conj_add_self (c : Ri R) :
    c + Ri.conj R c = algebraMap R (Ri R) (2 * Ri.reL c) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr, two_mul, map_add]
  ring

set_option linter.unusedSectionVars false in
/-- `reL (c²) = (reL c)² − (imL c)²`. -/
private theorem reL_sq (c : Ri R) : Ri.reL (c ^ 2) = Ri.reL c ^ 2 - Ri.imL c ^ 2 := by
  rw [show (c : Ri R) ^ 2 = c * c from pow_two c, reL_mul]; ring

set_option linter.unusedSectionVars false in
/-- `reL (conj c) = reL c`. -/
private theorem reL_conj (c : Ri R) : Ri.reL (Ri.conj R c) = Ri.reL c := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.reL_lin a (-b)]

/-! ### Conjugation facts on `herRoots` -/

omit [IsRealClosed R] in
/-- Conjugation preserves `aroots P` (the conjugate of a root is a root, with equal
multiplicity). -/
theorem aroots_map_conj [IsRealClosed R] (P : R[X]) :
    (P.aroots (Ri R)).map (Ri.conj R) = P.aroots (Ri R) := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  have hsplit : (P.map (algebraMap R (Ri R))).Splits := IsAlgClosed.splits _
  -- conjugation of the polynomial fixes it (coefficients lie in `R`)
  have hmapconj : (P.map (algebraMap R (Ri R))).map (Ri.conj R : Ri R →+* Ri R)
      = P.map (algebraMap R (Ri R)) := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp only [RingHom.comp_apply]
    exact Ri.conj_algebraMap_ordered r
  -- roots of the conjugated polynomial = conj of the roots
  have hroots := hsplit.roots_map (Ri.conj R : Ri R →+* Ri R)
  rw [Polynomial.aroots]
  rw [hmapconj] at hroots
  exact hroots.symm

/-- Conjugation preserves `aroots P` (the conjugate of a root is a root, with equal
multiplicity). -/
theorem count_aroots_conj (P : R[X]) (x : Ri R) :
    Multiset.count (Ri.conj R x) (P.aroots (Ri R))
      = Multiset.count x (P.aroots (Ri R)) := by
  classical
  conv_lhs => rw [← aroots_map_conj P]
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  -- {y ∈ aroots | conj x = conj y} = {y ∈ aroots | x = y} since conj injective
  exact congrArg Multiset.card (Multiset.filter_congr fun y _ =>
    ⟨fun h => Ri.conj_injective R h, fun h => by rw [h]⟩)

omit [IsRealClosed R] in
/-- `Ri.imL` is negated by conjugation. -/
theorem imL_conj (x : Ri R) : Ri.imL (Ri.conj R x) = - Ri.imL x := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  rw [hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.imL_lin a b, Ri.imL_lin a (-b)]

omit [IsRealClosed R] in
/-- A non-real element has nonzero imaginary part. -/
theorem imL_ne_zero_of_not_real {x : Ri R} (hx : Ri.conj R x ≠ x) : Ri.imL x ≠ 0 := by
  intro h
  apply hx
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  have hb : b = 0 := by
    have := hab ▸ h
    rwa [show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl,
      Ri.imL_lin a b] at this
  rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]

set_option linter.unusedSectionVars false in
/-- `aeval (conj x) Q = conj (aeval x Q)` since `Q` has real coefficients. -/
theorem aeval_conj (Q : R[X]) (x : Ri R) :
    aeval (Ri.conj R x) Q = Ri.conj R (aeval x Q) := by
  rw [← Polynomial.aeval_algHom_apply]

/-- Conjugation maps `herRoots P Q` to itself. -/
theorem conj_mem_herRoots {P Q : R[X]} {x : Ri R} (hx : x ∈ herRoots P Q) :
    Ri.conj R x ∈ herRoots P Q := by
  rw [mem_herRoots_iff] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [Polynomial.mem_aroots] at hx ⊢
    refine ⟨hx.1.1, ?_⟩
    rw [aeval_conj, hx.1.2, map_zero]
  · rw [aeval_conj]
    intro h
    apply hx.2
    have : aeval x Q = 0 := by
      have := congrArg (Ri.conj R) h
      rwa [Ri.conj_conj, map_zero] at this
    exact this

set_option linter.unusedSectionVars false in
/-- For a non-real `x`, `herCoeff` at `conj x` is the negation of `herCoeff` at `x`
(the `±2` flip from the imaginary part changing sign). -/
theorem herCoeff_conj_of_not_real (P Q : R[X]) {x : Ri R} (hx : Ri.conj R x ≠ x) :
    herCoeff P Q (Ri.conj R x) = - herCoeff P Q x := by
  have hx' : Ri.conj R (Ri.conj R x) ≠ Ri.conj R x := fun h => hx (Ri.conj_injective R h)
  rw [herCoeff, herCoeff, if_neg hx, if_neg hx']
  rw [imL_conj]
  have him : Ri.imL x ≠ 0 := imL_ne_zero_of_not_real hx
  rcases lt_or_gt_of_ne him with hlt | hgt
  · rw [if_pos (by simpa using hlt), if_neg (not_lt.mpr hlt.le)]; norm_num
  · rw [if_neg (by simpa using hgt.le), if_pos hgt]

set_option linter.unusedSectionVars false in
/-- **The diagonalizing identity.** `quadraticForm (HerMatR P Q) f` equals the weighted
sum of squares of the linear forms `herFormVec … ⬝ᵥ f` with coefficients `herCoeff`. -/
theorem herApply_eq (P Q : R[X]) (hP : P.Monic) (f : Fin P.natDegree → R) :
    quadraticForm (HerMatR P Q) f
      = ∑ x ∈ herRoots P Q,
          herCoeff P Q x * (herFormVec P Q P.natDegree x ⬝ᵥ f) ^ 2 := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  apply (algebraMap R (Ri R)).injective
  rw [algebraMap_quadraticForm_eq P Q hP f, map_sum]
  -- abbreviations
  set ι := algebraMap R (Ri R) with hι
  set lcv : Ri R → Ri R := fun x => ∑ k : Fin P.natDegree, ι (f k) * x ^ (k : ℕ) with hlcv
  set A : Ri R → Ri R := fun x => herWeight P Q x * (lcv x) ^ 2 with hA
  set B : Ri R → Ri R := fun x => ι (herCoeff P Q x) * (ι (herFormVec P Q P.natDegree x ⬝ᵥ f)) ^ 2
    with hB
  -- RHS terms are exactly `B`
  have hRHS : ∀ x : Ri R,
      ι (herCoeff P Q x * (herFormVec P Q P.natDegree x ⬝ᵥ f) ^ 2) = B x := by
    intro x; rw [map_mul, map_pow]
  rw [Finset.sum_congr rfl (fun x _ => hRHS x)]
  -- the image under `ι` of a dot product with `f`
  have hdot : ∀ v : Fin P.natDegree → R,
      ι (v ⬝ᵥ f) = ∑ k : Fin P.natDegree, ι (v k) * ι (f k) := by
    intro v
    rw [dotProduct, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul ι (v k) (f k)
  -- `lcv` commutes with conjugation
  have hlcv_conj : ∀ x : Ri R, lcv (Ri.conj R x) = Ri.conj R (lcv x) := by
    intro x
    simp only [hlcv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, Ri.conj_algebraMap_ordered]
  -- `herWeight` commutes with conjugation
  have hweight_conj : ∀ x : Ri R, herWeight P Q (Ri.conj R x) = Ri.conj R (herWeight P Q x) := by
    intro x
    rw [herWeight, herWeight, count_aroots_conj, aeval_conj, map_nsmul]
  -- `A` commutes with conjugation
  have hAconj : ∀ x : Ri R, A (Ri.conj R x) = Ri.conj R (A x) := by
    intro x
    simp only [hA]
    rw [hweight_conj, hlcv_conj, map_mul, map_pow]
  -- the real-part value of `A x` lifts back via `ι`
  have hreal_A : ∀ x : Ri R, ι (2 * Ri.reL (A x)) = A x + A (Ri.conj R x) := by
    intro x
    rw [hAconj, hι, conj_add_self]
  -- real `x`: `B x = A x` (so `A x - B x = 0`)
  have hBreal : ∀ x : Ri R, x ∈ herRoots P Q → Ri.conj R x = x → B x = A x := by
    intro x hxmem hxr
    -- `herWeight x` is conj-fixed, so `ι (herCoeff x) = herWeight x`
    have hwfix : Ri.conj R (herWeight P Q x) = herWeight P Q x := by
      rw [← hweight_conj, hxr]
    have hcoeff : ι (herCoeff P Q x) = herWeight P Q x := by
      rw [herCoeff, if_pos hxr, hι]
      exact algebraMap_reL_of_conj_fixed hwfix
    -- `ι (herFormVec x ⬝ᵥ f) = lcv x`
    have hform : ι (herFormVec P Q P.natDegree x ⬝ᵥ f) = lcv x := by
      rw [hdot, hlcv]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [herFormVec, if_pos hxr]
      have hpowfix : Ri.conj R (x ^ (k : ℕ)) = x ^ (k : ℕ) := by
        rw [map_pow, hxr]
      have : ι (Ri.reL (x ^ (k : ℕ))) = x ^ (k : ℕ) := by
        rw [hι]; exact algebraMap_reL_of_conj_fixed hpowfix
      rw [this]; ring
    rw [hB, hA]
    dsimp only
    rw [hcoeff, hform]
  -- non-real `x`: `B x + B (conj x) = ι (2 * Ri.reL (A x))`
  -- `reL`/`imL` of `ι c * z` for `c : R`
  have hreLc : ∀ (c : R) (z : Ri R), Ri.reL (ι c * z) = c * Ri.reL z := by
    intro c z; rw [hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have himLc : ∀ (c : R) (z : Ri R), Ri.imL (ι c * z) = c * Ri.imL z := by
    intro c z; rw [hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  -- `reL`/`imL` of `w * lcv x` distribute over the sum
  have hreL_wlcv : ∀ (w x : Ri R),
      Ri.reL (w * lcv x) = ∑ k : Fin P.natDegree, Ri.reL (w * x ^ (k : ℕ)) * f k := by
    intro w x
    rw [hlcv]
    dsimp only
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show w * (ι (f k) * x ^ (k : ℕ)) = ι (f k) * (w * x ^ (k : ℕ)) by ring, hreLc, mul_comm]
  have himL_wlcv : ∀ (w x : Ri R),
      Ri.imL (w * lcv x) = ∑ k : Fin P.natDegree, Ri.imL (w * x ^ (k : ℕ)) * f k := by
    intro w x
    rw [hlcv]
    dsimp only
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show w * (ι (f k) * x ^ (k : ℕ)) = ι (f k) * (w * x ^ (k : ℕ)) by ring, himLc, mul_comm]
  have hBnonreal : ∀ x : Ri R, x ∈ herRoots P Q → Ri.conj R x ≠ x →
      B x + B (Ri.conj R x) = ι (2 * Ri.reL (A x)) := by
    intro x hxmem hxr
    set lrx : R := herFormVec P Q P.natDegree x ⬝ᵥ f with hlrx
    set lrc : R := herFormVec P Q P.natDegree (Ri.conj R x) ⬝ᵥ f with hlrc
    -- pair the two `B` terms via `herCoeff (conj x) = - herCoeff x`
    have hBpair : B x + B (Ri.conj R x)
        = ι (herCoeff P Q x * (lrx ^ 2 - lrc ^ 2)) := by
      rw [hB]
      dsimp only
      rw [herCoeff_conj_of_not_real P Q hxr, ← hlrx, ← hlrc]
      simp only [← map_pow, ← map_mul, ← map_add]
      congr 1
      ring
    rw [hBpair]
    -- reduce to the `R`-level identity
    congr 1
    -- the `R`-level identity: `herCoeff x * (lrx² - lrc²) = 2 * reL (A x)`
    have hcc : Ri.conj R (Ri.conj R x) = x := Ri.conj_conj R x
    have himne : Ri.imL x ≠ 0 := imL_ne_zero_of_not_real hxr
    by_cases hpos : 0 < Ri.imL x
    · -- positive imaginary part: `w = herSqrt x`, `lrx = reL (w·lcv x)`, `lrc = imL (w·lcv x)`
      set w : Ri R := herSqrt P Q x with hw
      have hwsq : w ^ 2 = herWeight P Q x := herSqrt_sq P Q x
      have hcjneg : ¬ (0 < Ri.imL (Ri.conj R x)) := by
        rw [imL_conj]; exact not_lt.mpr (le_of_lt (neg_neg_of_pos hpos))
      have hlrx_pos : lrx = Ri.reL (w * lcv x) := by
        rw [hlrx, dotProduct, hreL_wlcv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [herFormVec, if_neg hxr, if_pos hpos, reL_mul]
      have hlrc_pos : lrc = Ri.imL (w * lcv x) := by
        rw [hlrc, dotProduct, himL_wlcv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [herFormVec, if_neg (by rw [hcc]; exact fun h => hxr h.symm), if_neg hcjneg]
        simp only [hcc]
        rw [hw, imL_mul]
      rw [hlrx_pos, hlrc_pos, herCoeff, if_neg hxr, if_pos hpos]
      -- `reL(wL)² − imL(wL)² = reL((wL)²) = reL(A x)`
      have hsq : Ri.reL (w * lcv x) ^ 2 - Ri.imL (w * lcv x) ^ 2 = Ri.reL (A x) := by
        rw [← reL_sq, mul_pow, hwsq]
      rw [show Ri.reL (w * lcv x) ^ 2 - Ri.imL (w * lcv x) ^ 2 = Ri.reL (A x) from hsq]
    · -- negative imaginary part: `w' = herSqrt (conj x)`
      have hneg : Ri.imL x < 0 := lt_of_le_of_ne (not_lt.mp hpos) himne
      set w' : Ri R := herSqrt P Q (Ri.conj R x) with hw'
      have hw'sq : w' ^ 2 = herWeight P Q (Ri.conj R x) := herSqrt_sq P Q (Ri.conj R x)
      have hcjpos : 0 < Ri.imL (Ri.conj R x) := by
        rw [imL_conj]; exact neg_pos.mpr hneg
      have hlrx_neg : lrx = Ri.imL (w' * lcv (Ri.conj R x)) := by
        rw [hlrx, dotProduct, himL_wlcv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [herFormVec, if_neg hxr, if_neg hpos, imL_mul, ← hw']
      have hlrc_neg : lrc = Ri.reL (w' * lcv (Ri.conj R x)) := by
        rw [hlrc, dotProduct, hreL_wlcv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [herFormVec, if_neg (by rw [hcc]; exact fun h => hxr h.symm), if_pos hcjpos, reL_mul,
          ← hw']
      rw [hlrx_neg, hlrc_neg, herCoeff, if_neg hxr, if_neg hpos]
      -- `−2·(imL(w'L')² − reL(w'L')²) = 2·reL((w'L')²) = 2·reL(conj (A x)) = 2·reL (A x)`
      have hsq : Ri.reL (w' * lcv (Ri.conj R x)) ^ 2 - Ri.imL (w' * lcv (Ri.conj R x)) ^ 2
          = Ri.reL (A x) := by
        rw [← reL_sq, mul_pow, hw'sq,
          show herWeight P Q (Ri.conj R x) * lcv (Ri.conj R x) ^ 2 = A (Ri.conj R x) from rfl,
          hAconj, reL_conj]
      linear_combination (2 : R) * hsq
  -- reduce ∑ A = ∑ B to ∑ (A - B) = 0
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_involution (fun x _ => Ri.conj R x) ?_ ?_ ?_ ?_
  · -- (A - B) x + (A - B) (conj x) = 0
    intro x hx
    show A x - B x + (A (Ri.conj R x) - B (Ri.conj R x)) = 0
    by_cases hxr : Ri.conj R x = x
    · -- real: both terms vanish
      rw [hBreal x hx hxr, hxr, hBreal x hx hxr]; ring
    · -- non-real: pair up
      have key := hBnonreal x hx hxr
      have hAsum : A x + A (Ri.conj R x) = ι (2 * Ri.reL (A x)) := (hreal_A x).symm
      linear_combination hAsum - key
  · -- (A - B) x ≠ 0 → conj x ≠ x
    intro x hx hne hxr
    apply hne
    show A x - B x = 0
    rw [hBreal x hx hxr]; ring
  · -- conj x ∈ herRoots P Q
    intro x hx
    exact conj_mem_herRoots hx
  · -- conj (conj x) = x
    intro x _
    exact Ri.conj_conj R x

set_option linter.unusedSectionVars false in
/-- The number of distinct roots in `herRoots` is at most `deg P` (with `P` monic). -/
theorem card_herRoots_le (P Q : R[X]) (hP : P.Monic) :
    (herRoots P Q).card ≤ P.natDegree := by
  classical
  have hPne : P ≠ 0 := hP.ne_zero
  have hmapne : P.map (algebraMap R (Ri R)) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff (algebraMap R (Ri R)).injective]; exact hPne
  calc (herRoots P Q).card
      ≤ (P.aroots (Ri R)).toFinset.card := by
        rw [herRoots]; exact Finset.card_filter_le _ _
    _ ≤ Multiset.card (P.aroots (Ri R)) := Multiset.toFinset_card_le _
    _ ≤ (P.map (algebraMap R (Ri R))).natDegree := by
        rw [Polynomial.aroots]; exact Polynomial.card_roots' _
    _ = P.natDegree := Polynomial.natDegree_map_eq_of_injective (algebraMap R (Ri R)).injective P

set_option linter.unusedSectionVars false in
/-- **Vandermonde independence.** The `r` Vandermonde vectors `(xⱼᵏ)ₖ` over `C = Ri R` for the
`r ≤ p` distinct roots `xⱼ ∈ herRoots P Q` are `C`-linearly independent (as vectors in
`Fin p → Ri R`). -/
theorem vandermonde_herRoots_indep (P Q : R[X]) (p : ℕ) (hrp : (herRoots P Q).card ≤ p) :
    LinearIndependent (Ri R)
      (fun j : Fin (herRoots P Q).card =>
        (fun k : Fin p => ((herRoots P Q).equivFin.symm j : Ri R) ^ (k : ℕ))) := by
  classical
  set r := (herRoots P Q).card with hr
  set pts : Fin r → Ri R := fun j => ((herRoots P Q).equivFin.symm j : Ri R) with hpts
  -- the `r × r` Vandermonde minor is invertible (points distinct)
  have hinj : Function.Injective pts := by
    intro a b hab
    exact (herRoots P Q).equivFin.symm.injective (Subtype.ext hab)
  have hdet : (Matrix.vandermonde pts).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hindep_r : LinearIndependent (Ri R) (fun j : Fin r => Matrix.vandermonde pts j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  -- project `Fin p → C` onto the first `r` coordinates
  let proj : (Fin p → Ri R) →ₗ[Ri R] (Fin r → Ri R) :=
    LinearMap.funLeft (Ri R) (Ri R) (fun i : Fin r => Fin.castLE hrp i)
  refine LinearIndependent.of_comp proj ?_
  -- `proj ∘ (Vandermonde in Fin p)` is the `r × r` Vandermonde
  have hcomp : (⇑proj ∘ fun j : Fin r => (fun k : Fin p => pts j ^ (k : ℕ)))
      = fun j : Fin r => Matrix.vandermonde pts j := by
    funext j
    funext i
    simp only [Function.comp_apply, proj, LinearMap.funLeft_apply, Matrix.vandermonde_apply,
      Fin.val_castLE]
  rw [hcomp]
  exact hindep_r

set_option linter.unusedSectionVars false in
/-- The `ι`-images of the Hermite form vectors are `C`-linearly independent. (Each is a
`C`-combination of the two Vandermonde vectors `(xⱼᵏ)`, `((conj xⱼ)ᵏ)`, related by an
invertible block; combined with Vandermonde independence this gives independence.) -/
theorem herFormVec_image_C_indep (P Q : R[X]) (hP : P.Monic) :
    LinearIndependent (Ri R)
      (fun j : Fin (herRoots P Q).card =>
        (fun k : Fin P.natDegree =>
          algebraMap R (Ri R)
            (herFormVec P Q P.natDegree ((herRoots P Q).equivFin.symm j : Ri R) k))) := by
  classical
  set ι := algebraMap R (Ri R) with hι
  set eqv := (herRoots P Q).equivFin with heqv
  set p := P.natDegree with hp
  -- abbreviations: `F y k = ι (herFormVec y k)`
  set F : Ri R → Fin p → Ri R := fun y k => ι (herFormVec P Q p y k) with hF
  -- helper: `i ≠ 0`
  have hine : Ri.i R ≠ 0 := by
    intro h; have := Ri.i_sq R; rw [h] at this; simp at this
  have h2ne : (2 : Ri R) ≠ 0 := by
    rw [show (2 : Ri R) = ι 2 by rw [hι, map_ofNat], hι, ← map_zero (algebraMap R (Ri R))]
    intro h
    exact (two_ne_zero : (2 : R) ≠ 0) ((algebraMap R (Ri R)).injective h)
  -- helper: `2 • reL` and the conjugate-difference identity
  have h2reL : ∀ c : Ri R, ι (2 * Ri.reL c) = c + Ri.conj R c := fun c => (conj_add_self c).symm
  have himL_diff : ∀ c : Ri R, c - Ri.conj R c = 2 * (ι (Ri.imL c) * Ri.i R) := by
    intro c
    obtain ⟨a, b, hab⟩ := Ri.repr_exists c
    have hb : Ri.imL c = b := by
      rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (X ^ 2 + 1 : R[X]) a from rfl,
        show algebraMap R (Ri R) b = AdjoinRoot.of (X ^ 2 + 1 : R[X]) b from rfl, Ri.imL_lin]
    rw [hb, hab, hι, Ri.conj_repr]
    ring
  have hisq : Ri.i R * Ri.i R = -1 := by have := Ri.i_sq R; rwa [pow_two] at this
  have h2imL : ∀ c : Ri R, 2 * ι (Ri.imL c) = Ri.i R * (Ri.conj R c - c) := by
    intro c
    have h := himL_diff c
    -- `c - conj c = 2 (ι(imL c) i)`; multiply by `-i`
    have : Ri.i R * (Ri.conj R c - c) = Ri.i R * (- (2 * (ι (Ri.imL c) * Ri.i R))) := by
      rw [← h]; ring
    rw [this]
    rw [show Ri.i R * (- (2 * (ι (Ri.imL c) * Ri.i R)))
          = -2 * ι (Ri.imL c) * (Ri.i R * Ri.i R) by ring, hisq]
    ring
  -- coefficient functions `cF`, `eF`
  set w : Ri R → Ri R := fun x => herSqrt P Q x with hw
  have hwx : ∀ y : Ri R, w y = herSqrt P Q y := fun y => rfl
  set cF : Ri R → Ri R := fun x =>
    if Ri.conj R x = x then 2
    else if 0 < Ri.imL x then w x else Ri.i R * Ri.conj R (w (Ri.conj R x)) with hcF
  set eF : Ri R → Ri R := fun x =>
    if Ri.conj R x = x then 0
    else if 0 < Ri.imL x then Ri.conj R (w x) else - Ri.i R * w (Ri.conj R x) with heF
  -- the key per-component identity
  have h2F : ∀ x ∈ herRoots P Q, ∀ k : Fin p,
      2 * F x k = cF x * x ^ (k : ℕ) + eF x * (Ri.conj R x) ^ (k : ℕ) := by
    intro x hxmem k
    rw [hF, hcF, heF]
    dsimp only
    by_cases hxr : Ri.conj R x = x
    · -- real
      rw [if_pos hxr, if_pos hxr]
      have hpowfix : Ri.conj R (x ^ (k : ℕ)) = x ^ (k : ℕ) := by rw [map_pow, hxr]
      have : ι (Ri.reL (x ^ (k : ℕ))) = x ^ (k : ℕ) := by
        rw [hι]; exact algebraMap_reL_of_conj_fixed hpowfix
      rw [herFormVec, if_pos hxr, this]
      ring
    · rw [if_neg hxr, if_neg hxr]
      by_cases hpos : 0 < Ri.imL x
      · -- positive imaginary part
        rw [if_pos hpos, if_pos hpos]
        rw [herFormVec, if_neg hxr, if_pos hpos]
        simp only [← hwx]
        rw [show Ri.reL (w x) * Ri.reL (x ^ (k:ℕ)) - Ri.imL (w x) * Ri.imL (x ^ (k:ℕ))
              = Ri.reL (w x * x ^ (k:ℕ)) from (reL_mul _ _).symm,
          show (2 : Ri R) * ι (Ri.reL (w x * x ^ (k:ℕ)))
              = ι (2 * Ri.reL (w x * x ^ (k:ℕ))) by rw [← map_ofNat ι 2, ← map_mul],
          h2reL, map_mul, map_pow]
      · -- negative imaginary part
        rw [if_neg hpos, if_neg hpos]
        rw [herFormVec, if_neg hxr, if_neg hpos]
        simp only [← hwx]
        rw [show Ri.reL (w (Ri.conj R x)) * Ri.imL ((Ri.conj R x) ^ (k:ℕ))
                + Ri.imL (w (Ri.conj R x)) * Ri.reL ((Ri.conj R x) ^ (k:ℕ))
              = Ri.imL (w (Ri.conj R x) * (Ri.conj R x) ^ (k:ℕ)) from (imL_mul _ _).symm,
          h2imL, map_mul, map_pow, Ri.conj_conj]
        ring
  -- `w` is nonzero on `herRoots`
  have hw_ne : ∀ x ∈ herRoots P Q, w x ≠ 0 := by
    intro x hxmem hwx0
    have : herWeight P Q x = 0 := by
      have := herSqrt_sq P Q x
      rw [← hwx x, hwx0] at this
      simpa using this.symm
    exact herWeight_ne_zero P Q hxmem this
  -- recovery values of `cF`, `eF`
  have hcF_real : ∀ x : Ri R, Ri.conj R x = x → cF x = 2 := fun x h => by rw [hcF]; simp [h]
  have heF_real : ∀ x : Ri R, Ri.conj R x = x → eF x = 0 := fun x h => by rw [heF]; simp [h]
  have hcF_pos : ∀ x : Ri R, ¬ Ri.conj R x = x → 0 < Ri.imL x → cF x = w x :=
    fun x h1 h2 => by rw [hcF]; simp [h1, h2]
  have heF_pos : ∀ x : Ri R, ¬ Ri.conj R x = x → 0 < Ri.imL x → eF x = Ri.conj R (w x) :=
    fun x h1 h2 => by rw [heF]; simp [h1, h2]
  have hcF_neg : ∀ x : Ri R, ¬ Ri.conj R x = x → ¬ 0 < Ri.imL x →
      cF x = Ri.i R * Ri.conj R (w (Ri.conj R x)) := fun x h1 h2 => by rw [hcF]; simp [h1, h2]
  have heF_neg : ∀ x : Ri R, ¬ Ri.conj R x = x → ¬ 0 < Ri.imL x →
      eF x = - Ri.i R * w (Ri.conj R x) := fun x h1 h2 => by rw [heF]; simp [h1, h2]
  -- main: use the finite criterion for linear independence
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- transport `g` to a function on `herRoots`
  set G : Ri R → Ri R := fun y => if h : y ∈ herRoots P Q then g (eqv ⟨y, h⟩) else 0 with hG
  have hGy : ∀ (y : herRoots P Q), G (y : Ri R) = g (eqv y) := by
    intro y; rw [hG]; simp only [y.2, dif_pos]
  -- `hg` says `∀ k, ∑ j, g j • F (eqv.symm j) k = 0`; rewrite over `herRoots`
  have hgk : ∀ k : Fin p, ∑ y ∈ herRoots P Q, G y * F y k = 0 := by
    intro k
    have hgk0 := congrArg (fun v : Fin p → Ri R => v k) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgk0
    rw [← hgk0]
    rw [← Finset.sum_coe_sort (herRoots P Q) (fun y => G y * F y k)]
    rw [← Equiv.sum_comp eqv.symm (fun y : herRoots P Q => G (y : Ri R) * F (y : Ri R) k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((eqv.symm j : herRoots P Q) : Ri R) = (eqv.symm j : Ri R) from rfl, hGy]
    rw [Equiv.apply_symm_apply, mul_comm]
  -- define `D y = G y * cF y + G (conj y) * eF (conj y)`; show `∀ k, ∑ D y y^k = 0`
  set D : Ri R → Ri R := fun y => G y * cF y + G (Ri.conj R y) * eF (Ri.conj R y) with hD
  have hDk : ∀ k : Fin p, ∑ y ∈ herRoots P Q, D y * y ^ (k : ℕ) = 0 := by
    intro k
    have h2 : (2 : Ri R) * ∑ y ∈ herRoots P Q, G y * F y k = 0 := by rw [hgk k, mul_zero]
    rw [Finset.mul_sum] at h2
    -- expand each term via `h2F`
    have hexp : ∑ y ∈ herRoots P Q, 2 * (G y * F y k)
        = ∑ y ∈ herRoots P Q, (G y * cF y * y ^ (k:ℕ) + G y * eF y * (Ri.conj R y) ^ (k:ℕ)) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [show 2 * (G y * F y k) = G y * (2 * F y k) by ring, h2F y hy k]
      ring
    rw [hexp, Finset.sum_add_distrib] at h2
    -- reindex the second sum by conjugation
    have hreindex : ∑ y ∈ herRoots P Q, G y * eF y * (Ri.conj R y) ^ (k:ℕ)
        = ∑ y ∈ herRoots P Q, G (Ri.conj R y) * eF (Ri.conj R y) * y ^ (k:ℕ) := by
      refine Finset.sum_nbij' (fun y => Ri.conj R y) (fun y => Ri.conj R y) ?_ ?_ ?_ ?_ ?_
      · intro y hy; exact conj_mem_herRoots hy
      · intro y hy; exact conj_mem_herRoots hy
      · intro y _; rw [Ri.conj_conj]
      · intro y _; rw [Ri.conj_conj]
      · intro y _; rw [Ri.conj_conj]
    rw [hreindex] at h2
    rw [← Finset.sum_add_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hD]; ring
  -- Vandermonde: `D y = 0` for all `y ∈ herRoots`
  have hD0 : ∀ y ∈ herRoots P Q, D y = 0 := by
    have hvand := vandermonde_herRoots_indep P Q p (hp ▸ card_herRoots_le P Q hP)
    rw [Fintype.linearIndependent_iff] at hvand
    -- the coefficient function `j ↦ D (pts j)`
    have hvand0 := hvand (fun j => D ((herRoots P Q).equivFin.symm j : Ri R)) ?_
    · intro y hy
      have := hvand0 (eqv ⟨y, hy⟩)
      rwa [show ((herRoots P Q).equivFin.symm (eqv ⟨y, hy⟩) : Ri R) = (y : Ri R) by
        rw [heqv, Equiv.symm_apply_apply]] at this
    · funext k
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply]
      rw [← hDk k]
      rw [← Finset.sum_coe_sort (herRoots P Q) (fun y => D y * y ^ (k:ℕ))]
      rw [← Equiv.sum_comp (herRoots P Q).equivFin.symm
            (fun y : herRoots P Q => D (y : Ri R) * (y : Ri R) ^ (k:ℕ))]
  -- recovery: `D = 0` forces `g = 0`
  intro j
  -- reduce to `G = 0` on `herRoots`
  suffices hGmem : ∀ y ∈ herRoots P Q, G y = 0 by
    have := hGmem (eqv.symm j : Ri R) (eqv.symm j).2
    rwa [show (eqv.symm j : Ri R) = ((eqv.symm j : herRoots P Q) : Ri R) from rfl,
      hGy, Equiv.apply_symm_apply] at this
  -- prove `G z = 0` and `G (conj z) = 0` for the pos-im representative `z`
  have hGpair : ∀ z ∈ herRoots P Q, ¬ Ri.conj R z = z → 0 < Ri.imL z →
      G z = 0 ∧ G (Ri.conj R z) = 0 := by
    intro z hz hzr hzpos
    have hcjmem : Ri.conj R z ∈ herRoots P Q := conj_mem_herRoots hz
    have hcjr : ¬ Ri.conj R (Ri.conj R z) = Ri.conj R z := by
      rw [Ri.conj_conj]; exact fun h => hzr h.symm
    have hcjneg : ¬ 0 < Ri.imL (Ri.conj R z) := by
      rw [imL_conj]; exact not_lt.mpr (le_of_lt (neg_neg_of_pos hzpos))
    have hwz : w z ≠ 0 := hw_ne z hz
    have hwcz : Ri.conj R (w z) ≠ 0 := fun h => hwz (by
      have := congrArg (Ri.conj R) h; rwa [Ri.conj_conj, map_zero] at this)
    -- `D z = w z * (G z - i * G (conj z))`
    have hDz : w z * (G z - Ri.i R * G (Ri.conj R z)) = 0 := by
      have hh := hD0 z hz
      simp only [hD, hcF_pos z hzr hzpos, heF_neg (Ri.conj R z) hcjr hcjneg, Ri.conj_conj] at hh
      rw [← hh]; ring
    -- `D (conj z) = conj (w z) * (G z + i * G (conj z))`
    have hDcz : Ri.conj R (w z) * (G z + Ri.i R * G (Ri.conj R z)) = 0 := by
      have hh := hD0 (Ri.conj R z) hcjmem
      simp only [hD, hcF_neg (Ri.conj R z) hcjr hcjneg, heF_pos z hzr hzpos, Ri.conj_conj] at hh
      rw [← hh]; ring
    -- conclude
    have e1 : G z - Ri.i R * G (Ri.conj R z) = 0 :=
      (mul_eq_zero.mp hDz).resolve_left hwz
    have e2 : G z + Ri.i R * G (Ri.conj R z) = 0 :=
      (mul_eq_zero.mp hDcz).resolve_left hwcz
    have h2gz : (2 : Ri R) * G z = 0 := by linear_combination e1 + e2
    have hGz : G z = 0 := (mul_eq_zero.mp h2gz).resolve_left h2ne
    refine ⟨hGz, ?_⟩
    have hiG : Ri.i R * G (Ri.conj R z) = 0 := by linear_combination hGz - e1
    exact (mul_eq_zero.mp hiG).resolve_left hine
  intro y hy
  by_cases hyr : Ri.conj R y = y
  · -- real: `D y = 2 * G y`
    have hh := hD0 y hy
    simp only [hD, hcF_real y hyr, heF_real y hyr, hyr] at hh
    have h2g : (2 : Ri R) * G y = 0 := by rw [← hh]; ring
    exact (mul_eq_zero.mp h2g).resolve_left h2ne
  · -- non-real: reduce to the pos-im representative
    by_cases hypos : 0 < Ri.imL y
    · exact (hGpair y hy hyr hypos).1
    · -- `y` neg-im, so `conj y` is the pos-im representative
      have hcjmem : Ri.conj R y ∈ herRoots P Q := conj_mem_herRoots hy
      have hcjr : ¬ Ri.conj R (Ri.conj R y) = Ri.conj R y := by
        rw [Ri.conj_conj]; exact fun h => hyr h.symm
      have hcjpos : 0 < Ri.imL (Ri.conj R y) := by
        rw [imL_conj]
        have hyne : Ri.imL y ≠ 0 := imL_ne_zero_of_not_real hyr
        exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hypos) hyne)
      have := (hGpair (Ri.conj R y) hcjmem hcjr hcjpos).2
      rwa [Ri.conj_conj] at this

set_option linter.unusedSectionVars false in
/-- The Hermite form vectors `herFormVec` (at the distinct roots) are `R`-linearly independent. -/
theorem herFormVec_indep (P Q : R[X]) (hP : P.Monic) :
    LinearIndependent R
      (fun j : Fin (herRoots P Q).card =>
        herFormVec P Q P.natDegree ((herRoots P Q).equivFin.symm j : Ri R)) := by
  classical
  -- map componentwise by `ι = algebraMap R (Ri R)` (injective `R`-linear)
  let g : (Fin P.natDegree → R) →ₗ[R] (Fin P.natDegree → Ri R) :=
    LinearMap.compLeft (Algebra.linearMap R (Ri R)) (Fin P.natDegree)
  refine LinearIndependent.of_comp g ?_
  -- the image family is `C`-linearly independent, hence `R`-linearly independent
  have hC := herFormVec_image_C_indep P Q hP
  have hRimg : LinearIndependent R
      (fun j : Fin (herRoots P Q).card =>
        (fun k : Fin P.natDegree =>
          algebraMap R (Ri R)
            (herFormVec P Q P.natDegree ((herRoots P Q).equivFin.symm j : Ri R) k))) := by
    refine hC.restrict_scalars ?_
    intro a b hab
    apply (algebraMap R (Ri R)).injective
    simpa only [Algebra.smul_def, mul_one] using hab
  -- `⇑g ∘ vecs` is exactly that image family
  convert hRimg using 1

/-- **The Hermite diagonal expression.** A diagonal expression of `quadraticForm (HerMatR P Q)`
with `r = #(herRoots P Q)` terms, indexed by the distinct roots of `P` in `C = Ri R` at
which `Q` does not vanish, with coefficients `herCoeff` and forms `herDotLM (herFormVec …)`. -/
noncomputable def herDiagExpr (P Q : R[X]) (hP : P.Monic) :
    DiagonalExpression (quadraticForm (HerMatR P Q)) where
  r := (herRoots P Q).card
  coeff j := herCoeff P Q ((herRoots P Q).equivFin.symm j : Ri R)
  form j := herDotLM (herFormVec P Q P.natDegree ((herRoots P Q).equivFin.symm j : Ri R))
  coeff_ne_zero := by
    intro j
    set x : Ri R := ((herRoots P Q).equivFin.symm j : Ri R) with hx
    have hxmem : x ∈ herRoots P Q := ((herRoots P Q).equivFin.symm j).2
    rw [herCoeff]
    split_ifs with hreal himpos
    · -- real root: reL of a nonzero real value
      intro hzero
      have hfix : Ri.conj R (herWeight P Q x) = herWeight P Q x := by
        rw [herWeight, map_nsmul]
        congr 1
        rw [← Polynomial.aeval_algHom_apply, hreal]
      have hw0 : herWeight P Q x = 0 := by
        rw [← algebraMap_reL_of_conj_fixed hfix, hzero, map_zero]
      exact herWeight_ne_zero P Q hxmem hw0
    · norm_num
    · norm_num
  form_indep := by
    classical
    -- `herDotLM` as a bundled injective `R`-linear map `v ↦ (f ↦ v ⬝ᵥ f)`
    let D : (Fin P.natDegree → R) →ₗ[R] ((Fin P.natDegree → R) →ₗ[R] R) :=
      { toFun := fun v => herDotLM v
        map_add' := fun v w => by
          refine LinearMap.ext fun f => ?_
          simp only [herDotLM_apply, LinearMap.add_apply, add_dotProduct]
        map_smul' := fun c v => by
          refine LinearMap.ext fun f => ?_
          simp only [herDotLM_apply, LinearMap.smul_apply, smul_dotProduct, RingHom.id_apply,
            smul_eq_mul] }
    have hDker : LinearMap.ker D = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      funext k
      have hvk : herDotLM v (Pi.single k 1) = 0 := by
        have := congrFun (congrArg DFunLike.coe hv) (Pi.single k 1)
        simpa only [D, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] using this
      rw [herDotLM_apply, dotProduct_single, mul_one] at hvk
      simpa using hvk
    exact (herFormVec_indep P Q hP).map' D hDker
  apply_eq := by
    intro f
    rw [herApply_eq P Q hP f]
    rw [← Finset.sum_coe_sort (herRoots P Q)
      (fun x => herCoeff P Q x * (herFormVec P Q P.natDegree x ⬝ᵥ f) ^ 2),
      ← Equiv.sum_comp (herRoots P Q).equivFin.symm
        (fun x : herRoots P Q =>
          herCoeff P Q (x : Ri R) * (herFormVec P Q P.natDegree (x : Ri R) ⬝ᵥ f) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [herDotLM_apply]

set_option linter.unusedSectionVars false in
/-- Reindexing helper: the number of `j : Fin s.card` with `p (s.equivFin.symm j)` equals
the cardinality of `s.filter p`. -/
theorem card_filter_equivFin {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun j : Fin s.card => p (s.equivFin.symm j : α))).card
      = (s.filter p).card := by
  classical
  refine Finset.card_bij' (fun j _ => (s.equivFin.symm j : α))
    (fun a ha => s.equivFin ⟨a, (Finset.mem_filter.mp ha).1⟩) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨(s.equivFin.symm j).2, hj.2⟩
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ha.2
  · intro j _
    rw [Equiv.apply_symm_apply]
  · intro a ha
    simp

set_option linter.unusedSectionVars false in
/-- `posCount` of the Hermite diagonal expression as a filter over `herRoots`. -/
theorem herDiagExpr_posCount (P Q : R[X]) (hP : P.Monic) :
    (herDiagExpr P Q hP).posCount
      = ((herRoots P Q).filter (fun x => 0 < herCoeff P Q x)).card := by
  classical
  rw [DiagonalExpression.posCount]
  exact card_filter_equivFin (herRoots P Q) (fun x => 0 < herCoeff P Q x)

set_option linter.unusedSectionVars false in
/-- `negCount` of the Hermite diagonal expression as a filter over `herRoots`. -/
theorem herDiagExpr_negCount (P Q : R[X]) (hP : P.Monic) :
    (herDiagExpr P Q hP).negCount
      = ((herRoots P Q).filter (fun x => herCoeff P Q x < 0)).card := by
  classical
  rw [DiagonalExpression.negCount]
  exact card_filter_equivFin (herRoots P Q) (fun x => herCoeff P Q x < 0)

set_option linter.unusedSectionVars false in
/-- For a function `c` nonvanishing on a finite set `s`,
`#{x ∈ s | 0 < c x} − #{x ∈ s | c x < 0} = ∑_{x ∈ s} sign(c x)`. -/
theorem card_pos_sub_card_neg_eq_sum_sign {α : Type*} (s : Finset α) (c : α → R)
    (hc : ∀ x ∈ s, c x ≠ 0) :
    ((s.filter (fun x => 0 < c x)).card : ℤ) - (s.filter (fun x => c x < 0)).card
      = ∑ x ∈ s, (SignType.sign (c x) : ℤ) := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rcases lt_or_gt_of_ne (hc x hx) with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), if_pos hneg, sign_neg hneg]
    simp
  · rw [if_pos hpos, if_neg (not_lt.mpr hpos.le), sign_pos hpos]
    simp

/-! ### Real roots correspond to roots of `P` over `R` -/

omit [IsRealClosed R] in
/-- `aeval (algebraMap y) P = algebraMap (P.eval y)`. -/
theorem aeval_algebraMap_eq (P : R[X]) (y : R) :
    aeval (algebraMap R (Ri R) y) P = algebraMap R (Ri R) (P.eval y) := by
  rw [Polynomial.aeval_algebraMap_apply]; norm_cast

/-- A conj-fixed root `x ∈ herRoots` arises from a real root `y = reL x` of `P` with
`Q.eval y ≠ 0`; the sign of `herCoeff` matches `sign (Q.eval y)`. -/
theorem sign_herCoeff_real {P Q : R[X]} {x : Ri R} (hx : x ∈ herRoots P Q)
    (hxr : Ri.conj R x = x) :
    SignType.sign (herCoeff P Q x) = SignType.sign (Q.eval (Ri.reL x)) := by
  have hmap : algebraMap R (Ri R) (Ri.reL x) = x := algebraMap_reL_of_conj_fixed hxr
  rw [herCoeff, if_pos hxr]
  -- herWeight x = count • aeval x Q = algebraMap (count • Q.eval (reL x))
  have hweight : herWeight P Q x
      = algebraMap R (Ri R) ((Multiset.count x (P.aroots (Ri R))) • Q.eval (Ri.reL x)) := by
    rw [herWeight, map_nsmul]
    congr 1
    rw [← aeval_algebraMap_eq, hmap]
  have hfix : Ri.conj R (herWeight P Q x) = herWeight P Q x := by
    rw [hweight, Ri.conj_algebraMap_ordered]
  have hreL : Ri.reL (herWeight P Q x)
      = (Multiset.count x (P.aroots (Ri R))) • Q.eval (Ri.reL x) := by
    apply (algebraMap R (Ri R)).injective
    rw [algebraMap_reL_of_conj_fixed hfix, hweight]
  rw [hreL, nsmul_eq_mul]
  have hcount : 0 < (Multiset.count x (P.aroots (Ri R)) : R) := by
    have : 0 < Multiset.count x (P.aroots (Ri R)) :=
      Multiset.count_pos.mpr ((mem_herRoots_iff P Q x).mp hx).1
    exact_mod_cast this
  rw [sign_mul, sign_pos hcount, one_mul]

set_option linter.unusedSectionVars false in
/-- `algebraMap y ∈ aroots P` iff `P ≠ 0 ∧ P.eval y = 0` (real root over `R`). -/
theorem algebraMap_mem_aroots (P : R[X]) (y : R) :
    algebraMap R (Ri R) y ∈ P.aroots (Ri R) ↔ P ≠ 0 ∧ P.eval y = 0 := by
  rw [Polynomial.mem_aroots, aeval_algebraMap_eq]
  have hinj : algebraMap R (Ri R) (P.eval y) = 0 ↔ P.eval y = 0 := by
    rw [show (0 : Ri R) = algebraMap R (Ri R) 0 from (map_zero _).symm]
    exact ⟨fun h => (algebraMap R (Ri R)).injective h, fun h => by rw [h]⟩
  rw [hinj]

/-- The sum of `sign(herCoeff)` over the non-real roots vanishes (conjugate pairs cancel). -/
theorem sum_sign_herCoeff_nonreal (P Q : R[X]) :
    ∑ x ∈ (herRoots P Q).filter (fun x => ¬ Ri.conj R x = x),
        (SignType.sign (herCoeff P Q x) : ℤ) = 0 := by
  classical
  refine Finset.sum_involution (fun x _ => Ri.conj R x) ?_ ?_ ?_ ?_
  · -- f x + f (conj x) = 0
    intro x hx
    have hxr : ¬ Ri.conj R x = x := (Finset.mem_filter.mp hx).2
    rw [herCoeff_conj_of_not_real P Q hxr, Left.sign_neg]
    push_cast
    ring
  · -- f x ≠ 0 → conj x ≠ x
    intro x hx _
    exact (Finset.mem_filter.mp hx).2
  · -- conj x ∈ the filtered set
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨conj_mem_herRoots hx.1, ?_⟩
    intro h
    exact hx.2 (by rw [← h, Ri.conj_conj])
  · -- conj (conj x) = x
    intro x _
    exact Ri.conj_conj R x

/-- **The signature sum.** `∑_{x ∈ herRoots} sign(herCoeff x) = TaQ(Q, P)`. -/
theorem sum_sign_herCoeff (P Q : R[X]) :
    ∑ x ∈ herRoots P Q, (SignType.sign (herCoeff P Q x) : ℤ) = tarskiQuery Q P := by
  classical
  -- split into real and non-real parts
  rw [← Finset.sum_filter_add_sum_filter_not (herRoots P Q) (fun x => Ri.conj R x = x),
    sum_sign_herCoeff_nonreal, add_zero]
  rw [tarskiQuery_eq_sum_roots]
  -- the real part is a sum over real roots; the `Q = 0` roots contribute 0
  rw [← Finset.sum_filter_of_ne (p := fun y => Q.eval y ≠ 0)
    (s := P.roots.toFinset) (f := fun y => (SignType.sign (Q.eval y) : ℤ)) ?_]
  · -- bijection between real `herRoots` and `{y ∈ P.roots.toFinset | Q.eval y ≠ 0}`
    refine Finset.sum_nbij' (fun x => Ri.reL x) (fun y => algebraMap R (Ri R) y) ?_ ?_ ?_ ?_ ?_
    · -- hi: reL x is a real root with Q ≠ 0
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxmem := hx.1
      have hxr : Ri.conj R x = x := hx.2
      have hmap : algebraMap R (Ri R) (Ri.reL x) = x := algebraMap_reL_of_conj_fixed hxr
      have hxaroots := ((mem_herRoots_iff P Q x).mp hxmem).1
      have hQ := ((mem_herRoots_iff P Q x).mp hxmem).2
      rw [← hmap] at hxaroots
      obtain ⟨hPne, hPev⟩ := (algebraMap_mem_aroots P (Ri.reL x)).mp hxaroots
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨⟨hPne, hPev⟩, ?_⟩
      -- Q.eval (reL x) ≠ 0 since aeval x Q ≠ 0
      intro hQev
      apply hQ
      rw [← hmap, aeval_algebraMap_eq, hQev, map_zero]
    · -- hj: algebraMap y ∈ real herRoots
      intro y hy
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots'] at hy
      rw [Finset.mem_filter]
      refine ⟨?_, by rw [Ri.conj_algebraMap_ordered]⟩
      rw [mem_herRoots_iff]
      refine ⟨(algebraMap_mem_aroots P y).mpr ⟨hy.1.1, hy.1.2⟩, ?_⟩
      rw [aeval_algebraMap_eq]
      intro h
      exact hy.2 ((algebraMap R (Ri R)).injective (by rw [h, map_zero]))
    · -- left_neg: algebraMap (reL x) = x
      intro x hx
      rw [Finset.mem_filter] at hx
      exact algebraMap_reL_of_conj_fixed hx.2
    · -- right_neg: reL (algebraMap y) = y
      intro y _
      rw [show algebraMap R (Ri R) y = AdjoinRoot.of (X ^ 2 + 1 : R[X]) y from rfl, Ri.reL_of]
    · -- sign matching
      intro x hx
      rw [Finset.mem_filter] at hx
      exact congrArg (fun s : SignType => (s : ℤ)) (sign_herCoeff_real hx.1 hx.2)
  · intro y _ hsign
    by_contra hne
    apply hsign
    rw [hne, sign_zero]
    simp

/-! ## Theorem 4.58 -/

/-- **BPR Theorem 4.58 (Hermite), rank part.** The rank of Hermite's quadratic form equals
the number of distinct roots `x` of `P` in `C = R[i]` at which `Q(x) ≠ 0`. -/
theorem theorem_4_58_rank (P Q : R[X]) (hP : P.Monic) :
    quadraticFormRank (HerMatR P Q)
      = ((P.aroots (Ri R)).toFinset.filter (fun x => Polynomial.aeval x Q ≠ 0)).card := by
  rw [← (herDiagExpr P Q hP).r_eq_quadraticFormRank (HerMatR_isSymm P Q)]
  rfl

/-- `herCoeff` is nonzero on `herRoots` (the diagonal coefficients are nonzero). -/
theorem herCoeff_ne_zero_on_herRoots {P Q : R[X]} {x : Ri R} (hx : x ∈ herRoots P Q) :
    herCoeff P Q x ≠ 0 := by
  rw [herCoeff]
  split_ifs with hreal himpos
  · intro hzero
    have hfix : Ri.conj R (herWeight P Q x) = herWeight P Q x := by
      rw [herWeight, map_nsmul]
      congr 1
      rw [← Polynomial.aeval_algHom_apply, hreal]
    have hw0 : herWeight P Q x = 0 := by
      rw [← algebraMap_reL_of_conj_fixed hfix, hzero, map_zero]
    exact herWeight_ne_zero P Q hx hw0
  · norm_num
  · norm_num

/-- **BPR Theorem 4.58 (Hermite), signature part.** The signature of Hermite's quadratic
form equals the Tarski query `TaQ(Q, P)`. -/
theorem theorem_4_58_sign (P Q : R[X]) (hP : P.Monic) :
    Sign (quadraticForm (HerMatR P Q)) = tarskiQuery Q P := by
  rw [← (herDiagExpr P Q hP).signature_eq, DiagonalExpression.signature,
    herDiagExpr_posCount, herDiagExpr_negCount,
    card_pos_sub_card_neg_eq_sum_sign (herRoots P Q) (herCoeff P Q)
      (fun x hx => herCoeff_ne_zero_on_herRoots hx),
    sum_sign_herCoeff]

end Azurite.BPR.Chapter4
