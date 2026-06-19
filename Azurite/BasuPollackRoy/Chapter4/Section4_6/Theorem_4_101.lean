import Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_100
import Azurite.BasuPollackRoy.Chapter4.Section4_6.TarskiQuery
import Azurite.BasuPollackRoy.Chapter4.Section4_3.QuadraticForm
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp
import Mathlib.LinearAlgebra.Vandermonde

/-!
# BPR §4.6, Theorem 4.101: Multivariate Hermite's quadratic form

Over a real closed field `R`, with `C = R[i] = Ri R`, let `𝒫` be a zero-dimensional system in
`R[X₁, …, X_k]`, `A = R[X]/Ideal(𝒫, R)` and `Q ∈ A`. Then the rank and signature of Hermite's
quadratic form `Her(𝒫, Q)` compute as

* `Rank(Her(𝒫, Q)) = #{x ∈ Zer(𝒫, Cᵏ) | Q(x) ≠ 0}`;
* `Sign(Her(𝒫, Q)) = TaQ(Q, 𝒫)` (the Tarski query — a sum of signs over the real zeros).

The proof transports `Her(𝒫, Q)` to a quadratic form on `Fin N → R` through a basis of `A` and
builds a `DiagonalExpression` of it (§4.3.1), exactly mirroring the univariate Hermite theorem
(BPR Theorem 4.58, `Theorem_4_58.lean`). The diagonal expression is indexed by the distinct zeros
`x ∈ Zer(𝒫, Cᵏ)` at which `Q(x) ≠ 0`; the coefficient of a real zero is the (real) weight
`μ(x) Q(x)`, while a conjugate pair of non-real zeros contributes a difference of two squares of
real linear forms (signature `0`). The linear forms are the evaluations `f ↦ ∑_k f_k ω_k(x)`, whose
linear independence comes from a separating element (Lemma 4.90/4.91) and a Vandermonde argument.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical Matrix
open Azurite.BPR Azurite.BPR.Theorem2_11

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Rank of Hermite's quadratic form** `Rank(Her(𝒫, Q))`: the rank of the quadratic form
`Her(𝒫, Q) = hermiteQuad Ps Q` on `A`, expressed as the sum of its positive and negative inertia
indices (which equals the rank of its Gram matrix in any basis, by Corollary 4.40 / §4.3.1). -/
noncomputable def hermiteFormRank (Ps : Finset (MvPolynomial (Fin k) R)) (Q : quotPolys Ps) : ℕ :=
  sigPos (hermiteQuad Ps Q) + sigNeg (hermiteQuad Ps Q)

/-- **Signature of Hermite's quadratic form** `Sign(Her(𝒫, Q))`: the difference of the positive and
negative inertia indices of `Her(𝒫, Q) = hermiteQuad Ps Q`. -/
noncomputable def hermiteFormSign (Ps : Finset (MvPolynomial (Fin k) R)) (Q : quotPolys Ps) : ℤ :=
  (sigPos (hermiteQuad Ps Q) : ℤ) - sigNeg (hermiteQuad Ps Q)

/-! ## The geometric bridge

Mapping `her(𝒫, Q')(u, w)` into `C = Ri R` gives the geometric sum
`∑_x μ(x) · u(x) · w(x) · Q'(x)` over the zeros. This generalizes `hermite_bridge` (the `Q' = 1`
case) to an arbitrary `Q' ∈ A`. -/

/-- **Key bridge.** Applying `R ↪ C = Ri R` to `her(𝒫, Q')(u, w)` gives the geometric sum
`∑_x μ(x) · u(x) · w(x) · Q'(x)` over the zeros. -/
theorem hermiteBilin_bridge (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (hfin : (zerOfFinset (Ri R) Ps).Finite)
    (Q' u w : quotPolys Ps) :
    algebraMap R (Ri R) (hermiteBilin Ps Q' u w)
      = ∑ x : hfin.toFinset,
          multiplicityOfZero (Ri R) Ps x.1 (hfin.mem_toFinset.mp x.2)
            • (valueAt (Ri R) Ps u x.1 (hfin.mem_toFinset.mp x.2)
                * valueAt (Ri R) Ps w x.1 (hfin.mem_toFinset.mp x.2)
                * valueAt (Ri R) Ps Q' x.1 (hfin.mem_toFinset.mp x.2)) := by
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  rw [hermiteBilin_apply, ← remark_4_99_trace (Ri R) Ps (u * w * Q')]
  have hmm : mulMapBaseExt (Ri R) Ps (u * w * Q')
      = mulMapExt (Ri R) Ps (inclExt (Ri R) Ps (u * w * Q')) := rfl
  rw [hmm, (theorem_4_98 Ps hfin (inclExt (Ri R) Ps (u * w * Q'))).1]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul]
  rfl

/-! ## Multivariate Hermite data over `C = Ri R` -/

namespace MvHermite

set_option linter.unusedSectionVars false

attribute [local instance] algebraLocalizationAtPoint

/-- Componentwise conjugation of a tuple `x : Fin k → Ri R`. -/
noncomputable def conjTuple (x : Fin k → Ri R) : Fin k → Ri R := fun i => Ri.conj R (x i)

@[simp] theorem conjTuple_apply (x : Fin k → Ri R) (i : Fin k) :
    conjTuple x i = Ri.conj R (x i) := rfl

theorem conjTuple_involutive : Function.Involutive (conjTuple (R := R) (k := k)) := by
  intro x; funext i; simp [conjTuple, Ri.conj_conj]

@[simp] theorem conjTuple_conjTuple (x : Fin k → Ri R) : conjTuple (conjTuple x) = x :=
  conjTuple_involutive x

/-- `aeval (conjTuple x) P = conj (aeval x P)` for a polynomial `P` with `R`-coefficients. -/
theorem aeval_conjTuple (P : MvPolynomial (Fin k) R) (x : Fin k → Ri R) :
    aeval (conjTuple x) P = Ri.conj R (aeval x P) := by
  have hcomp : (Ri.conj R).comp (aeval x) = aeval (conjTuple x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl
  have := AlgHom.congr_fun hcomp P
  rw [AlgHom.comp_apply] at this
  exact this.symm

/-- The conjugate of a zero is a zero (the members of `𝒫` have `R`-coefficients). -/
theorem conjTuple_mem_zer {Ps : Finset (MvPolynomial (Fin k) R)} {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) : conjTuple x ∈ zerOfFinset (Ri R) Ps := by
  intro p hp
  rw [aeval_conjTuple, hx p hp, map_zero]

theorem conjTuple_mem_toFinset {Ps : Finset (MvPolynomial (Fin k) R)}
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ hfin.toFinset) : conjTuple x ∈ hfin.toFinset :=
  hfin.mem_toFinset.mpr (conjTuple_mem_zer (hfin.mem_toFinset.mp hx))

/-- The multiplicity `μ(x)` of a tuple `x` (zero outside `Zer(𝒫, Cᵏ)`). -/
noncomputable def mult (Ps : Finset (MvPolynomial (Fin k) R)) (x : Fin k → Ri R) : ℕ :=
  if h : x ∈ zerOfFinset (Ri R) Ps then multiplicityOfZero (Ri R) Ps x h else 0

theorem mult_eq_of_mem {Ps : Finset (MvPolynomial (Fin k) R)} {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) :
    mult Ps x = multiplicityOfZero (Ri R) Ps x hx := dif_pos hx

/-- The weight `μ(x)·Q(x)` of a tuple `x`. -/
noncomputable def mvHerWeight (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) : Ri R :=
  (mult Ps x) • MvPolynomial.aeval x Q

/-- The finset of distinct zeros over `C` at which `Q` does not vanish. -/
noncomputable def mvHerRoots (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    Finset (Fin k → Ri R) :=
  hfin.toFinset.filter (fun x => MvPolynomial.aeval x Q ≠ 0)

theorem mem_mvHerRoots_iff {Ps : Finset (MvPolynomial (Fin k) R)}
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R} :
    x ∈ mvHerRoots Ps Q hfin ↔ x ∈ zerOfFinset (Ri R) Ps ∧ MvPolynomial.aeval x Q ≠ 0 := by
  rw [mvHerRoots, Finset.mem_filter, hfin.mem_toFinset]

/-! ### Multiplicity is conjugation invariant (keystone, BPR Route A) -/

/-- **Multiplicity is conjugation invariant.** `μ(conjTuple x) = μ(x)`.

The characteristic polynomial of `L_a` on `Ā` (for a separating element `a`) is the base change
of a polynomial `Pₐ ∈ R[X]` (Remark 4.99); by Theorem 4.97 its roots are exactly the values `a(x)`
with multiplicity `μ(x)`. Since `Pₐ` has `R`-coefficients, conjugation fixes `Pₐ.map alg`, so the
multiplicity of `conj(a(x)) = a(conjTuple x)` equals that of `a(x)`. -/
theorem mult_conjTuple (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (hfin : (zerOfFinset (Ri R) Ps).Finite)
    (x : Fin k → Ri R) :
    mult Ps (conjTuple x) = mult Ps x := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  haveI : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  -- separating element
  obtain ⟨i, _, hsep⟩ := lemma_4_90 (K := R) (Ri R) Ps hfin
  set a : quotPolys Ps := Ideal.Quotient.mk _ (linearForm (K := R) i) with ha
  -- the value function `a(·)` commutes with conjugation
  have haval_conj : ∀ (y : Fin k → Ri R) (hy : y ∈ zerOfFinset (Ri R) Ps)
      (hcy : conjTuple y ∈ zerOfFinset (Ri R) Ps),
      valueAt (Ri R) Ps a (conjTuple y) hcy = Ri.conj R (valueAt (Ri R) Ps a y hy) := by
    intro y hy hcy
    rw [ha, valueAt_mk, valueAt_mk, aeval_conjTuple]
  -- the charpoly of `L_a` over Ā equals the image of `Pa ∈ R[X]`
  set Pa : Polynomial R := LinearMap.charpoly (mulMap Ps a) with hPa
  have hcharImg : LinearMap.charpoly (mulMapExt (Ri R) Ps (inclExt (Ri R) Ps a))
      = Pa.map (algebraMap R (Ri R)) := by
    rw [hPa, ← remark_4_99_charpoly (Ri R) Ps a]
    rfl
  -- by Theorem 4.97, that charpoly factors over the zeros
  have hfactor := theorem_4_97 (C := Ri R) Ps hfin (inclExt (Ri R) Ps a)
  -- so `Pa.map alg` is the product ∏_x (X - a(x))^μ(x)
  set prodPoly : Polynomial (Ri R) :=
    ∏ z : hfin.toFinset,
      (Polynomial.X - Polynomial.C (valueAt (Ri R) Ps a z.1 (hfin.mem_toFinset.mp z.2)))
        ^ multiplicityOfZero (Ri R) Ps z.1 (hfin.mem_toFinset.mp z.2) with hprodPoly
  have hPaeq : Pa.map (algebraMap R (Ri R)) = prodPoly := by
    rw [← hcharImg, hfactor]
    rfl
  -- conjugation fixes `Pa.map alg`
  have hmapconj : (Pa.map (algebraMap R (Ri R))).map (Ri.conj R : Ri R →+* Ri R)
      = Pa.map (algebraMap R (Ri R)) := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp only [RingHom.comp_apply]
    exact Ri.conj_algebraMap_ordered r
  -- conjugation preserves the root multiset of `Pa.map alg`
  have hroots_conj : (Pa.map (algebraMap R (Ri R))).roots.map (Ri.conj R : Ri R →+* Ri R)
      = (Pa.map (algebraMap R (Ri R))).roots := by
    have hsplit : (Pa.map (algebraMap R (Ri R))).Splits := IsAlgClosed.splits _
    have hroots := hsplit.roots_map (Ri.conj R : Ri R →+* Ri R)
    rw [hmapconj] at hroots
    exact hroots.symm
  -- conjugation invariance of root multiplicities of `Pa.map alg`
  have hcount_conj : ∀ v : Ri R,
      Multiset.count (Ri.conj R v) (Pa.map (algebraMap R (Ri R))).roots
        = Multiset.count v (Pa.map (algebraMap R (Ri R))).roots := by
    intro v
    conv_lhs => rw [← hroots_conj]
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    refine congrArg Multiset.card (Multiset.filter_congr fun y _ => ?_)
    constructor
    · intro h; exact Ri.conj_injective R h
    · rintro rfl; rfl
  -- `prodPoly ≠ 0`
  have hprodNe : prodPoly ≠ 0 := by
    rw [hprodPoly]
    exact Finset.prod_ne_zero_iff.mpr fun z _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  -- count of any value in `prodPoly.roots`
  have hcount_prod : ∀ v : Ri R,
      Multiset.count v prodPoly.roots
        = ∑ z : hfin.toFinset,
            multiplicityOfZero (Ri R) Ps z.1 (hfin.mem_toFinset.mp z.2)
              * (if valueAt (Ri R) Ps a z.1 (hfin.mem_toFinset.mp z.2) = v then 1 else 0) := by
    intro v
    have hpne : prodPoly ≠ 0 := hprodNe
    rw [hprodPoly] at hpne ⊢
    rw [Polynomial.roots_prod _ _ hpne, Multiset.count_bind, Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum ?_
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [Polynomial.roots_pow, Multiset.count_nsmul, Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
    congr 1
    by_cases h : valueAt (Ri R) Ps a z.1 (hfin.mem_toFinset.mp z.2) = v
    · rw [if_pos (by rw [eq_comm]; exact h), if_pos h]
    · rw [if_neg (by rw [eq_comm]; exact h), if_neg h]
  -- the count of `a(y)` is exactly `μ(y)` (separation)
  have hcount_aval : ∀ (y : Fin k → Ri R) (hy : y ∈ zerOfFinset (Ri R) Ps),
      Multiset.count (valueAt (Ri R) Ps a y hy) prodPoly.roots = mult Ps y := by
    intro y hy
    rw [hcount_prod, mult_eq_of_mem hy]
    set yT : hfin.toFinset := ⟨y, hfin.mem_toFinset.mpr hy⟩ with hyT
    rw [Finset.sum_eq_single yT]
    · rw [if_pos (by
        show valueAt (Ri R) Ps a y (hfin.mem_toFinset.mp yT.2) = valueAt (Ri R) Ps a y hy
        rfl), mul_one]
    · intro z _ hz
      rw [if_neg ?_, mul_zero]
      intro hval
      apply hz
      apply Subtype.ext
      exact hsep z.1 (hfin.mem_toFinset.mp z.2) y hy hval
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  -- conclude: `μ(conjTuple x) = μ(x)`
  by_cases hx : x ∈ zerOfFinset (Ri R) Ps
  · have hcx : conjTuple x ∈ zerOfFinset (Ri R) Ps := conjTuple_mem_zer hx
    have key : Multiset.count (valueAt (Ri R) Ps a (conjTuple x) hcx) prodPoly.roots
        = Multiset.count (valueAt (Ri R) Ps a x hx) prodPoly.roots := by
      rw [haval_conj x hx hcx, ← hPaeq, hcount_conj, hPaeq]
    rw [← hcount_aval (conjTuple x) hcx, ← hcount_aval x hx, key]
  · have hcx : conjTuple x ∉ zerOfFinset (Ri R) Ps := by
      intro h
      exact hx (by have := conjTuple_mem_zer h; rwa [conjTuple_involutive x] at this)
    rw [mult, mult, dif_neg hx, dif_neg hcx]

theorem mvHerWeight_conjTuple (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (hfin : (zerOfFinset (Ri R) Ps).Finite)
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) :
    mvHerWeight Ps Q (conjTuple x) = Ri.conj R (mvHerWeight Ps Q x) := by
  rw [mvHerWeight, mvHerWeight, mult_conjTuple Ps hfin, aeval_conjTuple, map_nsmul]

/-- The weight `μ(x)·Q(x)` is nonzero for `x ∈ mvHerRoots`. -/
theorem mvHerWeight_ne_zero {Ps : Finset (MvPolynomial (Fin k) R)}
    [Module.Finite R (quotPolys Ps)]
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R}
    (hx : x ∈ mvHerRoots Ps Q hfin) : mvHerWeight Ps Q x ≠ 0 := by
  haveI : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  rw [mem_mvHerRoots_iff] at hx
  rw [mvHerWeight, nsmul_eq_mul]
  refine mul_ne_zero ?_ hx.2
  have hpos : 0 < mult Ps x := by
    rw [mult_eq_of_mem hx.1]
    haveI : Module.Finite (Ri R) (quotPolysExt (Ri R) Ps) := moduleFinite_quotPolysExt (Ri R) Ps
    haveI : Nontrivial (localizationAtPoint (Ri R) Ps x hx.1) :=
      (isLocalRing_localizationAtPoint (Ri R) Ps x hx.1).toNontrivial
    exact Module.finrank_pos
  exact Nat.cast_ne_zero.mpr hpos.ne'

/-! ### Real/imaginary arithmetic in `Ri R` (helpers; mirror §4.3) -/

theorem algebraMap_reL_of_conj_fixed {z : Ri R} (hz : Ri.conj R z = z) :
    algebraMap R (Ri R) (Ri.reL z) = z := by
  obtain ⟨a, hra⟩ := Ri.conj_fixed_mem_range_ordered z hz
  have hreL : Ri.reL z = a := by
    rw [← hra, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      Ri.reL_of]
  rw [hreL, hra]

theorem reL_mul (c d : Ri R) :
    Ri.reL (c * d) = Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.reL_lin]

theorem imL_mul (c d : Ri R) :
    Ri.imL (c * d) = Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.imL_lin]

theorem conj_add_self (c : Ri R) :
    c + Ri.conj R c = algebraMap R (Ri R) (2 * Ri.reL c) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr, two_mul, map_add]
  ring

theorem reL_sq (c : Ri R) : Ri.reL (c ^ 2) = Ri.reL c ^ 2 - Ri.imL c ^ 2 := by
  rw [show (c : Ri R) ^ 2 = c * c from pow_two c, reL_mul]; ring

theorem reL_conj (c : Ri R) : Ri.reL (Ri.conj R c) = Ri.reL c := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists c
  have hreL : Ri.reL c = a := by
    rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl, Ri.reL_lin]
  rw [hreL, hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.reL_lin a (-b)]

theorem imL_conj (x : Ri R) : Ri.imL (Ri.conj R x) = - Ri.imL x := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  rw [hab, Ri.conj_repr]
  rw [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
    show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  rw [Ri.imL_lin a b, Ri.imL_lin a (-b)]

theorem imL_ne_zero_of_not_real {x : Ri R} (hx : Ri.conj R x ≠ x) : Ri.imL x ≠ 0 := by
  intro h
  apply hx
  obtain ⟨a, b, hab⟩ := Ri.repr_exists x
  have hb : b = 0 := by
    have := hab ▸ h
    rwa [show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
      show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl,
      Ri.imL_lin a b] at this
  rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]

/-! ### A separating element and the conjugate-pair selector -/

/-- A chosen separating polynomial for `𝒫` over `C = Ri R` (Lemma 4.90). -/
noncomputable def sepElt (Ps : Finset (MvPolynomial (Fin k) R))
    [CharZero R] (hfin : (zerOfFinset (Ri R) Ps).Finite) : MvPolynomial (Fin k) R :=
  linearForm (K := R) (lemma_4_90 (K := R) (Ri R) Ps hfin).choose

/-- The chosen separating element separates the zeros: distinct zeros get distinct values. -/
theorem sepElt_separating (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x y : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hy : y ∈ zerOfFinset (Ri R) Ps)
    (h : MvPolynomial.aeval x (sepElt Ps hfin) = MvPolynomial.aeval y (sepElt Ps hfin)) :
    x = y := by
  have hsep := (lemma_4_90 (K := R) (Ri R) Ps hfin).choose_spec.2
  have := hsep x hx y hy
  rw [valueAt_mk, valueAt_mk] at this
  exact this h

/-- The conjugate-pair selector: `posRep x` holds when the separating value `a(x)` has positive
imaginary part. For a non-real zero `x` it holds for exactly one of `x`, `conjTuple x`. -/
noncomputable def posRep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) (x : Fin k → Ri R) : Prop :=
  0 < Ri.imL (MvPolynomial.aeval x (sepElt Ps hfin))

/-- For a non-real zero `x`, the separating value `a(x)` is non-real. -/
theorem imL_sepVal_ne_zero (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hxr : conjTuple x ≠ x) :
    Ri.imL (MvPolynomial.aeval x (sepElt Ps hfin)) ≠ 0 := by
  apply imL_ne_zero_of_not_real
  intro hfix
  apply hxr
  -- `a(x)` conj-fixed ⟹ `a(conjTuple x) = a(x)` ⟹ `conjTuple x = x` by separation
  have hcx : conjTuple x ∈ zerOfFinset (Ri R) Ps := conjTuple_mem_zer hx
  have hval : MvPolynomial.aeval (conjTuple x) (sepElt Ps hfin)
      = MvPolynomial.aeval x (sepElt Ps hfin) := by
    rw [aeval_conjTuple, hfix]
  exact sepElt_separating Ps hfin hcx hx hval

/-- The selector splits a non-real conjugate pair: `posRep x ↔ ¬ posRep (conjTuple x)`. -/
theorem posRep_conjTuple_iff (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hxr : conjTuple x ≠ x) :
    posRep Ps hfin x ↔ ¬ posRep Ps hfin (conjTuple x) := by
  unfold posRep
  rw [aeval_conjTuple, imL_conj]
  have hne := imL_sepVal_ne_zero Ps hfin hx hxr
  constructor
  · intro h; rw [not_lt]; exact (neg_nonpos.mpr h.le)
  · intro h
    rw [not_lt, neg_le, neg_zero] at h
    exact lt_of_le_of_ne h (Ne.symm hne)

/-! ### Basis of `A` and polynomial representatives -/

/-- The rank `N = dim_R A`. -/
noncomputable def mvN (Ps : Finset (MvPolynomial (Fin k) R)) : ℕ :=
  Module.finrank R (quotPolys Ps)

/-- A chosen `R`-basis of `A = quotPolys Ps`, indexed by `Fin N`. -/
noncomputable def mvBasis (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] : Module.Basis (Fin (mvN Ps)) R (quotPolys Ps) :=
  Module.finBasis R (quotPolys Ps)

/-- Polynomial representatives `ω j` of the basis elements: `mk (ω j) = B j`. -/
noncomputable def mvRep (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (j : Fin (mvN Ps)) : MvPolynomial (Fin k) R :=
  (Ideal.Quotient.mk_surjective (mvBasis Ps j)).choose

theorem mvRep_spec (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (j : Fin (mvN Ps)) :
    Ideal.Quotient.mk (idealOfPolys Ps) (mvRep Ps j) = mvBasis Ps j :=
  (Ideal.Quotient.mk_surjective (mvBasis Ps j)).choose_spec

/-- `valueAt (B j) x = aeval x (ω j)`. -/
theorem valueAt_mvBasis (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] {x : Fin k → Ri R} (hx : x ∈ zerOfFinset (Ri R) Ps)
    (j : Fin (mvN Ps)) :
    valueAt (Ri R) Ps (mvBasis Ps j) x hx = MvPolynomial.aeval x (mvRep Ps j) := by
  rw [← mvRep_spec Ps j, valueAt_mk]

/-- `valueAt` of any `g ∈ A` expands over the basis: `g(x) = ∑_j (B.repr g j) · ω_j(x)`. -/
theorem valueAt_eq_sum (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] {x : Fin k → Ri R} (hx : x ∈ zerOfFinset (Ri R) Ps)
    (g : quotPolys Ps) :
    valueAt (Ri R) Ps g x hx
      = ∑ j, algebraMap R (Ri R) ((mvBasis Ps).repr g j) * MvPolynomial.aeval x (mvRep Ps j) := by
  set φ : quotPolys Ps →+* Ri R := (evalBar (Ri R) Ps x hx).comp (inclExt (Ri R) Ps) with hφ
  have hval : ∀ g', valueAt (Ri R) Ps g' x hx = φ g' := fun g' => rfl
  -- `φ` sends `algebraMap R c` to `algebraMap R (Ri R) c`
  have hφalg : ∀ c : R, φ (algebraMap R (quotPolys Ps) c) = algebraMap R (Ri R) c := by
    intro c
    rw [← hval, show algebraMap R (quotPolys Ps) c = Ideal.Quotient.mk _ (MvPolynomial.C c) from rfl,
      valueAt_mk, MvPolynomial.aeval_C]
  -- `φ` pushes through `R`-scalars
  have hφsmul : ∀ (c : R) (a : quotPolys Ps), φ (c • a) = algebraMap R (Ri R) c * φ a := by
    intro c a
    rw [Algebra.smul_def (R := R) (A := quotPolys Ps), map_mul, hφalg]
  rw [hval]
  conv_lhs => rw [← (mvBasis Ps).sum_repr g]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hφsmul, ← hval (mvBasis Ps j), valueAt_mvBasis Ps hx j]

/-! ### Hermite coefficients and form vectors -/

/-- A chosen square root in `C = Ri R` of the weight `μ(x)·Q(x)`. -/
noncomputable def mvHerSqrt (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) : Ri R :=
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  (IsAlgClosed.exists_pow_nat_eq (mvHerWeight Ps Q x) (n := 2) (by norm_num)).choose

theorem mvHerSqrt_sq (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (x : Fin k → Ri R) :
    mvHerSqrt Ps Q x ^ 2 = mvHerWeight Ps Q x := by
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact (IsAlgClosed.exists_pow_nat_eq (mvHerWeight Ps Q x) (n := 2) (by norm_num)).choose_spec

/-- The coefficient attached to a zero `x`:
* real `x` (`conjTuple x = x`): the real weight `reL (μ(x)·Q(x))`;
* non-real `x` with `posRep`: `+2`; otherwise `-2`. -/
noncomputable def mvHerCoeff (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite)
    (x : Fin k → Ri R) : R :=
  if conjTuple x = x then Ri.reL (mvHerWeight Ps Q x)
  else if posRep Ps hfin x then 2 else -2

/-- The coefficient vector (in `R^N`) of the linear form attached to a zero `x`, mirroring §4.3
`herFormVec` with `x^k` replaced by `ω_j(x)`. -/
noncomputable def mvHerFormVec (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite)
    [Module.Finite R (quotPolys Ps)] (x : Fin k → Ri R) : Fin (mvN Ps) → R :=
  if conjTuple x = x then fun j => Ri.reL (MvPolynomial.aeval x (mvRep Ps j))
  else if posRep Ps hfin x then
    (fun j => Ri.reL (mvHerSqrt Ps Q x) * Ri.reL (MvPolynomial.aeval x (mvRep Ps j))
                - Ri.imL (mvHerSqrt Ps Q x) * Ri.imL (MvPolynomial.aeval x (mvRep Ps j)))
  else
    (fun j => Ri.reL (mvHerSqrt Ps Q (conjTuple x)) * Ri.imL (MvPolynomial.aeval (conjTuple x) (mvRep Ps j))
                + Ri.imL (mvHerSqrt Ps Q (conjTuple x)) * Ri.reL (MvPolynomial.aeval (conjTuple x) (mvRep Ps j)))

/-- The linear form `f ↦ v ⬝ᵥ f` with coefficient vector `v`. -/
def mvHerDotLM {N : ℕ} (v : Fin N → R) : (Fin N → R) →ₗ[R] R where
  toFun f := v ⬝ᵥ f
  map_add' := dotProduct_add v
  map_smul' c f := by simp [dotProduct_smul]

theorem mvHerDotLM_apply {N : ℕ} (v f : Fin N → R) : mvHerDotLM v f = v ⬝ᵥ f := rfl

/-! ### Conjugation facts on `mvHerRoots` -/

/-- Conjugation maps `mvHerRoots` to itself. -/
theorem conjTuple_mem_mvHerRoots {Ps : Finset (MvPolynomial (Fin k) R)}
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R}
    (hx : x ∈ mvHerRoots Ps Q hfin) : conjTuple x ∈ mvHerRoots Ps Q hfin := by
  rw [mem_mvHerRoots_iff] at hx ⊢
  refine ⟨conjTuple_mem_zer hx.1, ?_⟩
  rw [aeval_conjTuple]
  intro h
  exact hx.2 (by have := congrArg (Ri.conj R) h; rwa [Ri.conj_conj, map_zero] at this)

/-- For a non-real zero `x`, `mvHerCoeff` at `conjTuple x` is the negation of `mvHerCoeff` at `x`. -/
theorem mvHerCoeff_conjTuple_of_not_real [CharZero R] (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite) {x : Fin k → Ri R}
    (hx : x ∈ zerOfFinset (Ri R) Ps) (hxr : conjTuple x ≠ x) :
    mvHerCoeff Ps Q hfin (conjTuple x) = - mvHerCoeff Ps Q hfin x := by
  have hxr' : conjTuple (conjTuple x) ≠ conjTuple x := by
    rw [conjTuple_involutive]; exact fun h => hxr h.symm
  rw [mvHerCoeff, mvHerCoeff, if_neg hxr, if_neg hxr']
  by_cases hpos : posRep Ps hfin x
  · rw [if_pos hpos, if_neg ((posRep_conjTuple_iff Ps hfin hx hxr).mp hpos)]
  · rw [if_neg hpos]
    have : posRep Ps hfin (conjTuple x) := by
      by_contra hc
      exact hpos ((posRep_conjTuple_iff Ps hfin hx hxr).mpr hc)
    rw [if_pos this]; norm_num

/-- `mvHerCoeff` is nonzero on `mvHerRoots`. -/
theorem mvHerCoeff_ne_zero {Ps : Finset (MvPolynomial (Fin k) R)}
    [Module.Finite R (quotPolys Ps)]
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R}
    (hx : x ∈ mvHerRoots Ps Q hfin) : mvHerCoeff Ps Q hfin x ≠ 0 := by
  rw [mvHerCoeff]
  split_ifs with hreal hpos
  · intro hzero
    have hfix : Ri.conj R (mvHerWeight Ps Q x) = mvHerWeight Ps Q x := by
      rw [← mvHerWeight_conjTuple Ps hfin, hreal]
    have hw0 : mvHerWeight Ps Q x = 0 := by
      rw [← algebraMap_reL_of_conj_fixed hfix, hzero, map_zero]
    exact mvHerWeight_ne_zero hx hw0
  · norm_num
  · norm_num

/-! ### Independence via a separating element -/

/-- The number of distinct zeros in `mvHerRoots` is at most `#zeros = n`. -/
theorem card_mvHerRoots_le (Ps : Finset (MvPolynomial (Fin k) R))
    (Q : MvPolynomial (Fin k) R) (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    (mvHerRoots Ps Q hfin).card ≤ hfin.toFinset.card := by
  rw [mvHerRoots]
  exact Finset.card_filter_le _ _

/-- **Independence of the evaluation vectors.** The vectors `(j ↦ ω_j(x))` for the distinct zeros
`x ∈ mvHerRoots` are `Ri R`-linearly independent. (Separation makes the values `a(x)` distinct, so
a Vandermonde argument in `a(x)` forces all coefficients to vanish.) -/
theorem mvEval_indep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    LinearIndependent (Ri R)
      (fun j : Fin (mvHerRoots Ps Q hfin).card =>
        (fun l : Fin (mvN Ps) =>
          MvPolynomial.aeval ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R)
            (mvRep Ps l))) := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  haveI : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  set r := (mvHerRoots Ps Q hfin).card with hr
  set xs : Fin r → (Fin k → Ri R) :=
    fun j => ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R) with hxs
  -- each `xs j` is a zero
  have hxmem : ∀ j, xs j ∈ zerOfFinset (Ri R) Ps := fun j =>
    (mem_mvHerRoots_iff.mp ((mvHerRoots Ps Q hfin).equivFin.symm j).2).1
  -- separating values
  set av : Fin r → Ri R := fun j => MvPolynomial.aeval (xs j) (sepElt Ps hfin) with hav
  have hav_inj : Function.Injective av := by
    intro a b hab
    have := sepElt_separating Ps hfin (hxmem a) (hxmem b) hab
    exact (mvHerRoots Ps Q hfin).equivFin.symm.injective (Subtype.ext this)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- `hc` : for all l, ∑ j, c j • (ω_l (xs j)) = 0
  have hcl : ∀ l : Fin (mvN Ps), ∑ j, c j * MvPolynomial.aeval (xs j) (mvRep Ps l) = 0 := by
    intro l
    have := congrFun hc l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  -- for any `g ∈ A`, ∑ j, c j • valueAt(g, xs j) = 0
  have hg : ∀ g : quotPolys Ps,
      ∑ j, c j * valueAt (Ri R) Ps g (xs j) (hxmem j) = 0 := by
    intro g
    have hexp : ∀ j, valueAt (Ri R) Ps g (xs j) (hxmem j)
        = ∑ l, algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * MvPolynomial.aeval (xs j) (mvRep Ps l) :=
      fun j => valueAt_eq_sum Ps (hxmem j) g
    calc ∑ j, c j * valueAt (Ri R) Ps g (xs j) (hxmem j)
        = ∑ j, ∑ l, c j * (algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * MvPolynomial.aeval (xs j) (mvRep Ps l)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hexp j, Finset.mul_sum]
      _ = ∑ l, algebraMap R (Ri R) ((mvBasis Ps).repr g l)
            * ∑ j, c j * MvPolynomial.aeval (xs j) (mvRep Ps l) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [hcl l, mul_zero]
  -- apply with `g = a^i`
  set a : quotPolys Ps := Ideal.Quotient.mk _ (sepElt Ps hfin) with ha
  have hpow : ∀ (i : Fin r) (j : Fin r),
      valueAt (Ri R) Ps (a ^ (i : ℕ)) (xs j) (hxmem j) = av j ^ (i : ℕ) := by
    intro i j
    rw [ha, ← map_pow, valueAt_mk, hav, ← map_pow]
  have hvand : ∀ i : Fin r, ∑ j, c j * av j ^ (i : ℕ) = 0 := by
    intro i
    have := hg (a ^ (i : ℕ))
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow i j]
  exact congrFun (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hav_inj hvand)

/-- The `algebraMap`-images of the Hermite form vectors are `Ri R`-linearly independent. -/
theorem mvHerFormVec_image_C_indep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    LinearIndependent (Ri R)
      (fun j : Fin (mvHerRoots Ps Q hfin).card =>
        (fun l : Fin (mvN Ps) =>
          algebraMap R (Ri R)
            (mvHerFormVec Ps Q hfin
              ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R) l))) := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  haveI : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  set ι := algebraMap R (Ri R) with hι
  set eqv := (mvHerRoots Ps Q hfin).equivFin with heqv
  set p := mvN Ps with hp
  -- `ev x l = ω_l(x)`
  set ev : (Fin k → Ri R) → Fin p → Ri R := fun x l => MvPolynomial.aeval x (mvRep Ps l) with hev
  -- `ev` commutes with conjugation
  have hev_conj : ∀ (x : Fin k → Ri R) (l : Fin p), ev (conjTuple x) l = Ri.conj R (ev x l) := by
    intro x l; rw [hev]; exact aeval_conjTuple _ _
  set F : (Fin k → Ri R) → Fin p → Ri R := fun y l => ι (mvHerFormVec Ps Q hfin y l) with hF
  -- helpers (mirror §4.3)
  have hine : Ri.i R ≠ 0 := by
    intro h; have := Ri.i_sq R; rw [h] at this; simp at this
  have h2ne : (2 : Ri R) ≠ 0 := by
    rw [show (2 : Ri R) = ι 2 by rw [hι, map_ofNat], hι, ← map_zero (algebraMap R (Ri R))]
    intro h
    exact (two_ne_zero : (2 : R) ≠ 0) ((algebraMap R (Ri R)).injective h)
  have h2reL : ∀ c : Ri R, ι (2 * Ri.reL c) = c + Ri.conj R c := fun c => (conj_add_self c).symm
  have himL_diff : ∀ c : Ri R, c - Ri.conj R c = 2 * (ι (Ri.imL c) * Ri.i R) := by
    intro c
    obtain ⟨a, b, hab⟩ := Ri.repr_exists c
    have hb : Ri.imL c = b := by
      rw [hab, show algebraMap R (Ri R) a = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a from rfl,
        show algebraMap R (Ri R) b = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b from rfl, Ri.imL_lin]
    rw [hb, hab, hι, Ri.conj_repr]
    ring
  have hisq : Ri.i R * Ri.i R = -1 := by have := Ri.i_sq R; rwa [pow_two] at this
  have h2imL : ∀ c : Ri R, 2 * ι (Ri.imL c) = Ri.i R * (Ri.conj R c - c) := by
    intro c
    have h := himL_diff c
    have : Ri.i R * (Ri.conj R c - c) = Ri.i R * (- (2 * (ι (Ri.imL c) * Ri.i R))) := by
      rw [← h]; ring
    rw [this, show Ri.i R * (- (2 * (ι (Ri.imL c) * Ri.i R)))
          = -2 * ι (Ri.imL c) * (Ri.i R * Ri.i R) by ring, hisq]
    ring
  set w : (Fin k → Ri R) → Ri R := fun x => mvHerSqrt Ps Q x with hw
  have hwx : ∀ y, w y = mvHerSqrt Ps Q y := fun y => rfl
  set cF : (Fin k → Ri R) → Ri R := fun x =>
    if conjTuple x = x then 2
    else if posRep Ps hfin x then w x else Ri.i R * Ri.conj R (w (conjTuple x)) with hcF
  set eF : (Fin k → Ri R) → Ri R := fun x =>
    if conjTuple x = x then 0
    else if posRep Ps hfin x then Ri.conj R (w x) else - Ri.i R * w (conjTuple x) with heF
  -- key per-component identity: `2 F x l = cF x · ω_l(x) + eF x · ω_l(conj x)`
  have h2F : ∀ x ∈ mvHerRoots Ps Q hfin, ∀ l : Fin p,
      2 * F x l = cF x * ev x l + eF x * ev (conjTuple x) l := by
    intro x hxmem l
    have hxz : x ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hxmem).1
    rw [hF, hcF, heF]
    dsimp only
    by_cases hxr : conjTuple x = x
    · rw [if_pos hxr, if_pos hxr]
      have hpowfix : Ri.conj R (ev x l) = ev x l := by rw [← hev_conj, hxr]
      have : ι (Ri.reL (ev x l)) = ev x l := by
        rw [hι]; exact algebraMap_reL_of_conj_fixed hpowfix
      rw [mvHerFormVec, if_pos hxr]
      show 2 * ι (Ri.reL (ev x l)) = 2 * ev x l + 0 * ev (conjTuple x) l
      rw [this]
      ring
    · rw [if_neg hxr, if_neg hxr]
      by_cases hpos : posRep Ps hfin x
      · rw [if_pos hpos, if_pos hpos]
        rw [mvHerFormVec, if_neg hxr, if_pos hpos]
        rw [show Ri.reL (w x) * Ri.reL (ev x l) - Ri.imL (w x) * Ri.imL (ev x l)
              = Ri.reL (w x * ev x l) from (reL_mul _ _).symm,
          show (2 : Ri R) * ι (Ri.reL (w x * ev x l))
              = ι (2 * Ri.reL (w x * ev x l)) by rw [← map_ofNat ι 2, ← map_mul],
          h2reL, map_mul]
        rw [hev_conj]
      · rw [if_neg hpos, if_neg hpos]
        rw [mvHerFormVec, if_neg hxr, if_neg hpos]
        rw [show Ri.reL (w (conjTuple x)) * Ri.imL (ev (conjTuple x) l)
                + Ri.imL (w (conjTuple x)) * Ri.reL (ev (conjTuple x) l)
              = Ri.imL (w (conjTuple x) * ev (conjTuple x) l) from (imL_mul _ _).symm,
          h2imL, map_mul]
        rw [hev_conj, Ri.conj_conj]
        ring
  -- `w` is nonzero on `mvHerRoots`
  have hw_ne : ∀ x ∈ mvHerRoots Ps Q hfin, w x ≠ 0 := by
    intro x hxmem hwx0
    have : mvHerWeight Ps Q x = 0 := by
      have := mvHerSqrt_sq Ps Q x
      rw [← hwx x, hwx0] at this
      simpa using this.symm
    exact mvHerWeight_ne_zero hxmem this
  -- recovery values of `cF`, `eF`
  have hcF_real : ∀ x : Fin k → Ri R, conjTuple x = x → cF x = 2 := fun x h => by rw [hcF]; simp [h]
  have heF_real : ∀ x : Fin k → Ri R, conjTuple x = x → eF x = 0 := fun x h => by rw [heF]; simp [h]
  have hcF_pos : ∀ x : Fin k → Ri R, ¬ conjTuple x = x → posRep Ps hfin x → cF x = w x :=
    fun x h1 h2 => by rw [hcF]; simp [h1, h2]
  have heF_pos : ∀ x : Fin k → Ri R, ¬ conjTuple x = x → posRep Ps hfin x →
      eF x = Ri.conj R (w x) := fun x h1 h2 => by rw [heF]; simp [h1, h2]
  have hcF_neg : ∀ x : Fin k → Ri R, ¬ conjTuple x = x → ¬ posRep Ps hfin x →
      cF x = Ri.i R * Ri.conj R (w (conjTuple x)) := fun x h1 h2 => by rw [hcF]; simp [h1, h2]
  have heF_neg : ∀ x : Fin k → Ri R, ¬ conjTuple x = x → ¬ posRep Ps hfin x →
      eF x = - Ri.i R * w (conjTuple x) := fun x h1 h2 => by rw [heF]; simp [h1, h2]
  -- main: finite criterion
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set G : (Fin k → Ri R) → Ri R :=
    fun y => if h : y ∈ mvHerRoots Ps Q hfin then g (eqv ⟨y, h⟩) else 0 with hG
  have hGy : ∀ (y : mvHerRoots Ps Q hfin), G (y : Fin k → Ri R) = g (eqv y) := by
    intro y; rw [hG]; simp only [y.2, dif_pos]
  have hgl : ∀ l : Fin p, ∑ y ∈ mvHerRoots Ps Q hfin, G y * F y l = 0 := by
    intro l
    have hgl0 := congrArg (fun v : Fin p → Ri R => v l) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgl0
    rw [← hgl0]
    rw [← Finset.sum_coe_sort (mvHerRoots Ps Q hfin) (fun y => G y * F y l)]
    rw [← Equiv.sum_comp eqv.symm
      (fun y : mvHerRoots Ps Q hfin => G (y : Fin k → Ri R) * F (y : Fin k → Ri R) l)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((eqv.symm j : mvHerRoots Ps Q hfin) : Fin k → Ri R) = (eqv.symm j : Fin k → Ri R) from rfl,
      hGy]
    rw [Equiv.apply_symm_apply, mul_comm]
  set D : (Fin k → Ri R) → Ri R :=
    fun y => G y * cF y + G (conjTuple y) * eF (conjTuple y) with hD
  have hDl : ∀ l : Fin p, ∑ y ∈ mvHerRoots Ps Q hfin, D y * ev y l = 0 := by
    intro l
    have h2 : (2 : Ri R) * ∑ y ∈ mvHerRoots Ps Q hfin, G y * F y l = 0 := by rw [hgl l, mul_zero]
    rw [Finset.mul_sum] at h2
    have hexp : ∑ y ∈ mvHerRoots Ps Q hfin, 2 * (G y * F y l)
        = ∑ y ∈ mvHerRoots Ps Q hfin,
            (G y * cF y * ev y l + G y * eF y * ev (conjTuple y) l) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [show 2 * (G y * F y l) = G y * (2 * F y l) by ring, h2F y hy l]
      ring
    rw [hexp, Finset.sum_add_distrib] at h2
    have hreindex : ∑ y ∈ mvHerRoots Ps Q hfin, G y * eF y * ev (conjTuple y) l
        = ∑ y ∈ mvHerRoots Ps Q hfin, G (conjTuple y) * eF (conjTuple y) * ev y l := by
      refine Finset.sum_nbij' (fun y => conjTuple y) (fun y => conjTuple y) ?_ ?_ ?_ ?_ ?_
      · intro y hy; exact conjTuple_mem_mvHerRoots hy
      · intro y hy; exact conjTuple_mem_mvHerRoots hy
      · intro y _; rw [conjTuple_involutive]
      · intro y _; rw [conjTuple_involutive]
      · intro y _; rw [conjTuple_involutive]
    rw [hreindex] at h2
    rw [← Finset.sum_add_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hD]; ring
  -- Vandermonde (separating element): `D y = 0` for all `y ∈ mvHerRoots`
  have hD0 : ∀ y ∈ mvHerRoots Ps Q hfin, D y = 0 := by
    have hvand := mvEval_indep Ps Q hfin
    rw [Fintype.linearIndependent_iff] at hvand
    have hvand0 := hvand (fun j => D ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R)) ?_
    · intro y hy
      have := hvand0 (eqv ⟨y, hy⟩)
      rwa [show ((mvHerRoots Ps Q hfin).equivFin.symm (eqv ⟨y, hy⟩) : Fin k → Ri R)
          = (y : Fin k → Ri R) by rw [heqv, Equiv.symm_apply_apply]] at this
    · funext l
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply]
      rw [← hDl l]
      rw [← Finset.sum_coe_sort (mvHerRoots Ps Q hfin) (fun y => D y * ev y l)]
      rw [← Equiv.sum_comp (mvHerRoots Ps Q hfin).equivFin.symm
            (fun y : mvHerRoots Ps Q hfin => D (y : Fin k → Ri R) * ev (y : Fin k → Ri R) l)]
  -- recovery: `D = 0` forces `g = 0`
  intro j
  suffices hGmem : ∀ y ∈ mvHerRoots Ps Q hfin, G y = 0 by
    have := hGmem (eqv.symm j : Fin k → Ri R) (eqv.symm j).2
    rwa [show (eqv.symm j : Fin k → Ri R) = ((eqv.symm j : mvHerRoots Ps Q hfin) : Fin k → Ri R) from rfl,
      hGy, Equiv.apply_symm_apply] at this
  have hGpair : ∀ z ∈ mvHerRoots Ps Q hfin, ¬ conjTuple z = z → posRep Ps hfin z →
      G z = 0 ∧ G (conjTuple z) = 0 := by
    intro z hz hzr hzpos
    have hzz : z ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hz).1
    have hcjmem : conjTuple z ∈ mvHerRoots Ps Q hfin := conjTuple_mem_mvHerRoots hz
    have hcjr : ¬ conjTuple (conjTuple z) = conjTuple z := by
      rw [conjTuple_involutive]; exact fun h => hzr h.symm
    have hcjneg : ¬ posRep Ps hfin (conjTuple z) :=
      fun h => ((posRep_conjTuple_iff Ps hfin hzz hzr).mp hzpos) h
    have hwz : w z ≠ 0 := hw_ne z hz
    have hwcz : Ri.conj R (w z) ≠ 0 := fun h => hwz (by
      have := congrArg (Ri.conj R) h; rwa [Ri.conj_conj, map_zero] at this)
    have hDz : w z * (G z - Ri.i R * G (conjTuple z)) = 0 := by
      have hh := hD0 z hz
      simp only [hD, hcF_pos z hzr hzpos, heF_neg (conjTuple z) hcjr hcjneg, conjTuple_conjTuple] at hh
      rw [← hh]; ring
    have hDcz : Ri.conj R (w z) * (G z + Ri.i R * G (conjTuple z)) = 0 := by
      have hh := hD0 (conjTuple z) hcjmem
      simp only [hD, hcF_neg (conjTuple z) hcjr hcjneg, heF_pos z hzr hzpos, conjTuple_conjTuple] at hh
      rw [← hh]; ring
    have e1 : G z - Ri.i R * G (conjTuple z) = 0 :=
      (mul_eq_zero.mp hDz).resolve_left hwz
    have e2 : G z + Ri.i R * G (conjTuple z) = 0 :=
      (mul_eq_zero.mp hDcz).resolve_left hwcz
    have h2gz : (2 : Ri R) * G z = 0 := by linear_combination e1 + e2
    have hGz : G z = 0 := (mul_eq_zero.mp h2gz).resolve_left h2ne
    refine ⟨hGz, ?_⟩
    have hiG : Ri.i R * G (conjTuple z) = 0 := by linear_combination hGz - e1
    exact (mul_eq_zero.mp hiG).resolve_left hine
  intro y hy
  by_cases hyr : conjTuple y = y
  · have hh := hD0 y hy
    simp only [hD, hcF_real y hyr, heF_real y hyr, hyr] at hh
    have h2g : (2 : Ri R) * G y = 0 := by rw [← hh]; ring
    exact (mul_eq_zero.mp h2g).resolve_left h2ne
  · by_cases hypos : posRep Ps hfin y
    · exact (hGpair y hy hyr hypos).1
    · have hyz : y ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hy).1
      have hcjmem : conjTuple y ∈ mvHerRoots Ps Q hfin := conjTuple_mem_mvHerRoots hy
      have hcjr : ¬ conjTuple (conjTuple y) = conjTuple y := by
        rw [conjTuple_involutive]; exact fun h => hyr h.symm
      have hcjpos : posRep Ps hfin (conjTuple y) := by
        by_contra hc
        exact hypos ((posRep_conjTuple_iff Ps hfin hyz hyr).mpr hc)
      have := (hGpair (conjTuple y) hcjmem hcjr hcjpos).2
      rwa [conjTuple_involutive] at this

/-- The Hermite form vectors `mvHerFormVec` are `R`-linearly independent. -/
theorem mvHerFormVec_indep (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    LinearIndependent R
      (fun j : Fin (mvHerRoots Ps Q hfin).card =>
        mvHerFormVec Ps Q hfin ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R)) := by
  classical
  let gL : (Fin (mvN Ps) → R) →ₗ[R] (Fin (mvN Ps) → Ri R) :=
    LinearMap.compLeft (Algebra.linearMap R (Ri R)) (Fin (mvN Ps))
  refine LinearIndependent.of_comp gL ?_
  have hC := mvHerFormVec_image_C_indep Ps Q hfin
  have hRimg : LinearIndependent R
      (fun j : Fin (mvHerRoots Ps Q hfin).card =>
        (fun l : Fin (mvN Ps) =>
          algebraMap R (Ri R)
            (mvHerFormVec Ps Q hfin
              ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R) l))) := by
    refine hC.restrict_scalars ?_
    intro a b hab
    apply (algebraMap R (Ri R)).injective
    simpa only [Algebra.smul_def, mul_one] using hab
  convert hRimg using 1

/-! ### The transported quadratic form and its diagonal expression -/

/-- The Hermite form transported to `Fin N → R` via the basis. -/
noncomputable def mvHerQuad (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R) :
    QuadraticForm R (Fin (mvN Ps) → R) :=
  (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q)).basisRepr (mvBasis Ps)

/-- `hermiteQuad Ps Q' g = hermiteBilin Ps Q' g g`. -/
theorem hermiteQuad_eq_bilin (Ps : Finset (MvPolynomial (Fin k) R)) (Q' g : quotPolys Ps) :
    hermiteQuad Ps Q' g = hermiteBilin Ps Q' g g := by
  rw [hermiteQuad, LinearMap.BilinMap.toQuadraticMap_apply]

/-- **The image under `R ↪ C` of the transported form** is the weighted sum of squares over the
zeros (mirror §4.3 `algebraMap_quadraticForm_eq`). -/
theorem algebraMap_mvHerQuad_eq (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) (f : Fin (mvN Ps) → R) :
    algebraMap R (Ri R) (mvHerQuad Ps Q f)
      = ∑ x ∈ mvHerRoots Ps Q hfin,
          mvHerWeight Ps Q x
            * (∑ l, algebraMap R (Ri R) (f l) * MvPolynomial.aeval x (mvRep Ps l)) ^ 2 := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  set v : quotPolys Ps := ∑ l, f l • mvBasis Ps l with hv
  -- `Ψ f = hermiteBilin Ps (mk Q) v v`
  have hΨ : mvHerQuad Ps Q f = hermiteBilin Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q) v v := by
    rw [mvHerQuad, QuadraticMap.basisRepr_apply, ← hv, hermiteQuad_eq_bilin]
  rw [hΨ, hermiteBilin_bridge Ps hfin _ v v]
  -- the sum over `hfin.toFinset` (subtype) reindexed and reduced to `mvHerRoots`
  -- value of `v` at `x`
  have hvalv : ∀ (x : Fin k → Ri R) (hx : x ∈ zerOfFinset (Ri R) Ps),
      valueAt (Ri R) Ps v x hx
        = ∑ l, algebraMap R (Ri R) (f l) * MvPolynomial.aeval x (mvRep Ps l) := by
    intro x hx
    rw [valueAt_eq_sum Ps hx v]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 2
    rw [hv, (mvBasis Ps).repr_sum_self]
  -- value of `mk Q` at `x`
  have hvalQ : ∀ (x : Fin k → Ri R) (hx : x ∈ zerOfFinset (Ri R) Ps),
      valueAt (Ri R) Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q) x hx = MvPolynomial.aeval x Q := by
    intro x hx; rw [valueAt_mk]
  -- abbreviation for the linear combination value
  set lcv : (Fin k → Ri R) → Ri R :=
    fun x => ∑ l, algebraMap R (Ri R) (f l) * MvPolynomial.aeval x (mvRep Ps l) with hlcv
  -- the subtype sums are termwise equal to `mvHerWeight x * lcv x ^ 2`
  have hterm : (∑ x : hfin.toFinset,
        multiplicityOfZero (Ri R) Ps x.1 (hfin.mem_toFinset.mp x.2)
          • (valueAt (Ri R) Ps v x.1 (hfin.mem_toFinset.mp x.2)
              * valueAt (Ri R) Ps v x.1 (hfin.mem_toFinset.mp x.2)
              * valueAt (Ri R) Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q) x.1
                  (hfin.mem_toFinset.mp x.2)))
      = ∑ x : hfin.toFinset, mvHerWeight Ps Q x.1 * lcv x.1 ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hxz : x.1 ∈ zerOfFinset (Ri R) Ps := hfin.mem_toFinset.mp x.2
    rw [hvalv x.1 hxz, hvalQ x.1 hxz, mvHerWeight, mult_eq_of_mem hxz, hlcv,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hterm, Finset.sum_coe_sort hfin.toFinset (fun x => mvHerWeight Ps Q x * lcv x ^ 2)]
  -- drop `Q(x) = 0` terms: those have `mvHerWeight = 0`
  rw [mvHerRoots]
  refine (Finset.sum_filter_of_ne ?_).symm
  intro x _ hne hQ0
  exact hne (by rw [mvHerWeight, hQ0]; simp)

/-- **The diagonalizing identity** for the transported form: `Ψ f` equals the weighted sum of
squares of the linear forms `mvHerFormVec … ⬝ᵥ f` with coefficients `mvHerCoeff`. -/
theorem mvHerApply_eq (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) (f : Fin (mvN Ps) → R) :
    mvHerQuad Ps Q f
      = ∑ x ∈ mvHerRoots Ps Q hfin,
          mvHerCoeff Ps Q hfin x * (mvHerFormVec Ps Q hfin x ⬝ᵥ f) ^ 2 := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  apply (algebraMap R (Ri R)).injective
  rw [algebraMap_mvHerQuad_eq Ps Q hfin f, map_sum]
  set ι := algebraMap R (Ri R) with hι
  set lcv : (Fin k → Ri R) → Ri R :=
    fun x => ∑ l, ι (f l) * MvPolynomial.aeval x (mvRep Ps l) with hlcv
  set A : (Fin k → Ri R) → Ri R := fun x => mvHerWeight Ps Q x * (lcv x) ^ 2 with hA
  set B : (Fin k → Ri R) → Ri R :=
    fun x => ι (mvHerCoeff Ps Q hfin x) * (ι (mvHerFormVec Ps Q hfin x ⬝ᵥ f)) ^ 2 with hB
  have hRHS : ∀ x : Fin k → Ri R,
      ι (mvHerCoeff Ps Q hfin x * (mvHerFormVec Ps Q hfin x ⬝ᵥ f) ^ 2) = B x := by
    intro x; rw [map_mul, map_pow]
  rw [Finset.sum_congr rfl (fun x _ => hRHS x)]
  -- `ι` of a dot product
  have hdot : ∀ vec : Fin (mvN Ps) → R,
      ι (vec ⬝ᵥ f) = ∑ l, ι (vec l) * ι (f l) := by
    intro vec
    rw [dotProduct, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_mul ι (vec l) (f l)
  -- `lcv` commutes with conjugation
  have hlcv_conj : ∀ x : Fin k → Ri R, lcv (conjTuple x) = Ri.conj R (lcv x) := by
    intro x
    simp only [hlcv, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, aeval_conjTuple, Ri.conj_algebraMap_ordered]
  -- `mvHerWeight` commutes with conjugation
  have hweight_conj : ∀ x : Fin k → Ri R,
      mvHerWeight Ps Q (conjTuple x) = Ri.conj R (mvHerWeight Ps Q x) :=
    fun x => mvHerWeight_conjTuple Ps hfin Q x
  have hAconj : ∀ x : Fin k → Ri R, A (conjTuple x) = Ri.conj R (A x) := by
    intro x
    simp only [hA]
    rw [hweight_conj, hlcv_conj, map_mul, map_pow]
  have hreal_A : ∀ x : Fin k → Ri R, ι (2 * Ri.reL (A x)) = A x + A (conjTuple x) := by
    intro x
    rw [hAconj, hι, conj_add_self]
  -- real `x`: `B x = A x`
  have hBreal : ∀ x : Fin k → Ri R, x ∈ mvHerRoots Ps Q hfin → conjTuple x = x → B x = A x := by
    intro x hxmem hxr
    have hwfix : Ri.conj R (mvHerWeight Ps Q x) = mvHerWeight Ps Q x := by
      rw [← hweight_conj, hxr]
    have hcoeff : ι (mvHerCoeff Ps Q hfin x) = mvHerWeight Ps Q x := by
      rw [mvHerCoeff, if_pos hxr, hι]
      exact algebraMap_reL_of_conj_fixed hwfix
    have hform : ι (mvHerFormVec Ps Q hfin x ⬝ᵥ f) = lcv x := by
      rw [hdot, hlcv]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mvHerFormVec, if_pos hxr]
      have hpowfix : Ri.conj R (MvPolynomial.aeval x (mvRep Ps l)) = MvPolynomial.aeval x (mvRep Ps l) := by
        rw [← aeval_conjTuple, hxr]
      have : ι (Ri.reL (MvPolynomial.aeval x (mvRep Ps l))) = MvPolynomial.aeval x (mvRep Ps l) := by
        rw [hι]; exact algebraMap_reL_of_conj_fixed hpowfix
      rw [this]; ring
    rw [hB, hA]
    dsimp only
    rw [hcoeff, hform]
  -- reL/imL of `ι c * z`
  have hreLc : ∀ (c : R) (z : Ri R), Ri.reL (ι c * z) = c * Ri.reL z := by
    intro c z; rw [hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have himLc : ∀ (c : R) (z : Ri R), Ri.imL (ι c * z) = c * Ri.imL z := by
    intro c z; rw [hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  -- reL/imL of `w * lcv x` distribute over the sum
  have hreL_wmul : ∀ (wv : Ri R) (xt : Fin k → Ri R),
      Ri.reL (wv * lcv xt)
        = ∑ l, Ri.reL (wv * MvPolynomial.aeval xt (mvRep Ps l)) * f l := by
    intro wv xt
    rw [hlcv]; dsimp only
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show wv * (ι (f l) * MvPolynomial.aeval xt (mvRep Ps l))
          = ι (f l) * (wv * MvPolynomial.aeval xt (mvRep Ps l)) by ring, hreLc, mul_comm]
  have himL_wmul : ∀ (wv : Ri R) (xt : Fin k → Ri R),
      Ri.imL (wv * lcv xt)
        = ∑ l, Ri.imL (wv * MvPolynomial.aeval xt (mvRep Ps l)) * f l := by
    intro wv xt
    rw [hlcv]; dsimp only
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show wv * (ι (f l) * MvPolynomial.aeval xt (mvRep Ps l))
          = ι (f l) * (wv * MvPolynomial.aeval xt (mvRep Ps l)) by ring, himLc, mul_comm]
  -- non-real `x`: `B x + B (conj x) = ι (2 reL (A x))`
  have hBnonreal : ∀ x : Fin k → Ri R, x ∈ mvHerRoots Ps Q hfin → conjTuple x ≠ x →
      B x + B (conjTuple x) = ι (2 * Ri.reL (A x)) := by
    intro x hxmem hxr
    have hxz : x ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hxmem).1
    set lrx : R := mvHerFormVec Ps Q hfin x ⬝ᵥ f with hlrx
    set lrc : R := mvHerFormVec Ps Q hfin (conjTuple x) ⬝ᵥ f with hlrc
    have hBpair : B x + B (conjTuple x) = ι (mvHerCoeff Ps Q hfin x * (lrx ^ 2 - lrc ^ 2)) := by
      rw [hB]; dsimp only
      rw [mvHerCoeff_conjTuple_of_not_real Ps Q hfin hxz hxr, ← hlrx, ← hlrc]
      simp only [← map_pow, ← map_mul, ← map_add]
      congr 1; ring
    rw [hBpair]
    congr 1
    have hcc : conjTuple (conjTuple x) = x := conjTuple_involutive x
    by_cases hpos : posRep Ps hfin x
    · set w : Ri R := mvHerSqrt Ps Q x with hw
      have hwsq : w ^ 2 = mvHerWeight Ps Q x := mvHerSqrt_sq Ps Q x
      have hcjneg : ¬ posRep Ps hfin (conjTuple x) :=
        (posRep_conjTuple_iff Ps hfin hxz hxr).mp hpos
      have hlrx_pos : lrx = Ri.reL (w * lcv x) := by
        rw [hlrx, dotProduct, hreL_wmul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mvHerFormVec, if_neg hxr, if_pos hpos, reL_mul]
      have hlrc_pos : lrc = Ri.imL (w * lcv x) := by
        rw [hlrc, dotProduct, himL_wmul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mvHerFormVec, if_neg (by rw [hcc]; exact fun h => hxr h.symm), if_neg hcjneg]
        simp only [hcc]
        rw [hw, imL_mul]
      rw [hlrx_pos, hlrc_pos, mvHerCoeff, if_neg hxr, if_pos hpos]
      have hsq : Ri.reL (w * lcv x) ^ 2 - Ri.imL (w * lcv x) ^ 2 = Ri.reL (A x) := by
        rw [← reL_sq, mul_pow, hwsq]
      rw [show Ri.reL (w * lcv x) ^ 2 - Ri.imL (w * lcv x) ^ 2 = Ri.reL (A x) from hsq]
    · set w' : Ri R := mvHerSqrt Ps Q (conjTuple x) with hw'
      have hw'sq : w' ^ 2 = mvHerWeight Ps Q (conjTuple x) := mvHerSqrt_sq Ps Q (conjTuple x)
      have hcjpos : posRep Ps hfin (conjTuple x) := by
        by_contra hc; exact hpos ((posRep_conjTuple_iff Ps hfin hxz hxr).mpr hc)
      have hlrx_neg : lrx = Ri.imL (w' * lcv (conjTuple x)) := by
        rw [hlrx, dotProduct, himL_wmul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mvHerFormVec, if_neg hxr, if_neg hpos, imL_mul, ← hw']
      have hlrc_neg : lrc = Ri.reL (w' * lcv (conjTuple x)) := by
        rw [hlrc, dotProduct, hreL_wmul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mvHerFormVec, if_neg (by rw [hcc]; exact fun h => hxr h.symm), if_pos hcjpos, reL_mul,
          ← hw']
      rw [hlrx_neg, hlrc_neg, mvHerCoeff, if_neg hxr, if_neg hpos]
      have hsq : Ri.reL (w' * lcv (conjTuple x)) ^ 2 - Ri.imL (w' * lcv (conjTuple x)) ^ 2
          = Ri.reL (A x) := by
        rw [← reL_sq, mul_pow, hw'sq,
          show mvHerWeight Ps Q (conjTuple x) * lcv (conjTuple x) ^ 2 = A (conjTuple x) from rfl,
          hAconj, reL_conj]
      linear_combination (2 : R) * hsq
  -- assemble via involution
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_involution (fun x _ => conjTuple x) ?_ ?_ ?_ ?_
  · intro x hx
    show A x - B x + (A (conjTuple x) - B (conjTuple x)) = 0
    by_cases hxr : conjTuple x = x
    · rw [hBreal x hx hxr, hxr, hBreal x hx hxr]; ring
    · have key := hBnonreal x hx hxr
      have hAsum : A x + A (conjTuple x) = ι (2 * Ri.reL (A x)) := (hreal_A x).symm
      linear_combination hAsum - key
  · intro x hx hne hxr
    apply hne
    show A x - B x = 0
    rw [hBreal x hx hxr]; ring
  · intro x hx
    exact conjTuple_mem_mvHerRoots hx
  · intro x _
    exact conjTuple_involutive x

/-- **The Hermite diagonal expression** of the transported form `mvHerQuad Ps Q`. -/
noncomputable def mvHerDiagExpr (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    DiagonalExpression (mvHerQuad Ps Q) where
  r := (mvHerRoots Ps Q hfin).card
  coeff j := mvHerCoeff Ps Q hfin ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R)
  form j := mvHerDotLM (mvHerFormVec Ps Q hfin
    ((mvHerRoots Ps Q hfin).equivFin.symm j : Fin k → Ri R))
  coeff_ne_zero j := mvHerCoeff_ne_zero ((mvHerRoots Ps Q hfin).equivFin.symm j).2
  form_indep := by
    classical
    let D : (Fin (mvN Ps) → R) →ₗ[R] ((Fin (mvN Ps) → R) →ₗ[R] R) :=
      { toFun := fun vec => mvHerDotLM vec
        map_add' := fun vec w => by
          refine LinearMap.ext fun f => ?_
          simp only [mvHerDotLM_apply, LinearMap.add_apply, add_dotProduct]
        map_smul' := fun c vec => by
          refine LinearMap.ext fun f => ?_
          simp only [mvHerDotLM_apply, LinearMap.smul_apply, smul_dotProduct, RingHom.id_apply,
            smul_eq_mul] }
    have hDker : LinearMap.ker D = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro vec hv
      funext l
      have hvl : mvHerDotLM vec (Pi.single l 1) = 0 := by
        have := congrFun (congrArg DFunLike.coe hv) (Pi.single l 1)
        simpa only [D, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] using this
      rw [mvHerDotLM_apply, dotProduct_single, mul_one] at hvl
      simpa using hvl
    exact (mvHerFormVec_indep Ps Q hfin).map' D hDker
  apply_eq := by
    intro f
    rw [mvHerApply_eq Ps Q hfin f]
    rw [← Finset.sum_coe_sort (mvHerRoots Ps Q hfin)
      (fun x => mvHerCoeff Ps Q hfin x * (mvHerFormVec Ps Q hfin x ⬝ᵥ f) ^ 2),
      ← Equiv.sum_comp (mvHerRoots Ps Q hfin).equivFin.symm
        (fun x : mvHerRoots Ps Q hfin =>
          mvHerCoeff Ps Q hfin (x : Fin k → Ri R)
            * (mvHerFormVec Ps Q hfin (x : Fin k → Ri R) ⬝ᵥ f) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mvHerDotLM_apply]

/-- The isometry between `hermiteQuad Ps (mk Q)` and its basis representation `mvHerQuad`. -/
theorem mvHerQuad_equiv (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R) :
    QuadraticMap.Equivalent (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q))
      (mvHerQuad Ps Q) :=
  ⟨QuadraticMap.isometryEquivBasisRepr _ (mvBasis Ps)⟩

/-- Reindexing helper (local copy of §4.3 `card_filter_equivFin`). -/
theorem card_filter_equivFin {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun j : Fin s.card => P (s.equivFin.symm j : α))).card
      = (s.filter P).card := by
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

/-- `posCount` of the Hermite diagonal expression as a filter over `mvHerRoots`. -/
theorem mvHerDiagExpr_posCount (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    (mvHerDiagExpr Ps Q hfin).posCount
      = ((mvHerRoots Ps Q hfin).filter (fun x => 0 < mvHerCoeff Ps Q hfin x)).card := by
  classical
  rw [DiagonalExpression.posCount]
  exact card_filter_equivFin (mvHerRoots Ps Q hfin) (fun x => 0 < mvHerCoeff Ps Q hfin x)

/-- `negCount` of the Hermite diagonal expression as a filter over `mvHerRoots`. -/
theorem mvHerDiagExpr_negCount (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    (mvHerDiagExpr Ps Q hfin).negCount
      = ((mvHerRoots Ps Q hfin).filter (fun x => mvHerCoeff Ps Q hfin x < 0)).card := by
  classical
  rw [DiagonalExpression.negCount]
  exact card_filter_equivFin (mvHerRoots Ps Q hfin) (fun x => mvHerCoeff Ps Q hfin x < 0)

/-- Local copy of §4.3 `card_pos_sub_card_neg_eq_sum_sign`. -/
theorem card_pos_sub_card_neg_eq_sum_sign {α : Type*} (s : Finset α) (c : α → R)
    (hc : ∀ x ∈ s, c x ≠ 0) :
    ((s.filter (fun x => 0 < c x)).card : ℤ) - (s.filter (fun x => c x < 0)).card
      = ∑ x ∈ s, (SignType.sign (c x) : ℤ) := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rcases lt_or_gt_of_ne (hc x hx) with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), if_pos hneg, sign_neg hneg]; simp
  · rw [if_pos hpos, if_neg (not_lt.mpr hpos.le), sign_pos hpos]; simp

/-! ### The signature sum equals the Tarski query -/

/-- A conj-fixed tuple has each coordinate conj-fixed, hence comes from a real point. -/
theorem algebraMap_reL_tuple_of_conj_fixed {x : Fin k → Ri R} (hxr : conjTuple x = x) (i : Fin k) :
    algebraMap R (Ri R) (Ri.reL (x i)) = x i := by
  apply algebraMap_reL_of_conj_fixed
  have := congrFun hxr i
  rwa [conjTuple_apply] at this

omit [IsRealClosed R] in
/-- `aeval (algebraMap ∘ y) P = algebraMap (aeval y P)` for `y : Fin k → R`. -/
theorem aeval_algebraMap_tuple (P : MvPolynomial (Fin k) R) (y : Fin k → R) :
    MvPolynomial.aeval (fun i => algebraMap R (Ri R) (y i)) P
      = algebraMap R (Ri R) (MvPolynomial.aeval y P) := by
  have hcomp : (IsScalarTower.toAlgHom R R (Ri R)).comp (MvPolynomial.aeval y)
      = MvPolynomial.aeval (fun i => algebraMap R (Ri R) (y i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      IsScalarTower.toAlgHom_apply]
  have := AlgHom.congr_fun hcomp P
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at this
  exact this.symm

/-- A real zero `y` over `R` gives a conj-fixed zero `algebraMap ∘ y` over `C`. -/
theorem algebraMap_tuple_mem_zer {Ps : Finset (MvPolynomial (Fin k) R)} {y : Fin k → R}
    (hy : y ∈ zerOfFinset R Ps) :
    (fun i => algebraMap R (Ri R) (y i)) ∈ zerOfFinset (Ri R) Ps := by
  intro p hp
  rw [aeval_algebraMap_tuple, hy p hp, map_zero]

/-- The sign of `mvHerCoeff` at a real zero `x` matches `sign(Q(reL x))`. -/
theorem sign_mvHerCoeff_real {Ps : Finset (MvPolynomial (Fin k) R)}
    [Module.Finite R (quotPolys Ps)]
    {Q : MvPolynomial (Fin k) R} {hfin : (zerOfFinset (Ri R) Ps).Finite} {x : Fin k → Ri R}
    (hx : x ∈ mvHerRoots Ps Q hfin) (hxr : conjTuple x = x) :
    SignType.sign (mvHerCoeff Ps Q hfin x)
      = SignType.sign (MvPolynomial.aeval (fun i => Ri.reL (x i)) Q) := by
  have hxz : x ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hx).1
  have hmap : (fun i => algebraMap R (Ri R) (Ri.reL (x i))) = x := by
    funext i; exact algebraMap_reL_tuple_of_conj_fixed hxr i
  rw [mvHerCoeff, if_pos hxr]
  -- mvHerWeight x = mult • aeval x Q = algebraMap (mult • aeval (reL x) Q)
  have hweight : mvHerWeight Ps Q x
      = algebraMap R (Ri R) ((mult Ps x) • MvPolynomial.aeval (fun i => Ri.reL (x i)) Q) := by
    rw [mvHerWeight, map_nsmul]
    congr 1
    rw [← aeval_algebraMap_tuple, hmap]
  have hfix : Ri.conj R (mvHerWeight Ps Q x) = mvHerWeight Ps Q x := by
    rw [hweight, Ri.conj_algebraMap_ordered]
  have hreL : Ri.reL (mvHerWeight Ps Q x)
      = (mult Ps x) • MvPolynomial.aeval (fun i => Ri.reL (x i)) Q := by
    apply (algebraMap R (Ri R)).injective
    rw [algebraMap_reL_of_conj_fixed hfix, hweight]
  rw [hreL, nsmul_eq_mul]
  have hcount : 0 < (mult Ps x : R) := by
    have hpos : 0 < mult Ps x := by
      rw [mult_eq_of_mem hxz]
      haveI : Module.Finite (Ri R) (quotPolysExt (Ri R) Ps) := moduleFinite_quotPolysExt (Ri R) Ps
      haveI : Nontrivial (localizationAtPoint (Ri R) Ps x hxz) :=
        (isLocalRing_localizationAtPoint (Ri R) Ps x hxz).toNontrivial
      exact Module.finrank_pos
    exact_mod_cast hpos
  rw [sign_mul, sign_pos hcount, one_mul]

/-- The sum of `sign(mvHerCoeff)` over non-real zeros vanishes (conjugate pairs cancel). -/
theorem sum_sign_mvHerCoeff_nonreal (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) :
    ∑ x ∈ (mvHerRoots Ps Q hfin).filter (fun x => ¬ conjTuple x = x),
        (SignType.sign (mvHerCoeff Ps Q hfin x) : ℤ) = 0 := by
  classical
  refine Finset.sum_involution (fun x _ => conjTuple x) ?_ ?_ ?_ ?_
  · intro x hx
    have hxr : ¬ conjTuple x = x := (Finset.mem_filter.mp hx).2
    have hxz : x ∈ zerOfFinset (Ri R) Ps :=
      (mem_mvHerRoots_iff.mp (Finset.mem_filter.mp hx).1).1
    rw [mvHerCoeff_conjTuple_of_not_real Ps Q hfin hxz hxr, Left.sign_neg]
    push_cast; ring
  · intro x hx _
    exact (Finset.mem_filter.mp hx).2
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨conjTuple_mem_mvHerRoots hx.1, ?_⟩
    intro h
    exact hx.2 (by rw [← h, conjTuple_involutive])
  · intro x _
    exact conjTuple_involutive x

/-- **The signature sum.** `∑_{x ∈ mvHerRoots} sign(mvHerCoeff x) = TaQ(Q, 𝒫)`. -/
theorem sum_sign_mvHerCoeff (Ps : Finset (MvPolynomial (Fin k) R)) [CharZero R]
    [Module.Finite R (quotPolys Ps)] (Q : MvPolynomial (Fin k) R)
    (hfin : (zerOfFinset (Ri R) Ps).Finite) (hfinR : (zerOfFinset R Ps).Finite) :
    ∑ x ∈ mvHerRoots Ps Q hfin, (SignType.sign (mvHerCoeff Ps Q hfin x) : ℤ)
      = tarskiQuery R Q Ps hfinR := by
  classical
  -- split into real and non-real
  rw [← Finset.sum_filter_add_sum_filter_not (mvHerRoots Ps Q hfin) (fun x => conjTuple x = x),
    sum_sign_mvHerCoeff_nonreal, add_zero]
  rw [tarskiQuery]
  -- the real part sums over real zeros; the `Q = 0` real zeros contribute 0
  rw [← Finset.sum_filter_of_ne (p := fun y => MvPolynomial.aeval y Q ≠ 0)
    (s := hfinR.toFinset) (f := fun y => (SignType.sign (MvPolynomial.aeval y Q) : ℤ)) ?_]
  · -- bijection real `mvHerRoots` ↔ {y ∈ real zeros | Q(y) ≠ 0}
    refine Finset.sum_nbij' (fun x => fun i => Ri.reL (x i))
      (fun y => fun i => algebraMap R (Ri R) (y i)) ?_ ?_ ?_ ?_ ?_
    · -- hi: reL x is a real zero with Q ≠ 0
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxmem := hx.1
      have hxr : conjTuple x = x := hx.2
      have hxz : x ∈ zerOfFinset (Ri R) Ps := (mem_mvHerRoots_iff.mp hxmem).1
      have hQ := (mem_mvHerRoots_iff.mp hxmem).2
      have hmap : (fun i => algebraMap R (Ri R) (Ri.reL (x i))) = x := by
        funext i; exact algebraMap_reL_tuple_of_conj_fixed hxr i
      rw [Finset.mem_filter, hfinR.mem_toFinset]
      refine ⟨?_, ?_⟩
      · -- `reL x` is a real zero
        intro p hp
        apply (algebraMap R (Ri R)).injective
        rw [map_zero, ← aeval_algebraMap_tuple, hmap]
        exact hxz p hp
      · -- `Q(reL x) ≠ 0`
        intro hQev
        apply hQ
        have : MvPolynomial.aeval (fun i => algebraMap R (Ri R) (Ri.reL (x i))) Q = 0 := by
          rw [aeval_algebraMap_tuple, hQev, map_zero]
        rwa [hmap] at this
    · -- hj: algebraMap ∘ y ∈ real mvHerRoots
      intro y hy
      rw [Finset.mem_filter, hfinR.mem_toFinset] at hy
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_mvHerRoots_iff]
        refine ⟨algebraMap_tuple_mem_zer hy.1, ?_⟩
        rw [aeval_algebraMap_tuple]
        intro h
        exact hy.2 ((algebraMap R (Ri R)).injective (by rw [h, map_zero]))
      · funext i; rw [conjTuple_apply, Ri.conj_algebraMap_ordered]
    · -- left inverse
      intro x hx
      rw [Finset.mem_filter] at hx
      funext i; exact algebraMap_reL_tuple_of_conj_fixed hx.2 i
    · -- right inverse
      intro y _
      funext i
      show Ri.reL (algebraMap R (Ri R) (y i)) = y i
      rw [show algebraMap R (Ri R) (y i) = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (y i) from rfl,
        Ri.reL_of]
    · -- sign matching
      intro x hx
      rw [Finset.mem_filter] at hx
      exact congrArg (fun s : SignType => (s : ℤ)) (sign_mvHerCoeff_real hx.1 hx.2)
  · intro y _ hsign
    by_contra hne
    apply hsign
    rw [hne, sign_zero]; simp

end MvHermite

/-- **Finiteness of the complex zero set from finite-dimensionality.** When `A = R[X]/Ideal(𝒫, R)`
is finite-dimensional, the set `Zer(𝒫, Cᵏ)` of zeros over the algebraic closure `C = Ri R` is
finite. This is the `R`-finiteness direction of Theorem 4.86 (`FiniteDimensional R A ↔
Zer(𝒫, Cᵏ).Finite`), so `hfinC` need not be assumed separately. -/
theorem zerOfFinset_finite_of_moduleFinite (Ps : Finset (MvPolynomial (Fin k) R))
    [Module.Finite R (quotPolys Ps)] : (zerOfFinset (Ri R) Ps).Finite := by
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  haveI : CharZero R := inferInstance
  have hfd : FiniteDimensional R (quotPolys Ps) ↔ (zerOfFinset (Ri R) Ps).Finite := by
    rw [(lemma_4_88 (Ri R) Ps).2, finiteDimensional_ext_iff_isIntegral, isIntegral_iff_finite]
  exact hfd.mp inferInstance

/-- **BPR Theorem 4.101 (Multivariate Hermite).** Over a real closed field `R` with `C = Ri R`, the
rank of Hermite's quadratic form `Her(𝒫, Q)` is the number of distinct zeros `x ∈ Zer(𝒫, Cᵏ)` with
`Q(x) ≠ 0`, and its signature is the Tarski query `TaQ(Q, 𝒫)`. The finiteness of `Zer(𝒫, Cᵏ)` is a
consequence of `Module.Finite` (`zerOfFinset_finite_of_moduleFinite`), so it is not assumed. -/
theorem theorem_4_101 (Ps : Finset (MvPolynomial (Fin k) R)) (Q : MvPolynomial (Fin k) R)
    [Module.Finite R (quotPolys Ps)]
    (hfinR : (zerOfFinset R Ps).Finite) :
    hermiteFormRank Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q)
        = {x ∈ zerOfFinset (Ri R) Ps | MvPolynomial.aeval x Q ≠ 0}.ncard
      ∧ hermiteFormSign Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q)
        = tarskiQuery R Q Ps hfinR := by
  haveI : CharZero R := inferInstance
  have hfinC : (zerOfFinset (Ri R) Ps).Finite := zerOfFinset_finite_of_moduleFinite Ps
  -- isometry invariance of the inertia indices
  have hequiv := MvHermite.mvHerQuad_equiv Ps Q
  have hpos : sigPos (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q))
      = sigPos (MvHermite.mvHerQuad Ps Q) := hequiv.sigPos_eq
  have hneg : sigNeg (hermiteQuad Ps (Ideal.Quotient.mk (idealOfPolys Ps) Q))
      = sigNeg (MvHermite.mvHerQuad Ps Q) := hequiv.sigNeg_eq
  set de := MvHermite.mvHerDiagExpr Ps Q hfinC with hde
  constructor
  · -- RANK
    rw [hermiteFormRank, hpos, hneg, ← de.r_eq_sigPos_add_sigNeg]
    show (MvHermite.mvHerRoots Ps Q hfinC).card = _
    rw [MvHermite.mvHerRoots, ← Set.ncard_coe_finset]
    congr 1
    rw [Finset.coe_filter]
    ext x
    simp only [Set.mem_setOf_eq, hfinC.mem_toFinset]
  · -- SIGNATURE
    rw [hermiteFormSign, hpos, hneg,
      show ((sigPos (MvHermite.mvHerQuad Ps Q) : ℤ) - sigNeg (MvHermite.mvHerQuad Ps Q))
          = de.signature from by
        rw [de.signature_eq, Sign]]
    rw [DiagonalExpression.signature, MvHermite.mvHerDiagExpr_posCount,
      MvHermite.mvHerDiagExpr_negCount,
      MvHermite.card_pos_sub_card_neg_eq_sum_sign (MvHermite.mvHerRoots Ps Q hfinC)
        (MvHermite.mvHerCoeff Ps Q hfinC) (fun x hx => MvHermite.mvHerCoeff_ne_zero hx),
      MvHermite.sum_sign_mvHerCoeff Ps Q hfinC hfinR]

end Azurite.BPR.Chapter4
