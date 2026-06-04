import Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgClosedAlgebraicPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Corollary_2_98
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # BPR §2.6 — `C⟨ε⟩ = R⟨ε⟩[i]` for `C = R[i]`

This is the algebraically closed companion to Corollary 2.98. If `R` is real closed and `C = R[i]`
(`Ri R`), then the field `C⟨ε⟩` of algebraic Puiseux series over `C` is an algebraic closure of
`C(ε)` (Corollary `cor:alg-closed-puiseux`), and it coincides with `R⟨ε⟩[i]`:
`algebraicPuiseux (Ri R) ≃+* Ri (algebraicPuiseux R)`.

The proof is by uniqueness of algebraic closures (`IsAlgClosure.equivOfAlgebraic`): both fields are
algebraic closures of `R(ε) = RatFunc R`. The left-hand field is the algebraic closure of
`C(ε) = (R[i])(ε)`, and `C(ε)` is a degree-two algebraic extension of `R(ε)` (the crux lemma
`isAlgebraic_baseChange`); the right-hand field `R⟨ε⟩[i]` is the algebraic closure of `R⟨ε⟩` (which is
real closed by Corollary 2.98, so `Ri (R⟨ε⟩)` is algebraically closed by Theorem 2.11) and is
algebraic over `R(ε)` since `R⟨ε⟩` is. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

/-- The base-change ring homomorphism `R(ε) → (R[i])(ε)` induced by `R → R[i]`, mapping numerator and
denominator. -/
noncomputable def baseChange (R : Type*) [Field R] [IsRealClosed R] :
    RatFunc R →+* RatFunc (Ri R) :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap R (Ri R)))
    (by
      intro p hp
      simp only [Submonoid.mem_comap, coe_mapRingHom]
      rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
      rw [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
      exact hp)

/-- `R(ε)` acts on `(R[i])(ε)` via the base-change map `baseChange`. -/
noncomputable instance instAlgRatFuncRi : Algebra (RatFunc R) (RatFunc (Ri R)) :=
  (baseChange R).toAlgebra

theorem algebraMap_eq_baseChange :
    (algebraMap (RatFunc R) (RatFunc (Ri R))) = baseChange R := rfl

/-- `baseChange` on the inclusion of a polynomial is the inclusion of its coefficient-mapped image. -/
theorem baseChange_algebraMap (p : R[X]) :
    baseChange R (algebraMap R[X] (RatFunc R) p)
      = algebraMap (Ri R)[X] (RatFunc (Ri R)) (p.map (algebraMap R (Ri R))) := by
  have : algebraMap R[X] (RatFunc R) p
      = algebraMap R[X] (RatFunc R) p / algebraMap R[X] (RatFunc R) 1 := by simp
  rw [baseChange, this, RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  simp [coe_mapRingHom]

/-- The imaginary unit of `R[i]`, regarded as a constant in `(R[i])(ε)`. -/
noncomputable def riConst (R : Type*) [Field R] [IsRealClosed R] : RatFunc (Ri R) :=
  algebraMap (Ri R) (RatFunc (Ri R)) (Ri.i R)

theorem riConst_sq : (riConst R) ^ 2 = -1 := by
  rw [riConst, ← map_pow, Ri.i_sq, map_neg, map_one]

/-- **The crux: `(R[i])(ε)` is algebraic over `R(ε)`** (a degree-two base change). Every element is a
ratio of polynomials in `R[i]`, whose coefficients decompose as `a + b·i` with `a, b ∈ R`; the
constant `i` is algebraic (a root of `x² + 1`) and the rest lie in the image of `R(ε)`. -/
theorem isAlgebraic_baseChange : Algebra.IsAlgebraic (RatFunc R) (RatFunc (Ri R)) := by
  rw [← algebraicClosure.eq_top_iff, eq_top_iff]
  intro z _
  set AC := algebraicClosure (RatFunc R) (RatFunc (Ri R)) with hAC
  have hi : riConst R ∈ AC := by
    rw [mem_algebraicClosure_iff]
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · exact fun h => by simpa using congrArg (Polynomial.coeff · 0) h
    · rw [map_add, map_pow, aeval_X, map_one, riConst_sq]; ring
  have hX : algebraMap (Ri R)[X] (RatFunc (Ri R)) Polynomial.X ∈ AC := by
    have h1 : algebraMap (Ri R)[X] (RatFunc (Ri R)) Polynomial.X
        = baseChange R (algebraMap R[X] (RatFunc R) Polynomial.X) := by
      rw [baseChange_algebraMap, Polynomial.map_X]
    rw [h1, ← algebraMap_eq_baseChange]; exact IntermediateField.algebraMap_mem _ _
  have hC : ∀ c : Ri R, algebraMap (Ri R) (RatFunc (Ri R)) c ∈ AC := by
    intro c
    have hc := Ri.of_reL_add_of_imL_mul_i c
    rw [← hc, map_add, map_mul]
    refine AC.add_mem ?_ (AC.mul_mem ?_ hi)
    · have : algebraMap (Ri R) (RatFunc (Ri R)) (AdjoinRoot.of (X ^ 2 + 1) (Ri.reL c))
          = baseChange R (algebraMap R[X] (RatFunc R) (C (Ri.reL c))) := by
        rw [baseChange_algebraMap, Polynomial.map_C, RatFunc.algebraMap_C,
          ← RatFunc.algebraMap_eq_C]; rfl
      rw [this, ← algebraMap_eq_baseChange]; exact IntermediateField.algebraMap_mem _ _
    · have : algebraMap (Ri R) (RatFunc (Ri R)) (AdjoinRoot.of (X ^ 2 + 1) (Ri.imL c))
          = baseChange R (algebraMap R[X] (RatFunc R) (C (Ri.imL c))) := by
        rw [baseChange_algebraMap, Polynomial.map_C, RatFunc.algebraMap_C,
          ← RatFunc.algebraMap_eq_C]; rfl
      rw [this, ← algebraMap_eq_baseChange]; exact IntermediateField.algebraMap_mem _ _
  have hP : ∀ p : (Ri R)[X], algebraMap (Ri R)[X] (RatFunc (Ri R)) p ∈ AC := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact AC.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C]
      exact AC.mul_mem (hC a) (AC.pow_mem hX n)
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := (Ri R)[X]) z
  exact AC.div_mem (hP p) (hP q)

/-- **`C⟨ε⟩ = R⟨ε⟩[i]` for `C = R[i]`.** When `R` is real closed, the algebraic Puiseux series over
`C = R[i]` form the field `R⟨ε⟩[i]`: `algebraicPuiseux (Ri R) ≃+* Ri (algebraicPuiseux R)`. -/
noncomputable def riAlgebraicPuiseuxEquiv (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] :
    algebraicPuiseux (Ri R) ≃+* Ri (algebraicPuiseux R) := by
  haveI hrcAP : IsRealClosed (algebraicPuiseux R) := isRealClosed_algebraicPuiseux R
  haveI : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  haveI : CharZero (Ri R) := by
    refine ⟨fun a b h => Nat.cast_injective (R := R) (RingHom.injective (algebraMap R (Ri R)) ?_)⟩
    rw [map_natCast, map_natCast]; exact h
  haveI : IsAlgClosed (PuiseuxSeries (Ri R)) := isAlgClosed_puiseuxSeries (Ri R)
  -- the algebra structures on the relative algebraic closures (defeq to the intermediate fields)
  letI algJL : Algebra (RatFunc (Ri R)) (algebraicPuiseux (Ri R)) :=
    inferInstanceAs (Algebra (RatFunc (Ri R))
      (algebraicClosure (RatFunc (Ri R)) (PuiseuxSeries (Ri R))))
  letI algRaP : Algebra (RatFunc R) (algebraicPuiseux R) :=
    inferInstanceAs (Algebra (RatFunc R) (algebraicClosure (RatFunc R) (PuiseuxSeries R)))
  -- L = algebraicPuiseux (Ri R) is an algebraic closure of J = RatFunc (Ri R)
  haveI hAClL : IsAlgClosure (RatFunc (Ri R)) (algebraicPuiseux (Ri R)) :=
    algebraicClosure.isAlgClosure (RatFunc (Ri R)) (PuiseuxSeries (Ri R))
  -- M = Ri (algebraicPuiseux R) is an algebraic closure of K = RatFunc R
  -- (its `RatFunc R`-algebra and scalar tower through `algebraicPuiseux R` are canonical)
  haveI : Module.Finite (algebraicPuiseux R) (Ri (algebraicPuiseux R)) :=
    riMonic.finite_adjoinRoot
  haveI : Algebra.IsAlgebraic (algebraicPuiseux R) (Ri (algebraicPuiseux R)) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI algKaP : Algebra.IsAlgebraic (RatFunc R) (algebraicPuiseux R) :=
    inferInstanceAs (Algebra.IsAlgebraic (RatFunc R)
      (algebraicClosure (RatFunc R) (PuiseuxSeries R)))
  haveI : Algebra.IsAlgebraic (RatFunc R) (Ri (algebraicPuiseux R)) :=
    Algebra.IsAlgebraic.trans (RatFunc R) (algebraicPuiseux R) (Ri (algebraicPuiseux R))
  haveI : IsAlgClosed (Ri (algebraicPuiseux R)) := Theorem2_11.isAlgClosed_Ri
  haveI hAClM : IsAlgClosure (RatFunc R) (Ri (algebraicPuiseux R)) := ⟨inferInstance, inferInstance⟩
  -- K = RatFunc R acts on L = algebraicPuiseux (Ri R) through J = RatFunc (Ri R)
  letI algKL : Algebra (RatFunc R) (algebraicPuiseux (Ri R)) :=
    ((algebraMap (RatFunc (Ri R)) (algebraicPuiseux (Ri R))).comp (baseChange R)).toAlgebra
  haveI towerKJL : IsScalarTower (RatFunc R) (RatFunc (Ri R)) (algebraicPuiseux (Ri R)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic (RatFunc R) (RatFunc (Ri R)) := isAlgebraic_baseChange
  exact (IsAlgClosure.equivOfAlgebraic (RatFunc R) (RatFunc (Ri R))
    (algebraicPuiseux (Ri R)) (Ri (algebraicPuiseux R))).toRingEquiv

end Azurite.BPR
