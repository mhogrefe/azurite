import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_11
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_7
import Azurite.BasuPollackRoy.Chapter2.Section2_1.OrderZeroPlus
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_86
import Azurite.BasuPollackRoy.Chapter2.Section2_4.RealClosureEmbedding
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! # BPR §3.3 — Proposition 3.13: the germ field is the real closure of `R(ε)`

The germs of semialgebraic continuous functions at the right of the origin form the real closure of
`R(ε)`, equipped with the unique order making `ε` positive and infinitesimal, where `ε` is sent to
the germ of the identity map. By Proposition 3.11 the germ field is real closed, and by
Proposition 2.86 every germ is algebraic over `R(ε)`; uniqueness of the real closure then identifies
the two fields.

This file builds the identification in stages: the identity germ `ε` (this section), the
order-preserving embedding of `R(ε)`, algebraicity, and the assembly. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **`ε` as a germ:** the representative `t ↦ t` (the identity), defined on `(0, 1)`. -/
noncomputable def idGermRep : SemialgGermRep R where
  bound := 1
  bound_pos := one_pos
  toFun := fun u => u 0
  isSemialgContinuous := by
    have hsf : scalarFun (fun u : Fin 1 → R => u 0) = polynomialMap ![MvPolynomial.X 0] := by
      funext u i; rw [Subsingleton.elim i 0]; simp [scalarFun, constPt, polynomialMap]
    refine ⟨?_, ?_⟩
    · rw [hsf]; exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_rightNbhd 1) _
    · rw [hsf]; exact (continuous_polynomialMap _).continuousOn

/-- **`ε`**, the germ of the identity at the right of the origin. -/
noncomputable def idGerm : SemialgGerm R := Quotient.mk _ idGermRep

@[simp] theorem idGermRep_toFun (u : Fin 1 → R) : (idGermRep : SemialgGermRep R).toFun u = u 0 := rfl

/-- **`ε` is positive.** -/
theorem idGerm_pos : (0 : SemialgGerm R) < idGerm :=
  SemialgGerm.lt_zero_iff.mpr (by
    rw [idGerm, isPosGerm_mk]
    exact ⟨1, one_pos, fun s hs _ => hs⟩)

/-! ### The sign of a polynomial near `0⁺`

The key analytic fact behind the order-preserving embedding of `R(ε)`: a polynomial keeps the sign of
its trailing coefficient on a right-neighborhood of the origin. This is established without limits,
using only the intermediate value property of `R`. -/

omit [IsRealClosed R] in
/-- A polynomial nonzero at `0` is nonzero on a right-neighborhood of `0` (no positive root below the
smallest positive root). -/
theorem poly_eval_ne_zero_near_zero {q : Polynomial R} (h0 : q.eval 0 ≠ 0) :
    ∃ t₀, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ → q.eval t ≠ 0 := by
  classical
  have hq : q ≠ 0 := fun hq => h0 (by rw [hq, Polynomial.eval_zero])
  have hmem : ∀ t, 0 < t → q.eval t = 0 →
      t ∈ q.roots.toFinset.filter (fun r => 0 < r) := fun t ht hev =>
    Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hev), ht⟩
  by_cases hSne : (q.roots.toFinset.filter (fun r => 0 < r)).Nonempty
  · refine ⟨(q.roots.toFinset.filter (fun r => 0 < r)).min' hSne, ?_, fun t ht htlt hev => ?_⟩
    · exact (Finset.mem_filter.mp
        ((q.roots.toFinset.filter (fun r => 0 < r)).min'_mem hSne)).2
    · exact absurd ((q.roots.toFinset.filter (fun r => 0 < r)).min'_le t (hmem t ht hev))
        (not_le.mpr htlt)
  · exact ⟨1, one_pos, fun t ht _ hev => hSne ⟨t, hmem t ht hev⟩⟩

/-- A polynomial keeps the sign of its value at `0` on a right-neighborhood of `0` (a sign change
would force a root by the intermediate value property). -/
theorem poly_eval_same_sign_near_zero {q : Polynomial R} (h0 : q.eval 0 ≠ 0) :
    ∃ t₀, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ → 0 < q.eval t * q.eval 0 := by
  obtain ⟨t₀, ht₀, hne⟩ := poly_eval_ne_zero_near_zero h0
  refine ⟨t₀, ht₀, fun t ht htlt => ?_⟩
  have hqt : q.eval t ≠ 0 := hne t ht htlt
  rcases lt_trichotomy (q.eval t * q.eval 0) 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨x, hx0, hxt, hxev⟩ :=
      hasIVP_of_isRealClosed q 0 t ht (by rw [mul_comm]; exact hlt)
    exact hne x hx0 (lt_trans hxt htlt) hxev
  · exact absurd heq (mul_ne_zero hqt h0)
  · exact hgt

/-- **The sign of a polynomial near `0⁺` is the sign of its trailing coefficient.** -/
theorem poly_eval_mul_trailingCoeff_pos {p : Polynomial R} (hp : p ≠ 0) :
    ∃ t₀, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ → 0 < p.eval t * p.trailingCoeff := by
  have hdvd : (Polynomial.X : Polynomial R) ^ p.natTrailingDegree ∣ p := by
    rw [Polynomial.X_pow_dvd_iff]
    exact fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  obtain ⟨q, hpq⟩ := hdvd
  have hcoeff : p.trailingCoeff = q.eval 0 := by
    have key : (Polynomial.X ^ p.natTrailingDegree * q).coeff (0 + p.natTrailingDegree) = q.coeff 0 :=
      Polynomial.coeff_X_pow_mul q p.natTrailingDegree 0
    rw [zero_add, ← hpq] at key
    rw [Polynomial.trailingCoeff, key, Polynomial.coeff_zero_eq_eval_zero]
  have hq0 : q.eval 0 ≠ 0 := by
    rw [← hcoeff]; exact fun h => hp (Polynomial.trailingCoeff_eq_zero.mp h)
  obtain ⟨t₀, ht₀, hsign⟩ := poly_eval_same_sign_near_zero hq0
  refine ⟨t₀, ht₀, fun t ht htlt => ?_⟩
  rw [hcoeff, hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    mul_assoc]
  exact mul_pos (pow_pos ht _) (hsign t ht htlt)

/-! ### The embedding `R[X] → SemialgGerm R` -/

/-- A constant function is semialgebraic and continuous near the origin. -/
theorem isSemialgContinuousOn_const (a : R) {t : R} :
    IsSemialgContinuousOn (rightNbhd t) (fun _ : Fin 1 → R => a) := by
  have hsf : scalarFun (fun _ : Fin 1 → R => a) = polynomialMap ![MvPolynomial.C a] := by
    funext u i; rw [Subsingleton.elim i 0]
    simp [scalarFun, constPt, polynomialMap, MvPolynomial.eval_C]
  exact ⟨by rw [hsf]; exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_rightNbhd t) _,
    by rw [hsf]; exact (continuous_polynomialMap _).continuousOn⟩

/-- The ring hom `R →+* semialgContSubring 1` sending `a` to the constant function `a`. -/
noncomputable def constSubHom : R →+* semialgContSubring (1 : R) :=
  (algebraMap R ((Fin 1 → R) → R)).codRestrict (semialgContSubring 1) fun a =>
    mem_semialgContSubring.mpr (by
      have : (algebraMap R ((Fin 1 → R) → R)) a = fun _ : Fin 1 → R => a := rfl
      rw [this]; exact isSemialgContinuousOn_const a)

/-- The identity function as an element of `semialgContSubring 1`. -/
noncomputable def idSubFun : semialgContSubring (1 : R) :=
  ⟨fun u => u 0, mem_semialgContSubring.mpr (idGermRep : SemialgGermRep R).isSemialgContinuous⟩

/-- **The evaluation map `R[X] → SemialgGerm R` sending `X` to `ε`** (the germ of the identity). -/
noncomputable def polyToGermHom : Polynomial R →+* SemialgGerm R :=
  (germHom (1 : R) one_pos).comp (Polynomial.eval₂RingHom constSubHom idSubFun)

/-- The underlying function of `eval₂ p` is `u ↦ p(u₀)`. -/
theorem polyToSub_val (p : Polynomial R) (u : Fin 1 → R) :
    ((Polynomial.eval₂RingHom constSubHom idSubFun p : semialgContSubring (1 : R)) :
      (Fin 1 → R) → R) u = p.eval (u 0) := by
  have hcomp : ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
      (semialgContSubring (1 : R)).subtype).comp constSubHom = RingHom.id R := by
    ext a; rfl
  show ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp (semialgContSubring (1 : R)).subtype)
      (Polynomial.eval₂RingHom constSubHom idSubFun p) = p.eval (u 0)
  rw [show (Polynomial.eval₂RingHom constSubHom idSubFun p) = p.eval₂ constSubHom idSubFun from rfl,
    Polynomial.hom_eval₂, hcomp,
    show ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
      (semialgContSubring (1 : R)).subtype) idSubFun = u 0 from rfl, Polynomial.eval₂_id]

/-- **The evaluation map is injective:** `ε` is transcendental over `R` (a nonzero polynomial is
eventually nonzero near `0⁺`). -/
theorem polyToGermHom_injective :
    Function.Injective (polyToGermHom : Polynomial R →+* SemialgGerm R) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hpne
  obtain ⟨t₀, ht₀, hsign⟩ := poly_eval_mul_trailingCoeff_pos hpne
  rw [polyToGermHom, RingHom.comp_apply, germHom_apply,
    show (0 : SemialgGerm R) = Quotient.mk _ SemialgGermRep.zero from rfl] at hp
  obtain ⟨t, ht, H⟩ := Quotient.exact hp
  set s := min t t₀ / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hsmin : s < min t t₀ := by rw [hsdef]; exact half_lt_self (lt_min ht ht₀)
  have hH := H s hs0 (hsmin.trans_le (min_le_left _ _))
  simp only [SemialgGermRep.zero_toFun, Pi.zero_apply] at hH
  have hpe : p.eval s = 0 := by
    have hv := polyToSub_val p (constPt s)
    rw [show (constPt s) 0 = s from rfl] at hv
    rw [← hv]; exact hH
  have hsg := hsign s hs0 (hsmin.trans_le (min_le_right _ _))
  rw [hpe, zero_mul] at hsg
  exact absurd hsg (lt_irrefl 0)

/-- **The embedding `R(ε) → SemialgGerm R`** sending `ε` to the germ of the identity, obtained from
`polyToGermHom` by the universal property of the field of fractions. -/
noncomputable def ratFuncToGermHom : RatFunc R →+* SemialgGerm R :=
  RatFunc.liftRingHom polyToGermHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polyToGermHom_injective)

theorem ratFuncToGermHom_injective :
    Function.Injective (ratFuncToGermHom : RatFunc R → SemialgGerm R) :=
  RatFunc.liftRingHom_injective _ polyToGermHom_injective _

/-- A polynomial eventually positive near `0⁺` has a positive germ. -/
theorem polyToGermHom_pos {p : Polynomial R}
    (h : ∃ t, 0 < t ∧ ∀ s, 0 < s → s < t → 0 < p.eval s) : 0 < polyToGermHom p := by
  rw [SemialgGerm.lt_zero_iff, polyToGermHom, RingHom.comp_apply, germHom_apply, isPosGerm_mk]
  obtain ⟨t, ht, H⟩ := h
  refine ⟨t, ht, fun s hs hst => ?_⟩
  show 0 < ((Polynomial.eval₂RingHom constSubHom idSubFun p : semialgContSubring (1 : R)) :
    (Fin 1 → R) → R) (constPt s)
  rw [polyToSub_val]
  exact H s hs hst

/-- **The embedding is positive-cone preserving** (the crux of order-preservation): a `0₊`-positive
rational function has a positive germ. -/
theorem ratFuncToGermHom_pos {x : RatFunc R} (hx : ZeroPlus.rfPos x) :
    0 < ratFuncToGermHom x := by
  obtain ⟨hne, htrail⟩ := hx
  have hx_eq : ratFuncToGermHom x = polyToGermHom x.num / polyToGermHom x.denom := by
    conv_lhs => rw [← RatFunc.num_div_denom x]
    exact RatFunc.liftRingHom_apply_div polyToGermHom _ x.num x.denom
  rw [hx_eq]
  have hmul : 0 < polyToGermHom (x.num * x.denom) := by
    obtain ⟨t₀, ht₀, hsign⟩ := poly_eval_mul_trailingCoeff_pos hne
    exact polyToGermHom_pos ⟨t₀, ht₀, fun s hs hst => (mul_pos_iff_of_pos_right htrail).mp
      (hsign s hs hst)⟩
  rw [map_mul] at hmul
  rcases mul_pos_iff.mp hmul with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact div_pos ha hb
  · exact div_pos_of_neg_of_neg ha hb

/-- **The embedding `R(ε) → SemialgGerm R` is strictly monotone** in the `0₊` order. -/
theorem ratFuncToGermHom_strictMono :
    StrictMono (ratFuncToGermHom : RatFunc R → SemialgGerm R) := by
  intro r s hrs
  rw [← sub_pos, ← map_sub]
  exact ratFuncToGermHom_pos (ZeroPlus.rf_lt_def.mp hrs)

/-- `X ↦ ε`: the polynomial variable maps to the identity germ. -/
theorem polyToGermHom_X : polyToGermHom (Polynomial.X : Polynomial R) = idGerm := by
  rw [polyToGermHom, RingHom.comp_apply,
    show Polynomial.eval₂RingHom constSubHom idSubFun Polynomial.X = idSubFun from
      Polynomial.eval₂_X _ _,
    germHom_apply]
  rfl

/-- `ε ↦ ε`: the rational-function variable maps to the identity germ. -/
theorem ratFuncToGermHom_εR :
    ratFuncToGermHom (algebraMap (Polynomial R) (RatFunc R) Polynomial.X) = idGerm := by
  rw [ratFuncToGermHom, RatFunc.liftRingHom_algebraMap, polyToGermHom_X]

/-! ### Algebraicity over `R(ε)` (BPR Proposition 2.86) -/

/-- The constant-germ embedding `R →+* SemialgGerm R` (`a ↦ ⟦a⟧`). -/
noncomputable def constGermHom : R →+* SemialgGerm R := (germHom (1 : R) one_pos).comp constSubHom

theorem constGermHom_eq (a : R) : constGermHom a = polyToGermHom (Polynomial.C a) := by
  rw [constGermHom, polyToGermHom, RingHom.comp_apply, RingHom.comp_apply]
  congr 1
  simp

theorem ratFuncToGermHom_C (a : R) :
    ratFuncToGermHom (algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)) = constGermHom a := by
  rw [ratFuncToGermHom, RatFunc.liftRingHom_algebraMap, constGermHom_eq]

noncomputable instance : Algebra (RatFunc R) (SemialgGerm R) := ratFuncToGermHom.toAlgebra
noncomputable instance : Algebra R (SemialgGerm R) := constGermHom.toAlgebra

instance : IsScalarTower R (RatFunc R) (SemialgGerm R) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    show constGermHom a = ratFuncToGermHom (algebraMap R (RatFunc R) a)
    have hh : algebraMap R (RatFunc R) a
        = algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (RatFunc R), ← Polynomial.C_eq_algebraMap]
    rw [hh, ratFuncToGermHom_C]

/-- **The germ relation.** If `P(t, f(t)) = 0` on a right-neighborhood of the origin, then
`P(ε, ⟦f⟧) = 0` in the germ field: substituting `X ↦ ε` to view `P` as a polynomial in `Y` over
`R(ε)` and evaluating at the germ `⟦f⟧` gives the germ of the pointwise evaluation
`u ↦ P(u₀, f(u))`, which vanishes. -/
theorem aeval_germ_eq_zero (f : SemialgGermRep R) (P : MvPolynomial (Fin 2) R)
    (hP : ∀ u ∈ rightNbhd f.bound, MvPolynomial.eval (pt (u 0) (f.toFun u)) P = 0) :
    Polynomial.aeval (Quotient.mk (semialgGermSetoid R) f)
      (MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X),
        Polynomial.X] : Fin 2 → Polynomial (RatFunc R)) P) = 0 := by
  set t : R := min 1 f.bound with htdef
  have ht : 0 < t := lt_min one_pos f.bound_pos
  have hidsc : IsSemialgContinuousOn (rightNbhd t) (fun u : Fin 1 → R => u 0) :=
    (idGermRep : SemialgGermRep R).isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd t)
      (rightNbhd_subset (min_le_left _ _))
  have hfsc : IsSemialgContinuousOn (rightNbhd t) f.toFun :=
    f.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd t) (rightNbhd_subset (min_le_right _ _))
  set cSub : R →+* semialgContSubring t :=
    (algebraMap R ((Fin 1 → R) → R)).codRestrict (semialgContSubring t) (fun a =>
      mem_semialgContSubring.mpr (isSemialgContinuousOn_const a)) with hcSub
  set vSub : Fin 2 → semialgContSubring t :=
    ![⟨fun u => u 0, mem_semialgContSubring.mpr hidsc⟩, ⟨f.toFun, mem_semialgContSubring.mpr hfsc⟩]
    with hvSub
  set evalSub : MvPolynomial (Fin 2) R →+* semialgContSubring t :=
    MvPolynomial.eval₂Hom cSub vSub with hevalSub
  -- the underlying function of `evalSub Q` is the pointwise evaluation
  have hval : ∀ (Q : MvPolynomial (Fin 2) R) (u : Fin 1 → R),
      ((evalSub Q : semialgContSubring t) : (Fin 1 → R) → R) u
        = MvPolynomial.eval (pt (u 0) (f.toFun u)) Q := by
    intro Q u
    have h1 : ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
        (semialgContSubring t).subtype).comp cSub = RingHom.id R := by ext a; rfl
    have h2 : (fun i => ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
        (semialgContSubring t).subtype) (vSub i)) = pt (u 0) (f.toFun u) := by
      funext i; fin_cases i <;> simp [pt, vSub]
    show ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp (semialgContSubring t).subtype)
      (MvPolynomial.eval₂Hom cSub vSub Q) = _
    rw [MvPolynomial.map_eval₂Hom, h1, h2]
    rfl
  -- the bridge: `aeval ⟦f⟧ ∘ (X ↦ ε) = germHom ∘ evalSub`, all at the `RingHom` level
  have hbridge : ((Polynomial.aeval (Quotient.mk (semialgGermSetoid R) f)).toRingHom.comp
      (MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X),
        Polynomial.X] : Fin 2 → Polynomial (RatFunc R))).toRingHom)
      = (germHom t ht).comp evalSub := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show Polynomial.aeval _ (MvPolynomial.aeval _ (MvPolynomial.C a))
        = germHom t ht (evalSub (MvPolynomial.C a))
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply R (RatFunc R) (Polynomial (RatFunc R)),
        Polynomial.algebraMap_eq, Polynomial.aeval_C, hevalSub, MvPolynomial.eval₂Hom_C, germHom_apply]
      show ratFuncToGermHom (algebraMap R (RatFunc R) a) = _
      rw [show algebraMap R (RatFunc R) a = algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a) from by
            rw [IsScalarTower.algebraMap_apply R (Polynomial R) (RatFunc R), ← Polynomial.C_eq_algebraMap],
        ratFuncToGermHom_C, constGermHom, RingHom.comp_apply, germHom_apply]
      exact Quotient.sound ⟨t, ht, fun s _ _ => rfl⟩
    · intro i
      fin_cases i
      · show Polynomial.aeval _ (MvPolynomial.aeval _ (MvPolynomial.X 0))
          = germHom t ht (evalSub (MvPolynomial.X 0))
        rw [MvPolynomial.aeval_X]
        simp only [Matrix.cons_val_zero]
        rw [Polynomial.aeval_C]
        show ratFuncToGermHom (algebraMap (Polynomial R) (RatFunc R) Polynomial.X) = _
        rw [ratFuncToGermHom_εR, hevalSub, MvPolynomial.eval₂Hom_X', hvSub, germHom_apply]
        simp only [Matrix.cons_val_zero]
        exact Quotient.sound ⟨t, ht, fun s _ _ => rfl⟩
      · show Polynomial.aeval _ (MvPolynomial.aeval _ (MvPolynomial.X 1))
          = germHom t ht (evalSub (MvPolynomial.X 1))
        rw [MvPolynomial.aeval_X]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [Polynomial.aeval_X, hevalSub, MvPolynomial.eval₂Hom_X', hvSub, germHom_apply]
        simp only [Matrix.cons_val_one]
        exact Quotient.sound ⟨t, ht, fun s _ _ => rfl⟩
  have key := DFunLike.congr_fun hbridge P
  rw [show (((Polynomial.aeval (Quotient.mk (semialgGermSetoid R) f)).toRingHom.comp
      (MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X),
        Polynomial.X] : Fin 2 → Polynomial (RatFunc R))).toRingHom) P)
      = Polynomial.aeval (Quotient.mk (semialgGermSetoid R) f) (MvPolynomial.aeval
        (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X), Polynomial.X] :
          Fin 2 → Polynomial (RatFunc R)) P) from rfl] at key
  rw [key, RingHom.comp_apply, germHom_apply,
    show (0 : SemialgGerm R) = Quotient.mk _ SemialgGermRep.zero from rfl]
  refine Quotient.sound ⟨t, ht, fun s hs hst => ?_⟩
  simp only [SemialgGermRep.zero_toFun, Pi.zero_apply]
  rw [hval]
  exact hP (constPt s) ⟨hs, lt_of_lt_of_le hst (min_le_right _ _)⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Substituting `X ↦ ε` and `Y ↦ Y` is injective from `R[X, Y]` to `R(ε)[Y]`: since `ε` is
transcendental over `R`, this factors as the variable-swap isomorphism `R[X, Y] ≅ R[X][Y]` followed
by the (injective) coefficient extension `R[X] ↪ R(ε)`. -/
private theorem aeval_two_injective : Function.Injective
    (MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X),
      Polynomial.X] : Fin 2 → Polynomial (RatFunc R)) :
      MvPolynomial (Fin 2) R →ₐ[R] Polynomial (RatFunc R)) := by
  have htr : Transcendental R (algebraMap (Polynomial R) (RatFunc R) Polynomial.X) :=
    (transcendental_algebraMap_iff (RatFunc.algebraMap_injective R)).mpr
      (Polynomial.transcendental_X R)
  set cm : MvPolynomial (Fin 1) R →ₐ[R] RatFunc R :=
    MvPolynomial.aeval (![algebraMap (Polynomial R) (RatFunc R) Polynomial.X] :
      Fin 1 → RatFunc R) with hcm
  have hcm_inj : Function.Injective cm :=
    algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_iff_transcendental.mpr htr)
  set e : MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (MvPolynomial (Fin 1) R) :=
    (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).trans (MvPolynomial.finSuccEquiv R 1)
    with he
  have hcomp : (MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R)
        Polynomial.X), Polynomial.X] : Fin 2 → Polynomial (RatFunc R)))
      = (Polynomial.mapAlgHom cm).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · show MvPolynomial.aeval _ (MvPolynomial.X 0)
        = (Polynomial.mapAlgHom cm).comp e.toAlgHom (MvPolynomial.X 0)
      rw [MvPolynomial.aeval_X]
      simp only [Matrix.cons_val_zero, AlgHom.comp_apply]
      rw [he]
      simp [AlgEquiv.trans_apply, Polynomial.coe_mapAlgHom, hcm]
      rw [show (MvPolynomial.X 1 : MvPolynomial (Fin 2) R) = MvPolynomial.X (0 : Fin 1).succ from rfl,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      simp
    · show MvPolynomial.aeval _ (MvPolynomial.X 1)
        = (Polynomial.mapAlgHom cm).comp e.toAlgHom (MvPolynomial.X 1)
      rw [MvPolynomial.aeval_X]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, AlgHom.comp_apply]
      rw [he]
      simp [AlgEquiv.trans_apply, Polynomial.coe_mapAlgHom, hcm]
      rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  rw [hcomp, AlgHom.coe_comp]
  refine Function.Injective.comp ?_ e.injective
  rw [Polynomial.coe_mapAlgHom]
  exact Polynomial.map_injective cm.toRingHom hcm_inj

/-- **The germ field is algebraic over `R(ε)`.** Every germ `⟦f⟧` is algebraic over `R(ε)`: by
Proposition 2.86 the semialgebraic function `f` satisfies a nonzero polynomial relation
`P(t, f(t)) = 0`, and substituting `X ↦ ε` turns `P` into a nonzero polynomial over `R(ε)` that
`⟦f⟧` is a root of. -/
instance instIsAlgebraicSemialgGerm : Algebra.IsAlgebraic (RatFunc R) (SemialgGerm R) := by
  constructor
  intro g
  obtain ⟨f, rfl⟩ := Quotient.exists_rep g
  obtain ⟨P, hPne, hP⟩ := proposition_2_86 f.isSemialgContinuous.1
  refine ⟨MvPolynomial.aeval (![Polynomial.C (algebraMap (Polynomial R) (RatFunc R) Polynomial.X),
    Polynomial.X] : Fin 2 → Polynomial (RatFunc R)) P, ?_, ?_⟩
  · intro h
    exact hPne (aeval_two_injective (h.trans (map_zero _).symm))
  · apply aeval_germ_eq_zero f P
    intro u hu
    have := hP u hu
    simpa [scalarFun, constPt] using this

/-! ### The germ field is the real closure of `R(ε)` (BPR Proposition 3.13) -/

/-- **The order of `R(ε)` extends to the germ field.** Every nonnegative element of `R(ε)` maps to a
square in the (real closed) germ field, since the embedding `ratFuncToGermHom` is order-preserving. -/
theorem germ_isSquare_of_nonneg (p : RatFunc R) (hp : 0 ≤ p) :
    IsSquare (algebraMap (RatFunc R) (SemialgGerm R) p) := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  apply IsRealClosed.nonneg_iff_isSquare.mp
  show (0 : SemialgGerm R) ≤ ratFuncToGermHom p
  calc (0 : SemialgGerm R) = ratFuncToGermHom 0 := (map_zero ratFuncToGermHom).symm
    _ ≤ ratFuncToGermHom p := ratFuncToGermHom_strictMono.monotone hp

/-- **BPR Proposition 3.13.** The germs of semialgebraic continuous functions at the right of the
origin form the real closure of `R(ε)`, equipped with the unique order making `ε` positive and
infinitesimal, where `ε` is sent to the germ of the identity map (`ratFuncToGermHom_εR`).

By Proposition 3.11 the germ field is real closed, by Proposition 2.86 it is algebraic over `R(ε)`
(`instIsAlgebraicSemialgGerm`), and its order extends that of `R(ε)` (`germ_isSquare_of_nonneg`);
hence by uniqueness of the real closure it is `R(ε)`-isomorphic to any real closure `R'` of `R(ε)`. -/
theorem proposition_3_13 {R' : Type*} [Field R'] [IsRealClosed R'] [Algebra (RatFunc R) R']
    (halg' : Algebra.IsAlgebraic (RatFunc R) R')
    (hR'_ext : ∀ p : RatFunc R, 0 ≤ p → IsSquare (algebraMap (RatFunc R) R' p)) :
    Nonempty (SemialgGerm R ≃ₐ[RatFunc R] R') := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  exact realClosure_unique instIsAlgebraicSemialgGerm halg' germ_isSquare_of_nonneg hR'_ext

end Azurite.BPR
