/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGerm
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_3
import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism
import Azurite.BasuPollackRoy.Chapter2.Section2_5.RecipIsSemialgebraic
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Corollary_2_79

/-! # BPR §3.3 — the germs at the right of the origin form a field

We equip `SemialgGerm R` (germs of semialgebraic continuous functions at `0⁺`) with a field
structure. The ring operations are pointwise on a common interval of definition; the inverse uses the
dichotomy that a semialgebraic continuous germ is either zero or eventually nonzero (from the
one-dimensional structure of semialgebraic sets, `semialgebraic_sect_FUOC`). -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### `scalarFun` is a ring homomorphism, and `IsSemialgContinuousOn` is closed under the
ring operations -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem scalarFun_zero : scalarFun (0 : (Fin k → R) → R) = 0 := by
  funext u j; simp [scalarFun, constPt]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem scalarFun_one : scalarFun (1 : (Fin k → R) → R) = 1 := by
  funext u j; simp [scalarFun, constPt]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem scalarFun_add (c d : (Fin k → R) → R) : scalarFun (c + d) = scalarFun c + scalarFun d := by
  funext u j; simp [scalarFun, constPt]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem scalarFun_mul (c d : (Fin k → R) → R) : scalarFun (c * d) = scalarFun c * scalarFun d := by
  funext u j; simp [scalarFun, constPt]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem scalarFun_neg' (c : (Fin k → R) → R) : scalarFun (-c) = -scalarFun c := by
  funext u j; simp [scalarFun, constPt]

/-- `IsSemialgContinuousOn S c` is exactly membership of `scalarFun c` in the ring of semialgebraic
continuous functions on `S`. -/
theorem isSemialgContinuousOn_iff_mem {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    (c : (Fin k → R) → R) :
    IsSemialgContinuousOn S c ↔ scalarFun c ∈ continuousSemialgebraicFunctions hS := Iff.rfl

theorem IsSemialgContinuousOn.add {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {c d : (Fin k → R) → R} (hc : IsSemialgContinuousOn S c) (hd : IsSemialgContinuousOn S d) :
    IsSemialgContinuousOn S (c + d) := by
  rw [isSemialgContinuousOn_iff_mem hS, scalarFun_add]
  exact (continuousSemialgebraicFunctions hS).add_mem hc hd

theorem IsSemialgContinuousOn.mul {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {c d : (Fin k → R) → R} (hc : IsSemialgContinuousOn S c) (hd : IsSemialgContinuousOn S d) :
    IsSemialgContinuousOn S (c * d) := by
  rw [isSemialgContinuousOn_iff_mem hS, scalarFun_mul]
  exact (continuousSemialgebraicFunctions hS).mul_mem hc hd

theorem IsSemialgContinuousOn.neg {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {c : (Fin k → R) → R} (hc : IsSemialgContinuousOn S c) :
    IsSemialgContinuousOn S (-c) := by
  rw [isSemialgContinuousOn_iff_mem hS, scalarFun_neg']
  exact neg_mem hc

theorem isSemialgContinuousOn_zero {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgContinuousOn S (0 : (Fin k → R) → R) := by
  rw [isSemialgContinuousOn_iff_mem hS, scalarFun_zero]; exact zero_mem _

theorem isSemialgContinuousOn_one {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgContinuousOn S (1 : (Fin k → R) → R) := by
  rw [isSemialgContinuousOn_iff_mem hS, scalarFun_one]; exact one_mem _

/-- Semialgebraic continuity is preserved by restricting to a smaller semialgebraic set. -/
theorem IsSemialgContinuousOn.mono {S S' : Set (Fin k → R)} {c : (Fin k → R) → R}
    (hc : IsSemialgContinuousOn S c) (hS' : IsSemialgebraicSet S') (hsub : S' ⊆ S) :
    IsSemialgContinuousOn S' c := by
  refine ⟨?_, hc.2.mono hsub⟩
  have hunivSA : IsSemialgebraicSet (Set.univ : Set (Fin 1 → R)) := by
    have he : (Set.univ : Set (Fin 1 → R))
        = {x | MvPolynomial.eval x (0 : MvPolynomial (Fin 1) R) = 0} := by ext x; simp
    rw [he]; exact IsSemialgebraicSet.eqZero 0
  have heq : funGraph S' (scalarFun c)
      = funGraph S (scalarFun c) ∩ setProd S' (Set.univ : Set (Fin 1 → R)) := by
    ext z
    simp only [mem_funGraph, setProd, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    exact ⟨fun ⟨hz, hf⟩ => ⟨⟨hsub hz, hf⟩, hz⟩, fun ⟨⟨_, hf⟩, hz⟩ => ⟨hz, hf⟩⟩
  rw [IsSemialgebraicFunction, heq]
  exact hc.1.inter (hS'.prod hunivSA)

/-! ### The reciprocal is semialgebraic and continuous where the function is nonzero -/

/-- The reciprocal `x ↦ 1/x` is continuous on `R ∖ {0}` (ε–δ, since our topology carries no
topological-field structure). -/
theorem continuousOn_recipFun : ContinuousOn (recipFun (R := R)) {x : Fin 1 → R | x 0 ≠ 0} := by
  rw [continuousOn_fin_one_iff]
  intro x hx r hr
  have hapos : 0 < |x 0| := abs_pos.mpr hx
  refine ⟨min (|x 0| / 2) (r * |x 0| ^ 2 / 2), lt_min (by positivity) (by positivity),
    fun y hy hyd => ?_⟩
  rw [euclideanNorm_fin_one, Pi.sub_apply] at hyd
  have hx0 : x 0 ≠ 0 := hx
  have hy0 : y 0 ≠ 0 := hy
  have hd2 : |y 0 - x 0| < r * |x 0| ^ 2 / 2 := lt_of_lt_of_le hyd (min_le_right _ _)
  have hyb : |x 0| / 2 < |y 0| := by
    have h := abs_sub_abs_le_abs_sub (x 0) (y 0)
    rw [abs_sub_comm (x 0) (y 0)] at h
    have hd1 : |y 0 - x 0| < |x 0| / 2 := lt_of_lt_of_le hyd (min_le_left _ _)
    linarith
  have hbpos : 0 < |y 0| := by linarith
  have hbx : 0 < |y 0| * |x 0| := mul_pos hbpos hapos
  show |(y 0)⁻¹ - (x 0)⁻¹| < r
  have key : |(y 0)⁻¹ - (x 0)⁻¹| * (|y 0| * |x 0|) = |y 0 - x 0| := by
    rw [← mul_assoc, ← abs_mul, ← abs_mul,
      show ((y 0)⁻¹ - (x 0)⁻¹) * y 0 * x 0 = x 0 - y 0 by field_simp [hx0, hy0],
      abs_sub_comm]
  have hkey : |(y 0)⁻¹ - (x 0)⁻¹| = |y 0 - x 0| / (|y 0| * |x 0|) := by
    rw [eq_div_iff (ne_of_gt hbx)]; exact key
  rw [hkey, div_lt_iff₀ hbx]
  nlinarith [hd2, mul_pos (mul_pos hr hapos) (show (0 : R) < |y 0| - |x 0| / 2 by linarith)]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem scalarFun_inv_eq (c : (Fin k → R) → R) :
    scalarFun (fun u => (c u)⁻¹) = recipFun ∘ scalarFun c := by
  funext u j; simp [scalarFun, constPt, recipFun, Function.comp]

/-- If `c` is semialgebraic continuous on `S` and nonzero throughout `S`, then `1/c` is semialgebraic
continuous on `S`. -/
theorem IsSemialgContinuousOn.inv {S : Set (Fin k → R)}
    {c : (Fin k → R) → R} (hc : IsSemialgContinuousOn S c) (hne : ∀ u ∈ S, c u ≠ 0) :
    IsSemialgContinuousOn S (fun u => (c u)⁻¹) := by
  have hmaps : Set.MapsTo (scalarFun c) S {x : Fin 1 → R | x 0 ≠ 0} := by
    intro u hu; show (scalarFun c u) 0 ≠ 0; simpa [scalarFun, constPt] using hne u hu
  refine ⟨?_, ?_⟩
  · rw [scalarFun_inv_eq]
    exact proposition_2_84 hc.1 recipFun_isSemialgebraicFunction hmaps
  · rw [scalarFun_inv_eq]
    exact continuousOn_recipFun.comp hc.2 hmaps

/-! ### Ring operations on representatives -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem rightNbhd_subset {s t : R} (h : s ≤ t) : rightNbhd s ⊆ rightNbhd t :=
  fun _ hu => ⟨hu.1, lt_of_lt_of_le hu.2 h⟩

/-- Sum of representatives: defined on the smaller interval. -/
def SemialgGermRep.add (f g : SemialgGermRep R) : SemialgGermRep R where
  bound := min f.bound g.bound
  bound_pos := lt_min f.bound_pos g.bound_pos
  toFun := f.toFun + g.toFun
  isSemialgContinuous :=
    IsSemialgContinuousOn.add (isSemialgebraicSet_rightNbhd _)
      (f.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
        (rightNbhd_subset (min_le_left _ _)))
      (g.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
        (rightNbhd_subset (min_le_right _ _)))

/-- Product of representatives. -/
def SemialgGermRep.mul (f g : SemialgGermRep R) : SemialgGermRep R where
  bound := min f.bound g.bound
  bound_pos := lt_min f.bound_pos g.bound_pos
  toFun := f.toFun * g.toFun
  isSemialgContinuous :=
    IsSemialgContinuousOn.mul (isSemialgebraicSet_rightNbhd _)
      (f.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
        (rightNbhd_subset (min_le_left _ _)))
      (g.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
        (rightNbhd_subset (min_le_right _ _)))

/-- Negation of a representative. -/
def SemialgGermRep.neg (f : SemialgGermRep R) : SemialgGermRep R where
  bound := f.bound
  bound_pos := f.bound_pos
  toFun := -f.toFun
  isSemialgContinuous := f.isSemialgContinuous.neg (isSemialgebraicSet_rightNbhd _)

/-- The zero representative. -/
def SemialgGermRep.zero : SemialgGermRep R :=
  ⟨1, one_pos, 0, isSemialgContinuousOn_zero (isSemialgebraicSet_rightNbhd 1)⟩

/-- The one representative. -/
def SemialgGermRep.one : SemialgGermRep R :=
  ⟨1, one_pos, 1, isSemialgContinuousOn_one (isSemialgebraicSet_rightNbhd 1)⟩

@[simp] theorem SemialgGermRep.add_toFun (f g : SemialgGermRep R) :
    (f.add g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem SemialgGermRep.mul_toFun (f g : SemialgGermRep R) :
    (f.mul g).toFun = f.toFun * g.toFun := rfl
@[simp] theorem SemialgGermRep.neg_toFun (f : SemialgGermRep R) :
    (f.neg).toFun = -f.toFun := rfl
@[simp] theorem SemialgGermRep.zero_toFun : (SemialgGermRep.zero : SemialgGermRep R).toFun = 0 := rfl
@[simp] theorem SemialgGermRep.one_toFun : (SemialgGermRep.one : SemialgGermRep R).toFun = 1 := rfl

/-! ### Compatibility of the operations with the germ equivalence -/

theorem SemialgGermRep.add_equiv {f f' g g' : SemialgGermRep R} (hf : f ≈ f') (hg : g ≈ g') :
    f.add g ≈ f'.add g' := by
  obtain ⟨tf, htf, Hf⟩ := hf
  obtain ⟨tg, htg, Hg⟩ := hg
  refine ⟨min tf tg, lt_min htf htg, fun s hs hst => ?_⟩
  simp only [add_toFun, Pi.add_apply]
  rw [Hf s hs (lt_of_lt_of_le hst (min_le_left _ _)), Hg s hs (lt_of_lt_of_le hst (min_le_right _ _))]

theorem SemialgGermRep.mul_equiv {f f' g g' : SemialgGermRep R} (hf : f ≈ f') (hg : g ≈ g') :
    f.mul g ≈ f'.mul g' := by
  obtain ⟨tf, htf, Hf⟩ := hf
  obtain ⟨tg, htg, Hg⟩ := hg
  refine ⟨min tf tg, lt_min htf htg, fun s hs hst => ?_⟩
  simp only [mul_toFun, Pi.mul_apply]
  rw [Hf s hs (lt_of_lt_of_le hst (min_le_left _ _)), Hg s hs (lt_of_lt_of_le hst (min_le_right _ _))]

theorem SemialgGermRep.neg_equiv {f f' : SemialgGermRep R} (hf : f ≈ f') : f.neg ≈ f'.neg := by
  obtain ⟨t, ht, H⟩ := hf
  refine ⟨t, ht, fun s hs hst => ?_⟩
  simp only [neg_toFun, Pi.neg_apply]
  rw [H s hs hst]

/-! ### The germ operations -/

instance : Zero (SemialgGerm R) := ⟨Quotient.mk _ SemialgGermRep.zero⟩
instance : One (SemialgGerm R) := ⟨Quotient.mk _ SemialgGermRep.one⟩
instance : Add (SemialgGerm R) :=
  ⟨Quotient.map₂ SemialgGermRep.add fun _ _ h₁ _ _ h₂ => SemialgGermRep.add_equiv h₁ h₂⟩
instance : Mul (SemialgGerm R) :=
  ⟨Quotient.map₂ SemialgGermRep.mul fun _ _ h₁ _ _ h₂ => SemialgGermRep.mul_equiv h₁ h₂⟩
instance : Neg (SemialgGerm R) :=
  ⟨Quotient.map SemialgGermRep.neg fun _ _ h => SemialgGermRep.neg_equiv h⟩

theorem germ_mk_add (f g : SemialgGermRep R) :
    (Quotient.mk _ f + Quotient.mk _ g : SemialgGerm R) = Quotient.mk _ (f.add g) := rfl
theorem germ_mk_mul (f g : SemialgGermRep R) :
    (Quotient.mk _ f * Quotient.mk _ g : SemialgGerm R) = Quotient.mk _ (f.mul g) := rfl
theorem germ_mk_neg (f : SemialgGermRep R) :
    (-Quotient.mk _ f : SemialgGerm R) = Quotient.mk _ f.neg := rfl

/-! ### The germs form a commutative ring -/

instance : CommRing (SemialgGerm R) where
  add := (· + ·)
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun f g h => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by simp only [SemialgGermRep.add_toFun, Pi.add_apply]; ring⟩
  zero := 0
  zero_add a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.add_toFun, SemialgGermRep.zero_toFun, Pi.add_apply, Pi.zero_apply]
      ring⟩
  add_zero a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.add_toFun, SemialgGermRep.zero_toFun, Pi.add_apply, Pi.zero_apply]
      ring⟩
  add_comm a b := by
    refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by simp only [SemialgGermRep.add_toFun, Pi.add_apply]; ring⟩
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.add_toFun, SemialgGermRep.neg_toFun, SemialgGermRep.zero_toFun,
        Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      ring⟩
  mul := (· * ·)
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun f g h => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by simp only [SemialgGermRep.mul_toFun, Pi.mul_apply]; ring⟩
  one := 1
  one_mul a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.one_toFun, Pi.mul_apply, Pi.one_apply]
      ring⟩
  mul_one a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.one_toFun, Pi.mul_apply, Pi.one_apply]
      ring⟩
  zero_mul a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.zero_toFun, Pi.mul_apply, Pi.zero_apply]
      ring⟩
  mul_zero a := by
    refine Quotient.inductionOn a fun f => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.zero_toFun, Pi.mul_apply, Pi.zero_apply]
      ring⟩
  left_distrib a b c := by
    refine Quotient.inductionOn₃ a b c fun f g h => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.add_toFun, Pi.mul_apply, Pi.add_apply]
      ring⟩
  right_distrib a b c := by
    refine Quotient.inductionOn₃ a b c fun f g h => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by
      simp only [SemialgGermRep.mul_toFun, SemialgGermRep.add_toFun, Pi.mul_apply, Pi.add_apply]
      ring⟩
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ?_
    exact ⟨1, one_pos, fun s _ _ => by simp only [SemialgGermRep.mul_toFun, Pi.mul_apply]; ring⟩

/-! ### Dichotomy: a germ is either zero or eventually nonzero -/

omit [IsRealClosed R] in
/-- An order-connected set in `R` is, near `0⁺`, either contained in some `(0, t)` or disjoint from
some `(0, t)`. -/
theorem ordConnected_dichotomy_at_zero {C : Set R} (hC : C.OrdConnected) :
    (∃ t, 0 < t ∧ Set.Ioo 0 t ⊆ C) ∨ (∃ t, 0 < t ∧ Set.Ioo 0 t ∩ C = ∅) := by
  by_cases hpos : ∃ c ∈ C, 0 < c
  · obtain ⟨c₀, hc₀C, hc₀⟩ := hpos
    by_cases hsub : Set.Ioo 0 c₀ ⊆ C
    · exact Or.inl ⟨c₀, hc₀, hsub⟩
    · obtain ⟨s, hsmem, hsC⟩ := Set.not_subset.mp hsub
      refine Or.inr ⟨s, hsmem.1, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxC⟩
      exact hsC (hC.out hxC hc₀C ⟨le_of_lt hx.2, le_of_lt hsmem.2⟩)
  · push Not at hpos
    refine Or.inr ⟨1, one_pos, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxC⟩
    exact absurd (hpos x hxC) (not_le.mpr hx.1)

omit [IsRealClosed R] in
/-- Finitely many sets each eventually disjoint from `0⁺` are eventually jointly disjoint. -/
theorem exists_common_empty (𝒞 : Finset (Set R))
    (h : ∀ C ∈ 𝒞, ∃ t, 0 < t ∧ Set.Ioo 0 t ∩ C = ∅) :
    ∃ t, 0 < t ∧ ∀ C ∈ 𝒞, Set.Ioo 0 t ∩ C = ∅ := by
  classical
  induction 𝒞 using Finset.induction with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert C 𝒞' hCnotin ih =>
    obtain ⟨t', ht', H'⟩ := ih (fun D hD => h D (Finset.mem_insert_of_mem hD))
    obtain ⟨tC, htC, HC⟩ := h C (Finset.mem_insert_self _ _)
    refine ⟨min t' tC, lt_min ht' htC, fun D hD => ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxD⟩
    rcases Finset.mem_insert.mp hD with rfl | hD'
    · rw [Set.eq_empty_iff_forall_notMem] at HC
      exact HC x ⟨⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩, hxD⟩
    · have hH := H' D hD'
      rw [Set.eq_empty_iff_forall_notMem] at hH
      exact hH x ⟨⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩, hxD⟩

omit [IsRealClosed R] in
/-- A finite union of points and intervals is, near `0⁺`, either contained in some `(0, t)` or
disjoint from some `(0, t)`. -/
theorem FUOC_dichotomy_at_zero {W : Set R} (hW : IsFinUnionOfOrdConnected W) :
    (∃ t, 0 < t ∧ Set.Ioo 0 t ⊆ W) ∨ (∃ t, 0 < t ∧ Set.Ioo 0 t ∩ W = ∅) := by
  obtain ⟨𝒞, hfin, hoc, rfl⟩ := hW
  by_cases hany : ∃ C ∈ 𝒞, ∃ t, 0 < t ∧ Set.Ioo 0 t ⊆ C
  · obtain ⟨C, hC, t, ht, hsub⟩ := hany
    exact Or.inl ⟨t, ht, hsub.trans (Set.subset_sUnion_of_mem hC)⟩
  · right
    have hC_disj : ∀ C ∈ hfin.toFinset, ∃ t, 0 < t ∧ Set.Ioo 0 t ∩ C = ∅ := fun C hC => by
      rw [hfin.mem_toFinset] at hC
      rcases ordConnected_dichotomy_at_zero (hoc C hC) with ⟨t, ht, hsub⟩ | h
      · exact absurd ⟨C, hC, t, ht, hsub⟩ hany
      · exact h
    obtain ⟨t, ht, htall⟩ := exists_common_empty hfin.toFinset hC_disj
    refine ⟨t, ht, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, C, hC, hxC⟩
    have hC' := htall C (hfin.mem_toFinset.mpr hC)
    rw [Set.eq_empty_iff_forall_notMem] at hC'
    exact hC' x ⟨hx, hxC⟩

/-- **A germ is either zero or eventually nonzero.** If a representative `f` is not the zero germ,
then `f` is nonzero on some interval `(0, t)` with `t ≤ f.bound`. -/
theorem SemialgGermRep.eventually_nonzero_of_not_equiv_zero {f : SemialgGermRep R}
    (hf : ¬ f ≈ SemialgGermRep.zero) :
    ∃ t, 0 < t ∧ t ≤ f.bound ∧ ∀ s : R, 0 < s → s < t → f.toFun (constPt s) ≠ 0 := by
  have hA : IsSemialgebraicSet (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) = 0}) :=
    (proposition_2_83 f.isSemialgContinuous.1).2 (IsSemialgebraicSet.eqZero _)
  have hmemZ : ∀ s : R, s ∈ constPt ⁻¹' (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) = 0}) ↔
      (0 < s ∧ s < f.bound) ∧ f.toFun (constPt s) = 0 := by
    intro s
    simp only [Set.mem_preimage, Set.mem_inter_iff, rightNbhd, Set.mem_ofPred_eq,
      MvPolynomial.eval_X, scalarFun, constPt]
  rcases FUOC_dichotomy_at_zero (semialgebraic_sect_FUOC hA) with ⟨t, ht, hsub⟩ | ⟨t, ht, hdisj⟩
  · exact absurd ⟨t, ht, fun s hs hst => by
      have h := ((hmemZ s).mp (hsub ⟨hs, hst⟩)).2
      simpa only [SemialgGermRep.zero_toFun, Pi.zero_apply] using h⟩ hf
  · refine ⟨min t f.bound, lt_min ht f.bound_pos, min_le_right _ _, fun s hs hst hcontra => ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hdisj
    exact hdisj s ⟨⟨hs, lt_of_lt_of_le hst (min_le_left _ _)⟩,
      (hmemZ s).mpr ⟨⟨hs, lt_of_lt_of_le hst (min_le_right _ _)⟩, hcontra⟩⟩

/-! ### Inverse of a germ -/

open Classical in
/-- Inverse of a representative: the zero germ inverts to itself; a nonzero germ inverts to the
reciprocal on an interval where it is nonzero. -/
noncomputable def SemialgGermRep.inv (f : SemialgGermRep R) : SemialgGermRep R :=
  if hf : f ≈ SemialgGermRep.zero then SemialgGermRep.zero
  else
    { bound := (f.eventually_nonzero_of_not_equiv_zero hf).choose
      bound_pos := (f.eventually_nonzero_of_not_equiv_zero hf).choose_spec.1
      toFun := fun u => (f.toFun u)⁻¹
      isSemialgContinuous := by
        have hspec := (f.eventually_nonzero_of_not_equiv_zero hf).choose_spec
        refine (f.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
          (rightNbhd_subset hspec.2.1)).inv ?_
        intro u hu
        have hue : f.toFun u = f.toFun (constPt (u 0)) := by
          congr 1; funext i; rw [Subsingleton.elim i 0]; rfl
        rw [hue]; exact hspec.2.2 (u 0) hu.1 hu.2 }

theorem SemialgGermRep.inv_of_equiv_zero {f : SemialgGermRep R} (hf : f ≈ SemialgGermRep.zero) :
    f.inv = SemialgGermRep.zero := by
  simp only [SemialgGermRep.inv, dite_eq_left hf]

theorem SemialgGermRep.inv_spec_of_not_equiv_zero {f : SemialgGermRep R}
    (hf : ¬ f ≈ SemialgGermRep.zero) :
    (f.inv).toFun = (fun u => (f.toFun u)⁻¹) ∧ 0 < (f.inv).bound ∧
      ∀ s : R, 0 < s → s < (f.inv).bound → f.toFun (constPt s) ≠ 0 := by
  simp only [SemialgGermRep.inv, dite_eq_right hf]
  exact ⟨trivial, (f.eventually_nonzero_of_not_equiv_zero hf).choose_spec.1,
    (f.eventually_nonzero_of_not_equiv_zero hf).choose_spec.2.2⟩

theorem SemialgGermRep.inv_equiv {f g : SemialgGermRep R} (h : f ≈ g) : f.inv ≈ g.inv := by
  by_cases hf : f ≈ SemialgGermRep.zero
  · have hg : g ≈ SemialgGermRep.zero := Setoid.trans (Setoid.symm h) hf
    rw [SemialgGermRep.inv_of_equiv_zero hf, SemialgGermRep.inv_of_equiv_zero hg]
  · have hg : ¬ g ≈ SemialgGermRep.zero := fun hg => hf (Setoid.trans h hg)
    obtain ⟨tf, htf, Hf⟩ := h
    refine ⟨tf, htf, fun s hs hst => ?_⟩
    simp only [(SemialgGermRep.inv_spec_of_not_equiv_zero hf).1,
      (SemialgGermRep.inv_spec_of_not_equiv_zero hg).1]
    rw [Hf s hs hst]

noncomputable instance : Inv (SemialgGerm R) :=
  ⟨Quotient.map SemialgGermRep.inv fun _ _ h => SemialgGermRep.inv_equiv h⟩

theorem germ_mk_inv (f : SemialgGermRep R) :
    (Quotient.mk _ f : SemialgGerm R)⁻¹ = Quotient.mk _ f.inv := rfl

/-! ### The germs form a field -/

noncomputable instance : Field (SemialgGerm R) where
  __ := (inferInstance : CommRing (SemialgGerm R))
  inv := (·⁻¹)
  qsmul := _
  nnqsmul := _
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    obtain ⟨t, ht, H⟩ := Quotient.exact h
    have := H (t / 2) (by linarith) (by linarith)
    simp only [SemialgGermRep.zero_toFun, SemialgGermRep.one_toFun, Pi.zero_apply,
      Pi.one_apply] at this
    exact zero_ne_one this
  mul_inv_cancel a ha := by
    induction a using Quotient.inductionOn with
    | _ f =>
      have hf : ¬ f ≈ SemialgGermRep.zero := fun h => ha (Quotient.sound h)
      obtain ⟨htf, hbpos, hne⟩ := SemialgGermRep.inv_spec_of_not_equiv_zero hf
      rw [germ_mk_inv, germ_mk_mul]
      refine Quotient.sound ⟨(f.inv).bound, hbpos, fun s hs hst => ?_⟩
      simp only [SemialgGermRep.mul_toFun, Pi.mul_apply, htf, SemialgGermRep.one_toFun, Pi.one_apply]
      exact mul_inv_cancel₀ (hne s hs hst)
  inv_zero := by
    show (Quotient.mk _ SemialgGermRep.zero : SemialgGerm R)⁻¹ = Quotient.mk _ SemialgGermRep.zero
    rw [germ_mk_inv, SemialgGermRep.inv_of_equiv_zero (Setoid.refl _)]

end Azurite.BPR
