/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Exercise_3_1
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4
import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxLimit

/-! # BPR §3.1, Proposition 3.5 — continuity via the Puiseux limit

A semialgebraic `f : S → R^ℓ` is continuous iff for every `x ∈ S` and every `y ∈ Ext(S, R⟨ε⟩)` with
`lim_ε y = x`, one has `lim_ε (Ext(f) y) = f(x)`. Both directions transfer the ε–δ condition between
`R` and `R⟨ε⟩` (Tarski–Seidenberg), using a *real* modulus of continuity `b` so that infinitesimal
closeness is preserved. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R']
  [IsRealClosed R'] in
/-- The embedding commutes with `Fin.append`. -/
theorem algebraMap_comp_append {k ℓ : ℕ} (x : Fin k → R) (y : Fin ℓ → R) :
    algebraMap R R' ∘ Fin.append x y
      = Fin.append (algebraMap R R' ∘ x) (algebraMap R R' ∘ y) := by
  funext i
  induction i using Fin.addCases with
  | left a => simp [Fin.append_left]
  | right b => simp [Fin.append_right]

/-- **`Ext(f)` fixes embedded `R`-points**: `Ext(f)(x) = f(x)` for `x ∈ S` (via the embedding). -/
theorem ext_fun_algebraMap {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → R') → (Fin ℓ → R')} (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf = funGraph (extension (R' := R') S hS) f')
    {x : Fin k → R} (hx : x ∈ S) :
    f' (algebraMap R R' ∘ x) = algebraMap R R' ∘ (f x) := by
  have hmem : Fin.append x (f x) ∈ funGraph S f := (append_mem_funGraph S f x (f x)).mpr ⟨hx, rfl⟩
  have hext : (algebraMap R R' ∘ Fin.append x (f x)) ∈ extension (R' := R') (funGraph S f) hf :=
    (mem_ext_algebraMap hf _).mpr hmem
  rw [hgraph, algebraMap_comp_append] at hext
  exact ((append_mem_funGraph (extension (R' := R') S hS) f' _ _).mp hext).2.symm

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R']
  [IsRealClosed R'] in
theorem map_ballPoly {k : ℕ} (x : Fin k → R) (r : R) :
    MvPolynomial.map (algebraMap R R') (ballPoly x r)
      = ballPoly (algebraMap R R' ∘ x) (algebraMap R R' r) := by
  simp only [ballPoly, map_sub, map_sum, map_pow, MvPolynomial.map_X, MvPolynomial.map_C,
    Function.comp_apply]

/-- **`Ext` of an open ball** (with embedded centre and radius). -/
theorem ext_openBall {k : ℕ} (x : Fin k → R) (r : R) :
    extension (R' := R') (openBall x r) (isSemialgebraicSet_openBall x r)
      = openBall (algebraMap R R' ∘ x) (algebraMap R R' r) := by
  have hΦ : openBall x r = (Formula.ltZeroO (ballPoly x r)).realization (C := R) := by
    rw [Formula.realization_ltZeroO]; ext y
    simp only [mem_openBall, Set.mem_ofPred_eq, aeval_eq_eval_self, eval_ballPoly, sub_lt_zero]
  rw [ext_eq _ hΦ, Formula.realization_ltZeroO]
  ext y'
  simp only [mem_openBall, Set.mem_ofPred_eq,
    show aeval y' (ballPoly x r) = eval y' (ballPoly (algebraMap R R' ∘ x) (algebraMap R R' r)) from by
      rw [aeval_def, ← eval_map, map_ballPoly],
    eval_ballPoly, sub_lt_zero]

/-- **The granular Tarski–Seidenberg transfer of an `(a, b)`-modulus.** If `f` is `a`-close on the
`b`-ball around `x ∈ S` (real `a, b`), then `Ext(f)` is `a`-close on the `b`-ball around the embedded
`x` — preserving the *real* radius `b`, which is what makes infinitesimal closeness transfer. -/
theorem transfer_modulus {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → R') → (Fin ℓ → R')} (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf = funGraph (extension (R' := R') S hS) f')
    {x : Fin k → R} (a b : R)
    (hcond : ∀ y ∈ S, euclideanNormSq (y - x) < b ^ 2 → euclideanNormSq (f y - f x) < a ^ 2) :
    ∀ y' ∈ extension (R' := R') S hS,
      euclideanNormSq (y' - algebraMap R R' ∘ x) < (algebraMap R R' b) ^ 2 →
        euclideanNormSq (f' y' - algebraMap R R' ∘ (f x)) < (algebraMap R R' a) ^ 2 := by
  have hcoBallS : IsSemialgebraicSet ((openBall (f x) a)ᶜ) := (isSemialgebraicSet_openBall (f x) a).compl
  have hPreS : IsSemialgebraicSet {y : Fin k → R | y ∈ S ∧ f y ∈ (openBall (f x) a)ᶜ} :=
    (proposition_2_83 hf).2 hcoBallS
  have hBadS : IsSemialgebraicSet
      ({y : Fin k → R | y ∈ S ∧ f y ∈ (openBall (f x) a)ᶜ} ∩ openBall x b) :=
    hPreS.inter (isSemialgebraicSet_openBall x b)
  have hempty : {y : Fin k → R | y ∈ S ∧ f y ∈ (openBall (f x) a)ᶜ} ∩ openBall x b = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨hyS, hyf⟩, hyb⟩
    rw [Set.mem_compl_iff, mem_openBall] at hyf
    rw [mem_openBall] at hyb
    exact hyf (hcond y hyS hyb)
  have hext : extension (R' := R') _ hBadS
      = {y' : Fin k → R' | y' ∈ extension (R' := R') S hS ∧
          f' y' ∈ (openBall (algebraMap R R' ∘ (f x)) (algebraMap R R' a))ᶜ}
        ∩ openBall (algebraMap R R' ∘ x) (algebraMap R R' b) := by
    rw [ext_inter hPreS (isSemialgebraicSet_openBall x b), ext_openBall,
      exercise_2_17b hS hcoBallS hf hgraph hPreS,
      ext_compl (isSemialgebraicSet_openBall (f x) a), ext_openBall]
  rw [(ext_eq_empty_iff hBadS).mpr hempty] at hext
  intro y' hy' hball
  by_contra hcon
  rw [not_lt] at hcon
  refine absurd (show y' ∈ (∅ : Set (Fin k → R')) from ?_) (Set.notMem_empty y')
  rw [hext]
  exact ⟨⟨hy', by rw [Set.mem_compl_iff, mem_openBall]; exact not_lt.mpr hcon⟩,
    by rw [mem_openBall]; exact hball⟩

/-- `y : R'^k` is **infinitesimally close** to the embedded `x : R^k`: its squared distance to
`x` is below `(b)²` for every real `b > 0` (i.e. `lim_ε y = x`). -/
def InfClose {k : ℕ} (y : Fin k → R') (x : Fin k → R) : Prop :=
  ∀ b : R, 0 < b → euclideanNormSq (y - algebraMap R R' ∘ x) < (algebraMap R R' b) ^ 2

/-- **Proposition 3.5, ⟹.** If `f` is continuous, then `Ext(f)` maps infinitesimally-close points to
infinitesimally-close points. -/
theorem prop_3_5_forward {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → R') → (Fin ℓ → R')} (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf = funGraph (extension (R' := R') S hS) f')
    (hcont : ContinuousOn f S) {x : Fin k → R} (hx : x ∈ S) {y : Fin k → R'}
    (hyExt : y ∈ extension (R' := R') S hS) (hclose : InfClose y x) : InfClose (f' y) (f x) := by
  intro a ha
  rw [continuousOn_iff_ball] at hcont
  obtain ⟨δ, hδ, hδcont⟩ := hcont x hx a ha
  have hcond : ∀ z ∈ S, euclideanNormSq (z - x) < δ ^ 2 → euclideanNormSq (f z - f x) < a ^ 2 :=
    fun z hz hzb => (normSq_lt_sq_iff ha).mpr (hδcont z hz ((normSq_lt_sq_iff hδ).mp hzb))
  exact transfer_modulus hS hf hgraph a δ hcond y hyExt (hclose δ hδ)

/-! ### Backward direction

For the converse we build a *parametrized* bad set in `R^{1+k}` whose first coordinate is the radius
`b`: discontinuity at `x` (real tolerance `a`) says every positive `b` has a witness. Projecting out
`y` and transferring (Tarski–Seidenberg) yields a witness over `R⟨ε⟩` for the infinitesimal radius
`ε`, contradicting the limit hypothesis. -/

/-- **Parametrized ball polynomial** over `Fin (1 + k)`: coordinate `0` is the radius `b`, the last
`k` coordinates are the point `y`; its value is `‖y − x‖² − b²`. -/
noncomputable def varBallPoly {K : Type*} [CommRing K] {k : ℕ} (x : Fin k → K) :
    MvPolynomial (Fin (1 + k)) K :=
  (∑ i : Fin k, (X (Fin.natAdd 1 i) - C (x i)) ^ 2) - X (Fin.castAdd k (0 : Fin 1)) ^ 2

theorem eval_varBallPoly {K : Type*} [Field K] {k : ℕ} (x : Fin k → K) (w : Fin (1 + k) → K) :
    eval w (varBallPoly x)
      = euclideanNormSq ((w ∘ Fin.natAdd 1) - x) - (w (Fin.castAdd k (0 : Fin 1))) ^ 2 := by
  simp only [varBallPoly, euclideanNormSq, map_sub, map_sum, map_pow, eval_X, eval_C,
    Function.comp_apply, Pi.sub_apply]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R']
  [IsStrictOrderedRing R'] [IsRealClosed R'] in
theorem map_varBallPoly {k : ℕ} (x : Fin k → R) :
    MvPolynomial.map (algebraMap R R') (varBallPoly x) = varBallPoly (algebraMap R R' ∘ x) := by
  simp only [varBallPoly, map_sub, map_sum, map_pow, MvPolynomial.map_X, MvPolynomial.map_C,
    Function.comp_apply]

/-- **`Ext` of a `> 0` polynomial locus** (coefficients embedded). -/
theorem ext_evalPos {n : ℕ} (P : MvPolynomial (Fin n) R) :
    extension (R' := R') {w : Fin n → R | eval w P > 0} (IsSemialgebraicSet.gtZero P)
      = {w' : Fin n → R' | eval w' (MvPolynomial.map (algebraMap R R') P) > 0} := by
  have hΦ : {w : Fin n → R | eval w P > 0} = (Formula.gtZeroO P).realization (C := R) := by
    rw [Formula.realization_gtZeroO]; ext w
    simp only [Set.mem_ofPred_eq, aeval_eq_eval_self, gt_iff_lt]
  rw [ext_eq _ hΦ, Formula.realization_gtZeroO]
  ext w'
  simp only [Set.mem_ofPred_eq, gt_iff_lt,
    show aeval w' P = eval w' (MvPolynomial.map (algebraMap R R') P) from by rw [aeval_def, ← eval_map]]

/-- **`Ext` of a `< 0` polynomial locus** (coefficients embedded). -/
theorem ext_evalNeg {n : ℕ} (P : MvPolynomial (Fin n) R) :
    extension (R' := R') {w : Fin n → R | eval w P < 0} (IsSemialgebraicSet.ltZero P)
      = {w' : Fin n → R' | eval w' (MvPolynomial.map (algebraMap R R') P) < 0} := by
  have hΦ : {w : Fin n → R | eval w P < 0} = (Formula.ltZeroO P).realization (C := R) := by
    rw [Formula.realization_ltZeroO]; ext w
    simp only [Set.mem_ofPred_eq, aeval_eq_eval_self]
  rw [ext_eq _ hΦ, Formula.realization_ltZeroO]
  ext w'
  simp only [Set.mem_ofPred_eq,
    show aeval w' P = eval w' (MvPolynomial.map (algebraMap R R') P) from by rw [aeval_def, ← eval_map]]

/-- **Proposition 3.5, ⟸.** If `Ext(f)` preserves infinitesimal closeness at every embedded point,
then `f` is continuous. The witness is the infinitesimal radius `ε ∈ R⟨ε⟩`. -/
theorem prop_3_5_backward {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → algebraicPuiseux R) → (Fin ℓ → algebraicPuiseux R)}
    (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := algebraicPuiseux R) (funGraph S f) hf
      = funGraph (extension (R' := algebraicPuiseux R) S hS) f')
    (hlim : ∀ x ∈ S, ∀ y ∈ extension (R' := algebraicPuiseux R) S hS,
      InfClose (R' := algebraicPuiseux R) y x → InfClose (R' := algebraicPuiseux R) (f' y) (f x)) :
    ContinuousOn f S := by
  rw [continuousOn_iff_ball]
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, a, ha, hdisc⟩ := hcon
  -- Squared form of the discontinuity at `x` with real tolerance `a`.
  have hdiscSq : ∀ b : R, 0 < b →
      ∃ y, y ∈ S ∧ euclideanNormSq (y - x) < b ^ 2 ∧ a ^ 2 ≤ euclideanNormSq (f y - f x) := by
    intro b hb
    obtain ⟨y, hyS, hyn, hyf⟩ := hdisc b hb
    exact ⟨y, hyS, (normSq_lt_sq_iff hb).mpr hyn, (sq_le_normSq_iff ha).mpr hyf⟩
  -- The point-set part `CoF = {y ∈ S | a² ≤ ‖f y − f x‖²}`.
  have hcoBall : IsSemialgebraicSet ((openBall (f x) a)ᶜ) :=
    (isSemialgebraicSet_openBall (f x) a).compl
  set CoF : Set (Fin k → R) := {y : Fin k → R | y ∈ S ∧ f y ∈ (openBall (f x) a)ᶜ} with hCoFdef
  have hCoF : IsSemialgebraicSet CoF := (proposition_2_83 hf).2 hcoBall
  -- The parametrized bad set in `R^{1+k}`: ball condition ∧ `y ∈ CoF`.
  set Pball : Set (Fin (1 + k) → R) := {w | eval w (varBallPoly x) < 0} with hPballdef
  set Pcyl : Set (Fin (1 + k) → R) := {w | (w ∘ Fin.natAdd 1) ∈ CoF} with hPcyldef
  have hPball : IsSemialgebraicSet Pball := IsSemialgebraicSet.ltZero _
  have hPcyl : IsSemialgebraicSet Pcyl := hCoF.comap (Fin.natAdd 1)
  set Bad : Set (Fin (1 + k) → R) := Pball ∩ Pcyl with hBaddef
  have hBad : IsSemialgebraicSet Bad := hPball.inter hPcyl
  set ExB : Set (Fin 1 → R) := {p | ∃ y : Fin k → R, Fin.append p y ∈ Bad} with hExBdef
  have hExB : IsSemialgebraicSet ExB := IsSemialgebraicSet.exists_append_right hBad
  -- Discontinuity: every positive radius `b` lies in the projection `ExB`.
  have hsub : ∀ p : Fin 1 → R, 0 < p 0 → p ∈ ExB := by
    intro p hp
    obtain ⟨y, hyS, hball, hff⟩ := hdiscSq (p 0) hp
    have hc : Fin.append p y (Fin.castAdd k (0 : Fin 1)) = p 0 :=
      congrFun (append_comp_castAdd p y) 0
    refine ⟨y, ?_, ?_⟩
    · rw [hPballdef, Set.mem_ofPred_eq, eval_varBallPoly, append_comp_natAdd, hc]
      linarith [hball]
    · rw [hPcyldef, Set.mem_ofPred_eq, append_comp_natAdd, hCoFdef, Set.mem_ofPred_eq,
        Set.mem_compl_iff, mem_openBall, not_lt]
      exact ⟨hyS, hff⟩
  -- Hence `{p | 0 < p 0} ∩ ExBᶜ = ∅`.
  set posSet : Set (Fin 1 → R) := {p | eval p (X (0 : Fin 1)) > 0} with hposdef
  have hpos : IsSemialgebraicSet posSet := IsSemialgebraicSet.gtZero _
  have hgapEmpty : posSet ∩ ExBᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp, hpn⟩
    rw [hposdef, Set.mem_ofPred_eq, eval_X, gt_iff_lt] at hp
    exact hpn (hsub p hp)
  -- Transfer the emptiness to `R⟨ε⟩` (all extension-equalities are stated as `have`s with the
  -- local set names on the left, so `rw` matches without disturbing the proof arguments).
  have hgapExt : (extension (R' := algebraicPuiseux R) posSet hpos)
      ∩ (extension (R' := algebraicPuiseux R) ExB hExB)ᶜ = ∅ := by
    rw [← ext_compl hExB, ← ext_inter hpos hExB.compl]
    exact (ext_eq_empty_iff (R' := algebraicPuiseux R) (hpos.inter hExB.compl)).mpr hgapEmpty
  have hposExt : extension (R' := algebraicPuiseux R) posSet hpos
      = {p' : Fin 1 → algebraicPuiseux R | 0 < p' 0} := by
    rw [ext_evalPos (R' := algebraicPuiseux R) (X (0 : Fin 1))]; ext p'
    simp only [Set.mem_ofPred_eq, MvPolynomial.map_X, eval_X, gt_iff_lt]
  have hExBExt : extension (R' := algebraicPuiseux R) ExB hExB
      = {p' : Fin 1 → algebraicPuiseux R |
          ∃ y' : Fin k → algebraicPuiseux R,
            Fin.append p' y' ∈ extension (R' := algebraicPuiseux R) Bad hBad} :=
    ext_exists_append (R' := algebraicPuiseux R) hBad hExB
  rw [hposExt, hExBExt] at hgapExt
  -- So every positive `R⟨ε⟩`-radius has a witness; apply it to `ε`.
  have hAll : ∀ p' : Fin 1 → algebraicPuiseux R, 0 < p' 0 →
      ∃ y' : Fin k → algebraicPuiseux R,
        Fin.append p' y' ∈ extension (R' := algebraicPuiseux R) Bad hBad := by
    intro p' hp'
    by_contra hno
    refine absurd (show p' ∈ (∅ : Set (Fin 1 → algebraicPuiseux R)) from ?_) (Set.notMem_empty p')
    rw [← hgapExt]; exact ⟨hp', hno⟩
  obtain ⟨y', hy'⟩ := hAll (fun _ => epsAP R) (by simpa using epsAP_pos (R := R))
  -- Unpack the witness across the extension.
  have hBadExt : extension (R' := algebraicPuiseux R) Bad hBad
      = extension (R' := algebraicPuiseux R) Pball hPball
        ∩ extension (R' := algebraicPuiseux R) Pcyl hPcyl :=
    ext_inter hPball hPcyl
  rw [hBadExt] at hy'
  obtain ⟨hy'ball, hy'cyl⟩ := hy'
  have hc' : Fin.append (fun _ => epsAP R) y' (Fin.castAdd k (0 : Fin 1)) = epsAP R :=
    congrFun (append_comp_castAdd (fun _ => epsAP R) y') 0
  have hballExt : extension (R' := algebraicPuiseux R) Pball hPball
      = {w' : Fin (1 + k) → algebraicPuiseux R |
          eval w' (MvPolynomial.map (algebraMap R (algebraicPuiseux R)) (varBallPoly x)) < 0} :=
    ext_evalNeg (R' := algebraicPuiseux R) (varBallPoly x)
  rw [hballExt, Set.mem_ofPred_eq, map_varBallPoly, eval_varBallPoly, append_comp_natAdd, hc',
    sub_neg] at hy'ball
  have hcylExt : extension (R' := algebraicPuiseux R) Pcyl hPcyl
      = {w' : Fin (1 + k) → algebraicPuiseux R |
          (w' ∘ Fin.natAdd 1) ∈ extension (R' := algebraicPuiseux R) CoF hCoF} :=
    ext_comap (R' := algebraicPuiseux R) (Fin.natAdd 1) (Fin.natAdd_injective k 1) hCoF
  have hCoFExt : extension (R' := algebraicPuiseux R) CoF hCoF
      = {y' : Fin k → algebraicPuiseux R | y' ∈ extension (R' := algebraicPuiseux R) S hS
          ∧ f' y' ∈ extension (R' := algebraicPuiseux R) ((openBall (f x) a)ᶜ)
              (isSemialgebraicSet_openBall (f x) a).compl} :=
    exercise_2_17b (R' := algebraicPuiseux R) hS (isSemialgebraicSet_openBall (f x) a).compl hf
      hgraph hCoF
  rw [hcylExt, Set.mem_ofPred_eq, append_comp_natAdd, hCoFExt, Set.mem_ofPred_eq,
    ext_compl (R' := algebraicPuiseux R) (isSemialgebraicSet_openBall (f x) a),
    ext_openBall (R' := algebraicPuiseux R) (f x) a, Set.mem_compl_iff, mem_openBall,
    not_lt] at hy'cyl
  obtain ⟨hy'S, hy'far⟩ := hy'cyl
  -- `y'` is infinitesimally close to `x` but `f' y'` is `a`-far from `f x`: contradiction.
  have hInf : InfClose (R' := algebraicPuiseux R) y' x := by
    intro b hb
    calc euclideanNormSq (y' - algebraMap R (algebraicPuiseux R) ∘ x) < (epsAP R) ^ 2 := hy'ball
      _ < (algebraMap R (algebraicPuiseux R) b) ^ 2 := by
        nlinarith [epsAP_pos (R := R), epsAP_lt_algebraMap (R := R) hb]
  exact absurd (hlim x hx y' hy'S hInf a ha) (not_lt.mpr hy'far)

/-- **BPR Proposition 3.5.** A semialgebraic total `f` with semialgebraic domain `S` is continuous
iff `Ext(f)` over `R⟨ε⟩` sends every point infinitesimally close to an embedded `x ∈ S` to a point
infinitesimally close to `f(x)`. -/
theorem proposition_3_5 {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → algebraicPuiseux R) → (Fin ℓ → algebraicPuiseux R)}
    (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := algebraicPuiseux R) (funGraph S f) hf
      = funGraph (extension (R' := algebraicPuiseux R) S hS) f') :
    ContinuousOn f S ↔ ∀ x ∈ S, ∀ y ∈ extension (R' := algebraicPuiseux R) S hS,
      InfClose (R' := algebraicPuiseux R) y x → InfClose (R' := algebraicPuiseux R) (f' y) (f x) :=
  ⟨fun hcont _ hx _ hyExt hclose => prop_3_5_forward hS hf hgraph hcont hx hyExt hclose,
    fun hlim => prop_3_5_backward hS hf hgraph hlim⟩

end Azurite.BPR
