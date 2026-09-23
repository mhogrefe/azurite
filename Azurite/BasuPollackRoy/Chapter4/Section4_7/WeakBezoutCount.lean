/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezout
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_9
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19

/-!
# BPR §4.7, Proposition 4.106: the fiber-cardinality route

This file develops the **fiber-cardinality** route to the weak Bézout bound, which bounds the number
of zeros without constructing global path-lifts of individual zeros. The idea is to bound, along
the deformation path `γ : [0,1] → ℙ₁(C)` (from `WeakBezout.exists_gammaPath_off_delta`), the *number*
of distinct common projective zeros of the pencil `S₍γ(t)₎`, using semialgebraic connectedness of the
parameter interval `(0,1]`.

For `m : ℕ` we consider the parameter set

`Pm m = {w : Fin 1 → R | w 0 ∈ (0,1] ∧ S₍γ(w 0)₎ has ≥ m distinct common projective zeros}`,

and the program is:

1. `Pm m` is semialgebraic (the existential "∃ m distinct common zeros" is a projection of a
   semialgebraic condition);
2. `Pm m` is open in `(0,1]` (each non-singular zero persists locally by the IFT);
3. `Pm m` is closed in `(0,1]` (curve selection + projective completeness: the `m` distinct zeros
   converge, and stay distinct because off `Δ` they are non-singular hence isolated);
4. `(0,1]` is semialgebraically connected, so a clopen subset is `∅` or everything;
5. the endpoint `(0:1)` has exactly `∏ dᵢ` zeros, so `Pm (∏dᵢ + 1) = ∅` — no `t ∈ (0,1]` carries more
   than `∏ dᵢ` distinct zeros;
6. finite subsets of `{x | IsNonsingularProjectiveZero P x}` inject (via finitely many local IFT
   continuations near `(1:0)`) into the zeros of `S₍γ(t₀)₎` for a common small `t₀`, bounding the
   `ncard`.

Step (1) is the main infrastructure step.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

open scoped Azurite.BPR

/-- The common projective zeros of the diagonal system `S₍₀:₁₎` form a finite set of cardinality
`d₁ ⋯ d_k` (every common zero is non-singular, by `diagSystem_common_zero_isNonsingular`, and the
non-singular zeros number `d₁ ⋯ d_k`, by `diagSystem_nonsingularZero_ncard`). -/
theorem diagSystem_commonZero_eq_nonsingular (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) :
    {x : complexProjectiveSpace R k | ∀ i, aeval x.rep (diagSystem (R := R) d i) = 0}
      = {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero (diagSystem d) x} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · exact fun hx => diagSystem_common_zero_isNonsingular d hd x hx
  · exact fun hx => hx.1

set_option linter.unusedSectionVars false in
/-- A finite indexed union of semialgebraic sets is semialgebraic. -/
theorem isSemialgebraicSet_iUnion_fintype {ι : Type*} [Fintype ι] {p : ℕ}
    {S : ι → Set (Fin p → R)} (h : ∀ i, IsSemialgebraicSet (S i)) :
    IsSemialgebraicSet (⋃ i, S i) := by
  classical
  have hbi : (⋃ i, S i) = ⋃ i ∈ (Finset.univ : Finset ι), S i := by
    simp only [Finset.mem_univ, Set.iUnion_true]
  rw [hbi]
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty];
             exact isSemialgebraicSet_empty
  | @insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a).union ih

/-! ### Closure of `IsSemialgebraicSetRP` under intersection -/

set_option linter.unusedSectionVars false in
/-- `IsSemialgebraicSetRP` is closed under intersection (mirror of `IsSemialgebraicSetRP.union`). -/
theorem IsSemialgebraicSetRP.inter {k p : ℕ}
    {S T : Set ((Fin p → R) × complexProjectiveSpace R k)}
    (hS : IsSemialgebraicSetRP S) (hT : IsSemialgebraicSetRP T) :
    IsSemialgebraicSetRP (S ∩ T) := by
  intro i
  have heq : {w : Fin (p + (k + k)) → R |
        (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ S ∩ T}
      = {w : Fin (p + (k + k)) → R |
          (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ S}
        ∩ {w | (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ T} := by
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [heq]
  exact (hS i).inter (hT i)

set_option linter.unusedSectionVars false in
/-- **Projecting the projective factor out of an `IsSemialgebraicSetRP` set.** If `T ⊆ Rᵖ × ℙ_k(C)`
is semialgebraic (in the mixed sense), then its projection onto `Rᵖ`, `{w | ∃ p, (w, p) ∈ T}`, is a
semialgebraic subset of `Rᵖ`. The projective point ranges over a *finite* chart cover; on each chart
`i` the condition becomes the existence of a realified chart coordinate `z ∈ R^{2k}` with
`(w, φᵢ(realEquiv⁻¹ z)) ∈ T`, which is exactly the `exists_append_right` projection of the chart-`i`
defining set of `IsSemialgebraicSetRP T`. -/
theorem IsSemialgebraicSetRP.proj {k p : ℕ}
    {T : Set ((Fin p → R) × complexProjectiveSpace R k)} (hT : IsSemialgebraicSetRP T) :
    IsSemialgebraicSet {w : Fin p → R | ∃ q : complexProjectiveSpace R k, (w, q) ∈ T} := by
  classical
  -- Rewrite the projection as a finite union over the charts of the per-chart projections.
  have hcover : {w : Fin p → R | ∃ q : complexProjectiveSpace R k, (w, q) ∈ T}
      = ⋃ i : Fin (k + 1),
          {w : Fin p → R | ∃ z : Fin k → Ri R, (w, chartMap i z) ∈ T} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      -- `q` lies in some chart `i`.
      obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), q.rep i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact q.rep_nonzero (funext fun i => hcon i)
      refine ⟨i, chartInv i q, ?_⟩
      rw [chartMap_chartInv i q hi]; exact hq
    · rintro ⟨i, z, hz⟩; exact ⟨chartMap i z, hz⟩
  rw [hcover]
  refine isSemialgebraicSet_iUnion_fintype (fun i => ?_)
  -- Per chart `i`: the projection of the chart-`i` defining set of `IsSemialgebraicSetRP T`.
  have hRP := hT i
  -- `hRP : IsSemialgebraicSet {u : Fin (p+(k+k)) → R | (u∘castAdd, chartMap i (realEquiv.symm (u∘natAdd))) ∈ T}`
  have hproj := IsSemialgebraicSet.exists_append_right (k := p) (ℓ := k + k) hRP
  -- Massage the projection to the chart-`i` slice of the cover.
  convert hproj using 1
  ext w
  simp only [Set.mem_ofPred_eq]
  have hcappend : ∀ v : Fin (k + k) → R,
      (Fin.append w v ∘ Fin.castAdd (k + k) : Fin p → R) = w := by
    intro v; funext a; rw [Function.comp_apply, Fin.append_left]
  have hnappend : ∀ v : Fin (k + k) → R,
      (Fin.append w v ∘ Fin.natAdd p : Fin (k + k) → R) = v := by
    intro v; funext a; rw [Function.comp_apply, Fin.append_right]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨realEquiv z, ?_⟩
    rw [hcappend, hnappend, Equiv.symm_apply_apply]; exact hz
  · rintro ⟨v, hv⟩
    rw [hcappend] at hv
    exact ⟨realEquiv.symm (Fin.append w v ∘ Fin.natAdd p), hv⟩

set_option linter.unusedSectionVars false in
/-- **Cylinder over a semialgebraic base is `IsSemialgebraicSetRP`.** If `S ⊆ Rᵖ` is semialgebraic,
then the cylinder `{(w, p) | w ∈ S}` (no constraint on the projective coordinate) is semialgebraic in
the mixed real–projective sense. -/
theorem isSemialgebraicSetRP_cylinder {k p : ℕ} {S : Set (Fin p → R)}
    (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSetRP {tp : (Fin p → R) × complexProjectiveSpace R k | tp.1 ∈ S} := by
  intro i
  have heq : {w : Fin (p + (k + k)) → R |
        (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p)))
          ∈ {tp : (Fin p → R) × complexProjectiveSpace R k | tp.1 ∈ S}}
      = {w : Fin (p + (k + k)) → R | w ∘ Fin.castAdd (k + k) ∈ S} := by
    ext w; simp only [Set.mem_ofPred_eq]
  rw [heq]
  exact IsSemialgebraicSet.comap (Fin.castAdd (k + k)) hS

/-! ### The parameter interval `(0,1]` -/

/-- The parameter interval `(0,1] ⊆ R`, packaged as a line-set in `Fin 1 → R`. This is the domain on
which the deformation `γ` is followed (the closed endpoint `t = 1` carries the diagonal system; the
open endpoint `t = 0` is the original system `(1:0)`, which lies *outside* the set since `γ(0) = (1:0)`
may itself be in `Δ`). -/
def intervalSet : Set (Fin 1 → R) := {w : Fin 1 → R | w 0 ∈ Set.Ioc (0 : R) 1}

set_option linter.unusedSectionVars false in
theorem mem_intervalSet {w : Fin 1 → R} : w ∈ intervalSet (R := R) ↔ 0 < w 0 ∧ w 0 ≤ 1 :=
  Set.mem_Ioc

set_option linter.unusedSectionVars false in
/-- The parameter interval `(0,1]` is a semialgebraic subset of `Fin 1 → R`: it is the locus
`X₀ > 0 ∧ 1 - X₀ ≥ 0`. -/
theorem isSemialgebraicSet_intervalSet :
    IsSemialgebraicSet (intervalSet (R := R)) := by
  have h : intervalSet (R := R)
      = {x | MvPolynomial.eval x (X 0 : MvPolynomial (Fin 1) R) > 0}
        ∩ {x | MvPolynomial.eval x (1 - X 0 : MvPolynomial (Fin 1) R) ≥ 0} := by
    ext w
    simp only [intervalSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioc, map_sub, eval_X,
      map_one, gt_iff_lt, ge_iff_le, sub_nonneg]
  rw [h]
  exact (IsSemialgebraicSet.pos_locus _).inter (IsSemialgebraicSet.geZero _)

set_option linter.unusedSectionVars false in
/-- The parameter interval `(0,1]` is semialgebraically connected (it is order-connected). -/
theorem isSemialgebraicallyConnected_intervalSet :
    IsSemialgebraicallyConnected (intervalSet (R := R)) :=
  isSemialgebraicallyConnected_interval Set.ordConnected_Ioc

/-! ### The "at least `m` distinct zeros" parameter set `Pm` -/

/-- The predicate "the pencil `S₍γ(t)₎` has at least `m` distinct common projective zeros": there is
an injection `ys : Fin m → ℙ_k(C)` all of whose values are common projective zeros of the pencil at
the parameter `γ(t)`. The parameter `γ(t)` enters through its homogeneous coordinates
`((γ t).rep 0, (γ t).rep 1)`; since `homotopyPoly P d λ µ i` is linear in `(λ, µ)`, the common-zero
condition is independent of the chosen representative. -/
def AtLeastZeros (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) (m : ℕ) : Prop :=
  ∃ ys : Fin m → complexProjectiveSpace R k, Function.Injective ys ∧
    ∀ a i, aeval (ys a).rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0

/-- The parameter set `Pm m`: those `t ∈ (0,1]` for which `S₍γ(t)₎` has at least `m` distinct common
projective zeros. -/
def Pm (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) (m : ℕ) : Set (Fin 1 → R) :=
  {w : Fin 1 → R | w 0 ∈ Set.Ioc (0 : R) 1 ∧ AtLeastZeros P d (γ w) m}

set_option linter.unusedSectionVars false in
theorem mem_Pm {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    {γ : (Fin 1 → R) → complexProjectiveSpace R 1} {m : ℕ} {w : Fin 1 → R} :
    w ∈ Pm P d γ m ↔ (0 < w 0 ∧ w 0 ≤ 1) ∧ AtLeastZeros P d (γ w) m :=
  Iff.rfl

set_option linter.unusedSectionVars false in
/-- `Pm m ⊆ (0,1]`. -/
theorem Pm_subset_intervalSet (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) (m : ℕ) :
    Pm P d γ m ⊆ intervalSet (R := R) :=
  fun _ hw => hw.1

set_option linter.unusedSectionVars false in
/-- `AtLeastZeros` is antitone in `m` (more zeros required ⇒ fewer parameters). -/
theorem atLeastZeros_mono {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    {p : complexProjectiveSpace R 1} {m n : ℕ} (hmn : m ≤ n) (h : AtLeastZeros P d p n) :
    AtLeastZeros P d p m := by
  obtain ⟨ys, hinj, hzero⟩ := h
  refine ⟨fun a => ys (Fin.castLE hmn a), ?_, fun a i => hzero (Fin.castLE hmn a) i⟩
  exact hinj.comp (Fin.castLE_injective hmn)

set_option linter.unusedSectionVars false in
/-- `Pm m` is antitone in `m`. -/
theorem Pm_mono (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) {m n : ℕ} (hmn : m ≤ n) :
    Pm P d γ n ⊆ Pm P d γ m :=
  fun _ hw => ⟨hw.1, atLeastZeros_mono hmn hw.2⟩

set_option linter.unusedSectionVars false in
/-- `AtLeastZeros … 0` is vacuously true. -/
theorem atLeastZeros_zero (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) : AtLeastZeros P d p 0 :=
  ⟨Fin.elim0, Function.injective_of_subsingleton _, fun a => a.elim0⟩

/-! ### Atom for step 1: the parameter-coupled joint zero condition is semialgebraic over `C` -/

/-- The **joint homotopy polynomial** `Q_{i'}` in the `2 + (k+1)` complex variables
`(λ, µ, v₀, …, v_k)`: it equals `X_λ · P_{i'}(v) + X_µ · D_{i'}(v)`, i.e. `homotopyPoly P d λ µ i'`
with `(λ, µ)` promoted to the first two variables and the homogeneous coordinates to the last `k+1`.
Evaluating it at `Fin.append ![λ, µ] v` recovers `aeval v (homotopyPoly P d λ µ i')`. -/
noncomputable def homotopyJointPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i' : Fin k) : MvPolynomial (Fin (2 + (k + 1))) (Ri R) :=
  X (Fin.castAdd (k + 1) 0) * rename (Fin.natAdd 2) (P i')
    + X (Fin.castAdd (k + 1) 1) * rename (Fin.natAdd 2) (diagFactor (d i') i')

set_option linter.unusedSectionVars false in
/-- Evaluating the joint polynomial at `Fin.append ![λ, µ] v` recovers
`aeval v (homotopyPoly P d λ µ i')`. -/
theorem aeval_homotopyJointPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i' : Fin k) (lam mu : Ri R) (v : Fin (k + 1) → Ri R) :
    aeval (Fin.append ![lam, mu] v) (homotopyJointPoly P d i')
      = aeval v (homotopyPoly P d lam mu i') := by
  have hcomp : (Fin.append ![lam, mu] v : Fin (2 + (k + 1)) → Ri R) ∘ Fin.natAdd 2 = v := by
    funext j; rw [Function.comp_apply, Fin.append_right]
  have hlam : (Fin.append ![lam, mu] v : Fin (2 + (k + 1)) → Ri R) (Fin.castAdd (k + 1) 0) = lam := by
    rw [Fin.append_left]; rfl
  have hmu : (Fin.append ![lam, mu] v : Fin (2 + (k + 1)) → Ri R) (Fin.castAdd (k + 1) 1) = mu := by
    rw [Fin.append_left]; rfl
  rw [homotopyJointPoly, homotopyPoly, map_add, map_mul, map_mul, aeval_X, aeval_X,
    aeval_rename, aeval_rename, hcomp, map_add, map_mul, map_mul, aeval_C, aeval_C, hlam, hmu,
    Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]

set_option linter.unusedSectionVars false in
/-- **Atom (step 1).** The joint zero condition "for all `i'`, `aeval v (homotopyPoly P d λ µ i') = 0`"
— as a condition on the combined complex coordinate `(λ, µ, v) ∈ C^{2+(k+1)}` — is semialgebraic over
`C`. This is the per-point, parameter-coupled common-zero locus; the full `atLeastZerosRP` is built
from `m` distinct copies of it (with distinctness and the chart/projection structure) and is the
remaining content of step 1. -/
theorem isSemialgebraicSetC_jointZeroLocus (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) :
    IsSemialgebraicSetC
      {u : Fin (2 + (k + 1)) → Ri R |
        ∀ i' : Fin k, aeval u (homotopyJointPoly P d i') = 0} := by
  classical
  have heq : {u : Fin (2 + (k + 1)) → Ri R |
        ∀ i' : Fin k, aeval u (homotopyJointPoly P d i') = 0}
      = ⋂ i' ∈ (Finset.univ : Finset (Fin k)),
          {u : Fin (2 + (k + 1)) → Ri R | aeval u (homotopyJointPoly P d i') = 0} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left]
  rw [heq]
  exact IsSemialgebraicSetC.biInter_finset Finset.univ
    (fun i' _ => isSemialgebraicSetC_complexPolyZero (homotopyJointPoly P d i'))

/-- The mixed real–projective lift of the `AtLeastZeros` condition: `{(w, p) | AtLeastZeros P d p m}`
(the condition does not depend on `w`). -/
def atLeastZerosRP (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) (m : ℕ) :
    Set ((Fin 1 → R) × complexProjectiveSpace R 1) :=
  {tp | AtLeastZeros P d tp.2 m}

set_option linter.unusedSectionVars false in
/-- **Reduction of step 1.** `Pm P d γ m` is the projection onto the parameter axis of the
intersection of three mixed real–projective sets: the cylinder over the interval `(0,1]`, the graph of
`γ` (semialgebraic from `exists_gammaPath_off_delta`), and the `AtLeastZeros` lift. Hence if the
`AtLeastZeros` lift is `IsSemialgebraicSetRP`, then `Pm P d γ m` is semialgebraic. This isolates the
remaining content of step 1 to the single fact `IsSemialgebraicSetRP (atLeastZerosRP P d m)`. -/
theorem isSemialgebraicSet_Pm_of_atLeastZerosRP (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (γ : (Fin 1 → R) → complexProjectiveSpace R 1) (m : ℕ)
    (hgraph : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1})
    (hAZ : IsSemialgebraicSetRP (atLeastZerosRP P d m)) :
    IsSemialgebraicSet (Pm P d γ m) := by
  -- The triple intersection.
  set T : Set ((Fin 1 → R) × complexProjectiveSpace R 1) :=
    {tp | tp.1 ∈ intervalSet (R := R)} ∩
      {tp | tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1} ∩
      atLeastZerosRP P d m with hT
  have hTsa : IsSemialgebraicSetRP T :=
    ((isSemialgebraicSetRP_cylinder isSemialgebraicSet_intervalSet).inter hgraph).inter hAZ
  have hproj := hTsa.proj
  -- Identify the projection with `Pm`.
  have heq : {w : Fin 1 → R | ∃ q : complexProjectiveSpace R 1, (w, q) ∈ T} = Pm P d γ m := by
    ext w
    simp only [Set.mem_ofPred_eq, hT, Set.mem_inter_iff, atLeastZerosRP, mem_Pm]
    constructor
    · rintro ⟨q, ⟨⟨hint, _, hq⟩, haz⟩⟩
      refine ⟨hint, ?_⟩
      rw [← hq]; exact haz
    · rintro ⟨hint, haz⟩
      have hw01 : w ∈ Set.Icc (0 : Fin 1 → R) 1 := by
        refine ⟨fun j => ?_, fun j => ?_⟩
        · fin_cases j; exact hint.1.le
        · fin_cases j; exact hint.2
      exact ⟨γ w, ⟨⟨hint, hw01, rfl⟩, haz⟩⟩
  rw [heq] at hproj; exact hproj

/-! ### The common-zero set of the pencil at a parameter, and the cardinality bridge -/

/-- The common projective zero set of the pencil `S₍p₎`. -/
def pencilZeroSet (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) : Set (complexProjectiveSpace R k) :=
  {x | ∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0}

set_option linter.unusedSectionVars false in
/-- `AtLeastZeros P d p m` says exactly that the common-zero set `pencilZeroSet P d p` contains the
range of some injective `ys : Fin m → ℙ_k(C)`. -/
theorem atLeastZeros_iff_exists_injOn {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    {p : complexProjectiveSpace R 1} {m : ℕ} :
    AtLeastZeros P d p m
      ↔ ∃ ys : Fin m → complexProjectiveSpace R k,
          Function.Injective ys ∧ ∀ a, ys a ∈ pencilZeroSet P d p := by
  rfl

set_option linter.unusedSectionVars false in
/-- **Cardinality bridge (`m ≤ ncard ⇒ AtLeastZeros`).** If the common-zero set has at least `m`
elements, there are `m` distinct zeros. Holds for any set whose `ncard` is `≥ m`. -/
theorem atLeastZeros_of_le_ncard {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    {p : complexProjectiveSpace R 1} {m : ℕ} (h : m ≤ (pencilZeroSet P d p).ncard) :
    AtLeastZeros P d p m := by
  classical
  rw [atLeastZeros_iff_exists_injOn]
  -- A set with `ncard ≥ m > 0` is finite (else `ncard = 0`); extract `m` distinct elements.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; exact ⟨Fin.elim0, Function.injective_of_subsingleton _, fun a => a.elim0⟩
  have hfin : (pencilZeroSet P d p).Finite := by
    rw [← Set.not_infinite]; intro hinf; rw [hinf.ncard] at h; omega
  -- Use the finset of the zero set; it has card ≥ m, so choose an injection from Fin m.
  set Z := hfin.toFinset with hZ
  have hZcard : m ≤ Z.card := by
    rw [Set.ncard_eq_toFinset_card (pencilZeroSet P d p) hfin] at h; exact h
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hZcard
  -- `T` is a finset of size `m`; its elements give an injective `Fin m → ℙ_k(C)`.
  have hcard : Fintype.card { x // x ∈ T } = m := by
    rw [Fintype.card_coe, hTcard]
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hcard |>.nonempty
  refine ⟨fun a => (e.symm a : complexProjectiveSpace R k), ?_, fun a => ?_⟩
  · intro a b hab
    have : e.symm a = e.symm b := Subtype.ext hab
    exact e.symm.injective this
  · have hmem : (e.symm a : complexProjectiveSpace R k) ∈ T := (e.symm a).2
    have := hTsub hmem
    rwa [hZ, Set.Finite.mem_toFinset] at this

set_option linter.unusedSectionVars false in
/-- **Cardinality bridge (`AtLeastZeros ⇒ m ≤ ncard`), finite case.** If the common-zero set is
finite and there are `m` distinct zeros, then `m ≤ ncard`. -/
theorem le_ncard_of_atLeastZeros {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    {p : complexProjectiveSpace R 1} {m : ℕ} (hfin : (pencilZeroSet P d p).Finite)
    (h : AtLeastZeros P d p m) : m ≤ (pencilZeroSet P d p).ncard := by
  classical
  obtain ⟨ys, hinj, hzero⟩ := h
  -- range of `ys` is a subset of the zero set, of cardinality `m`.
  have hsub : Set.range ys ⊆ pencilZeroSet P d p := by
    rintro _ ⟨a, rfl⟩; exact hzero a
  have hrcard : (Set.range ys).ncard = m := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  calc m = (Set.range ys).ncard := hrcard.symm
    _ ≤ (pencilZeroSet P d p).ncard := Set.ncard_le_ncard hsub hfin

set_option linter.unusedSectionVars false in
/-- The common-zero set of the pencil at `(0:1)` equals the common-zero set of the diagonal system. -/
theorem pencilZeroSet_pencilPt01 (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    pencilZeroSet P d (pencilPt01 (R := R))
      = {x : complexProjectiveSpace R k | ∀ i, aeval x.rep (diagSystem (R := R) d i) = 0} := by
  ext x
  exact zero_at_pencilPt01_iff_diagSystem P d x

set_option linter.unusedSectionVars false in
/-- The common-zero set of the pencil at `(0:1)` is finite of cardinality `∏ dᵢ`. -/
theorem pencilZeroSet_pencilPt01_ncard (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) :
    (pencilZeroSet P d (pencilPt01 (R := R))).ncard = ∏ i, d i := by
  rw [pencilZeroSet_pencilPt01, diagSystem_commonZero_eq_nonsingular d hd,
    diagSystem_nonsingularZero_ncard d hd]

set_option linter.unusedSectionVars false in
theorem pencilZeroSet_pencilPt01_finite (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) :
    (pencilZeroSet P d (pencilPt01 (R := R))).Finite := by
  rw [← Set.not_infinite]
  intro hinf
  have hprodpos : ∏ i, d i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.one_le_iff_ne_zero.mp (hd i)
  have := pencilZeroSet_pencilPt01_ncard P d hd
  rw [hinf.ncard] at this
  exact hprodpos this.symm

set_option linter.unusedSectionVars false in
/-- **Endpoint count (step 5).** At the diagonal endpoint `(0:1)`, the pencil has at least `m`
distinct zeros iff `m ≤ ∏ dᵢ`. -/
theorem atLeastZeros_pencilPt01_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (m : ℕ) :
    AtLeastZeros P d (pencilPt01 (R := R)) m ↔ m ≤ ∏ i, d i := by
  constructor
  · intro h
    have := le_ncard_of_atLeastZeros (pencilZeroSet_pencilPt01_finite P d hd) h
    rwa [pencilZeroSet_pencilPt01_ncard P d hd] at this
  · intro h
    apply atLeastZeros_of_le_ncard
    rw [pencilZeroSet_pencilPt01_ncard P d hd]; exact h

/-! ### The clopen dichotomy on the connected interval `(0,1]` (step 4) -/

set_option linter.unusedSectionVars false in
/-- **Clopen dichotomy on `(0,1]`.** A semialgebraic subset `U ⊆ (0,1]` that is both relatively open
and relatively closed in `(0,1]` is either empty or all of `(0,1]`. This is the engine of the
connectedness argument: applied to `Pm m` (open by the IFT, closed by curve selection), it forces
`Pm m` to be `∅` or everything. -/
theorem intervalSet_clopen_dichotomy {U : Set (Fin 1 → R)} (hUsub : U ⊆ intervalSet (R := R))
    (hUsa : IsSemialgebraicSet U) (hUopen : IsOpenIn (intervalSet (R := R)) U)
    (hUclosed : IsClosedIn (intervalSet (R := R)) U) :
    U = (∅ : Set (Fin 1 → R)) ∨ U = intervalSet (R := R) := by
  by_cases hUempty : U = (∅ : Set (Fin 1 → R))
  · exact Or.inl hUempty
  · right
    by_contra hUne
    have hconn := isSemialgebraicallyConnected_intervalSet (R := R)
    rw [isSemialgebraicallyConnected_iff isSemialgebraicSet_intervalSet] at hconn
    exact hconn ⟨U, Set.nonempty_iff_ne_empty.mpr hUempty, hUne, hUsub, hUsa, hUopen, hUclosed⟩

/-! ### The connectedness conclusion: a uniform bound on the number of zeros along `γ` (steps 4+5) -/

set_option linter.unusedSectionVars false in
/-- **Uniform zero bound along `γ` (steps 4+5 assembled).** Assume the path `γ` lands at the diagonal
endpoint (`γ 1 = (0:1)`) with `1 ∈ (0,1]`, and that for every `m` the set `Pm m` is semialgebraic and
both relatively open and relatively closed in `(0,1]`. Then **no** parameter `t ∈ (0,1]` carries more
than `∏ dᵢ` distinct common projective zeros of the pencil `S₍γ(t)₎`.
That is, for every `w ∈ (0,1]` and every `m`, `AtLeastZeros P d (γ w) m → m ≤ ∏ dᵢ`.

This packages the connectedness core of the BPR argument: the analytic content (openness via the IFT,
closedness via curve selection / projective completeness) is isolated into the three clopen
hypotheses, and the diagonal endpoint count is `pencilZeroSet_pencilPt01_ncard`. -/
theorem uniform_zero_bound_of_clopen (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγ1 : γ (1 : Fin 1 → R) = pencilPt01 (R := R))
    (hone : (1 : Fin 1 → R) 0 = 1)
    (hsa : ∀ m, IsSemialgebraicSet (Pm P d γ m))
    (hopen : ∀ m, IsOpenIn (intervalSet (R := R)) (Pm P d γ m))
    (hclosed : ∀ m, IsClosedIn (intervalSet (R := R)) (Pm P d γ m)) :
    ∀ w : Fin 1 → R, w ∈ intervalSet (R := R) → ∀ m, AtLeastZeros P d (γ w) m → m ≤ ∏ i, d i := by
  intro w hw m hat
  by_contra hlt
  push Not at hlt
  -- It suffices to show `Pm m = ∅` for this `m > ∏ dᵢ`, contradicting `w ∈ Pm m`.
  have hwPm : w ∈ Pm P d γ m := ⟨hw, hat⟩
  -- `Pm m` is clopen in `(0,1]`, so it is `∅` or everything.
  rcases intervalSet_clopen_dichotomy (Pm_subset_intervalSet P d γ m) (hsa m) (hopen m)
      (hclosed m) with hempty | hfull
  · rw [hempty] at hwPm; exact (Set.notMem_empty w) hwPm
  · -- If `Pm m = (0,1]`, then `1 ∈ Pm m`, so the diagonal endpoint has `≥ m` zeros, i.e. `m ≤ ∏ dᵢ`.
    have h1mem : (1 : Fin 1 → R) ∈ intervalSet (R := R) := by
      rw [mem_intervalSet, hone]; exact ⟨zero_lt_one, le_refl 1⟩
    have h1Pm : (1 : Fin 1 → R) ∈ Pm P d γ m := by rw [hfull]; exact h1mem
    have hat1 : AtLeastZeros P d (pencilPt01 (R := R)) m := by rw [← hγ1]; exact h1Pm.2
    have := (atLeastZeros_pencilPt01_iff P d hd m).mp hat1
    omega

/-! ### From a uniform finite-subset bound to an `ncard` bound -/

set_option linter.unusedSectionVars false in
/-- **From finite-subset bounds to an `ncard` bound.** If every finite subset of `T` has cardinality
at most `N`, then `T.ncard ≤ N`. (If `T` is infinite, `ncard T = 0 ≤ N`; if finite, take `F = T`.) -/
theorem ncard_le_of_forall_finset_card_le {α : Type*} {T : Set α} {N : ℕ}
    (h : ∀ F : Finset α, ↑F ⊆ T → F.card ≤ N) : T.ncard ≤ N := by
  have hmk : Cardinal.mk (T : Set α) ≤ (N : Cardinal) :=
    Cardinal.mk_le_iff_forall_finset_subset_card_le.mpr h
  have hlt : Cardinal.mk (T : Set α) < Cardinal.aleph0 :=
    lt_of_le_of_lt hmk (Cardinal.natCast_lt_aleph0 (n := N))
  have hfin : T.Finite := Set.finite_coe_iff.mp (Cardinal.lt_aleph0_iff_finite.mp hlt)
  have hcast : (T.ncard : Cardinal) = Cardinal.mk (T : Set α) := Set.cast_ncard hfin
  have : (T.ncard : Cardinal) ≤ (N : Cardinal) := hcast ▸ hmk
  exact_mod_cast this

/-! ### Final assembly (step 6) -/

set_option linter.unusedSectionVars false in
/-- **Weak Bézout from the uniform bound and the local injection.** Combining
* the **uniform zero bound** (`huniform`): no parameter `t ∈ (0,1]` carries more than `∏ dᵢ` distinct
  common projective zeros of `S₍γ(t)₎` (the output of `uniform_zero_bound_of_clopen`); and
* the **local-injection hypothesis** (`hinject`): every finite set `F` of non-singular projective
  zeros of `P` injects, via finitely many local IFT continuations near `(1:0)`, into the common zeros
  of `S₍γ(w)₎` for some common parameter `w ∈ (0,1]` (i.e. `AtLeastZeros P d (γ w) F.card`),

yields the weak Bézout bound `{x | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ dᵢ`. -/
theorem weakBezout_of_uniform_bound (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (huniform : ∀ w : Fin 1 → R, w ∈ intervalSet (R := R) →
      ∀ m, AtLeastZeros P d (γ w) m → m ≤ ∏ i, d i)
    (hinject : ∀ F : Finset (complexProjectiveSpace R k),
      (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x} →
      ∃ w : Fin 1 → R, w ∈ intervalSet (R := R) ∧ AtLeastZeros P d (γ w) F.card) :
    {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ i, d i := by
  apply ncard_le_of_forall_finset_card_le
  intro F hF
  obtain ⟨w, hw, hat⟩ := hinject F hF
  exact huniform w hw F.card hat

set_option linter.unusedSectionVars false in
/-- **Finite-subset form of `weakBezout_of_uniform_bound`.** Under the same uniform zero bound and
local-injection hypotheses, every finite set `F` of non-singular projective zeros of `P` has
cardinality at most `∏ dᵢ`. This is the per-finset content behind `weakBezout_of_uniform_bound` (which
just passes it to `ncard_le_of_forall_finset_card_le`); exposing it lets downstream injections (e.g.
the affine-to-projective embedding in Theorem 4.107) bound `Finset.card` directly. -/
theorem weakBezout_finsetCard_of_uniform_bound (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (huniform : ∀ w : Fin 1 → R, w ∈ intervalSet (R := R) →
      ∀ m, AtLeastZeros P d (γ w) m → m ≤ ∏ i, d i)
    (hinject : ∀ F : Finset (complexProjectiveSpace R k),
      (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x} →
      ∃ w : Fin 1 → R, w ∈ intervalSet (R := R) ∧ AtLeastZeros P d (γ w) F.card) :
    ∀ F : Finset (complexProjectiveSpace R k),
      (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x} →
      F.card ≤ ∏ i, d i := by
  intro F hF
  obtain ⟨w, hw, hat⟩ := hinject F hF
  exact huniform w hw F.card hat

end Azurite.BPR.Chapter4
