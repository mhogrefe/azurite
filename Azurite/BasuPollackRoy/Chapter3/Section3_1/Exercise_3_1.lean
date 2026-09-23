import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_1
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_3
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_89
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Exercise_2_17

/-! # BPR §3.1, Exercise 3.1 — topology transfers along a real closed field extension

Let `R'` be a real closed field containing `R`. A semialgebraic `S ⊆ R^k` is open (resp. closed)
iff `Ext(S, R')` is, and `Ext(closure S) = closure(Ext S)`; a semialgebraic function `f` is
continuous iff `Ext(f, R')` is.

The crux is `ext_closure : Ext(closure S) = closure(Ext S)`. We reuse Proposition 3.1's projection
construction of the closure: `closure S = (farSet S)ᶜ`, where `farSet S` is built by a double
coordinate projection from a polynomial sign condition (`distPoly`). Pushing `extension` through that
construction — each step a Tarski–Seidenberg-backed `ext_*` lemma, with the two atom loci handled by
`ext_eq` — gives `Ext(farSet S) = farSet(Ext S)`, hence the closure identity. -/

namespace Azurite.BPR

open MvPolynomial

/-! ### The `farSet` and the projection chain, over a single real closed field -/

section Generic

variable {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]

/-- `farSet S = {x | ∃ r > 0, ∀ y ∈ S, ‖y − x‖² ≥ r²}` — the complement of the closure of `S`. -/
def farSet {k : ℕ} (S : Set (Fin k → C)) : Set (Fin k → C) :=
  {x | ∃ r, 0 < r ∧ ∀ y ∈ S, r ^ 2 ≤ euclideanNormSq (y - x)}

/-- Sign-condition `‖y − x‖² < r²` in the combined variables `(x, r, y)`. -/
def closeChainSet (k : ℕ) : Set (Fin ((k + 1) + k) → C) := {w | eval w (distPoly k) < 0}

/-- The radius coordinate is positive. -/
def posChainSet (k : ℕ) : Set (Fin (k + 1) → C) :=
  {xr | eval xr (X (Fin.natAdd k (0 : Fin 1))) > 0}

/-- Cylinder of `S` over the witness block `y`. -/
def sliftChainSet {k : ℕ} (S : Set (Fin k → C)) : Set (Fin ((k + 1) + k) → C) :=
  {w | w ∘ Fin.natAdd (k + 1) ∈ S}

/-- `{(x,r) | ∃ y ∈ S, ‖y − x‖² < r²}` — projecting the witness `y` away. -/
def existsCloseChainSet {k : ℕ} (S : Set (Fin k → C)) : Set (Fin (k + 1) → C) :=
  {xr | ∃ y : Fin k → C, Fin.append xr y ∈ sliftChainSet S ∩ closeChainSet k}

/-- `{(x,r) | r > 0 ∧ ∀ y ∈ S, ‖y − x‖² ≥ r²}`. -/
def farChainSet {k : ℕ} (S : Set (Fin k → C)) : Set (Fin (k + 1) → C) :=
  posChainSet k ∩ (existsCloseChainSet S)ᶜ

/-- `{x | ∃ r > 0, ∀ y ∈ S, ‖y − x‖² ≥ r²}` — projecting the radius away; equals `farSet S`. -/
def notClosureChainSet {k : ℕ} (S : Set (Fin k → C)) : Set (Fin k → C) :=
  {x | ∃ rv : Fin 1 → C, Fin.append x rv ∈ farChainSet S}

omit [IsRealClosed C] in
theorem mem_farChainSet {k : ℕ} {S : Set (Fin k → C)} (x : Fin k → C) (rv : Fin 1 → C) :
    Fin.append x rv ∈ farChainSet S ↔
      (0 < rv 0 ∧ ∀ y ∈ S, (rv 0) ^ 2 ≤ euclideanNormSq (y - x)) := by
  have hSm : ∀ y : Fin k → C, (Fin.append (Fin.append x rv) y ∈ sliftChainSet S) ↔ y ∈ S := by
    intro y; rw [sliftChainSet, Set.mem_ofPred_eq, append_comp_natAdd]
  have hCm : ∀ y : Fin k → C,
      (Fin.append (Fin.append x rv) y ∈ closeChainSet k) ↔ euclideanNormSq (y - x) < (rv 0) ^ 2 := by
    intro y
    rw [closeChainSet, Set.mem_ofPred_eq, eval_distPoly]
    simp only [Fin.append_left, Fin.append_right]
    rw [show (∑ i, (y i - x i) ^ 2) = euclideanNormSq (y - x) from by
          simp only [euclideanNormSq, Pi.sub_apply], sub_lt_zero]
  rw [farChainSet, Set.mem_inter_iff, posChainSet, Set.mem_ofPred_eq, eval_X, Fin.append_right,
    Set.mem_compl_iff, existsCloseChainSet, Set.mem_ofPred_eq, not_exists]
  refine and_congr_right (fun _ => forall_congr' (fun y => ?_))
  rw [Set.mem_inter_iff, hSm y, hCm y, not_and, not_lt]

omit [IsRealClosed C] in
theorem notClosureChainSet_eq_farSet {k : ℕ} {S : Set (Fin k → C)} :
    notClosureChainSet S = farSet S := by
  ext x
  simp only [notClosureChainSet, farSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rv, hrv⟩; rw [mem_farChainSet] at hrv; exact ⟨rv 0, hrv.1, hrv.2⟩
  · rintro ⟨r, hr, hall⟩
    exact ⟨fun _ => r, (mem_farChainSet x (fun _ => r)).mpr ⟨hr, by simpa using hall⟩⟩

theorem closure_eq_compl_farSet {k : ℕ} {S : Set (Fin k → C)} : closure S = (farSet S)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, mem_closure_iff_ball, farSet, Set.mem_ofPred_eq]
  constructor
  · rintro hcl ⟨r, hr, hall⟩
    obtain ⟨y, hyS, hlt⟩ := hcl r hr
    exact absurd (hall y hyS) (not_le.mpr hlt)
  · intro hnot r hr
    by_contra hcon
    push Not at hcon
    exact hnot ⟨r, hr, by simpa using hcon⟩

theorem farSet_eq_compl_closure {k : ℕ} {S : Set (Fin k → C)} : farSet S = (closure S)ᶜ := by
  rw [closure_eq_compl_farSet, compl_compl]

theorem isSemialgebraicSet_farSet {k : ℕ} {S : Set (Fin k → C)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet (farSet S) := by
  rw [farSet_eq_compl_closure]; exact (isSemialgebraicSet_closure hS).compl

end Generic

/-! ### Pushing the extension through the chain (Tarski–Seidenberg) -/

section Ext

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem aeval_eq_eval_self {σ : Type*} (w : σ → R) (P : MvPolynomial σ R) :
    aeval w P = eval w P := by rw [aeval_def]; rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R'] in
theorem map_distPoly (k : ℕ) :
    MvPolynomial.map (algebraMap R R') (distPoly k) = distPoly k := by
  simp only [distPoly, map_sub, map_sum, map_pow, MvPolynomial.map_X]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R']
  [IsRealClosed R'] in
theorem aeval_distPoly (k : ℕ) (w' : Fin ((k + 1) + k) → R') :
    aeval w' (distPoly k : MvPolynomial (Fin ((k + 1) + k)) R)
      = eval w' (distPoly k : MvPolynomial (Fin ((k + 1) + k)) R') := by
  rw [aeval_def, ← eval_map, map_distPoly]

/-- **Atom locus `‖y − x‖² < r²` extends to its `R'`-counterpart** (via `ext_eq`). -/
theorem ext_closeChainSet (k : ℕ) :
    extension (R' := R') (closeChainSet (C := R) k) (IsSemialgebraicSet.ltZero _)
      = closeChainSet (C := R') k := by
  have hΦ : closeChainSet (C := R) k
      = (Formula.ltZeroO (distPoly k : MvPolynomial (Fin ((k + 1) + k)) R)).realization (C := R) := by
    rw [Formula.realization_ltZeroO]
    ext w; simp only [closeChainSet, Set.mem_ofPred_eq, aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_ltZeroO]
  ext w'; simp only [closeChainSet, Set.mem_ofPred_eq, aeval_distPoly]

/-- **Atom locus `r > 0` extends to its `R'`-counterpart**. -/
theorem ext_posChainSet (k : ℕ) :
    extension (R' := R') (posChainSet (C := R) k) (IsSemialgebraicSet.gtZero _)
      = posChainSet (C := R') k := by
  have hΦ : posChainSet (C := R) k
      = (Formula.gtZeroO (X (Fin.natAdd k (0 : Fin 1)) : MvPolynomial (Fin (k + 1)) R)).realization
          (C := R) := by
    rw [Formula.realization_gtZeroO]
    ext xr; simp only [posChainSet, Set.mem_ofPred_eq, aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_gtZeroO]
  ext xr'; simp only [posChainSet, Set.mem_ofPred_eq, aeval_X, eval_X]

/-- **The cylinder over `S` extends to the cylinder over `Ext S`** (via `ext_comap`). -/
theorem ext_sliftChainSet {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    extension (R' := R') (sliftChainSet S) (IsSemialgebraicSet.comap (Fin.natAdd (k + 1)) hS)
      = sliftChainSet (extension (R' := R') S hS) :=
  ext_comap (Fin.natAdd (k + 1)) (Fin.natAdd_injective _ _) hS

/-- **`Ext(farSet S) = farSet(Ext S)`** — pushing the extension through the whole chain. -/
theorem ext_farSet {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    extension (R' := R') (farSet S) (isSemialgebraicSet_farSet hS)
      = farSet (extension (R' := R') S hS) := by
  set T := extension (R' := R') S hS with hT
  have hslift : IsSemialgebraicSet (sliftChainSet S) := IsSemialgebraicSet.comap (Fin.natAdd (k + 1)) hS
  have hclose : IsSemialgebraicSet (closeChainSet (C := R) k) := IsSemialgebraicSet.ltZero _
  have hexists : IsSemialgebraicSet (existsCloseChainSet S) :=
    IsSemialgebraicSet.exists_append_right (hslift.inter hclose)
  have hpos : IsSemialgebraicSet (posChainSet (C := R) k) := IsSemialgebraicSet.gtZero _
  have hfar : IsSemialgebraicSet (farChainSet S) := hpos.inter hexists.compl
  have hnot : IsSemialgebraicSet (notClosureChainSet S) := IsSemialgebraicSet.exists_append_right hfar
  have e_exists : extension (R' := R') (existsCloseChainSet S) hexists = existsCloseChainSet T := by
    show extension (R' := R')
      {xr : Fin (k + 1) → R | ∃ y : Fin k → R, Fin.append xr y ∈ sliftChainSet S ∩ closeChainSet k}
      _ = _
    rw [ext_exists_append (hslift.inter hclose) hexists, ext_inter hslift hclose,
      ext_sliftChainSet hS, ext_closeChainSet]
    rfl
  have e_far : extension (R' := R') (farChainSet S) hfar = farChainSet T := by
    show extension (R' := R') (posChainSet (C := R) k ∩ (existsCloseChainSet S)ᶜ) _ = _
    rw [ext_inter hpos hexists.compl, ext_posChainSet, ext_compl hexists, e_exists]
    rfl
  have e_not : extension (R' := R') (notClosureChainSet S) hnot = farSet T := by
    show extension (R' := R')
      {x : Fin k → R | ∃ rv : Fin 1 → R, Fin.append x rv ∈ farChainSet S} _ = _
    rw [ext_exists_append hfar hnot, e_far, ← notClosureChainSet_eq_farSet]
    rfl
  rw [ext_congr (isSemialgebraicSet_farSet hS) hnot notClosureChainSet_eq_farSet.symm, e_not]

/-! ### Part (a): open/closed/closure transfer -/

/-- **`Ext(closure S) = closure(Ext S)`** (Exercise 3.1a). -/
theorem ext_closure {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    extension (R' := R') (closure S) (isSemialgebraicSet_closure hS)
      = closure (extension (R' := R') S hS) := by
  rw [ext_congr (isSemialgebraicSet_closure hS) (isSemialgebraicSet_farSet hS).compl
      closure_eq_compl_farSet, ext_compl (isSemialgebraicSet_farSet hS), ext_farSet hS,
      ← closure_eq_compl_farSet]

/-- `Ext` is injective on semialgebraic sets. -/
theorem ext_inj {k : ℕ} {A B : Set (Fin k → R)} (hA : IsSemialgebraicSet A) (hB : IsSemialgebraicSet B)
    (h : extension (R' := R') A hA = extension (R' := R') B hB) : A = B :=
  Set.Subset.antisymm ((ext_subset_iff hA hB).mpr h.le) ((ext_subset_iff hB hA).mpr h.ge)

/-- **`S` is closed iff `Ext S` is closed** (Exercise 3.1a). -/
theorem ext_isClosed {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsClosed S ↔ IsClosed (extension (R' := R') S hS) := by
  rw [← closure_eq_iff_isClosed, ← closure_eq_iff_isClosed, ← ext_closure hS]
  constructor
  · intro h; exact ext_congr (isSemialgebraicSet_closure hS) hS h
  · intro h; exact ext_inj (isSemialgebraicSet_closure hS) hS h

/-- **`S` is open iff `Ext S` is open** (Exercise 3.1a). -/
theorem ext_isOpen {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsOpen S ↔ IsOpen (extension (R' := R') S hS) := by
  rw [show IsOpen S ↔ IsClosed Sᶜ from isClosed_compl_iff.symm,
    show IsOpen (extension (R' := R') S hS) ↔ IsClosed (extension (R' := R') S hS)ᶜ from
      isClosed_compl_iff.symm, ← ext_compl hS]
  exact ext_isClosed hS.compl

end Ext

/-! ### Part (b): continuity transfers — the discontinuity locus

`f` is continuous on `S` iff its *discontinuity locus* `D_f` is empty. We express `D_f` over the
graph `G = funGraph S f` as `dscGraph G`, a semialgebraic set built by a four-fold projection from
two squared-distance sign conditions. Pushing `extension` through `dscGraph` (Tarski–Seidenberg)
turns `D_f = ∅` over `R` into `D_{f'} = ∅` over `R'`, i.e. continuity of `f'`. -/

section GenericB

variable {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C]

/-- Generic squared-distance-minus-square polynomial `‖(X∘yi) − (X∘xi)‖² − (X ri)²`. -/
noncomputable def distSqPoly {N k : ℕ} (xi yi : Fin k → Fin N) (ri : Fin N) :
    MvPolynomial (Fin N) C :=
  (∑ i, (X (yi i) - X (xi i)) ^ 2) - (X ri) ^ 2

omit [LinearOrder C] [IsStrictOrderedRing C] [IsRealClosed C] in
theorem eval_distSqPoly {N k : ℕ} (xi yi : Fin k → Fin N) (ri : Fin N) (w : Fin N → C) :
    eval w (distSqPoly xi yi ri) = (∑ i, (w (yi i) - w (xi i)) ^ 2) - (w ri) ^ 2 := by
  simp only [distSqPoly, map_sub, map_sum, map_pow, eval_X]

variable (k ℓ : ℕ)

/-- Index of the `x`-block coordinate `i` in the combined space `Fin (k+ℓ+1+1+(k+ℓ))`. -/
def xIdx (i : Fin k) : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.castAdd (k + ℓ) (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd ℓ i)))
def uIdx (j : Fin ℓ) : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.castAdd (k + ℓ) (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd k j)))
def rIdx : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.castAdd (k + ℓ) (Fin.castAdd 1 (Fin.natAdd (k + ℓ) (0 : Fin 1)))
def dltIdx : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.castAdd (k + ℓ) (Fin.natAdd (k + ℓ + 1) (0 : Fin 1))
def yIdx (i : Fin k) : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.natAdd (k + ℓ + 1 + 1) (Fin.castAdd ℓ i)
def vIdx (j : Fin ℓ) : Fin (k + ℓ + 1 + 1 + (k + ℓ)) :=
  Fin.natAdd (k + ℓ + 1 + 1) (Fin.natAdd k j)

variable {k ℓ}

/-- `‖y − x‖² < δ²` in the combined variables. -/
def ball1Set : Set (Fin (k + ℓ + 1 + 1 + (k + ℓ)) → C) :=
  {w | eval w (distSqPoly (xIdx k ℓ) (yIdx k ℓ) (dltIdx k ℓ)) < 0}
/-- `‖v − u‖² ≥ r²` in the combined variables. -/
def ball2Set : Set (Fin (k + ℓ + 1 + 1 + (k + ℓ)) → C) :=
  {w | eval w (distSqPoly (uIdx k ℓ) (vIdx k ℓ) (rIdx k ℓ)) ≥ 0}
/-- The `(y,v)` block lands in the graph `G`. -/
def graphBlockSet (G : Set (Fin (k + ℓ) → C)) : Set (Fin (k + ℓ + 1 + 1 + (k + ℓ)) → C) :=
  {w | w ∘ Fin.natAdd (k + ℓ + 1 + 1) ∈ G}

/-- `∃ (y,v), (y,v) ∈ G ∧ ‖y−x‖² < δ² ∧ ‖v−u‖² ≥ r²` — projecting the `(y,v)` block. -/
def existsQSet (G : Set (Fin (k + ℓ) → C)) : Set (Fin (k + ℓ + 1 + 1) → C) :=
  {p | ∃ yv : Fin (k + ℓ) → C, Fin.append p yv ∈ graphBlockSet G ∩ ball1Set ∩ ball2Set}
/-- `δ > 0`. -/
def posDltSet : Set (Fin (k + ℓ + 1 + 1) → C) :=
  {p | eval p (X (Fin.natAdd (k + ℓ + 1) (0 : Fin 1))) > 0}
/-- `∀ δ > 0, (∃ (y,v) …)` — complement of the projection of `δ>0 ∧ ¬∃`. -/
def allDltSet (G : Set (Fin (k + ℓ) → C)) : Set (Fin (k + ℓ + 1) → C) :=
  {q | ∃ dlt : Fin 1 → C, Fin.append q dlt ∈ posDltSet ∩ (existsQSet G)ᶜ}ᶜ
/-- `r > 0`. -/
def posRSet : Set (Fin (k + ℓ + 1) → C) :=
  {q | eval q (X (Fin.natAdd (k + ℓ) (0 : Fin 1))) > 0}
/-- `∃ r > 0, ∀ δ > 0, ∃ (y,v) …` — the discontinuity condition on `(x,u)`. -/
def dscPointSet (G : Set (Fin (k + ℓ) → C)) : Set (Fin (k + ℓ) → C) :=
  {p | ∃ rr : Fin 1 → C, Fin.append p rr ∈ posRSet ∩ allDltSet G}
/-- **Discontinuity locus** over the graph: `{x | ∃ u, (x,u)∈G ∧ (x,u) discontinuity point}`. -/
def dscGraph (G : Set (Fin (k + ℓ) → C)) : Set (Fin k → C) :=
  {x | ∃ u : Fin ℓ → C, Fin.append x u ∈ G ∩ dscPointSet G}

/-! #### Membership characterization of `dscGraph` -/

omit [IsRealClosed C] in
theorem mem_inner {G : Set (Fin (k + ℓ) → C)} (x : Fin k → C) (u : Fin ℓ → C) (rr dlt : Fin 1 → C)
    (yv : Fin (k + ℓ) → C) :
    Fin.append (Fin.append (Fin.append (Fin.append x u) rr) dlt) yv
        ∈ graphBlockSet G ∩ ball1Set ∩ ball2Set ↔
      (yv ∈ G ∧ euclideanNormSq (yv ∘ Fin.castAdd ℓ - x) < (dlt 0) ^ 2
        ∧ (rr 0) ^ 2 ≤ euclideanNormSq (yv ∘ Fin.natAdd k - u)) := by
  rw [Set.mem_inter_iff, Set.mem_inter_iff, graphBlockSet, Set.mem_ofPred_eq, ball1Set,
    Set.mem_ofPred_eq, ball2Set, Set.mem_ofPred_eq, eval_distSqPoly, eval_distSqPoly,
    append_comp_natAdd]
  simp only [xIdx, uIdx, rIdx, dltIdx, yIdx, vIdx, Fin.append_left, Fin.append_right]
  rw [show (∑ i, (yv (Fin.castAdd ℓ i) - x i) ^ 2) = euclideanNormSq (yv ∘ Fin.castAdd ℓ - x) from by
        simp only [euclideanNormSq, Pi.sub_apply, Function.comp_apply],
    show (∑ j, (yv (Fin.natAdd k j) - u j) ^ 2) = euclideanNormSq (yv ∘ Fin.natAdd k - u) from by
        simp only [euclideanNormSq, Pi.sub_apply, Function.comp_apply],
    sub_lt_zero, ge_iff_le, sub_nonneg, and_assoc]

omit [IsRealClosed C] in
theorem mem_dscGraph {G : Set (Fin (k + ℓ) → C)} (x : Fin k → C) :
    x ∈ dscGraph G ↔ ∃ u : Fin ℓ → C, Fin.append x u ∈ G ∧ ∃ r, 0 < r ∧ ∀ d, 0 < d →
      ∃ yv : Fin (k + ℓ) → C, yv ∈ G ∧ euclideanNormSq (yv ∘ Fin.castAdd ℓ - x) < d ^ 2
        ∧ r ^ 2 ≤ euclideanNormSq (yv ∘ Fin.natAdd k - u) := by
  rw [dscGraph, Set.mem_ofPred_eq]
  refine exists_congr (fun u => ?_)
  rw [Set.mem_inter_iff]
  refine and_congr_right (fun _ => ?_)
  rw [dscPointSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rr, hrr⟩
    rw [Set.mem_inter_iff, posRSet, Set.mem_ofPred_eq, eval_X, Fin.append_right, allDltSet,
      Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists] at hrr
    refine ⟨rr 0, hrr.1, fun d hd => ?_⟩
    have := hrr.2 (fun _ => d)
    rw [Set.mem_inter_iff, posDltSet, Set.mem_ofPred_eq, eval_X, Fin.append_right,
      Set.mem_compl_iff, existsQSet, Set.mem_ofPred_eq, not_and, not_not] at this
    obtain ⟨yv, hyv⟩ := this hd
    rw [mem_inner] at hyv
    exact ⟨yv, hyv.1, hyv.2.1, hyv.2.2⟩
  · rintro ⟨r, hr, hall⟩
    refine ⟨fun _ => r, ?_⟩
    rw [Set.mem_inter_iff, posRSet, Set.mem_ofPred_eq, eval_X, Fin.append_right, allDltSet,
      Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists]
    refine ⟨hr, fun dlt => ?_⟩
    rw [Set.mem_inter_iff, posDltSet, Set.mem_ofPred_eq, eval_X, Fin.append_right,
      Set.mem_compl_iff, existsQSet, Set.mem_ofPred_eq, not_and, not_not]
    intro hdlt
    obtain ⟨yv, hyv1, hyv2, hyv3⟩ := hall (dlt 0) hdlt
    exact ⟨yv, (mem_inner x u (fun _ => r) dlt yv).mpr ⟨hyv1, hyv2, hyv3⟩⟩

theorem normSq_lt_sq_iff {n : ℕ} {z : Fin n → C} {δ : C} (hδ : 0 < δ) :
    euclideanNormSq z < δ ^ 2 ↔ euclideanNorm z < δ := by
  rw [← euclideanNorm_sq]
  constructor
  · intro h; nlinarith [euclideanNorm_nonneg z]
  · intro h; nlinarith [euclideanNorm_nonneg z]

theorem sq_le_normSq_iff {n : ℕ} {z : Fin n → C} {r : C} (hr : 0 < r) :
    r ^ 2 ≤ euclideanNormSq z ↔ r ≤ euclideanNorm z := by
  rw [← not_lt, ← not_lt, not_iff_not]; exact normSq_lt_sq_iff hr

omit [IsRealClosed C] in
/-- Membership in the discontinuity locus of a function graph, in terms of `f`. -/
theorem mem_dscGraph_funGraph {S : Set (Fin k → C)} {f : (Fin k → C) → (Fin ℓ → C)}
    (x : Fin k → C) :
    x ∈ dscGraph (funGraph S f) ↔ x ∈ S ∧ ∃ r, 0 < r ∧ ∀ d, 0 < d → ∃ y ∈ S,
      euclideanNormSq (y - x) < d ^ 2 ∧ r ^ 2 ≤ euclideanNormSq (f y - f x) := by
  rw [mem_dscGraph]
  constructor
  · rintro ⟨u, hu, r, hr, hall⟩
    rw [append_mem_funGraph] at hu
    obtain ⟨hxS, rfl⟩ := hu
    refine ⟨hxS, r, hr, fun d hd => ?_⟩
    obtain ⟨yv, hyvmem, hyv1, hyv2⟩ := hall d hd
    rw [mem_funGraph] at hyvmem
    refine ⟨yv ∘ Fin.castAdd ℓ, hyvmem.1, hyv1, ?_⟩
    rwa [hyvmem.2] at hyv2
  · rintro ⟨hxS, r, hr, hall⟩
    refine ⟨f x, (append_mem_funGraph S f x (f x)).mpr ⟨hxS, rfl⟩, r, hr, fun d hd => ?_⟩
    obtain ⟨y, hyS, hy1, hy2⟩ := hall d hd
    refine ⟨Fin.append y (f y), (append_mem_funGraph S f y (f y)).mpr ⟨hyS, rfl⟩, ?_, ?_⟩
    · rw [append_comp_castAdd]; exact hy1
    · rw [append_comp_natAdd]; exact hy2

/-- **The discontinuity locus is empty iff `f` is continuous on `S`** (over any real closed field). -/
theorem dscGraph_funGraph_eq_empty_iff {S : Set (Fin k → C)} {f : (Fin k → C) → (Fin ℓ → C)} :
    dscGraph (funGraph S f) = ∅ ↔ ContinuousOn f S := by
  rw [Set.eq_empty_iff_forall_notMem, continuousOn_iff_ball]
  refine forall_congr' fun x => ?_
  rw [mem_dscGraph_funGraph]
  constructor
  · intro hnotmem hxS ε hε
    by_contra hcon
    push Not at hcon
    refine absurd ⟨hxS, ε, hε, fun d hd => ?_⟩ hnotmem
    obtain ⟨y, hyS, hy1, hy2⟩ := hcon d hd
    exact ⟨y, hyS, (normSq_lt_sq_iff hd).mpr hy1, (sq_le_normSq_iff hε).mpr hy2⟩
  · rintro hcont ⟨hxS, r, hr, hall⟩
    obtain ⟨δ, hδ, hδall⟩ := hcont hxS r hr
    obtain ⟨y, hyS, hy1, hy2⟩ := hall δ hδ
    exact absurd (hδall y hyS ((normSq_lt_sq_iff hδ).mp hy1)) (not_lt.mpr ((sq_le_normSq_iff hr).mp hy2))

theorem isSemialgebraicSet_dscGraph {G : Set (Fin (k + ℓ) → C)} (hG : IsSemialgebraicSet G) :
    IsSemialgebraicSet (dscGraph G) := by
  have hgb : IsSemialgebraicSet (graphBlockSet G) := IsSemialgebraicSet.comap _ hG
  have hb1 : IsSemialgebraicSet (ball1Set (C := C) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.ltZero _
  have hb2 : IsSemialgebraicSet (ball2Set (C := C) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.geZero _
  have heq : IsSemialgebraicSet (existsQSet G) :=
    IsSemialgebraicSet.exists_append_right ((hgb.inter hb1).inter hb2)
  have hpd : IsSemialgebraicSet (posDltSet (C := C) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.gtZero _
  have had : IsSemialgebraicSet (allDltSet G) :=
    (IsSemialgebraicSet.exists_append_right (hpd.inter heq.compl)).compl
  have hpr : IsSemialgebraicSet (posRSet (C := C) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.gtZero _
  have hdp : IsSemialgebraicSet (dscPointSet G) :=
    IsSemialgebraicSet.exists_append_right (hpr.inter had)
  exact IsSemialgebraicSet.exists_append_right (hG.inter hdp)

end GenericB

/-! ### Pushing the extension through the discontinuity locus -/

section ExtB

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']
variable {k ℓ : ℕ}

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R']
  [IsRealClosed R'] in
theorem map_distSqPoly {N m : ℕ} (xi yi : Fin m → Fin N) (ri : Fin N) :
    MvPolynomial.map (algebraMap R R') (distSqPoly xi yi ri) = distSqPoly xi yi ri := by
  simp only [distSqPoly, map_sub, map_sum, map_pow, MvPolynomial.map_X]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder R'] [IsStrictOrderedRing R']
  [IsRealClosed R'] in
theorem aeval_distSqPoly {N m : ℕ} (xi yi : Fin m → Fin N) (ri : Fin N) (w' : Fin N → R') :
    aeval w' (distSqPoly xi yi ri : MvPolynomial (Fin N) R)
      = eval w' (distSqPoly xi yi ri : MvPolynomial (Fin N) R') := by
  rw [aeval_def, ← eval_map, map_distSqPoly]

theorem ext_ball1Set :
    extension (R' := R') (ball1Set (C := R) (k := k) (ℓ := ℓ)) (IsSemialgebraicSet.ltZero _)
      = ball1Set (C := R') := by
  have hΦ : ball1Set (C := R) (k := k) (ℓ := ℓ) = (Formula.ltZeroO
      (distSqPoly (xIdx k ℓ) (yIdx k ℓ) (dltIdx k ℓ) : MvPolynomial _ R)).realization (C := R) := by
    rw [Formula.realization_ltZeroO]; ext w; simp only [ball1Set, Set.mem_ofPred_eq, aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_ltZeroO]
  ext w'; simp only [ball1Set, Set.mem_ofPred_eq, aeval_distSqPoly]

theorem ext_ball2Set :
    extension (R' := R') (ball2Set (C := R) (k := k) (ℓ := ℓ)) (IsSemialgebraicSet.geZero _)
      = ball2Set (C := R') := by
  have hΦ : ball2Set (C := R) (k := k) (ℓ := ℓ) = (Formula.geZeroO
      (distSqPoly (uIdx k ℓ) (vIdx k ℓ) (rIdx k ℓ) : MvPolynomial _ R)).realization (C := R) := by
    rw [Formula.realization_geZeroO]; ext w; simp only [ball2Set, Set.mem_ofPred_eq, ge_iff_le,
      aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_geZeroO]
  ext w'; simp only [ball2Set, Set.mem_ofPred_eq, ge_iff_le, aeval_distSqPoly]

theorem ext_graphBlockSet {G : Set (Fin (k + ℓ) → R)} (hG : IsSemialgebraicSet G) :
    extension (R' := R') (graphBlockSet G) (IsSemialgebraicSet.comap (Fin.natAdd (k + ℓ + 1 + 1)) hG)
      = graphBlockSet (extension (R' := R') G hG) :=
  ext_comap (Fin.natAdd (k + ℓ + 1 + 1)) (Fin.natAdd_injective _ _) hG

theorem ext_posDltSet :
    extension (R' := R') (posDltSet (C := R) (k := k) (ℓ := ℓ)) (IsSemialgebraicSet.gtZero _)
      = posDltSet (C := R') := by
  have hΦ : posDltSet (C := R) (k := k) (ℓ := ℓ) = (Formula.gtZeroO
      (X (Fin.natAdd (k + ℓ + 1) (0 : Fin 1)) : MvPolynomial (Fin (k + ℓ + 1 + 1)) R)).realization
        (C := R) := by
    rw [Formula.realization_gtZeroO]; ext p; simp only [posDltSet, Set.mem_ofPred_eq, aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_gtZeroO]
  ext p'; simp only [posDltSet, Set.mem_ofPred_eq, aeval_X, eval_X]

theorem ext_posRSet :
    extension (R' := R') (posRSet (C := R) (k := k) (ℓ := ℓ)) (IsSemialgebraicSet.gtZero _)
      = posRSet (C := R') := by
  have hΦ : posRSet (C := R) (k := k) (ℓ := ℓ) = (Formula.gtZeroO
      (X (Fin.natAdd (k + ℓ) (0 : Fin 1)) : MvPolynomial (Fin (k + ℓ + 1)) R)).realization
        (C := R) := by
    rw [Formula.realization_gtZeroO]; ext q; simp only [posRSet, Set.mem_ofPred_eq, aeval_eq_eval_self]
  refine (ext_eq _ hΦ).trans ?_
  rw [Formula.realization_gtZeroO]
  ext q'; simp only [posRSet, Set.mem_ofPred_eq, aeval_X, eval_X]

/-- **`Ext(dscGraph G) = dscGraph(Ext G)`** — pushing the extension through the locus. -/
theorem ext_dscGraph {G : Set (Fin (k + ℓ) → R)} (hG : IsSemialgebraicSet G) :
    extension (R' := R') (dscGraph G) (isSemialgebraicSet_dscGraph hG)
      = dscGraph (extension (R' := R') G hG) := by
  set T := extension (R' := R') G hG with hT
  have hgb : IsSemialgebraicSet (graphBlockSet G) := IsSemialgebraicSet.comap _ hG
  have hb1 : IsSemialgebraicSet (ball1Set (C := R) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.ltZero _
  have hb2 : IsSemialgebraicSet (ball2Set (C := R) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.geZero _
  have heq : IsSemialgebraicSet (existsQSet G) :=
    IsSemialgebraicSet.exists_append_right ((hgb.inter hb1).inter hb2)
  have hpd : IsSemialgebraicSet (posDltSet (C := R) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.gtZero _
  have had : IsSemialgebraicSet (allDltSet G) :=
    (IsSemialgebraicSet.exists_append_right (hpd.inter heq.compl)).compl
  have hpr : IsSemialgebraicSet (posRSet (C := R) (k := k) (ℓ := ℓ)) := IsSemialgebraicSet.gtZero _
  have hdp : IsSemialgebraicSet (dscPointSet G) :=
    IsSemialgebraicSet.exists_append_right (hpr.inter had)
  have e_existsQ : extension (R' := R') (existsQSet G) heq = existsQSet T := by
    show extension (R' := R') {p : Fin (k + ℓ + 1 + 1) → R |
      ∃ yv : Fin (k + ℓ) → R, Fin.append p yv ∈ graphBlockSet G ∩ ball1Set ∩ ball2Set} _ = _
    rw [ext_exists_append ((hgb.inter hb1).inter hb2) heq, ext_inter (hgb.inter hb1) hb2,
      ext_inter hgb hb1, ext_graphBlockSet hG, ext_ball1Set, ext_ball2Set]
    rfl
  have e_allDlt : extension (R' := R') (allDltSet G) had = allDltSet T := by
    show extension (R' := R') {q : Fin (k + ℓ + 1) → R |
      ∃ dlt : Fin 1 → R, Fin.append q dlt ∈ posDltSet ∩ (existsQSet G)ᶜ}ᶜ _ = _
    rw [ext_compl (IsSemialgebraicSet.exists_append_right (hpd.inter heq.compl)),
      ext_exists_append (hpd.inter heq.compl) (IsSemialgebraicSet.exists_append_right (hpd.inter heq.compl)),
      ext_inter hpd heq.compl, ext_posDltSet, ext_compl heq, e_existsQ]
    rfl
  have e_dscPoint : extension (R' := R') (dscPointSet G) hdp = dscPointSet T := by
    show extension (R' := R') {p : Fin (k + ℓ) → R |
      ∃ rr : Fin 1 → R, Fin.append p rr ∈ posRSet ∩ allDltSet G} _ = _
    rw [ext_exists_append (hpr.inter had) hdp, ext_inter hpr had, ext_posRSet, e_allDlt]
    rfl
  show extension (R' := R') {x : Fin k → R | ∃ u : Fin ℓ → R, Fin.append x u ∈ G ∩ dscPointSet G} _ = _
  refine (ext_exists_append (hG.inter hdp) _).trans ?_
  rw [ext_inter hG hdp, e_dscPoint]
  rfl

/-- `Ext A = ∅ ↔ A = ∅` for semialgebraic `A`. -/
theorem ext_eq_empty_iff {n : ℕ} {A : Set (Fin n → R)} (hA : IsSemialgebraicSet A) :
    extension (R' := R') A hA = ∅ ↔ A = ∅ := by
  constructor
  · intro h; exact ext_inj hA IsSemialgebraicSet.empty (h.trans (ext_empty IsSemialgebraicSet.empty).symm)
  · rintro rfl; exact ext_empty hA

/-- **BPR Exercise 3.1(b).** A semialgebraic function `f : S → T` is continuous iff its extension
`f'` (Proposition 2.89) is continuous. -/
theorem ext_continuousOn {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    {f' : (Fin k → R') → (Fin ℓ → R')} (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf = funGraph (extension (R' := R') S hS) f') :
    ContinuousOn f S ↔ ContinuousOn f' (extension (R' := R') S hS) := by
  rw [← dscGraph_funGraph_eq_empty_iff, ← dscGraph_funGraph_eq_empty_iff, ← hgraph,
    ← ext_dscGraph hf, ext_eq_empty_iff]

end ExtB

end Azurite.BPR
