import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezoutDeformation
import Azurite.BasuPollackRoy.Chapter4.Section4_7.AtLeastZerosSemialg
import Azurite.BasuPollackRoy.Chapter3.Section3_4.Theorem_3_20
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Exercise_3_1

/-!
# BPR §4.7, Proposition 4.106: the mixed real–projective witness sets

This file builds the witness sets used to prove relative closedness of the parameter set
`Pm P d γ m` in the interval `(0,1]` (gap (c)).

The reduction `isClosedIn_of_closure_inter_subset` shows it suffices to prove that every point of
`(0,1]` in the euclidean closure of `Pm m` already lies in `Pm m`. The route (curve selection
`theorem_3_19` + projective completeness `projective_curve_limit`) requires the `m` common
projective zeros witnessing `AtLeastZeros` to be available as semialgebraic curves of the parameter.

To that end this file builds:

* the **refined mixed real–projective witness set** `witnessRP`: pairs `((w, r̄), p)` where
  `w ∈ [0,1]`, `p = γ(w)`, and `r̄` realifies `m` homogeneous representatives that are valid common
  zeros of the pencil `S₍p₎` (nonzero, pairwise non-proportional, vanishing). Its
  `IsSemialgebraicSetRP` semialgebraicity (`isSemialgebraicSetRP_witnessRP`) is proven by reusing the
  chart-by-chart machinery of `AtLeastZerosSemialg` (`isSemialgebraicSet_predReal`,
  `mem_predReal_iff`) through the reindex `witReindex`, together with the real-reindex comap lemma
  `isSemialgebraicSetRP_comap_param`. Projecting out the projective factor
  (`IsSemialgebraicSetRP.proj`) yields a *real* semialgebraic witness set `witnessReal`.
* the **bounded, unit-normalized** witness set `Wb`: tuples carrying the parameter `w ∈ [0,1]`
  together with `m` real-realified homogeneous representatives `r a ∈ C^{k+1}`, each a UNIT vector
  (`hermNormSq (r a) = 1`), pairwise non-proportional, and common zeros of the pencil at `γ(w)`.
  Unit-normalization makes `Wb` bounded. `closure Wb` is semialgebraic, closed and bounded;
  **Theorem 3.20** applied to the coordinate projection `projW` produces `projW '' closure Wb`
  closed, which contains `closure (Pm m)`, so the closure point of `Pm m` is produced by
  `exists_closurePt_Wb`. The closed unit constraint passes to the closure point
  (`unit_of_mem_closure_Wb`), and `mkLine_eq_chartMap_div` is the chart presentation of a
  representative line.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

open scoped Azurite.BPR

set_option linter.unusedSectionVars false in
/-- **Reduction of relative closedness to a closure-membership inclusion.** Since `Pm m ⊆ (0,1]`, to
show `Pm m` is closed in `(0,1]` it suffices to prove that every point of `(0,1]` lying in the
(euclidean) closure of `Pm m` is already in `Pm m`. The witnessing closed set is `closure (Pm m)`. -/
theorem isClosedIn_of_closure_inter_subset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (γ : (Fin 1 → R) → complexProjectiveSpace R 1) (m : ℕ)
    (h : intervalSet (R := R) ∩ closure (Pm P d γ m) ⊆ Pm P d γ m) :
    IsClosedIn (intervalSet (R := R)) (Pm P d γ m) := by
  refine ⟨closure (Pm P d γ m), isClosed_closure, ?_⟩
  apply Set.Subset.antisymm
  · intro w hw
    exact ⟨subset_closure hw, Pm_subset_intervalSet P d γ m hw⟩
  · intro w hw
    exact h ⟨hw.2, hw.1⟩

/-! ### The realified per-representative validity predicate on a `ℙ₁` chart -/

variable (m : ℕ)

/-- `RepsValid P d i z r`: the `m` representatives `r : Fin m → Cᵏ⁺¹` are nonzero, pairwise
non-proportional, and are common zeros of the pencil at the parameter line with concrete homogeneous
coordinates `insertNth i 1 z`. By `atLeastZeros_chartMap_iff_exists_rep`, the existence of such
representatives is equivalent to `AtLeastZeros P d (chartMap i z) m`. -/
def RepsValid (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) (z : Fin 1 → Ri R) (r : Fin m → Fin (k + 1) → Ri R) : Prop :=
  (∀ a, r a ≠ 0) ∧
  (∀ a b, a ≠ b → ∃ j l : Fin (k + 1), r a j * r b l ≠ r a l * r b j) ∧
  (∀ a (i' : Fin k), aeval (r a)
    (homotopyPoly P d ((Fin.insertNth i 1 z : Fin 2 → Ri R) 0)
      ((Fin.insertNth i 1 z : Fin 2 → Ri R) 1) i') = 0)

/-- The representatives read off a realified rep vector `y : Fin (M+M) → R` (with `M = m*(k+1)`). -/
noncomputable def repsFromY (y : Fin (m * (k + 1) + m * (k + 1)) → R) :
    Fin m → Fin (k + 1) → Ri R :=
  fun a j => (realEquiv.symm y : Fin (m * (k + 1)) → Ri R) (finProdFinEquiv (a, j))

set_option linter.unusedSectionVars false in
/-- The realified pred set on chart `i`: realified `(ζ, y)` with `y` encoding `m` valid
representatives at the parameter line `chartMap i (realEquiv.symm ζ)`. This is exactly the
pre-projection set used inside `isSemialgebraicSet_chartT`. -/
theorem isSemialgebraicSet_predReal (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) :
    IsSemialgebraicSet
      {v : Fin (2 + (m * (k + 1) + m * (k + 1))) → R |
        v ∘ packReindex m ∈ realEquiv '' {u : Fin (1 + m * (k + 1)) → Ri R |
          (∀ a, packR m u a ≠ 0) ∧
          (∀ a b, a ≠ b →
            ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j) ∧
          (∀ a (i' : Fin k), aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0)}} := by
  have hC := isSemialgebraicSetC_predC m P d i
  rw [IsSemialgebraicSetC] at hC
  exact IsSemialgebraicSet.comap (packReindex m) hC

set_option linter.unusedSectionVars false in
/-- Membership of `predReal` at `Fin.append ζ y` says `RepsValid` of the representatives `repsFromY y`
at the chart-`i` parameter line `realEquiv.symm ζ`. -/
theorem mem_predReal_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) (ζ : Fin 2 → R) (y : Fin (m * (k + 1) + m * (k + 1)) → R) :
    Fin.append ζ y ∈ {v : Fin (2 + (m * (k + 1) + m * (k + 1))) → R |
        v ∘ packReindex m ∈ realEquiv '' {u : Fin (1 + m * (k + 1)) → Ri R |
          (∀ a, packR m u a ≠ 0) ∧
          (∀ a b, a ≠ b →
            ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j) ∧
          (∀ a (i' : Fin k), aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0)}}
      ↔ RepsValid m P d i (realEquiv.symm ζ) (repsFromY m y) := by
  classical
  simp only [Set.mem_ofPred_eq]
  rw [append_comp_packReindex, realEquiv.injective.mem_set_image]
  set u : Fin (1 + m * (k + 1)) → Ri R :=
    Fin.append (realEquiv.symm ζ) (realEquiv.symm y) with hu
  have hpackR : ∀ a, packR m u a = repsFromY m y a := by
    intro a; funext j
    rw [packR, hu, Fin.append_right, repsFromY]
  have hz : (fun _ : Fin 1 => packZ m u) = (realEquiv.symm ζ : Fin 1 → Ri R) := by
    funext s
    have hs : s = 0 := Subsingleton.elim _ _
    subst hs
    rw [packZ, hu]
    show Fin.append (realEquiv.symm ζ : Fin 1 → Ri R) (realEquiv.symm y) 0
      = (realEquiv.symm ζ : Fin 1 → Ri R) 0
    rw [show (0 : Fin (1 + m * (k + 1)))
          = Fin.castAdd (m * (k + 1)) (0 : Fin 1) by
        apply Fin.ext; simp only [Fin.val_zero, Fin.val_castAdd], Fin.append_left]
  rw [RepsValid]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a => by rw [← hpackR]; exact h1 a,
      fun a b hab => by rw [← hpackR, ← hpackR]; exact h2 a b hab, fun a i' => ?_⟩
    have := h3 a i'
    rw [aeval_jointSubst, hpackR, hz] at this
    exact this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a => by rw [hpackR]; exact h1 a,
      fun a b hab => by rw [hpackR, hpackR]; exact h2 a b hab, fun a i' => ?_⟩
    rw [aeval_jointSubst, hpackR, hz]
    exact h3 a i'

set_option linter.unusedSectionVars false in
/-- `RepsValid` exactly witnesses `AtLeastZeros` on the chart. -/
theorem atLeastZeros_chartMap_iff_repsValid (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i)) (i : Fin 2) (z : Fin 1 → Ri R) :
    AtLeastZeros P d (chartMap i z) m ↔ ∃ r : Fin m → Fin (k + 1) → Ri R, RepsValid m P d i z r :=
  atLeastZeros_chartMap_iff_exists_rep P d hP i z m

set_option linter.unusedSectionVars false in
/-- **Real reindex comap for `IsSemialgebraicSetRP`.** If `T ⊆ Rᵖ × ℙ_n(C)` is semialgebraic-RP and
`g : Fin q → Fin p` is a coordinate reindex, then `{tp : Rᵠ × ℙ_n | (tp.1 ∘ g, tp.2) ∈ T}` is
semialgebraic-RP. -/
theorem isSemialgebraicSetRP_comap_param {n p q : ℕ}
    {T : Set ((Fin q → R) × complexProjectiveSpace R n)} (hT : IsSemialgebraicSetRP T)
    (g : Fin q → Fin p) :
    IsSemialgebraicSetRP
      {tp : (Fin p → R) × complexProjectiveSpace R n | (tp.1 ∘ g, tp.2) ∈ T} := by
  intro i
  -- Build the reindex `G' : Fin (q+(n+n)) → Fin (p+(n+n))`:
  -- castAdd-block via `g`, natAdd-block identically.
  let G' : Fin (q + (n + n)) → Fin (p + (n + n)) :=
    Fin.addCases (fun a : Fin q => Fin.castAdd (n + n) (g a))
      (fun b : Fin (n + n) => Fin.natAdd p b)
  have hcomap := IsSemialgebraicSet.comap G' (hT i)
  convert hcomap using 1
  ext w
  simp only [Set.mem_ofPred_eq]
  have hcast : (w ∘ Fin.castAdd (n + n)) ∘ g = (w ∘ G') ∘ Fin.castAdd (n + n) := by
    funext a; simp only [Function.comp_apply, G', Fin.addCases_left]
  have hnat : w ∘ Fin.natAdd p = (w ∘ G') ∘ Fin.natAdd q := by
    funext b; simp only [Function.comp_apply, G', Fin.addCases_right]
  rw [hcast, hnat]

/-! ### The refined mixed real–projective witness set -/

/-- The reindex carrying the chart-`i` RP pullback layout
`[param-block (1+(M+M)) , ζ (2)]` to the `predReal` layout `[ζ (2), reps (M+M)]`. -/
def witReindex :
    Fin (2 + (m * (k + 1) + m * (k + 1))) →
      Fin ((1 + (m * (k + 1) + m * (k + 1))) + (1 + 1)) :=
  Fin.addCases
    (fun s : Fin 2 => Fin.natAdd (1 + (m * (k + 1) + m * (k + 1))) s)
    (fun t : Fin (m * (k + 1) + m * (k + 1)) =>
      Fin.castAdd (1 + 1) (Fin.natAdd 1 t))

set_option linter.unusedSectionVars false in
/-- Composing the chart-`i` RP pullback point `v` with `witReindex` recovers
`Fin.append (ζ-block) (rep-block)`. -/
theorem comp_witReindex (v : Fin ((1 + (m * (k + 1) + m * (k + 1))) + (1 + 1)) → R) :
    v ∘ witReindex m
      = Fin.append (v ∘ Fin.natAdd (1 + (m * (k + 1) + m * (k + 1))))
          ((v ∘ Fin.castAdd (1 + 1)) ∘ Fin.natAdd 1) := by
  funext s
  refine Fin.addCases (fun s => ?_) (fun t => ?_) s
  · rw [Function.comp_apply, witReindex, Fin.addCases_left, Fin.append_left, Function.comp_apply]
  · rw [Function.comp_apply, witReindex, Fin.addCases_right, Fin.append_right, Function.comp_apply,
      Function.comp_apply]

/-- The chart-independent "the `m` representatives `r` are valid zeros at the projective parameter
`p`": nonzero, pairwise non-proportional, and each a common projective zero of the pencil `S₍p₎`. -/
def RepsValidAt (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) (r : Fin m → Fin (k + 1) → Ri R) : Prop :=
  (∀ a, r a ≠ 0) ∧
  (∀ a b, a ≠ b → ∃ j l : Fin (k + 1), r a j * r b l ≠ r a l * r b j) ∧
  (∀ a (i' : Fin k), aeval (r a) (homotopyPoly P d (p.rep 0) (p.rep 1) i') = 0)

set_option linter.unusedSectionVars false in
/-- On a chart `i` (with `p = chartMap i z`), `RepsValidAt p r ↔ RepsValid i z r`. -/
theorem repsValidAt_chartMap_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) (z : Fin 1 → Ri R) (r : Fin m → Fin (k + 1) → Ri R) :
    RepsValidAt m P d (chartMap i z) r ↔ RepsValid m P d i z r := by
  rw [RepsValidAt, RepsValid]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun i' => ?_
  exact aeval_homotopyPoly_chartMap_iff P d i z (r a) i'

/-- The reads off the single parameter coordinate `w 0` and the representatives from a witness real
point `z : Fin (1 + (M+M)) → R`. -/
def witW (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) : Fin 1 → R :=
  fun _ => z (Fin.castAdd (m * (k + 1) + m * (k + 1)) 0)

/-- The refined witness RP set: pairs `((w, reps-realified), p)` with `w ∈ Icc 0 1`, `p = γ(w)`, and
the `m` realified representatives valid at `p`. Living in `Rᴾ × ℙ₁(C)` with `P = 1 + (M+M)`. -/
def witnessRP (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    Set ((Fin (1 + (m * (k + 1) + m * (k + 1))) → R) × complexProjectiveSpace R 1) :=
  {tp |
    witW m tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧
    tp.2 = γ (witW m tp.1) ∧
    RepsValidAt m P d tp.2 (repsFromY m (tp.1 ∘ Fin.natAdd 1))}

set_option linter.unusedSectionVars false in
/-- The "representatives valid at the projective parameter" condition is `IsSemialgebraicSetRP`. -/
theorem isSemialgebraicSetRP_repsValidAt (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) :
    IsSemialgebraicSetRP
      {tp : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) × complexProjectiveSpace R 1 |
        RepsValidAt m P d tp.2 (repsFromY m (tp.1 ∘ Fin.natAdd 1))} := by
  classical
  intro i
  -- the chart-`i` pullback set
  have heq : {v : Fin ((1 + (m * (k + 1) + m * (k + 1))) + (1 + 1)) → R |
        (v ∘ Fin.castAdd (1 + 1),
            chartMap i (realEquiv.symm (v ∘ Fin.natAdd (1 + (m * (k + 1) + m * (k + 1))))))
          ∈ {tp : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) × complexProjectiveSpace R 1 |
              RepsValidAt m P d tp.2 (repsFromY m (tp.1 ∘ Fin.natAdd 1))}}
      = {v : Fin ((1 + (m * (k + 1) + m * (k + 1))) + (1 + 1)) → R |
          v ∘ witReindex m ∈ {w : Fin (2 + (m * (k + 1) + m * (k + 1))) → R |
            w ∘ packReindex m ∈ realEquiv '' {u : Fin (1 + m * (k + 1)) → Ri R |
              (∀ a, packR m u a ≠ 0) ∧
              (∀ a b, a ≠ b →
                ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j) ∧
              (∀ a (i' : Fin k), aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0)}}} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    rw [repsValidAt_chartMap_iff,
      ← mem_predReal_iff m P d i (v ∘ Fin.natAdd (1 + (m * (k + 1) + m * (k + 1))))
        ((v ∘ Fin.castAdd (1 + 1)) ∘ Fin.natAdd 1),
      ← comp_witReindex]
    exact Iff.rfl
  rw [heq]
  exact IsSemialgebraicSet.comap (witReindex m) (isSemialgebraicSet_predReal m P d i)

set_option linter.unusedSectionVars false in
/-- **The refined witness set is semialgebraic-RP.** -/
theorem isSemialgebraicSetRP_witnessRP (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) :
    IsSemialgebraicSetRP (witnessRP m P d γ) := by
  -- the graph piece, via the real-reindex comap
  have hgraph' :=
    isSemialgebraicSetRP_comap_param (n := 1)
      (T := {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) hgraphRP
      (fun _ : Fin 1 => Fin.castAdd (m * (k + 1) + m * (k + 1)) (0 : Fin 1))
  have hWeq : (witnessRP m P d γ) =
      {tp : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) × complexProjectiveSpace R 1 |
        (tp.1 ∘ (fun _ : Fin 1 => Fin.castAdd (m * (k + 1) + m * (k + 1)) (0 : Fin 1)), tp.2)
          ∈ {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
              tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}}
      ∩ {tp : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) × complexProjectiveSpace R 1 |
          RepsValidAt m P d tp.2 (repsFromY m (tp.1 ∘ Fin.natAdd 1))} := by
    ext tp
    simp only [witnessRP, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · show witW m tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1; exact h1
      · show tp.2 = γ (witW m tp.1); exact h2
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  rw [hWeq]
  exact hgraph'.inter (isSemialgebraicSetRP_repsValidAt m P d)

/-- The **real** witness set: the projection of `witnessRP` onto its real factor. A point
`z : Fin (1 + (M+M)) → R` lies in it iff `witW z ∈ [0,1]` and the realified representatives
`repsFromY (z ∘ natAdd 1)` are valid common zeros of the pencil `S₍γ(witW z)₎`. This is the real
semialgebraic set on which curve selection (`theorem_3_19`) would be run to obtain the `m`
representatives as semialgebraic curves of the parameter. -/
def witnessReal (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    Set (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :=
  {z | ∃ p : complexProjectiveSpace R 1, (z, p) ∈ witnessRP m P d γ}

set_option linter.unusedSectionVars false in
/-- **The real witness set is semialgebraic.** -/
theorem isSemialgebraicSet_witnessReal (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) :
    IsSemialgebraicSet (witnessReal m P d γ) :=
  (isSemialgebraicSetRP_witnessRP m P d γ hgraphRP).proj

set_option linter.unusedSectionVars false in
/-- Membership characterization of the real witness set: the `∃ p` collapses to `p = γ(witW z)`. -/
theorem mem_witnessReal_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :
    z ∈ witnessReal m P d γ
      ↔ witW m z ∈ Set.Icc (0 : Fin 1 → R) 1 ∧
          RepsValidAt m P d (γ (witW m z)) (repsFromY m (z ∘ Fin.natAdd 1)) := by
  constructor
  · rintro ⟨p, h1, h2, h3⟩
    exact ⟨h1, by rw [← h2]; exact h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨γ (witW m z), h1, rfl, h2⟩

set_option linter.unusedSectionVars false in
/-- **The witness set sits over `Pm m`.** A parameter `w ∈ (0,1]` lies in `Pm m` iff it is `witW z`
for some `z ∈ witnessReal`. This is the precise statement that `witnessReal` is the rep-carrying lift
of `Pm m`: applying curve selection to `witnessReal` would furnish the `m` representatives as
semialgebraic curves of the parameter, the missing input to gap (c). -/
theorem mem_Pm_iff_exists_witnessReal (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) (w : Fin 1 → R) :
    w ∈ Pm P d γ m
      ↔ ∃ z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R,
          z ∈ witnessReal m P d γ ∧ witW m z 0 ∈ Set.Ioc (0 : R) 1 ∧ witW m z = w := by
  classical
  constructor
  · rintro ⟨hw, hAZ⟩
    -- `AtLeastZeros (γ w) m` gives representatives `r` valid at `γ w`.
    obtain ⟨i, hi⟩ := exists_mem_chartSet (γ w)
    have hchart : γ w = chartMap i (chartInv i (γ w)) := by
      rw [chartSet_eq] at hi
      exact (chartMap_chartInv i (γ w) hi).symm
    have hAZ' : AtLeastZeros P d (chartMap i (chartInv i (γ w))) m := by rw [← hchart]; exact hAZ
    obtain ⟨r, hr⟩ := (atLeastZeros_chartMap_iff_repsValid m P d hP i (chartInv i (γ w))).mp hAZ'
    -- realify `r` into a rep block `y`, and pack `z`
    set y : Fin (m * (k + 1) + m * (k + 1)) → R :=
      realEquiv (fun idx : Fin (m * (k + 1)) =>
        r (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2) with hy
    have hrepsY : repsFromY m y = r := by
      funext a j
      rw [repsFromY, hy, Equiv.symm_apply_apply]
      show r (finProdFinEquiv.symm (finProdFinEquiv (a, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (a, j))).2 = r a j
      rw [Equiv.symm_apply_apply]
    set z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R := Fin.append (fun _ : Fin 1 => w 0) y with hz
    have hwitW : witW m z = w := by
      funext s
      have hs : s = 0 := Subsingleton.elim _ _
      subst hs
      rw [witW, hz, Fin.append_left]
    have hznat : z ∘ Fin.natAdd 1 = y := by funext t; rw [hz, Function.comp_apply, Fin.append_right]
    have hwIcc : witW m z ∈ Set.Icc (0 : Fin 1 → R) 1 := by
      rw [hwitW, show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
      exact ⟨hw.1.le, hw.2⟩
    have hvalid : RepsValidAt m P d (γ (witW m z)) (repsFromY m (z ∘ Fin.natAdd 1)) := by
      rw [hwitW, hznat, hrepsY, hchart, repsValidAt_chartMap_iff]
      exact hr
    refine ⟨z, (mem_witnessReal_iff m P d γ z).mpr ⟨hwIcc, hvalid⟩, ?_, hwitW⟩
    rw [hwitW]; exact hw
  · rintro ⟨z, hzmem, hioc, hwitW⟩
    rw [← hwitW]
    obtain ⟨hIcc, hvalid⟩ := (mem_witnessReal_iff m P d γ z).mp hzmem
    refine ⟨hioc, ?_⟩
    -- the representatives give `AtLeastZeros`
    obtain ⟨i, hi⟩ := exists_mem_chartSet (γ (witW m z))
    have hchart : γ (witW m z) = chartMap i (chartInv i (γ (witW m z))) := by
      rw [chartSet_eq] at hi
      exact (chartMap_chartInv i (γ (witW m z)) hi).symm
    rw [hchart, atLeastZeros_chartMap_iff_repsValid m P d hP i]
    refine ⟨repsFromY m (z ∘ Fin.natAdd 1), ?_⟩
    rw [← repsValidAt_chartMap_iff, ← hchart]
    exact hvalid

set_option linter.unusedSectionVars false

/-! ### Unit-vector normalization of a nonzero representative -/

/-- `reL`/`imL` of a real-scalar multiple `of(t) • z`: scales each part by `t`. -/
theorem hermNormSq_of_smul (t : R) (v : Fin (k + 1) → Ri R) :
    hermNormSq (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) t • v) = t ^ 2 * hermNormSq v := by
  rw [hermNormSq, hermNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsmul : (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) t • v) j
      = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) t * v j := by
    rw [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, reL_mul, imL_mul, Ri.reL_of, Ri.imL_of]
  ring

/-- Any nonzero vector has a UNIT-Hermitian-norm representative spanning the same projective line:
divide by `√(hermNormSq v)`. -/
theorem exists_unit_rep (v : Fin (k + 1) → Ri R) (hv : v ≠ 0) :
    ∃ u : Fin (k + 1) → Ri R, u ≠ 0 ∧ hermNormSq u = 1 ∧
      ∃ c : Ri R, c ≠ 0 ∧ u = c • v := by
  classical
  -- the scalar `c = (√‖v‖²)⁻¹ : R ↪ Ri R`
  set s : R := sqrt (hermNormSq v) with hs
  have hpos : 0 < hermNormSq v := hermNormSq_pos hv
  have hs2 : s ^ 2 = hermNormSq v := by rw [hs]; exact sq_sqrt (le_of_lt hpos)
  have hs0 : 0 < s := by
    have hge : 0 ≤ s := by rw [hs]; exact sqrt_nonneg _
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exfalso; rw [← h] at hs2; simp at hs2; exact ne_of_gt hpos hs2.symm
  set c : Ri R := AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) s⁻¹ with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    intro h
    have : s⁻¹ = 0 := by
      have := congrArg Ri.reL h
      rwa [Ri.reL_of, map_zero] at this
    exact (inv_ne_zero (ne_of_gt hs0)) this
  refine ⟨c • v, ?_, ?_, c, hcne, rfl⟩
  · intro h
    exact hv (by rwa [smul_eq_zero, or_iff_right hcne] at h)
  · rw [hc, hermNormSq_of_smul, inv_pow, hs2, inv_mul_cancel₀ (ne_of_gt hpos)]

/-! ### The unit constraint as a polynomial identity in the real coordinates -/


/-- `hermNormSq (repsFromY y a)` read in the real coordinates of `y`: the sum over `j` of the squared
real and imaginary parts, which are simply the coordinates `y (castAdd …)` and `y (natAdd …)`. -/
theorem hermNormSq_repsFromY (y : Fin (m * (k + 1) + m * (k + 1)) → R) (a : Fin m) :
    hermNormSq (repsFromY m y a)
      = ∑ j : Fin (k + 1),
          (y (Fin.castAdd (m * (k + 1)) (finProdFinEquiv (a, j))) ^ 2
            + y (Fin.natAdd (m * (k + 1)) (finProdFinEquiv (a, j))) ^ 2) := by
  rw [hermNormSq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [repsFromY, reL_symm_apply, imL_symm_apply]

/-- The polynomial over `Fin (1 + (M+M))` whose evaluation at `z` is
`hermNormSq (repsFromY (z ∘ natAdd 1) a) - 1`. -/
noncomputable def unitPoly (a : Fin m) :
    MvPolynomial (Fin (1 + (m * (k + 1) + m * (k + 1)))) R :=
  (∑ j : Fin (k + 1),
      ((X (Fin.natAdd 1 (Fin.castAdd (m * (k + 1)) (finProdFinEquiv (a, j))))) ^ 2
        + (X (Fin.natAdd 1 (Fin.natAdd (m * (k + 1)) (finProdFinEquiv (a, j))))) ^ 2)) - 1

theorem eval_unitPoly (a : Fin m) (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :
    eval z (unitPoly m a) = hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) - 1 := by
  rw [unitPoly, hermNormSq_repsFromY, map_sub, map_one, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_pow, map_pow, eval_X, eval_X, Function.comp_apply, Function.comp_apply]

/-- The unit-constraint locus on the witness real coordinates: every representative `a` has unit
Hermitian norm. Semialgebraic (a finite intersection of polynomial-equation loci). -/
theorem isSemialgebraicSet_unitLocus :
    IsSemialgebraicSet
      {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R |
        ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1} := by
  classical
  have heq : {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R |
        ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1}
      = ⋂ a ∈ (Finset.univ : Finset (Fin m)),
          {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R | eval z (unitPoly m a) = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left, eval_unitPoly,
      sub_eq_zero]
  rw [heq]
  exact IsSemialgebraicSet.iInter_finset _ (fun a _ => IsSemialgebraicSet.eqZero _)

/-! ### The bounded unit-normalized witness set `Wb` -/

/-- The bounded unit-normalized witness set: the real witness set `witnessReal` intersected with the
unit constraint. Its points carry the parameter `w` together with `m` unit-Hermitian-norm,
pairwise non-proportional representatives that are common zeros of the pencil at `γ(w)`. -/
def Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    Set (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :=
  witnessReal m P d γ ∩
    {z | ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1}

theorem mem_Wb_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :
    z ∈ Wb m P d γ
      ↔ (witW m z ∈ Set.Icc (0 : Fin 1 → R) 1 ∧
          RepsValidAt m P d (γ (witW m z)) (repsFromY m (z ∘ Fin.natAdd 1)))
        ∧ (∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1) := by
  rw [Wb, Set.mem_inter_iff, mem_witnessReal_iff, Set.mem_ofPred_eq]

theorem isSemialgebraicSet_Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) :
    IsSemialgebraicSet (Wb m P d γ) :=
  (isSemialgebraicSet_witnessReal m P d γ hgraphRP).inter (isSemialgebraicSet_unitLocus m)

/-! ### `Wb` is bounded -/

/-- The sum over the representative block equals `m` (each representative is a unit vector). -/
theorem sum_rep_block (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R)
    (hunit : ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1) :
    ∑ t : Fin (m * (k + 1) + m * (k + 1)), (z (Fin.natAdd 1 t)) ^ 2 = m := by
  classical
  set y : Fin (m * (k + 1) + m * (k + 1)) → R := z ∘ Fin.natAdd 1 with hy
  -- `∑_t y t² = ∑_a hermNormSq (repsFromY y a) = m`.
  have hsum : ∑ a : Fin m, hermNormSq (repsFromY m y a)
      = ∑ t : Fin (m * (k + 1) + m * (k + 1)), (y t) ^ 2 := by
    have hstep : ∑ a : Fin m, hermNormSq (repsFromY m y a)
        = ∑ a : Fin m, ∑ j : Fin (k + 1),
            (y (Fin.castAdd (m * (k + 1)) (finProdFinEquiv (a, j))) ^ 2
              + y (Fin.natAdd (m * (k + 1)) (finProdFinEquiv (a, j))) ^ 2) :=
      Finset.sum_congr rfl (fun a _ => hermNormSq_repsFromY m y a)
    rw [hstep]
    -- split the target into castAdd/natAdd blocks and reindex by finProdFinEquiv
    rw [Fin.sum_univ_add (f := fun t => y t ^ 2)]
    rw [← Equiv.sum_comp finProdFinEquiv
          (fun idx : Fin (m * (k + 1)) => (y (Fin.castAdd (m * (k + 1)) idx)) ^ 2),
        ← Equiv.sum_comp finProdFinEquiv
          (fun idx : Fin (m * (k + 1)) => (y (Fin.natAdd (m * (k + 1)) idx)) ^ 2)]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
  have hone : ∑ a : Fin m, hermNormSq (repsFromY m y a) = (m : R) := by
    rw [Finset.sum_congr rfl (fun a _ => hunit a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hgoal : ∑ t : Fin (m * (k + 1) + m * (k + 1)), (z (Fin.natAdd 1 t)) ^ 2
      = ∑ t : Fin (m * (k + 1) + m * (k + 1)), (y t) ^ 2 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hy]; rfl
  rw [hgoal, ← hsum, hone]

theorem isBoundedSet_Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    IsBoundedSet (Wb m P d γ) := by
  classical
  have hm0 : (0 : R) ≤ (m : R) := Nat.cast_nonneg m
  refine ⟨sqrt (1 + (m : R)) + 1, by have := sqrt_nonneg (1 + (m : R)); linarith,
    fun z hz => ?_⟩
  rw [mem_closedBall, sub_zero, euclideanNormSq, Fin.sum_univ_add, Fin.sum_univ_one]
  rw [mem_Wb_iff] at hz
  obtain ⟨⟨hIcc, _⟩, hunit⟩ := hz
  -- the parameter coordinate is in [0,1], so its square ≤ 1
  have hparam : (z (Fin.castAdd (m * (k + 1) + m * (k + 1)) 0)) ^ 2 ≤ 1 := by
    have hp : z (Fin.castAdd (m * (k + 1) + m * (k + 1)) (0 : Fin 1)) = (witW m z) 0 := rfl
    rw [hp]
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local] at hIcc
    obtain ⟨h0, h1⟩ := hIcc
    nlinarith [h0, h1]
  have hrep : ∑ t : Fin (m * (k + 1) + m * (k + 1)), (z (Fin.natAdd 1 t)) ^ 2 = m :=
    sum_rep_block m z hunit
  rw [hrep]
  have hsqrt : sqrt (1 + (m : R)) ^ 2 = 1 + m := sq_sqrt (by positivity)
  nlinarith [hparam, sqrt_nonneg (1 + (m : R)), hsqrt, hm0]

/-! ### The projection `proj` and the cover of `Pm m` -/

/-- The coordinate projection extracting the parameter block; agrees with `witW m`. -/
def projW : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) → (Fin 1 → R) :=
  fun z => z ∘ Fin.castAdd (m * (k + 1) + m * (k + 1))

theorem projW_eq_witW (z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) :
    projW m z = witW m z := by
  funext s
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  rfl

/-- **`Pm m ⊆ projW '' Wb`.** Every parameter carrying `m` distinct projective zeros lifts to a
witness with UNIT representatives (each nonzero rep is unit-normalized without changing its line). -/
theorem pm_subset_projW_Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    Pm P d γ m ⊆ projW m '' Wb m P d γ := by
  classical
  intro w hw
  obtain ⟨hw01, hAZ⟩ := hw
  -- chart for `γ w`
  obtain ⟨i, hi⟩ := exists_mem_chartSet (γ w)
  have hchart : γ w = chartMap i (chartInv i (γ w)) := by
    rw [chartSet_eq] at hi
    exact (chartMap_chartInv i (γ w) hi).symm
  have hAZ' : AtLeastZeros P d (chartMap i (chartInv i (γ w))) m := by rw [← hchart]; exact hAZ
  obtain ⟨r, hr⟩ := (atLeastZeros_chartMap_iff_repsValid m P d hP i (chartInv i (γ w))).mp hAZ'
  obtain ⟨hne, hminor, hzero⟩ := hr
  -- unit-normalize each representative; the line (hence validity) is unchanged
  have hunitrep : ∀ a, ∃ u : Fin (k + 1) → Ri R, u ≠ 0 ∧ hermNormSq u = 1 ∧
      ∃ c : Ri R, c ≠ 0 ∧ u = c • r a := fun a => exists_unit_rep (r a) (hne a)
  choose u hune huunit c hcne hueq using hunitrep
  -- the unit reps `u` are still nonzero, pairwise non-proportional, and common zeros
  have hr' : RepsValid m P d i (chartInv i (γ w)) u := by
    refine ⟨hune, ?_, ?_⟩
    · intro a b hab
      obtain ⟨j, l, hjl⟩ := hminor a b hab
      refine ⟨j, l, ?_⟩
      rw [hueq, hueq]
      simp only [Pi.smul_apply, smul_eq_mul]
      intro hcon
      apply hjl
      have hcc : c a * c b ≠ 0 := mul_ne_zero (hcne a) (hcne b)
      have : c a * c b * (r a j * r b l) = c a * c b * (r a l * r b j) := by ring_nf; ring_nf at hcon; linear_combination hcon
      exact mul_left_cancel₀ hcc this
    · intro a i'
      rw [hueq, aeval_smul_isHomogeneous
            (homotopyPoly_isHomogeneous P d hP _ _ i') (c a) (r a),
        mul_eq_zero, or_iff_right (pow_ne_zero _ (hcne a))]
      exact hzero a i'
  -- realify the unit reps `u` into a rep block `y`
  set y : Fin (m * (k + 1) + m * (k + 1)) → R :=
    realEquiv (fun idx : Fin (m * (k + 1)) =>
      u (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2) with hy
  have hrepsY : repsFromY m y = u := by
    funext a j
    rw [repsFromY, hy, Equiv.symm_apply_apply]
    show u (finProdFinEquiv.symm (finProdFinEquiv (a, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (a, j))).2 = u a j
    rw [Equiv.symm_apply_apply]
  set z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R := Fin.append (fun _ : Fin 1 => w 0) y with hz
  have hwitW : witW m z = w := by
    funext s
    have hs : s = 0 := Subsingleton.elim _ _
    subst hs
    rw [witW, hz, Fin.append_left]
  have hznat : z ∘ Fin.natAdd 1 = y := by funext t; rw [hz, Function.comp_apply, Fin.append_right]
  have hwIcc : witW m z ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    rw [hwitW, show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
    exact ⟨hw01.1.le, hw01.2⟩
  have hvalid : RepsValidAt m P d (γ (witW m z)) (repsFromY m (z ∘ Fin.natAdd 1)) := by
    rw [hwitW, hznat, hrepsY, hchart, repsValidAt_chartMap_iff]
    exact hr'
  have hunitc : ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1 := by
    rw [hznat, hrepsY]; exact huunit
  refine ⟨z, (mem_Wb_iff m P d γ z).mpr ⟨⟨hwIcc, hvalid⟩, hunitc⟩, ?_⟩
  rw [projW_eq_witW, hwitW]

/-! ### Step (ii): the closure point of `Pm m` via Theorem 3.20 -/

/-- The projection `projW` is semialgebraic-continuous on any semialgebraic domain (it is a single
coordinate function). -/
theorem isSemialgContinuousOn_projW {D : Set (Fin (1 + (m * (k + 1) + m * (k + 1))) → R)}
    (hD : IsSemialgebraicSet D) (j : Fin 1) :
    IsSemialgContinuousOn D (fun z => projW m z j) := by
  have hco : scalarFun (fun z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R => projW m z j)
      = polyFun (X (Fin.castAdd (m * (k + 1) + m * (k + 1)) j)) := by
    funext z s
    simp only [scalarFun, polyFun, constPt, projW, Function.comp_apply, eval_X]
  refine ⟨?_, ?_⟩
  · rw [hco]; exact polyFun_isSemialgebraicFunction_on hD _
  · rw [hco]
    exact (continuous_iff_components.mpr fun _ =>
      continuousR_eval (X (Fin.castAdd (m * (k + 1) + m * (k + 1)) j))).continuousOn

/-- **Step (ii): the closure point.** For `t₀ ∈ (0,1] ∩ closure (Pm m)`, there is `ζ* ∈ closure Wb`
projecting to `t₀`. This uses Theorem 3.20: `projW '' closure Wb` is closed and contains `Pm m`,
hence contains `closure (Pm m)`. The closure point is produced independently of curve selection. -/
theorem exists_closurePt_Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1})
    {t₀ : Fin 1 → R} (ht₀ : t₀ ∈ closure (Pm P d γ m)) :
    ∃ ζ : Fin (1 + (m * (k + 1) + m * (k + 1))) → R, ζ ∈ closure (Wb m P d γ) ∧ projW m ζ = t₀ := by
  classical
  have : Nonempty (Fin (1 + (m * (k + 1) + m * (k + 1)))) := ⟨0⟩
  have : Nonempty (Fin 1) := ⟨0⟩
  -- `closure Wb` is semialgebraic, closed, bounded.
  have hWbsa : IsSemialgebraicSet (Wb m P d γ) := isSemialgebraicSet_Wb m P d γ hgraphRP
  have hclsa : IsSemialgebraicSet (closure (Wb m P d γ)) := isSemialgebraicSet_closure hWbsa
  have hclcl : IsClosed (closure (Wb m P d γ)) := isClosed_closure
  have hclbd : IsBoundedSet (closure (Wb m P d γ)) := by
    obtain ⟨M, hM, hsub⟩ := isBoundedSet_Wb m P d γ
    refine ⟨M, hM, ?_⟩
    have hballcl : IsClosed (closedBall (0 : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) M) :=
      isClosed_closedBall 0 M
    exact closure_minimal hsub hballcl
  -- apply Theorem 3.20 to `projW`
  have h320 := theorem_3_20 (closure (Wb m P d γ)) hclsa hclcl hclbd (projW m)
    (fun j => isSemialgContinuousOn_projW m hclsa j)
  have hclosedImg : IsClosed (projW m '' closure (Wb m P d γ)) := h320.1
  -- `Pm m ⊆ projW '' Wb ⊆ projW '' closure Wb`
  have hPmsub : Pm P d γ m ⊆ projW m '' closure (Wb m P d γ) :=
    (pm_subset_projW_Wb m P d hP γ).trans (Set.image_mono subset_closure)
  -- so `closure (Pm m) ⊆ projW '' closure Wb`
  have hclsub : closure (Pm P d γ m) ⊆ projW m '' closure (Wb m P d γ) :=
    closure_minimal hPmsub hclosedImg
  obtain ⟨ζ, hζcl, hζeq⟩ := hclsub ht₀
  exact ⟨ζ, hζcl, hζeq⟩

/-- The unit constraint is a CLOSED condition: it holds on `closure Wb`, in particular at the
closure point `ζ*`. Hence the limit representatives are nonzero unit vectors. -/
theorem unit_of_mem_closure_Wb (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    {ζ : Fin (1 + (m * (k + 1) + m * (k + 1))) → R} (hζ : ζ ∈ closure (Wb m P d γ)) :
    ∀ a : Fin m, hermNormSq (repsFromY m (ζ ∘ Fin.natAdd 1) a) = 1 := by
  classical
  -- the unit-locus is closed (algebraic); `Wb ⊆ unit-locus`; so `closure Wb ⊆ unit-locus`.
  have hUclosed : IsClosed
      {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R |
        ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1} := by
    have heq : {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R |
          ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1}
        = ⋂ a : Fin m, {z | eval z (unitPoly m a) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, eval_unitPoly, sub_eq_zero]
    rw [heq]
    refine isClosed_iInter fun a => ?_
    have hcont : Continuous (fun z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R =>
        (fun _ : Fin 1 => eval z (unitPoly m a))) :=
      continuous_iff_components.mpr (fun _ => continuousR_eval (unitPoly m a))
    have heq2 : {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R | eval z (unitPoly m a) = 0}
        = (fun z => (fun _ : Fin 1 => eval z (unitPoly m a))) ⁻¹' {(0 : Fin 1 → R)} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; funext s; exact h
      · intro h; exact congrFun h 0
    rw [heq2]
    exact (isClosed_singleton).preimage hcont
  have hsub : Wb m P d γ ⊆
      {z : Fin (1 + (m * (k + 1) + m * (k + 1))) → R |
        ∀ a : Fin m, hermNormSq (repsFromY m (z ∘ Fin.natAdd 1) a) = 1} := by
    intro z hz; exact ((mem_Wb_iff m P d γ z).mp hz).2
  exact (closure_minimal hsub hUclosed) hζ

/-! ### Continuity of `mkLine` along a curve via the chart `j₀` -/

/-- For `v j₀ ≠ 0`, the line `mkLine v` is the chart-`j₀` image of the affine ratios
`fun j => v (j₀.succAbove j) / v j₀`. -/
theorem mkLine_eq_chartMap_div {n : ℕ} (v : Fin (n + 1) → Ri R) (hv : v ≠ 0) (j₀ : Fin (n + 1))
    (hvj : v j₀ ≠ 0) :
    mkLine v hv = chartMap j₀ (fun j => v (j₀.succAbove j) / v j₀) := by
  classical
  have hrepj : (mkLine v hv).rep j₀ ≠ 0 := by
    obtain ⟨c, hc, hrep⟩ := exists_rep_smul v hv
    rw [hrep, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hvj
  rw [← chartMap_chartInv j₀ (mkLine v hv) hrepj]
  congr 1
  funext j
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul v hv
  rw [chartInv, hrep]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc]

end Azurite.BPR.Chapter4
