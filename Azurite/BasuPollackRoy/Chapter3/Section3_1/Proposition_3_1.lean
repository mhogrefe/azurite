import Azurite.BasuPollackRoy.Chapter3.Section3_1.ClosureInterior
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR §3.1 — open/closure/interior reformulations and Proposition 3.1

The euclidean topology on `R^k` admits the familiar metric reformulations:
`U` is open iff every point sits in an open ball *centred at it* contained in `U`
(`isOpen_iff_ball_self`); the closure of `S` is the set of points every ball around which meets `S`
(`mem_closure_iff_ball`); and the interior is the set of points some ball around which lies in `S`
(`mem_interior_iff_ball_self`).

When `S` is semialgebraic these conditions are first-order formulas in the language of ordered
fields (membership in `S` is replaced by a quantifier-free formula describing it, and the bounded
quantifiers `∀x ∈ S` / `∃x ∈ S` by `(Ψ ⇒ ·)` / `(Ψ ∧ ·)`). Quantifier elimination
(Theorem 2.77 / Corollary 2.78) — here in the form that semialgebraic sets are closed under
coordinate projection (`IsSemialgebraicSet.exists_append_right`) and Boolean operations — then gives
**Proposition 3.1**: the closure and the interior of a semialgebraic set are semialgebraic. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Metric reformulations of open, closure, interior -/

/-- **`U` is open iff every point lies in an open ball centred at it contained in `U`.** -/
theorem isOpen_iff_ball_self {k : ℕ} {U : Set (Fin k → R)} :
    IsOpen U ↔ ∀ x ∈ U, ∃ r, 0 < r ∧ openBall x r ⊆ U := by
  rw [isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨c, r, hr, hxc, hsub⟩ := h x hx
    rw [mem_openBall_iff_norm hr] at hxc
    exact ⟨r - euclideanNorm (x - c), by linarith,
      (openBall_subset_openBall hr (by linarith) (by linarith)).trans hsub⟩
  · intro h x hx
    obtain ⟨r, hr, hsub⟩ := h x hx
    exact ⟨x, r, hr, mem_openBall_self x hr, hsub⟩

/-- **Closure via balls.** `x ∈ S̄` iff every ball around `x` meets `S`. -/
theorem mem_closure_iff_ball {k : ℕ} {S : Set (Fin k → R)} {x : Fin k → R} :
    x ∈ closure S ↔ ∀ r, 0 < r → ∃ y ∈ S, euclideanNormSq (y - x) < r ^ 2 := by
  rw [mem_closure_iff]
  constructor
  · intro h r hr
    obtain ⟨y, hyB, hyS⟩ := h (openBall x r) (isOpen_openBall x hr) (mem_openBall_self x hr)
    exact ⟨y, hyS, mem_openBall.mp hyB⟩
  · intro h o hoopen hxo
    rw [isOpen_iff] at hoopen
    obtain ⟨c, ρ, hρ, hxc, hsub⟩ := hoopen x hxo
    rw [mem_openBall_iff_norm hρ] at hxc
    obtain ⟨y, hyS, hylt⟩ := h (ρ - euclideanNorm (x - c)) (by linarith)
    exact ⟨y, hsub ((openBall_subset_openBall hρ (by linarith) (by linarith))
      (mem_openBall.mpr hylt)), hyS⟩

/-- **Interior via balls.** `x ∈ S°` iff some ball around `x` is contained in `S`. -/
theorem mem_interior_iff_ball_self {k : ℕ} {S : Set (Fin k → R)} {x : Fin k → R} :
    x ∈ interior S ↔ ∃ r, 0 < r ∧ ∀ y, euclideanNormSq (y - x) < r ^ 2 → y ∈ S := by
  rw [mem_interior_iff_ball]
  constructor
  · rintro ⟨c, r, hr, hxc, hsub⟩
    rw [mem_openBall_iff_norm hr] at hxc
    refine ⟨r - euclideanNorm (x - c), by linarith, fun y hy => ?_⟩
    exact hsub ((openBall_subset_openBall hr (by linarith) (by linarith)) (mem_openBall.mpr hy))
  · rintro ⟨r, hr, h⟩
    exact ⟨x, r, hr, mem_openBall_self x hr, fun y hy => h y (mem_openBall.mp hy)⟩

/-! ### Closure and interior of a semialgebraic set are semialgebraic -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The polynomial in the variables `(x, r, y) ∈ R^{(k+1)+k}` (with `x ∈ R^k` the centre, `r` the
radius, `y ∈ R^k` the witness) whose value is `‖y − x‖² − r²`. Used to express the ball condition
`‖y − x‖² < r²` as a single sign condition while `x`, `r`, `y` all range as variables. -/
noncomputable def distPoly (k : ℕ) : MvPolynomial (Fin ((k + 1) + k)) R :=
  (∑ i : Fin k, (X (Fin.natAdd (k + 1) i) - X (Fin.castAdd k (Fin.castAdd 1 i))) ^ 2)
    - (X (Fin.castAdd k (Fin.natAdd k 0))) ^ 2

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem eval_distPoly (k : ℕ) (w : Fin ((k + 1) + k) → R) :
    eval w (distPoly k) =
      (∑ i : Fin k, (w (Fin.natAdd (k + 1) i) - w (Fin.castAdd k (Fin.castAdd 1 i))) ^ 2)
        - (w (Fin.castAdd k (Fin.natAdd k 0))) ^ 2 := by
  simp only [distPoly, map_sub, map_sum, map_pow, eval_X]

/-- **BPR Proposition 3.1 (closure).** The closure of a semialgebraic set is semialgebraic. -/
theorem isSemialgebraicSet_closure {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) : IsSemialgebraicSet (closure S) := by
  classical
  -- cylinder over `S` in the variables `(x, r, y)`, and the ball sign-condition `‖y − x‖² < r²`
  set Slift : Set (Fin ((k + 1) + k) → R) := {w | w ∘ Fin.natAdd (k + 1) ∈ S} with hSlift_def
  have hSlift : IsSemialgebraicSet Slift := by
    rw [hSlift_def]; exact IsSemialgebraicSet.comap (Fin.natAdd (k + 1)) hS
  set Close : Set (Fin ((k + 1) + k) → R) := {w | eval w (distPoly k) < 0} with hClose_def
  have hClose : IsSemialgebraicSet Close := by
    rw [hClose_def]; exact IsSemialgebraicSet.ltZero (distPoly k)
  -- `∃ y, (y ∈ S ∧ ‖y − x‖² < r²)`: project the witness `y` away
  set ExistsClose : Set (Fin (k + 1) → R) :=
    {xr | ∃ y : Fin k → R, Fin.append xr y ∈ Slift ∩ Close} with hEC_def
  have hEC : IsSemialgebraicSet ExistsClose := by
    rw [hEC_def]; exact IsSemialgebraicSet.exists_append_right (hSlift.inter hClose)
  -- `r > 0`, then `r > 0 ∧ ∀ y ∈ S, ‖y − x‖² ≥ r²`
  set Pos : Set (Fin (k + 1) → R) :=
    {xr | eval xr (X (Fin.natAdd k (0 : Fin 1))) > 0} with hPos_def
  have hPos : IsSemialgebraicSet Pos := by rw [hPos_def]; exact IsSemialgebraicSet.gtZero _
  set Far : Set (Fin (k + 1) → R) := Pos ∩ ExistsCloseᶜ with hFar_def
  have hFar : IsSemialgebraicSet Far := by rw [hFar_def]; exact hPos.inter hEC.compl
  -- `∃ r > 0, ∀ y ∈ S, ‖y − x‖² ≥ r²`: project the radius `r` away — the complement of the closure
  set NotClosure : Set (Fin k → R) :=
    {x | ∃ rv : Fin 1 → R, Fin.append x rv ∈ Far} with hNC_def
  have hNC : IsSemialgebraicSet NotClosure := by
    rw [hNC_def]; exact IsSemialgebraicSet.exists_append_right hFar
  -- membership characterization of `Far` at `(x, r)`
  have hmem : ∀ (x : Fin k → R) (rv : Fin 1 → R), (Fin.append x rv ∈ Far) ↔
      (0 < rv 0 ∧ ∀ y ∈ S, (rv 0) ^ 2 ≤ euclideanNormSq (y - x)) := by
    intro x rv
    have hSm : ∀ y : Fin k → R, (Fin.append (Fin.append x rv) y ∈ Slift) ↔ y ∈ S := by
      intro y; rw [hSlift_def, Set.mem_setOf_eq, append_comp_natAdd]
    have hCm : ∀ y : Fin k → R,
        (Fin.append (Fin.append x rv) y ∈ Close) ↔ euclideanNormSq (y - x) < (rv 0) ^ 2 := by
      intro y
      rw [hClose_def, Set.mem_setOf_eq, eval_distPoly]
      simp only [Fin.append_left, Fin.append_right]
      rw [show (∑ i, (y i - x i) ^ 2) = euclideanNormSq (y - x) from by
            simp only [euclideanNormSq, Pi.sub_apply], sub_lt_zero]
    rw [hFar_def, Set.mem_inter_iff, hPos_def, Set.mem_setOf_eq, eval_X, Fin.append_right,
      Set.mem_compl_iff, hEC_def, Set.mem_setOf_eq, not_exists]
    refine and_congr_right (fun _ => forall_congr' (fun y => ?_))
    rw [Set.mem_inter_iff, hSm y, hCm y, not_and, not_lt]
  -- closure S = (NotClosure)ᶜ
  have hEq : closure S = NotClosureᶜ := by
    ext x
    rw [Set.mem_compl_iff, hNC_def, Set.mem_setOf_eq, mem_closure_iff_ball, not_exists]
    constructor
    · intro hcl rv hF
      rw [hmem] at hF
      obtain ⟨y, hyS, hlt⟩ := hcl (rv 0) hF.1
      exact absurd (hF.2 y hyS) (not_le.mpr hlt)
    · intro hnot r hr
      by_contra hcon
      push Not at hcon
      exact hnot (fun _ => r) ((hmem x (fun _ => r)).mpr ⟨hr, by simpa using hcon⟩)
  rw [hEq]; exact hNC.compl

/-- **BPR Proposition 3.1 (interior).** The interior of a semialgebraic set is semialgebraic. -/
theorem isSemialgebraicSet_interior {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) : IsSemialgebraicSet (interior S) := by
  have h : interior S = (closure Sᶜ)ᶜ := by rw [closure_compl, compl_compl]
  rw [h]; exact (isSemialgebraicSet_closure hS.compl).compl

/-- **BPR Proposition 3.1.** The closure and the interior of a semialgebraic set are semialgebraic
sets. -/
theorem proposition_3_1 {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet (closure S) ∧ IsSemialgebraicSet (interior S) :=
  ⟨isSemialgebraicSet_closure hS, isSemialgebraicSet_interior hS⟩

end Azurite.BPR
