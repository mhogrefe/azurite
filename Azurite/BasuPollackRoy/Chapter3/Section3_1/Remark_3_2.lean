import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_1

/-! # BPR §3.1, Remark 3.2 — the closure is *not* obtained by relaxing strict inequalities

It is tempting to think the closure of a semialgebraic set is obtained by relaxing the strict
inequalities describing it; this is mistaken. With `S = {x ∈ R | x³ − x² > 0}` (which equals the
ray `(1, ∞)`, since `x³ − x² = x²(x − 1)`), the closure is **not** `T = {x | x³ − x² ≥ 0}` — because
`0 ∈ T` yet `0 ∉ S̄`. In fact `S̄ = {x | x³ − x² ≥ 0 ∧ x ≥ 1} = [1, ∞)`
(`closure_remarkS_eq`). -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The polynomial `x³ − x²` of Remark 3.2. -/
noncomputable def remarkPoly : MvPolynomial (Fin 1) R := X 0 ^ 3 - X 0 ^ 2

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem eval_remarkPoly (x : Fin 1 → R) : eval x remarkPoly = (x 0) ^ 3 - (x 0) ^ 2 := by
  simp only [remarkPoly, map_sub, map_pow, eval_X]

/-- `S = {x ∈ R | x³ − x² > 0}`. -/
def remarkS : Set (Fin 1 → R) := {x | eval x remarkPoly > 0}

/-- `T = {x ∈ R | x³ − x² ≥ 0}`, the set obtained by relaxing the strict inequality of `S`. -/
def remarkT : Set (Fin 1 → R) := {x | eval x remarkPoly ≥ 0}

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem isSemialgebraicSet_remarkS : IsSemialgebraicSet (remarkS (R := R)) :=
  IsSemialgebraicSet.gtZero remarkPoly

omit [IsRealClosed R] in
theorem isSemialgebraicSet_remarkT : IsSemialgebraicSet (remarkT (R := R)) :=
  IsSemialgebraicSet.geZero remarkPoly

omit [IsRealClosed R] in
/-- `S = (1, ∞)`: `x³ − x² > 0` iff `x > 1`. -/
theorem mem_remarkS {x : Fin 1 → R} : x ∈ remarkS ↔ 1 < x 0 := by
  rw [remarkS, Set.mem_setOf_eq, eval_remarkPoly]
  constructor
  · intro h; nlinarith [sq_nonneg (x 0), h]
  · intro h
    nlinarith [mul_pos (mul_pos (show (0 : R) < x 0 by linarith) (show (0 : R) < x 0 by linarith))
      (show (0 : R) < x 0 - 1 by linarith)]

/-- `S̄ = [1, ∞)`: `x ∈ S̄` iff `x ≥ 1`. -/
theorem mem_closure_remarkS {x : Fin 1 → R} : x ∈ closure remarkS ↔ 1 ≤ x 0 := by
  have hnorm : ∀ a b : Fin 1 → R, euclideanNormSq (a - b) = (a 0 - b 0) ^ 2 := fun a b => by
    simp [euclideanNormSq, Pi.sub_apply]
  rw [mem_closure_iff_ball]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyS, hball⟩ := h (1 - x 0) (by linarith)
    rw [mem_remarkS] at hyS
    rw [hnorm] at hball
    nlinarith [hball, mul_pos (show (0 : R) < y 0 - 1 by linarith)
      (show (0 : R) < y 0 + 1 - 2 * x 0 by linarith)]
  · intro hx r hr
    refine ⟨fun _ => x 0 + r / 2, ?_, ?_⟩
    · rw [mem_remarkS]; show 1 < x 0 + r / 2; linarith
    · rw [hnorm]; show (x 0 + r / 2 - x 0) ^ 2 < r ^ 2; nlinarith [mul_pos hr hr]

/-- BPR's formula for the closure: `S̄ = {x | x³ − x² ≥ 0 ∧ x ≥ 1}`. -/
theorem closure_remarkS_eq :
    closure remarkS = {x : Fin 1 → R | eval x remarkPoly ≥ 0 ∧ 1 ≤ x 0} := by
  ext x
  rw [mem_closure_remarkS, Set.mem_setOf_eq, eval_remarkPoly]
  exact ⟨fun hx => ⟨by nlinarith [sq_nonneg (x 0), hx], hx⟩, fun hx => hx.2⟩

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `0 ∈ T` (the relaxed set contains the origin). -/
theorem zero_mem_remarkT : (0 : Fin 1 → R) ∈ remarkT := by
  rw [remarkT, Set.mem_setOf_eq, eval_remarkPoly]; simp

/-- `0 ∉ S̄`: the origin is not in the closure. -/
theorem zero_not_mem_closure_remarkS : (0 : Fin 1 → R) ∉ closure remarkS := by
  rw [mem_closure_remarkS]; simp

/-- **BPR Remark 3.2.** The closure of `S` is not the relaxation `T`: `0 ∈ T` but `0 ∉ S̄`. -/
theorem closure_remarkS_ne_remarkT : closure remarkS ≠ (remarkT (R := R)) := fun h =>
  zero_not_mem_closure_remarkS (h.symm ▸ zero_mem_remarkT)

end Azurite.BPR
