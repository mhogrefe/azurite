import Azurite.BasuPollackRoy.Chapter2.Section2_5.EvenRootIsSemialgebraic

/-! # Rational powers are semialgebraic on `[0, ∞)`

(Not in BPR.) For a rational `q ≥ 0`, the power function `x ↦ x^q` is semialgebraic on
`[0, ∞)`. Writing `q = a/b` (`a = q.num`, `b = q.den`), `x^q` is the unique nonnegative
`b`-th root of `x^a`, so its graph `{(x, y) | 0 ≤ y ∧ y^b = x^a}` (with `x ≥ 0`) is
semialgebraic. This reuses the nonnegative-root machinery from `EvenRootIsSemialgebraic`.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- `x^q` for `x ≥ 0` and rational `q`: the nonnegative `q.den`-th root of `x^(q.num)`,
valued in `Fin 1 → R`. -/
noncomputable def ratPow (q : ℚ) : (Fin 1 → R) → (Fin 1 → R) :=
  fun x _ => (exists_root_total q.den_pos.ne' ((x 0) ^ q.num.toNat)).choose

/-- Defining property of `ratPow`: for `x ≥ 0`, `ratPow q x 0` is nonnegative and its
`q.den`-th power is `x^(q.num)`. -/
theorem ratPow_spec (q : ℚ) (x : Fin 1 → R) (hx : 0 ≤ x 0) :
    0 ≤ ratPow q x 0 ∧ (ratPow q x 0) ^ q.den = (x 0) ^ q.num.toNat :=
  (exists_root_total q.den_pos.ne' ((x 0) ^ q.num.toNat)).choose_spec (pow_nonneg hx _)

/-- **The rational power `x ↦ x^q` (`q ≥ 0`) is semialgebraic on `[0, ∞)`.** Its graph is the
intersection of `{x ≥ 0}`, `{y ≥ 0}`, and the zero set of `X_2^{q.den} - X_1^{q.num}`. -/
theorem ratPow_isSemialgebraicFunction (q : ℚ) (_hq : 0 ≤ q) :
    IsSemialgebraicFunction {x : Fin 1 → R | 0 ≤ x 0} (ratPow (R := R) q) := by
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph {x : Fin 1 → R | 0 ≤ x 0} (ratPow q)
      = {z : Fin 2 → R | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 1 ^ q.den = z 0 ^ q.num.toNat} := by
    ext z
    rw [mem_funGraph]
    constructor
    · rintro ⟨ha, hb⟩
      have ha0 : (0 : R) ≤ z 0 := by
        have h : (0 : R) ≤ (z ∘ Fin.castAdd 1) 0 := ha
        rwa [Function.comp_apply, hcidx] at h
      have hspec := ratPow_spec q (z ∘ Fin.castAdd 1) (by rw [Function.comp_apply, hcidx]; exact ha0)
      rw [Function.comp_apply, hcidx] at hspec
      have hb0 : z 1 = ratPow q (z ∘ Fin.castAdd 1) 0 := by
        have h := congrFun hb 0
        rwa [Function.comp_apply, hnidx] at h
      refine ⟨ha0, ?_, ?_⟩
      · rw [hb0]; exact hspec.1
      · rw [hb0]; exact hspec.2
    · rintro ⟨hz0, hz1, hz1k⟩
      have hspec := ratPow_spec q (z ∘ Fin.castAdd 1) (by rw [Function.comp_apply, hcidx]; exact hz0)
      rw [Function.comp_apply, hcidx] at hspec
      refine ⟨?_, ?_⟩
      · show (0 : R) ≤ (z ∘ Fin.castAdd 1) 0
        rwa [Function.comp_apply, hcidx]
      · funext i; rw [Subsingleton.elim i 0]
        show (z ∘ Fin.natAdd 1) 0 = ratPow q (z ∘ Fin.castAdd 1) 0
        rw [Function.comp_apply, hnidx]
        exact (pow_left_inj₀ hz1 hspec.1 q.den_pos.ne').mp (by rw [hz1k, hspec.2])
  have hsemialg : IsSemialgebraicSet
      {z : Fin 2 → R | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 1 ^ q.den = z 0 ^ q.num.toNat} := by
    have heq : {z : Fin 2 → R | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 1 ^ q.den = z 0 ^ q.num.toNat}
        = {z | MvPolynomial.eval z (X 0) ≥ 0} ∩ ({z | MvPolynomial.eval z (X 1) ≥ 0} ∩
            {z | MvPolynomial.eval z (X 1 ^ q.den - X 0 ^ q.num.toNat) = 0}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, MvPolynomial.eval_X, map_sub,
        MvPolynomial.eval_pow, sub_eq_zero, ge_iff_le]
    rw [heq]
    exact (IsSemialgebraicSet.geZero _).inter
      ((IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.eqZero _))
  show IsSemialgebraicSet (funGraph {x : Fin 1 → R | 0 ≤ x 0} (ratPow q))
  rw [hgraph]; exact hsemialg

end Azurite.BPR
