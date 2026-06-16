import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_51

/-!
# BPR Remark 4.52: the non-negativity sign condition does not imply real roots

The sign condition `sDisc_{p-2}(P) ≥ 0 ∧ ⋯ ∧ sDisc_0(P) ≥ 0` does NOT imply that `P` has
all its roots in `R`. The witness is `P = X^4 + 1`: it has no real root (`x^4 + 1 > 0`),
yet `sDisc_2(P) = sDisc_1(P) = 0` and `sDisc_0(P) = 256 > 0`, so all three
subdiscriminants `sDisc_2, sDisc_1, sDisc_0` are `≥ 0` while `P` does not split over `R`.

We formalize here the tractable algebraic core — `X^4 + 1` does not split over `R`. The
concrete subdiscriminant values `sDisc_2 = sDisc_1 = 0`, `sDisc_0 = 256` are a heavy
determinant computation over the abstract field `R` (`sDisc_0` is a `7 × 7` Sylvester–
Habicht determinant); they are **deferred** until the computable `Az*` subdiscriminant
machinery (cf. Example 4.12, `bareissDet` of the Newton matrix) together with a bridge to
the abstract `sDiscK` can verify them by computation.

(The set of polynomials with all roots in `R` is the closure of the set `sDisc_i(P) > 0`,
but is strictly contained in the relaxed set `sDisc_i(P) ≥ 0` — a new occurrence of the
fact that the closure of a semialgebraic set is not obtained by relaxing the defining
sign conditions, cf. Remark 3.2.)
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open _root_.Polynomial

section

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- **Remark 4.52** (tractable core). `X^4 + 1` has no roots in `R`: it does not split
over `R`. This witnesses that the relaxed sign condition `sDisc_i(P) ≥ 0` does not imply
all roots are in `R` — the subdiscriminants of `X^4 + 1` are `sDisc_2 = sDisc_1 = 0` and
`sDisc_0 = 256 > 0` (all `≥ 0`); those numeric values are deferred to the computable
`Az*` layer (see the module docstring). -/
theorem remark_4_52 : ¬ Polynomial.Splits (X ^ 4 + 1 : R[X]) := by
  have hne : (X ^ 4 + 1 : R[X]) ≠ 0 := (monic_X_pow_add_C (1 : R) (by norm_num)).ne_zero
  have hnd : (X ^ 4 + 1 : R[X]).natDegree = 4 := by compute_degree!
  rw [Polynomial.splits_iff_card_roots]
  have hroots : (X ^ 4 + 1 : R[X]).roots = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at hx
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]
  rw [hroots, Multiset.card_zero, hnd]
  norm_num

end

end Azurite.BPR.Chapter4
