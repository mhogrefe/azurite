import Azurite.BasuPollackRoy.Chapter4.Section4_7.SemialgebraicFunctionC

/-!
# BPR §4.7: complex polynomial loci are semialgebraic over `C`

The realification `Cᵏ ≅ R^{2k}` (`realEquiv`) carries the evaluation of a complex polynomial to a
pair of real polynomials in twice as many variables: the real and imaginary parts of
`aeval (realEquiv.symm w) P` are each polynomial in `w` (`exists_reL_imL_aeval`). Consequently the
zero locus of a complex polynomial is semialgebraic over `C`
(`isSemialgebraicSetC_complexPolyZero`), and a complex polynomial map is semialgebraic over `C`
(`isSemialgebraicFunctionC_complexPolyMap`). This is a reusable building block for the §4.7
semialgebraic-over-`C` framework.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {m : ℕ}

/-! ### STEP 1: product formulas for `Ri.reL` / `Ri.imL` -/

set_option linter.unusedSectionVars false in
/-- Real part of a product in `Ri R`. -/
theorem reL_mul (c d : Ri R) :
    Ri.reL (c * d) = Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.reL_lin]

set_option linter.unusedSectionVars false in
/-- Imaginary part of a product in `Ri R`. -/
theorem imL_mul (c d : Ri R) :
    Ri.imL (c * d) = Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  conv_lhs => rw [← Ri.of_reL_add_of_imL_mul_i c, ← Ri.of_reL_add_of_imL_mul_i d]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
          * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL d)
            + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d) * Ri.i R)
        = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.reL d - Ri.imL c * Ri.imL d)
          + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c * Ri.imL d + Ri.imL c * Ri.reL d) * Ri.i R
      from by
        simp only [map_sub, map_add, map_mul]
        linear_combination (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c)
          * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL d)) * hi2]
  rw [Ri.imL_lin]

/-! ### Helpers: `reL`/`imL` of a reconstructed coordinate -/

set_option linter.unusedSectionVars false in
/-- The real part of the `a`-th reconstructed coordinate is `w (castAdd a)`. -/
theorem reL_symm_apply (w : Fin (m + m) → R) (a : Fin m) :
    Ri.reL ((realEquiv.symm w) a) = w (Fin.castAdd m a) := by
  rw [realEquiv_symm_apply, Ri.reL_lin]

set_option linter.unusedSectionVars false in
/-- The imaginary part of the `a`-th reconstructed coordinate is `w (natAdd a)`. -/
theorem imL_symm_apply (w : Fin (m + m) → R) (a : Fin m) :
    Ri.imL ((realEquiv.symm w) a) = w (Fin.natAdd m a) := by
  rw [realEquiv_symm_apply, Ri.imL_lin]

/-! ### STEP 2: the realification of complex polynomial evaluation is real-polynomial -/

set_option linter.unusedSectionVars false in
/-- **The crux.** The real and imaginary parts of `aeval (realEquiv.symm w) P` are each polynomial in
`w`. Real and imaginary parts are *mutually* recursive (the `mul_X` step crosses them over), so we
prove the existence of both polynomials simultaneously. -/
theorem exists_reL_imL_aeval (P : MvPolynomial (Fin m) (Ri R)) :
    ∃ Qre Qim : MvPolynomial (Fin (m + m)) R, ∀ w : Fin (m + m) → R,
      Ri.reL (aeval (realEquiv.symm w) P) = eval w Qre ∧
      Ri.imL (aeval (realEquiv.symm w) P) = eval w Qim := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨C (Ri.reL a), C (Ri.imL a), fun w => ?_⟩
    simp only [aeval_C, eval_C]
    constructor
    · rw [Algebra.algebraMap_self_apply]
    · rw [Algebra.algebraMap_self_apply]
  | add P' P'' ihP' ihP'' =>
    obtain ⟨Qre', Qim', hQ'⟩ := ihP'
    obtain ⟨Qre'', Qim'', hQ''⟩ := ihP''
    refine ⟨Qre' + Qre'', Qim' + Qim'', fun w => ?_⟩
    obtain ⟨hre', him'⟩ := hQ' w
    obtain ⟨hre'', him''⟩ := hQ'' w
    rw [map_add, eval_add, eval_add, map_add, map_add]
    exact ⟨by rw [hre', hre''], by rw [him', him'']⟩
  | mul_X P' c ihP' =>
    obtain ⟨Qre', Qim', hQ'⟩ := ihP'
    refine ⟨Qre' * X (Fin.castAdd m c) - Qim' * X (Fin.natAdd m c),
            Qre' * X (Fin.natAdd m c) + Qim' * X (Fin.castAdd m c), fun w => ?_⟩
    obtain ⟨hre', him'⟩ := hQ' w
    rw [map_mul, aeval_X]
    constructor
    · rw [reL_mul, reL_symm_apply, imL_symm_apply, hre', him',
        eval_sub, eval_mul, eval_mul, eval_X, eval_X]
    · rw [imL_mul, reL_symm_apply, imL_symm_apply, hre', him',
        eval_add, eval_mul, eval_mul, eval_X, eval_X]

/-! ### STEP 3: consequences -/

set_option linter.unusedSectionVars false in
/-- A complex number is zero iff its real and imaginary parts both vanish. -/
theorem reL_eq_zero_and_imL_eq_zero_iff (u : Ri R) :
    u = 0 ↔ Ri.reL u = 0 ∧ Ri.imL u = 0 := by
  constructor
  · rintro rfl; exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨hre, him⟩
    rw [← Ri.of_reL_add_of_imL_mul_i u, hre, him]
    simp

set_option linter.unusedSectionVars false in
/-- **A complex polynomial zero locus is semialgebraic over `C`.** -/
theorem isSemialgebraicSetC_complexPolyZero (P : MvPolynomial (Fin m) (Ri R)) :
    IsSemialgebraicSetC {z : Fin m → Ri R | aeval z P = 0} := by
  obtain ⟨Qre, Qim, hQ⟩ := exists_reL_imL_aeval P
  rw [IsSemialgebraicSetC, Equiv.image_eq_preimage_symm]
  have hset : (realEquiv.symm ⁻¹' {z : Fin m → Ri R | aeval z P = 0})
      = {w : Fin (m + m) → R | eval w Qre = 0} ∩ {w | eval w Qim = 0} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff,
      reL_eq_zero_and_imL_eq_zero_iff]
    rw [(hQ w).1, (hQ w).2]
  rw [hset]
  exact (IsSemialgebraicSet.eqZero Qre).inter (IsSemialgebraicSet.eqZero Qim)

set_option linter.unusedSectionVars false in
/-- **A complex polynomial map is semialgebraic over `C`.** For polynomials
`P : Fin n → MvPolynomial (Fin m) (Ri R)`, the map `g z b = aeval z (P b)` is semialgebraic over `C`
on all of `Cᵐ`: its graph is the intersection over output coordinates `b` of the complex zero loci
`{p | aeval p (X_{m+b} - rename(P b)) = 0}`. -/
theorem isSemialgebraicFunctionC_complexPolyMap {n : ℕ}
    (P : Fin n → MvPolynomial (Fin m) (Ri R)) :
    IsSemialgebraicFunctionC (Set.univ : Set (Fin m → Ri R))
      (fun z => fun b => aeval z (P b)) := by
  classical
  rw [IsSemialgebraicFunctionC]
  have hgraph : complexFunGraph (Set.univ : Set (Fin m → Ri R)) (fun z => fun b => aeval z (P b))
      = ⋂ b ∈ (Finset.univ : Finset (Fin n)),
          {p : Fin (m + n) → Ri R |
            aeval p (X (Fin.natAdd m b) - rename (Fin.castAdd n) (P b)) = 0} := by
    ext p
    simp only [complexFunGraph, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_iInter,
      Finset.mem_univ, forall_true_left, map_sub, aeval_X, aeval_rename, sub_eq_zero,
      funext_iff, Function.comp_apply]
  rw [hgraph]
  exact IsSemialgebraicSetC.biInter_finset _ (fun b _ => isSemialgebraicSetC_complexPolyZero _)

end Azurite.BPR.Chapter4
