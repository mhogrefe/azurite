import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicPolynomial
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_7
import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_3
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_85

/-! # BPR §3.3 — the bivariate evaluation `(u, z) ↦ P(u, z)` is semialgebraic and continuous

For `P` with semialgebraic continuous coefficients on `S`, the map `(u, z) ↦ P(u, z) = ∑ᵢ Pᵢ(u) zⁱ`
is a semialgebraic *and continuous* function on the cylinder `S × R ⊆ R^{k+1}`. This is what makes
the graph of an implicit root `{(u, z) | P(u, z) = 0, …}` semialgebraic, and the implicit root itself
continuous (Proposition 3.10).

The proof writes the evaluation as `∑_{i < deg P + 1} ĉᵢ · ẑⁱ`, where `ĉᵢ` is the i-th coefficient
function pulled back along the projection `R^{k+1} → R^k` (semialgebraic and continuous by composition
with a polynomial projection) and `ẑ` is the last coordinate; then closes under the ring of
semialgebraic *continuous* functions (Proposition 3.3). -/

namespace Azurite.BPR

open Polynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A real-valued function continuous in the `ContinuousR` (ε–δ) sense gives a `ContinuousOn` line-
valued function `scalarFun g` on any set. -/
theorem continuousOn_scalarFun_of_continuousR {g : (Fin k → R) → R} (hg : ContinuousR g)
    {A : Set (Fin k → R)} : ContinuousOn (scalarFun g) A := by
  rw [continuousOn_fin_one_iff]
  intro x _ r hr
  obtain ⟨δ, hδ, h⟩ := hg x r hr
  exact ⟨δ, hδ, fun y _ hyd => h y hyd⟩

/-- The **bivariate evaluation** `(u, z) ↦ P(u, z)` as a line-valued function on `R^{k+1}` (first `k`
coordinates `u`, last coordinate `z`). -/
noncomputable def bivariateEval (P : Polynomial ((Fin k → R) → R)) :
    (Fin (k + 1) → R) → (Fin 1 → R) :=
  fun w => constPt ((specializeAt P (w ∘ Fin.castAdd 1)).eval (w (Fin.natAdd k 0)))

/-- **The bivariate evaluation of `P` is semialgebraic and continuous on the cylinder `S × R`** — it
lies in the ring of semialgebraic continuous functions (Proposition 3.3). -/
theorem isSemialgebraicFunction_and_continuousOn_bivariateEval {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) {P : Polynomial ((Fin k → R) → R)}
    (hP : HasSemialgContinuousCoeffs S P) :
    IsSemialgebraicFunction (setProd S (Set.univ : Set (Fin 1 → R))) (bivariateEval P) ∧
      ContinuousOn (bivariateEval P) (setProd S (Set.univ : Set (Fin 1 → R))) := by
  have huniv : IsSemialgebraicSet (Set.univ : Set (Fin 1 → R)) := by
    have he : (Set.univ : Set (Fin 1 → R))
        = {x | MvPolynomial.eval x (0 : MvPolynomial (Fin 1) R) = 0} := by ext x; simp
    rw [he]; exact IsSemialgebraicSet.eqZero 0
  set C := setProd S (Set.univ : Set (Fin 1 → R)) with hCdef
  have hC : IsSemialgebraicSet C := hS.prod huniv
  suffices h : bivariateEval P ∈ continuousSemialgebraicFunctions hC from h
  -- projection onto the first `k` coordinates (the `u`-part), a polynomial map
  set proj : (Fin (k + 1) → R) → (Fin k → R) :=
    polynomialMap (fun j : Fin k => MvPolynomial.X (Fin.castAdd 1 j)) with hproj
  have hproj_app : ∀ w : Fin (k + 1) → R, proj w = w ∘ Fin.castAdd 1 := by
    intro w; funext j; simp [hproj, polynomialMap]
  have hprojsa : IsSemialgebraicFunction C proj := isSemialgebraicFunction_polynomialMap hC _
  have hprojcont : ContinuousOn proj C :=
    (continuous_polynomialMap (fun j : Fin k => MvPolynomial.X (Fin.castAdd 1 j))).continuousOn
  have hprojmaps : Set.MapsTo proj C S := fun w hw => by rw [hproj_app]; exact hw.1
  -- each coefficient function `ĉᵢ` pulled back along `proj` is semialgebraic and continuous on `C`
  have hci : ∀ i, scalarFun (P.coeff i) ∘ proj ∈ continuousSemialgebraicFunctions hC := fun i =>
    ⟨proposition_2_84 hprojsa (hP i).1 hprojmaps, (hP i).2.comp hprojcont hprojmaps⟩
  -- the last coordinate `ẑ` is semialgebraic and continuous on `C`
  have hz : (polyFun (MvPolynomial.X (Fin.natAdd k 0)) : (Fin (k + 1) → R) → (Fin 1 → R))
      ∈ continuousSemialgebraicFunctions hC :=
    ⟨polyFun_isSemialgebraicFunction_on hC _,
      continuousOn_scalarFun_of_continuousR (continuousR_eval (MvPolynomial.X (Fin.natAdd k 0)))⟩
  -- `bivariateEval P = ∑_{i < deg P + 1} ĉᵢ · ẑⁱ`
  have hdecomp : bivariateEval P
      = ∑ i ∈ Finset.range (P.natDegree + 1),
          (scalarFun (P.coeff i) ∘ proj)
            * (polyFun (MvPolynomial.X (Fin.natAdd k 0)) : (Fin (k + 1) → R) → (Fin 1 → R)) ^ i := by
    funext w ι
    have hdeg : (specializeAt P (w ∘ Fin.castAdd 1)).natDegree < P.natDegree + 1 :=
      Nat.lt_succ_of_le Polynomial.natDegree_map_le
    rw [Subsingleton.elim ι (0 : Fin 1), bivariateEval,
      Polynomial.eval_eq_sum_range' hdeg (w (Fin.natAdd k 0))]
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, scalarFun,
      constPt, polyFun, MvPolynomial.eval_X, hproj_app]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [specializeAt, Polynomial.coeff_map, Pi.evalRingHom_apply]
  rw [hdecomp]
  exact (continuousSemialgebraicFunctions hC).sum_mem fun i _ =>
    (continuousSemialgebraicFunctions hC).mul_mem (hci i) (pow_mem hz i)

/-- **The bivariate evaluation of `P` is semialgebraic on the cylinder `S × R`.** -/
theorem isSemialgebraicFunction_bivariateEval {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) :
    IsSemialgebraicFunction (setProd S (Set.univ : Set (Fin 1 → R))) (bivariateEval P) :=
  (isSemialgebraicFunction_and_continuousOn_bivariateEval hS hP).1

/-- **The bivariate evaluation of `P` is continuous on the cylinder `S × R`.** -/
theorem continuousOn_bivariateEval {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) :
    ContinuousOn (bivariateEval P) (setProd S (Set.univ : Set (Fin 1 → R))) :=
  (isSemialgebraicFunction_and_continuousOn_bivariateEval hS hP).2

end Azurite.BPR
