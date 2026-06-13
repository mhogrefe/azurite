import Azurite.BasuPollackRoy.Chapter3.Section3_5.Translation
import Azurite.BasuPollackRoy.Chapter3.Section3_5.InverseSmoothness

/-! # BPR §3.5 — the Inverse Function Theorem at a base point, with `𝒮^ℓ` inverse

`proposition_3_24_at_sClass` combines the base-point Inverse Function Theorem
(`proposition_3_24_at`, which exposes the Jacobian's pointwise invertibility and the
Lipschitz bound) with the smoothness bootstrap (`isSFunction_inverse`): if `f`'s partial
derivatives are `𝒮^m`, the local inverse is `𝒮^{m+1}`. This is the form consumed by the
Implicit Function Theorem (Theorem 3.25) to obtain the smoothness of the implicit
function. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Inverse Function Theorem at a base point, with `𝒮^{m+1}` inverse.** If `U′` is a
semialgebraic open neighborhood of `z₀`, `f ∈ 𝒮^{m+1}(U′, R^k)` (its partials `g` are
`𝒮^m`), and `df(z₀)` is invertible, then there are semialgebraic open neighborhoods
`U ∋ z₀` (inside `U′`) and `V ∋ f(z₀)` such that `f|_U` is a semialgebraic homeomorphism
onto `V` whose inverse is `𝒮^{m+1}`. -/
theorem proposition_3_24_at_sClass {k : ℕ} {U' : Set (Fin k → R)} {z₀ : Fin k → R}
    {f : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hU'open : IsOpen U') (hU'sa : IsSemialgebraicSet U') (hz₀ : z₀ ∈ U')
    (hf : ∀ l, IsSemialgContinuousOn U' (fun z => f z l))
    (hdiff : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => f w l) U' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn U' (g l j))
    (hdet : IsUnit (jacobianMatrix g z₀).det)
    (m : ℕ) (hgS : ∀ l j, IsSFunction m U' (g l j)) :
    ∃ U V : Set (Fin k → R),
      IsSemialgebraicSet U ∧ IsOpen U ∧ z₀ ∈ U ∧ U ⊆ U' ∧
      IsSemialgebraicSet V ∧ IsOpen V ∧ f z₀ ∈ V ∧
      ∃ finv : (Fin k → R) → (Fin k → R),
        IsSemialgebraicHomeomorphism U V f finv ∧ IsSemialgebraicFunction V finv ∧
        ∀ a, IsSFunction (m + 1) V (fun y => finv y a) := by
  obtain ⟨U, V, hUsa, hUopen, hz₀U, hUsub, hVsa, hVopen, hfz₀V, finv,
    hhomeo, hFinvSa, hdetU, C, hC, hLip⟩ :=
    proposition_3_24_at hU'open hU'sa hz₀ hf hdiff hgsc hdet
  refine ⟨U, V, hUsa, hUopen, hz₀U, hUsub, hVsa, hVopen, hfz₀V, finv,
    hhomeo, hFinvSa, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; intro a; exact a.elim0
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hfinvMaps : Set.MapsTo finv V U := by
    intro y hy
    obtain ⟨x, hxU, hfx⟩ := hhomeo.bijOn.surjOn hy
    rw [← hfx, hhomeo.invOn.1 hxU]
    exact hxU
  have hrinv : ∀ y ∈ V, f (finv y) = y := fun y hy => hhomeo.invOn.2 hy
  have hfinvSC : ∀ a, IsSemialgContinuousOn V (fun y => finv y a) := by
    intro a
    exact ⟨proposition_2_84 hFinvSa (isSemialgContinuousOn_coord hUsa a).1 hfinvMaps,
      (isSemialgContinuousOn_coord hUsa a).2.comp hhomeo.continuousOn_inv hfinvMaps⟩
  have hfU : ∀ l, IsSemialgContinuousOn U (fun x => f x l) :=
    fun l => (hf l).mono hUsa hUsub
  have hgU : ∀ l j, ∀ x ∈ U, HasPartialDerivAtIn (fun w => f w l) U j x (g l j x) :=
    fun l j x hx => (hdiff l j x (hUsub hx)).mono_set hUsub
  have hgscU : ∀ l j, IsSemialgContinuousOn U (g l j) :=
    fun l j => (hgsc l j).mono hUsa hUsub
  have hgSU : ∀ l j, IsSFunction m U (g l j) :=
    fun l j => (hgS l j).mono_set hUsa hUsub
  exact isSFunction_inverse hUopen hVsa hfU hgU hgscU hfinvSC hfinvMaps hrinv hdetU
    C hC hLip m hgSU

end Azurite.BPR
