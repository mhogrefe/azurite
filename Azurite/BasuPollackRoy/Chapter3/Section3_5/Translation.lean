import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_24

/-! # BPR §3.5 — translation toolkit, and the Inverse Function Theorem at a base point

BPR states Proposition 3.24 at the origin ("we can suppose without loss of generality
that `x⁰ = 0` and `f(x⁰) = 0`"); `proposition_3_24` follows the text. This file supplies
the "without loss of generality": translations `z ↦ z + c` are polynomial maps, hence
continuous semialgebraic maps of `R^k`, and all the `𝒮¹` data transports along them —
semialgebraic sets (`IsSemialgebraicSet.preimage_translate`), semialgebraic continuous
scalar functions (`IsSemialgContinuousOn.translate`), and partial derivatives
(`HasPartialDerivAtIn.translate`).

The payoff is `proposition_3_24_at`: the Inverse Function Theorem at an arbitrary base
point `z₀` with no normalization hypotheses — conjugate `f` by the translations
`z ↦ z + z₀` and `w ↦ w + (−f(z₀))`, apply `proposition_3_24` at the origin, and
translate the neighborhoods and the inverse back. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Translations are polynomial maps -/

omit [IsRealClosed R] in
/-- `R^k` itself is a semialgebraic set. -/
theorem isSemialgebraicSet_univ {k : ℕ} :
    IsSemialgebraicSet (Set.univ : Set (Fin k → R)) := by
  have heq : (Set.univ : Set (Fin k → R))
      = {z | eval z (C 1 : MvPolynomial (Fin k) R) > 0} := by
    ext z
    simp
  rw [heq]
  exact IsSemialgebraicSet.gtZero _

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The translation `z ↦ z + c` is the polynomial map with components `Xᵢ + cᵢ`. -/
theorem translate_eq_polynomialMap {k : ℕ} (c : Fin k → R) :
    (fun z : Fin k → R => z + c) = polynomialMap (fun i => X i + C (c i)) := by
  funext z i
  simp [polynomialMap]

/-- Translations of `R^k` are continuous. -/
theorem continuous_translate {k : ℕ} (c : Fin k → R) :
    Continuous (fun z : Fin k → R => z + c) := by
  rw [translate_eq_polynomialMap]
  exact continuous_polynomialMap _

omit [IsRealClosed R] in
/-- Translations of `R^k` are semialgebraic functions. -/
theorem isSemialgebraicFunction_translate_univ {k : ℕ} (c : Fin k → R) :
    IsSemialgebraicFunction Set.univ (fun z : Fin k → R => z + c) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have heq : (fun z : Fin 0 → R => z + c) = id := by
      funext z
      exact Subsingleton.elim _ _
    rw [heq]
    exact isSemialgebraicFunction_id isSemialgebraicSet_univ
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine isSemialgebraicFunction_of_coords fun j => ?_
  have heq : (fun z : Fin k → R => fun _ : Fin 1 => (z + c) j)
      = polyFun (X j + C (c j)) := by
    funext z i
    simp [polyFun]
  rw [heq]
  exact polyFun_isSemialgebraicFunction_on isSemialgebraicSet_univ _

omit [IsRealClosed R] in
/-- Translations of `R^k` are semialgebraic functions on any semialgebraic domain. -/
theorem isSemialgebraicFunction_translate {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (c : Fin k → R) :
    IsSemialgebraicFunction S (fun z : Fin k → R => z + c) :=
  (isSemialgebraicFunction_translate_univ c).mono hS (Set.subset_univ S)

/-- The translate `S − c` (as the preimage of `S` under `z ↦ z + c`) of a semialgebraic
set is semialgebraic. -/
theorem IsSemialgebraicSet.preimage_translate {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (c : Fin k → R) :
    IsSemialgebraicSet ((fun z : Fin k → R => z + c) ⁻¹' S) := by
  have h := (proposition_2_83 (isSemialgebraicFunction_translate_univ c)).2 hS
  rwa [Set.univ_inter] at h

/-! ### Semialgebraic continuity transports along translations -/

/-- Precomposing a semialgebraic continuous scalar function with a translation. -/
theorem IsSemialgContinuousOn.translate {k : ℕ} {U : Set (Fin k → R)}
    {c' : (Fin k → R) → R} (h : IsSemialgContinuousOn U c') (hU : IsSemialgebraicSet U)
    (c : Fin k → R) :
    IsSemialgContinuousOn ((fun z : Fin k → R => z + c) ⁻¹' U)
      (fun z => c' (z + c)) := by
  have hmaps : Set.MapsTo (fun z : Fin k → R => z + c)
      ((fun z : Fin k → R => z + c) ⁻¹' U) U := fun z hz => hz
  constructor
  · have hcomp : IsSemialgebraicFunction ((fun z : Fin k → R => z + c) ⁻¹' U)
        (scalarFun c' ∘ fun z : Fin k → R => z + c) :=
      proposition_2_84 (isSemialgebraicFunction_translate (hU.preimage_translate c) c)
        h.1 hmaps
    exact hcomp
  · show ContinuousOn (scalarFun c' ∘ fun z : Fin k → R => z + c) _
    exact h.2.comp (continuous_translate c).continuousOn hmaps

/-! ### Partial derivatives transport along translations -/

omit [IsRealClosed R] in
/-- Partial derivatives transport along translations: if `c'` has `j`-th partial
derivative `d` at `x + c` within `U`, then `z ↦ c'(z + c)` has `j`-th partial
derivative `d` at `x` within `U − c`. -/
theorem HasPartialDerivAtIn.translate {k : ℕ} {c' : (Fin k → R) → R}
    {U : Set (Fin k → R)} {j : Fin k} {x : Fin k → R} {d : R} {c : Fin k → R}
    (h : HasPartialDerivAtIn c' U j (x + c) d) :
    HasPartialDerivAtIn (fun w => c' (w + c)) ((fun z : Fin k → R => z + c) ⁻¹' U)
      j x d := by
  -- the displaced slice point: `x[j := t] + c = (x + c)[j := t + cⱼ]`
  have hupd : ∀ t : R,
      Function.update x j t + c = Function.update (x + c) j (t + c j) := by
    intro t
    funext i
    by_cases hij : i = j
    · subst hij
      rw [Pi.add_apply, Function.update_self, Function.update_self]
    · rw [Pi.add_apply, Function.update_of_ne hij, Function.update_of_ne hij,
        Pi.add_apply]
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := h r hr
  refine ⟨δ, hδ, fun t ht htne habs => ?_⟩
  have hs : Function.update (x + c) j (t + c j) ∈ U := by
    rw [← hupd t]
    exact ht
  have hsne : t + c j ≠ (x + c) j := by
    rw [Pi.add_apply]
    intro hcon
    exact htne (add_right_cancel hcon)
  have hsabs : |t + c j - (x + c) j| < δ := by
    have he : t + c j - (x + c) j = t - x j := by
      rw [Pi.add_apply]
      ring
    rwa [he]
  have hq : |(c' (Function.update (x + c) j (t + c j))
      - c' (Function.update (x + c) j ((x + c) j))) / (t + c j - (x + c) j) - d| < r :=
    hb (t + c j) hs hsne hsabs
  show |(c' (Function.update x j t + c) - c' (Function.update x j (x j) + c))
      / (t - x j) - d| < r
  have e1 : c' (Function.update x j t + c)
      = c' (Function.update (x + c) j (t + c j)) := by
    rw [hupd t]
  have e2 : c' (Function.update x j (x j) + c)
      = c' (Function.update (x + c) j ((x + c) j)) := by
    rw [Function.update_eq_self, Function.update_eq_self]
  have e3 : t - x j = t + c j - (x + c) j := by
    rw [Pi.add_apply]
    ring
  rw [e1, e2, e3]
  exact hq

/-! ### The Inverse Function Theorem at a base point -/

/-- **Proposition 3.24 at an arbitrary base point** (BPR's "we can suppose without loss
of generality"): if `U′` is a semialgebraic open neighborhood of `z₀` in `R^k`,
`f ∈ 𝒮¹(U′, R^k)` (coordinatewise data as in `proposition_3_24`), and `df(z₀)` is
invertible, then there are semialgebraic open neighborhoods `U ∋ z₀` (inside `U′`) and
`V ∋ f(z₀)` such that `f|_U` is a semialgebraic homeomorphism onto `V` with semialgebraic
continuous inverse. -/
theorem proposition_3_24_at {k : ℕ} {U' : Set (Fin k → R)} {z₀ : Fin k → R}
    {f : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hU'open : IsOpen U') (hU'sa : IsSemialgebraicSet U') (hz₀ : z₀ ∈ U')
    (hf : ∀ l, IsSemialgContinuousOn U' (fun z => f z l))
    (hdiff : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => f w l) U' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn U' (g l j))
    (hdet : IsUnit (jacobianMatrix g z₀).det) :
    ∃ U V : Set (Fin k → R),
      IsSemialgebraicSet U ∧ IsOpen U ∧ z₀ ∈ U ∧ U ⊆ U' ∧
      IsSemialgebraicSet V ∧ IsOpen V ∧ f z₀ ∈ V ∧
      ∃ finv : (Fin k → R) → (Fin k → R),
        IsSemialgebraicHomeomorphism U V f finv ∧ IsSemialgebraicFunction V finv ∧
        (∀ z ∈ U, IsUnit (jacobianMatrix g z).det) ∧
        ∃ C : R, 0 < C ∧ ∀ y ∈ V, ∀ y' ∈ V,
          euclideanNorm (finv y - finv y') ≤ C * euclideanNorm (y - y') := by
  classical
  set w₀ : Fin k → R := f z₀ with hw₀
  -- the conjugated data at the origin
  set F : (Fin k → R) → (Fin k → R) := fun z => f (z + z₀) - w₀ with hF
  set G : Fin k → Fin k → (Fin k → R) → R := fun l j z => g l j (z + z₀) with hG
  set U'' : Set (Fin k → R) := (fun z : Fin k → R => z + z₀) ⁻¹' U' with hU''
  have hU''open : IsOpen U'' := hU'open.preimage (continuous_translate z₀)
  have hU''sa : IsSemialgebraicSet U'' := hU'sa.preimage_translate z₀
  have h0U'' : (0 : Fin k → R) ∈ U'' := by
    show (0 : Fin k → R) + z₀ ∈ U'
    rwa [zero_add]
  have hmem : ∀ z ∈ U'', z + z₀ ∈ U' := fun z hz => hz
  have hFc : ∀ l, IsSemialgContinuousOn U'' (fun z => F z l) := by
    intro l
    have h1 : IsSemialgContinuousOn U'' (fun z => f (z + z₀) l) :=
      (hf l).translate hU'sa z₀
    have h2 : IsSemialgContinuousOn U''
        ((fun z => f (z + z₀) l) + fun _ => -(w₀ l)) :=
      IsSemialgContinuousOn.add hU''sa h1
        (isSemialgContinuousOn_constFun hU''sa (-(w₀ l)))
    have heq : ((fun z => f (z + z₀) l) + fun _ => -(w₀ l)) = fun z => F z l := by
      funext z
      simp [hF, sub_eq_add_neg]
    rwa [heq] at h2
  have hFdiff : ∀ l j, ∀ z ∈ U'',
      HasPartialDerivAtIn (fun w => F w l) U'' j z (G l j z) := by
    intro l j z hz
    have h1 : HasPartialDerivAtIn (fun w => f (w + z₀) l) U'' j z (g l j (z + z₀)) :=
      (hdiff l j (z + z₀) (hmem z hz)).translate
    have h2 : HasPartialDerivAtIn (fun y => f (y + z₀) l + -(w₀ l)) U'' j z
        (g l j (z + z₀) + 0) :=
      h1.add (hasPartialDerivAtIn_const (-(w₀ l)) U'' j z)
    have heq : (fun y => f (y + z₀) l + -(w₀ l)) = fun w => F w l := by
      funext y
      simp [hF, sub_eq_add_neg]
    rw [heq, add_zero] at h2
    exact h2
  have hGsc : ∀ l j, IsSemialgContinuousOn U'' (G l j) :=
    fun l j => (hgsc l j).translate hU'sa z₀
  have hF0 : F 0 = 0 := by
    rw [hF]
    show f (0 + z₀) - w₀ = 0
    rw [zero_add, hw₀, sub_self]
  have hGdet : IsUnit (jacobianMatrix G 0).det := by
    have heq : jacobianMatrix G 0 = jacobianMatrix g z₀ := by
      ext l j
      show g l j ((0 : Fin k → R) + z₀) = g l j z₀
      rw [zero_add]
    rwa [heq]
  obtain ⟨U₁, V₁, hU₁sa, hU₁open, h0U₁, hU₁sub, hV₁sa, hV₁open, h0V₁, Finv,
    hhomeo, hFinvSa, hdetU₁, C, hC, hLipFinv⟩ :=
    proposition_3_24 hU''open hU''sa h0U'' hFc hFdiff hGsc hF0 hGdet
  -- translate the neighborhoods and the inverse back
  set U : Set (Fin k → R) := (fun z : Fin k → R => z + -z₀) ⁻¹' U₁ with hU
  set V : Set (Fin k → R) := (fun w : Fin k → R => w + -w₀) ⁻¹' V₁ with hV
  set finv : (Fin k → R) → (Fin k → R) := fun w => Finv (w + -w₀) + z₀ with hfinv
  have hUsa' : IsSemialgebraicSet U := hU₁sa.preimage_translate (-z₀)
  have hVsa' : IsSemialgebraicSet V := hV₁sa.preimage_translate (-w₀)
  -- the conjugation identity
  have hkey : ∀ z : Fin k → R, f z = F (z + -z₀) + w₀ := by
    intro z
    rw [hF]
    show f z = f (z + -z₀ + z₀) - w₀ + w₀
    rw [neg_add_cancel_right, sub_add_cancel]
  have hUmem : ∀ {z : Fin k → R}, z ∈ U ↔ z + -z₀ ∈ U₁ := fun {z} => Iff.rfl
  have hVmem : ∀ {w : Fin k → R}, w ∈ V ↔ w + -w₀ ∈ V₁ := fun {w} => Iff.rfl
  -- `Finv` maps `V₁` into `U₁`
  have hFinvMaps : Set.MapsTo Finv V₁ U₁ := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hhomeo.bijOn.surjOn hv
    rw [hhomeo.invOn.1 hu]
    exact hu
  refine ⟨U, V, hUsa', hU₁open.preimage (continuous_translate (-z₀)), ?_, ?_, hVsa',
    hV₁open.preimage (continuous_translate (-w₀)), ?_, finv, ?_, ?_, ?_, ?_⟩
  · -- `z₀ ∈ U`
    show z₀ + -z₀ ∈ U₁
    rw [add_neg_cancel]
    exact h0U₁
  · -- `U ⊆ U'`
    intro z hz
    have h1 : z + -z₀ ∈ U'' := hU₁sub (hUmem.mp hz)
    have h2 : z + -z₀ + z₀ ∈ U' := h1
    rwa [neg_add_cancel_right] at h2
  · -- `f z₀ ∈ V`
    show w₀ + -w₀ ∈ V₁
    rw [add_neg_cancel]
    exact h0V₁
  · -- the homeomorphism
    have hmapsU : Set.MapsTo (fun z : Fin k → R => z + -z₀) U U₁ := fun z hz => hz
    -- `f` is semialgebraic on `U`: conjugate the graph
    have hfsaU : IsSemialgebraicFunction U f := by
      have hc1 : IsSemialgebraicFunction U (F ∘ fun z : Fin k → R => z + -z₀) :=
        proposition_2_84 (isSemialgebraicFunction_translate hUsa' (-z₀))
          hhomeo.isSemialgebraicFunction hmapsU
      have hc2 : IsSemialgebraicFunction U
          ((fun w : Fin k → R => w + w₀) ∘ F ∘ fun z : Fin k → R => z + -z₀) :=
        proposition_2_84 hc1 (isSemialgebraicFunction_translate_univ w₀)
          (Set.mapsTo_univ _ _)
      have heq : ((fun w : Fin k → R => w + w₀) ∘ F ∘ fun z : Fin k → R => z + -z₀)
          = f := by
        funext z
        show F (z + -z₀) + w₀ = f z
        rw [← hkey]
      rwa [heq] at hc2
    -- `f` maps `U` into `V`, `finv` maps `V` into `U`
    have hfMaps : Set.MapsTo f U V := by
      intro z hz
      rw [hVmem]
      have h1 : F (z + -z₀) ∈ V₁ := hhomeo.bijOn.mapsTo (hUmem.mp hz)
      have h2 : f z + -w₀ = F (z + -z₀) := by
        rw [hkey z, add_neg_cancel_right]
      rwa [h2]
    have hfinvMaps : Set.MapsTo finv V U := by
      intro w hw
      rw [hUmem]
      have h1 : Finv (w + -w₀) ∈ U₁ := hFinvMaps (hVmem.mp hw)
      have h2 : finv w + -z₀ = Finv (w + -w₀) := by
        show Finv (w + -w₀) + z₀ + -z₀ = Finv (w + -w₀)
        rw [add_neg_cancel_right]
      rwa [h2]
    -- two-sided inverse
    have hinvOn : Set.InvOn finv f U V := by
      constructor
      · intro z hz
        have h1 : f z + -w₀ = F (z + -z₀) := by
          rw [hkey z, add_neg_cancel_right]
        show Finv (f z + -w₀) + z₀ = z
        rw [h1, hhomeo.invOn.1 (hUmem.mp hz), neg_add_cancel_right]
      · intro w hw
        have h1 : finv w + -z₀ = Finv (w + -w₀) := by
          show Finv (w + -w₀) + z₀ + -z₀ = Finv (w + -w₀)
          rw [add_neg_cancel_right]
        rw [hkey (finv w), h1, hhomeo.invOn.2 (hVmem.mp hw), neg_add_cancel_right]
    -- continuity of `f` on `U` and of `finv` on `V`
    have hfcont : ContinuousOn f U := by
      have hc : ContinuousOn
          ((fun w : Fin k → R => w + w₀) ∘ F ∘ fun z : Fin k → R => z + -z₀) U :=
        (continuous_translate w₀).comp_continuousOn
          (hhomeo.continuousOn.comp (continuous_translate (-z₀)).continuousOn hmapsU)
      have heq : ((fun w : Fin k → R => w + w₀) ∘ F ∘ fun z : Fin k → R => z + -z₀)
          = f := by
        funext z
        show F (z + -z₀) + w₀ = f z
        rw [← hkey]
      rwa [heq] at hc
    have hfinvcont : ContinuousOn finv V := by
      have hmapsV : Set.MapsTo (fun w : Fin k → R => w + -w₀) V V₁ := fun w hw => hw
      have hc : ContinuousOn
          ((fun u : Fin k → R => u + z₀) ∘ Finv ∘ fun w : Fin k → R => w + -w₀) V :=
        (continuous_translate z₀).comp_continuousOn
          (hhomeo.continuousOn_inv.comp (continuous_translate (-w₀)).continuousOn hmapsV)
      have heq : ((fun u : Fin k → R => u + z₀) ∘ Finv ∘ fun w : Fin k → R => w + -w₀)
          = finv := rfl
      rwa [heq] at hc
    exact ⟨hfsaU, hinvOn.bijOn hfMaps hfinvMaps, hfcont, hinvOn, hfinvcont⟩
  · -- `finv` is semialgebraic on `V`
    have hmapsV : Set.MapsTo (fun w : Fin k → R => w + -w₀) V V₁ := fun w hw => hw
    have hc1 : IsSemialgebraicFunction V (Finv ∘ fun w : Fin k → R => w + -w₀) :=
      proposition_2_84 (isSemialgebraicFunction_translate hVsa' (-w₀)) hFinvSa hmapsV
    have hc2 : IsSemialgebraicFunction V
        ((fun u : Fin k → R => u + z₀) ∘ Finv ∘ fun w : Fin k → R => w + -w₀) :=
      proposition_2_84 hc1 (isSemialgebraicFunction_translate_univ z₀)
        (Set.mapsTo_univ _ _)
    have heq : ((fun u : Fin k → R => u + z₀) ∘ Finv ∘ fun w : Fin k → R => w + -w₀)
        = finv := rfl
    rwa [heq] at hc2
  · -- pointwise invertibility of the Jacobian on `U` (translated from `U₁`)
    intro z hz
    have h1 := hdetU₁ (z + -z₀) (hUmem.mp hz)
    have heq : jacobianMatrix G (z + -z₀) = jacobianMatrix g z := by
      ext l j
      show g l j (z + -z₀ + z₀) = g l j z
      rw [neg_add_cancel_right]
    rwa [heq] at h1
  · -- the inverse is Lipschitz on `V` (translations cancel in the difference)
    refine ⟨C, hC, fun y hy y' hy' => ?_⟩
    have h1 := hLipFinv (y + -w₀) (hVmem.mp hy) (y' + -w₀) (hVmem.mp hy')
    have heq1 : finv y - finv y' = Finv (y + -w₀) - Finv (y' + -w₀) := by
      show (Finv (y + -w₀) + z₀) - (Finv (y' + -w₀) + z₀)
        = Finv (y + -w₀) - Finv (y' + -w₀)
      abel
    have heq2 : (y + -w₀) - (y' + -w₀) = y - y' := by abel
    rw [heq1]
    rw [heq2] at h1
    exact h1

end Azurite.BPR
