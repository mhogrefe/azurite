import Azurite.BasuPollackRoy.Chapter3.Section3_5.ChainRule

/-! # BPR §3.5 — closure properties of `𝒮^ℓ`

The closure lemmas needed to bootstrap the `𝒮^ℓ`-smoothness of the inverse in
Proposition 3.24 from the chain rule:

* **finite sums and products** (`isSFunction_finsetSum`, `isSFunction_finsetProd`),
  by `Finset` induction on the binary `add'`/`mul'`;
* **reciprocals** (`IsSFunction.inv'`), by induction on the order using the reciprocal
  rule `HasPartialDerivAtIn.inv`;
* **composition** (`isSFunction_comp`): an `𝒮^ℓ` scalar precomposed with a map whose
  components are `𝒮^ℓ` is `𝒮^ℓ`, by induction on the order using the chain rule
  `hasPartialDerivAtIn_comp`;
* **determinants and matrix-inverse entries** (`isSFunction_matrixDet`,
  `isSFunction_matrixInvEntry`): the determinant of a matrix whose entries are `𝒮^ℓ` is
  `𝒮^ℓ` (Leibniz expansion), and where the determinant is nonvanishing, every entry of
  the inverse is `𝒮^ℓ` (`A⁻¹ = (det A)⁻¹ • adjugate A`, with the adjugate entries again
  determinants of `𝒮^ℓ`-entry matrices). -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Finite sums and products -/

/-- A finite sum of `𝒮^ℓ` functions is `𝒮^ℓ`. -/
theorem isSFunction_finsetSum {k ℓ : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    {ι : Type*} (s : Finset ι) (F : ι → (Fin k → R) → R)
    (hF : ∀ i ∈ s, IsSFunction ℓ U (F i)) :
    IsSFunction ℓ U (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact isSFunction_const hU 0 ℓ
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact IsSFunction.add' hU (hF a (Finset.mem_cons_self a s))
      (ih fun i hi => hF i (Finset.mem_cons_of_mem hi))

/-- A finite product of `𝒮^ℓ` functions is `𝒮^ℓ`. -/
theorem isSFunction_finsetProd {k ℓ : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    {ι : Type*} (s : Finset ι) (F : ι → (Fin k → R) → R)
    (hF : ∀ i ∈ s, IsSFunction ℓ U (F i)) :
    IsSFunction ℓ U (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact isSFunction_const hU 1 ℓ
  | cons a s ha ih =>
    simp only [Finset.prod_cons]
    exact IsSFunction.mul' hU (hF a (Finset.mem_cons_self a s))
      (ih fun i hi => hF i (Finset.mem_cons_of_mem hi))

/-! ### Reciprocals -/

/-- **Reciprocal closure.** Where `c` is nonvanishing on `U`, if `c ∈ 𝒮^ℓ(U)` then
`1/c ∈ 𝒮^ℓ(U)`. -/
theorem IsSFunction.inv' {k : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U) :
    ∀ {ℓ : ℕ} {c : (Fin k → R) → R}, IsSFunction ℓ U c → (∀ x ∈ U, c x ≠ 0) →
      IsSFunction ℓ U (fun y => (c y)⁻¹) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro c h hne
    exact IsSemialgContinuousOn.inv h hne
  | succ ℓ ih =>
    intro c h hne
    refine ⟨IsSemialgContinuousOn.inv h.1 hne, fun j => ?_⟩
    obtain ⟨gj, hgj, hS⟩ := h.2 j
    refine ⟨fun y => -(gj y) * (c y * c y)⁻¹, fun x hx => (hgj x hx).inv hne hx, ?_⟩
    have hcℓ : IsSFunction ℓ U c := h.of_succ
    have hcc : IsSFunction ℓ U (fun y => c y * c y) := IsSFunction.mul' hU hcℓ hcℓ
    have hccne : ∀ x ∈ U, c x * c x ≠ 0 := fun x hx => mul_ne_zero (hne x hx) (hne x hx)
    have hinv : IsSFunction ℓ U (fun y => (c y * c y)⁻¹) := ih hcc hccne
    exact IsSFunction.mul' hU (IsSFunction.neg' hU hS) hinv

/-! ### Composition -/

/-- The order-`0` (semialgebraic-and-continuous) case of composition. -/
theorem isSemialgContinuousOn_comp {k p : ℕ} [Nonempty (Fin p)]
    {V : Set (Fin k → R)} {U : Set (Fin p → R)}
    {h : (Fin k → R) → (Fin p → R)} {c : (Fin p → R) → R}
    (hmaps : Set.MapsTo h V U)
    (hc : IsSemialgContinuousOn U c)
    (hh : ∀ m, IsSemialgContinuousOn V (fun x => h x m)) :
    IsSemialgContinuousOn V (fun x => c (h x)) := by
  have hhsa : IsSemialgebraicFunction V h :=
    isSemialgebraicFunction_of_coords fun m => (hh m).1
  have hhcont : ContinuousOn h V :=
    continuousOn_of_components fun m => (hh m).2
  exact ⟨proposition_2_84 hhsa hc.1 hmaps, hc.2.comp hhcont hmaps⟩

/-- **Composition closure.** If `c ∈ 𝒮^ℓ(U)` and `h : V → U` has every component in
`𝒮^ℓ(V)`, then `c ∘ h ∈ 𝒮^ℓ(V)`. -/
theorem isSFunction_comp {k p : ℕ} [Nonempty (Fin p)]
    {V : Set (Fin k → R)} {U : Set (Fin p → R)}
    (hVsa : IsSemialgebraicSet V) (hUopen : IsOpen U)
    {h : (Fin k → R) → (Fin p → R)} (hmaps : Set.MapsTo h V U) :
    ∀ {ℓ : ℕ} {c : (Fin p → R) → R}, IsSFunction ℓ U c →
      (∀ m, IsSFunction ℓ V (fun x => h x m)) →
      IsSFunction ℓ V (fun x => c (h x)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro c hc hh
    exact isSemialgContinuousOn_comp hmaps hc hh
  | succ ℓ ih =>
    intro c hc hh
    refine ⟨isSemialgContinuousOn_comp hmaps hc.isSemialgContinuousOn
      (fun m => (hh m).isSemialgContinuousOn), fun j => ?_⟩
    choose gc hgc hgcS using hc.2
    choose Hpart hHpart hHpartS using fun m => (hh m).2 j
    refine ⟨fun x => ∑ m, gc m (h x) * Hpart m x, fun x hx => ?_, ?_⟩
    · exact hasPartialDerivAtIn_comp hUopen hmaps hc.1.1 (fun m u hu => hgc m u hu)
        (fun m => (hgcS m).isSemialgContinuousOn.2) hx (fun m => hHpart m x hx)
    · refine isSFunction_finsetSum hVsa Finset.univ _ fun m _ => ?_
      exact IsSFunction.mul' hVsa (ih (hgcS m) (fun m' => (hh m').of_succ)) (hHpartS m)

/-! ### Determinants and matrix inverses -/

/-- **Determinant closure.** The determinant of a matrix whose entries are `𝒮^ℓ`
functions is `𝒮^ℓ`. -/
theorem isSFunction_matrixDet {k n ℓ : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    {E : Fin n → Fin n → (Fin k → R) → R} (hE : ∀ i j, IsSFunction ℓ U (E i j)) :
    IsSFunction ℓ U (fun x => (Matrix.of fun i j => E i j x).det) := by
  classical
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  refine isSFunction_finsetSum hU Finset.univ _ fun σ _ => ?_
  refine IsSFunction.mul' hU (isSFunction_const hU _ ℓ) ?_
  exact isSFunction_finsetProd hU Finset.univ _ fun i _ => hE (σ i) i

/-- **Matrix-inverse entry closure.** If the entries of a square matrix-valued function
are `𝒮^ℓ` and its determinant is nonvanishing on `U`, then every entry of the inverse is
`𝒮^ℓ`. -/
theorem isSFunction_matrixInvEntry {k n ℓ : ℕ} {U : Set (Fin k → R)}
    (hU : IsSemialgebraicSet U) {E : Fin n → Fin n → (Fin k → R) → R}
    (hE : ∀ i j, IsSFunction ℓ U (E i j))
    (hdet : ∀ x ∈ U, (Matrix.of fun i j => E i j x).det ≠ 0) (a b : Fin n) :
    IsSFunction ℓ U (fun x => (Matrix.of fun i j => E i j x)⁻¹ a b) := by
  classical
  -- entrywise: `A⁻¹ a b = (det A)⁻¹ * adjugate A a b`
  have hentry : (fun x => (Matrix.of fun i j => E i j x)⁻¹ a b)
      = fun x => ((Matrix.of fun i j => E i j x).det)⁻¹
        * (Matrix.of fun i j => E i j x).adjugate a b := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [hentry]
  refine IsSFunction.mul' hU
    (IsSFunction.inv' hU (isSFunction_matrixDet hU hE) hdet) ?_
  -- the adjugate entry is the determinant of an `updateRow` matrix with `𝒮^ℓ` entries
  have hadj : (fun x => (Matrix.of fun i j => E i j x).adjugate a b)
      = fun x => (Matrix.of fun i j =>
          ((Matrix.of fun i' j' => E i' j' x).updateRow b (Pi.single a 1)) i j).det := by
    funext x
    rw [Matrix.adjugate_apply]
    rfl
  rw [hadj]
  refine isSFunction_matrixDet hU fun i j => ?_
  by_cases hib : i = b
  · have heq : (fun x => ((Matrix.of fun i' j' => E i' j' x).updateRow b (Pi.single a 1)) i j)
        = fun _ : Fin k → R => (Pi.single a (1 : R) : Fin n → R) j := by
      funext x; rw [Matrix.updateRow_apply, ite_eq_left hib]
    rw [heq]
    exact isSFunction_const hU _ ℓ
  · have heq : (fun x => ((Matrix.of fun i' j' => E i' j' x).updateRow b (Pi.single a 1)) i j)
        = E i j := by
      funext x; rw [Matrix.updateRow_apply, ite_eq_right hib, Matrix.of_apply]
    rw [heq]
    exact hE i j

end Azurite.BPR
