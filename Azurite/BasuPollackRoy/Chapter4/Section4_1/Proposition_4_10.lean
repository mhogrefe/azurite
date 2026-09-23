import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# BPR Proposition 4.10: Cauchy-Binet formula

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For `A : Matrix (Fin n) (Fin m) R` and `B : Matrix (Fin m) (Fin n) R`
over a commutative ring `R` with `n ≤ m`,

  `det(A · B) = ∑_{I ⊆ Fin m, |I| = n} det(A_I) · det(B^I)`

where `A_I` (the `n × n` matrix obtained from `A` by selecting columns
indexed by `I`) is `A.submatrix id (I.orderEmbOfFin _)` and
`B^I` (selecting rows indexed by `I`) is `B.submatrix (I.orderEmbOfFin _) id`.

See `Proposition_4_10_PLAN.md` for the proof decomposition.
-/

namespace Azurite.BPR.Chapter4

open Matrix Finset

variable {R : Type*} [CommRing R]

/-- **Step 1**: Leibniz expansion of `det(A * B)` distributed via
    `Fintype.prod_sum`:
    `det(A · B) = ∑_f (∏_i B[f(i), i]) · det(A.submatrix id f)`,
    where `f` ranges over all functions `Fin n → Fin m`. -/
private lemma det_mul_eq_sum_over_functions {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ f : Fin n → Fin m,
        (∏ i, B (f i) i) * (A.submatrix id f).det := by
  rw [Matrix.det_apply]
  simp_rw [Matrix.mul_apply, Fintype.prod_sum, Finset.smul_sum,
           Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp_rw [← smul_mul_assoc, ← Finset.sum_mul]
  rw [mul_comm]
  congr 1
  rw [Matrix.det_apply]
  rfl

/-- **Step 2**: When `f : Fin n → Fin m` is not injective,
    `A.submatrix id f` has two equal columns, so its determinant is `0`.
    Proven via transpose + `Matrix.det_zero_of_row_eq`. -/
private lemma det_submatrix_id_eq_zero_of_not_injective {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) {f : Fin n → Fin m}
    (hf : ¬ Function.Injective f) :
    (A.submatrix id f).det = 0 := by
  rw [Function.not_injective_iff] at hf
  obtain ⟨i, j, hfij, hij⟩ := hf
  rw [← Matrix.det_transpose]
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [Matrix.transpose_apply, Matrix.submatrix_apply, hfij]

/-- **BPR Proposition 4.10** (Cauchy-Binet formula). For
    `A : Matrix (Fin n) (Fin m) R` and `B : Matrix (Fin m) (Fin n) R`,
    the determinant of `A * B` is the sum over `n`-element subsets
    `I` of `Fin m` of the product of the `I`-minor of `A` (columns
    indexed by `I`) and the `I`-minor of `B` (rows indexed by `I`).

    The `Finset` sum uses a dependent `if` so the `orderEmbOfFin`
    proof obligation `|I| = n` is discharged from `I ∈ powersetCard n`. -/
theorem proposition_4_10 {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det =
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
        if h : I.card = n then
          (A.submatrix id (I.orderEmbOfFin h)).det *
          (B.submatrix (I.orderEmbOfFin h) id).det
        else 0 := by
  classical
  rw [det_mul_eq_sum_over_functions]
  -- LHS: ∑ f : Fin n → Fin m, (∏ i, B (f i) i) * (A.submatrix id f).det.
  -- Drop non-injective f (their summands vanish by Step 2).
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Function.Injective]
  rw [show (Finset.univ.filter (fun f : Fin n → Fin m =>
              ¬ Function.Injective f)).sum
            (fun f => (∏ i, B (f i) i) * (A.submatrix id f).det) = 0 from by
    apply Finset.sum_eq_zero
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [det_submatrix_id_eq_zero_of_not_injective A hf.2, mul_zero]]
  rw [add_zero]
  -- Now: ∑ f injective, (∏ i, B (f i) i) * (A.submatrix id f).det
  -- Expand the RHS via `Matrix.det_permute'`: each summand becomes
  -- a sum over τ ∈ Perm (Fin n).
  symm
  -- RHS = ∑ I, if h : I.card = n then A_I.det * B^I.det else 0
  -- Expand B^I.det via det_apply, absorb sign τ.
  rw [show (∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : I.card = n then
        (A.submatrix id (I.orderEmbOfFin h)).det *
        (B.submatrix (I.orderEmbOfFin h) id).det
      else 0) =
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
        ∑ τ : Equiv.Perm (Fin n),
        if h : I.card = n then
          (∏ i, B (I.orderEmbOfFin h (τ i)) i) *
          (A.submatrix id ((I.orderEmbOfFin h : Fin n → Fin m) ∘ τ)).det
        else 0 from by
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.mem_powersetCard] at hI
    have h : I.card = n := hI.2
    rw [dite_eq_left h]
    rw [show (B.submatrix (I.orderEmbOfFin h) id).det =
        ∑ τ : Equiv.Perm (Fin n), Equiv.Perm.sign τ •
          ∏ i, B (I.orderEmbOfFin h (τ i)) i from Matrix.det_apply _]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [dite_eq_left h]
    -- A.submatrix id ((I.orderEmbOfFin h) ∘ τ) = (A.submatrix id (I.orderEmbOfFin h)).submatrix id τ
    rw [show (A.submatrix id ((I.orderEmbOfFin h : Fin n → Fin m) ∘ τ)) =
        (A.submatrix id (I.orderEmbOfFin h)).submatrix id τ from rfl]
    rw [Matrix.det_permute' τ]
    -- Convert smul to mul, then ring.
    simp only [Units.smul_def, zsmul_eq_mul]
    ring]
  -- Flatten nested sum to a sigma sum.
  rw [Finset.sum_sigma']
  -- Apply Finset.sum_bij with bijection ⟨I, τ⟩ ↦ (I.orderEmbOfFin _) ∘ τ.
  apply Finset.sum_bij
    (i := fun (x : (Σ _ : Finset (Fin m), Equiv.Perm (Fin n))) hx =>
      ((x.1.orderEmbOfFin
        (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).1).2 :
        Fin n → Fin m) ∘ (x.2 : Fin n → Fin n)))
  -- Conditions: membership, injectivity, surjectivity, summand equality.
  · -- Membership: i x ∈ filter Injective.
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (x.1.orderEmbOfFin _).injective.comp x.2.injective
  · -- Injectivity of i on the source.
    intro x hx y hy hmap
    have hxI : x.1.card = n :=
      (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).1).2
    have hyI : y.1.card = n :=
      (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hy).1).2
    -- Step A: I_x = I_y via image equality.
    have him : x.1 = y.1 := by
      have h_im_x : Finset.image ((x.1.orderEmbOfFin hxI : Fin n → Fin m) ∘ x.2)
          Finset.univ = x.1 := by
        rw [show ((x.1.orderEmbOfFin hxI : Fin n → Fin m) ∘ x.2) =
            (x.1.orderEmbOfFin hxI : Fin n → Fin m) ∘
              (x.2 : Fin n → Fin n) from rfl]
        rw [← Finset.image_image]
        rw [show Finset.image (x.2 : Fin n → Fin n) Finset.univ = Finset.univ from
            Finset.image_univ_of_surjective x.2.surjective]
        exact Finset.image_orderEmbOfFin_univ x.1 hxI
      have h_im_y : Finset.image ((y.1.orderEmbOfFin hyI : Fin n → Fin m) ∘ y.2)
          Finset.univ = y.1 := by
        rw [show ((y.1.orderEmbOfFin hyI : Fin n → Fin m) ∘ y.2) =
            (y.1.orderEmbOfFin hyI : Fin n → Fin m) ∘
              (y.2 : Fin n → Fin n) from rfl]
        rw [← Finset.image_image]
        rw [show Finset.image (y.2 : Fin n → Fin n) Finset.univ = Finset.univ from
            Finset.image_univ_of_surjective y.2.surjective]
        exact Finset.image_orderEmbOfFin_univ y.1 hyI
      rw [← h_im_x, ← h_im_y, hmap]
    -- Step B: with I_x = I_y, τ_x = τ_y.
    obtain ⟨I_x, τ_x⟩ := x
    obtain ⟨I_y, τ_y⟩ := y
    simp only at him
    subst him
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext k
    have hk : (I_x.orderEmbOfFin hxI) (τ_x k) =
        (I_x.orderEmbOfFin hyI) (τ_y k) := congrFun hmap k
    have h_emb_eq : I_x.orderEmbOfFin hxI = I_x.orderEmbOfFin hyI := by congr
    rw [h_emb_eq] at hk
    exact Fin.val_eq_of_eq ((I_x.orderEmbOfFin hyI).injective hk)
  · -- Surjectivity: every injective f comes from some (I, τ).
    intro f hf
    rw [Finset.mem_filter] at hf
    have hfinj : Function.Injective f := hf.2
    let I : Finset (Fin m) := Finset.image f Finset.univ
    have hI_card : I.card = n := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ,
          Fintype.card_fin]
    -- Build τ : Equiv.Perm (Fin n).
    let τ_fun : Fin n → Fin n := fun k =>
      (I.orderIsoOfFin hI_card).symm ⟨f k,
        Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
    have hτ_inj : Function.Injective τ_fun := by
      intro k₁ k₂ h
      have h' : (I.orderIsoOfFin hI_card).symm
            ⟨f k₁, Finset.mem_image.mpr ⟨k₁, Finset.mem_univ _, rfl⟩⟩ =
          (I.orderIsoOfFin hI_card).symm
            ⟨f k₂, Finset.mem_image.mpr ⟨k₂, Finset.mem_univ _, rfl⟩⟩ := h
      have h'' : f k₁ = f k₂ := by
        have := (I.orderIsoOfFin hI_card).symm.injective h'
        exact (Subtype.mk_eq_mk.mp this)
      exact hfinj h''
    let τ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective τ_fun (Function.Injective.bijective_of_finite hτ_inj)
    refine ⟨⟨I, τ⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hI_card⟩
    · -- Show (I.orderEmbOfFin _) ∘ τ = f.
      funext k
      show (I.orderEmbOfFin hI_card) (τ k) = f k
      have hτ_def : τ k = τ_fun k := rfl
      rw [hτ_def]
      show ((I.orderEmbOfFin hI_card) :
          Fin n → Fin m) ((I.orderIsoOfFin hI_card).symm
        ⟨f k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩) = f k
      have : (I.orderEmbOfFin hI_card) = Subtype.val ∘ I.orderIsoOfFin hI_card :=
        rfl
      rw [this]
      simp
  · -- Equation: summand equality after destructuring.
    intro x hx
    have hI : x.1.card = n :=
      (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).1).2
    rw [dite_eq_left hI]
    rfl

end Azurite.BPR.Chapter4
