import Azurite.BasuPollackRoy.Chapter4.Section4_1.Subdiscriminant
import Azurite.BasuPollackRoy.Chapter4.Section4_1.NewtonMatrix
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_10
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Lemma_4_11
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Remark_4_6

/-!
# BPR Proposition 4.9: subdiscriminant as determinant of Newton matrix

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For `P : K[X]` with `p := (P.aroots C).card` and `1 ≤ k ≤ p`,

  `sDisc_{p-k}(P) = det(Newt_{p-k}(P))`.

The proof factors `Newt_{p-k}(P) = V_k · V_k^T` where `V_k` is the
`k × p` matrix with entry `x_j^i` (rows indexed by powers, columns by
roots), then applies Cauchy-Binet (Proposition 4.10) and Lemma 4.11
(Vandermonde determinant) to identify the resulting sum with the
defining formula of `sDisc_{p-k}(P)`.

See `Proposition_4_9_PLAN.md` for the proof decomposition.
-/

namespace Azurite.BPR.Chapter4

open Matrix Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- Enumeration `Fin l.length → C` of `P.aroots C` (via `toList.get`). -/
private noncomputable def arootsEnum (P : K[X]) :
    Fin (P.aroots C).toList.length → C :=
  (P.aroots C).toList.get

omit [IsAlgClosed C] in
/-- The bridge from multiset sum over `P.aroots C` to Fin-indexed sum. -/
private lemma sum_aroots_eq_fin_sum (P : K[X]) (f : C → C) :
    ((P.aroots C).map f).sum =
      ∑ i : Fin (P.aroots C).toList.length, f (arootsEnum P i) := by
  unfold arootsEnum
  rw [show ((P.aroots C).map f).sum = ((P.aroots C).toList.map f).sum from by
    nth_rewrite 1 [← Multiset.coe_toList (P.aroots C)]
    rw [Multiset.map_coe, Multiset.sum_coe]]
  exact (Fin.sum_univ_fun_getElem _ _).symm

/-- The `k × p` rectangular Vandermonde matrix `V_k` with entry
    `(arootsEnum P j) ^ i.val` (BPR's V_k matrix). -/
private noncomputable def vandermondeRect (P : K[X]) (k : ℕ) :
    Matrix (Fin k) (Fin (P.aroots C).toList.length) C :=
  Matrix.of fun i j => arootsEnum P j ^ i.val

omit [IsAlgClosed C] in
/-- **Step 2**: `V_k · V_k^T = Newt_{p-k}(P)`. Each `(i, j)` entry of the
    product expands as `∑_l (e l)^i · (e l)^j = ∑_l (e l)^(i+j) =
    newtonSum P (i+j)`, matching the `(i, j)` entry of `newtMat P k`. -/
private lemma vandermondeRect_mul_transpose_eq_newtMat (P : K[X]) (k : ℕ) :
    (vandermondeRect P k) * (vandermondeRect (C := C) P k).transpose =
      newtMat P k := by
  ext i j
  unfold vandermondeRect newtMat newtonSum
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [sum_aroots_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← pow_add]

omit [IsAlgClosed C] in
/-- **Step 5**: each `V_k.submatrix id (I.orderEmbOfFin h)` is the
    `k × k` Vandermonde matrix on the elements indexed by `I`. -/
private lemma vandermondeRect_submatrix_eq (P : K[X]) (k : ℕ)
    (I : Finset (Fin (P.aroots C).toList.length)) (h : I.card = k) :
    (vandermondeRect P k).submatrix id (I.orderEmbOfFin h) =
      vandermondeMat (arootsEnum (C := C) P ∘ I.orderEmbOfFin h) := by
  ext i j
  rfl

omit [IsAlgClosed C] in
/-- The multiset `P.aroots C` is the image of `arootsEnum P` under
    `Finset.univ`. -/
private lemma aroots_eq_univ_map_arootsEnum (P : K[X]) :
    (P.aroots C) =
      (Finset.univ : Finset (Fin (P.aroots C).toList.length)).val.map (arootsEnum P) := by
  conv_lhs => rw [← Multiset.coe_toList (P.aroots C)]
  rw [Finset.val_univ_fin]
  unfold arootsEnum
  rw [Multiset.map_coe]
  rw [List.map_get_finRange]

omit [IsAlgClosed C] in
/-- A Finset's underlying multiset equals the image of `Finset.univ` (on
    `Fin k`) under `Finset.orderEmbOfFin`. -/
private lemma univ_map_orderEmbOfFin_val_eq {α : Type*} [LinearOrder α] {k : ℕ}
    (s : Finset α) (h : s.card = k) :
    (Finset.univ : Finset (Fin k)).val.map (s.orderEmbOfFin h) = s.val := by
  conv_rhs => rw [← s.map_orderEmbOfFin_univ h]
  rfl

omit [IsAlgClosed C] in
/-- The multiset `t ×ˢ t` decomposes as `t.map (·,·)` plus the off-diagonal
    image of `Finset.univ.offDiag`, when `t = univ.val.map σ`. -/
private lemma prod_self_decomp
    {R : Type*} [CommRing R] [DecidableEq R] {k : ℕ} (σ : Fin k → R) :
    ((Finset.univ : Finset (Fin k)).val.map σ) ×ˢ
        ((Finset.univ : Finset (Fin k)).val.map σ) =
      ((Finset.univ : Finset (Fin k)).val.map σ).map (fun a => (a, a)) +
        (Finset.univ : Finset (Fin k)).offDiag.val.map (fun p => (σ p.1, σ p.2)) := by
  rw [multiset_product_map]
  rw [show (Finset.univ : Finset (Fin k)).val ×ˢ (Finset.univ : Finset (Fin k)).val =
      (Finset.univ : Finset (Fin k × Fin k)).val from by
      rw [← Finset.product_val, Finset.univ_product_univ]]
  rw [show (Finset.univ : Finset (Fin k × Fin k)).val =
        (Finset.univ : Finset (Fin k)).diag.val +
        (Finset.univ : Finset (Fin k)).offDiag.val from by
      rw [show (Finset.univ : Finset (Fin k)).diag.val +
              (Finset.univ : Finset (Fin k)).offDiag.val =
              ((Finset.univ : Finset (Fin k)).diag.disjUnion
                (Finset.univ : Finset (Fin k)).offDiag
                (Finset.disjoint_diag_offDiag _)).val from by rw [Finset.disjUnion_val]]
      rw [show (Finset.univ : Finset (Fin k)).diag.disjUnion
            (Finset.univ : Finset (Fin k)).offDiag (Finset.disjoint_diag_offDiag _) =
          (Finset.univ : Finset (Fin k)).diag ∪ (Finset.univ : Finset (Fin k)).offDiag from
          Finset.disjUnion_eq_union _ _ _]
      rw [Finset.diag_union_offDiag, Finset.univ_product_univ]]
  rw [Multiset.map_add]
  congr 1
  rw [show (Finset.univ : Finset (Fin k)).diag.val =
        (Finset.univ : Finset (Fin k)).val.map (fun a => (a, a)) from rfl]
  rw [Multiset.map_map, Multiset.map_map]
  rfl

omit [IsAlgClosed C] in
/-- **Off-diag multiset/Finset bridge**. The multiset off-diagonal product
    over `univ.val.map σ` equals the Finset product over `Finset.univ.offDiag`. -/
private lemma offdiag_multi_eq_finset_offDiag_prod
    {R : Type*} [CommRing R] [DecidableEq R] {k : ℕ} (σ : Fin k → R) :
    let t : Multiset R := (Finset.univ : Finset (Fin k)).val.map σ
    ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab : R × R => ab.1 - ab.2)).prod =
      ∏ p ∈ ((Finset.univ : Finset (Fin k)).offDiag), (σ p.1 - σ p.2) := by
  rw [Finset.prod_eq_multiset_prod]
  rw [show ((Finset.univ : Finset (Fin k)).offDiag.val.map
        (fun p : Fin k × Fin k => σ p.1 - σ p.2)) =
      ((Finset.univ : Finset (Fin k)).offDiag.val.map
        (fun p : Fin k × Fin k => (σ p.1, σ p.2))).map
        (fun ab : R × R => ab.1 - ab.2) from by rw [Multiset.map_map]; rfl]
  congr 1
  rw [prod_self_decomp σ]
  rw [add_tsub_cancel_left]

omit [IsAlgClosed C] in
/-- **Squaring identity** (Fin-based generic). For `σ : Fin k → R` over a
    commutative ring `R`,
    `(vandermondeDet σ)^2 = (-1)^{k(k-1)/2} · ∏_{(a,b) off-diagonal} (a - b)`
    over the multiset `t = univ.val.map σ`. -/
private lemma vandermondeDet_sq_eq_signed_offdiag_multi
    {R : Type*} [CommRing R] [DecidableEq R] {k : ℕ} (σ : Fin k → R) :
    (vandermondeDet σ) ^ 2 = (-1 : R) ^ (k * (k - 1) / 2) *
      (((Finset.univ : Finset (Fin k)).val.map σ ×ˢ
          (Finset.univ : Finset (Fin k)).val.map σ -
          ((Finset.univ : Finset (Fin k)).val.map σ).map (fun a => (a, a))).map
        (fun ab : R × R => ab.1 - ab.2)).prod := by
  rw [offdiag_multi_eq_finset_offDiag_prod]
  have key : (-1 : R) ^ (k * (k - 1) / 2) * (vandermondeDet σ) ^ 2 =
      ∏ p ∈ ((Finset.univ : Finset (Fin k)).offDiag), (σ p.1 - σ p.2) := by
    have hmathlib :
        ∏ i, ∏ j ∈ Finset.Ioi i, (σ i - σ j) * (σ j - σ i) =
        ∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin k)), (σ i - σ j) :=
      Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun a b => σ b - σ a)
    -- LHS reformulation: (σ i - σ j) * (σ j - σ i) = -(σ j - σ i)^2,
    -- so the double product becomes (-1)^N · (vandermondeDet σ)^2.
    have hLHS :
        (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (σ i - σ j) * (σ j - σ i)) =
        (-1 : R) ^ (k * (k - 1) / 2) * (vandermondeDet σ) ^ 2 := by
      have hfactor : ∀ a b : R, (a - b) * (b - a) = -((b - a) ^ 2) :=
        fun a b => by ring
      simp_rw [hfactor]
      simp_rw [Finset.prod_neg, Finset.prod_pow]
      rw [Finset.prod_mul_distrib]
      -- Now goal: (∏ i, (-1)^(Ioi i).card) * (∏ i, (∏ j ∈ Ioi i, σ j - σ i)^2) =
      --          (-1)^(k(k-1)/2) * vandermondeDet σ ^ 2
      congr 1
      · -- ∏ i, (-1)^(Ioi i).card = (-1)^(∑ i, (Ioi i).card) = (-1)^(k(k-1)/2)
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        -- Goal: ∑ i : Fin k, (Ioi i).card = k(k-1)/2
        simp_rw [Fin.card_Ioi]
        rw [show (∑ i : Fin k, (k - 1 - i.val)) = ∑ i ∈ Finset.range k, (k - 1 - i) from
            Fin.sum_univ_eq_sum_range _ _]
        rw [show (∑ i ∈ Finset.range k, (k - 1 - i)) = ∑ i ∈ Finset.range k, i from
            Finset.sum_range_reflect (fun n => n) k]
        exact Finset.sum_range_id k
      · -- (∏ i, (∏ j, ...)^2 = (∏ i, ∏ j, ...)^2 = vandermondeDet σ^2
        rw [Finset.prod_pow, ← lemma_4_11]
    -- RHS reformulation: turn the nested compl product into an offDiag product.
    have hRHS :
        (∏ i : Fin k, ∏ j ∈ ({i}ᶜ : Finset (Fin k)), (σ i - σ j)) =
        ∏ p ∈ ((Finset.univ : Finset (Fin k)).offDiag), (σ p.1 - σ p.2) := by
      symm
      apply Finset.prod_finset_product
      intro p
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_compl,
        Finset.mem_singleton, ne_eq]
      exact ⟨fun h heq => h heq.symm, fun h heq => h heq.symm⟩
    rw [← hLHS, ← hRHS]
    exact hmathlib
  have hsq : (-1 : R) ^ (k * (k - 1) / 2) * (-1 : R) ^ (k * (k - 1) / 2) = 1 := by
    rw [← pow_add,
        show k * (k - 1) / 2 + k * (k - 1) / 2 = 2 * (k * (k - 1) / 2) from by ring,
        pow_mul, neg_one_sq, one_pow]
  linear_combination (-1 : R) ^ (k * (k - 1) / 2) * key -
    (vandermondeDet σ) ^ 2 * hsq

omit [IsAlgClosed C] in
/-- **Multiset/Finset bridge**: a sum over `(P.aroots C).powersetCard k` rewrites
    as a sum over `(Finset.univ : Finset (Fin _)).powersetCard k`. -/
private lemma sum_powersetCard_aroots_eq_sum_finset_univ (P : K[X]) (k : ℕ)
    (f : Multiset C → C) :
    (((P.aroots C).powersetCard k).map f).sum =
      ∑ I ∈ (Finset.univ : Finset (Fin (P.aroots C).toList.length)).powersetCard k,
        f (I.val.map (arootsEnum P)) := by
  classical
  conv_lhs =>
    rw [aroots_eq_univ_map_arootsEnum P]
    rw [Multiset.powersetCard_map]
    rw [Multiset.map_map]
    rw [← Finset.map_val_val_powersetCard]
    rw [Multiset.map_map]
  rw [Finset.sum_eq_multiset_sum]
  rfl

omit [IsAlgClosed C] in
/-- **BPR Proposition 4.9**. For `P : K[X]` and `k ≤ (P.aroots C).card`,
    the `(p - k)`-subdiscriminant of `P` is `a_p^{2k-2}` times the
    determinant of the `k × k` Newton matrix `Newt_{p-k}(P)`. (For monic
    `P`, the leading factor is `1`.) -/
theorem proposition_4_9 (P : K[X]) (k : ℕ)
    (hk : k ≤ (P.aroots C).card) :
    (sDisc P ((P.aroots C).card - k) : C) =
      algebraMap K C P.leadingCoeff ^ (2 * k - 2) *
        (newtMat P k : Matrix (Fin k) (Fin k) C).det := by
  classical
  -- Step A: rewrite newtMat as V * V^T.
  rw [← vandermondeRect_mul_transpose_eq_newtMat]
  -- Step B: apply Cauchy-Binet.
  rw [proposition_4_10 (vandermondeRect P k) (vandermondeRect P k).transpose]
  -- Step C+D: simplify each summand to `(vandermondeDet (arootsEnum ∘ s_I))^2`.
  have summand_simp : ∀ I ∈
      (Finset.univ : Finset (Fin (P.aroots C).toList.length)).powersetCard k,
      (if h : I.card = k then
         ((vandermondeRect P k).submatrix id (I.orderEmbOfFin h)).det *
         ((vandermondeRect P k).transpose.submatrix (I.orderEmbOfFin h) id).det
       else 0) =
      (-1 : C) ^ (k * (k - 1) / 2) *
        ((I.val.map (arootsEnum P) ×ˢ I.val.map (arootsEnum P) -
            (I.val.map (arootsEnum P)).map (fun a => (a, a))).map
          (fun ab : C × C => ab.1 - ab.2)).prod := by
    intro I hI
    have h : I.card = k := (Finset.mem_powersetCard.mp hI).2
    rw [dif_pos h]
    -- Transpose-submatrix identity
    have h_eq : (vandermondeRect P k).transpose.submatrix (I.orderEmbOfFin h) id =
                ((vandermondeRect P k).submatrix id (I.orderEmbOfFin h)).transpose := by
      ext; rfl
    rw [h_eq, Matrix.det_transpose]
    -- Identify as vandermondeDet
    rw [vandermondeRect_submatrix_eq P k I h]
    rw [show (vandermondeMat (arootsEnum P ∘ I.orderEmbOfFin h) :
              Matrix (Fin k) (Fin k) C).det =
        vandermondeDet (arootsEnum P ∘ I.orderEmbOfFin h) from rfl]
    rw [← sq]
    -- Apply squaring identity
    rw [vandermondeDet_sq_eq_signed_offdiag_multi (arootsEnum P ∘ I.orderEmbOfFin h)]
    -- Identify univ.val.map (arootsEnum ∘ s_I) = I.val.map arootsEnum
    rw [show ((Finset.univ : Finset (Fin k)).val.map
              (arootsEnum P ∘ I.orderEmbOfFin h)) =
        I.val.map (arootsEnum P) from by
        rw [show (arootsEnum P ∘ I.orderEmbOfFin h) =
            (arootsEnum P) ∘ (I.orderEmbOfFin h) from rfl]
        rw [← Multiset.map_map]
        rw [univ_map_orderEmbOfFin_val_eq]]
  rw [Finset.sum_congr rfl summand_simp]
  -- Factor out (-1)^N from the sum
  rw [← Finset.mul_sum]
  -- Step E: bridge the multiset sum in sDisc to a Finset sum.
  unfold sDisc
  have hp_sub : (P.aroots C).card - ((P.aroots C).card - k) = k := by omega
  rw [hp_sub]
  rw [sum_powersetCard_aroots_eq_sum_finset_univ P k
        (fun t => ((t ×ˢ t - t.map (fun a => (a, a))).map
                    (fun ab : C × C => ab.1 - ab.2)).prod)]

end Azurite.BPR.Chapter4
