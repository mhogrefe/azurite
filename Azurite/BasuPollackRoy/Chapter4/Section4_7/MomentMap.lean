import Azurite.BasuPollackRoy.Chapter4.Section4_7.HermitianNorm
import Azurite.BasuPollackRoy.Chapter4.Section4_7.AffineCharts

/-!
# BPR §4.7, Proposition 4.106: the moment-map embedding of `ℙ_k(C)`

To establish projective completeness, BPR embeds `ℙ_k(C)` into a real matrix space via the
orthogonal projector onto the line. For a nonzero vector `v ∈ Cᵏ⁺¹`, the rank-one Hermitian
projector onto the line `C·v` is `P(v) = (v ⊗ v̄)/‖v‖²`, with `(j,l)` entry `vⱼ v̄ₗ / ‖v‖²`. We
record the real and imaginary parts of these entries through the order-free maps `Ri.reL`/`Ri.imL`,
bundle them into a single real-valued function `momentFn v` on a finite index, and show this
function is invariant under nonzero complex scaling of `v`. Hence it descends to a well-defined map
`momentMap : ℙ_k(C) → R^N`, which we prove is **injective**: the projector recovers its line.

This file is the *algebraic* core of the embedding step; topological properties (closed, bounded,
homeomorphism onto its image) are handled separately.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### The realified projector entries -/

/-- The real part of the `(j,l)` entry `vⱼ v̄ₗ / ‖v‖²` of the projector onto the line of `v`. -/
noncomputable def projReV (v : Fin (k + 1) → Ri R) (j l : Fin (k + 1)) : R :=
  (Ri.reL (v j) * Ri.reL (v l) + Ri.imL (v j) * Ri.imL (v l)) / hermNormSq v

/-- The imaginary part of the `(j,l)` entry `vⱼ v̄ₗ / ‖v‖²` of the projector onto the line of `v`. -/
noncomputable def projImV (v : Fin (k + 1) → Ri R) (j l : Fin (k + 1)) : R :=
  (Ri.imL (v j) * Ri.reL (v l) - Ri.reL (v j) * Ri.imL (v l)) / hermNormSq v

/-- The **moment function** of a raw vector: the real and imaginary parts of all entries of the
Hermitian projector onto the line of `v`, bundled into a single real-valued function on the
finite index set `(Fin (k+1) × Fin (k+1)) ⊕ (Fin (k+1) × Fin (k+1))`. -/
noncomputable def momentFn (v : Fin (k + 1) → Ri R) :
    (Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1)) → R :=
  Sum.elim (fun p => projReV v p.1 p.2) (fun p => projImV v p.1 p.2)

set_option linter.unusedSectionVars false in
@[simp] theorem momentFn_inl (v : Fin (k + 1) → Ri R) (p : Fin (k + 1) × Fin (k + 1)) :
    momentFn v (Sum.inl p) = projReV v p.1 p.2 := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem momentFn_inr (v : Fin (k + 1) → Ri R) (p : Fin (k + 1) × Fin (k + 1)) :
    momentFn v (Sum.inr p) = projImV v p.1 p.2 := rfl

/-! ### Behavior of `reL`/`imL` and `hermNormSq` under complex scaling -/

set_option linter.unusedSectionVars false in
/-- Real part of a scaled coordinate `(c • v) j = c * v j`. -/
theorem reL_smul_apply (c : Ri R) (v : Fin (k + 1) → Ri R) (j : Fin (k + 1)) :
    Ri.reL ((c • v) j) = Ri.reL c * Ri.reL (v j) - Ri.imL c * Ri.imL (v j) := by
  rw [Pi.smul_apply, smul_eq_mul, reL_mul]

set_option linter.unusedSectionVars false in
/-- Imaginary part of a scaled coordinate `(c • v) j = c * v j`. -/
theorem imL_smul_apply (c : Ri R) (v : Fin (k + 1) → Ri R) (j : Fin (k + 1)) :
    Ri.imL ((c • v) j) = Ri.reL c * Ri.imL (v j) + Ri.imL c * Ri.reL (v j) := by
  rw [Pi.smul_apply, smul_eq_mul, imL_mul]

set_option linter.unusedSectionVars false in
/-- The Hermitian norm scales by `|c|² = (Re c)² + (Im c)²`. -/
theorem hermNormSq_smul (c : Ri R) (v : Fin (k + 1) → Ri R) :
    hermNormSq (c • v) = (Ri.reL c ^ 2 + Ri.imL c ^ 2) * hermNormSq v := by
  rw [hermNormSq, hermNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [reL_smul_apply, imL_smul_apply]
  ring

set_option linter.unusedSectionVars false in
/-- `|c|² = (Re c)² + (Im c)² > 0` for a nonzero `c`. -/
theorem normSqC_pos {c : Ri R} (hc : c ≠ 0) : 0 < Ri.reL c ^ 2 + Ri.imL c ^ 2 := by
  refine lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) fun h => hc ?_
  rw [reL_eq_zero_and_imL_eq_zero_iff]
  rw [eq_comm, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff] at h
  exact ⟨h.1, h.2⟩

/-! ### Scaling invariance of the moment function -/

set_option linter.unusedSectionVars false in
/-- **Scaling invariance.** The moment function is unchanged under nonzero complex scaling of the
vector; this is what lets it descend to projective space. -/
theorem momentFn_smul {c : Ri R} (hc : c ≠ 0) (v : Fin (k + 1) → Ri R) (hv : v ≠ 0) :
    momentFn (c • v) = momentFn v := by
  have hN : (0 : R) < Ri.reL c ^ 2 + Ri.imL c ^ 2 := normSqC_pos hc
  have hNne : Ri.reL c ^ 2 + Ri.imL c ^ 2 ≠ 0 := ne_of_gt hN
  have hvN : (0 : R) < hermNormSq v := hermNormSq_pos hv
  funext s
  obtain ⟨p⟩ | ⟨p⟩ := s
  · -- real part entry
    simp only [momentFn_inl, projReV, hermNormSq_smul, reL_smul_apply, imL_smul_apply]
    rw [show (Ri.reL c * Ri.reL (v p.1) - Ri.imL c * Ri.imL (v p.1)) *
              (Ri.reL c * Ri.reL (v p.2) - Ri.imL c * Ri.imL (v p.2)) +
            (Ri.reL c * Ri.imL (v p.1) + Ri.imL c * Ri.reL (v p.1)) *
              (Ri.reL c * Ri.imL (v p.2) + Ri.imL c * Ri.reL (v p.2))
          = (Ri.reL c ^ 2 + Ri.imL c ^ 2) *
              (Ri.reL (v p.1) * Ri.reL (v p.2) + Ri.imL (v p.1) * Ri.imL (v p.2)) by ring,
      mul_div_mul_left _ _ hNne]
  · -- imaginary part entry
    simp only [momentFn_inr, projImV, hermNormSq_smul, reL_smul_apply, imL_smul_apply]
    rw [show (Ri.reL c * Ri.imL (v p.1) + Ri.imL c * Ri.reL (v p.1)) *
              (Ri.reL c * Ri.reL (v p.2) - Ri.imL c * Ri.imL (v p.2)) -
            (Ri.reL c * Ri.reL (v p.1) - Ri.imL c * Ri.imL (v p.1)) *
              (Ri.reL c * Ri.imL (v p.2) + Ri.imL c * Ri.reL (v p.2))
          = (Ri.reL c ^ 2 + Ri.imL c ^ 2) *
              (Ri.imL (v p.1) * Ri.reL (v p.2) - Ri.reL (v p.1) * Ri.imL (v p.2)) by ring,
      mul_div_mul_left _ _ hNne]

/-! ### The moment map on `ℙ_k(C)` -/

/-- **The moment-map embedding.** Sends a line `x ∈ ℙ_k(C)` to the real coordinates of the Hermitian
projector onto it, computed via any representative `x.rep`. Well-definedness is `momentFn_smul`. -/
noncomputable def momentMap (x : complexProjectiveSpace R k) :
    (Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1)) → R :=
  momentFn x.rep

set_option linter.unusedSectionVars false in
/-- The moment map computed on homogeneous coordinates agrees with the moment function of the raw
vector. -/
theorem momentMap_mkLine (v : Fin (k + 1) → Ri R) (hv : v ≠ 0) :
    momentMap (mkLine v hv) = momentFn v := by
  obtain ⟨c, hc, hrep⟩ :=
    (mkLine_eq_mkLine_iff (mkLine v hv).rep v (mkLine v hv).rep_nonzero hv).1
      (by rw [mkLine, Projectivization.mk_rep])
  rw [momentMap, hrep, momentFn_smul hc v hv]

/-! ### Injectivity -/

set_option linter.unusedSectionVars false in
/-- Cleared-denominator form of the equality of real-part projector entries. -/
private theorem projReV_eq_cleared {v w : Fin (k + 1) → Ri R} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ j l, projReV v j l = projReV w j l) (j l : Fin (k + 1)) :
    (Ri.reL (v j) * Ri.reL (v l) + Ri.imL (v j) * Ri.imL (v l)) * hermNormSq w =
      (Ri.reL (w j) * Ri.reL (w l) + Ri.imL (w j) * Ri.imL (w l)) * hermNormSq v := by
  have := h j l
  rw [projReV, projReV,
    div_eq_div_iff (ne_of_gt (hermNormSq_pos hv)) (ne_of_gt (hermNormSq_pos hw))] at this
  exact this

set_option linter.unusedSectionVars false in
/-- Cleared-denominator form of the equality of imaginary-part projector entries. -/
private theorem projImV_eq_cleared {v w : Fin (k + 1) → Ri R} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ j l, projImV v j l = projImV w j l) (j l : Fin (k + 1)) :
    (Ri.imL (v j) * Ri.reL (v l) - Ri.reL (v j) * Ri.imL (v l)) * hermNormSq w =
      (Ri.imL (w j) * Ri.reL (w l) - Ri.reL (w j) * Ri.imL (w l)) * hermNormSq v := by
  have := h j l
  rw [projImV, projImV,
    div_eq_div_iff (ne_of_gt (hermNormSq_pos hv)) (ne_of_gt (hermNormSq_pos hw))] at this
  exact this

set_option linter.unusedSectionVars false in
/-- `vⱼ = 0` iff `wⱼ = 0` when the moment functions agree: forced by the diagonal entries. -/
private theorem eq_zero_iff_of_projReV {v w : Fin (k + 1) → Ri R} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : ∀ j l, projReV v j l = projReV w j l) (j : Fin (k + 1)) :
    v j = 0 ↔ w j = 0 := by
  have hd := projReV_eq_cleared hv hw h j j
  have hvN : (0 : R) < hermNormSq v := hermNormSq_pos hv
  have hwN : (0 : R) < hermNormSq w := hermNormSq_pos hw
  rw [reL_eq_zero_and_imL_eq_zero_iff, reL_eq_zero_and_imL_eq_zero_iff]
  constructor
  · rintro ⟨hre, him⟩
    rw [hre, him] at hd
    -- `0 = (reL wⱼ² + imL wⱼ²) * ‖v‖²`, so the bracket is 0
    have hb : Ri.reL (w j) * Ri.reL (w j) + Ri.imL (w j) * Ri.imL (w j) = 0 := by
      have hbn : 0 ≤ Ri.reL (w j) * Ri.reL (w j) + Ri.imL (w j) * Ri.imL (w j) :=
        add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      nlinarith [hd, hvN, hbn]
    rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (mul_self_nonneg _),
      mul_self_eq_zero, mul_self_eq_zero] at hb
    exact hb
  · rintro ⟨hre, him⟩
    rw [hre, him] at hd
    have hb : Ri.reL (v j) * Ri.reL (v j) + Ri.imL (v j) * Ri.imL (v j) = 0 := by
      have hbn : 0 ≤ Ri.reL (v j) * Ri.reL (v j) + Ri.imL (v j) * Ri.imL (v j) :=
        add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      nlinarith [hd, hwN, hbn]
    rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (mul_self_nonneg _),
      mul_self_eq_zero, mul_self_eq_zero] at hb
    exact hb

set_option linter.unusedSectionVars false in
/-- **Key cross-ratio identity.** If the moment functions of `v` and `w` agree, then for the chosen
pivot `m` and any index `j`, the cross terms `vⱼ wₘ` and `vₘ wⱼ` coincide (`vⱼ wₘ − vₘ wⱼ = 0`),
proven by showing the squared Hermitian length of `vⱼ wₘ − vₘ wⱼ` vanishes. -/
private theorem cross_eq {v w : Fin (k + 1) → Ri R} (hv : v ≠ 0) (hw : w ≠ 0)
    (hre : ∀ j l, projReV v j l = projReV w j l) (him : ∀ j l, projImV v j l = projImV w j l)
    (m j : Fin (k + 1)) (hvm : v m ≠ 0) : v j * w m = v m * w j := by
  set s := hermNormSq v with hs
  set t := hermNormSq w with ht
  have htne : t ≠ 0 := ne_of_gt (hermNormSq_pos hw)
  -- abbreviations
  set a₁ := Ri.reL (v j); set b₁ := Ri.imL (v j)
  set a₂ := Ri.reL (v m); set b₂ := Ri.imL (v m)
  set c₁ := Ri.reL (w j); set d₁ := Ri.imL (w j)
  set c₂ := Ri.reL (w m); set d₂ := Ri.imL (w m)
  -- the cleared entry equations we need (in `a..d, s, t` form)
  have Ejm : (a₁ * a₂ + b₁ * b₂) * t = (c₁ * c₂ + d₁ * d₂) * s :=
    projReV_eq_cleared hv hw hre j m
  have Imm : (b₁ * a₂ - a₁ * b₂) * t = (d₁ * c₂ - c₁ * d₂) * s :=
    projImV_eq_cleared hv hw him j m
  have Dmm : (a₂ * a₂ + b₂ * b₂) * t = (c₂ * c₂ + d₂ * d₂) * s :=
    projReV_eq_cleared hv hw hre m m
  -- write δ = (v j) * (w m) - (v m) * (w j); compute its real/imaginary parts
  set Reδ := (a₁ * c₂ - b₁ * d₂) - (a₂ * c₁ - b₂ * d₁) with hReδ
  set Imδ := (a₁ * d₂ + b₁ * c₂) - (a₂ * d₁ + b₂ * c₁) with hImδ
  -- `δ * conj(v m)` has vanishing real and imaginary parts after multiplying by `t`:
  -- this is the telescoping `δ v̄_m t = s·(w_j |w_m|² - |w_m|² w_j) = 0`.
  have hRe : (Reδ * a₂ + Imδ * b₂) * t = 0 := by
    rw [hReδ, hImδ]; linear_combination c₂ * Ejm - d₂ * Imm - c₁ * Dmm
  have hIm : (Imδ * a₂ - Reδ * b₂) * t = 0 := by
    rw [hReδ, hImδ]; linear_combination d₂ * Ejm + c₂ * Imm - d₁ * Dmm
  -- cancel `t`
  have hRe' : Reδ * a₂ + Imδ * b₂ = 0 := by
    rcases mul_eq_zero.mp hRe with h | h
    · exact h
    · exact absurd h htne
  have hIm' : Imδ * a₂ - Reδ * b₂ = 0 := by
    rcases mul_eq_zero.mp hIm with h | h
    · exact h
    · exact absurd h htne
  -- `a₂² + b₂² = |v m|² > 0`, so `Reδ = Imδ = 0`
  have hN : (0 : R) < a₂ ^ 2 + b₂ ^ 2 := normSqC_pos hvm
  have hNne : a₂ ^ 2 + b₂ ^ 2 ≠ 0 := ne_of_gt hN
  have hReδ0 : Reδ = 0 := by
    have h : Reδ * (a₂ ^ 2 + b₂ ^ 2) = 0 := by linear_combination a₂ * hRe' - b₂ * hIm'
    exact (mul_eq_zero.mp h).resolve_right hNne
  have hImδ0 : Imδ = 0 := by
    have h : Imδ * (a₂ ^ 2 + b₂ ^ 2) = 0 := by linear_combination a₂ * hIm' + b₂ * hRe'
    exact (mul_eq_zero.mp h).resolve_right hNne
  -- conclude δ = 0
  refine sub_eq_zero.mp ((reL_eq_zero_and_imL_eq_zero_iff _).2 ⟨?_, ?_⟩)
  · rw [map_sub, reL_mul, reL_mul]; rw [← hReδ0, hReδ]
  · rw [map_sub, imL_mul, imL_mul]; rw [← hImδ0, hImδ]

set_option linter.unusedSectionVars false in
/-- **Injectivity of the moment map.** Two lines with the same Hermitian projector are equal: the
projector recovers its line. -/
theorem momentMap_injective :
    Function.Injective (momentMap : complexProjectiveSpace R k → _) := by
  intro x y hxy
  -- pass to representatives
  set v := x.rep with hvdef
  set w := y.rep with hwdef
  have hv : v ≠ 0 := x.rep_nonzero
  have hw : w ≠ 0 := y.rep_nonzero
  -- entrywise equalities from `momentMap x = momentMap y`
  have hre : ∀ j l, projReV v j l = projReV w j l := fun j l =>
    congrFun hxy (Sum.inl (j, l))
  have him : ∀ j l, projImV v j l = projImV w j l := fun j l =>
    congrFun hxy (Sum.inr (j, l))
  -- choose a pivot index `m` with `v m ≠ 0`
  have hex : ∃ m, v m ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨m, hvm⟩ := hex
  have hwm : w m ≠ 0 := (eq_zero_iff_of_projReV hv hw hre m).not.1 hvm
  -- the scalar `c = v m / w m`
  set c : Ri R := v m * (w m)⁻¹ with hc
  have hcne : c ≠ 0 := mul_ne_zero hvm (inv_ne_zero hwm)
  -- show `v = c • w`
  have hvcw : v = c • w := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, hc]
    -- `(v m * (w m)⁻¹) * w j = v m * w j * (w m)⁻¹ = v j * w m * (w m)⁻¹ = v j`
    rw [mul_right_comm, ← cross_eq hv hw hre him m j hvm, mul_assoc, mul_inv_cancel₀ hwm, mul_one]
  -- conclude the lines are equal
  have hmk : mkLine v hv = mkLine w hw := (mkLine_eq_mkLine_iff v w hv hw).2 ⟨c, hcne, hvcw⟩
  rw [mkLine, mkLine] at hmk
  have hx : Projectivization.mk (Ri R) v hv = x := x.mk_rep
  have hy : Projectivization.mk (Ri R) w hw = y := y.mk_rep
  rw [hx, hy] at hmk
  exact hmk

end Azurite.BPR.Chapter4
