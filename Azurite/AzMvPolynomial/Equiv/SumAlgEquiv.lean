import Azurite.AzMvPolynomial.SumAlgEquiv
import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Rename
import Azurite.AzMvPolynomial.Equiv.RenameHom
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Equivalence: `AzMvPolynomial.sumEquiv` ↔ Mathlib `MvPolynomial.eval₂`

Bridges the Azurite `sumEquiv` and `sumEquivSymm` to the corresponding
Mathlib `MvPolynomial.eval₂` formulations, across the `toMvPoly` bridges,
and bundles the result as an `AlgEquiv`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward bridge -/

/-- `AzMvPolynomial.sumEquiv` corresponds to an `MvPolynomial.eval₂` that
    sends `C r ↦ C (C r)`, outer variables `Fin.castAdd n j ↦ X j`, and
    inner variables `Fin.natAdd m j ↦ C (X j)`, across the `toMvPoly`
    bridges on both sides. -/
theorem AzMvPolynomial.toMvPoly_map_sumEquiv {m n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (m+n) R ord) :
    MvPolynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
        (AzMvPolynomial.sumEquiv p).toMvPoly
      = MvPolynomial.eval₂
          ((MvPolynomial.C : MvPolynomial (Fin n) R →+*
              MvPolynomial (Fin m) (MvPolynomial (Fin n) R)).comp
            (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
          (fun i : Fin (m+n) => Fin.addCases
            (fun j : Fin m => MvPolynomial.X j)
            (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
            i)
          p.toMvPoly := by
  unfold AzMvPolynomial.sumEquiv
  rw [AzMvPolynomial.toMvPoly_eval₂]
  set φ_az : R →+* AzMvPolynomial m (AzMvPolynomial n R ord) ord :=
    (AzMvPolynomial.CHom : AzMvPolynomial n R ord →+*
        AzMvPolynomial m (AzMvPolynomial n R ord) ord).comp
      (AzMvPolynomial.CHom : R →+* AzMvPolynomial n R ord)
  set f_az : Fin (m+n) → AzMvPolynomial m (AzMvPolynomial n R ord) ord :=
    fun i : Fin (m+n) => Fin.addCases
      (fun j : Fin m => AzMvPolynomial.X (ord := ord) j)
      (fun j : Fin n =>
        AzMvPolynomial.C (ord := ord)
          (AzMvPolynomial.X (ord := ord) j : AzMvPolynomial n R ord))
      i
  set φ_mv : R →+* MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    (MvPolynomial.C : MvPolynomial (Fin n) R →+*
      MvPolynomial (Fin m) (MvPolynomial (Fin n) R)).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)
  set f_mv : Fin (m+n) → MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    fun i : Fin (m+n) => Fin.addCases
      (fun j : Fin m => MvPolynomial.X j)
      (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
      i
  change ((MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))).comp
          (AzMvPolynomial.toMvPolyHom.comp (MvPolynomial.eval₂Hom φ_az f_az)))
          p.toMvPoly
        = (MvPolynomial.eval₂Hom φ_mv f_mv) p.toMvPoly
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzMvPolynomial.toMvPolyHom
            ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.C r)))
        = (MvPolynomial.eval₂Hom φ_mv f_mv) (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    show MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzMvPolynomial.toMvPoly
            (AzMvPolynomial.CHom
              (AzMvPolynomial.CHom r : AzMvPolynomial n R ord)
              : AzMvPolynomial m (AzMvPolynomial n R ord) ord))
        = MvPolynomial.C (MvPolynomial.C r)
    rw [show AzMvPolynomial.toMvPoly
          (AzMvPolynomial.CHom
            (AzMvPolynomial.CHom r : AzMvPolynomial n R ord)
            : AzMvPolynomial m (AzMvPolynomial n R ord) ord)
        = MvPolynomial.C (AzMvPolynomial.CHom r : AzMvPolynomial n R ord)
        from toMvPoly_C _,
        MvPolynomial.map_C]
    congr 1
    show AzMvPolynomial.toMvPoly
          (AzMvPolynomial.CHom r : AzMvPolynomial n R ord) = MvPolynomial.C r
    exact toMvPoly_C r
  · intro i
    show MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzMvPolynomial.toMvPolyHom
            ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.X i)))
        = (MvPolynomial.eval₂Hom φ_mv f_mv) (MvPolynomial.X i)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzMvPolynomial.toMvPolyHom (f_az (Fin.castAdd n j)))
          = f_mv (Fin.castAdd n j)
      simp only [f_az, f_mv, Fin.addCases_left]
      show MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzMvPolynomial.toMvPoly
              (AzMvPolynomial.X (ord := ord) j
                : AzMvPolynomial m (AzMvPolynomial n R ord) ord))
          = MvPolynomial.X j
      rw [show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.X (ord := ord) j
              : AzMvPolynomial m (AzMvPolynomial n R ord) ord)
          = MvPolynomial.X j from toMvPoly_X j,
          MvPolynomial.map_X]
    · show MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzMvPolynomial.toMvPolyHom (f_az (Fin.natAdd m j)))
          = f_mv (Fin.natAdd m j)
      simp only [f_az, f_mv, Fin.addCases_right]
      show MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzMvPolynomial.toMvPoly
              (AzMvPolynomial.C (ord := ord)
                (AzMvPolynomial.X (ord := ord) j : AzMvPolynomial n R ord)
                : AzMvPolynomial m (AzMvPolynomial n R ord) ord))
          = MvPolynomial.C (MvPolynomial.X j)
      rw [show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.C (ord := ord)
              (AzMvPolynomial.X (ord := ord) j : AzMvPolynomial n R ord)
              : AzMvPolynomial m (AzMvPolynomial n R ord) ord)
          = MvPolynomial.C (AzMvPolynomial.X (ord := ord) j
              : AzMvPolynomial n R ord)
          from toMvPoly_C _,
          MvPolynomial.map_C]
      congr 1
      show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.X (ord := ord) j : AzMvPolynomial n R ord)
          = MvPolynomial.X j
      exact toMvPoly_X j

/-! ### Reverse bridge -/

/-- `AzMvPolynomial.sumEquivSymm` corresponds to an `MvPolynomial.eval₂` that
    sends inner coefficient polynomials through `MvPolynomial.rename (Fin.natAdd m)`
    and outer variables `j : Fin m` to `X (Fin.castAdd n j)`, across the
    `toMvPoly` bridges. -/
theorem AzMvPolynomial.toMvPoly_sumEquivSymm {m n : ℕ} {ord : MonomialOrder}
    (q : AzMvPolynomial m (AzMvPolynomial n R ord) ord) :
    (AzMvPolynomial.sumEquivSymm q).toMvPoly
      = MvPolynomial.eval₂
          (MvPolynomial.eval₂Hom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
            (fun j : Fin n =>
              MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
          (fun i : Fin m =>
            MvPolynomial.X (Fin.castAdd n i : Fin (m+n)))
          (MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            q.toMvPoly) := by
  unfold AzMvPolynomial.sumEquivSymm
  rw [AzMvPolynomial.toMvPoly_eval₂]
  set φ_az : AzMvPolynomial n R ord →+* AzMvPolynomial (m+n) R ord :=
    AzMvPolynomial.renameMonotoneHom (R := R) (ord := ord)
      (Fin.natAdd m : Fin n → Fin (m+n)) (Fin.strictMono_natAdd m)
  set f_az : Fin m → AzMvPolynomial (m+n) R ord :=
    fun i : Fin m =>
      AzMvPolynomial.X (ord := ord) (Fin.castAdd n i : Fin (m+n))
  set ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin (m+n)) R :=
    MvPolynomial.eval₂Hom
      (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
      (fun j : Fin n =>
        MvPolynomial.X (Fin.natAdd m j : Fin (m+n)))
  set g : Fin m → MvPolynomial (Fin (m+n)) R :=
    fun i : Fin m =>
      MvPolynomial.X (Fin.castAdd n i : Fin (m+n))
  change (AzMvPolynomial.toMvPolyHom.comp (MvPolynomial.eval₂Hom φ_az f_az))
          q.toMvPoly
        = (MvPolynomial.eval₂Hom ψ g).comp
            (MvPolynomial.map
              (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord)))
            q.toMvPoly
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    show AzMvPolynomial.toMvPolyHom
          ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.C c))
        = (MvPolynomial.eval₂Hom ψ g)
          ((MvPolynomial.map
              (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord)))
              (MvPolynomial.C c))
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
    show AzMvPolynomial.toMvPoly (φ_az c)
        = ψ (AzMvPolynomial.toMvPoly c)
    -- φ_az c = renameMonotone (Fin.natAdd m) c
    show AzMvPolynomial.toMvPoly
          (c.renameMonotone (Fin.natAdd m : Fin n → Fin (m+n))
            (Fin.strictMono_natAdd m))
        = ψ (AzMvPolynomial.toMvPoly c)
    rw [AzMvPolynomial.toMvPoly_renameMonotone]
    -- Now: MvPolynomial.rename (Fin.natAdd m) c.toMvPoly = ψ c.toMvPoly
    -- ψ = eval₂Hom C (X ∘ natAdd m), and this equals MvPolynomial.rename (natAdd m)
    -- by ringHom_ext / ringHom equality.
    have hψ : ψ = (MvPolynomial.rename (Fin.natAdd m : Fin n → Fin (m+n))
                    : MvPolynomial (Fin n) R →ₐ[R]
                      MvPolynomial (Fin (m+n)) R).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show (MvPolynomial.eval₂Hom
                (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
                (fun j : Fin n =>
                  MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
              (MvPolynomial.C r) = MvPolynomial.rename _ (MvPolynomial.C r)
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.rename_C]
      · intro i
        show (MvPolynomial.eval₂Hom
                (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
                (fun j : Fin n =>
                  MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
              (MvPolynomial.X i) =
            MvPolynomial.rename (Fin.natAdd m : Fin n → Fin (m+n))
              (MvPolynomial.X i)
        rw [MvPolynomial.eval₂Hom_X', MvPolynomial.rename_X]
    rw [hψ]
    rfl
  · intro i
    show AzMvPolynomial.toMvPolyHom
          ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.X i))
        = (MvPolynomial.eval₂Hom ψ g)
          ((MvPolynomial.map
              (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord)))
              (MvPolynomial.X i))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
    show AzMvPolynomial.toMvPoly
          (AzMvPolynomial.X (ord := ord) (Fin.castAdd n i : Fin (m+n)))
        = MvPolynomial.X (Fin.castAdd n i : Fin (m+n))
    exact toMvPoly_X _

/-! ### Bundled `AlgEquiv` -/

section Bundled

variable {m n : ℕ} {ord : MonomialOrder}

/-- Injectivity of the composite bridge
    `MvPolynomial.map toMvPolyHom ∘ AzMvPolynomial.toMvPoly` on the iterated side. -/
private theorem map_toMvPoly_bridge_injective
    {q₁ q₂ : AzMvPolynomial m (AzMvPolynomial n R ord) ord}
    (h : MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          q₁.toMvPoly
        = MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          q₂.toMvPoly) :
    q₁ = q₂ :=
  toMvPoly_injective
    (MvPolynomial.map_injective _ toMvPoly_injective h)

/-- Ring-hom form of the forward `eval₂`. -/
private noncomputable def fwdHom : MvPolynomial (Fin (m+n)) R →+*
    MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : MvPolynomial (Fin n) R →+*
        MvPolynomial (Fin m) (MvPolynomial (Fin n) R)).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
    (fun i : Fin (m+n) => Fin.addCases
      (fun j : Fin m => MvPolynomial.X j)
      (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
      i)

/-- Ring-hom form of the reverse `eval₂`. -/
private noncomputable def revHom : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+*
    MvPolynomial (Fin (m+n)) R :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
      (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
    (fun i : Fin m => MvPolynomial.X (Fin.castAdd n i : Fin (m+n)))

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `revHom ∘ fwdHom = id` on `MvPolynomial (Fin (m+n)) R`. -/
private theorem revHom_comp_fwdHom :
    (revHom (R := R) (m := m) (n := n)).comp (fwdHom (R := R) (m := m) (n := n))
      = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    show revHom (fwdHom (MvPolynomial.C r)) = MvPolynomial.C r
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    show revHom (MvPolynomial.C (MvPolynomial.C r)) = MvPolynomial.C r
    unfold revHom
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
  · intro i
    show revHom (fwdHom (MvPolynomial.X i)) = MvPolynomial.X i
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_X']
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show revHom
          (Fin.addCases (motive := fun _ =>
              MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
            (fun j : Fin m => MvPolynomial.X j)
            (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
            (Fin.castAdd n j))
          = MvPolynomial.X (Fin.castAdd n j)
      rw [Fin.addCases_left]
      show revHom (MvPolynomial.X j : MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
          = MvPolynomial.X (Fin.castAdd n j)
      unfold revHom
      rw [MvPolynomial.eval₂Hom_X']
    · show revHom
          (Fin.addCases (motive := fun _ =>
              MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
            (fun j : Fin m => MvPolynomial.X j)
            (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
            (Fin.natAdd m j))
          = MvPolynomial.X (Fin.natAdd m j)
      rw [Fin.addCases_right]
      show revHom (MvPolynomial.C (MvPolynomial.X j)
            : MvPolynomial (Fin m) (MvPolynomial (Fin n) R))
          = MvPolynomial.X (Fin.natAdd m j)
      unfold revHom
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `fwdHom ∘ revHom = id` on `MvPolynomial (Fin m) (MvPolynomial (Fin n) R)`. -/
private theorem fwdHom_comp_revHom :
    (fwdHom (R := R) (m := m) (n := n)).comp (revHom (R := R) (m := m) (n := n))
      = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    show fwdHom (revHom (MvPolynomial.C c)) = MvPolynomial.C c
    unfold revHom
    rw [MvPolynomial.eval₂Hom_C]
    -- Need: fwdHom ((eval₂Hom C (X ∘ natAdd m)) c) = C c
    -- Key: this inner eval₂Hom = MvPolynomial.rename (Fin.natAdd m) as ring hom.
    -- So fwdHom (rename natAdd c) = C c.
    -- And fwdHom on rename natAdd c equals MvPolynomial.C c by ringHom_ext on c.
    revert c
    suffices h :
        (fwdHom (R := R) (m := m) (n := n)).comp
          (MvPolynomial.eval₂Hom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
            (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
        = (MvPolynomial.C : MvPolynomial (Fin n) R →+*
            MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) by
      intro c
      exact congrArg (fun f : MvPolynomial (Fin n) R →+*
          MvPolynomial (Fin m) (MvPolynomial (Fin n) R) => f c) h
    apply MvPolynomial.ringHom_ext
    · intro r
      show fwdHom
            ((MvPolynomial.eval₂Hom
              (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
              (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
              (MvPolynomial.C r))
          = MvPolynomial.C (MvPolynomial.C r)
      rw [MvPolynomial.eval₂Hom_C]
      unfold fwdHom
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    · intro j
      show fwdHom
            ((MvPolynomial.eval₂Hom
              (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
              (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
              (MvPolynomial.X j))
          = MvPolynomial.C (MvPolynomial.X j)
      rw [MvPolynomial.eval₂Hom_X']
      show fwdHom (MvPolynomial.X (Fin.natAdd m j : Fin (m+n)))
          = MvPolynomial.C (MvPolynomial.X j)
      unfold fwdHom
      rw [MvPolynomial.eval₂Hom_X', Fin.addCases_right]
  · intro i
    show fwdHom (revHom (MvPolynomial.X i)) = MvPolynomial.X i
    unfold revHom
    rw [MvPolynomial.eval₂Hom_X']
    show fwdHom (MvPolynomial.X (Fin.castAdd n i : Fin (m+n)))
        = MvPolynomial.X i
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_X', Fin.addCases_left]

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Pointwise form of `revHom_comp_fwdHom`. -/
private theorem reverse_forward_eval₂_eq_id (x : MvPolynomial (Fin (m+n)) R) :
    MvPolynomial.eval₂
        (MvPolynomial.eval₂Hom
          (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
          (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
        (fun i : Fin m => MvPolynomial.X (Fin.castAdd n i : Fin (m+n)))
        (MvPolynomial.eval₂
          ((MvPolynomial.C : MvPolynomial (Fin n) R →+*
              MvPolynomial (Fin m) (MvPolynomial (Fin n) R)).comp
            (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
          (fun i : Fin (m+n) => Fin.addCases
            (fun j : Fin m => MvPolynomial.X j)
            (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
            i)
          x) = x := by
  have h := RingHom.congr_fun (revHom_comp_fwdHom (R := R) (m := m) (n := n)) x
  simp only [RingHom.comp_apply, RingHom.id_apply, revHom, fwdHom,
             MvPolynomial.coe_eval₂Hom] at h
  exact h

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Pointwise form of `fwdHom_comp_revHom`. -/
private theorem forward_reverse_eval₂_eq_id
    (y : MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) :
    MvPolynomial.eval₂
        ((MvPolynomial.C : MvPolynomial (Fin n) R →+*
            MvPolynomial (Fin m) (MvPolynomial (Fin n) R)).comp
          (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (m+n) => Fin.addCases
          (fun j : Fin m => MvPolynomial.X j)
          (fun j : Fin n => MvPolynomial.C (MvPolynomial.X j))
          i)
        (MvPolynomial.eval₂
          (MvPolynomial.eval₂Hom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (m+n)) R)
            (fun j : Fin n => MvPolynomial.X (Fin.natAdd m j : Fin (m+n))))
          (fun i : Fin m => MvPolynomial.X (Fin.castAdd n i : Fin (m+n)))
          y) = y := by
  have h := RingHom.congr_fun (fwdHom_comp_revHom (R := R) (m := m) (n := n)) y
  simp only [RingHom.comp_apply, RingHom.id_apply, revHom, fwdHom,
             MvPolynomial.coe_eval₂Hom] at h
  exact h

private lemma left_inv_aux (p : AzMvPolynomial (m+n) R ord) :
    sumEquivSymm (sumEquiv p) = p :=
  toMvPoly_injective (by
    rw [AzMvPolynomial.toMvPoly_sumEquivSymm,
        AzMvPolynomial.toMvPoly_map_sumEquiv]
    exact reverse_forward_eval₂_eq_id p.toMvPoly)

private lemma right_inv_aux (q : AzMvPolynomial m (AzMvPolynomial n R ord) ord) :
    sumEquiv (sumEquivSymm q) = q :=
  map_toMvPoly_bridge_injective (by
    rw [AzMvPolynomial.toMvPoly_map_sumEquiv,
        AzMvPolynomial.toMvPoly_sumEquivSymm]
    apply forward_reverse_eval₂_eq_id)

private lemma map_add_aux (p q : AzMvPolynomial (m+n) R ord) :
    sumEquiv (p + q) = sumEquiv p + sumEquiv q :=
  map_toMvPoly_bridge_injective (by
    rw [toMvPoly_add, map_add,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        toMvPoly_add, MvPolynomial.eval₂_add])

private lemma map_mul_aux (p q : AzMvPolynomial (m+n) R ord) :
    sumEquiv (p * q) = sumEquiv p * sumEquiv q :=
  map_toMvPoly_bridge_injective (by
    rw [toMvPoly_mul, map_mul,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        AzMvPolynomial.toMvPoly_map_sumEquiv,
        toMvPoly_mul, MvPolynomial.eval₂_mul])

private lemma commutes_aux (r : R) :
    sumEquiv ((algebraMap R (AzMvPolynomial (m+n) R ord)) r) =
      algebraMap R (AzMvPolynomial m (AzMvPolynomial n R ord) ord) r :=
  map_toMvPoly_bridge_injective (by
    show MvPolynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzMvPolynomial.sumEquiv
            (AzMvPolynomial.C r : AzMvPolynomial (m+n) R ord)).toMvPoly
        = MvPolynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzMvPolynomial.C
              (AzMvPolynomial.C r : AzMvPolynomial n R ord)
              : AzMvPolynomial m (AzMvPolynomial n R ord) ord).toMvPoly
    rw [AzMvPolynomial.toMvPoly_map_sumEquiv, toMvPoly_C, toMvPoly_C,
        MvPolynomial.eval₂_C, RingHom.comp_apply, MvPolynomial.map_C]
    show MvPolynomial.C (MvPolynomial.C r)
        = MvPolynomial.C
            (AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord)
              (AzMvPolynomial.C r : AzMvPolynomial n R ord))
    rw [show AzMvPolynomial.toMvPolyHom (R := R) (n := n) (ord := ord)
            (AzMvPolynomial.C r : AzMvPolynomial n R ord)
          = MvPolynomial.C r from toMvPoly_C r])

/-- `AzMvPolynomial.sumEquiv` bundled as an `R`-algebra isomorphism. -/
noncomputable def AzMvPolynomial.sumAlgEquiv :
    AzMvPolynomial (m+n) R ord ≃ₐ[R]
      AzMvPolynomial m (AzMvPolynomial n R ord) ord where
  toFun := AzMvPolynomial.sumEquiv
  invFun := AzMvPolynomial.sumEquivSymm
  left_inv := left_inv_aux
  right_inv := right_inv_aux
  map_add' := map_add_aux
  map_mul' := map_mul_aux
  commutes' := commutes_aux

end Bundled

end Azurite
