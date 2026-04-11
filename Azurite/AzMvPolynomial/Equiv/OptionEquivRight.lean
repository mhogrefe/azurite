import Azurite.AzMvPolynomial.OptionEquivRight
import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra
import Azurite.AzPolynomial.Equiv.Algebra
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Equivalence: `AzMvPolynomial.optionEquivRight` ↔ Mathlib `MvPolynomial.eval₂`

Bridges the Azurite `optionEquivRight` and `optionEquivRightSymm` to the
corresponding Mathlib `MvPolynomial.eval₂` formulations, across the
`toMvPoly` / `toPoly` bridges.
-/

namespace Azurite

open AzMvPolynomial AzPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward bridge -/

/-- `AzMvPolynomial.optionEquivRight` corresponds to an `MvPolynomial.eval₂`
    that sends `C r ↦ C (Polynomial.C r)`, `X 0 ↦ C Polynomial.X`, and
    `X (succ k) ↦ X k`, across the `toMvPoly` / `toPoly` bridges. -/
theorem AzMvPolynomial.toMvPoly_map_optionEquivRight {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (n+1) R ord) :
    MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
        (AzMvPolynomial.optionEquivRight p).toMvPoly
      = MvPolynomial.eval₂
          ((MvPolynomial.C : Polynomial R →+*
              MvPolynomial (Fin n) (Polynomial R)).comp
            (Polynomial.C : R →+* Polynomial R))
          (fun i : Fin (n+1) => Fin.cases (MvPolynomial.C Polynomial.X)
              (fun k => MvPolynomial.X k) i)
          p.toMvPoly := by
  unfold AzMvPolynomial.optionEquivRight
  rw [AzMvPolynomial.toMvPoly_eval₂]
  set φ_az : R →+* AzMvPolynomial n (AzPolynomial R) ord :=
    (AzMvPolynomial.CHom (n := n) (ord := ord)).comp AzPolynomial.CHom
  set f_az : Fin (n+1) → AzMvPolynomial n (AzPolynomial R) ord :=
    (fun i => Fin.cases
      (AzMvPolynomial.C (ord := ord) (AzPolynomial.X : AzPolynomial R))
      (fun k => AzMvPolynomial.X (ord := ord) k) i)
  set φ_mv : R →+* MvPolynomial (Fin n) (Polynomial R) :=
    (MvPolynomial.C : Polynomial R →+*
        MvPolynomial (Fin n) (Polynomial R)).comp
      (Polynomial.C : R →+* Polynomial R)
  set f_mv : Fin (n+1) → MvPolynomial (Fin n) (Polynomial R) :=
    fun i => Fin.cases (MvPolynomial.C Polynomial.X)
      (fun k => MvPolynomial.X k) i
  change ((MvPolynomial.map
            (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)).comp
          (AzMvPolynomial.toMvPolyHom.comp (MvPolynomial.eval₂Hom φ_az f_az)))
          p.toMvPoly
        = (MvPolynomial.eval₂Hom φ_mv f_mv) p.toMvPoly
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          (AzMvPolynomial.toMvPolyHom
            ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.C r)))
        = (MvPolynomial.eval₂Hom φ_mv f_mv) (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    show MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          (AzMvPolynomial.toMvPoly
            (AzMvPolynomial.CHom (n := n) (ord := ord)
              (AzPolynomial.CHom r : AzPolynomial R)))
        = MvPolynomial.C (Polynomial.C r)
    rw [show AzMvPolynomial.toMvPoly
          (AzMvPolynomial.CHom (n := n) (ord := ord)
            (AzPolynomial.CHom r : AzPolynomial R))
        = MvPolynomial.C (AzPolynomial.CHom r : AzPolynomial R)
        from toMvPoly_C _, MvPolynomial.map_C]
    show MvPolynomial.C
          (AzPolynomial.toPolyHom (AzPolynomial.CHom r : AzPolynomial R))
        = MvPolynomial.C (Polynomial.C r)
    congr 1
    show AzPolynomial.toPoly (AzPolynomial.C r) = Polynomial.C r
    exact toPoly_C r
  · intro i
    show MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          (AzMvPolynomial.toMvPolyHom
            ((MvPolynomial.eval₂Hom φ_az f_az) (MvPolynomial.X i)))
        = (MvPolynomial.eval₂Hom φ_mv f_mv) (MvPolynomial.X i)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    refine Fin.cases ?_ ?_ i
    · show MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
            (AzMvPolynomial.toMvPolyHom
              (AzMvPolynomial.C (ord := ord)
                (AzPolynomial.X : AzPolynomial R)))
          = MvPolynomial.C Polynomial.X
      rw [show AzMvPolynomial.toMvPolyHom
            (AzMvPolynomial.C (ord := ord)
              (AzPolynomial.X : AzPolynomial R))
          = MvPolynomial.C (AzPolynomial.X : AzPolynomial R)
          from toMvPoly_C _, MvPolynomial.map_C]
      congr 1
      exact toPoly_X
    · intro k
      show MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
            (AzMvPolynomial.toMvPolyHom
              (AzMvPolynomial.X (ord := ord) k : AzMvPolynomial n (AzPolynomial R) ord))
          = MvPolynomial.X k
      rw [show AzMvPolynomial.toMvPolyHom
            (AzMvPolynomial.X (ord := ord) k : AzMvPolynomial n (AzPolynomial R) ord)
          = MvPolynomial.X k from toMvPoly_X k, MvPolynomial.map_X]

/-! ### Reverse bridge -/

/-- `AzMvPolynomial.optionEquivRightSymm` corresponds to an `MvPolynomial.eval₂`
    that sends `C c ↦ Polynomial.eval₂ C (X 0) c` (substituting `X 0` for
    `Polynomial.X`) and `X k ↦ X k.succ`, across the `toMvPoly` / `toPoly`
    bridges. -/
theorem AzMvPolynomial.toMvPoly_optionEquivRightSymm {n : ℕ} {ord : MonomialOrder}
    (q : AzMvPolynomial n (AzPolynomial R) ord) :
    (AzMvPolynomial.optionEquivRightSymm q).toMvPoly
      = MvPolynomial.eval₂
          (Polynomial.eval₂RingHom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
            (MvPolynomial.X (0 : Fin (n+1))))
          (fun k : Fin n => MvPolynomial.X k.succ)
          (MvPolynomial.map
            (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
            q.toMvPoly) := by
  unfold AzMvPolynomial.optionEquivRightSymm
  rw [AzMvPolynomial.toMvPoly_eval₂]
  set φ_az : AzPolynomial R →+* AzMvPolynomial (n+1) R ord :=
    AzPolynomial.eval₂Hom (AzMvPolynomial.CHom (n := n+1) (ord := ord))
      (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))
  set f_az : Fin n → AzMvPolynomial (n+1) R ord :=
    fun k => AzMvPolynomial.X (ord := ord) (k.succ : Fin (n+1))
  set ψ : Polynomial R →+* MvPolynomial (Fin (n+1)) R :=
    Polynomial.eval₂RingHom
      (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
      (MvPolynomial.X (0 : Fin (n+1)))
  set g : Fin n → MvPolynomial (Fin (n+1)) R :=
    fun k => MvPolynomial.X k.succ
  change (AzMvPolynomial.toMvPolyHom.comp (MvPolynomial.eval₂Hom φ_az f_az))
          q.toMvPoly
        = (MvPolynomial.eval₂Hom ψ g).comp
            (MvPolynomial.map
              (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R))
            q.toMvPoly
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    show AzMvPolynomial.toMvPolyHom ((MvPolynomial.eval₂Hom φ_az f_az)
            (MvPolynomial.C c))
        = (MvPolynomial.eval₂Hom ψ g)
            ((MvPolynomial.map
              (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R))
              (MvPolynomial.C c))
    rw [MvPolynomial.eval₂Hom_C]
    show AzMvPolynomial.toMvPoly (φ_az c)
        = (MvPolynomial.eval₂Hom ψ g)
            ((MvPolynomial.map
              (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R))
              (MvPolynomial.C c))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
    show AzMvPolynomial.toMvPoly
          (AzPolynomial.eval₂Hom
            (AzMvPolynomial.CHom (n := n+1) (ord := ord))
            (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1))) c)
        = ψ (AzPolynomial.toPolyHom c)
    rw [AzPolynomial.eval₂Hom_eq_polynomial_eval₂]
    show AzMvPolynomial.toMvPolyHom
          (Polynomial.eval₂
            (AzMvPolynomial.CHom (n := n+1) (ord := ord))
            (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))
            (AzPolynomial.toPoly c))
        = (Polynomial.eval₂RingHom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
            (MvPolynomial.X (0 : Fin (n+1))))
            (AzPolynomial.toPoly c)
    rw [Polynomial.hom_eval₂]
    show Polynomial.eval₂
          (AzMvPolynomial.toMvPolyHom.comp
            (AzMvPolynomial.CHom (n := n+1) (ord := ord)))
          (AzMvPolynomial.toMvPolyHom
            (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1))))
          (AzPolynomial.toPoly c)
        = Polynomial.eval₂
            (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
            (MvPolynomial.X (0 : Fin (n+1)))
            (AzPolynomial.toPoly c)
    congr 1
    · apply RingHom.ext
      intro r
      show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.CHom (n := n+1) (ord := ord) r)
          = MvPolynomial.C r
      exact toMvPoly_C r
    · exact toMvPoly_X _
  · intro k
    show AzMvPolynomial.toMvPolyHom ((MvPolynomial.eval₂Hom φ_az f_az)
            (MvPolynomial.X k))
        = (MvPolynomial.eval₂Hom ψ g)
            ((MvPolynomial.map
              (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R))
              (MvPolynomial.X k))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
    show AzMvPolynomial.toMvPoly
          (AzMvPolynomial.X (ord := ord) (k.succ : Fin (n+1)))
        = MvPolynomial.X k.succ
    exact toMvPoly_X _

/-! ### Bundled `RingEquiv` -/

section Bundled

variable {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] in
/-- Injectivity of the composite bridge
    `MvPolynomial.map toPolyHom ∘ AzMvPolynomial.toMvPoly`. -/
private theorem map_toPoly_bridge_injective
    {q₁ q₂ : AzMvPolynomial n (AzPolynomial R) ord}
    (h : MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          q₁.toMvPoly
        = MvPolynomial.map (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          q₂.toMvPoly) :
    q₁ = q₂ :=
  toMvPoly_injective
    (MvPolynomial.map_injective _ (fun _ _ hab => toPoly_inj.mp hab) h)

/-- Ring hom form of the forward `eval₂`, used to compose with the reverse. -/
private noncomputable def fwdHom : MvPolynomial (Fin (n+1)) R →+*
    MvPolynomial (Fin n) (Polynomial R) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : Polynomial R →+*
        MvPolynomial (Fin n) (Polynomial R)).comp
      (Polynomial.C : R →+* Polynomial R))
    (fun i : Fin (n+1) => Fin.cases (MvPolynomial.C Polynomial.X)
        (fun k => MvPolynomial.X k) i)

/-- Ring hom form of the reverse `eval₂`. -/
private noncomputable def revHom : MvPolynomial (Fin n) (Polynomial R) →+*
    MvPolynomial (Fin (n+1)) R :=
  MvPolynomial.eval₂Hom
    (Polynomial.eval₂RingHom
      (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
      (MvPolynomial.X (0 : Fin (n+1))))
    (fun k : Fin n => MvPolynomial.X k.succ)

omit [NoZeroDivisors R] [DecidableEq R] in
/-- The composition `revHom ∘ fwdHom` is the identity on
    `MvPolynomial (Fin (n+1)) R`. -/
private theorem revHom_comp_fwdHom :
    (revHom (R := R) (n := n)).comp (fwdHom (R := R) (n := n)) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    show revHom (fwdHom (MvPolynomial.C r)) = MvPolynomial.C r
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    show revHom (MvPolynomial.C (Polynomial.C r)) = MvPolynomial.C r
    unfold revHom
    rw [MvPolynomial.eval₂Hom_C]
    show (Polynomial.eval₂RingHom MvPolynomial.C
            (MvPolynomial.X (0 : Fin (n+1)))) (Polynomial.C r)
        = MvPolynomial.C r
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  · intro i
    show revHom (fwdHom (MvPolynomial.X i)) = MvPolynomial.X i
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_X']
    refine Fin.cases ?_ ?_ i
    · show revHom (MvPolynomial.C Polynomial.X) = MvPolynomial.X (0 : Fin (n+1))
      unfold revHom
      rw [MvPolynomial.eval₂Hom_C]
      show (Polynomial.eval₂RingHom MvPolynomial.C
              (MvPolynomial.X (0 : Fin (n+1)))) Polynomial.X
          = MvPolynomial.X (0 : Fin (n+1))
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    · intro k
      show revHom (MvPolynomial.X k) = MvPolynomial.X k.succ
      unfold revHom
      rw [MvPolynomial.eval₂Hom_X']

omit [NoZeroDivisors R] [DecidableEq R] in
/-- The composition `fwdHom ∘ revHom` is the identity on
    `MvPolynomial (Fin n) (Polynomial R)`. -/
private theorem fwdHom_comp_revHom :
    (fwdHom (R := R) (n := n)).comp (revHom (R := R) (n := n)) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    show fwdHom (revHom (MvPolynomial.C c)) = MvPolynomial.C c
    unfold revHom
    rw [MvPolynomial.eval₂Hom_C]
    -- Goal: fwdHom (Polynomial.eval₂RingHom MvPolynomial.C (X 0) c) = C c
    -- Use Polynomial.hom_eval₂ to push fwdHom through the Polynomial.eval₂
    show fwdHom ((Polynomial.eval₂RingHom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
            (MvPolynomial.X (0 : Fin (n+1)))) c)
        = MvPolynomial.C c
    rw [Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    -- Goal: Polynomial.eval₂ (fwdHom.comp C) (fwdHom (X 0)) c = C c
    have h1 : (fwdHom (R := R) (n := n)).comp
          (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
        = (MvPolynomial.C : Polynomial R →+*
            MvPolynomial (Fin n) (Polynomial R)).comp
          (Polynomial.C : R →+* Polynomial R) := by
      apply RingHom.ext
      intro r
      show fwdHom (MvPolynomial.C r) = MvPolynomial.C (Polynomial.C r)
      unfold fwdHom
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    have h2 : fwdHom (MvPolynomial.X (0 : Fin (n+1)) : MvPolynomial (Fin (n+1)) R)
        = MvPolynomial.C (Polynomial.X : Polynomial R) := by
      unfold fwdHom
      rw [MvPolynomial.eval₂Hom_X']
      rfl
    rw [h1, h2]
    -- Goal: Polynomial.eval₂ (C.comp C) (C X) c = C c
    -- This equals Polynomial.eval₂ on (C c) via Polynomial.eval₂ properties
    -- Use Polynomial.hom_eval₂ backwards: MvPolynomial.C (eval₂ C X c) = eval₂ (C.comp C) (C X) c
    rw [← Polynomial.hom_eval₂ c Polynomial.C
          (MvPolynomial.C : Polynomial R →+*
            MvPolynomial (Fin n) (Polynomial R)) Polynomial.X,
        Polynomial.eval₂_C_X]
  · intro k
    show fwdHom (revHom (MvPolynomial.X k)) = MvPolynomial.X k
    unfold revHom
    rw [MvPolynomial.eval₂Hom_X']
    show fwdHom (MvPolynomial.X k.succ) = MvPolynomial.X k
    unfold fwdHom
    rw [MvPolynomial.eval₂Hom_X']
    rfl

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Pointwise form of `revHom_comp_fwdHom` expressed with `MvPolynomial.eval₂`. -/
private theorem reverse_forward_eval₂_eq_id (x : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial.eval₂
        (Polynomial.eval₂RingHom
          (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
          (MvPolynomial.X (0 : Fin (n+1))))
        (fun k : Fin n => MvPolynomial.X k.succ)
        (MvPolynomial.eval₂
          ((MvPolynomial.C : Polynomial R →+*
              MvPolynomial (Fin n) (Polynomial R)).comp
            (Polynomial.C : R →+* Polynomial R))
          (fun i : Fin (n+1) => Fin.cases (MvPolynomial.C Polynomial.X)
              (fun k => MvPolynomial.X k) i)
          x) = x := by
  have h := RingHom.congr_fun (revHom_comp_fwdHom (R := R) (n := n)) x
  simp only [RingHom.comp_apply, RingHom.id_apply, revHom, fwdHom,
             MvPolynomial.coe_eval₂Hom] at h
  exact h

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Pointwise form of `fwdHom_comp_revHom` expressed with `MvPolynomial.eval₂`. -/
private theorem forward_reverse_eval₂_eq_id (y : MvPolynomial (Fin n) (Polynomial R)) :
    MvPolynomial.eval₂
        ((MvPolynomial.C : Polynomial R →+*
            MvPolynomial (Fin n) (Polynomial R)).comp
          (Polynomial.C : R →+* Polynomial R))
        (fun i : Fin (n+1) => Fin.cases (MvPolynomial.C Polynomial.X)
            (fun k => MvPolynomial.X k) i)
        (MvPolynomial.eval₂
          (Polynomial.eval₂RingHom
            (MvPolynomial.C : R →+* MvPolynomial (Fin (n+1)) R)
            (MvPolynomial.X (0 : Fin (n+1))))
          (fun k : Fin n => MvPolynomial.X k.succ)
          y) = y := by
  have h := RingHom.congr_fun (fwdHom_comp_revHom (R := R) (n := n)) y
  simp only [RingHom.comp_apply, RingHom.id_apply, revHom, fwdHom,
             MvPolynomial.coe_eval₂Hom] at h
  exact h

private lemma left_inv_aux (p : AzMvPolynomial (n+1) R ord) :
    optionEquivRightSymm (optionEquivRight p) = p :=
  toMvPoly_injective (by
    rw [AzMvPolynomial.toMvPoly_optionEquivRightSymm,
        AzMvPolynomial.toMvPoly_map_optionEquivRight]
    exact reverse_forward_eval₂_eq_id p.toMvPoly)

private lemma right_inv_aux (q : AzMvPolynomial n (AzPolynomial R) ord) :
    optionEquivRight (optionEquivRightSymm q) = q :=
  map_toPoly_bridge_injective (by
    rw [AzMvPolynomial.toMvPoly_map_optionEquivRight,
        AzMvPolynomial.toMvPoly_optionEquivRightSymm]
    apply forward_reverse_eval₂_eq_id)

private lemma map_add_aux (p q : AzMvPolynomial (n+1) R ord) :
    optionEquivRight (p + q) = optionEquivRight p + optionEquivRight q :=
  map_toPoly_bridge_injective (by
    rw [toMvPoly_add, map_add,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        toMvPoly_add, MvPolynomial.eval₂_add])

private lemma map_mul_aux (p q : AzMvPolynomial (n+1) R ord) :
    optionEquivRight (p * q) = optionEquivRight p * optionEquivRight q :=
  map_toPoly_bridge_injective (by
    rw [toMvPoly_mul, map_mul,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        AzMvPolynomial.toMvPoly_map_optionEquivRight,
        toMvPoly_mul, MvPolynomial.eval₂_mul])

private lemma commutes_aux (r : R) :
    optionEquivRight ((algebraMap R (AzMvPolynomial (n+1) R ord)) r) =
      algebraMap R (AzMvPolynomial n (AzPolynomial R) ord) r :=
  map_toPoly_bridge_injective (by
    show MvPolynomial.map
          (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
          (AzMvPolynomial.optionEquivRight
            (AzMvPolynomial.C r : AzMvPolynomial (n+1) R ord)).toMvPoly
        = MvPolynomial.map
            (AzPolynomial.toPolyHom : AzPolynomial R →+* Polynomial R)
            (AzMvPolynomial.C
              (AzPolynomial.C r : AzPolynomial R)
              : AzMvPolynomial n (AzPolynomial R) ord).toMvPoly
    rw [AzMvPolynomial.toMvPoly_map_optionEquivRight, toMvPoly_C, toMvPoly_C,
        MvPolynomial.eval₂_C, RingHom.comp_apply, MvPolynomial.map_C]
    show MvPolynomial.C (Polynomial.C r) =
         MvPolynomial.C (AzPolynomial.toPolyHom (AzPolynomial.C r))
    rw [show AzPolynomial.toPolyHom (AzPolynomial.C r) = Polynomial.C r
          from toPoly_C r])

/-- `AzMvPolynomial.optionEquivRight` bundled as an `R`-algebra isomorphism. -/
noncomputable def AzMvPolynomial.optionEquivRightAlgEquiv :
    AzMvPolynomial (n+1) R ord ≃ₐ[R]
      AzMvPolynomial n (AzPolynomial R) ord where
  toFun := AzMvPolynomial.optionEquivRight
  invFun := AzMvPolynomial.optionEquivRightSymm
  left_inv := left_inv_aux
  right_inv := right_inv_aux
  map_add' := map_add_aux
  map_mul' := map_mul_aux
  commutes' := commutes_aux

end Bundled

end Azurite
