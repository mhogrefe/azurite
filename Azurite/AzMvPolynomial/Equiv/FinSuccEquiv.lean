import Azurite.AzMvPolynomial.FinSuccEquiv
import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Rename
import Azurite.AzPolynomial.Equiv.AlgebraOfAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzMvPolynomial.finSuccEquiv` ↔ `MvPolynomial.finSuccEquiv`

Bridges the Azurite `finSuccEquiv` and `finSuccEquivSymm` to Mathlib's
`MvPolynomial.finSuccEquiv`, and bundles the result as an `AlgEquiv`.

The forward direction is verified via `MvPolynomial.ringHom_ext`: both
sides, after crossing the `toMvPolyHom` / `toPolyHom` bridges, are ring
homomorphisms `MvPolynomial (Fin (n+1)) R →+* Polynomial (MvPolynomial (Fin n) R)`
that agree on constants and on each variable.

The reverse direction is verified by list induction on the coefficient
array, then passing through `(MvPolynomial.finSuccEquiv R n).injective`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward bridge -/

/-- `AzMvPolynomial.finSuccEquiv` corresponds to `MvPolynomial.finSuccEquiv`
    across the `toMvPoly` / `toPoly` bridges: mapping the coefficient ring of
    the resulting univariate polynomial by `toMvPoly` gives exactly Mathlib's
    `finSuccEquiv` applied to `toMvPoly p`. -/
theorem AzMvPolynomial.toPoly_map_finSuccEquiv {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin (n+1)) R ord) :
    Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
        (AzPolynomial.toPoly (AzMvPolynomial.finSuccEquiv p))
      = MvPolynomial.finSuccEquiv R n p.toMvPoly := by
  unfold AzMvPolynomial.finSuccEquiv
  rw [AzMvPolynomial.toMvPoly_eval₂]
  rw [MvPolynomial.finSuccEquiv_apply]
  -- Reframe LHS as `((mapRingHom toMvPolyHom).comp (toPolyHom.comp (eval₂Hom φ f))) p.toMvPoly`
  -- and then show the ring hom equals `eval₂Hom (C.comp C) ...` via `ringHom_ext`.
  set φ : R →+* AzPolynomial (AzMvPolynomial (Fin n) R ord) :=
    AzPolynomial.CHom.comp (AzMvPolynomial.CHom (σ := Fin n) (ord := ord))
  set f : Fin (n+1) → AzPolynomial (AzMvPolynomial (Fin n) R ord) :=
    (fun i => Fin.cases AzPolynomial.X
      (fun k => AzPolynomial.C (AzMvPolynomial.X (ord := ord) k)) i)
  change ((Polynomial.mapRingHom
            (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))).comp
          (AzPolynomial.toPolyHom.comp (MvPolynomial.eval₂Hom φ f))) p.toMvPoly
        = _
  have key :
      ((Polynomial.mapRingHom
          (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))).comp
        (AzPolynomial.toPolyHom.comp (MvPolynomial.eval₂Hom φ f)))
        = MvPolynomial.eval₂Hom
            (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
            (fun i : Fin (n+1) =>
              Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (AzPolynomial.toPolyHom ((MvPolynomial.eval₂Hom φ f) (MvPolynomial.C r)))
          = (MvPolynomial.eval₂Hom
              (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
              (fun i : Fin (n+1) =>
                Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i))
              (MvPolynomial.C r)
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (AzPolynomial.toPoly
              (AzPolynomial.C (AzMvPolynomial.CHom (σ := Fin n) (ord := ord) r)))
          = Polynomial.C (MvPolynomial.C r)
      rw [AzPolynomial.toPoly_C, Polynomial.map_C]
      congr 1
      show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.CHom (σ := Fin n) (ord := ord) r) = MvPolynomial.C r
      exact toMvPoly_C r
    · intro i
      show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (AzPolynomial.toPolyHom ((MvPolynomial.eval₂Hom φ f) (MvPolynomial.X i)))
          = (MvPolynomial.eval₂Hom
              (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
              (fun i : Fin (n+1) =>
                Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i))
              (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      refine Fin.cases ?_ ?_ i
      · -- i = 0
        show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (AzPolynomial.toPolyHom (AzPolynomial.X : AzPolynomial _))
            = Polynomial.X
        show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (AzPolynomial.toPoly (AzPolynomial.X : AzPolynomial _))
            = Polynomial.X
        rw [AzPolynomial.toPoly_X, Polynomial.map_X]
      · intro k
        -- i = k.succ
        show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (AzPolynomial.toPolyHom
                (AzPolynomial.C
                  (AzMvPolynomial.X (ord := ord) k : AzMvPolynomial (Fin n) R ord)))
            = Polynomial.C (MvPolynomial.X k)
        show Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (AzPolynomial.toPoly
                (AzPolynomial.C
                  (AzMvPolynomial.X (ord := ord) k : AzMvPolynomial (Fin n) R ord)))
            = Polynomial.C (MvPolynomial.X k)
        rw [AzPolynomial.toPoly_C, Polynomial.map_C]
        congr 1
        show AzMvPolynomial.toMvPoly
              (AzMvPolynomial.X (ord := ord) k : AzMvPolynomial (Fin n) R ord)
            = MvPolynomial.X k
        exact toMvPoly_X k
  rw [key]

/-! ### Helpers for the reverse bridge -/

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Applying `MvPolynomial.finSuccEquiv` to a polynomial renamed via `Fin.succ`
    yields a constant polynomial. -/
private theorem finSuccEquiv_rename_succ (n : ℕ)
    (a : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n ((MvPolynomial.rename Fin.succ) a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.rename_C]
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    rfl
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← Polynomial.C_add]
  | mul_X p k ih =>
    rw [map_mul, map_mul, ih, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ,
        ← Polynomial.C_mul]

/-! ### Reverse bridge -/

/-- Core list-induction lemma for the reverse bridge: for any list of
    multivariate polynomials in `Fin n`, applying `finSuccEquivSymm`'s
    Horner fold and then `toMvPoly` matches Mathlib's `finSuccEquiv` applied
    to the list viewed as a univariate polynomial. -/
private theorem toMvPoly_foldr_finSuccEquivSymm {n : ℕ} {ord : MonomialOrder}
    (l : List (AzMvPolynomial (Fin n) R ord)) :
    MvPolynomial.finSuccEquiv R n
      (AzMvPolynomial.toMvPoly
        (l.foldr
          (fun c acc =>
            AzMvPolynomial.renameInjective c Fin.succ (Fin.succ_injective n) +
            acc * AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))
          0))
      = Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
          l.toPoly := by
  induction l with
  | nil =>
    show MvPolynomial.finSuccEquiv R n
          (AzMvPolynomial.toMvPoly (0 : AzMvPolynomial (Fin (n+1)) R ord)) = _
    rw [toMvPoly_zero, map_zero]
    show (0 : Polynomial (MvPolynomial (Fin n) R)) = Polynomial.map _ (0 : Polynomial _)
    rw [Polynomial.map_zero]
  | cons c l ih =>
    show MvPolynomial.finSuccEquiv R n
          (AzMvPolynomial.toMvPoly
            (AzMvPolynomial.renameInjective c Fin.succ (Fin.succ_injective n)
              + _ * AzMvPolynomial.X (ord := ord) (0 : Fin (n+1))))
        = Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            ((c :: l).toPoly)
    rw [toMvPoly_add, toMvPoly_mul, AzMvPolynomial.toMvPoly_renameInjective]
    rw [show AzMvPolynomial.toMvPoly
            (AzMvPolynomial.X (ord := ord) (0 : Fin (n+1))
              : AzMvPolynomial (Fin (n+1)) R ord)
          = MvPolynomial.X (0 : Fin (n+1)) from toMvPoly_X _]
    rw [map_add, map_mul, ih, finSuccEquiv_rename_succ,
        MvPolynomial.finSuccEquiv_X_zero]
    show Polynomial.C (AzMvPolynomial.toMvPoly c)
          + Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (List.toPoly (c :: l))
    show Polynomial.C (AzMvPolynomial.toMvPoly c)
          + Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (Polynomial.C c + Polynomial.X * List.toPoly l)
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    show Polynomial.C (AzMvPolynomial.toMvPoly c)
          + Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.C (AzMvPolynomial.toMvPolyHom c)
          + Polynomial.X
            * Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
                (List.toPoly l)
    show Polynomial.C (AzMvPolynomial.toMvPoly c)
          + Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.C (AzMvPolynomial.toMvPoly c)
          + Polynomial.X
            * Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
                (List.toPoly l)
    ring

/-- Reverse bridge: `toMvPoly (finSuccEquivSymm q)` matches Mathlib's
    `(MvPolynomial.finSuccEquiv R n).symm` applied to `q.toPoly` (after
    mapping the coefficient ring via `toMvPolyHom`). -/
theorem AzMvPolynomial.toMvPoly_finSuccEquivSymm {n : ℕ} {ord : MonomialOrder}
    (q : AzPolynomial (AzMvPolynomial (Fin n) R ord)) :
    (AzMvPolynomial.finSuccEquivSymm q).toMvPoly
      = (MvPolynomial.finSuccEquiv R n).symm
          (Polynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (AzPolynomial.toPoly q)) := by
  apply (MvPolynomial.finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply]
  show MvPolynomial.finSuccEquiv R n
        (AzMvPolynomial.toMvPoly (AzMvPolynomial.finSuccEquivSymm q)) = _
  unfold AzMvPolynomial.finSuccEquivSymm
  rw [← Array.foldr_toList]
  show MvPolynomial.finSuccEquiv R n
        (AzMvPolynomial.toMvPoly
          (q.coeffs.toList.foldr
            (fun c acc =>
              AzMvPolynomial.renameInjective c Fin.succ (Fin.succ_injective n) +
              acc * AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))
            0)) = _
  rw [toMvPoly_foldr_finSuccEquivSymm]
  rfl

/-! ### Bundled `AlgEquiv` -/

section Bundled

variable {n : ℕ} {ord : MonomialOrder}

/-- Injectivity of the composite bridge
    `Polynomial.map toMvPolyHom ∘ AzPolynomial.toPoly`, used to transfer
    ring-hom properties back from Mathlib's `finSuccEquiv`. -/
private theorem bridge_injective
    {q₁ q₂ : AzPolynomial (AzMvPolynomial (Fin n) R ord)}
    (h : Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
          (AzPolynomial.toPoly q₁)
        = Polynomial.map (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
          (AzPolynomial.toPoly q₂)) :
    q₁ = q₂ := by
  apply toPoly_inj.mp
  exact Polynomial.map_injective _ toMvPoly_injective h

/-- `AzMvPolynomial.finSuccEquiv` bundled as an `R`-algebra isomorphism,
    matching `MvPolynomial.finSuccEquiv` from Mathlib. The forward map and its
    inverse are both the computable Azurite functions `finSuccEquiv` and
    `finSuccEquivSymm`; the ring-hom laws are discharged by transferring them
    from Mathlib's equivalence across the `toMvPoly` / `toPoly` bridges. -/
def AzMvPolynomial.finSuccAlgEquiv :
    AzMvPolynomial (Fin (n+1)) R ord ≃ₐ[R]
      AzPolynomial (AzMvPolynomial (Fin n) R ord) where
  toFun := AzMvPolynomial.finSuccEquiv
  invFun := AzMvPolynomial.finSuccEquivSymm
  left_inv p := toMvPoly_injective (by
    rw [AzMvPolynomial.toMvPoly_finSuccEquivSymm,
        AzMvPolynomial.toPoly_map_finSuccEquiv,
        AlgEquiv.symm_apply_apply])
  right_inv q := bridge_injective (by
    rw [AzMvPolynomial.toPoly_map_finSuccEquiv,
        AzMvPolynomial.toMvPoly_finSuccEquivSymm,
        AlgEquiv.apply_symm_apply])
  map_add' p q := bridge_injective (by
    rw [AzMvPolynomial.toPoly_map_finSuccEquiv, toMvPoly_add, map_add,
        AzPolynomial.toPoly_add, Polynomial.map_add,
        AzMvPolynomial.toPoly_map_finSuccEquiv,
        AzMvPolynomial.toPoly_map_finSuccEquiv])
  map_mul' p q := bridge_injective (by
    rw [AzMvPolynomial.toPoly_map_finSuccEquiv, toMvPoly_mul, map_mul,
        AzPolynomial.toPoly_mul, Polynomial.map_mul,
        AzMvPolynomial.toPoly_map_finSuccEquiv,
        AzMvPolynomial.toPoly_map_finSuccEquiv])
  commutes' r := bridge_injective (by
    show Polynomial.map
          (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
          (AzPolynomial.toPoly
            ((AzMvPolynomial.C r : AzMvPolynomial (Fin (n+1)) R ord).finSuccEquiv))
        = Polynomial.map
            (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord))
            (AzPolynomial.toPoly
              (AzPolynomial.C
                (AzMvPolynomial.C r : AzMvPolynomial (Fin n) R ord)))
    rw [AzMvPolynomial.toPoly_map_finSuccEquiv, toMvPoly_C,
        AzPolynomial.toPoly_C, Polynomial.map_C]
    show MvPolynomial.finSuccEquiv R n (MvPolynomial.C r)
        = Polynomial.C
            (AzMvPolynomial.toMvPolyHom (R := R) (σ := Fin n) (ord := ord)
              (AzMvPolynomial.C r))
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    show Polynomial.C (MvPolynomial.C r)
        = Polynomial.C
            (AzMvPolynomial.toMvPoly
              (AzMvPolynomial.C r : AzMvPolynomial (Fin n) R ord))
    rw [toMvPoly_C])

end Bundled

end Azurite
