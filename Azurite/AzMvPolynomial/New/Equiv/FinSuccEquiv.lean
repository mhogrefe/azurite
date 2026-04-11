import Azurite.AzMvPolynomial.New.FinSuccEquiv
import Azurite.AzMvPolynomial.New.Equiv.Eval2
import Azurite.AzMvPolynomial.New.Equiv.Rename
import Azurite.AzPolynomial.Equiv.AlgebraOfAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzMvPolynomialNew.finSuccEquiv` ↔ `MvPolynomial.finSuccEquiv`

Bridges the Azurite `finSuccEquiv` and `finSuccEquivSymm` to Mathlib's
`MvPolynomial.finSuccEquiv`, and bundles the result as an `AlgEquiv`.
-/

namespace Azurite

open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-! ### Forward bridge -/

/-- `AzMvPolynomialNew.finSuccEquiv` corresponds to `MvPolynomial.finSuccEquiv`
    across the `toMvPoly` / `toPoly` bridges. -/
theorem AzMvPolynomialNew.toPoly_map_finSuccEquiv {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomialNew (n+1) R ord) :
    Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
        (AzPolynomial.toPoly (AzMvPolynomialNew.finSuccEquiv p))
      = MvPolynomial.finSuccEquiv R n p.toMvPoly := by
  unfold AzMvPolynomialNew.finSuccEquiv
  rw [AzMvPolynomialNew.toMvPoly_eval₂]
  rw [MvPolynomial.finSuccEquiv_apply]
  set φ : R →+* AzPolynomial (AzMvPolynomialNew n R ord) :=
    AzPolynomial.CHom.comp (AzMvPolynomialNew.CHom (n := n) (ord := ord))
  set f : Fin (n+1) → AzPolynomial (AzMvPolynomialNew n R ord) :=
    (fun i => Fin.cases AzPolynomial.X
      (fun k => AzPolynomial.C (AzMvPolynomialNew.X (ord := ord) k)) i)
  change ((Polynomial.mapRingHom
            (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))).comp
          (AzPolynomial.toPolyHom.comp (MvPolynomial.eval₂Hom φ f))) p.toMvPoly
        = _
  have key :
      ((Polynomial.mapRingHom
          (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))).comp
        (AzPolynomial.toPolyHom.comp (MvPolynomial.eval₂Hom φ f)))
        = MvPolynomial.eval₂Hom
            (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
            (fun i : Fin (n+1) =>
              Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzPolynomial.toPolyHom ((MvPolynomial.eval₂Hom φ f) (MvPolynomial.C r)))
          = (MvPolynomial.eval₂Hom
              (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
              (fun i : Fin (n+1) =>
                Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i))
              (MvPolynomial.C r)
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzPolynomial.toPoly
              (AzPolynomial.C (AzMvPolynomialNew.CHom (n := n) (ord := ord) r)))
          = Polynomial.C (MvPolynomial.C r)
      rw [AzPolynomial.toPoly_C, Polynomial.map_C]
      congr 1
      show AzMvPolynomialNew.toMvPoly
            (AzMvPolynomialNew.CHom (n := n) (ord := ord) r) = MvPolynomial.C r
      exact toMvPoly_C_new r
    · intro i
      show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzPolynomial.toPolyHom ((MvPolynomial.eval₂Hom φ f) (MvPolynomial.X i)))
          = (MvPolynomial.eval₂Hom
              (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
              (fun i : Fin (n+1) =>
                Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i))
              (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      refine Fin.cases ?_ ?_ i
      · show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (AzPolynomial.toPolyHom (AzPolynomial.X : AzPolynomial _))
            = Polynomial.X
        show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (AzPolynomial.toPoly (AzPolynomial.X : AzPolynomial _))
            = Polynomial.X
        rw [AzPolynomial.toPoly_X, Polynomial.map_X]
      · intro k
        show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (AzPolynomial.toPolyHom
                (AzPolynomial.C
                  (AzMvPolynomialNew.X (ord := ord) k : AzMvPolynomialNew n R ord)))
            = Polynomial.C (MvPolynomial.X k)
        show Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (AzPolynomial.toPoly
                (AzPolynomial.C
                  (AzMvPolynomialNew.X (ord := ord) k : AzMvPolynomialNew n R ord)))
            = Polynomial.C (MvPolynomial.X k)
        rw [AzPolynomial.toPoly_C, Polynomial.map_C]
        congr 1
        show AzMvPolynomialNew.toMvPoly
              (AzMvPolynomialNew.X (ord := ord) k : AzMvPolynomialNew n R ord)
            = MvPolynomial.X k
        exact toMvPoly_X_new k
  rw [key]

/-! ### Helpers for the reverse bridge -/

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Applying `MvPolynomial.finSuccEquiv` to a polynomial renamed via `Fin.succ`
    yields a constant polynomial. -/
private theorem finSuccEquiv_rename_succ_new (n : ℕ)
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

/-- Core list-induction lemma for the reverse bridge. -/
private theorem toMvPoly_foldr_finSuccEquivSymm_new {n : ℕ} {ord : MonomialOrder}
    (l : List (AzMvPolynomialNew n R ord)) :
    MvPolynomial.finSuccEquiv R n
      (AzMvPolynomialNew.toMvPoly
        (l.foldr
          (fun c acc =>
            AzMvPolynomialNew.renameInjective c Fin.succ (Fin.succ_injective n) +
            acc * AzMvPolynomialNew.X (ord := ord) (0 : Fin (n+1)))
          0))
      = Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
          l.toPoly := by
  induction l with
  | nil =>
    show MvPolynomial.finSuccEquiv R n
          (AzMvPolynomialNew.toMvPoly (0 : AzMvPolynomialNew (n+1) R ord)) = _
    rw [toMvPoly_zero_new, map_zero]
    show (0 : Polynomial (MvPolynomial (Fin n) R)) = Polynomial.map _ (0 : Polynomial _)
    rw [Polynomial.map_zero]
  | cons c l ih =>
    show MvPolynomial.finSuccEquiv R n
          (AzMvPolynomialNew.toMvPoly
            (AzMvPolynomialNew.renameInjective c Fin.succ (Fin.succ_injective n)
              + _ * AzMvPolynomialNew.X (ord := ord) (0 : Fin (n+1))))
        = Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            ((c :: l).toPoly)
    rw [toMvPoly_add_new, toMvPoly_mul_new, AzMvPolynomialNew.toMvPoly_renameInjective]
    rw [show AzMvPolynomialNew.toMvPoly
            (AzMvPolynomialNew.X (ord := ord) (0 : Fin (n+1))
              : AzMvPolynomialNew (n+1) R ord)
          = MvPolynomial.X (0 : Fin (n+1)) from toMvPoly_X_new _]
    rw [map_add, map_mul, ih, finSuccEquiv_rename_succ_new,
        MvPolynomial.finSuccEquiv_X_zero]
    show Polynomial.C (AzMvPolynomialNew.toMvPoly c)
          + Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (List.toPoly (c :: l))
    show Polynomial.C (AzMvPolynomialNew.toMvPoly c)
          + Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (Polynomial.C c + Polynomial.X * List.toPoly l)
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    show Polynomial.C (AzMvPolynomialNew.toMvPoly c)
          + Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.C (AzMvPolynomialNew.toMvPolyHom c)
          + Polynomial.X
            * Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
                (List.toPoly l)
    show Polynomial.C (AzMvPolynomialNew.toMvPoly c)
          + Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
              (List.toPoly l) * Polynomial.X
        = Polynomial.C (AzMvPolynomialNew.toMvPoly c)
          + Polynomial.X
            * Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
                (List.toPoly l)
    ring

/-- Reverse bridge: `toMvPoly (finSuccEquivSymm q)` matches Mathlib's
    `(MvPolynomial.finSuccEquiv R n).symm` applied to `q.toPoly`. -/
theorem AzMvPolynomialNew.toMvPoly_finSuccEquivSymm {n : ℕ} {ord : MonomialOrder}
    (q : AzPolynomial (AzMvPolynomialNew n R ord)) :
    (AzMvPolynomialNew.finSuccEquivSymm q).toMvPoly
      = (MvPolynomial.finSuccEquiv R n).symm
          (Polynomial.map
            (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzPolynomial.toPoly q)) := by
  apply (MvPolynomial.finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply]
  show MvPolynomial.finSuccEquiv R n
        (AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.finSuccEquivSymm q)) = _
  unfold AzMvPolynomialNew.finSuccEquivSymm
  rw [← Array.foldr_toList]
  show MvPolynomial.finSuccEquiv R n
        (AzMvPolynomialNew.toMvPoly
          (q.coeffs.toList.foldr
            (fun c acc =>
              AzMvPolynomialNew.renameInjective c Fin.succ (Fin.succ_injective n) +
              acc * AzMvPolynomialNew.X (ord := ord) (0 : Fin (n+1)))
            0)) = _
  rw [toMvPoly_foldr_finSuccEquivSymm_new]
  rfl

/-! ### Bundled `AlgEquiv` -/

section Bundled

variable {n : ℕ} {ord : MonomialOrder}

/-- Injectivity of the composite bridge
    `Polynomial.map toMvPolyHom ∘ AzPolynomial.toPoly`. -/
private theorem bridge_injective_new
    {q₁ q₂ : AzPolynomial (AzMvPolynomialNew n R ord)}
    (h : Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzPolynomial.toPoly q₁)
        = Polynomial.map (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzPolynomial.toPoly q₂)) :
    q₁ = q₂ := by
  apply toPoly_inj.mp
  exact Polynomial.map_injective _ toMvPoly_injective_new h

/-- `AzMvPolynomialNew.finSuccEquiv` bundled as an `R`-algebra isomorphism. -/
def AzMvPolynomialNew.finSuccAlgEquiv :
    AzMvPolynomialNew (n+1) R ord ≃ₐ[R]
      AzPolynomial (AzMvPolynomialNew n R ord) where
  toFun := AzMvPolynomialNew.finSuccEquiv
  invFun := AzMvPolynomialNew.finSuccEquivSymm
  left_inv p := toMvPoly_injective_new (by
    rw [AzMvPolynomialNew.toMvPoly_finSuccEquivSymm,
        AzMvPolynomialNew.toPoly_map_finSuccEquiv,
        AlgEquiv.symm_apply_apply])
  right_inv q := bridge_injective_new (by
    rw [AzMvPolynomialNew.toPoly_map_finSuccEquiv,
        AzMvPolynomialNew.toMvPoly_finSuccEquivSymm,
        AlgEquiv.apply_symm_apply])
  map_add' p q := bridge_injective_new (by
    rw [AzMvPolynomialNew.toPoly_map_finSuccEquiv, toMvPoly_add_new, map_add,
        AzPolynomial.toPoly_add, Polynomial.map_add,
        AzMvPolynomialNew.toPoly_map_finSuccEquiv,
        AzMvPolynomialNew.toPoly_map_finSuccEquiv])
  map_mul' p q := bridge_injective_new (by
    rw [AzMvPolynomialNew.toPoly_map_finSuccEquiv, toMvPoly_mul_new, map_mul,
        AzPolynomial.toPoly_mul, Polynomial.map_mul,
        AzMvPolynomialNew.toPoly_map_finSuccEquiv,
        AzMvPolynomialNew.toPoly_map_finSuccEquiv])
  commutes' r := bridge_injective_new (by
    show Polynomial.map
          (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
          (AzPolynomial.toPoly
            ((AzMvPolynomialNew.C r : AzMvPolynomialNew (n+1) R ord).finSuccEquiv))
        = Polynomial.map
            (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord))
            (AzPolynomial.toPoly
              (AzPolynomial.C
                (AzMvPolynomialNew.C r : AzMvPolynomialNew n R ord)))
    rw [AzMvPolynomialNew.toPoly_map_finSuccEquiv, toMvPoly_C_new,
        AzPolynomial.toPoly_C, Polynomial.map_C]
    show MvPolynomial.finSuccEquiv R n (MvPolynomial.C r)
        = Polynomial.C
            (AzMvPolynomialNew.toMvPolyHom (R := R) (n := n) (ord := ord)
              (AzMvPolynomialNew.C r))
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    show Polynomial.C (MvPolynomial.C r)
        = Polynomial.C
            (AzMvPolynomialNew.toMvPoly
              (AzMvPolynomialNew.C r : AzMvPolynomialNew n R ord))
    rw [toMvPoly_C_new])

end Bundled

end Azurite
