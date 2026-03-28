/-
  Algebraic typeclass instances for AzMvPolynomial.

  Uses `Function.Injective.commSemiring` and `.commRing` to transfer the
  algebraic structure from `MvPolynomial σ R` to `AzMvPolynomial σ R ord`
  via the injective `toMvPoly` map.

  The `npow` field uses the computable `AzMvPolynomial.pow`, which includes
  a single-monomial optimization and binary exponentiation fallback.
-/
import Azurite.AzMvPolynomial.Equiv.Add
import Azurite.AzMvPolynomial.Equiv.Mul
import Azurite.AzMvPolynomial.Equiv.Neg
import Azurite.AzMvPolynomial.Equiv.Sub
import Azurite.AzMvPolynomial.Equiv.Pow
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Hom.InjSurj

namespace Azurite
open AzMvPolynomial

/-! ### CommSemiring -/

section CommSemiringSection

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

private noncomputable def nsmulAzS
    (n : ℕ) (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n • AzMvPolynomial.toMvPoly p)

private noncomputable def natCastAzS
    (n : ℕ) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n : MvPolynomial σ R)

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_nsmulAzS (n : ℕ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.toMvPoly (nsmulAzS n p) = n • AzMvPolynomial.toMvPoly p := by
  unfold nsmulAzS; exact toMvPoly_ofMvPoly _

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_natCastAzS (n : ℕ) :
    AzMvPolynomial.toMvPoly (natCastAzS n : AzMvPolynomial σ R ord) =
    (n : MvPolynomial σ R) := by
  unfold natCastAzS; exact toMvPoly_ofMvPoly _

/-- `AzMvPolynomial σ R ord` forms a commutative semiring when `R` is a
    commutative semiring with no zero divisors. The `npow` field uses the
    computable `AzMvPolynomial.pow`. -/
noncomputable instance : CommSemiring (AzMvPolynomial σ R ord) :=
  letI : SMul ℕ (AzMvPolynomial σ R ord) := ⟨nsmulAzS⟩
  letI : Pow (AzMvPolynomial σ R ord) ℕ := ⟨fun p n => p.pow n⟩
  letI : NatCast (AzMvPolynomial σ R ord) := ⟨natCastAzS⟩
  Function.Injective.commSemiring AzMvPolynomial.toMvPoly
    (fun _ _ h => toMvPoly_injective h)
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    toMvPoly_nsmulAzS toMvPoly_pow toMvPoly_natCastAzS

end CommSemiringSection

/-! ### CommRing -/

section CommRingSection

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

private noncomputable def nsmulAzR
    (n : ℕ) (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n • AzMvPolynomial.toMvPoly p)

private noncomputable def natCastAzR
    (n : ℕ) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n : MvPolynomial σ R)

private noncomputable def zsmulAzR
    (n : ℤ) (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n • AzMvPolynomial.toMvPoly p)

private noncomputable def intCastAzR
    (n : ℤ) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.ofMvPoly (n : MvPolynomial σ R)

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_nsmulAzR (n : ℕ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.toMvPoly (nsmulAzR n p) = n • AzMvPolynomial.toMvPoly p := by
  unfold nsmulAzR; exact toMvPoly_ofMvPoly _

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_natCastAzR (n : ℕ) :
    AzMvPolynomial.toMvPoly (natCastAzR n : AzMvPolynomial σ R ord) =
    (n : MvPolynomial σ R) := by
  unfold natCastAzR; exact toMvPoly_ofMvPoly _

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_zsmulAzR (n : ℤ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.toMvPoly (zsmulAzR n p) = n • AzMvPolynomial.toMvPoly p := by
  unfold zsmulAzR; exact toMvPoly_ofMvPoly _

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_intCastAzR (n : ℤ) :
    AzMvPolynomial.toMvPoly (intCastAzR n : AzMvPolynomial σ R ord) =
    (n : MvPolynomial σ R) := by
  unfold intCastAzR; exact toMvPoly_ofMvPoly _

/-- `AzMvPolynomial σ R ord` forms a commutative ring when `R` is a
    commutative ring with no zero divisors. The `npow` field uses the
    computable `AzMvPolynomial.pow`. -/
noncomputable instance : CommRing (AzMvPolynomial σ R ord) :=
  letI : SMul ℕ (AzMvPolynomial σ R ord) := ⟨nsmulAzR⟩
  letI : SMul ℤ (AzMvPolynomial σ R ord) := ⟨zsmulAzR⟩
  letI : Pow (AzMvPolynomial σ R ord) ℕ := ⟨fun p n => p.pow n⟩
  letI : NatCast (AzMvPolynomial σ R ord) := ⟨natCastAzR⟩
  letI : IntCast (AzMvPolynomial σ R ord) := ⟨intCastAzR⟩
  Function.Injective.commRing AzMvPolynomial.toMvPoly
    (fun _ _ h => toMvPoly_injective h)
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    toMvPoly_nsmulAzR toMvPoly_zsmulAzR toMvPoly_pow toMvPoly_natCastAzR toMvPoly_intCastAzR

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzMvPolynomial σ R ord` and Mathlib's `MvPolynomial σ R`. -/
noncomputable def ringEquivMvPolynomial :
    AzMvPolynomial σ R ord ≃+* MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  invFun := AzMvPolynomial.ofMvPoly
  left_inv := ofMvPoly_toMvPoly
  right_inv := toMvPoly_ofMvPoly
  map_mul' := toMvPoly_mul
  map_add' := toMvPoly_add

/-! ### Ring homomorphism -/

/-- The canonical ring homomorphism from `AzMvPolynomial σ R ord` to `MvPolynomial σ R`. -/
noncomputable def toMvPolyHom :
    AzMvPolynomial σ R ord →+* MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  map_zero' := toMvPoly_zero
  map_one' := toMvPoly_one
  map_add' := toMvPoly_add
  map_mul' := toMvPoly_mul

/-! ### Integral domain -/

/-- `AzMvPolynomial σ R ord` is an integral domain when `R` is. -/
noncomputable instance [IsDomain R] :
    IsDomain (AzMvPolynomial σ R ord) :=
  Function.Injective.isDomain toMvPolyHom (fun _ _ h => toMvPoly_injective h)

end CommRingSection

end Azurite
