import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzPolynomial.Equiv.Sub
import Mathlib.Algebra.Ring.InjSurj

/-!
# Algebraic typeclass instances for AzPolynomial

Uses `Function.Injective.semiring` etc. to transfer the algebraic structure
from `Polynomial R` to `AzPolynomial R` via the injective `toPoly` map.
-/

open Polynomial

namespace Azurite.AzPolynomial

private noncomputable def nsmulAz {R : Type _} [Semiring R] [DecidableEq R]
    (n : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  AzPolynomial.ofPoly (n • AzPolynomial.toPoly p)

private noncomputable def npowAz {R : Type _} [Semiring R] [DecidableEq R]
    (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  AzPolynomial.ofPoly (AzPolynomial.toPoly p ^ n)

private noncomputable def natCastAz {R : Type _} [Semiring R] [DecidableEq R]
    (n : ℕ) : AzPolynomial R :=
  AzPolynomial.ofPoly (n : Polynomial R)

private noncomputable def zsmulAz {R : Type _} [Ring R] [DecidableEq R]
    (n : ℤ) (p : AzPolynomial R) : AzPolynomial R :=
  AzPolynomial.ofPoly (n • AzPolynomial.toPoly p)

private noncomputable def intCastAz {R : Type _} [Ring R] [DecidableEq R]
    (n : ℤ) : AzPolynomial R :=
  AzPolynomial.ofPoly (n : Polynomial R)

private theorem toPoly_nsmulAz {R : Type _} [Semiring R] [DecidableEq R]
    (n : ℕ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (nsmulAz n p) = n • AzPolynomial.toPoly p := by
  unfold nsmulAz; exact toPoly_ofPoly _

private theorem toPoly_npowAz {R : Type _} [Semiring R] [DecidableEq R]
    (p : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (npowAz p n) = AzPolynomial.toPoly p ^ n := by
  unfold npowAz; exact toPoly_ofPoly _

private theorem toPoly_natCastAz {R : Type _} [Semiring R] [DecidableEq R]
    (n : ℕ) : AzPolynomial.toPoly (natCastAz n : AzPolynomial R) = (n : Polynomial R) := by
  unfold natCastAz; exact toPoly_ofPoly _

private theorem toPoly_zsmulAz {R : Type _} [Ring R] [DecidableEq R]
    (n : ℤ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (zsmulAz n p) = n • AzPolynomial.toPoly p := by
  unfold zsmulAz; exact toPoly_ofPoly _

private theorem toPoly_intCastAz {R : Type _} [Ring R] [DecidableEq R]
    (n : ℤ) : AzPolynomial.toPoly (intCastAz n : AzPolynomial R) = (n : Polynomial R) := by
  unfold intCastAz; exact toPoly_ofPoly _

/-! ### Semiring -/

noncomputable instance {R : Type _} [Semiring R] [DecidableEq R] :
    Semiring (AzPolynomial R) :=
  letI : SMul ℕ (AzPolynomial R) := ⟨nsmulAz⟩
  letI : Pow (AzPolynomial R) ℕ := ⟨npowAz⟩
  letI : NatCast (AzPolynomial R) := ⟨natCastAz⟩
  Function.Injective.semiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul
    toPoly_nsmulAz toPoly_npowAz toPoly_natCastAz

/-! ### CommSemiring -/

noncomputable instance {R : Type _} [CommSemiring R] [DecidableEq R] :
    CommSemiring (AzPolynomial R) :=
  letI : SMul ℕ (AzPolynomial R) := ⟨nsmulAz⟩
  letI : Pow (AzPolynomial R) ℕ := ⟨npowAz⟩
  letI : NatCast (AzPolynomial R) := ⟨natCastAz⟩
  Function.Injective.commSemiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul
    toPoly_nsmulAz toPoly_npowAz toPoly_natCastAz

/-! ### Ring -/

noncomputable instance {R : Type _} [Ring R] [DecidableEq R] :
    Ring (AzPolynomial R) :=
  letI : SMul ℕ (AzPolynomial R) := ⟨nsmulAz⟩
  letI : SMul ℤ (AzPolynomial R) := ⟨zsmulAz⟩
  letI : Pow (AzPolynomial R) ℕ := ⟨npowAz⟩
  letI : NatCast (AzPolynomial R) := ⟨natCastAz⟩
  letI : IntCast (AzPolynomial R) := ⟨intCastAz⟩
  Function.Injective.ring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg toPoly_sub
    toPoly_nsmulAz toPoly_zsmulAz toPoly_npowAz toPoly_natCastAz toPoly_intCastAz

/-! ### CommRing -/

noncomputable instance {R : Type _} [CommRing R] [DecidableEq R] :
    CommRing (AzPolynomial R) :=
  letI : SMul ℕ (AzPolynomial R) := ⟨nsmulAz⟩
  letI : SMul ℤ (AzPolynomial R) := ⟨zsmulAz⟩
  letI : Pow (AzPolynomial R) ℕ := ⟨npowAz⟩
  letI : NatCast (AzPolynomial R) := ⟨natCastAz⟩
  letI : IntCast (AzPolynomial R) := ⟨intCastAz⟩
  Function.Injective.commRing AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg toPoly_sub
    toPoly_nsmulAz toPoly_zsmulAz toPoly_npowAz toPoly_natCastAz toPoly_intCastAz

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzPolynomial R` and Mathlib's `Polynomial R`. -/
noncomputable def ringEquivPolynomial {R : Type _} [Semiring R] [DecidableEq R] :
    AzPolynomial R ≃+* Polynomial R :=
  { equivPolynomial with
    map_mul' := toPoly_mul
    map_add' := toPoly_add }

end Azurite.AzPolynomial
