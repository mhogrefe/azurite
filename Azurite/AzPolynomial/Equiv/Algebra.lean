import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.Algorithm.FastPow
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Algebraic typeclass instances for AzPolynomial

Uses `Function.Injective.semiring` etc. to transfer the algebraic structure
from `Polynomial R` to `AzPolynomial R` via the injective `toPoly` map.

The `Pow` field uses computable exponentiation by squaring (`fastPow`)
rather than the noncomputable round-trip through `ofPoly`/`toPoly`.
-/

open Polynomial

namespace Azurite.AzPolynomial

private noncomputable def nsmulAz {R : Type _} [Semiring R] [DecidableEq R]
    (n : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  AzPolynomial.ofPoly (n • AzPolynomial.toPoly p)

/-- Computable exponentiation for AzPolynomial via binary exponentiation. -/
private def npowAz {R : Type _} [Semiring R] [DecidableEq R]
    (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  Azurite.fastPow p n

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

-- Direct induction proof: toPoly preserves fastPowAux
private theorem toPoly_fastPowAux {R : Type _} [Semiring R] [DecidableEq R]
    (acc base : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (Azurite.fastPowAux acc base n) =
    AzPolynomial.toPoly acc * AzPolynomial.toPoly base ^ n := by
  induction n using Nat.strongRecOn generalizing acc base with
  | _ n ih =>
    unfold Azurite.fastPowAux
    split
    · rename_i h; subst h; simp [pow_zero, mul_one]
    · rename_i h
      split
      · rename_i heven
        rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        simp only [toPoly_mul]
        rw [show AzPolynomial.toPoly base * AzPolynomial.toPoly base =
            AzPolynomial.toPoly base ^ 2 from (sq _).symm, ← pow_mul]
        congr 2; omega
      · rename_i hodd
        rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        simp only [toPoly_mul]
        rw [mul_assoc]; congr 1
        rw [show AzPolynomial.toPoly base * AzPolynomial.toPoly base =
            AzPolynomial.toPoly base ^ 2 from (sq _).symm, ← pow_mul, ← pow_succ']
        congr 1; omega

private theorem toPoly_npowAz {R : Type _} [Semiring R] [DecidableEq R]
    (p : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (npowAz p n) = AzPolynomial.toPoly p ^ n := by
  simp [npowAz, Azurite.fastPow, toPoly_fastPowAux, toPoly_one, one_mul]

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

/-! ### Ring homomorphism -/

/-- The canonical ring homomorphism from `AzPolynomial R` to `Polynomial R`. -/
noncomputable def toPolyHom {R : Type _} [CommRing R] [DecidableEq R] :
    AzPolynomial R →+* Polynomial R where
  toFun := AzPolynomial.toPoly
  map_zero' := toPoly_zero
  map_one' := toPoly_one
  map_add' := toPoly_add
  map_mul' := toPoly_mul

/-! ### Integral domain -/

/-- `AzPolynomial R` is an integral domain when `R` is. -/
noncomputable instance {R : Type _} [CommRing R] [IsDomain R] [DecidableEq R] :
    IsDomain (AzPolynomial R) :=
  Function.Injective.isDomain toPolyHom (fun _ _ h => toPoly_inj.mp h)

end Azurite.AzPolynomial
