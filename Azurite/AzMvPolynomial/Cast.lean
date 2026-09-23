/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Coefficient-type casts for `AzMvPolynomial`, between the Az coefficient types.
-/
import Azurite.AzMvPolynomial.Map
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzRat.Instances
import Azurite.AzRat.Conversion
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Azurite.AzZMod.CastHom

namespace Azurite

variable {n : ℕ} {ord : MonomialOrder}

/-- Lifts an `AzMvPolynomial n AzNat` to `AzMvPolynomial n AzInt`. -/
def AzMvPolynomial.mapAzNatToAzInt (p : AzMvPolynomial n AzNat ord) :
    AzMvPolynomial n AzInt ord :=
  AzMvPolynomial.mapZeroInjective AzNat.toAzInt
    (fun a => ⟨fun h => congrArg AzInt.abs h, fun h => by subst h; rfl⟩) p

/-- Lifts an `AzMvPolynomial n AzInt` to `AzMvPolynomial n AzRat`. -/
def AzMvPolynomial.mapAzIntToAzRat (p : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n AzRat ord :=
  AzMvPolynomial.mapZeroInjective AzInt.toAzRat
    (fun z => ⟨fun h => by
        have hz := congrArg AzRat.toRat h
        rw [AzRat.toRat_toAzRat_int, AzRat.toRat_zero] at hz
        have hz0 : z.toInt = 0 := by exact_mod_cast hz
        rw [← AzInt.ofInt_toInt z, hz0, AzInt.ofInt_zero],
      fun h => by subst h; exact AzRat.toRat_injective (by
        rw [AzRat.toRat_toAzRat_int, AzInt.toInt_zero, AzRat.toRat_zero, Int.cast_zero])⟩) p

/-- Maps an `AzMvPolynomial n (AzZMod m)` to `AzMvPolynomial n AzNat`. -/
def AzMvPolynomial.mapAzZModToAzNat {m : AzNat} [NeZero m.toNat]
    (p : AzMvPolynomial n (AzZMod m) ord) :
    AzMvPolynomial n AzNat ord :=
  AzMvPolynomial.mapZeroInjective AzZMod.val
    (fun r => ⟨fun h => AzZMod.ext (h.trans AzZMod.val_zero.symm),
               fun h => by rw [h, AzZMod.val_zero]⟩) p

/-- Maps an `AzMvPolynomial n AzNat` to `AzMvPolynomial n (AzZMod m)`. -/
def AzMvPolynomial.mapAzNatToAzZMod {m : AzNat} [NeZero m.toNat]
    (p : AzMvPolynomial n AzNat ord) :
    AzMvPolynomial n (AzZMod m) ord :=
  AzMvPolynomial.map AzZMod.ofAzNatRingHom p

/-- Maps an `AzMvPolynomial n AzInt` to `AzMvPolynomial n (AzZMod m)`. -/
def AzMvPolynomial.mapAzIntToAzZMod {m : AzNat} [NeZero m.toNat]
    (p : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial n (AzZMod m) ord :=
  AzMvPolynomial.map AzZMod.ofAzIntRingHom p

end Azurite
