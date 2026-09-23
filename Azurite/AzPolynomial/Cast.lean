/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzRat.Instances
import Azurite.AzRat.Conversion
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Azurite.AzZMod.CastHom

namespace Azurite
namespace AzPolynomial

/-- Lifts a `AzPolynomial AzNat` to `AzPolynomial AzInt`. -/
def mapAzNatToAzInt (p : AzPolynomial AzNat) : AzPolynomial AzInt :=
  mapZeroInjective AzNat.toAzInt
    (fun n => ⟨fun h => congrArg AzInt.abs h, fun h => by subst h; rfl⟩) p

/-- Lifts a `AzPolynomial AzInt` to `AzPolynomial AzRat`. -/
def mapAzIntToAzRat (p : AzPolynomial AzInt) : AzPolynomial AzRat :=
  mapZeroInjective AzInt.toAzRat
    (fun z => ⟨fun h => by
        have hz := congrArg AzRat.toRat h
        rw [AzRat.toRat_toAzRat_int, AzRat.toRat_zero] at hz
        have hz0 : z.toInt = 0 := by exact_mod_cast hz
        rw [← AzInt.ofInt_toInt z, hz0, AzInt.ofInt_zero],
      fun h => by subst h; exact AzRat.toRat_injective (by
        rw [AzRat.toRat_toAzRat_int, AzInt.toInt_zero, AzRat.toRat_zero, Int.cast_zero])⟩) p

/-- Maps a `AzPolynomial (AzZMod m)` to `AzPolynomial AzNat` (the residue values). -/
def mapAzZModToAzNat {m : AzNat} [NeZero m.toNat] (p : AzPolynomial (AzZMod m)) :
    AzPolynomial AzNat :=
  mapZeroInjective AzZMod.val
    (fun r => ⟨fun h => AzZMod.ext (h.trans AzZMod.val_zero.symm),
               fun h => by rw [h, AzZMod.val_zero]⟩) p

/-- Maps a `AzPolynomial AzNat` to `AzPolynomial (AzZMod m)` (reduces; normalizes). -/
def mapAzNatToAzZMod {m : AzNat} [NeZero m.toNat] (p : AzPolynomial AzNat) :
    AzPolynomial (AzZMod m) :=
  map AzZMod.ofAzNatRingHom p

/-- Maps a `AzPolynomial AzInt` to `AzPolynomial (AzZMod m)` (reduces; normalizes). -/
def mapAzIntToAzZMod {m : AzNat} [NeZero m.toNat] (p : AzPolynomial AzInt) :
    AzPolynomial (AzZMod m) :=
  map AzZMod.ofAzIntRingHom p

end AzPolynomial
end Azurite
