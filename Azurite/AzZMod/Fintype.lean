/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `AzZMod m` is a finite type with `m.toNat` elements.

  The residues are canonical (`val` reduced, with its proof carried in the
  structure), so `AzZMod m` is equivalent to `Fin m.toNat` by reading the
  value off — a computable `Equiv`, no modular arithmetic involved.  The
  resulting `Fintype` instance and the cardinality `card_eq` are what let
  the finite-field theorems (e.g. the correctness of distinct-degree
  factorization, GG Theorem 14.4, stated over `[Fintype K]` with
  `q = Fintype.card K`) be instantiated at concrete `AzZMod p` moduli.

  No `NeZero` hypothesis: at `m.toNat = 0` the type is empty and the count
  is `0`, consistently.
-/
import Azurite.AzZMod.Basic
import Mathlib.Data.Fintype.Card

namespace Azurite

namespace AzZMod

variable {m : AzNat}

/-- `AzZMod m` is equivalent to `Fin m.toNat`: the canonical residue and its
canonicity proof are exactly the data of a `Fin`. -/
def finEquiv (m : AzNat) : AzZMod m ≃ Fin m.toNat where
  toFun a := ⟨a.val.toNat, a.isLt⟩
  invFun i := ⟨AzNat.ofNat i.val, by rw [AzNat.toNat_ofNat]; exact i.isLt⟩
  left_inv a := by
    apply ext
    exact AzNat.ofNat_toNat a.val
  right_inv i := by
    apply Fin.ext
    exact AzNat.toNat_ofNat i.val

instance instFintype : Fintype (AzZMod m) :=
  Fintype.ofEquiv (Fin m.toNat) (finEquiv m).symm

/-- `AzZMod m` has `m.toNat` elements. -/
@[simp] theorem card_eq (m : AzNat) : Fintype.card (AzZMod m) = m.toNat := by
  rw [Fintype.card_congr (finEquiv m), Fintype.card_fin]

end AzZMod

end Azurite
