/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace Azurite

structure AzNat where
  limbs : Array UInt64
  last_ne_zero : limbs.back? ≠ some 0
  deriving DecidableEq

instance : OfNat AzNat 0 := ⟨⟨#[], by simp⟩⟩
instance : OfNat AzNat 1 := ⟨⟨#[1], by decide⟩⟩

instance : Zero AzNat := ⟨0⟩
instance : One AzNat := ⟨1⟩

instance : Inhabited AzNat := ⟨0⟩

def AzNat.beqUInt64 (a : AzNat) (u : UInt64) : Bool :=
  match a.limbs.size with
  | 0 => u == 0
  | 1 => a.limbs.back? == some u
  | _ => false

def AzNat.beqInt64 (a : AzNat) (i : Int64) : Bool :=
  (i ≥ 0) && a.beqUInt64 i.toUInt64

def AzNat.compareUInt64 (a : AzNat) (u : UInt64) : Ordering :=
  match h : a.limbs.size with
  | 0 => if u == 0 then .eq else .lt
  | 1 => Ord.compare a.limbs[0] u
  | _ + 2 => .gt

def AzNat.compareInt64 (a : AzNat) (i : Int64) : Ordering :=
  if i < 0 then .gt else a.compareUInt64 i.toUInt64

end Azurite
