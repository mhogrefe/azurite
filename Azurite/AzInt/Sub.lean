import Azurite.AzInt.Add

namespace Azurite.AzInt

/-- Subtract a `UInt64` `u` from an `AzInt` `z`. -/
def subUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  if z.sign then
    match z.abs.compareUInt64 u with
    | .lt => mkNorm false (u.toAzNat - z.abs)
    | .eq => 0
    | .gt => mkNorm true (z.abs.subUInt64 u)
  else
    mkNorm false (z.abs.addUInt64 u)

/-- Add an `Int64` `i` to an `AzInt` `z`. -/
def addInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then z.addUInt64 i.toUInt64 else z.subUInt64 (-i).toUInt64

/-- Subtract an `Int64` `i` from an `AzInt` `z`. -/
def subInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then z.subUInt64 i.toUInt64 else z.addUInt64 (-i).toUInt64

/-- Subtract `b` from `a` in `AzInt`. -/
def sub (a b : AzInt) : AzInt :=
  match a.sign, b.sign with
  | true, true =>
    match AzNat.compare a.abs b.abs with
    | .lt => mkNorm false (b.abs - a.abs)
    | .eq => 0
    | .gt => mkNorm true (a.abs - b.abs)
  | false, false =>
    match AzNat.compare a.abs b.abs with
    | .lt => mkNorm true (b.abs - a.abs)
    | .eq => 0
    | .gt => mkNorm false (a.abs - b.abs)
  | true, false => mkNorm true (a.abs + b.abs)
  | false, true => mkNorm false (a.abs + b.abs)

instance : Sub AzInt := ⟨sub⟩

end Azurite.AzInt
