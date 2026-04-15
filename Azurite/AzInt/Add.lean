import Azurite.AzInt.Basic
import Azurite.AzInt.Conversion
import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.Compare

namespace Azurite.AzInt

/-- Smart constructor: normalizes the zero case so the `zero_sign` invariant
    holds for any input sign. -/
def mkNorm (s : Bool) (a : AzNat) : AzInt :=
  if h : a = 0 then ⟨true, 0, fun _ => rfl⟩
  else ⟨s, a, fun h' => absurd h' h⟩

/-- Add a `UInt64` `u` to an `AzInt` `z`. -/
def addUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  if z.sign then
    mkNorm true (z.abs.addUInt64 u)
  else
    match z.abs.compareUInt64 u with
    | .lt => mkNorm true (u.toAzNat - z.abs)
    | .eq => 0
    | .gt => mkNorm false (z.abs.subUInt64 u)

/-- Add two `AzInt`s. -/
def add (a b : AzInt) : AzInt :=
  match a.sign, b.sign with
  | true, true => mkNorm true (a.abs + b.abs)
  | false, false => mkNorm false (a.abs + b.abs)
  | true, false =>
    match AzNat.compare a.abs b.abs with
    | .lt => mkNorm false (b.abs - a.abs)
    | .eq => 0
    | .gt => mkNorm true (a.abs - b.abs)
  | false, true =>
    match AzNat.compare a.abs b.abs with
    | .lt => mkNorm true (b.abs - a.abs)
    | .eq => 0
    | .gt => mkNorm false (a.abs - b.abs)

instance : Add AzInt := ⟨add⟩

/-- Negation of an `AzInt`: flip the sign, preserving the `zero_sign`
    invariant via `mkNorm`. -/
def neg (z : AzInt) : AzInt := mkNorm (!z.sign) z.abs

instance : Neg AzInt := ⟨neg⟩

end Azurite.AzInt
