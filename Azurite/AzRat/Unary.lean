import Azurite.AzRat.Construct
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString

/-!
# Unary operations on `AzRat`: negation, absolute value, reciprocal

All three are sign/field-level operations — no limb arithmetic happens:

* `neg` flips the sign (zero stays canonically positive), giving the `Neg` instance;
* `abs` forces the sign positive;
* `inv` swaps numerator and denominator keeping the sign (a swap preserves both the
  coprimality invariant and the value's reducedness), with `0⁻¹ = 0` per the
  `GroupWithZero` convention, giving the `Inv` instance.

Correctness against `ℚ` (in both `toRat` and `ofRat` forms) is proven in
`Azurite/AzRat/Equiv/Unary.lean`.
-/

namespace Azurite.AzRat

/-- Negation: flip the sign. Zero stays canonically positive. -/
def neg (q : AzRat) : AzRat where
  sign := if q.num = 0 then true else !q.sign
  num := q.num
  den := q.den
  den_nz := q.den_nz
  zero_sign := fun h => if_pos h
  reduced := q.reduced

instance : Neg AzRat := ⟨neg⟩

/-- Absolute value: force the sign positive. (No `|·|` notation yet — Mathlib's
lattice-`abs` needs order instances `AzRat` does not have so far.) -/
def abs (q : AzRat) : AzRat :=
  { q with sign := true, zero_sign := fun _ => rfl }

/-- Reciprocal: swap numerator and denominator, keeping the sign; `0⁻¹ = 0`
(the `GroupWithZero` convention). The swap preserves coprimality, so no
re-reduction is needed. -/
def inv (q : AzRat) : AzRat :=
  if hn : q.num = 0 then 0
  else
    { sign := q.sign
      num := q.den
      den := q.num
      den_nz := hn
      zero_sign := fun h => absurd h q.den_nz
      reduced := (AzNat.coprime_iff _ _).mpr ((AzNat.coprime_iff _ _).mp q.reduced).symm }

instance : Inv AzRat := ⟨inv⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.toString`/`AzRat.parse`).

#guard ((fun q => AzRat.toString (-q)) <$> AzRat.parse "1/3") == some "-1/3"
#guard ((fun q => AzRat.toString (-q)) <$> AzRat.parse "-1/3") == some "1/3"
#guard ((fun q => AzRat.toString (-q)) <$> AzRat.parse "0") == some "0"
#guard ((fun q => AzRat.toString q.abs) <$> AzRat.parse "-2/9") == some "2/9"
#guard ((fun q => AzRat.toString q.abs) <$> AzRat.parse "4") == some "4"
#guard ((fun q => AzRat.toString q.abs) <$> AzRat.parse "0") == some "0"
#guard ((fun q => AzRat.toString q⁻¹) <$> AzRat.parse "-2/3") == some "-3/2"
#guard ((fun q => AzRat.toString q⁻¹) <$> AzRat.parse "5") == some "1/5"
#guard ((fun q => AzRat.toString q⁻¹) <$> AzRat.parse "1/5") == some "5"
#guard ((fun q => AzRat.toString q⁻¹) <$> AzRat.parse "0") == some "0"

end Azurite
