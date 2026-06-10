import Azurite.AzRat.Basic
import Azurite.AzInt.Basic
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Div.DivMod

/-!
# Constructing `AzRat`s from numerator/denominator pairs

`AzRat.ofAzNats num den` builds the reduced nonnegative fraction `num / den` from a pair
of `AzNat`s, and `AzRat.ofAzInts num den` builds the reduced signed fraction from a pair
of `AzInt`s (positive iff the signs agree). Both follow the `mkRat` convention of mapping
a zero denominator to `0`, and both share the sign-aware core `ofSignAzNats`, which
canonicalizes zero and discharges the `AzRat` invariants:

* `den_nz` and `zero_sign` reduce (via `toNat_div`/`toNat_gcd`) to positivity of
  `x / gcd x y` for nonzero `x`;
* `reduced` is `Nat.coprime_div_gcd_div_gcd` across the `coprime_iff` bridge.

Also provides the canonical zero `+0/1` and one `+1/1` (`OfNat`/`Zero`/`One`
instances, mirroring `AzNat`/`AzInt`), and `Inhabited` with default `0`.
-/

namespace Azurite.AzRat

instance : OfNat AzRat 0 :=
  ⟨{ sign := true
     num := 0
     den := 1
     den_nz := by decide
     zero_sign := fun _ => rfl
     reduced := (AzNat.coprime_iff 0 1).mpr (by
       rw [AzNat.toNat_one]; exact Nat.coprime_one_right _) }⟩

instance : Zero AzRat := ⟨0⟩

instance : OfNat AzRat 1 :=
  ⟨{ sign := true
     num := 1
     den := 1
     den_nz := by decide
     zero_sign := fun _ => rfl
     reduced := (AzNat.coprime_iff 1 1).mpr (by
       rw [AzNat.toNat_one]; exact Nat.coprime_one_right _) }⟩

instance : One AzRat := ⟨1⟩

instance : Inhabited AzRat := ⟨0⟩

/-- Build the reduced fraction `num / den` with sign `s` (`true` = nonnegative).
Returns the canonical zero when `den = 0` (the `mkRat` convention) or `num = 0`,
so a stray sign on a zero value never escapes. -/
def ofSignAzNats (s : Bool) (num den : AzNat) : AzRat :=
  if hd : den = 0 then 0
  else if hn : num = 0 then 0
  else
    -- `let` guarantees the gcd is computed once at the source level (the
    -- compiler's CSE would merge the duplicated calls anyway, but an O(n²)
    -- operation's call count should not depend on an optimization pass).
    let g := AzNat.gcd num den
    have hgN : g.toNat = Nat.gcd num.toNat den.toNat := AzNat.toNat_gcd num den
    have hd' : den.toNat ≠ 0 := fun h => hd (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hn' : num.toNat ≠ 0 := fun h => hn (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hg : 0 < Nat.gcd num.toNat den.toNat :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hd')
    { sign := s
      num := num / g
      den := den / g
      den_nz := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_div, hgN, AzNat.toNat_zero] at h0
        exact absurd h0 (Nat.ne_of_gt (Nat.div_pos
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hd') (Nat.gcd_dvd_right _ _)) hg))
      zero_sign := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_div, hgN, AzNat.toNat_zero] at h0
        exact absurd h0 (Nat.ne_of_gt (Nat.div_pos
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hn') (Nat.gcd_dvd_left _ _)) hg))
      reduced := (AzNat.coprime_iff _ _).mpr (by
        rw [AzNat.toNat_div, AzNat.toNat_div, hgN]
        exact Nat.coprime_div_gcd_div_gcd hg) }

/-- The reduced nonnegative fraction `num / den` from a pair of `AzNat`s
(`0` when `den = 0`, per the `mkRat` convention). -/
def ofAzNats (num den : AzNat) : AzRat :=
  ofSignAzNats true num den

/-- The reduced signed fraction `num / den` from a pair of `AzInt`s: sign-magnitude
division, nonnegative iff the signs agree (`0` when `den = 0`, per the `mkRat`
convention). -/
def ofAzInts (num den : AzInt) : AzRat :=
  ofSignAzNats (num.sign == den.sign) num.abs den.abs

end Azurite.AzRat
