/-
  Correctness of the limb-level modular inverse `AzNat.invMod`:

  * `invMod_lt` — the result is a residue, `invMod a n < n`;
  * `mul_invMod` — the defining property
    `a · invMod a n ≡ 1 (mod n)` for coprime inputs, from the
    extended-GCD Bézout identity (`AzInt.egcd_bezout` +
    `AzInt.egcd_gcd`);
  * `toNat_invMod` — agreement with the reference `CP.invMod` on
    coprime inputs: the two use different Bézout pairs (binary vs
    classical extended Euclid), but the inverse below the modulus is
    unique (`CP.invMod_unique`).
-/
import Azurite.AzNat.InvMod
import Azurite.AzInt.Equiv.ExtendedGcd
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzInt.Equiv.Conversion
import Azurite.CrandallPomerance.Chapter2.Algorithm_2_1_7

namespace Azurite

namespace AzNat

/-- The value of `invMod` over `ℤ`: the Euclidean reduction of the
Bézout coefficient. -/
private theorem intCast_toNat_invMod (a : AzNat) {n : AzNat}
    (hn : 0 < n.toNat) :
    ((invMod a n).toNat : ℤ)
      = (AzInt.egcd a n).2.1.toInt % (n.toNat : ℤ) := by
  have hn0 : ((n.toNat : ℤ)) ≠ 0 := by exact_mod_cast hn.ne'
  rw [invMod, AzInt.toNat_natAbs, AzInt.toInt_emod, AzNat.toInt_toAzInt,
    Int.natAbs_of_nonneg (Int.emod_nonneg _ hn0)]

theorem invMod_lt (a : AzNat) {n : AzNat} (hn : 0 < n.toNat) :
    (invMod a n).toNat < n.toNat := by
  have h := Int.emod_lt_of_pos (AzInt.egcd a n).2.1.toInt
    (b := (n.toNat : ℤ)) (by exact_mod_cast hn)
  have hval := intCast_toNat_invMod a hn
  omega

/-- The defining property: for coprime `a`, `n`,
`a · invMod a n ≡ 1 (mod n)`. -/
theorem mul_invMod {a n : AzNat} (h : Nat.Coprime a.toNat n.toNat)
    (hn : 0 < n.toNat) :
    a.toNat * (invMod a n).toNat ≡ 1 [MOD n.toNat] := by
  have hbez : (1 : ℤ) = (AzInt.egcd a n).2.1.toInt * (a.toNat : ℤ)
      + (AzInt.egcd a n).2.2.toInt * (n.toNat : ℤ) := by
    have hb := AzInt.egcd_bezout a n
    rw [AzInt.egcd_gcd a n, h] at hb
    exact_mod_cast hb.symm
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  push_cast
  rw [intCast_toNat_invMod a hn]
  refine ⟨-((a.toNat : ℤ)
      * ((AzInt.egcd a n).2.1.toInt / (n.toNat : ℤ)))
      - (AzInt.egcd a n).2.2.toInt, ?_⟩
  rw [Int.emod_def, hbez]
  ring

/-- **Agreement with the reference**: on coprime inputs the
limb-level inverse equals `CP.invMod` (inverses below the modulus
are unique, though the Bézout pairs differ). -/
theorem toNat_invMod {a n : AzNat} (h : Nat.Coprime a.toNat n.toNat)
    (hn : 0 < n.toNat) :
    (invMod a n).toNat = CP.invMod a.toNat n.toNat :=
  CP.invMod_unique hn (invMod_lt a hn) (mul_invMod h hn)

end AzNat

end Azurite
