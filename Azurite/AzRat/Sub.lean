import Azurite.AzRat.Add
import Azurite.AzRat.Unary

/-!
# Subtraction for `AzRat`

Subtraction is addition with the second operand's sign flipped, and the
implementation is exactly that: a copy of `AzRat.add` whose `combineSigned`
call receives `!y.sign`, with the `x = 0` shortcut returning `-y`. Flipping
the sign bit inline avoids materializing the intermediate `-y` (a fresh
constructor cell), and all the reduction arguments — the cross-denominator
gcd splitting, the coprimality of the combined numerator — are sign-blind,
so the invariant proofs are reused verbatim from `Azurite/AzRat/Add.lean`.

Despite the separate implementation, `x - y = x + (-y)` holds *structurally*
(`sub_eq_add_neg` in `Azurite/AzRat/Equiv/Sub.lean`): negation only flips
the sign bit, so `add`'s body applied to `-y` is syntactically `sub`'s body
applied to `y`. Correctness in both directions (`toRat_sub`, `ofRat_sub`)
then follows from the addition and negation theorems.
-/

namespace Azurite.AzRat

/-- Subtract two `AzRat`s: `AzRat.add` with `y`'s sign flipped inline (no
intermediate `-y` is allocated). See the docstring of `AzRat.add` for the
gcd-splitting strategy; it is identical here. -/
protected def sub (x y : AzRat) : AzRat :=
  if hx : x.num = 0 then -y
  else if hy : y.num = 0 then x
  else
    let g := AzNat.gcd x.den y.den
    have hgN : g.toNat = Nat.gcd x.den.toNat y.den.toNat := AzNat.toNat_gcd _ _
    have hxd : x.den.toNat ≠ 0 :=
      fun h => x.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hyd : y.den.toNat ≠ 0 :=
      fun h => y.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hxr : Nat.Coprime x.num.toNat x.den.toNat := (AzNat.coprime_iff _ _).mp x.reduced
    have hyr : Nat.Coprime y.num.toNat y.den.toNat := (AzNat.coprime_iff _ _).mp y.reduced
    if hg : g = 1 then
      -- Fast path: coprime denominators, no reduction needed at all.
      have hg1 : Nat.Coprime x.den.toNat y.den.toNat := by
        show Nat.gcd _ _ = 1
        rw [← hgN, hg, AzNat.toNat_one]
      let sm := combineSigned x.sign (!y.sign) (x.num * y.den) (x.den * y.num)
      if hm : sm.2 = 0 then 0
      else
        { sign := sm.1
          num := sm.2
          den := x.den * y.den
          den_nz := fun h => by
            have h0 := congrArg AzNat.toNat h
            rw [AzNat.toNat_mul, AzNat.toNat_zero] at h0
            exact absurd h0 (Nat.mul_ne_zero hxd hyd)
          zero_sign := fun h => absurd h hm
          reduced := (AzNat.coprime_iff _ _).mpr (by
            rw [AzNat.toNat_mul]
            have hspec := combineSigned_snd_spec x.sign (!y.sign)
              (x.num * y.den) (x.den * y.num)
            rw [AzNat.toNat_mul, AzNat.toNat_mul] at hspec
            exact Nat.Coprime.mul_right
              (coprime_combine hspec (dvd_mul_right _ _)
                (Nat.Coprime.mul_left hxr hg1.symm))
              (coprime_combine' hspec (dvd_mul_left _ _)
                (Nat.Coprime.mul_left hg1 hyr))) }
    else
      -- Common-factor path: small numerator, second gcd on small operands.
      have hGpos : 0 < Nat.gcd x.den.toNat y.den.toNat :=
        Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxd)
      have hB' : x.den.toNat / Nat.gcd x.den.toNat y.den.toNat ∣ x.den.toNat :=
        Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
      have hD' : y.den.toNat / Nat.gcd x.den.toNat y.den.toNat ∣ y.den.toNat :=
        Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
      have hB'D' : Nat.Coprime (x.den.toNat / Nat.gcd x.den.toNat y.den.toNat)
          (y.den.toNat / Nat.gcd x.den.toNat y.den.toNat) :=
        Nat.coprime_div_gcd_div_gcd hGpos
      let b' := x.den / g
      let d' := y.den / g
      have hb'N : b'.toNat = x.den.toNat / Nat.gcd x.den.toNat y.den.toNat := by
        show (x.den / g).toNat = _
        rw [AzNat.toNat_div, hgN]
      have hd'N : d'.toNat = y.den.toNat / Nat.gcd x.den.toNat y.den.toNat := by
        show (y.den / g).toNat = _
        rw [AzNat.toNat_div, hgN]
      let sm := combineSigned x.sign (!y.sign) (x.num * d') (b' * y.num)
      if hm : sm.2 = 0 then 0
      else
        have hmN : sm.2.toNat ≠ 0 :=
          fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
        let g2 := AzNat.gcd sm.2 g
        have hg2N : g2.toNat = Nat.gcd sm.2.toNat (Nat.gcd x.den.toNat y.den.toNat) := by
          show (AzNat.gcd sm.2 g).toNat = _
          rw [AzNat.toNat_gcd, hgN]
        have hspec := combineSigned_snd_spec x.sign (!y.sign) (x.num * d') (b' * y.num)
        have hspec' := hspec
        have hrw : ((x.num * d').toNat = x.num.toNat *
              (y.den.toNat / Nat.gcd x.den.toNat y.den.toNat)) ∧
            ((b' * y.num).toNat = x.den.toNat / Nat.gcd x.den.toNat y.den.toNat *
              y.num.toNat) := by
          constructor
          · rw [AzNat.toNat_mul, AzNat.toNat_div, hgN]
          · rw [AzNat.toNat_mul, AzNat.toNat_div, hgN]
        have h1 : Nat.Coprime sm.2.toNat
            (x.den.toNat / Nat.gcd x.den.toNat y.den.toNat) := by
          rw [hrw.1, hrw.2] at hspec
          exact coprime_combine hspec (dvd_mul_right _ _)
            (Nat.Coprime.mul_left (hxr.coprime_dvd_right hB') hB'D'.symm)
        have h2 : Nat.Coprime sm.2.toNat
            (y.den.toNat / Nat.gcd x.den.toNat y.den.toNat) := by
          rw [hrw.1, hrw.2] at hspec'
          exact coprime_combine' hspec' (dvd_mul_left _ _)
            (Nat.Coprime.mul_left hB'D' (hyr.coprime_dvd_right hD'))
        { sign := sm.1
          num := sm.2 / g2
          den := b' * (d' * (g / g2))
          den_nz := fun h => by
            have h0 := congrArg AzNat.toNat h
            simp only [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_zero] at h0
            rw [hb'N, hd'N, hg2N, hgN] at h0
            have hb : 0 < x.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
              Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxd)
                (Nat.gcd_dvd_left _ _)) hGpos
            have hd : 0 < y.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
              Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hyd)
                (Nat.gcd_dvd_right _ _)) hGpos
            have hgg : 0 < Nat.gcd x.den.toNat y.den.toNat /
                Nat.gcd sm.2.toNat (Nat.gcd x.den.toNat y.den.toNat) :=
              Nat.div_pos (Nat.le_of_dvd hGpos (Nat.gcd_dvd_right _ _))
                (Nat.gcd_pos_of_pos_right _ hGpos)
            exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos hb (Nat.mul_pos hd hgg)))
          zero_sign := fun h => by
            have h0 := congrArg AzNat.toNat h
            simp only [AzNat.toNat_div, AzNat.toNat_zero] at h0
            rw [hg2N] at h0
            have : 0 < sm.2.toNat /
                Nat.gcd sm.2.toNat (Nat.gcd x.den.toNat y.den.toNat) :=
              Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hmN)
                (Nat.gcd_dvd_left _ _))
                (Nat.gcd_pos_of_pos_right _ hGpos)
            exact absurd h0 (Nat.ne_of_gt this)
          reduced := (AzNat.coprime_iff _ _).mpr (by
            simp only [AzNat.toNat_mul, AzNat.toNat_div]
            rw [hb'N, hd'N, hg2N, hgN]
            exact coprime_assemble (Nat.pos_iff_ne_zero.mp hGpos) h1 h2) }

instance : Sub AzRat := ⟨AzRat.sub⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "1/2" <*> AzRat.parse "1/3") == some "1/6"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "1/3" <*> AzRat.parse "1/2") == some "-1/6"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "1/6" <*> AzRat.parse "-1/10") == some "4/15"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "2/3" <*> AzRat.parse "1/6") == some "1/2"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "-1/2" <*> AzRat.parse "1/3") == some "-5/6"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "1/2" <*> AzRat.parse "1/2") == some "0"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "5/6" <*> AzRat.parse "-1/6") == some "1"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "0" <*> AzRat.parse "3/7") == some "-3/7"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "3/7" <*> AzRat.parse "0") == some "3/7"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "3" <*> AzRat.parse "3") == some "0"
#guard ((fun a b => AzRat.toString (a - b)) <$> AzRat.parse "-1/6" <*> AzRat.parse "-1/10") == some "-1/15"

end Azurite
