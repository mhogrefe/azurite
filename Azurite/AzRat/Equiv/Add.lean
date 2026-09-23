import Azurite.AzRat.Add
import Azurite.AzRat.Equiv.Unary
import Mathlib.Tactic.LinearCombination

/-!
# Correctness of `AzRat` addition

`toRat_add` / `ofRat_add`: gcd-splitting addition computes exactly the field
addition of `ℚ`, in both directions. The bridge is `combineSigned_int_spec`:
the sign-magnitude combination equals the *signed* sum `±u ± v` in `ℤ`. The
rest is the `divInt` playbook (`Rat.divInt_add_divInt`,
`Rat.divInt_eq_divInt_iff`), with the substitutions `b = b'·g`, `d = d'·g`,
`g = (g/g₂)·g₂`, `t = (t/g₂)·g₂` rewritten in and a single
`linear_combination` of the spec closing each sign case.
-/

namespace Azurite.AzRat

/-- `combineSigned` computes the signed sum: as integers,
`±(combineSigned sx sy u v) = ±u + ±v` with the signs interpreted by the
respective `Bool`s. -/
theorem combineSigned_int_spec (sx sy : Bool) (u v : AzNat) :
    (if (combineSigned sx sy u v).1 then ((combineSigned sx sy u v).2.toNat : ℤ)
     else -((combineSigned sx sy u v).2.toNat : ℤ))
    = (if sx then (u.toNat : ℤ) else -(u.toNat : ℤ))
      + (if sy then (v.toNat : ℤ) else -(v.toNat : ℤ)) := by
  unfold combineSigned
  cases sx <;> cases sy
  · -- false, false: -(u + v) = -u + -v
    rw [ite_eq_left (show ((false : Bool) == false) = true by decide)]
    dsimp only
    rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        ite_eq_right Bool.false_ne_true, AzNat.toNat_add]
    push_cast
    ring
  · -- false, true
    rw [ite_eq_right (show ¬(((false : Bool) == true) = true) by decide)]
    have hc := AzNat.compare_eq_compare_toNat u v
    rcases hcc : AzNat.compare u v with _ | _ | _ <;> rw [hcc] at hc
    · -- u < v: result (true, v - u)
      have hlt : u.toNat < v.toNat := compare_lt_iff_lt.mp hc.symm
      rw [ite_eq_left rfl, ite_eq_right Bool.false_ne_true, ite_eq_left rfl, AzNat.toNat_sub,
          Int.ofNat_sub (Nat.le_of_lt hlt)]
      ring
    · -- u = v: result (true, 0)
      have heq : u.toNat = v.toNat := compare_eq_iff_eq.mp hc.symm
      rw [ite_eq_left rfl, ite_eq_right Bool.false_ne_true, ite_eq_left rfl, AzNat.toNat_zero, heq]
      push_cast
      ring
    · -- u > v: result (false, u - v)
      have hgt : v.toNat < u.toNat := compare_gt_iff_gt.mp hc.symm
      rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_left rfl,
          AzNat.toNat_sub, Int.ofNat_sub (Nat.le_of_lt hgt)]
      ring
  · -- true, false
    rw [ite_eq_right (show ¬(((true : Bool) == false) = true) by decide)]
    have hc := AzNat.compare_eq_compare_toNat u v
    rcases hcc : AzNat.compare u v with _ | _ | _ <;> rw [hcc] at hc
    · -- u < v: result (false, v - u)
      have hlt : u.toNat < v.toNat := compare_lt_iff_lt.mp hc.symm
      rw [ite_eq_right Bool.false_ne_true, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
          AzNat.toNat_sub, Int.ofNat_sub (Nat.le_of_lt hlt)]
      ring
    · -- u = v: result (true, 0)
      have heq : u.toNat = v.toNat := compare_eq_iff_eq.mp hc.symm
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right Bool.false_ne_true, AzNat.toNat_zero, heq]
      push_cast
      ring
    · -- u > v: result (true, u - v)
      have hgt : v.toNat < u.toNat := compare_gt_iff_gt.mp hc.symm
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right Bool.false_ne_true, AzNat.toNat_sub,
          Int.ofNat_sub (Nat.le_of_lt hgt)]
      ring
  · -- true, true: u + v
    rw [ite_eq_left (show ((true : Bool) == true) = true by decide)]
    dsimp only
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, AzNat.toNat_add]
    push_cast
    ring

/-- Distribute a shared factor out of a signed conditional: lets the
correctness proofs treat the sign-conditionals as opaque atoms. -/
private lemma ite_neg_mul {P : Prop} [Decidable P] (a k : ℤ) :
    (if P then a * k else -(a * k)) = (if P then a else -a) * k := by
  split_ifs <;> ring

@[simp] theorem toRat_add (x y : AzRat) : toRat (x + y) = toRat x + toRat y := by
  show toRat (AzRat.add x y) = _
  by_cases hx : x.num = 0
  · rw [AzRat.add, dite_eq_left hx, toRat_of_num_zero x hx, zero_add]
  by_cases hy : y.num = 0
  · rw [AzRat.add, dite_eq_right hx, dite_eq_left hy, toRat_of_num_zero y hy, add_zero]
  have hxdN : x.den.toNat ≠ 0 :=
    fun h => x.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hydN : y.den.toNat ≠ 0 :=
    fun h => y.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  rw [AzRat.add, dite_eq_right hx, dite_eq_right hy, toRat_eq_divInt x, toRat_eq_divInt y,
      Rat.divInt_add_divInt _ _ (Int.natCast_ne_zero.mpr hxdN)
        (Int.natCast_ne_zero.mpr hydN)]
  by_cases hg : AzNat.gcd x.den y.den = 1
  · -- Coprime-denominator path.
    rw [dite_eq_left hg]
    have hspec := combineSigned_int_spec x.sign y.sign (x.num * y.den) (x.den * y.num)
    rw [AzNat.toNat_mul, AzNat.toNat_mul] at hspec
    simp only [Nat.cast_mul] at hspec
    rw [mul_comm ((x.den.toNat : ℤ)) ((y.num.toNat : ℤ)), ite_neg_mul, ite_neg_mul]
      at hspec
    by_cases hm : (combineSigned x.sign y.sign (x.num * y.den) (x.den * y.num)).2 = 0
    · rw [dite_eq_left hm, toRat_zero]
      rw [hm, AzNat.toNat_zero] at hspec
      simp only [Nat.cast_zero, neg_zero, ite_self] at hspec
      symm
      rw [show ((if x.sign = true then (x.num.toNat : ℤ) else -(x.num.toNat : ℤ)) *
            (y.den.toNat : ℤ) +
            (if y.sign = true then (y.num.toNat : ℤ) else -(y.num.toNat : ℤ)) *
            (x.den.toNat : ℤ)) = (0 : ℤ) from by linear_combination -hspec,
          Rat.zero_divInt]
    · rw [dite_eq_right hm, toRat_eq_divInt]
      dsimp only
      have hz1 : (((x.den * y.den).toNat : ℤ)) ≠ 0 := by
        rw [AzNat.toNat_mul]
        exact_mod_cast Nat.mul_ne_zero hxdN hydN
      have hz2 : ((x.den.toNat : ℤ)) * (y.den.toNat : ℤ) ≠ 0 :=
        mul_ne_zero (Int.natCast_ne_zero.mpr hxdN) (Int.natCast_ne_zero.mpr hydN)
      rw [Rat.divInt_eq_divInt_iff hz1 hz2]
      simp only [AzNat.toNat_mul, Nat.cast_mul]
      linear_combination ((x.den.toNat : ℤ) * (y.den.toNat : ℤ)) * hspec
  · -- Common-factor path.
    rw [dite_eq_right hg]
    have hspec := combineSigned_int_spec x.sign y.sign
      (x.num * (y.den / AzNat.gcd x.den y.den))
      (x.den / AzNat.gcd x.den y.den * y.num)
    rw [AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div,
        AzNat.toNat_gcd] at hspec
    simp only [Nat.cast_mul] at hspec
    rw [mul_comm ((x.den.toNat / Nat.gcd x.den.toNat y.den.toNat : ℕ) : ℤ)
          ((y.num.toNat : ℤ)), ite_neg_mul, ite_neg_mul] at hspec
    have hGpos : 0 < Nat.gcd x.den.toNat y.den.toNat :=
      Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxdN)
    have hBs : (x.den.toNat : ℤ) =
        ↑(x.den.toNat / Nat.gcd x.den.toNat y.den.toNat) *
          ↑(Nat.gcd x.den.toNat y.den.toNat) := by
      exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
    have hDs : (y.den.toNat : ℤ) =
        ↑(y.den.toNat / Nat.gcd x.den.toNat y.den.toNat) *
          ↑(Nat.gcd x.den.toNat y.den.toNat) := by
      exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
    by_cases hm : (combineSigned x.sign y.sign
        (x.num * (y.den / AzNat.gcd x.den y.den))
        (x.den / AzNat.gcd x.den y.den * y.num)).2 = 0
    · rw [dite_eq_left hm, toRat_zero]
      rw [hm, AzNat.toNat_zero] at hspec
      simp only [Nat.cast_zero, neg_zero, ite_self] at hspec
      symm
      rw [show ((if x.sign = true then (x.num.toNat : ℤ) else -(x.num.toNat : ℤ)) *
            (y.den.toNat : ℤ) +
            (if y.sign = true then (y.num.toNat : ℤ) else -(y.num.toNat : ℤ)) *
            (x.den.toNat : ℤ)) = (0 : ℤ) from by
              rw [hBs, hDs]
              linear_combination (-(↑(Nat.gcd x.den.toNat y.den.toNat) : ℤ)) * hspec,
          Rat.zero_divInt]
    · rw [dite_eq_right hm, toRat_eq_divInt]
      dsimp only
      have hg2pos : 0 < Nat.gcd (combineSigned x.sign y.sign
          (x.num * (y.den / AzNat.gcd x.den y.den))
          (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
          (Nat.gcd x.den.toNat y.den.toNat) :=
        Nat.gcd_pos_of_pos_right _ hGpos
      have hz1 : ((x.den / AzNat.gcd x.den y.den *
          (y.den / AzNat.gcd x.den y.den *
            (AzNat.gcd x.den y.den / AzNat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2
              (AzNat.gcd x.den y.den)))).toNat : ℤ) ≠ 0 := by
        simp only [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_gcd]
        have hb : 0 < x.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxdN)
            (Nat.gcd_dvd_left _ _)) hGpos
        have hd : 0 < y.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hydN)
            (Nat.gcd_dvd_right _ _)) hGpos
        have hw : 0 < Nat.gcd x.den.toNat y.den.toNat /
            Nat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
              (Nat.gcd x.den.toNat y.den.toNat) :=
          Nat.div_pos (Nat.le_of_dvd hGpos (Nat.gcd_dvd_right _ _)) hg2pos
        exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hb (Nat.mul_pos hd hw))
      have hz2 : ((x.den.toNat : ℤ)) * (y.den.toNat : ℤ) ≠ 0 :=
        mul_ne_zero (Int.natCast_ne_zero.mpr hxdN) (Int.natCast_ne_zero.mpr hydN)
      rw [Rat.divInt_eq_divInt_iff hz1 hz2]
      simp only [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_gcd, Nat.cast_mul]
      have hMs : ((combineSigned x.sign y.sign
          (x.num * (y.den / AzNat.gcd x.den y.den))
          (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat : ℤ) =
          ↑((combineSigned x.sign y.sign
            (x.num * (y.den / AzNat.gcd x.den y.den))
            (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat /
            Nat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
              (Nat.gcd x.den.toNat y.den.toNat)) *
          ↑(Nat.gcd (combineSigned x.sign y.sign
            (x.num * (y.den / AzNat.gcd x.den y.den))
            (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
            (Nat.gcd x.den.toNat y.den.toNat)) := by
        exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      have hGs : ((Nat.gcd x.den.toNat y.den.toNat : ℤ)) =
          ↑(Nat.gcd x.den.toNat y.den.toNat /
            Nat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
              (Nat.gcd x.den.toNat y.den.toNat)) *
          ↑(Nat.gcd (combineSigned x.sign y.sign
            (x.num * (y.den / AzNat.gcd x.den y.den))
            (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
            (Nat.gcd x.den.toNat y.den.toNat)) := by
        exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
      rw [hMs, ite_neg_mul] at hspec
      rw [hBs, hDs, hGs]
      linear_combination
        ((↑(x.den.toNat / Nat.gcd x.den.toNat y.den.toNat) : ℤ) *
          ↑(y.den.toNat / Nat.gcd x.den.toNat y.den.toNat) *
          ↑(Nat.gcd x.den.toNat y.den.toNat /
            Nat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
              (Nat.gcd x.den.toNat y.den.toNat)) *
          ↑(Nat.gcd x.den.toNat y.den.toNat /
            Nat.gcd (combineSigned x.sign y.sign
              (x.num * (y.den / AzNat.gcd x.den y.den))
              (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
              (Nat.gcd x.den.toNat y.den.toNat)) *
          ↑(Nat.gcd (combineSigned x.sign y.sign
            (x.num * (y.den / AzNat.gcd x.den y.den))
            (x.den / AzNat.gcd x.den y.den * y.num)).2.toNat
            (Nat.gcd x.den.toNat y.den.toNat))) * hspec

@[simp] theorem ofRat_add (r s : ℚ) : ofRat (r + s) = ofRat r + ofRat s :=
  toRat_injective (by rw [toRat_ofRat, toRat_add, toRat_ofRat, toRat_ofRat])

end Azurite.AzRat
