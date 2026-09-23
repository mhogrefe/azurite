/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Construct
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString
import Azurite.AzNat.Sub
import Azurite.AzNat.Equiv.Sub

/-!
# Addition for `AzRat`, with cross-denominator gcd splitting

To add `a/b` and `c/d` (both reduced), let `g = gcd b d`.

* If `g = 1`, the sum is `(a·d + b·c) / (b·d)` and **no reduction is
  needed**: a common divisor of the numerator and `b` would divide `a·d`,
  but it is coprime to `a` (since `a ⊥ b`) and to `d` (since `g = 1`);
  symmetrically for `d`.
* Otherwise write `b' = b/g`, `d' = d/g`. The sum is `t / (g·b'·d')` with
  the *small* numerator `t = a·d' + b'·c`, and `t` is automatically coprime
  to both `b'` and `d'` (same argument, using `b' ⊥ d'`) — so the only
  factor left to remove divides `g`. With `g₂ = gcd t g` the result is
  `(t/g₂) / (b'·(d'·(g/g₂)))`, in lowest terms.

Both gcds run on as-small-as-possible arguments: `g` on the two
denominators (never on products), and `g₂` on the small numerator `t`
against the small `g`. Signs are handled by `combineSigned`: with equal
signs the magnitudes add; with opposite signs the smaller is subtracted
from the larger (one magnitude comparison), and exact cancellation
short-circuits to the canonical zero.
-/

namespace Azurite.AzRat

/-- Combine two sign-magnitude values over a common denominator: the sign
and magnitude of `±u ± v`. Equal magnitudes with opposite signs give the
canonical positive zero. -/
def combineSigned (sx sy : Bool) (u v : AzNat) : Bool × AzNat :=
  if sx == sy then (sx, u + v)
  else
    match AzNat.compare u v with
    | .gt => (sx, u - v)
    | .lt => (sy, v - u)
    | .eq => (true, 0)

/-- The magnitude produced by `combineSigned` is `u + v`, `u - v`, or
`v - u` (with the matching order fact). -/
theorem combineSigned_snd_spec (sx sy : Bool) (u v : AzNat) :
    (combineSigned sx sy u v).2.toNat = u.toNat + v.toNat
    ∨ ((combineSigned sx sy u v).2.toNat = u.toNat - v.toNat ∧ v.toNat ≤ u.toNat)
    ∨ ((combineSigned sx sy u v).2.toNat = v.toNat - u.toNat ∧ u.toNat ≤ v.toNat) := by
  unfold combineSigned
  split_ifs with h
  · exact Or.inl (AzNat.toNat_add u v)
  · have hc := AzNat.compare_eq_compare_toNat u v
    rcases hcc : AzNat.compare u v with _ | _ | _ <;> rw [hcc] at hc
    · -- lt
      have hlt : u.toNat < v.toNat := compare_lt_iff_lt.mp hc.symm
      exact Or.inr (Or.inr ⟨AzNat.toNat_sub v u, Nat.le_of_lt hlt⟩)
    · -- eq
      have heq : u.toNat = v.toNat := compare_eq_iff_eq.mp hc.symm
      exact Or.inr (Or.inl ⟨by rw [AzNat.toNat_zero, heq, Nat.sub_self],
        Nat.le_of_eq heq.symm⟩)
    · -- gt
      have hgt : v.toNat < u.toNat := compare_gt_iff_gt.mp hc.symm
      exact Or.inr (Or.inl ⟨AzNat.toNat_sub u v, Nat.le_of_lt hgt⟩)

/-- A `±` combination of `u` and `v` is coprime to `k` when `k` divides `v`
and is coprime to `u`: a common divisor of the combination and `k` divides
`u` as well, hence divides `gcd u k = 1`. -/
theorem coprime_combine {u v m k : ℕ}
    (hm : m = u + v ∨ (m = u - v ∧ v ≤ u) ∨ (m = v - u ∧ u ≤ v))
    (hdvd : k ∣ v) (hu : Nat.Coprime u k) : Nat.Coprime m k := by
  have key : Nat.gcd m k ∣ u := by
    have h1 : Nat.gcd m k ∣ m := Nat.gcd_dvd_left m k
    have hv : Nat.gcd m k ∣ v := dvd_trans (Nat.gcd_dvd_right m k) hdvd
    rcases hm with rfl | ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · have := Nat.dvd_sub h1 hv
      rwa [Nat.add_sub_cancel] at this
    · have := Nat.dvd_add h1 hv
      rwa [Nat.sub_add_cancel hle] at this
    · have := Nat.dvd_sub hv h1
      rwa [Nat.sub_sub_self hle] at this
  have h := Nat.dvd_gcd key (Nat.gcd_dvd_right m k)
  rw [hu.gcd_eq_one] at h
  exact Nat.dvd_one.mp h

/-- Variant of `coprime_combine`: `k` divides `u` and is coprime to `v`. -/
theorem coprime_combine' {u v m k : ℕ}
    (hm : m = u + v ∨ (m = u - v ∧ v ≤ u) ∨ (m = v - u ∧ u ≤ v))
    (hdvd : k ∣ u) (hv : Nat.Coprime v k) : Nat.Coprime m k := by
  refine coprime_combine ?_ hdvd hv
  rcases hm with rfl | ⟨rfl, hle⟩ | ⟨rfl, hle⟩
  · exact Or.inl (Nat.add_comm u v)
  · exact Or.inr (Or.inr ⟨rfl, hle⟩)
  · exact Or.inr (Or.inl ⟨rfl, hle⟩)

/-- Assemble the reduced fraction: once the numerator `m` is coprime to
`b'` and `d'`, dividing `m` and `g` by `g₂ = gcd m g` puts the sum in
lowest terms. -/
theorem coprime_assemble {m b' d' g : ℕ} (hg : g ≠ 0)
    (h1 : Nat.Coprime m b') (h2 : Nat.Coprime m d') :
    Nat.Coprime (m / Nat.gcd m g) (b' * (d' * (g / Nat.gcd m g))) := by
  have hpos : 0 < Nat.gcd m g := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hg)
  have hdvd_m : m / Nat.gcd m g ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  exact Nat.Coprime.mul_right (h1.coprime_dvd_left hdvd_m)
    (Nat.Coprime.mul_right (h2.coprime_dvd_left hdvd_m)
      (Nat.coprime_div_gcd_div_gcd hpos))

/-- Add two `AzRat`s (see the module docstring): one gcd of the
two denominators; in the common-factor case a second gcd of the small
numerator against `g`. No gcd ever runs on a product. -/
protected def add (x y : AzRat) : AzRat :=
  if hx : x.num = 0 then y
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
      let sm := combineSigned x.sign y.sign (x.num * y.den) (x.den * y.num)
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
            have hspec := combineSigned_snd_spec x.sign y.sign
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
      let sm := combineSigned x.sign y.sign (x.num * d') (b' * y.num)
      if hm : sm.2 = 0 then 0
      else
        have hmN : sm.2.toNat ≠ 0 :=
          fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
        let g2 := AzNat.gcd sm.2 g
        have hg2N : g2.toNat = Nat.gcd sm.2.toNat (Nat.gcd x.den.toNat y.den.toNat) := by
          show (AzNat.gcd sm.2 g).toNat = _
          rw [AzNat.toNat_gcd, hgN]
        have hspec := combineSigned_snd_spec x.sign y.sign (x.num * d') (b' * y.num)
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

instance : Add AzRat := ⟨AzRat.add⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "1/2" <*> AzRat.parse "1/3") == some "5/6"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "1/6" <*> AzRat.parse "1/10") == some "4/15"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "2/3" <*> AzRat.parse "-1/6") == some "1/2"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "-1/2" <*> AzRat.parse "-1/3") == some "-5/6"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "1/2" <*> AzRat.parse "-1/2") == some "0"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "5/6" <*> AzRat.parse "1/6") == some "1"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "0" <*> AzRat.parse "3/7") == some "3/7"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "3/7" <*> AzRat.parse "0") == some "3/7"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "3" <*> AzRat.parse "-3") == some "0"
#guard ((fun a b => AzRat.toString (a + b)) <$> AzRat.parse "-1/6" <*> AzRat.parse "1/10") == some "-1/15"

end Azurite
