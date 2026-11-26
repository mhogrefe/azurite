/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Equiv.Curve
import Azurite.AzZMod.Pow

/-!
# The ladder in Montgomery form

`jacMul` over `AzZMod n` spends its time in multiplications modulo `n`.  For odd `n` the same
ladder is run here on Montgomery forms (`AzZMod.Mont n`, one reduction for about the price of
one multiplication), and `jacMul_eq_jacMulFast` — a `@[csimp]` replacement, proven equal for
every `n` — makes the compiled `jacMul` (hence the checker `checkStep` and the generator) use
it.  The definitions of `ECPP/Curve.lean` and everything proven about them are unchanged.

* `jacDblG`, `jacAddMixedG`, `jacMulG`: the formulas of `Curve.lean` over any type with
  `+`, `−`, `*`, squaring and `1`.
* `jacMulG_map`: over Montgomery forms they are the ladder of the specification.
* `jacMulMont`, `jacMulFast`, `jacMul_eq_jacMulFast`.
-/

namespace Azurite.ECPP

open AzZMod

section Generic

variable {R : Type _} [Add R] [Sub R] [Mul R] [Square R] [One R]

/-- `jacDbl` over any type with the ring operations it uses. -/
def jacDblG (a : R) (P : R × R × R) : R × R × R :=
  let x2 := Square.square P.1
  let y2 := Square.square P.2.1
  let z2 := Square.square P.2.2
  let m := x2 + x2 + x2 + a * Square.square z2
  let s := P.1 * y2
  let s2 := s + s
  let s4 := s2 + s2
  let x3 := Square.square m - (s4 + s4)
  let y4 := Square.square y2
  let y42 := y4 + y4
  let y44 := y42 + y42
  (x3, m * (s4 - x3) - (y44 + y44), (P.2.1 + P.2.1) * P.2.2)

/-- `jacAddMixed` over any type with the ring operations it uses. -/
def jacAddMixedG (u v : R) (P : R × R × R) : R × R × R :=
  let z2 := Square.square P.2.2
  let h := u * z2 - P.1
  let r := v * (P.2.2 * z2) - P.2.1
  let h2 := Square.square h
  let h3 := h * h2
  let w := P.1 * h2
  let x3 := Square.square r - h3 - (w + w)
  (x3, r * (w - x3) - P.2.1 * h3, P.2.2 * h)

/-- `jacMul` over any type with the ring operations it uses. -/
def jacMulG (a u v : R) : Nat → AzNat → Option (R × R × R)
  | 0, _ => none
  | fuel + 1, k =>
    if k = AzNat.ofNat 1 then some (u, v, 1)
    else
      (jacMulG a u v fuel (k.shiftRight 1)).map fun T =>
        let d := jacDblG a T
        if k.testBit 0 then jacAddMixedG u v d else d

end Generic

variable {n : AzNat}

section Mont

variable [d : MontData n]

/-- The residues a point in Montgomery form represents. -/
noncomputable def mapPtMont (P : Mont n × Mont n × Mont n) :
    ZMod n.toNat × ZMod n.toNat × ZMod n.toNat :=
  (Mont.toZMod P.1, Mont.toZMod P.2.1, Mont.toZMod P.2.2)

theorem mapPtMont_jacDblG (a : Mont n) (P : Mont n × Mont n × Mont n) :
    mapPtMont (jacDblG a P) = dblShort (Mont.toZMod a) (mapPtMont P) := by
  simp only [jacDblG, mapPtMont, dblShort, Mont.toZMod_add, Mont.toZMod_sub, Mont.toZMod_mul,
    Mont.toZMod_square]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem mapPtMont_jacAddMixedG (u v : Mont n) (P : Mont n × Mont n × Mont n) :
    mapPtMont (jacAddMixedG u v P)
      = addMixed (Mont.toZMod u) (Mont.toZMod v) (mapPtMont P) := by
  simp only [jacAddMixedG, mapPtMont, addMixed, Mont.toZMod_add, Mont.toZMod_sub,
    Mont.toZMod_mul, Mont.toZMod_square]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **Over Montgomery forms, `jacMulG` is the ladder of the specification.** -/
theorem jacMulG_map (a u v : Mont n) : ∀ (fuel : ℕ) (k : AzNat),
    (jacMulG a u v fuel k).map mapPtMont
      = ladder (Mont.toZMod a) (Mont.toZMod u) (Mont.toZMod v) fuel k.toNat
  | 0, _ => rfl
  | fuel + 1, k => by
    rw [jacMulG, ladder]
    have h1 : k = AzNat.ofNat 1 ↔ k.toNat = 1 := by
      constructor
      · rintro rfl
        exact AzNat.toNat_ofNat 1
      · intro h
        exact AzNat.toNat_injective (by rw [h, AzNat.toNat_ofNat])
    by_cases hk : k = AzNat.ofNat 1
    · rw [ite_eq_left hk, ite_eq_left (h1.mp hk)]
      simp [mapPtMont, Mont.toZMod_one]
    · rw [ite_eq_right hk, ite_eq_right (mt h1.mpr hk)]
      have hshift : (k.shiftRight 1).toNat = k.toNat / 2 := by
        rw [AzNat.toNat_shiftRight, pow_one]
      have ih := jacMulG_map a u v fuel (k.shiftRight 1)
      rw [hshift] at ih
      rw [← ih]
      have hbit : k.testBit 0 = decide (k.toNat % 2 = 1) := by
        rw [AzNat.testBit_eq_toNat_testBit, Nat.testBit_zero]
      cases jacMulG a u v fuel (k.shiftRight 1) with
      | none => rfl
      | some T =>
        simp only [Option.map_some]
        congr 1
        by_cases hodd : k.toNat % 2 = 1
        · have ht : k.testBit 0 = true := by rw [hbit]; exact decide_eq_true hodd
          rw [ite_eq_left ht, ite_eq_left hodd, mapPtMont_jacAddMixedG, mapPtMont_jacDblG]
        · have ht : ¬ k.testBit 0 = true := by rw [hbit]; simpa using hodd
          rw [ite_eq_right ht, ite_eq_right hodd, mapPtMont_jacDblG]

/-- A point out of Montgomery form. -/
def ofMontPt (P : Mont n × Mont n × Mont n) : JacPoint n :=
  (ofMont P.1, ofMont P.2.1, ofMont P.2.2)

theorem mapPt_ofMontPt (P : Mont n × Mont n × Mont n) : mapPt (ofMontPt P) = mapPtMont P := by
  simp only [mapPt, ofMontPt, mapPtMont, toZMod_ofMont]

end Mont

/-- `jacMul` for an odd `n`, in Montgomery form. -/
def jacMulMont (hn : Odd n.toNat) (a u v : AzZMod n) (fuel : ℕ) (k : AzNat) :
    Option (JacPoint n) :=
  let d : MontData n := ⟨AzNat.MontCtx.make n, rfl, hn⟩
  (jacMulG (toMont (d := d) a) (toMont (d := d) u) (toMont (d := d) v) fuel k).map
    (ofMontPt (d := d))

/-- `jacMul` as compiled: Montgomery form for an odd `n` and a long multiplier. -/
def jacMulFast [NeZero n.toNat] (a u v : AzZMod n) (fuel : ℕ) (k : AzNat) :
    Option (JacPoint n) :=
  if h : n.isOdd = true ∧ montPowMinBits ≤ k.size then
    jacMulMont ((AzNat.isOdd_iff n).mp h.1) a u v fuel k
  else jacMul a u v fuel k

theorem mapPt_injective [NeZero n.toNat] : Function.Injective (mapPt (n := n)) := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  simp only [mapPt, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [toZMod_injective h1, toZMod_injective h2, toZMod_injective h3]

theorem jacMulMont_eq [NeZero n.toNat] (hn : Odd n.toNat) (a u v : AzZMod n) (fuel : ℕ)
    (k : AzNat) : jacMulMont hn a u v fuel k = jacMul a u v fuel k := by
  apply Option.map_injective mapPt_injective
  unfold jacMulMont
  let _ : MontData n := ⟨AzNat.MontCtx.make n, rfl, hn⟩
  rw [jacMul_map, Option.map_map,
    show mapPt ∘ ofMontPt = mapPtMont from funext mapPt_ofMontPt, jacMulG_map,
    Mont.toZMod_toMont, Mont.toZMod_toMont, Mont.toZMod_toMont]

@[csimp] theorem jacMul_eq_jacMulFast : @jacMul = @jacMulFast := by
  funext n _ a u v fuel k
  unfold jacMulFast
  split
  · rw [jacMulMont_eq]
  · rfl

end Azurite.ECPP
