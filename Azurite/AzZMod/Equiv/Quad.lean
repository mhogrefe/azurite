/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the computable quadratic ring `QuadT n u a`.**

  * `toQuad : QuadT m u a → QuadRing (ZMod m) u a`, the coordinate map
    `x₀ + x₁α ↦ quadElt u a x₀ x₁`; multiplicative, unital, additive
    (`toQuad_mul`, …), powers (`toQuad_pow`), norm (`toZMod_norm`),
    conjugate (`toQuad_mul_conj`).
  * `toQuad_injective` (via `quadElt_injective`: the power basis `1, α`
    of a monic quadratic) — so a *failed* equality check in `QuadT`
    is a genuine inequality in the model, the ingredient every
    composite verdict needs.
  * `NormOne.toQuad_pow`: the shortcut-squaring power on norm-one
    elements is the monoid power.
  * Transported verdicts of Test (4.3), (4.4)(c2), Remark (4.10):
    `NormOne.pow_card_succ_eq_one` (`x^(n+1) = 1` for prime `n`),
    `alpha_pow_card_succ` (`α^(n+1) = −a`), and
    `normOneCandidate_isSome` (the candidate never fails for prime `n`).
  * `tryInv_some` / `tryInv_none`: the fallible inverse.
-/
import Azurite.AzZMod.Quad
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzZMod.Equiv.Pow
import Azurite.AzNat.Equiv.InvMod
import Azurite.AzNat.Equiv.Gcd
import Azurite.CohenLenstra.Impl_4_9
import Azurite.Algorithm.Equiv.SlidingWindowPowAzNat

namespace Azurite

open Polynomial

namespace AzZMod

variable {m : AzNat} [NeZero m.toNat]

/-! ### The fallible inverse -/

omit [NeZero m.toNat] in
theorem gcd_val_eq_one_iff (x : AzZMod m) :
    AzNat.gcd x.val m = 1 ↔ Nat.Coprime x.val.toNat m.toNat := by
  rw [Nat.Coprime, ← AzNat.toNat_gcd]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact AzNat.toNat_injective (by rw [h]; rfl)

theorem tryInv_some {x y : AzZMod m} (h : tryInv x = some y) : y * x = 1 := by
  unfold tryInv at h
  split_ifs at h with hg
  · obtain rfl : ofAzNat m (AzNat.invMod x.val m) = y := Option.some.inj h
    have hc := (gcd_val_eq_one_iff x).mp hg
    have hm : 0 < m.toNat := Nat.pos_of_ne_zero (NeZero.ne _)
    apply toZMod_injective
    rw [toZMod_mul, toZMod_one, toZMod_ofAzNat]
    show ((AzNat.invMod x.val m).toNat : ZMod m.toNat) * ((x.val.toNat : ℕ) : ZMod m.toNat) = 1
    rw [← Nat.cast_mul, mul_comm]
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (AzNat.mul_invMod hc hm)

theorem tryInv_none {x : AzZMod m} (h : tryInv x = none) : ¬ IsUnit (toZMod x) := by
  unfold tryInv at h
  split_ifs at h with hg
  intro hu
  apply hg
  rw [gcd_val_eq_one_iff]
  have hu' : IsUnit ((x.val.toNat : ℕ) : ZMod m.toNat) := hu
  exact (ZMod.isUnit_iff_coprime _ _).mp hu'

/-! ### The coordinate map -/

namespace QuadT

variable {u a : AzZMod m}

/-- **The coordinate map** into the abstract ring of `Impl_4_3.lean`. -/
noncomputable def toQuad (x : QuadT m u a) :
    CL.QuadRing (ZMod m.toNat) (toZMod u) (toZMod a) :=
  CL.quadElt (toZMod u) (toZMod a) (toZMod x.x₀) (toZMod x.x₁)

theorem toQuad_mul (x y : QuadT m u a) : toQuad (x * y) = toQuad x * toQuad y := by
  show toQuad (mul x y) = _
  simp only [toQuad, mul, CL.quadElt_mul, toZMod_add, toZMod_sub, toZMod_mul]
  congr 1
  ring

theorem toQuad_one : toQuad (1 : QuadT m u a) = 1 := by
  show toQuad ⟨1, 0⟩ = 1
  simp [toQuad, CL.quadElt]

theorem toQuad_zero : toQuad (0 : QuadT m u a) = 0 := by
  show toQuad ⟨0, 0⟩ = 0
  simp [toQuad, CL.quadElt]

theorem toQuad_add (x y : QuadT m u a) : toQuad (x + y) = toQuad x + toQuad y := by
  show toQuad (add x y) = _
  simp only [toQuad, add, CL.quadElt, toZMod_add, map_add]
  ring

theorem toQuad_neg (x : QuadT m u a) : toQuad (-x) = -toQuad x := by
  show toQuad (neg x) = _
  simp only [toQuad, neg, CL.quadElt, toZMod_neg, map_neg]
  ring

theorem toQuad_sub (x y : QuadT m u a) : toQuad (x - y) = toQuad x - toQuad y := by
  show toQuad (sub x y) = _
  simp only [toQuad, sub, CL.quadElt, toZMod_sub, map_sub]
  ring

theorem toQuad_alpha :
    toQuad (alpha : QuadT m u a)
      = AdjoinRoot.root (X ^ 2 - C (toZMod u) * X - C (toZMod a) : Polynomial (ZMod m.toNat)) := by
  simp [toQuad, alpha, CL.quadElt]

theorem toQuad_const (c : AzZMod m) :
    toQuad (const c : QuadT m u a) = algebraMap _ _ (toZMod c) := by
  simp [toQuad, const, CL.quadElt]

/-- **The norm computes `quadNorm`.** -/
theorem toZMod_norm (x : QuadT m u a) :
    toZMod (norm x) = CL.quadNorm (toZMod u) (toZMod a) (toZMod x.x₀) (toZMod x.x₁) := by
  simp only [norm, CL.quadNorm, toZMod_add, toZMod_sub, toZMod_mul]
  ring

theorem toQuad_conj (x : QuadT m u a) :
    toQuad (conj x)
      = algebraMap _ _ (toZMod x.x₀)
        + algebraMap _ _ (toZMod x.x₁)
          * (algebraMap (ZMod m.toNat) (CL.QuadRing (ZMod m.toNat) (toZMod u) (toZMod a))
              (toZMod u)
            - AdjoinRoot.root _) := by
  simp only [toQuad, conj, CL.quadElt, toZMod_add, toZMod_mul, toZMod_neg, map_add, map_mul,
    map_neg]
  ring

/-- `x · x̄ = N(x)`. -/
theorem toQuad_mul_conj (x : QuadT m u a) :
    toQuad x * toQuad (conj x) = algebraMap _ _ (toZMod (norm x)) := by
  rw [toQuad_conj, toZMod_norm]
  exact CL.mul_conj_eq_quadNorm _ _ _ _

/-- **Powers transport.** -/
theorem toQuad_pow (x : QuadT m u a) (n : ℕ) : toQuad (x ^ n) = toQuad x ^ n :=
  Azurite.map_slidingWindowPow toQuad toQuad_one toQuad_mul x n

theorem toQuad_powAzNat (x : QuadT m u a) (n : AzNat) :
    toQuad (x.powAzNat n) = toQuad x ^ n.toNat :=
  Azurite.map_slidingWindowPowAzNat toQuad toQuad_one toQuad_mul x n

/-- **The coordinate map is injective** (for `m > 1`). -/
theorem toQuad_injective [Fact (1 < m.toNat)] :
    Function.Injective (toQuad : QuadT m u a → _) := by
  intro x y h
  obtain ⟨h0, h1⟩ := CL.quadElt_injective _ _ h
  exact QuadT.ext (toZMod_injective h0) (toZMod_injective h1)

/-- **(4.4)(c2) transported**: for prime `n` and a nonsquare discriminant,
`α^(n+1) = −a` in `QuadT`. -/
theorem alpha_pow_card_succ [Fact (1 < m.toNat)] (hn : m.toNat.Prime)
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a)) :
    (alpha : QuadT m u a) ^ (m.toNat + 1) = const (-a) := by
  apply toQuad_injective
  rw [toQuad_pow, toQuad_alpha, CL.root_pow_card_succ_eq_neg hn hns, toQuad_const, toZMod_neg,
    map_neg]

/-- **(4.4)(c2) transported, `AzNat` exponent.** -/
theorem alpha_powAzNat_card_succ [Fact (1 < m.toNat)] (hn : m.toNat.Prime)
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a)) :
    (alpha : QuadT m u a).powAzNat (m + 1) = const (-a) := by
  apply toQuad_injective
  rw [toQuad_powAzNat, toQuad_alpha, AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl,
    CL.root_pow_card_succ_eq_neg hn hns, toQuad_const, toZMod_neg, map_neg]

end QuadT

namespace NormOne

variable {u a : AzZMod m}

/-- **The shortcut-squaring power is the monoid power.** -/
theorem toQuad_pow (x : NormOne m u a) (n : ℕ) :
    QuadT.toQuad (pow x n).1 = QuadT.toQuad x.1 ^ n :=
  Azurite.map_slidingWindowPow (fun y : NormOne m u a => QuadT.toQuad y.1)
    QuadT.toQuad_one (fun y z => QuadT.toQuad_mul y.1 z.1) x n

theorem toQuad_powAzNat (x : NormOne m u a) (n : AzNat) :
    QuadT.toQuad (powAzNat x n).1 = QuadT.toQuad x.1 ^ n.toNat :=
  Azurite.map_slidingWindowPowAzNat (fun y : NormOne m u a => QuadT.toQuad y.1)
    QuadT.toQuad_one (fun y z => QuadT.toQuad_mul y.1 z.1) x n

theorem quadNorm_toQuad (x : NormOne m u a) :
    CL.quadNorm (toZMod u) (toZMod a) (toZMod x.1.x₀) (toZMod x.1.x₁) = 1 := by
  rw [← QuadT.toZMod_norm, x.2, toZMod_one]

/-- **Test (4.3) transported**: for prime `n` and a nonsquare discriminant,
every norm-one `x` has `x^(n+1) = 1` in `QuadT` — so a computed
`x^(n+1) ≠ 1` proves `n` composite. -/
theorem pow_card_succ_eq_one [Fact (1 < m.toNat)] (hn : m.toNat.Prime)
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a)) (x : NormOne m u a) :
    (pow x (m.toNat + 1)).1 = 1 := by
  apply QuadT.toQuad_injective
  rw [toQuad_pow, QuadT.toQuad_one]
  exact CL.quadNorm_one_pow_eq_one hn hns (quadNorm_toQuad x)

/-- **Test (4.3) transported, `AzNat` exponent**: `x^(n+1) = 1` for the `AzNat`
exponent `n + 1`. -/
theorem powAzNat_card_succ_eq_one [Fact (1 < m.toNat)] (hn : m.toNat.Prime)
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a)) (x : NormOne m u a) :
    (powAzNat x (m + 1)).1 = 1 := by
  apply QuadT.toQuad_injective
  rw [toQuad_powAzNat, QuadT.toQuad_one, AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl]
  exact CL.quadNorm_one_pow_eq_one hn hns (quadNorm_toQuad x)

/-- **Remark (4.10) transported**: for prime `n` and a nonsquare
discriminant, `normOneCandidate c` never fails. -/
theorem normOneCandidate_isSome [Fact (1 < m.toNat)] (hn : m.toNat.Prime)
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a)) (c : AzZMod m) :
    (QuadT.normOneCandidate c : Option (NormOne m u a)).isSome = true := by
  unfold QuadT.normOneCandidate
  have hunit : IsUnit (toZMod (c * (c + u) - a)) := by
    rw [toZMod_sub, toZMod_mul, toZMod_add]
    exact CL.norm_one_denominator_isUnit hn hns (toZMod c)
  rcases hd : tryInv (c * (c + u) - a) with _ | d
  · exact absurd hunit (tryInv_none hd)
  · have hd1 := tryInv_some hd
    have hd1' : toZMod d * (toZMod c * (toZMod c + toZMod u) - toZMod a) = 1 := by
      have := congrArg toZMod hd1
      simpa only [toZMod_mul, toZMod_sub, toZMod_add, toZMod_one] using this
    have hN : QuadT.norm (⟨(c * c + a) * d, (c + c + u) * d⟩ : QuadT m u a) = 1 := by
      apply toZMod_injective
      rw [QuadT.toZMod_norm, toZMod_one]
      simp only [toZMod_mul, toZMod_add]
      have h := CL.quadNorm_norm_one_candidate (toZMod u) (toZMod a) (toZMod c) (toZMod d) hd1'
      convert h using 2 <;> ring
    simp only [dite_eq_left hN]
    rfl

end NormOne

end AzZMod

end Azurite
