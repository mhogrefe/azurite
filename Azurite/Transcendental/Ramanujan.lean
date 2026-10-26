/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Ramanujan
import Azurite.AzRat.Equiv.LogBase2

/-!
# Ramanujan's constant is not an integer, but within `10^(−12)` of one — by computation

`e^(π √163) = 262537412640768743.99999999999925…`.  This file proves
`262537412640768744 − 10^(−12) < e^(π √163) < 262537412640768744`, hence that the constant is
not an integer (`ramanujan_not_integer`), has floor `262537412640768743` (`floor_ramanujan`),
and is within `10^(−12)` of `262537412640768744 = 640320³ + 744` (`ramanujan_near_integer`).

**The numbers come from Azurite itself.**  The kernel evaluates `ramanujanPrecRound 110 .Floor`
and `ramanujanPrecRound 110 .Ceiling` (`decide +kernel`: the AGM bracket of `π`, the square root
of `163`, the `ln 2` reduction and the bit-burst `exp`, all on `UInt64` limbs), and the
specification `ramanujanPrecRound_eq_or` turns the two rounded floats into the real bounds
`⌊x⌋₁₁₀ ≤ x ≤ ⌈x⌉₁₁₀` (`roundVal_floor_err`, `roundVal_ceiling_err`).  The only remaining
arithmetic in the proof compares two rationals with 34-digit numerators, which stays within
two-word kernel `Nat` operations.  No `native_decide`, no big-operand `norm_num` certificates:
the trusted base is the kernel's `Nat` arithmetic on operands of at most a few words.

There is no transcendence shortcut here: "not an integer" is as hard as the enclosure (the
irrationality of `e^(π √163)` is Gelfond–Schneider, see the pending-irrationality ledger), while
"within `10^(−12)`" is the part that mathematics explains (`j((1 + √−163)/2) = −640320³` and the
`q`-expansion `j = 1/q + 744 + 196884 q + …`), which is far beyond this file.
-/

namespace Azurite

open Real AzFloat

/-- The data of a rounded float: the sign, numerator and denominator of its rational value. -/
def ratData (r : AzFloat × Ordering) : Option (Bool × ℕ × ℕ) :=
  r.1.toAzRat?.map fun q => (q.sign, q.num.toNat, q.den.toNat)

/-! ### The kernel computations -/

set_option maxRecDepth 100000 in
/-- `⌊e^(π √163)⌋₁₁₀ = 591181696869890130852706372286823 / 2^51`, computed by Azurite in the
kernel. -/
theorem ramanujan_floor_110 :
    ratData (ramanujanPrecRound 110 .Floor)
      = some (true, 591181696869890130852706372286823, 2251799813685248) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `⌈e^(π √163)⌉₁₁₀ = 1182363393739780261705412744573647 / 2^52`, computed by Azurite in the
kernel. -/
theorem ramanujan_ceiling_110 :
    ratData (ramanujanPrecRound 110 .Ceiling)
      = some (true, 1182363393739780261705412744573647, 4503599627370496) := by
  decide +kernel

/-! ### From the data to the real value -/

/-- The value of a rounded float with positive rational data `n / d`. -/
theorem toVal_of_ratData {r : AzFloat × Ordering} {n d : ℕ} (h : ratData r = some (true, n, d)) :
    r.1.toVal = some (((n : ℝ) / d : ℝ) : EReal) := by
  unfold ratData at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, hqd⟩ := h
  simp only [Prod.mk.injEq] at hqd
  obtain ⟨hs, hn, hd⟩ := hqd
  rw [toVal_of_toAzRat? _ _ hq, AzRat.toRat_cast_eq, hs, hn, hd]
  simp

theorem ramanujan_gt : (262537412640768744 : ℝ) - 1 / 10 ^ 12 < exp (π * √163) := by
  have hx : 0 ≤ exp (π * √163) := (exp_pos _).le
  have hval := toVal_of_ratData ramanujan_floor_110
  rcases ramanujanPrecRound_eq_or 110 .Floor with h | h
  · unfold liftVal₀ at h
    rw [h] at hval
    obtain ⟨r, hr, hfl⟩ := roundVal_floor_err 110 hx
    rw [hr, Option.some.injEq, EReal.coe_eq_coe_iff] at hval
    have hle := hfl.le
    rw [hval] at hle
    have hnum : (262537412640768744 : ℝ) - 1 / 10 ^ 12
        < (591181696869890130852706372286823 : ℝ) / 2251799813685248 := by norm_num
    linarith
  · rw [h] at hval
    simp at hval

theorem ramanujan_lt : exp (π * √163) < 262537412640768744 := by
  have hx : 0 ≤ exp (π * √163) := (exp_pos _).le
  have hval := toVal_of_ratData ramanujan_ceiling_110
  rcases ramanujanPrecRound_eq_or 110 .Ceiling with h | h
  · unfold liftVal₀ at h
    rw [h] at hval
    obtain ⟨r, hr, hc⟩ := roundVal_ceiling_err 110 hx
    rw [hr, Option.some.injEq, EReal.coe_eq_coe_iff] at hval
    have hge := hc.ge
    rw [hval] at hge
    have hnum : (1182363393739780261705412744573647 : ℝ) / 4503599627370496
        < 262537412640768744 := by norm_num
    linarith
  · rw [h] at hval
    simp at hval

/-! ### The consequences -/

/-- **Ramanujan's constant is within `10^(−12)` of the integer `640320³ + 744`.** -/
theorem ramanujan_near_integer : |exp (π * √163) - 262537412640768744| < 1 / 10 ^ 12 := by
  rw [abs_sub_lt_iff]
  constructor <;> linarith [ramanujan_gt, ramanujan_lt]

/-- `640320³ + 744 = 262537412640768744`. -/
theorem ramanujan_integer_eq : (640320 : ℤ) ^ 3 + 744 = 262537412640768744 := by norm_num

/-- **Ramanujan's constant is not an integer.** -/
theorem ramanujan_not_integer (n : ℤ) : exp (π * √163) ≠ n := by
  intro h
  have h1 := ramanujan_gt
  have h2 := ramanujan_lt
  rw [h] at h1 h2
  have h3 : (262537412640768743 : ℤ) < n := by
    have : (262537412640768743 : ℝ) < n := by linarith
    exact_mod_cast this
  have h4 : n < (262537412640768744 : ℤ) := by exact_mod_cast h2
  omega

/-- `⌊e^(π √163)⌋ = 262537412640768743`. -/
theorem floor_ramanujan : ⌊exp (π * √163)⌋ = 262537412640768743 := by
  rw [Int.floor_eq_iff]
  constructor
  · have := ramanujan_gt; push_cast; linarith
  · have := ramanujan_lt; push_cast; linarith

end Azurite
