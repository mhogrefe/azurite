/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Basic
import Azurite.AzZMod.ToString
import Azurite.Algorithm.SlidingWindowPow
import Azurite.Algorithm.SlidingWindowPowAzNat
import Azurite.Algorithm.Equiv.SlidingWindowPowAzNat
import Azurite.AzNat.Equiv.Montgomery
import Azurite.AzZMod.Equiv.Basic
import Azurite.AzNat.Pow

/-!
## Exponentiation for `AzZMod`

`pow` via the generic **sliding-window** exponentiation `Azurite.slidingWindowPow`,
so `a ^ n mod m` costs `O(log n)` modular multiplications, each squaring using the
fast `Square` instance rather than a general multiply.  Mirrors `AzZModPow2.pow`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **Exponentiation** in `ℤ / m`: `a ^ n mod m`, by sliding-window
exponentiation over the `AzZMod` ring operations. -/
def pow [NeZero m.toNat] (a : AzZMod m) (n : ℕ) : AzZMod m :=
  Azurite.slidingWindowPow a n

/-- **Exponentiation with an `AzNat` exponent** in `ℤ / m`: the exponent is
read at the limb level (never through `AzNat.toNat`), so huge exponents —
Miller–Rabin's `d` with `n − 1 = 2^s·d`, Fermat/Euler exponents — stay
limb-level.  Mirrors `AzPolyMod.powAzNat`. -/
def powAzNat [NeZero m.toNat] (a : AzZMod m) (n : AzNat) : AzZMod m :=
  Azurite.slidingWindowPowAzNat a n

/-! ## Powers through Montgomery reduction

For an odd modulus and an exponent of at least `montPowMinBits` bits, the compiled `pow` and
`powAzNat` run in Montgomery form (`AzNat/Montgomery.lean`): one reduction costs about one
multiplication instead of a division.  The definitions above are unchanged; `pow_eq_powFast`
and `powAzNat_eq_powAzNatFast` are `@[csimp]` replacements, proven equal. -/

/-- A residue modulo `m` in Montgomery form (`x R mod m`, reduced). -/
structure Mont (m : AzNat) where
  /-- The Montgomery form, in `[0, m)`. -/
  val : AzNat
  /-- It is reduced. -/
  isLt : val.toNat < m.toNat

/-- The Montgomery data of an odd modulus `m`, passed to the operations of `Mont m`. -/
class MontData (m : AzNat) where
  /-- The precomputed data. -/
  ctx : AzNat.MontCtx
  /-- It is that of `m`. -/
  ctx_eq : ctx = AzNat.MontCtx.make m
  /-- `m` is odd. -/
  odd : Odd m.toNat

namespace Mont

variable [d : MontData m]

omit d in
@[ext] theorem ext {a b : Mont m} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : Mul (Mont m) :=
  ⟨fun a b => ⟨d.ctx.mul a.val b.val, by
    rw [d.ctx_eq]; exact (AzNat.MontCtx.mul_spec m 0 d.odd a.val b.val a.isLt b.isLt).1⟩⟩

instance : One (Mont m) :=
  ⟨⟨d.ctx.one, by rw [d.ctx_eq]; exact (AzNat.MontCtx.one_spec m 0 d.odd).1⟩⟩

instance : Azurite.Square (Mont m) where
  square a := ⟨d.ctx.sqr a.val, by
    rw [d.ctx_eq]; exact (AzNat.MontCtx.sqr_spec m 0 d.odd a.val a.isLt).1⟩
  square_eq a := by
    apply ext
    show d.ctx.redc (AzNat.square a.val) = d.ctx.redc (a.val * a.val)
    congr 1
    apply AzNat.toNat_injective
    rw [AzNat.toNat_square, AzNat.toNat_mul, pow_two]

omit d in
/-- An odd modulus is nonzero. -/
theorem neZero_of_odd (hm : Odd m.toNat) : NeZero m.toNat :=
  ⟨by rintro h; rw [h] at hm; simp at hm⟩

/-- Addition of Montgomery forms is the addition of residues. -/
instance : Add (Mont m) :=
  ⟨fun a b =>
    haveI := neZero_of_odd d.odd
    let s : AzZMod m := (⟨a.val, a.isLt⟩ : AzZMod m) + ⟨b.val, b.isLt⟩
    ⟨s.val, s.isLt⟩⟩

/-- Subtraction of Montgomery forms is the subtraction of residues. -/
instance : Sub (Mont m) :=
  ⟨fun a b =>
    haveI := neZero_of_odd d.odd
    let s : AzZMod m := (⟨a.val, a.isLt⟩ : AzZMod m) - ⟨b.val, b.isLt⟩
    ⟨s.val, s.isLt⟩⟩

/-- The residue a Montgomery form represents: `x R⁻¹`. -/
noncomputable def toZMod (x : Mont m) : ZMod m.toNat :=
  (x.val.toNat : ZMod m.toNat) * ((2 ^ (64 * (AzNat.MontCtx.make m).ne) : ℕ) : ZMod m.toNat)⁻¹

theorem toZMod_mul (a b : Mont m) : toZMod (a * b) = toZMod a * toZMod b := by
  show ((d.ctx.mul a.val b.val).toNat : ZMod m.toNat) * _ = _
  rw [d.ctx_eq, (AzNat.MontCtx.mul_spec m 0 d.odd a.val b.val a.isLt b.isLt).2]
  unfold toZMod
  ring

theorem toZMod_one : toZMod (1 : Mont m) = 1 := by
  show (d.ctx.one.toNat : ZMod m.toNat) * _ = _
  rw [d.ctx_eq, (AzNat.MontCtx.one_spec m 0 d.odd).2, AzNat.MontCtx.pow_mul_inv m 0 d.odd]

theorem toZMod_add (a b : Mont m) : toZMod (a + b) = toZMod a + toZMod b := by
  have := neZero_of_odd d.odd
  show AzZMod.toZMod ((⟨a.val, a.isLt⟩ : AzZMod m) + ⟨b.val, b.isLt⟩) * _ = _
  rw [AzZMod.toZMod_add, add_mul]
  rfl

theorem toZMod_sub (a b : Mont m) : toZMod (a - b) = toZMod a - toZMod b := by
  have := neZero_of_odd d.odd
  show AzZMod.toZMod ((⟨a.val, a.isLt⟩ : AzZMod m) - ⟨b.val, b.isLt⟩) * _ = _
  rw [AzZMod.toZMod_sub, sub_mul]
  rfl

theorem toZMod_square (a : Mont m) :
    toZMod (Azurite.Square.square a) = toZMod a * toZMod a := by
  rw [Azurite.Square.square_eq, toZMod_mul]

end Mont

/-- Into Montgomery form. -/
def toMont [d : MontData m] (a : AzZMod m) : Mont m :=
  ⟨d.ctx.toMont a.val, by
    rw [d.ctx_eq]; exact (AzNat.MontCtx.toMont_spec m 0 d.odd a.val a.isLt).1⟩

/-- Out of Montgomery form. -/
def ofMont [d : MontData m] (x : Mont m) : AzZMod m :=
  ⟨d.ctx.fromMont x.val, by
    rw [d.ctx_eq]; exact (AzNat.MontCtx.fromMont_spec m 0 d.odd x.val x.isLt).1⟩

theorem Mont.toZMod_toMont [d : MontData m] (a : AzZMod m) :
    Mont.toZMod (toMont a) = AzZMod.toZMod a := by
  show ((d.ctx.toMont a.val).toNat : ZMod m.toNat) * _ = _
  rw [d.ctx_eq, (AzNat.MontCtx.toMont_spec m 0 d.odd a.val a.isLt).2, mul_assoc,
    AzNat.MontCtx.pow_mul_inv m 0 d.odd, mul_one]
  rfl

theorem toZMod_ofMont [d : MontData m] (x : Mont m) : toZMod (ofMont x) = Mont.toZMod x := by
  show ((d.ctx.fromMont x.val).toNat : ZMod m.toNat) = _
  rw [d.ctx_eq]
  exact (AzNat.MontCtx.fromMont_spec m 0 d.odd x.val x.isLt).2

/-- `a ^ n` for an odd modulus, in Montgomery form. -/
def powAzNatMont (hm : Odd m.toNat) (a : AzZMod m) (n : AzNat) : AzZMod m :=
  let d : MontData m := ⟨AzNat.MontCtx.make m, rfl, hm⟩
  ofMont (d := d) (Azurite.slidingWindowPowAzNat (toMont (d := d) a) n)

/-- `a ^ n` for an odd modulus and a `ℕ` exponent, in Montgomery form. -/
def powMont (hm : Odd m.toNat) (a : AzZMod m) (n : ℕ) : AzZMod m :=
  let d : MontData m := ⟨AzNat.MontCtx.make m, rfl, hm⟩
  ofMont (d := d) (Azurite.slidingWindowPow (toMont (d := d) a) n)

theorem toZMod_powAzNatMont (hm : Odd m.toNat) (a : AzZMod m) (n : AzNat) :
    toZMod (powAzNatMont hm a n) = toZMod a ^ n.toNat := by
  unfold powAzNatMont
  let _ : MontData m := ⟨AzNat.MontCtx.make m, rfl, hm⟩
  rw [toZMod_ofMont, Azurite.map_slidingWindowPowAzNat Mont.toZMod Mont.toZMod_one
    Mont.toZMod_mul, Mont.toZMod_toMont]

theorem toZMod_powMont (hm : Odd m.toNat) (a : AzZMod m) (n : ℕ) :
    toZMod (powMont hm a n) = toZMod a ^ n := by
  unfold powMont
  let _ : MontData m := ⟨AzNat.MontCtx.make m, rfl, hm⟩
  rw [toZMod_ofMont, Azurite.map_slidingWindowPow Mont.toZMod Mont.toZMod_one
    Mont.toZMod_mul, Mont.toZMod_toMont]

/-- Exponents of at least this many bits use Montgomery form (below, setting it up costs more
than it saves). -/
def montPowMinBits : ℕ := 32

/-- `powAzNat` as compiled: Montgomery form for an odd modulus and a long exponent. -/
def powAzNatFast [NeZero m.toNat] (a : AzZMod m) (n : AzNat) : AzZMod m :=
  if h : m.isOdd = true ∧ montPowMinBits ≤ n.size then
    powAzNatMont ((AzNat.isOdd_iff m).mp h.1) a n
  else Azurite.slidingWindowPowAzNat a n

/-- `pow` as compiled: Montgomery form for an odd modulus and a long exponent. -/
def powFast [NeZero m.toNat] (a : AzZMod m) (n : ℕ) : AzZMod m :=
  if h : m.isOdd = true ∧ 2 ^ montPowMinBits ≤ n then
    powMont ((AzNat.isOdd_iff m).mp h.1) a n
  else Azurite.slidingWindowPow a n

@[csimp] theorem powAzNat_eq_powAzNatFast : @powAzNat = @powAzNatFast := by
  funext m _ a n
  unfold powAzNatFast powAzNat
  split
  · apply toZMod_injective
    rw [toZMod_powAzNatMont,
      Azurite.map_slidingWindowPowAzNat toZMod toZMod_one toZMod_mul]
  · rfl

@[csimp] theorem pow_eq_powFast : @pow = @powFast := by
  funext m _ a n
  unfold powFast pow
  split
  · apply toZMod_injective
    rw [toZMod_powMont, Azurite.map_slidingWindowPow toZMod toZMod_one toZMod_mul]
  · rfl

end Azurite.AzZMod

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

-- `3^4 = 81 ≡ 4 (mod 7)`, `2^10 = 1024 ≡ 24 (mod 1000)`, `7^0 = 1`.
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 7) 3).pow 4) == "4"
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 2).pow 10) == "24"
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 7).pow 0) == "1"
-- `123^5 mod 1000`: `123^5 = 28153056843`, `≡ 843`.
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 123).pow 5) == "843"

-- Montgomery form (odd modulus, long exponent) against the plain sliding window.
#guard (List.range 40).all fun i =>
  let m := AzNat.pow (AzNat.ofNat 3) (20 + 13 * i) + AzNat.ofNat (2 * i)
  if h : m.toNat ≠ 0 then
    haveI : NeZero m.toNat := ⟨h⟩
    let a := AzZMod.ofAzNat m (AzNat.pow (AzNat.ofNat 7) (11 * i + 5))
    let e := AzNat.pow (AzNat.ofNat 5) (17 + i)
    AzZMod.powAzNatFast a e == Azurite.slidingWindowPowAzNat a e
      && AzZMod.powFast a (2 ^ 40 + 12345 * i) == Azurite.slidingWindowPow a (2 ^ 40 + 12345 * i)
  else false

end Tests
