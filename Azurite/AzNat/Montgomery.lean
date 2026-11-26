/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Add
import Azurite.AzNat.Compare
import Azurite.AzNat.Div
import Azurite.AzNat.Mul
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.Square
import Azurite.AzNat.Sub
import Azurite.UInt64.MulAddWithCarry

/-!
# Montgomery reduction on `AzNat` limbs

Reduction modulo an odd `m` without division (P. L. Montgomery, *Modular multiplication without
trial division*, Math. Comp. 44 (1985)).  With `R = 2 ^ (64 ne)` (`ne` the limb count of `m`
rounded up to an even number), `redc t = t R⁻¹ mod m` for `t < m R`, at the cost of about one
multiplication: `ne / 2` passes of the fused two-row multiply-accumulate `mulAdd2Limbs`, each
clearing two limbs.  The arithmetic behind it is in `Montgomery/Theory.lean`; the proofs about
the functions here are in `Equiv/Montgomery.lean`.

* `montNegInv n₀`: `−n₀⁻¹ mod 2^64` for odd `n₀`.
* `redcLimbs`: the reduction on a `2 ne + 1`-limb buffer, in place.
* `MontCtx`: the precomputed data of a modulus (`MontCtx.make`), with `redc`, `mul`, `sqr`,
  `toMont` (`a ↦ a R mod m`) and `fromMont` (`a ↦ a R⁻¹ mod m`).
-/

namespace Azurite.AzNat

/-- `−n₀⁻¹ mod 2^64` for odd `n₀`, by Newton steps `x ↦ x (2 − n₀ x)` from the seed `n₀`
(correct to two bits, then 4, 8, 16, 32, 64). -/
def montNegInv (n₀ : UInt64) : UInt64 :=
  let x := n₀
  let x := x * (2 - n₀ * x)
  let x := x * (2 - n₀ * x)
  let x := x * (2 - n₀ * x)
  let x := x * (2 - n₀ * x)
  let x := x * (2 - n₀ * x)
  0 - x

/-- One step of the reduction: chooses two quotient limbs from `a[i]`, `a[i + 1]` and adds
`(q₀ + q₁ 2^64) N 2^(64 i)` into the buffer `a` (of `2 ne + 1` limbs), which clears those two
limbs. -/
def redcStep (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64) (i : Nat)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) (hi : i + 2 ≤ ne) : Array UInt64 :=
  let t₀ := a[i]
  let t₁ := a[i + 1]
  let q₀ := t₀ * ninv
  let m₀ := UInt64.mulAddWithCarry N[0] q₀ t₀ 0
  let m₁ := UInt64.mulAddWithCarry N[1] q₀ t₁ m₀.1
  let q₁ := m₁.2 * ninv
  let r := mulAdd2Limbs N 0 ne i q₀ q₁ a (by omega) (by omega)
  have h₁ : r.1.size = a.size := mulAdd2Limbs_size _ _ _ _ _ _ _ _ _
  let s := addLimb r.1 (i + ne) (2 * ne + 1) r.2.1 (by omega) (by omega)
  have h₂ : s.1.size = a.size := by rw [addLimb_size, h₁]
  (addLimb s.1 (i + ne + 1) (2 * ne + 1) r.2.2 (by omega) (by omega)).1

/-- Size preservation of `redcStep`. -/
theorem redcStep_size (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64) (i : Nat)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) (hi : i + 2 ≤ ne) :
    (redcStep N ne ninv a i hN ha hi).size = a.size := by
  unfold redcStep
  simp only
  rw [addLimb_size, addLimb_size, mulAdd2Limbs_size]

/-- The steps of the reduction from limb `i` on, two limbs at a time. -/
def redcLoop (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64) (i : Nat)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) : Array UInt64 :=
  if hi : i + 2 ≤ ne then
    redcLoop N ne ninv (redcStep N ne ninv a i hN ha hi) (i + 2) hN
      (by rw [redcStep_size]; exact ha)
  else a
  termination_by ne - i

/-- Size preservation of `redcLoop`. -/
theorem redcLoop_size (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64) (i : Nat)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) :
    (redcLoop N ne ninv a i hN ha).size = a.size := by
  induction h : ne - i using Nat.strong_induction_on generalizing a i with
  | _ k ih =>
    rw [redcLoop]
    split
    · rw [ih (ne - (i + 2)) (by omega) _ _ _ rfl, redcStep_size]
    · rfl

/-- **Montgomery reduction on limbs.**  `a` is a buffer of `2 ne + 1` limbs holding `T`, `N`
the `ne` limbs of the modulus (`ne` even, at least 2), `ninv = montNegInv N[0]`.  On return the
limbs `a[ne : 2 ne)` hold `T R⁻¹ mod N` (for `T < N R`, `R = 2 ^ (64 ne)`). -/
def redcLimbs (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) : Array UInt64 :=
  let b := redcLoop N ne ninv a 0 hN ha
  have hb : b.size = 2 * ne + 1 := by rw [redcLoop_size]; exact ha
  if b[2 * ne] ≠ 0 ∨ compareLimbs b N ne 0 ne (by omega) (by omega) ≠ Ordering.lt then
    (subSameLengthLimbs b N ne 0 ne (by omega) (by omega)).1
  else b

/-- Size preservation of `redcLimbs`. -/
theorem redcLimbs_size (N : Array UInt64) (ne : Nat) (ninv : UInt64) (a : Array UInt64)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) :
    (redcLimbs N ne ninv a hN ha).size = a.size := by
  unfold redcLimbs
  simp only
  split
  · rw [subSameLengthLimbs_size, redcLoop_size]
  · rw [redcLoop_size]

/-- **The precomputed data of an odd modulus** for Montgomery reduction. -/
structure MontCtx where
  /-- The modulus. -/
  m : AzNat
  /-- Its limb count, rounded up to an even number (at least 2); `R = 2 ^ (64 ne)`. -/
  ne : Nat
  /-- The limbs of the modulus, zero-padded to `ne`. -/
  limbs : Array UInt64
  /-- `−m⁻¹ mod 2^64`. -/
  ninv : UInt64
  /-- `R mod m`, the Montgomery form of 1. -/
  one : AzNat
  /-- `R² mod m`, the factor that converts into Montgomery form. -/
  r2 : AzNat
  /-- The padded limbs have length `ne`. -/
  size_limbs : limbs.size = ne
  /-- There are at least two limbs. -/
  two_le : 2 ≤ ne

/-- The Montgomery data of `m` (meaningful for odd `m`), with `extra` more limbs than `m` has
(so that `R ≥ 2 ^ (64 extra) m`: `redc` then accepts sums of that many products of residues).
Costs two divisions by `m`. -/
def MontCtx.make (m : AzNat) (extra : Nat := 0) : MontCtx :=
  let n := m.limbs.size + extra
  let ne := max 2 (n + n % 2)
  let pad : Array UInt64 := m.limbs ++ Array.replicate (ne - m.limbs.size) 0
  have hs : pad.size = ne := by
    simp only [pad, Array.size_append, Array.size_replicate]
    omega
  { m := m
    ne := ne
    limbs := pad
    ninv := montNegInv (pad[0]'(by omega))
    one := ((1 : AzNat) <<< (64 * ne)) % m
    r2 := ((1 : AzNat) <<< (128 * ne)) % m
    size_limbs := hs
    two_le := by omega }

/-- **Montgomery reduction:** `t R⁻¹ mod m` for `t < m R`. -/
def MontCtx.redc (c : MontCtx) (t : AzNat) : AzNat :=
  if h : t.limbs.size ≤ 2 * c.ne + 1 then
    let a : Array UInt64 := t.limbs ++ Array.replicate (2 * c.ne + 1 - t.limbs.size) 0
    have ha : a.size = 2 * c.ne + 1 := by
      simp only [a, Array.size_append, Array.size_replicate]
      omega
    ofLimbs ((redcLimbs c.limbs c.ne c.ninv a c.size_limbs ha).extract c.ne (2 * c.ne))
  else 0

/-- Montgomery product: `a b R⁻¹ mod m` (for `a, b < m`).  On Montgomery forms this is the
Montgomery form of the product. -/
def MontCtx.mul (c : MontCtx) (a b : AzNat) : AzNat := c.redc (a * b)

/-- Montgomery square: `a² R⁻¹ mod m` (for `a < m`). -/
def MontCtx.sqr (c : MontCtx) (a : AzNat) : AzNat := c.redc (square a)

/-- Into Montgomery form: `a R mod m` (for `a < m`). -/
def MontCtx.toMont (c : MontCtx) (a : AzNat) : AzNat := c.redc (a * c.r2)

/-- Out of Montgomery form: `a R⁻¹ mod m` (for `a < m`). -/
def MontCtx.fromMont (c : MontCtx) (a : AzNat) : AzNat := c.redc a

end Azurite.AzNat
