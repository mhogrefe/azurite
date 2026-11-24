/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.Criterion

/-!
# The scalar multiplication of the certificate, as a specification

On Mathlib's objects only (no `Az*` type here: see `docs/ecpp_plan.md`); the computable
arithmetic on `AzZMod` (`ECPP/Curve.lean`) is proven equal to the functions of this file.

For the curve `y² = x³ + ax + b` over a commutative ring and Jacobian triples `(X, Y, Z)`:

* `dblShort`, `addShort`, `addZShort`: Mathlib's `dblXYZ`, and `addXYZ`, `addZ` with a second
  point `(u, v, 1)`, as explicit expressions (`dblXYZ_toFin3`, `addXYZ_toFin3`, `addZ_toFin3`).
  The doubling is the usual `M = 3X² + aZ⁴`, `S = 4XY²`, `X₃ = M² − 2S`,
  `Y₃ = M(S − X₃) − 8Y⁴`, `Z₃ = 2YZ`.  The addition is Mathlib's representative with
  `Z₃ = X − uZ²`, a polynomial in the coordinates; it differs from the usual mixed addition by
  a scaling that is a polynomial identity only on the curve.
* `ladder a b u v fuel k`: `k · (u, v)` by halving `k`, with the product `acc` of the
  `Z`-coordinates of the additions.  `ladder_chain`: if `acc` is a unit, the result is a
  `MulChain` for `k`.
* `ecppStep_of_ladder`: the conditions a checker tests, giving `EcppStep N q`.
-/

namespace Azurite.ECPP

open WeierstrassCurve WeierstrassCurve.Jacobian

variable {R : Type*} [CommRing R]

/-- A triple as a point representative. -/
def toFin3 (P : R × R × R) : Fin 3 → R := ![P.1, P.2.1, P.2.2]

/-- Doubling on `y² = x³ + ax + b` in Jacobian coordinates. -/
def dblShort (a : R) (P : R × R × R) : R × R × R :=
  ((3 * P.1 ^ 2 + a * P.2.2 ^ 4) ^ 2 - 8 * P.1 * P.2.1 ^ 2,
    (3 * P.1 ^ 2 + a * P.2.2 ^ 4)
        * (4 * P.1 * P.2.1 ^ 2 - ((3 * P.1 ^ 2 + a * P.2.2 ^ 4) ^ 2 - 8 * P.1 * P.2.1 ^ 2))
      - 8 * P.2.1 ^ 4,
    2 * P.2.1 * P.2.2)

/-- The `Z`-coordinate of `P + (u, v, 1)`: `X − uZ²`. -/
def addZShort (u : R) (P : R × R × R) : R := P.1 - u * P.2.2 ^ 2

/-- Addition of `(u, v, 1)` on `y² = x³ + ax + b` in Jacobian coordinates (Mathlib's
representative). -/
def addShort (a b u v : R) (P : R × R × R) : R × R × R :=
  (P.1 * u ^ 2 * P.2.2 ^ 2 - 2 * P.2.1 * v * P.2.2 + P.1 ^ 2 * u + a * u * P.2.2 ^ 4
      + a * P.1 * P.2.2 ^ 2 + 2 * b * P.2.2 ^ 4,
    -(-P.2.1 * u ^ 3 * P.2.2 ^ 3 + 2 * P.2.1 * v ^ 2 * P.2.2 ^ 3
      - 3 * P.1 ^ 2 * u * v * P.2.2 ^ 2 + 3 * P.1 * P.2.1 * u ^ 2 * P.2.2 + P.1 ^ 3 * v
      - 2 * P.2.1 ^ 2 * v - a * u * v * P.2.2 ^ 6 - a * P.1 * v * P.2.2 ^ 4
      + a * P.2.1 * u * P.2.2 ^ 3 + a * P.1 * P.2.1 * P.2.2 - 2 * b * v * P.2.2 ^ 6
      + 2 * b * P.2.1 * P.2.2 ^ 3),
    addZShort u P)

theorem dblXYZ_toFin3 (a b : R) (P : R × R × R) :
    (shortW a b).toJacobian.dblXYZ (toFin3 P) = toFin3 (dblShort a P) := by
  ext i
  fin_cases i <;>
    simp [toFin3, dblShort, dblXYZ, dblX, dblY, negDblY, dblZ, dblU_eq, negY, shortW] <;> ring

theorem addZ_toFin3 (u v : R) (P : R × R × R) :
    addZ (toFin3 P) ![u, v, 1] = addZShort u P := by
  simp [toFin3, addZShort, addZ]

theorem addXYZ_toFin3 (a b u v : R) (P : R × R × R) :
    (shortW a b).toJacobian.addXYZ (toFin3 P) ![u, v, 1] = toFin3 (addShort a b u v P) := by
  ext i
  fin_cases i <;>
    simp [toFin3, addShort, addZShort, addXYZ, addX, addY, negAddY, addZ, negY, shortW]

/-- **`k · (u, v)` by halving `k`**, with the product of the `Z`-coordinates of the
additions; `none` if the fuel runs out (or `k = 0`). -/
def ladder (a b u v : R) : ℕ → ℕ → Option ((R × R × R) × R)
  | 0, _ => none
  | fuel + 1, k =>
    if k = 1 then some ((u, v, 1), 1)
    else
      (ladder a b u v fuel (k / 2)).map fun s =>
        if k % 2 = 1 then
          (addShort a b u v (dblShort a s.1), s.2 * addZShort u (dblShort a s.1))
        else (dblShort a s.1, s.2)

/-- **The ladder is a checked chain** when the accumulated product is a unit. -/
theorem ladder_chain (a b u v : R) : ∀ (fuel k : ℕ) (V : R × R × R) (acc : R),
    ladder a b u v fuel k = some (V, acc) → IsUnit acc →
    MulChain (shortW a b).toJacobian ![u, v, 1] k (toFin3 V)
  | 0, _, _, _, h, _ => by simp [ladder] at h
  | fuel + 1, k, V, acc, h, hacc => by
    rw [ladder] at h
    by_cases hk : k = 1
    · rw [ite_eq_left hk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [hk]
      exact MulChain.base
    · rw [ite_eq_right hk] at h
      obtain ⟨s, hs, heq⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨T, c⟩ := s
      by_cases hodd : k % 2 = 1
      · rw [ite_eq_left hodd, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hc : IsUnit c := isUnit_of_mul_isUnit_left hacc
        have hz : IsUnit (addZShort u (dblShort a T)) := isUnit_of_mul_isUnit_right hacc
        have hT := (ladder_chain a b u v fuel (k / 2) T c hs hc).dbl
        rw [dblXYZ_toFin3] at hT
        have hadd := MulChain.add hT MulChain.base (by rw [addZ_toFin3]; exact hz)
        rw [addXYZ_toFin3] at hadd
        have hk' : 2 * (k / 2) + 1 = k := by omega
        rwa [hk'] at hadd
      · rw [ite_eq_right hodd, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hT := (ladder_chain a b u v fuel (k / 2) T c hs hacc).dbl
        rw [dblXYZ_toFin3] at hT
        have hk' : 2 * (k / 2) = k := by omega
        rwa [hk'] at hT

/-- **What a checker tests**: the conditions on a curve, a point and the ladder that give a
step of a proof. -/
theorem ecppStep_of_ladder {N q : ℕ} (hN : 1 < N) (hN6 : N.Coprime 6)
    (hq1 : Nat.sqrt N + 1 < q) (hq2 : 4 * Nat.sqrt N < (q - Nat.sqrt N - 1) ^ 2)
    {a b u v : ZMod N} (hdisc : IsUnit (4 * a ^ 3 + 27 * b ^ 2))
    (hE : v ^ 2 = u ^ 3 + a * u + b) {fuel : ℕ} {V : ZMod N × ZMod N × ZMod N} {acc : ZMod N}
    (hl : ladder a b u v fuel (q - 1) = some (V, acc)) (hunit : IsUnit (acc * V.2.2))
    (hx : V.1 = u * V.2.2 ^ 2) (hy : V.2.1 = -v * V.2.2 ^ 3) : EcppStep N q := by
  refine ⟨hN, hN6, hq1, hq2, a, b, u, v, toFin3 V, hdisc, ?_,
    ladder_chain a b u v fuel (q - 1) V acc hl (isUnit_of_mul_isUnit_left hunit),
    isUnit_of_mul_isUnit_right hunit, hx, hy⟩
  rw [Affine.equation_iff]
  simp only [shortW]
  linear_combination hE

end Azurite.ECPP
