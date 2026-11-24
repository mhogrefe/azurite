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
* `addMixed`: the usual mixed addition (`Z₃ = ZH`).  On the curve (`OnCurve`) it is Mathlib's
  representative scaled by the unit `−Z` (`addMixed_eq_smul`), and it stays on the curve
  (`onCurve_addMixed`, `onCurve_dblShort`).
* `ladder a u v fuel k`: `k · (u, v)` by halving `k` with `dblShort` and `addMixed`.
  `ladder_chain`: if the final `Z` is a unit — it is the product of the `Z` of all the steps
  — the result is a `MulChain` for `k`.
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

/-! ### The mixed addition -/

/-- The Jacobian equation of `y² = x³ + ax + b`. -/
def OnCurve (a b : R) (P : R × R × R) : Prop :=
  P.2.1 ^ 2 = P.1 ^ 3 + a * P.1 * P.2.2 ^ 4 + b * P.2.2 ^ 6

/-- **The usual mixed addition** of the affine point `(u, v)`: `H = uZ² − X`, `r = vZ³ − Y`,
`X₃ = r² − H³ − 2XH²`, `Y₃ = r(XH² − X₃) − YH³`, `Z₃ = ZH`. -/
def addMixed (u v : R) (P : R × R × R) : R × R × R :=
  ((v * P.2.2 ^ 3 - P.2.1) ^ 2 - (u * P.2.2 ^ 2 - P.1) ^ 3
      - 2 * P.1 * (u * P.2.2 ^ 2 - P.1) ^ 2,
    (v * P.2.2 ^ 3 - P.2.1)
        * (P.1 * (u * P.2.2 ^ 2 - P.1) ^ 2
          - ((v * P.2.2 ^ 3 - P.2.1) ^ 2 - (u * P.2.2 ^ 2 - P.1) ^ 3
            - 2 * P.1 * (u * P.2.2 ^ 2 - P.1) ^ 2))
      - P.2.1 * (u * P.2.2 ^ 2 - P.1) ^ 3,
    P.2.2 * (u * P.2.2 ^ 2 - P.1))

/-- Doubling stays on the curve. -/
theorem onCurve_dblShort {a b : R} {P : R × R × R} (h : OnCurve a b P) :
    OnCurve a b (dblShort a P) := by
  unfold OnCurve at h ⊢
  simp only [dblShort]
  linear_combination (64 * P.2.1^6) * h

/-- The mixed addition stays on the curve. -/
theorem onCurve_addMixed {a b u v : R} (hE : v ^ 2 = u ^ 3 + a * u + b) {P : R × R × R}
    (h : OnCurve a b P) : OnCurve a b (addMixed u v P) := by
  have hb : b = v ^ 2 - u ^ 3 - a * u := by linear_combination -hE
  subst hb
  unfold OnCurve at h ⊢
  simp only [addMixed]
  linear_combination
    (- P.2.2^12 * u^3 * v^2 + 2 * P.2.2^12 * u^6 + 2 * P.2.1 * P.2.2^9 * u^3 * v
        - P.2.1^2 * P.2.2^6 * u^3 + 3 * P.1 * P.2.2^10 * u^2 * v^2 - 9 * P.1 * P.2.2^10 * u^5
        - 6 * P.1 * P.2.1 * P.2.2^7 * u^2 * v + 3 * P.1 * P.2.1^2 * P.2.2^4 * u^2
        - 3 * P.1^2 * P.2.2^8 * u * v^2 + 15 * P.1^2 * P.2.2^8 * u^4
        + 6 * P.1^2 * P.2.1 * P.2.2^5 * u * v - 3 * P.1^2 * P.2.1^2 * P.2.2^2 * u
        + P.1^3 * P.2.2^6 * v^2 - 10 * P.1^3 * P.2.2^6 * u^3 - 2 * P.1^3 * P.2.1 * P.2.2^3 * v
        + P.1^3 * P.2.1^2 + 3 * P.1^5 * P.2.2^2 * u - P.1^6) * h

/-- **On the curve the mixed addition is Mathlib's addition, scaled by the unit `−Z`.** -/
theorem addMixed_eq_smul {a b u v : R} (hE : v ^ 2 = u ^ 3 + a * u + b) {P : R × R × R}
    (h : OnCurve a b P) :
    toFin3 (addMixed u v P) = (-P.2.2) • toFin3 (addShort a b u v P) := by
  have hb : b = v ^ 2 - u ^ 3 - a * u := by linear_combination -hE
  subst hb
  unfold OnCurve at h
  ext i
  fin_cases i
  · simp only [toFin3, addMixed, addShort, smul_fin3, Fin.zero_eta, Matrix.cons_val_zero]
    linear_combination h
  · simp only [toFin3, addMixed, addShort, smul_fin3, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    linear_combination (P.2.1 - P.2.2 ^ 3 * v) * h
  · simp [toFin3, addMixed, addShort, addZShort, smul_fin3]
    ring

/-! ### The ladder -/

/-- **`k · (u, v)` by halving `k`**, with `dblShort` and `addMixed`; `none` if the fuel runs
out (or `k = 0`). -/
def ladder (a u v : R) : ℕ → ℕ → Option (R × R × R)
  | 0, _ => none
  | fuel + 1, k =>
    if k = 1 then some (u, v, 1)
    else
      (ladder a u v fuel (k / 2)).map fun T =>
        if k % 2 = 1 then addMixed u v (dblShort a T) else dblShort a T

/-- **The ladder is a checked chain** when the `Z`-coordinate of its result is a unit: that
coordinate is the product of the `Z`-coordinates of all the additions (and doublings). -/
theorem ladder_chain {a b u v : R} (hE : v ^ 2 = u ^ 3 + a * u + b) :
    ∀ (fuel k : ℕ) (V : R × R × R), ladder a u v fuel k = some V → IsUnit V.2.2 →
      MulChain (shortW a b).toJacobian ![u, v, 1] k (toFin3 V) ∧ OnCurve a b V
  | 0, _, _, h, _ => by simp [ladder] at h
  | fuel + 1, k, V, h, hV => by
    rw [ladder] at h
    by_cases hk : k = 1
    · rw [ite_eq_left hk, Option.some.injEq] at h
      subst h
      rw [hk]
      refine ⟨MulChain.base, ?_⟩
      unfold OnCurve
      linear_combination hE
    · rw [ite_eq_right hk] at h
      obtain ⟨T, hT, heq⟩ := Option.map_eq_some_iff.mp h
      by_cases hodd : k % 2 = 1
      · rw [ite_eq_left hodd] at heq
        subst heq
        have hV' : IsUnit ((dblShort a T).2.2 * (u * (dblShort a T).2.2 ^ 2 - (dblShort a T).1)) :=
          hV
        have hDz : IsUnit (dblShort a T).2.2 := isUnit_of_mul_isUnit_left hV'
        have hH : IsUnit (u * (dblShort a T).2.2 ^ 2 - (dblShort a T).1) :=
          isUnit_of_mul_isUnit_right hV'
        have hTz : IsUnit T.2.2 := by
          have : IsUnit (2 * T.2.1 * T.2.2) := hDz
          exact isUnit_of_mul_isUnit_right this
        obtain ⟨hc, hon⟩ := ladder_chain hE fuel (k / 2) T hT hTz
        have hD := hc.dbl
        rw [dblXYZ_toFin3] at hD
        have honD := onCurve_dblShort hon
        have hz : IsUnit (addZ (toFin3 (dblShort a T)) ![u, v, 1]) := by
          rw [addZ_toFin3]
          have : addZShort u (dblShort a T)
              = -(u * (dblShort a T).2.2 ^ 2 - (dblShort a T).1) := by
            unfold addZShort
            ring
          rw [this]
          exact hH.neg
        have hadd := (MulChain.add hD MulChain.base hz).scale (-(dblShort a T).2.2) hDz.neg
        rw [addXYZ_toFin3, ← addMixed_eq_smul hE honD] at hadd
        have hk' : 2 * (k / 2) + 1 = k := by omega
        rw [hk'] at hadd
        exact ⟨hadd, onCurve_addMixed hE honD⟩
      · rw [ite_eq_right hodd] at heq
        subst heq
        have hTz : IsUnit T.2.2 := by
          have : IsUnit (2 * T.2.1 * T.2.2) := hV
          exact isUnit_of_mul_isUnit_right this
        obtain ⟨hc, hon⟩ := ladder_chain hE fuel (k / 2) T hT hTz
        have hD := hc.dbl
        rw [dblXYZ_toFin3] at hD
        have hk' : 2 * (k / 2) = k := by omega
        rw [hk'] at hD
        exact ⟨hD, onCurve_dblShort hon⟩

/-- **What a checker tests**: the conditions on a curve, a point and the ladder that give a
step of a proof. -/
theorem ecppStep_of_ladder {N q : ℕ} (hN : 1 < N) (hN6 : N.Coprime 6)
    (hq1 : Nat.sqrt N + 1 < q) (hq2 : 4 * Nat.sqrt N < (q - Nat.sqrt N - 1) ^ 2)
    {a b u v : ZMod N} (hdisc : IsUnit (4 * a ^ 3 + 27 * b ^ 2))
    (hE : v ^ 2 = u ^ 3 + a * u + b) {fuel : ℕ} {V : ZMod N × ZMod N × ZMod N}
    (hl : ladder a u v fuel (q - 1) = some V) (hunit : IsUnit V.2.2)
    (hx : V.1 = u * V.2.2 ^ 2) (hy : V.2.1 = -v * V.2.2 ^ 3) : EcppStep N q := by
  refine ⟨hN, hN6, hq1, hq2, a, b, u, v, toFin3 V, hdisc, ?_,
    (ladder_chain hE fuel (q - 1) V hl hunit).1, hunit, hx, hy⟩
  rw [Affine.equation_iff]
  simp only [shortW]
  linear_combination hE

end Azurite.ECPP
