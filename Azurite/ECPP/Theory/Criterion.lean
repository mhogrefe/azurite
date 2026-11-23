/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.Chain
import Azurite.ECPP.Theory.Hasse
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Field.ZMod

/-!
# The primality criterion of Goldwasser and Kilian

On Mathlib's objects only (no `Az*` type here: see `docs/ecpp_plan.md`).

`prime_of_point_of_order`: let `N > 1` be coprime to `6`, `E : y² = x³ + ax + b` a curve over
`ℤ/Nℤ` with `4a³ + 27b²` a unit, `(u, v)` a solution of its equation, and `q` a prime with
`q > (N^(1/4) + 1)²`, in the integer form

  `⌊√N⌋ + 1 < q` and `4 ⌊√N⌋ < (q − ⌊√N⌋ − 1)²`.

If `(q − 1) · (u, v)`, computed by the formulas with every addition checked (`MulChain`), is
`−(u, v)` with a unit `Z`-coordinate, then `N` is prime — given the Hasse bound.

*Proof.*  If not, `N` has a prime factor `p ≤ ⌊√N⌋`.  Modulo `p` the curve is elliptic and
`(u, v)` is a point `P ≠ O` of it with `(q − 1) P = −P`, so `P` has order `q` and
`q ≤ #E(𝔽_p) ≤ p + 1 + 2√p`, against the size of `q`.

This is the criterion of the certificate in the form "a point of order `q`": the usual
`m = #E`, cofactor and point `P₀` with `(m/q) P₀ = (u, v)` belong to the search, not to the
proof.  (Compare Morain 2007, Proposition 3.1, where `m = 2N′` and the conditions are stated
with division polynomials.)

`EcppStep N q` packages the hypotheses, and `EcppProof N` is a chain of steps down to a
number known to be prime: `EcppProof.prime`.
-/

namespace Azurite.ECPP

open WeierstrassCurve WeierstrassCurve.Jacobian

/-- The criterion for a general Weierstrass curve, given the bound on the number of points
of its reductions. -/
theorem prime_of_point_of_order_aux {N : ℕ} (hN : 1 < N)
    (W : WeierstrassCurve (ZMod N)) (hΔ : IsUnit W.Δ) {q : ℕ} (hq : q.Prime)
    (hq1 : Nat.sqrt N + 1 < q) (hq2 : 4 * Nat.sqrt N < (q - Nat.sqrt N - 1) ^ 2) {u v : ZMod N}
    (hU : W.toAffine.Equation u v) {V : Fin 3 → ZMod N}
    (hV : MulChain W.toJacobian ![u, v, 1] (q - 1) V) (hVz : IsUnit (V 2))
    (hx : V 0 = u * V 2 ^ 2) (hy : V 1 = (-v - W.a₁ * u - W.a₃) * V 2 ^ 3)
    (hbound : ∀ (p : ℕ) [Fact p.Prime], p ∣ N → ∀ f : ZMod N →+* ZMod p,
      ((Nat.card (W.map f).toAffine.Point : ℤ) - (p + 1)) ^ 2 ≤ 4 * p) : N.Prime := by
  by_contra hnp
  -- a prime factor `p ≤ ⌊√N⌋`
  have hp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hpN : N.minFac ∣ N := Nat.minFac_dvd N
  have hps : N.minFac ≤ Nat.sqrt N :=
    Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hnp)
  obtain ⟨p, hpdef⟩ : ∃ p, p = N.minFac := ⟨_, rfl⟩
  rw [← hpdef] at hp hpN hps
  have : Fact p.Prime := ⟨hp⟩
  -- the curve and the point modulo `p`
  obtain ⟨f⟩ : Nonempty (ZMod N →+* ZMod p) := ⟨ZMod.castHom hpN (ZMod p)⟩
  have : (W.map f).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map f⟩
  have hfU : f ∘ ![u, v, 1] = ![f u, f v, 1] := by
    rw [comp_fin3, map_one]
  have hns : (W.map f).toAffine.Nonsingular (f u) (f v) :=
    (Affine.equation_iff_nonsingular (W := (W.map f).toAffine)).mp (Affine.Equation.map f hU)
  have hŪ : (W.toJacobian.map f).Nonsingular (f ∘ ![u, v, 1]) := by
    rw [hfU]
    exact (nonsingular_some (f u) (f v)).mpr hns
  obtain ⟨hVn, hVa⟩ := hV.toAffine f hŪ
  -- the point `P` is not `O`
  obtain ⟨P, hPdef⟩ : ∃ P, P = Point.toAffine (W.toJacobian.map f) (f ∘ ![u, v, 1]) := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := by
    rw [hPdef, hfU, Point.toAffine_some (hfU ▸ hŪ)]
    exact Affine.Point.some_ne_zero _
  -- `(q − 1) P = −P`
  have hVz' : (f ∘ V) 2 ≠ 0 := (hVz.map f).ne_zero
  have hequiv : (f ∘ V) ≈ (W.toJacobian.map f).neg (f ∘ ![u, v, 1]) := by
    refine equiv_of_X_eq_of_Y_eq hVz' (by rw [neg_Z, hfU]; exact one_ne_zero) ?_ ?_
    · rw [neg_X, neg_Z, hfU]
      simp [hx]
    · rw [neg_Y, neg_Z, hfU, negY_eq]
      simp [hy]
  have hneg : (q - 1) • P = -P := by
    rw [hPdef, ← hVa, Point.toAffine_of_equiv hequiv, Point.toAffine_neg hŪ]
  have hqP : q • P = 0 := by
    have hq' : q = (q - 1) + 1 := by have := hq.pos; omega
    rw [hq', add_nsmul, one_nsmul, hneg, neg_add_cancel]
  -- the order of `P` is `q`, so `q ≤ #E(𝔽_p)`
  have : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf P = q := addOrderOf_eq_prime hqP hP0
  have hcard : q ≤ Nat.card (W.map f).toAffine.Point := hord ▸ addOrderOf_le_card
  -- against the Hasse bound
  have hhasse := hbound p hpN f
  obtain ⟨d, hd⟩ : ∃ d, q = Nat.sqrt N + 1 + d + 1 := ⟨q - Nat.sqrt N - 2, by omega⟩
  have hq2' : 4 * Nat.sqrt N < (d + 1) ^ 2 := by
    have : q - Nat.sqrt N - 1 = d + 1 := by omega
    rwa [this] at hq2
  have hq2z : (4 * (Nat.sqrt N : ℤ)) < ((d : ℤ) + 1) ^ 2 := by exact_mod_cast hq2'
  have hcz : ((Nat.sqrt N : ℤ) + 1 + d + 1) ≤ (Nat.card (W.map f).toAffine.Point : ℤ) := by
    have := hcard
    rw [hd] at this
    exact_mod_cast this
  have hpz : (p : ℤ) ≤ (Nat.sqrt N : ℤ) := by exact_mod_cast hps
  have hd0 : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have hlow : (d : ℤ) + 1 ≤ (Nat.card (W.map f).toAffine.Point : ℤ) - (p + 1) := by linarith
  have hsq : ((d : ℤ) + 1) ^ 2
      ≤ ((Nat.card (W.map f).toAffine.Point : ℤ) - (p + 1)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlow 2
  linarith

/-- **The Goldwasser–Kilian criterion**, with a point of order `q`, for a curve
`y² = x³ + ax + b` over `ℤ/Nℤ`, `N` coprime to `6`. -/
theorem prime_of_point_of_order (hH : HasseBound) {N : ℕ} (hN : 1 < N) (hN6 : N.Coprime 6)
    (a b : ZMod N) (hdisc : IsUnit (4 * a ^ 3 + 27 * b ^ 2)) {q : ℕ} (hq : q.Prime)
    (hq1 : Nat.sqrt N + 1 < q) (hq2 : 4 * Nat.sqrt N < (q - Nat.sqrt N - 1) ^ 2) {u v : ZMod N}
    (hU : (shortW a b).toAffine.Equation u v) {V : Fin 3 → ZMod N}
    (hV : MulChain (shortW a b).toJacobian ![u, v, 1] (q - 1) V) (hVz : IsUnit (V 2))
    (hx : V 0 = u * V 2 ^ 2) (hy : V 1 = -v * V 2 ^ 3) : N.Prime := by
  have h2 : Nat.Coprime 2 N := (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hN6).symm
  have h16 : IsUnit ((16 : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime 16 N).mpr (Nat.Coprime.pow_left 4 h2)
  have hΔ : IsUnit (shortW a b).Δ := by
    rw [shortW_Δ]
    have h16' : IsUnit (-16 : ZMod N) := by
      have : (-16 : ZMod N) = -((16 : ℕ) : ZMod N) := by norm_num
      rw [this]
      exact h16.neg
    exact h16'.mul hdisc
  refine prime_of_point_of_order_aux hN (shortW a b) hΔ hq hq1 hq2 hU hV hVz hx
    (by simpa [shortW] using hy) (fun p hp hpN f => ?_)
  have hp6 : p.Coprime 6 := Nat.Coprime.coprime_dvd_left hpN hN6
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2le := hp.out.two_le
    have hpr := hp.out
    interval_cases p
    · exact absurd hp6 (by decide)
    · exact absurd hp6 (by decide)
    · exact absurd hpr (by decide)
  rw [shortW_map]
  refine hH p hp5 (f a) (f b) ?_
  have := (hdisc.map f).ne_zero
  simpa [map_ofNat] using this

/-- **One step of a proof by elliptic curves**: `N > 1`, a prime-to-be `q` of the right size,
and a curve over `ℤ/Nℤ` with a point that the formulas show to be of order `q`. -/
def EcppStep (N q : ℕ) : Prop :=
  1 < N ∧ N.Coprime 6 ∧ Nat.sqrt N + 1 < q ∧ 4 * Nat.sqrt N < (q - Nat.sqrt N - 1) ^ 2 ∧
    ∃ (a b u v : ZMod N) (V : Fin 3 → ZMod N),
      IsUnit (4 * a ^ 3 + 27 * b ^ 2) ∧ (shortW a b).toAffine.Equation u v ∧
        MulChain (shortW a b).toJacobian ![u, v, 1] (q - 1) V ∧
        IsUnit (V 2) ∧ V 0 = u * V 2 ^ 2 ∧ V 1 = -v * V 2 ^ 3

/-- A step with a prime `q` proves `N` prime. -/
theorem EcppStep.prime (hH : HasseBound) {N q : ℕ} (h : EcppStep N q) (hq : q.Prime) :
    N.Prime := by
  obtain ⟨hN, hN6, hq1, hq2, a, b, u, v, V, hd, hU, hV, hVz, hx, hy⟩ := h
  exact prime_of_point_of_order hH hN hN6 a b hd hq hq1 hq2 hU hV hVz hx hy

/-- **A proof of primality by elliptic curves**: a chain of steps down to a number known to be
prime. -/
inductive EcppProof : ℕ → Prop
  | base {p : ℕ} : p.Prime → EcppProof p
  | step {N q : ℕ} : EcppStep N q → EcppProof q → EcppProof N

/-- **A proof by elliptic curves proves primality**, given the Hasse bound. -/
theorem EcppProof.prime (hH : HasseBound) {N : ℕ} (h : EcppProof N) : N.Prime := by
  induction h with
  | base hp => exact hp
  | step hs _ ih => exact hs.prime hH ih

end Azurite.ECPP
