/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Correctness of the computable Algorithm 4.3.2
  (`Azurite.AzPolynomial.gcdOrFactor`), by transport to the proven
  reference implementation `Azurite.CP.gcdOrFactor`.

  The transport is `toZModPoly : AzPolynomial (AzZMod m) →
  Polynomial (ZMod m.toNat)` — `toPoly` followed by the coefficient
  ring isomorphism `AzZMod.toZModRingHom`.  The bridge
  (`map_gcdOrFactor`) is a fuel induction: at each Euclidean step the
  branch conditions line up (`f = 0` transports along the injections;
  the `AzInt.egcd` gcd equals `Nat.gcd` of the transported leading
  coefficient by `egcd_gcd`), the Bézout coefficient reduces to
  `Ring.inverse` of the transported leading coefficient (uniqueness
  of inverses), and `modByMonic` transports to `%ₘ` by
  `toPoly_modByMonic` plus `Polynomial.map_modByMonic`.  Fuel
  sufficiency: each step strictly shrinks the dense size of the first
  argument (`modByMonic_coeffs_size_lt`; unit scaling never grows it,
  `size_normalize_le`), so `f.coeffs.size + 1` steps are enough.

  The reference specification then transfers verbatim:
  `gcdOrFactor_factor` (a factor verdict is a nontrivial divisor of
  `m`), `gcdOrFactor_gcd` (a gcd verdict is monic and generates the
  pair ideal), `isCoprime_iff_of_gcdOrFactor`, and
  `gcdOrFactor_ne_inl_of_prime` (over a prime modulus the algorithm
  never fails).
-/
import Azurite.AzPolynomial.GcdOrFactor
import Azurite.AzPolynomial.EqualDegreeSplitting
import Azurite.AzPolynomial.Equiv.DivModByMonic
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzZMod.Equiv.Inv
import Azurite.AzInt.Equiv.ExtendedGcd
import Azurite.CrandallPomerance.Chapter4.Algorithm_4_3_2

namespace Azurite.AzPolynomial

open Polynomial

variable {m : AzNat} [NeZero m.toNat]

/-- The transport `Z_m[x]` (limb level) `→ (ZMod m.toNat)[x]`:
`toPoly` followed by the coefficient isomorphism. -/
noncomputable def toZModPoly (f : AzPolynomial (AzZMod m)) :
    Polynomial (ZMod m.toNat) :=
  (AzPolynomial.toPoly f).map AzZMod.toZModRingHom

private theorem toZModRingHom_injective :
    Function.Injective (AzZMod.toZModRingHom (m := m)) :=
  fun a b hab => AzZMod.toZMod_injective (by simpa using hab)

private theorem toZModPoly_eq_zero_iff {f : AzPolynomial (AzZMod m)} :
    toZModPoly f = 0 ↔ f = 0 := by
  unfold toZModPoly
  rw [Polynomial.map_eq_zero_iff toZModRingHom_injective, ← toPoly_zero,
    toPoly_inj]

theorem toZModPoly_injective :
    Function.Injective (toZModPoly (m := m)) := fun _ _ hab =>
  toPoly_inj.mp (Polynomial.map_injective _ toZModRingHom_injective hab)

@[simp] theorem toZModPoly_one :
    toZModPoly (1 : AzPolynomial (AzZMod m)) = 1 := by
  unfold toZModPoly
  rw [toPoly_one, Polynomial.map_one]

@[simp] theorem toZModPoly_mul (a b : AzPolynomial (AzZMod m)) :
    toZModPoly (a * b) = toZModPoly a * toZModPoly b := by
  unfold toZModPoly
  rw [toPoly_mul, Polynomial.map_mul]

@[simp] theorem toZModPoly_sub (a b : AzPolynomial (AzZMod m)) :
    toZModPoly (a - b) = toZModPoly a - toZModPoly b := by
  unfold toZModPoly
  rw [toPoly_sub, Polynomial.map_sub]

@[simp] theorem toZModPoly_X :
    toZModPoly (X : AzPolynomial (AzZMod m)) = Polynomial.X := by
  unfold toZModPoly
  rw [toPoly_X, Polynomial.map_X]

private theorem leadingCoeff_toZModPoly (f : AzPolynomial (AzZMod m)) :
    (toZModPoly f).leadingCoeff = AzZMod.toZMod f.leadingCoeff := by
  unfold toZModPoly
  rw [Polynomial.leadingCoeff_map_of_injective toZModRingHom_injective,
    leadingCoeff_toPoly, AzZMod.toZModRingHom_apply]

omit [NeZero m.toNat] in
private theorem val_toZMod (a : AzZMod m) :
    (AzZMod.toZMod a).val = a.val.toNat := by
  show ((a.val.toNat : ZMod m.toNat)).val = a.val.toNat
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]

/-- Monicity transports along `toZModPoly` (both ways, since the
coefficient map is injective). -/
theorem Monic_toZModPoly {f : AzPolynomial (AzZMod m)} :
    (toZModPoly f).Monic ↔ f.Monic := by
  unfold toZModPoly
  rw [Polynomial.Monic.def,
    Polynomial.leadingCoeff_map_of_injective toZModRingHom_injective,
    leadingCoeff_toPoly, AzZMod.toZModRingHom_apply]
  constructor
  · intro h1
    show f.leadingCoeff = 1
    apply AzZMod.toZMod_injective
    rw [h1, AzZMod.toZMod_one]
  · intro h1
    rw [h1.leadingCoeff_eq_one, AzZMod.toZMod_one]

/-- Uniqueness of inverses pins `Ring.inverse` to any witness. -/
private theorem ring_inverse_eq {M₀ : Type _} [CommMonoidWithZero M₀]
    {a b : M₀} (h : a * b = 1) : Ring.inverse a = b := by
  have hu : IsUnit a := IsUnit.of_mul_eq_one b h
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = Ring.inverse a * a * b := (mul_assoc _ _ _).symm
    _ = b := by rw [Ring.inverse_mul_cancel a hu, one_mul]

/-- Unit scaling never grows the dense coefficient size. -/
private theorem smul_coeffs_size_le (r : AzZMod m)
    (p : AzPolynomial (AzZMod m)) :
    (r • p).coeffs.size ≤ p.coeffs.size := by
  show (smul r p).coeffs.size ≤ p.coeffs.size
  unfold smul
  calc (normalize (p.coeffs.map (r • ·))).coeffs.size
      ≤ (p.coeffs.map (r • ·)).size := size_normalize_le _
    _ = p.coeffs.size := Array.size_map ..

/-- **The bridge, fuel-uniform**: with fuel above the dense size of
`f`, the computable algorithm transports to the reference
implementation. -/
theorem map_gcdOrFactorAux (fuel : ℕ) :
    ∀ f g : AzPolynomial (AzZMod m), f.coeffs.size < fuel →
      Sum.map AzNat.toNat toZModPoly (gcdOrFactorAux m fuel f g)
        = CP.gcdOrFactor m.toNat (toZModPoly f) (toZModPoly g) := by
  induction fuel with
  | zero => exact fun f g hfuel => absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro f g hfuel
    simp only [gcdOrFactorAux]
    rw [CP.gcdOrFactor]
    by_cases hf : f = 0
    · rw [ite_eq_left hf, dite_eq_left (toZModPoly_eq_zero_iff.mpr hf)]
      rfl
    · rw [ite_eq_right hf,
        dite_eq_right (fun h => hf (toZModPoly_eq_zero_iff.mp h))]
      have hgcd : Nat.gcd ((toZModPoly f).leadingCoeff).val m.toNat
          = ((AzInt.egcd f.leadingCoeff.val m).1).toNat := by
        rw [leadingCoeff_toZModPoly, val_toZMod, AzInt.egcd_gcd]
      by_cases hc : (AzInt.egcd f.leadingCoeff.val m).1 = 1
      · rw [ite_eq_left hc,
          dite_eq_left (show Nat.gcd ((toZModPoly f).leadingCoeff).val m.toNat
            = 1 by rw [hgcd, hc, AzNat.toNat_one])]
        -- the leading coefficient is nonzero, so `Z_m` is nontrivial
        have hlc0 : f.leadingCoeff ≠ 0 := by
          intro h0
          apply hf
          rw [← toPoly_inj, toPoly_zero]
          refine Polynomial.leadingCoeff_eq_zero.mp ?_
          rw [leadingCoeff_toPoly, h0]
        have : Nontrivial (AzZMod m) := nontrivial_of_ne _ _ hlc0
        -- the Bézout coefficient is the modular inverse
        have hcop : Nat.Coprime f.leadingCoeff.val.toNat m.toNat := by
          unfold Nat.Coprime
          rw [← AzInt.egcd_gcd, hc, AzNat.toNat_one]
        have hmul : f.leadingCoeff
            * AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1
            = 1 := AzZMod.mul_inv f.leadingCoeff hcop
        -- the normalized divisor is monic
        have hmono : (AzPolynomial.toPoly
            (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f)).Monic := by
          rw [toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.Monic.def,
            Polynomial.leadingCoeff_mul']
          · rw [Polynomial.leadingCoeff_C, leadingCoeff_toPoly, mul_comm]
            exact hmul
          · rw [Polynomial.leadingCoeff_C, leadingCoeff_toPoly, mul_comm,
              hmul]
            exact one_ne_zero
        -- transported divisor: `C (Ring.inverse lc) * toZModPoly f`
        have hf' : toZModPoly
            (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f)
            = Polynomial.C (Ring.inverse (toZModPoly f).leadingCoeff)
              * toZModPoly f := by
          rw [show Ring.inverse (toZModPoly f).leadingCoeff
              = AzZMod.toZMod
                (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1)
            from ring_inverse_eq (by
              rw [leadingCoeff_toZModPoly, ← AzZMod.toZMod_mul, hmul,
                AzZMod.toZMod_one])]
          unfold toZModPoly
          rw [toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
            Polynomial.map_C, AzZMod.toZModRingHom_apply]
        -- transported remainder: `%ₘ`
        have hr : toZModPoly (modByMonic g
            (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f))
            = toZModPoly g %ₘ toZModPoly
              (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f) := by
          unfold toZModPoly
          rw [toPoly_modByMonic hmono hmono.ne_zero,
            Polynomial.map_modByMonic _ hmono]
        -- fuel bookkeeping: the first argument strictly shrinks
        have hpos : 0 < (AzZMod.ofAzInt m
            (AzInt.egcd f.leadingCoeff.val m).2.1 • f).coeffs.size := by
          rcases Nat.eq_zero_or_pos (AzZMod.ofAzInt m
            (AzInt.egcd f.leadingCoeff.val m).2.1 • f).coeffs.size
            with h0 | hgt
          · exfalso
            apply hmono.ne_zero
            have hz : AzZMod.ofAzInt m
                (AzInt.egcd f.leadingCoeff.val m).2.1 • f = 0 := by
              apply AzPolynomial.ext
              rw [Array.size_eq_zero_iff.mp h0]
              rfl
            rw [hz, toPoly_zero]
          · exact hgt
        have hsz : (modByMonic g (AzZMod.ofAzInt m
            (AzInt.egcd f.leadingCoeff.val m).2.1 • f)).coeffs.size
            < fuel := by
          have h2 := modByMonic_coeffs_size_lt g _ hpos
          have h3 := smul_coeffs_size_le
            (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1) f
          omega
        rw [ih _ _ hsz, hr, hf']
      · rw [ite_eq_right hc,
          dite_eq_right (fun h1 => hc (AzNat.toNat_injective
            ((hgcd.symm.trans h1).trans AzNat.toNat_one.symm)))]
        show Sum.inl ((AzInt.egcd f.leadingCoeff.val m).1).toNat = _
        rw [← hgcd]

/-- **The bridge**: `gcdOrFactor` transports to the reference
implementation `CP.gcdOrFactor` under `toNat`/`toZModPoly`. -/
theorem map_gcdOrFactor (f g : AzPolynomial (AzZMod m)) :
    Sum.map AzNat.toNat toZModPoly (gcdOrFactor m f g)
      = CP.gcdOrFactor m.toNat (toZModPoly f) (toZModPoly g) :=
  map_gcdOrFactorAux _ f g (Nat.lt_succ_self _)

/-! ### The transported specification -/

/-- A factor verdict of the computable Algorithm 4.3.2 is a nontrivial
divisor of `m`. -/
theorem gcdOrFactor_factor (hm : 1 < m.toNat)
    {f g : AzPolynomial (AzZMod m)} {d : AzNat}
    (hd : gcdOrFactor m f g = .inl d) :
    d.toNat ∣ m.toNat ∧ 1 < d.toNat ∧ d.toNat < m.toNat := by
  have h := map_gcdOrFactor f g
  rw [hd] at h
  exact CP.gcdOrFactor_factor hm h.symm

/-- A gcd verdict of the computable Algorithm 4.3.2 is monic and
generates the pair ideal — it IS `gcd(f, g)` in the sense of
Definition 4.3.1, over `ZMod m.toNat` via `toZModPoly`. -/
theorem gcdOrFactor_gcd {f g : AzPolynomial (AzZMod m)} (hg : g.Monic)
    {h : AzPolynomial (AzZMod m)} (hh : gcdOrFactor m f g = .inr h) :
    h.Monic ∧ Ideal.span {toZModPoly f, toZModPoly g}
      = Ideal.span {toZModPoly h} := by
  have hb := map_gcdOrFactor f g
  rw [hh] at hb
  obtain ⟨h1, h2⟩ :=
    CP.gcdOrFactor_gcd (Monic_toZModPoly.mpr hg) hb.symm
  exact ⟨Monic_toZModPoly.mp h1, h2⟩

/-- `f` and `g` are coprime in `Z_m[x]` exactly when the computed
principal generator is a unit. -/
theorem isCoprime_iff_of_gcdOrFactor
    {f g h : AzPolynomial (AzZMod m)} (hg : g.Monic)
    (hh : gcdOrFactor m f g = .inr h) :
    IsCoprime (toZModPoly f) (toZModPoly g) ↔ IsUnit (toZModPoly h) := by
  have hb := map_gcdOrFactor f g
  rw [hh] at hb
  exact CP.isCoprime_iff_of_gcdOrFactor (Monic_toZModPoly.mpr hg) hb.symm

/-- Over a prime modulus the computable algorithm never fails: every
nonzero leading coefficient is invertible. -/
theorem gcdOrFactor_ne_inl_of_prime (hp : Nat.Prime m.toNat)
    (f g : AzPolynomial (AzZMod m)) (d : AzNat) :
    gcdOrFactor m f g ≠ .inl d := by
  intro hd
  have hb := map_gcdOrFactor f g
  rw [hd] at hb
  exact CP.gcdOrFactor_ne_inl_of_prime hp _ _ _ hb.symm

end Azurite.AzPolynomial
