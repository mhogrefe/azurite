/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The computable cyclotomic ring `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]`** — Phase A1
  of the APR-CL implementation plan (`docs/aprcl_implementation_plan.md`).

  The ring of §6 of the implementation paper is `(ℤ/nℤ)[x]/(Φ_{p^k})`,
  realized here as `AzPolyMod` over `AzZMod n` with the modulus
  `Φ_{p^k} = Σ_{i<p} x^(i·p^(k−1))` (`cyclotomicPrimePow`: the
  coefficient array of length `(p−1)p^(k−1) + 1` with `1` at the
  multiples of `p^(k−1)` and `0` elsewhere).  The modulus is monic for
  every `p, k`, so the proven `AzPolyMod` machinery — computable
  `CommRing`, sliding-window powers, `ringEquivAdjoinRoot` — applies
  unconditionally; `Equiv/Cyclotomic.lean` identifies the ring with
  `CycModN (p^k) n` and hence with the abstract model `CycM (p^k)`
  modulo `n` (`cycM_quot_equiv`).

  Operations of the 1987 algorithm on coefficient vectors, each with
  its specification proved in the Cohen–Lenstra arc:

  * `sigmaT x` — `σ_x : ζ ↦ ζ^x`, by evaluation (`(1.3)(i1a)`);
  * `sigmaInvT x` — `σ_x⁻¹` by the (6.1) coefficient algorithm
    (`CL.sigmaInvCoeff`, spec `CL.sigmaInv_spec`);
  * `findHT` — the (6.2) search for `h` with `a = ζ^h`, with the
    corrected `h = l + m` in the second case (`CL.findH`, spec
    `CL.findH_spec`);
  * `lambdaT β` — `λ : ζ ↦ β` into `ℤ/nℤ` by Horner evaluation
    (`(1.3)(i2a)`, spec `CL.lambdaHom_sum`).
-/
import Azurite.AzPolyMod.GaussTower
import Azurite.AzPolynomial.Eval
import Azurite.CohenLenstra.Impl_6_1

namespace Azurite

namespace AzPolynomial

variable (R : Type _) [Semiring R] [DecidableEq R] [Nontrivial R]

/-- **`Φ_{p^k}` as a coefficient array**: `Σ_{i<p} x^(i·p^(k−1))`, of
length `(p−1)p^(k−1) + 1`, with `1` exactly at the multiples of
`p^(k−1)`. -/
def cyclotomicPrimePow (p k : ℕ) : AzPolynomial R :=
  ⟨Array.ofFn (fun i : Fin ((p - 1) * p ^ (k - 1) + 1) =>
      if (i : ℕ) % p ^ (k - 1) = 0 then (1 : R) else 0), by
    intro h
    rw [Array.back?_eq_getElem?, Array.size_ofFn, Nat.add_sub_cancel,
      Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self _)] at h
    simp only [Nat.mul_mod_left, ite_true] at h
    exact one_ne_zero (α := R) (Option.some.inj h)⟩

omit [DecidableEq R] in
@[simp] theorem cyclotomicPrimePow_coeffs_size (p k : ℕ) :
    (cyclotomicPrimePow R p k).coeffs.size = (p - 1) * p ^ (k - 1) + 1 := by
  simp [cyclotomicPrimePow]

omit [DecidableEq R] in
theorem coeff_cyclotomicPrimePow (p k i : ℕ) :
    (cyclotomicPrimePow R p k).coeff i
      = if i ≤ (p - 1) * p ^ (k - 1) ∧ i % p ^ (k - 1) = 0 then (1 : R) else 0 := by
  unfold coeff cyclotomicPrimePow
  simp only [Array.getElem?_ofFn]
  by_cases hi : i < (p - 1) * p ^ (k - 1) + 1
  · rw [dite_eq_left hi]
    simp only [Option.getD_some]
    by_cases hm : i % p ^ (k - 1) = 0
    · rw [ite_eq_left hm, ite_eq_left ⟨by omega, hm⟩]
    · rw [ite_eq_right hm, ite_eq_right (fun h => hm h.2)]
  · rw [dite_eq_right hi]
    simp only [Option.getD_none]
    rw [ite_eq_right (fun h => hi (by omega))]

omit [DecidableEq R] in
theorem leadingCoeff_cyclotomicPrimePow (p k : ℕ) :
    (cyclotomicPrimePow R p k).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree, cyclotomicPrimePow_coeffs_size, Nat.add_sub_cancel,
    coeff_cyclotomicPrimePow]
  rw [ite_eq_left ⟨le_refl _, Nat.mul_mod_left _ _⟩]

omit [DecidableEq R] in
/-- `Φ_{p^k}` is monic (as a Mathlib polynomial) for every `p, k`. -/
theorem monic_toPoly_cyclotomicPrimePow (p k : ℕ) :
    (AzPolynomial.toPoly (cyclotomicPrimePow R p k)).Monic := by
  have h := leadingCoeff_toPoly (cyclotomicPrimePow R p k)
  rw [Polynomial.Monic, h]
  exact leadingCoeff_cyclotomicPrimePow R p k

instance factMonicCyclotomicPrimePow (p k : ℕ) :
    Fact (AzPolynomial.toPoly (cyclotomicPrimePow R p k)).Monic :=
  ⟨monic_toPoly_cyclotomicPrimePow R p k⟩

end AzPolynomial

namespace AzPolyMod

open _root_.Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R]

/-- `R[x]/(Φ_{p^k})` is nontrivial for `p > 1`. -/
instance instNontrivialCyclotomicPrimePow {p k : ℕ} [hp : Fact (1 < p)] :
    Nontrivial (AzPolyMod (cyclotomicPrimePow R p k)) := by
  refine ⟨⟨⟨#[(1 : R)], by simp⟩, Or.inl ?_⟩, 0, fun h => ?_⟩
  · rw [cyclotomicPrimePow_coeffs_size]
    have h1 := hp.out
    have h2 : 0 < p ^ (k - 1) := Nat.pow_pos (by omega)
    have h3 : 1 ≤ (p - 1) * p ^ (k - 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) h2.ne')
    have hsz : (#[(1 : R)] : Array R).size = 1 := rfl
    rw [hsz]
    omega
  · have hval := congrArg (fun a : AzPolyMod (cyclotomicPrimePow R p k) =>
      a.val.coeffs.size) h
    have h0 : (0 : AzPolyMod (cyclotomicPrimePow R p k)).val = 0 := rfl
    rw [h0] at hval
    simp at hval

/-- **An element from a coefficient function** on `{0, …, m−1}`
(normalized, then reduced). -/
def ofCoeffFn {f : AzPolynomial R} (m : ℕ) (c : ℕ → R) : AzPolyMod f :=
  ofPoly (normalize (Array.ofFn fun i : Fin m => c i))

/-! ### The cyclotomic ring over `ℤ/nℤ` -/

/-- **`CycT n p k = (ℤ/nℤ)[x]/(Φ_{p^k})`**, the computation ring of §6. -/
abbrev CycT (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)] :=
  AzPolyMod (cyclotomicPrimePow (AzZMod n) p k)

section CycT

variable (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)]

/-- `ζ_{p^k}`: the class of `x`. -/
def zetaT : CycT n p k := ofPoly AzPolynomial.X

variable {n p k}

/-- The `i`-th coordinate `a_i` of `a = Σ_{i<m} a_i ζ^i`. -/
def coeffT (a : CycT n p k) (i : ℕ) : AzZMod n := a.val.coeff i

/-- **`σ_x`** (`ζ ↦ ζ^x`): `Σ a_i ζ^i ↦ Σ a_i ζ^(xi)`, by evaluation. -/
def sigmaT (x : ℕ) (a : CycT n p k) : CycT n p k :=
  (List.range ((p - 1) * p ^ (k - 1))).foldl
    (fun acc i => acc + ofCoeff (coeffT a i) * zetaT n p k ^ (x * i)) 0

/-- **`σ_x⁻¹` by Algorithm (6.1)** (`CL.sigmaInvCoeff`): the output
coordinates are `b_t = a_{xt mod p^k} − a_{x(m + t mod p^(k−1)) mod p^k}`. -/
def sigmaInvT (x : ℕ) (a : CycT n p k) : CycT n p k :=
  ofCoeffFn ((p - 1) * p ^ (k - 1)) (CL.sigmaInvCoeff p k x (coeffT a))

/-- **Algorithm (6.2)**: `some h` with `a = ζ^h`, else `none`
(corrected second case, `h = l + m`). -/
def findHT (a : CycT n p k) : Option ℕ := CL.findH p k (coeffT a)

/-- **`λ : ζ ↦ β`** into `ℤ/nℤ`, by Horner evaluation of the coordinate
polynomial at `β` (`(1.3)(i2a)`). -/
def lambdaT (β : AzZMod n) (a : CycT n p k) : AzZMod n := a.val.eval β

end CycT

/-! ### Sanity guards (`n = 101`) -/

section Guards

instance : Fact (1 < (AzNat.ofNat 101).toNat) := ⟨by rw [AzNat.toNat_ofNat]; norm_num⟩

private abbrev n101 : AzNat := AzNat.ofNat 101

-- `ζ^(p^k) = 1` and `Φ_{p^k}(ζ) = 0` (the defining relation) for the table sizes
#guard (zetaT n101 3 2) ^ 9 = 1
#guard (zetaT n101 2 4) ^ 16 = 1
#guard (zetaT n101 11 1) ^ 11 = 1
#guard (zetaT n101 3 2) ^ 6 + (zetaT n101 3 2) ^ 3 + 1 = 0
#guard (zetaT n101 2 4) ^ 8 + 1 = 0
-- (6.2): `ζ^7` for `p^k = 9` lives in the second (corrected) case, `h = 1 + 6`
#guard findHT ((zetaT n101 3 2) ^ 7) = some 7
#guard findHT ((zetaT n101 3 2) ^ 4) = some 4
#guard findHT ((zetaT n101 3 2) ^ 4 + 1) = none
#guard findHT ((zetaT n101 2 4) ^ 13) = some 13
-- (6.1): `σ_x⁻¹ ∘ σ_x = id` on a generic element, `x` coprime to `p`
#guard let a : CycT n101 3 2 := (zetaT n101 3 2) ^ 5 + 3 * (zetaT n101 3 2) ^ 2 + 7
       sigmaInvT 2 (sigmaT 2 a) = a ∧ sigmaT 2 (sigmaInvT 2 a) = a
#guard let a : CycT n101 2 4 := 5 * (zetaT n101 2 4) ^ 7 + (zetaT n101 2 4) ^ 3 + 2
       sigmaInvT 3 (sigmaT 3 a) = a ∧ sigmaT 5 (sigmaInvT 5 a) = a
-- `σ_x(ζ) = ζ^x`, `σ_x⁻¹(ζ^x) = ζ`
#guard sigmaT 4 (zetaT n101 3 2) = (zetaT n101 3 2) ^ 4
#guard sigmaInvT 4 ((zetaT n101 3 2) ^ 4) = zetaT n101 3 2
-- `λ(ζ^2 + 3ζ + 5) = β^2 + 3β + 5` at `β = 10`
#guard lambdaT (10 : AzZMod n101) ((zetaT n101 3 2) ^ 2 + 3 * zetaT n101 3 2 + 5)
  = (10 : AzZMod n101) ^ 2 + 3 * 10 + 5

end Guards

end AzPolyMod

end Azurite
