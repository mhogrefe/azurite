/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The single-cyclotomic model `ℤ[ζ_m] = ℤ[x]/(Φ_m)` — the COMMON
  RING of the Theorem 4.4.6 assembly.  The per-`q` hypotheses of
  `theorem_4_4_6_composite` need one domain carrying primitive
  `p`-th roots for every prime `p ∣ q − 1` together with a primitive
  `q`-th root, with the integers faithful: `ℤ[ζ_(q−1)q]` — all the
  needed roots are powers of `ζ_m` for `m = (q−1)q`.

  Unlike the pair tower `CycPQ` of Definition 4.4.4 (kept for the
  checker's per-pair coefficientwise computations), the single
  extension needs NO embedding argument for domain-ness: `Φ_m` is
  irreducible over `ℤ`, so the quotient is a domain outright.  The
  power basis gives the free `ℤ`-structure, the content, and the
  faithfulness of the integers, exactly as in the tower model.

  * `isDomain_cycM` — `ℤ[ζ_m]` is an integral domain;
  * `cycMBasis`, `contentM`, `natCast_dvd_iff_dvd_contentM` — the
    power basis, the content, and congruence-is-coefficientwise;
  * `natCast_dvd_natCast_iff_cycM` — the integers are faithful;
  * `isPrimitiveRoot_zetaM` — the symbol is a genuine primitive
    `m`-th root of unity.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.AdjoinRoot

namespace Azurite

namespace CP

open Polynomial Module

/-- The symbolic model of `ℤ[ζ_m]`: adjoin a root of the `m`-th
cyclotomic polynomial. -/
abbrev CycM (m : ℕ) := AdjoinRoot (cyclotomic m ℤ)

/-- The symbol `ζ_m`. -/
noncomputable def zetaM (m : ℕ) : CycM m := AdjoinRoot.root _

/-- **The model is an integral domain**: `Φ_m` is irreducible over
`ℤ`, hence prime. -/
theorem isDomain_cycM {m : ℕ} (hm : 0 < m) : IsDomain (CycM m) :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (cyclotomic.irreducible hm))

section Basis

variable (m : ℕ)

/-- The power basis `1, ζ_m, …, ζ_m^(φ(m)−1)` of `ℤ[ζ_m]` over
`ℤ`. -/
noncomputable def cycMBasis : Basis (Fin m.totient) ℤ (CycM m) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic m ℤ)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic]))

/-- The basis vectors are the monomials `ζ_m^i`. -/
theorem cycMBasis_apply (i : Fin m.totient) :
    cycMBasis m i = zetaM m ^ (i : ℕ) := by
  rw [cycMBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

/-- The content of an element: the gcd of its coordinates. -/
noncomputable def contentM (α : CycM m) : ℕ :=
  Finset.univ.gcd fun i => ((cycMBasis m).repr α i).natAbs

/-- **Congruence mod `n` is coefficientwise** in `ℤ[ζ_m]`:
divisibility by `n` in the ring is divisibility of the content. -/
theorem natCast_dvd_iff_dvd_contentM (n : ℕ) (α : CycM m) :
    (n : CycM m) ∣ α ↔ n ∣ contentM m α := by
  constructor
  · rintro ⟨β, rfl⟩
    refine Finset.dvd_gcd fun i _ => ?_
    have hsmul : (n : CycM m) * β = (n : ℤ) • β := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [hsmul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul,
      Int.natAbs_natCast]
    exact Dvd.intro _ rfl
  · intro h
    have hall : ∀ i, (n : ℤ) ∣ (cycMBasis m).repr α i := by
      intro i
      have h1 : n ∣ ((cycMBasis m).repr α i).natAbs :=
        h.trans (Finset.gcd_dvd (Finset.mem_univ i))
      have h2 : ((n : ℤ)).natAbs ∣ ((cycMBasis m).repr α i).natAbs := by
        rwa [Int.natAbs_natCast]
      exact Int.natAbs_dvd_natAbs.mp h2
    refine ⟨∑ i : Fin m.totient,
      ((cycMBasis m).repr α i / n) • cycMBasis m i, ?_⟩
    conv_lhs => rw [← (cycMBasis m).sum_repr α]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hzs : (n : CycM m)
        * (((cycMBasis m).repr α i / n) • cycMBasis m i)
        = ((n : ℤ) * ((cycMBasis m).repr α i / n)) • cycMBasis m i := by
      simp only [← smul_smul, zsmul_eq_mul, Int.cast_natCast]
    rw [hzs, Int.mul_ediv_cancel' (hall i)]

variable {m}

/-- Nonzero integers stay nonzero in the model. -/
theorem natCast_ne_zero_cycM (hm : 0 < m) {n : ℕ} (hn : n ≠ 0) :
    (n : CycM m) ≠ 0 := by
  have hpos : 0 < m.totient := Nat.totient_pos.mpr hm
  have hone : (1 : CycM m) = cycMBasis m ⟨0, hpos⟩ := by
    rw [cycMBasis_apply]
    simp
  have hcast : (n : CycM m) = (n : ℤ) • cycMBasis m ⟨0, hpos⟩ := by
    rw [← hone, zsmul_eq_mul, mul_one]
    push_cast
    rfl
  intro h0
  have hrepr := congrArg (fun x => ((cycMBasis m).repr x) ⟨0, hpos⟩) h0
  simp only [hcast, map_smul, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero,
    Finsupp.coe_zero, Pi.zero_apply] at hrepr
  exact_mod_cast hn (by exact_mod_cast hrepr)

/-- **The integers are faithful in the model**: divisibility of
integer constants in `ℤ[ζ_m]` is ordinary divisibility. -/
theorem natCast_dvd_natCast_iff_cycM (hm : 0 < m) (n k : ℕ) :
    (n : CycM m) ∣ (k : CycM m) ↔ n ∣ k := by
  constructor
  · intro h
    have hpos : 0 < m.totient := Nat.totient_pos.mpr hm
    have hone : (1 : CycM m) = cycMBasis m ⟨0, hpos⟩ := by
      rw [cycMBasis_apply]
      simp
    have hk : (k : CycM m) = (k : ℤ) • cycMBasis m ⟨0, hpos⟩ := by
      rw [← hone, zsmul_eq_mul, mul_one]
      push_cast
      rfl
    rw [natCast_dvd_iff_dvd_contentM] at h
    have hcoord := h.trans (Finset.gcd_dvd (Finset.mem_univ ⟨0, hpos⟩))
    rw [hk, map_smul] at hcoord
    simpa [Basis.repr_self] using hcoord
  · intro h
    exact_mod_cast Nat.cast_dvd_cast (α := CycM m) h

/-- **The symbol is a genuine primitive `m`-th root of unity.** -/
theorem isPrimitiveRoot_zetaM (hm : 0 < m) :
    IsPrimitiveRoot (zetaM m) m := by
  have := isDomain_cycM hm
  have : NeZero ((m : ℕ) : CycM m) := ⟨natCast_ne_zero_cycM hm hm.ne'⟩
  have hroot : IsRoot (cyclotomic m (CycM m)) (zetaM m) := by
    have h := AdjoinRoot.isRoot_root (cyclotomic m ℤ)
    rwa [map_cyclotomic] at h
  exact isRoot_cyclotomic_iff.mp hroot

/-- `ζ_m` as a unit. -/
noncomputable def zetaMUnit (hm : 0 < m) : (CycM m)ˣ :=
  ((isPrimitiveRoot_zetaM hm).isUnit hm.ne').unit

@[simp] theorem val_zetaMUnit (hm : 0 < m) :
    ((zetaMUnit hm : (CycM m)ˣ) : CycM m) = zetaM m :=
  IsUnit.unit_spec _

theorem zetaMUnit_pow_eq_one (hm : 0 < m) : zetaMUnit hm ^ m = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, val_zetaMUnit, Units.val_one]
  exact (isPrimitiveRoot_zetaM hm).pow_eq_one

end Basis

end CP

end Azurite
