/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The mod-`n` pair tower `(ℤ/n)[ζ_p, ζ_q]` and the REDUCTION
  homomorphism from `ℤ[ζ_p, ζ_q]` — the mathematical half of the
  semantic bridge between the computable Gauss-sum tower
  (`AzPolyMod/GaussTower.lean`) and the `CycPQ` congruences consumed
  by `theorem_4_4_6_composite_tower`.

  `CycPQModN n p q = (ℤ/n)[x]/(Φ_p)[y]/(Φ_q)` is the same double
  `AdjoinRoot` construction as Definition 4.4.4's tower with base
  `ℤ/n`; over it the monomials `ζ_p^i ζ_q^k` form a `ℤ/n`-basis
  (`cycBasisModN`, the same product of monic power bases).  The
  reduction `reduceModN : ℤ[ζ_p, ζ_q] →+* (ℤ/n)[ζ_p, ζ_q]` is a
  double `AdjoinRoot.lift` (each root maps to the corresponding
  root, which needs no primitivity: the tower root IS a root of the
  mapped cyclotomic).

  The payoff is the KERNEL THEOREM `natCast_dvd_iff_reduceModN`:

    `(n : ℤ[ζ_p, ζ_q]) ∣ x  ↔  reduceModN x = 0`,

  by reading coordinates — the reduction sends the `ℤ`-basis to the
  `ℤ/n`-basis, so `reduceModN x` vanishes exactly when every
  coordinate of `x` vanishes mod `n`, i.e. when `n` divides the
  content (Definition 4.4.4).  The algorithm's checks compute
  equalities in (a computable model of) `CycPQModN`; this theorem is
  what turns them into the ring divisibilities of the correctness
  machinery.
-/
import Azurite.CrandallPomerance.Chapter4.Definition_4_4_4

namespace Azurite

namespace CP

open Polynomial Module

variable (n p q : ℕ)

/-- The mod-`n` model of `ℤ/n[ζ_p]`. -/
abbrev CycPModN := AdjoinRoot (cyclotomic p (ZMod n))

/-- The mod-`n` model of `(ℤ/n)[ζ_p, ζ_q]`. -/
abbrev CycPQModN := AdjoinRoot (cyclotomic q (CycPModN n p))

/-- The symbol `ζ_p` in the mod-`n` tower. -/
noncomputable def zetaPModN : CycPQModN n p q :=
  algebraMap (CycPModN n p) (CycPQModN n p q)
    (AdjoinRoot.root (cyclotomic p (ZMod n)))

/-- The symbol `ζ_q` in the mod-`n` tower. -/
noncomputable def zetaQModN : CycPQModN n p q :=
  AdjoinRoot.root (cyclotomic q (CycPModN n p))

section Basis

variable [Fact (1 < n)] [Fact p.Prime] [Fact q.Prime]

/-- The power basis `1, ζ_p, …, ζ_p^(p−2)` of the first leg over
`ℤ/n`. -/
noncomputable def cycPBasisModN : Basis (Fin (p - 1)) (ZMod n) (CycPModN n p) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic p (ZMod n))).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic,
        Nat.totient_prime (Fact.out (p := p.Prime))]))

instance : Nontrivial (CycPModN n p) := by
  have hb := (cycPBasisModN n p).ne_zero ⟨0, by
    have := (Fact.out (p := p.Prime)).two_le
    omega⟩
  exact nontrivial_of_ne _ _ hb

/-- The power basis `1, ζ_q, …, ζ_q^(q−2)` of the mod-`n` tower over
its first leg. -/
noncomputable def cycQBasisModN :
    Basis (Fin (q - 1)) (CycPModN n p) (CycPQModN n p q) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic q (CycPModN n p))).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic,
        Nat.totient_prime (Fact.out (p := q.Prime))]))

/-- The monomials `ζ_p^i ζ_q^k` form a `ℤ/n`-basis of the mod-`n`
tower. -/
noncomputable def cycBasisModN :
    Basis (Fin (p - 1) × Fin (q - 1)) (ZMod n) (CycPQModN n p q) :=
  (cycPBasisModN n p).smulTower (cycQBasisModN n p q)

/-- The basis vectors are the monomials. -/
theorem cycBasisModN_apply (i : Fin (p - 1)) (k : Fin (q - 1)) :
    cycBasisModN n p q (i, k)
      = zetaPModN n p q ^ (i : ℕ) * zetaQModN n p q ^ (k : ℕ) := by
  rw [cycBasisModN, Basis.smulTower_apply]
  rw [Algebra.smul_def]
  congr 1
  · rw [cycPBasisModN, Basis.reindex_apply, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen, map_pow]
    rfl
  · rw [cycQBasisModN, Basis.reindex_apply, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen]
    rfl

end Basis

/-- An integer cyclotomic vanishes at any root of its mod-`S` image
(no primitivity needed). -/
private theorem eval₂_cyclotomic_int_of_eval {S : Type _} [CommRing S]
    {k : ℕ} {ζ : S} (hζ : eval ζ (cyclotomic k S) = 0) :
    (cyclotomic k ℤ).eval₂ (Int.castRingHom S) ζ = 0 := by
  rw [eval₂_eq_eval_map, map_cyclotomic]
  exact hζ

/-- The tower root is a root of the corresponding cyclotomic over the
tower. -/
private theorem eval_root_cyclotomic {S : Type _} [CommRing S] (k : ℕ) :
    eval (AdjoinRoot.root (cyclotomic k S))
      (cyclotomic k (AdjoinRoot (cyclotomic k S))) = 0 := by
  have h := AdjoinRoot.isRoot_root (cyclotomic k S)
  rwa [map_cyclotomic] at h

/-- The first leg of the reduction: `ℤ[ζ_p] → (ℤ/n)[ζ_p]`. -/
noncomputable def reducePModN : CycP p →+* CycPModN n p :=
  AdjoinRoot.lift (Int.castRingHom _)
    (AdjoinRoot.root (cyclotomic p (ZMod n)))
    (eval₂_cyclotomic_int_of_eval (eval_root_cyclotomic p))

/-- **The mod-`n` reduction** `ℤ[ζ_p, ζ_q] → (ℤ/n)[ζ_p, ζ_q]`:
`ζ_p ↦ ζ_p`, `ζ_q ↦ ζ_q`, coefficients mod `n`. -/
noncomputable def reduceModN : CycPQ p q →+* CycPQModN n p q :=
  AdjoinRoot.lift
    ((AdjoinRoot.of (cyclotomic q (CycPModN n p))).comp (reducePModN n p))
    (zetaQModN n p q) (by
      rw [show cyclotomic q (CycP p)
          = map (Int.castRingHom (CycP p)) (cyclotomic q ℤ) from
          (map_cyclotomic q (Int.castRingHom (CycP p))).symm,
        eval₂_map,
        Subsingleton.elim
          (((AdjoinRoot.of (cyclotomic q (CycPModN n p))).comp
            (reducePModN n p)).comp (Int.castRingHom (CycP p)))
          (Int.castRingHom _)]
      refine eval₂_cyclotomic_int_of_eval ?_
      have h := AdjoinRoot.isRoot_root (cyclotomic q (CycPModN n p))
      rwa [map_cyclotomic] at h)

@[simp] theorem reduceModN_zetaP :
    reduceModN n p q (zetaP p q) = zetaPModN n p q := by
  rw [zetaP, reduceModN]
  rw [show (algebraMap (CycP p) (CycPQ p q)) (AdjoinRoot.root _)
      = AdjoinRoot.of _ (AdjoinRoot.root _) from rfl,
    AdjoinRoot.lift_of, RingHom.comp_apply, reducePModN,
    AdjoinRoot.lift_root]
  rfl

@[simp] theorem reduceModN_zetaQ :
    reduceModN n p q (zetaQ p q) = zetaQModN n p q := by
  rw [zetaQ, reduceModN, AdjoinRoot.lift_root]

/-- `n` vanishes in the mod-`n` tower. -/
theorem natCast_self_reduceModN : ((n : ℕ) : CycPQModN n p q) = 0 := by
  have h : ((n : ℕ) : CycPQModN n p q)
      = algebraMap (ZMod n) (CycPQModN n p q) ((n : ℕ) : ZMod n) := by
    rw [map_natCast]
  rw [h, ZMod.natCast_self, map_zero]

section Kernel

variable [Fact (1 < n)] [Fact p.Prime] [Fact q.Prime]

/-- **The kernel theorem**: `n` divides `x` in `ℤ[ζ_p, ζ_q]` exactly
when the mod-`n` reduction of `x` vanishes — the semantic content of
the algorithm's coefficientwise computations. -/
theorem natCast_dvd_iff_reduceModN (x : CycPQ p q) :
    (n : CycPQ p q) ∣ x ↔ reduceModN n p q x = 0 := by
  have : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  constructor
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, natCast_self_reduceModN, zero_mul]
  · intro h0
    -- the reduction sends the `ℤ`-basis to the `ℤ/n`-basis
    have hmap : ∀ ik : Fin (p - 1) × Fin (q - 1),
        reduceModN n p q (cycBasis p q ik) = cycBasisModN n p q ik := by
      rintro ⟨i, k⟩
      rw [cycBasis_apply, map_mul, map_pow, map_pow, reduceModN_zetaP,
        reduceModN_zetaQ, cycBasisModN_apply]
    -- expand `x` in coordinates and reduce
    have hexp : reduceModN n p q x
        = ∑ ik : Fin (p - 1) × Fin (q - 1),
            (((cycBasis p q).repr x ik : ℤ) : ZMod n)
              • cycBasisModN n p q ik := by
      conv_lhs => rw [← (cycBasis p q).sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun ik _ => ?_
      rw [map_zsmul, hmap ik, Int.cast_smul_eq_zsmul]
    rw [hexp] at h0
    have hcoeff := Fintype.linearIndependent_iff.mp
      (cycBasisModN n p q).linearIndependent _ h0
    -- each coordinate vanishes mod `n`, so `n` divides the content
    refine (natCast_dvd_iff_dvd_content p q n x).mpr ?_
    refine Finset.dvd_gcd fun ik _ => ?_
    have hz : (((cycBasis p q).repr x ik : ℤ) : ZMod n) = 0 := hcoeff ik
    have hdvd : ((n : ℕ) : ℤ) ∣ (cycBasis p q).repr x ik :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz
    have habs := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at habs

end Kernel

end CP

end Azurite
