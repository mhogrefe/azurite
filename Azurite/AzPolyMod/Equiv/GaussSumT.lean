/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The G-element correspondence**: the computable tower's
  accumulated Gauss sum IS the reduction of the symbolic one —

    `reduceT (gaussSum χ_(p,q) ψ) = gaussSumT n p q g`
    (`reduceT_gaussSum`),

  for the checker's natural-number primitive root `g` reducing to
  the generator `gu` of `(Z_q)ˣ`.  With the kernel theorem
  (`natCast_dvd_iff_reduceT`) this makes every step-3/4 check of the
  rail — an equality test between `gaussSumT`-powers and
  `ζ_p`-powers in `GaussTowerPQ` — EXACTLY the tower congruence
  hypothesis of `theorem_4_4_6_composite_tower`.

  The proof walks both sides into the same sum: the symbolic side by
  the generator reindexing `gaussSum_eq_sum_range` and the value
  lemmas of the reduction; the computable side by the loop invariant
  `gaussSumTAux_spec` (the accumulation is
  `Σ_j ζ_p^j ζ_q^(g^j mod q)`, with the running residue `g^k mod q`
  kept below `q`).  En route: `ofCoeff` is multiplicative
  (`ofCoeff_mul`/`ofCoeff_pow`) and a reduced monomial factors as a
  constant times a power of the class of `x`
  (`ofPoly_monomial_eq`) — generic `AzPolyMod` facts.
-/
import Azurite.AzPolyMod.Equiv.GaussTower
import Azurite.CrandallPomerance.Chapter4.Theorem_4_4_6_Tower

namespace Azurite

namespace AzPolyMod

open _root_.Azurite.AzPolynomial

section OfCoeff

variable {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R]
  {f : AzPolynomial R} [hfact : Fact (AzPolynomial.toPoly f).Monic]

omit [DecidableEq R] [Nontrivial R] in
private theorem monic_f' : (AzPolynomial.toPoly f).Monic := hfact.out

omit [DecidableEq R] in
private theorem ne_zero_f' : AzPolynomial.toPoly f ≠ 0 := hfact.out.ne_zero

theorem ofCoeff_mul (a b : R) :
    (ofCoeff a : AzPolyMod f) * ofCoeff b = ofCoeff (a * b) :=
  toAdjoin_injective monic_f' ne_zero_f' (by
    rw [toAdjoin_mul monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f', map_mul])

theorem ofCoeff_pow (a : R) (k : ℕ) :
    (ofCoeff a : AzPolyMod f) ^ k = ofCoeff (a ^ k) :=
  toAdjoin_injective monic_f' ne_zero_f' (by
    show toAdjoin ((ofCoeff a : AzPolyMod f).pow k) = _
    rw [toAdjoin_pow monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f', map_pow])

/-- A reduced monomial factors as a constant times a power of the
class of `x`. -/
theorem ofPoly_monomial_eq (m : ℕ) (c : R) :
    (ofPoly (AzPolynomial.monomial m c) : AzPolyMod f)
      = ofCoeff c * (ofPoly AzPolynomial.X) ^ m :=
  toAdjoin_injective monic_f' ne_zero_f' (by
    show _ = toAdjoin ((ofCoeff c : AzPolyMod f)
      * (ofPoly AzPolynomial.X : AzPolyMod f).pow m)
    rw [toAdjoin_ofPoly monic_f' ne_zero_f', toPoly_monomial,
      toAdjoin_mul monic_f' ne_zero_f',
      toAdjoin_ofCoeff monic_f' ne_zero_f',
      toAdjoin_pow monic_f' ne_zero_f',
      toAdjoin_ofPoly monic_f' ne_zero_f', AzPolynomial.toPoly_X,
      AdjoinRoot.mk_X, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
      AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X])

end OfCoeff

section Correspondence

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [Fact p.Prime]
  [Fact q.Prime]

theorem constT_pow (c : GaussTowerP n p) (k : ℕ) :
    constT n p q c ^ k = constT n p q (c ^ k) := by
  rw [constT, constT]
  exact ofCoeff_pow c k

/-- The loop invariant of the Gauss-sum accumulation: with the
running residue `gk < q`, the loop adds
`Σ_j ζ_p-const · ζ_q-powers`. -/
theorem gaussSumTAux_spec (g : ℕ) : ∀ (steps gk : ℕ)
    (zk : GaussTowerP n p) (acc : GaussTowerPQ n p q), gk < q →
    gaussSumTAux n p q g steps gk zk acc
      = acc + ∑ j ∈ Finset.range steps,
          constT n p q (zk * zetaPT n p ^ j)
            * zetaQT n p q ^ ((gk * g ^ j) % q) := by
  intro steps
  induction steps with
  | zero =>
    intro gk zk acc _
    simp [gaussSumTAux]
  | succ steps ih =>
    intro gk zk acc hgk
    have hq : 0 < q := (Fact.out (p := q.Prime)).pos
    rw [gaussSumTAux, ih (gk * g % q) (zk * zetaPT n p) _
      (Nat.mod_lt _ hq)]
    rw [Finset.sum_range_succ']
    have hfirst : constT n p q (zk * zetaPT n p ^ 0)
        * zetaQT n p q ^ ((gk * g ^ 0) % q)
        = ofPoly (AzPolynomial.monomial gk zk) := by
      rw [pow_zero, mul_one, pow_zero, mul_one, Nat.mod_eq_of_lt hgk,
        ofPoly_monomial_eq, constT, zetaQT]
    have hshift : ∀ j, constT n p q (zk * zetaPT n p * zetaPT n p ^ j)
        * zetaQT n p q ^ ((gk * g % q * g ^ j) % q)
        = constT n p q (zk * zetaPT n p ^ (j + 1))
          * zetaQT n p q ^ ((gk * g ^ (j + 1)) % q) := by
      intro j
      rw [Nat.mod_mul_mod, mul_assoc gk g (g ^ j), ← pow_succ']
      rw [mul_assoc zk (zetaPT n p) (zetaPT n p ^ j), ← pow_succ']
    rw [Finset.sum_congr rfl fun j _ => hshift j, hfirst]
    ring

/-- The computable Gauss sum as a closed sum. -/
theorem gaussSumT_eq (g : ℕ) :
    gaussSumT n p q g
      = ∑ j ∈ Finset.range (q - 1),
          constT n p q (zetaPT n p ^ j) * zetaQT n p q ^ (g ^ j % q) := by
  have hq : 0 < q := (Fact.out (p := q.Prime)).pos
  rw [gaussSumT, gaussSumTAux_spec n p q g (q - 1) (1 % q) 1 0
    (Nat.mod_lt _ hq), zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_mul, Nat.mod_mul_mod, one_mul]

/-- **The G-element correspondence**: the reduction of the symbolic
Gauss sum is the computable tower's accumulated one. -/
theorem reduceT_gaussSum {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (q - 1).primeFactors) {gu : (ZMod q)ˣ}
    (hgen : ∀ x, x ∈ Subgroup.zpowers gu) {g : ℕ}
    (hg : ((g : ℕ) : ZMod q) = (gu : ZMod q)) :
    reduceT n p q (gaussSum
        (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp) hgen)
        (AddChar.zmodChar q (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one))
      = gaussSumT n p q g := by
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  rw [CP.gaussSum_eq_sum_range _ _ hgen, map_sum, gaussSumT_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, map_pow]
  congr 1
  · rw [MulChar.ofRootOfUnity_spec, CP.val_zetaPQUnit hp, reduceT_zetaP]
    exact constT_pow n p q _ k
  · rw [reduceT_zetaQ]
    congr 1
    rw [Units.val_pow_eq_pow_val, ← hg, ← Nat.cast_pow, ZMod.val_natCast]

end Correspondence

end AzPolyMod

end Azurite
