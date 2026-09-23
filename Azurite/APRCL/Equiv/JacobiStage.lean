/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the per-`(p, q)` Jacobi tests**: a found exponent `h` is
  the congruence `n ∣ W − ζ^h` in `ℤ[ζ_{p^k}]` for the product `W` of
  Theorems (8.5)/(9.1)/(9.3)/(9.5)/(9.10)/(9.19).  Every proof is the same
  three lines: the computed element is `reduceCycT W` (the tables are
  reductions by `jacobiSumT_eq_reduce`, the ring operations commute with the
  reduction, the `AzNat` powers are monoid powers), Algorithm (6.2) is sound
  (`findHT_spec`), and equality in `CycT` is congruence modulo `n`
  (`reduceCycT_eq_iff`).
-/
import Azurite.APRCL.JacobiStage
import Azurite.AzPolyMod.Equiv.Cyclotomic
import Azurite.AzPolyMod.Equiv.CycArith
import Azurite.CohenLenstra.Algorithm_12_1

namespace Azurite

namespace APRCL

open AzPolyMod CL CP Finset

variable {n : AzNat} [Fact (1 < n.toNat)] {p k : ℕ} (hp : p.Prime) (hk : 0 < k)

include hp hk in
/-- `cycPow` is the monoid power (restated for the `rw` chains below). -/
theorem cycT_pow_azNat (a : CycT n p k) (m : AzNat) : cycPow n p k a m = a ^ m.toNat :=
  cycPow_eq hp hk a m

include hp hk in
/-- **The common kernel of the bridges**: `findHT w = some h` and
`w = reduceCycT W` give `n ∣ W − ζ^h`. -/
theorem findHT_reduce {w : CycT n p k} {W : CycM (p ^ k)} {h : ℕ}
    (hfind : findHT w = some h) (hw : w = reduceCycT n p k hp hk W) :
    ((n.toNat : ℕ) : CycM (p ^ k)) ∣ W - zetaM (p ^ k) ^ h := by
  rw [← reduceCycT_eq_iff n p k hp hk, map_pow, reduceCycT_zetaM, ← hw]
  have h1 := findHT_spec hp hk hfind
  rw [← ringEquivAdjoinRoot_apply, ← ringEquivAdjoinRoot_apply, ← map_pow] at h1
  exact (ringEquivAdjoinRoot).injective h1

omit [Fact (1 < n.toNat)] in
theorem vRem_eq (m : ℕ) : vRem n m = n.toNat % m := by
  rw [vRem, AzNat.toNat_mod, AzNat.toNat_ofNat]

omit [Fact (1 < n.toNat)] in
theorem toNat_uQuot (m : ℕ) : (uQuot n m).toNat = n.toNat / m := by
  rw [uQuot, AzNat.toNat_div, AzNat.toNat_ofNat]

section Tables

variable {q : ℕ} [Fact q.Prime] (hpk : p ^ k ∣ q - 1) {gu : (ZMod q)ˣ}
  (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) {f : ℕ → ℕ}
  (hf : ∀ x ∈ Finset.Icc 1 (q - 2), ((gu : ZMod q)) ^ f x = 1 - ((gu : ZMod q)) ^ x)

include hp hk hpk hg hf

/-- **`jOdd` is Algorithm (6.2) on the reduced (8.8) product**. -/
theorem jOdd_eq :
    jOdd n p k q f = findHT (reduceCycT n p k hp hk (∏ x ∈ Mset p k,
      jacobiSum (chiT hp hpk hg ^ minv p k x) (chiT hp hpk hg ^ minv p k x) ^ αc n.toNat p k x)) := by
  simp only [jOdd]
  congr 1
  rw [prod_pow_alphac_decomp _ n.toNat p k (pow_pos hp.pos k), map_mul, map_pow, map_prod,
    map_prod, cycT_pow_azNat hp hk, toNat_uQuot]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [cycT_pow_azNat hp hk, AzNat.toNat_ofNat, map_pow, jacobiSumT_eq_reduce n hp hk hpk hg hf]
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [cycT_pow_azNat hp hk, AzNat.toNat_ofNat, map_pow, jacobiSumT_eq_reduce n hp hk hpk hg hf, vRem_eq]

/-- **(i1a)+(i2b), odd `p`, decoded**: the hypothesis (8.8) of Theorem (8.5) at
`a = b = 1`, with `ζ' = ζ^h`. -/
theorem jOdd_spec {h : ℕ} (hh : jOdd n p k q f = some h) :
    ((n.toNat : ℕ) : CycM (p ^ k)) ∣ (∏ x ∈ Mset p k,
      jacobiSum (chiT hp hpk hg ^ minv p k x) (chiT hp hpk hg ^ minv p k x) ^ αc n.toNat p k x)
      - zetaM (p ^ k) ^ h := by
  rw [jOdd_eq hp hk hpk hg hf] at hh
  exact findHT_reduce hp hk hh rfl

end Tables

section Two

variable {q : ℕ} [Fact q.Prime] {gu : (ZMod q)ˣ}
  (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) {f : ℕ → ℕ}
  (hf : ∀ x ∈ Finset.Icc 1 (q - 2), ((gu : ZMod q)) ^ f x = 1 - ((gu : ZMod q)) ^ x)

omit [Fact q.Prime] in
/-- **`j2k1` is Algorithm (6.2) on the reduced (9.2) element.** -/
theorem j2k1_eq :
    j2k1 n q = findHT (reduceCycT n 2 1 Nat.prime_two one_pos
      (((q : ℕ) : CycM (2 ^ 1)) ^ ((n.toNat - 1) / 2))) := by
  unfold j2k1
  congr 1
  rw [map_pow, map_natCast, cycT_pow_azNat Nat.prime_two one_pos, AzNat.toNat_div, AzNat.toNat_sub,
    AzNat.toNat_ofNat]
  rfl

omit [Fact q.Prime] in
/-- **(i1b), decoded**: the hypothesis (9.2) of Theorem (9.1), `ζ' = ζ^h`. -/
theorem j2k1_spec {h : ℕ} (hh : j2k1 n q = some h) :
    ((n.toNat : ℕ) : CycM (2 ^ 1)) ∣ ((q : ℕ) : CycM (2 ^ 1)) ^ ((n.toNat - 1) / 2)
      - zetaM (2 ^ 1) ^ h := by
  rw [j2k1_eq] at hh
  exact findHT_reduce Nat.prime_two one_pos hh rfl

include hg hf

/-- **`j2k2`, `n ≡ 1 (mod 4)`**, is Algorithm (6.2) on the reduced (9.4) element. -/
theorem j2k2_eq_one (hpk : 2 ^ 2 ∣ q - 1) (hn4 : n.toNat % 4 = 1) :
    j2k2 n q f = findHT (reduceCycT n 2 2 Nat.prime_two two_pos
      (jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((n.toNat - 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((n.toNat - 1) / 4))) := by
  unfold j2k2
  dsimp only
  rw [vRem_eq, ite_eq_left hn4]
  congr 1
  have hJ := jacobiSumT_eq_reduce n Nat.prime_two two_pos hpk hg hf 1 1
  rw [map_mul, map_pow, map_pow, map_natCast, hJ, cycT_pow_azNat Nat.prime_two two_pos,
    cycT_pow_azNat Nat.prime_two two_pos, AzNat.toNat_div, AzNat.toNat_div, AzNat.toNat_sub,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  simp only [pow_one]
  rfl

/-- **`j2k2`, `n ≡ 3 (mod 4)`**, is Algorithm (6.2) on the reduced (9.6) element. -/
theorem j2k2_eq_three (hpk : 2 ^ 2 ∣ q - 1) (hn4 : n.toNat % 4 = 3) :
    j2k2 n q f = findHT (reduceCycT n 2 2 Nat.prime_two two_pos
      (jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((n.toNat + 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((n.toNat - 3) / 4))) := by
  unfold j2k2
  dsimp only
  rw [vRem_eq, ite_eq_right (by omega)]
  congr 1
  have hJ := jacobiSumT_eq_reduce n Nat.prime_two two_pos hpk hg hf 1 1
  rw [map_mul, map_pow, map_pow, map_natCast, hJ, cycT_pow_azNat Nat.prime_two two_pos,
    cycT_pow_azNat Nat.prime_two two_pos, AzNat.toNat_div, AzNat.toNat_div, AzNat.toNat_add,
    AzNat.toNat_sub, AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  simp only [pow_one]
  rfl

/-- **(i1c), `n ≡ 1 (mod 4)`, decoded**: the hypothesis (9.4) of Theorem (9.3). -/
theorem j2k2_spec_one (hpk : 2 ^ 2 ∣ q - 1) (hn4 : n.toNat % 4 = 1) {h : ℕ}
    (hh : j2k2 n q f = some h) :
    ((n.toNat : ℕ) : CycM (2 ^ 2)) ∣
      jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((n.toNat - 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((n.toNat - 1) / 4) - zetaM (2 ^ 2) ^ h := by
  rw [j2k2_eq_one hg hf hpk hn4] at hh
  exact findHT_reduce Nat.prime_two two_pos hh rfl

/-- **(i1c), `n ≡ 3 (mod 4)`, decoded**: the hypothesis (9.6) of Theorem (9.5). -/
theorem j2k2_spec_three (hpk : 2 ^ 2 ∣ q - 1) (hn4 : n.toNat % 4 = 3) {h : ℕ}
    (hh : j2k2 n q f = some h) :
    ((n.toNat : ℕ) : CycM (2 ^ 2)) ∣
      jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((n.toNat + 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((n.toNat - 3) / 4) - zetaM (2 ^ 2) ^ h := by
  rw [j2k2_eq_three hg hf hpk hn4] at hh
  exact findHT_reduce Nat.prime_two two_pos hh rfl

variable (hpk : 2 ^ k ∣ q - 1)
include hpk

/-- The (9.11)/(9.20) product, as computed by `j2k3` before the `n mod 8` split. -/
theorem j2k3_core (hk : 0 < k) :
    cycPow n 2 k (∏ x ∈ M2set k, cycPow n 2 k (jacobiSumT n 2 k q f (minv 2 k x) (minv 2 k x)
        * jacobiSumT n 2 k q f (minv 2 k x) (2 * minv 2 k x)) (AzNat.ofNat x)) (uQuot n (2 ^ k))
      * ∏ x ∈ M2set k, cycPow n 2 k (jacobiSumT n 2 k q f (minv 2 k x) (minv 2 k x)
        * jacobiSumT n 2 k q f (minv 2 k x) (2 * minv 2 k x)) (AzNat.ofNat (αc (vRem n (2 ^ k)) 2 k x))
    = reduceCycT n 2 k Nat.prime_two (by omega) (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc n.toNat 2 k x) := by
  rw [prod_pow_alphac_decomp _ n.toNat 2 k (pow_pos two_pos k), map_mul, map_pow, map_prod,
    map_prod, cycT_pow_azNat Nat.prime_two hk, toNat_uQuot]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [cycT_pow_azNat Nat.prime_two hk, AzNat.toNat_ofNat, map_pow, map_mul,
      jacobiSumT_eq_reduce n Nat.prime_two hk hpk hg hf, jacobiSumT_eq_reduce n Nat.prime_two hk hpk hg hf]
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [cycT_pow_azNat Nat.prime_two hk, AzNat.toNat_ofNat, map_pow, map_mul,
      jacobiSumT_eq_reduce n Nat.prime_two hk hpk hg hf, jacobiSumT_eq_reduce n Nat.prime_two hk hpk hg hf,
      vRem_eq]

/-- **`j2k3`, `n ≡ 1, 3 (mod 8)`**, is Algorithm (6.2) on the reduced (9.11) product. -/
theorem j2k3_eq_low (hk3 : 3 ≤ k) (hn8 : n.toNat % 8 = 1 ∨ n.toNat % 8 = 3) :
    j2k3 n k q f = findHT (reduceCycT n 2 k Nat.prime_two (lt_of_lt_of_le (by decide) hk3) (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc n.toNat 2 k x)) := by
  unfold j2k3
  dsimp only
  rw [vRem_eq, ite_eq_left hn8, j2k3_core hg hf hpk (by omega)]

/-- **`j2k3`, `n ≡ 5, 7 (mod 8)`**, is Algorithm (6.2) on the reduced (9.20) product. -/
theorem j2k3_eq_high (hk3 : 3 ≤ k) (hn8 : n.toNat % 8 = 5 ∨ n.toNat % 8 = 7) :
    j2k3 n k q f = findHT (reduceCycT n 2 k Nat.prime_two (lt_of_lt_of_le (by decide) hk3) ((∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc n.toNat 2 k x)
        * jacobiSum (chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3))
            ((chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3)) ^ 3) ^ 2)) := by
  unfold j2k3
  dsimp only
  rw [vRem_eq, ite_eq_right (by omega)]
  congr 1
  rw [map_mul, ← j2k3_core hg hf hpk (by omega), map_pow, ← pow_mul, mul_comm (2 ^ (k - 3)) 3,
    ← jacobiSumT_eq_reduce n Nat.prime_two (by omega) hpk hg hf (2 ^ (k - 3)) (3 * 2 ^ (k - 3)),
    cycT_pow_azNat Nat.prime_two (by omega) (jacobiSumT n 2 k q f (2 ^ (k - 3)) (3 * 2 ^ (k - 3)))
      (AzNat.ofNat 2), AzNat.toNat_ofNat]

/-- **(i1d), `n ≡ 1, 3 (mod 8)`, decoded**: the hypothesis (9.11) of Theorem (9.10). -/
theorem j2k3_spec_low (hk3 : 3 ≤ k) (hn8 : n.toNat % 8 = 1 ∨ n.toNat % 8 = 3) {h : ℕ}
    (hh : j2k3 n k q f = some h) :
    ((n.toNat : ℕ) : CycM (2 ^ k)) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc n.toNat 2 k x)
      - zetaM (2 ^ k) ^ h := by
  rw [j2k3_eq_low hg hf hpk hk3 hn8] at hh
  exact findHT_reduce Nat.prime_two (by omega) hh rfl

/-- **(i1d), `n ≡ 5, 7 (mod 8)`, decoded**: the hypothesis (9.20) of Theorem (9.19). -/
theorem j2k3_spec_high (hk3 : 3 ≤ k) (hn8 : n.toNat % 8 = 5 ∨ n.toNat % 8 = 7) {h : ℕ}
    (hh : j2k3 n k q f = some h) :
    ((n.toNat : ℕ) : CycM (2 ^ k)) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc n.toNat 2 k x)
        * jacobiSum (chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3))
            ((chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3)) ^ 3) ^ 2
      - zetaM (2 ^ k) ^ h := by
  rw [j2k3_eq_high hg hf hpk hk3 hn8] at hh
  exact findHT_reduce Nat.prime_two (by omega) hh rfl

end Two

end APRCL

end Azurite
