/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The per-`(p, q)` Jacobi-sum tests of Algorithm (1.3)(i)** — Phase C3 of
  `docs/aprcl_implementation_plan.md`, computable side.

  For a prime `q ∣ s₂` and a prime `p ∣ q − 1` with `k = v_p(q − 1)`, the
  test computes, in the ring `CycT n p k = (ℤ/nℤ)[x]/(Φ_{p^k})`, the
  products of Theorems (8.5)/(9.1)/(9.3)/(9.5)/(9.10)/(9.19) from the
  Jacobi-sum tables `jacobiSumT` and searches the exponent `h` with
  `j₀^u·j_v = ζ^h` by Algorithm (6.2) (`findHT`).  Instead of the paper's
  `σ_x⁻¹(j^x)` the table `J(χ^{x⁻¹}, χ^{x⁻¹})` is read off directly
  (`jacobiSumT` with exponents `x⁻¹ mod p^k`), which is the same element
  and makes the correctness proof a one-line instance of
  `jacobiSumT_eq_reduce`.  All large powers use the `AzNat` exponent
  `u = n / p^k` (`uQuot`); only `v = n mod p^k` (`vRem`) is a small `ℕ`.

  The (i2a) `λ`-route for flagged prime powers is a performance option
  (Phase D); the (i2b) full-ring test is always valid and is what is
  implemented here.
-/
import Azurite.CohenLenstra.Tables
import Azurite.CohenLenstra.Theorem_9_10
import Azurite.AzPolyMod.CycArith

namespace Azurite

namespace APRCL

open AzPolyMod CL

variable (n : AzNat) [Fact (1 < n.toNat)]

/-- The small remainder `v = n mod m`. -/
def vRem (m : ℕ) : ℕ := (n % AzNat.ofNat m).toNat

/-- The large quotient `u = n / m`. -/
def uQuot (m : ℕ) : AzNat := n / AzNat.ofNat m

/-- **(i1a)+(i2b), odd `p`**: `j₀ = ∏_{x ∈ M} J(χ^{x⁻¹}, χ^{x⁻¹})^x`,
`j_v = ∏_{x ∈ M} J(χ^{x⁻¹}, χ^{x⁻¹})^{⌊vx/p^k⌋}`, and the exponent `h` with
`j₀^u · j_v = ζ^h` (Theorem (8.5) with `a = b = 1`). -/
def jOdd (p k q : ℕ) (f : ℕ → ℕ) : Option ℕ :=
  let J : ℕ → CycT n p k := fun x => jacobiSumT n p k q f (minv p k x) (minv p k x)
  let j0 : CycT n p k := ∏ x ∈ Mset p k, cycPow n p k (J x) (AzNat.ofNat x)
  let jv : CycT n p k := ∏ x ∈ Mset p k, cycPow n p k (J x) (AzNat.ofNat (αc (vRem n (p ^ k)) p k x))
  findHT (cycPow n p k j0 (uQuot n (p ^ k)) * jv)

/-- **(i1b), `p^k = 2`**: `q^((n−1)/2) = ζ^h` with `ζ = −1` (Theorem (9.1)). -/
def j2k1 (q : ℕ) : Option ℕ :=
  findHT (cycPow n 2 1 (q : CycT n 2 1) ((n - 1) / AzNat.ofNat 2))

/-- **(i1c), `p^k = 4`**: the tests (9.4)/(9.6) of Theorems (9.3)/(9.5):
`J(χ,χ)^((n−1)/2)·q^((n−1)/4) = ζ^h` for `n ≡ 1 (mod 4)`, and
`J(χ,χ)^((n+1)/2)·q^((n−3)/4) = ζ^h` for `n ≡ 3 (mod 4)`. -/
def j2k2 (q : ℕ) (f : ℕ → ℕ) : Option ℕ :=
  let J : CycT n 2 2 := jacobiSumT n 2 2 q f 1 1
  if vRem n 4 = 1 then
    findHT (cycPow n 2 2 J ((n - 1) / AzNat.ofNat 2)
      * cycPow n 2 2 (q : CycT n 2 2) ((n - 1) / AzNat.ofNat 4))
  else
    findHT (cycPow n 2 2 J ((n + 1) / AzNat.ofNat 2)
      * cycPow n 2 2 (q : CycT n 2 2) ((n - AzNat.ofNat 3) / AzNat.ofNat 4))

/-- **(i1d), `p = 2`, `k ≥ 3`**: with `J(x) = J(χ^{x⁻¹}, χ^{x⁻¹})·J(χ^{x⁻¹}, χ^{2x⁻¹})`
over `M = {x < 2^k : x ≡ 1, 3 (mod 8)}`, the product `j₀^u·j_v` of Theorem (9.10),
multiplied by `J(χ^{2^{k−3}}, χ^{3·2^{k−3}})²` when `n ≡ 5, 7 (mod 8)` (Theorem (9.19)). -/
def j2k3 (k q : ℕ) (f : ℕ → ℕ) : Option ℕ :=
  let J : ℕ → CycT n 2 k := fun x =>
    jacobiSumT n 2 k q f (minv 2 k x) (minv 2 k x) * jacobiSumT n 2 k q f (minv 2 k x) (2 * minv 2 k x)
  let j0 : CycT n 2 k := ∏ x ∈ M2set k, cycPow n 2 k (J x) (AzNat.ofNat x)
  let jv : CycT n 2 k := ∏ x ∈ M2set k, cycPow n 2 k (J x) (AzNat.ofNat (αc (vRem n (2 ^ k)) 2 k x))
  let w : CycT n 2 k := cycPow n 2 k j0 (uQuot n (2 ^ k)) * jv
  if vRem n 8 = 1 ∨ vRem n 8 = 3 then findHT w
  else findHT (w * cycPow n 2 k (jacobiSumT n 2 k q f (2 ^ (k - 3)) (3 * 2 ^ (k - 3))) (AzNat.ofNat 2))

/-- **The `(p, q)` test dispatch** on `k = v_p(q − 1)`. -/
def jTest (p k q : ℕ) (f : ℕ → ℕ) : Option ℕ :=
  if p = 2 then
    if k = 1 then j2k1 n q else if k = 2 then j2k2 n q f else j2k3 n k q f
  else jOdd n p k q f

/-! ### Guards (`n = 1000003`, prime) -/

section Guards

private abbrev N₀ : AzNat := AzNat.ofNat 1000003

instance : Fact (1 < N₀.toNat) := ⟨by rw [AzNat.toNat_ofNat]; norm_num⟩

-- `p = 3, q = 7` (`k = 1`), `p = 3, q = 19` (`k = 2`), `p = 5, q = 11`, `p = 7, q = 29`
#guard (jOdd N₀ 3 1 7 (indexTable 7 3)).isSome
#guard (jOdd N₀ 3 2 19 (indexTable 19 2)).isSome
#guard (jOdd N₀ 5 1 11 (indexTable 11 2)).isSome
#guard (jOdd N₀ 7 1 29 (indexTable 29 2)).isSome
-- `p = 2`: `q = 7` (`k = 1`), `q = 13` (`k = 2`), `q = 17` (`k = 4`), `q = 41` (`k = 3`)
#guard (j2k1 N₀ 7).isSome
#guard (j2k2 N₀ 13 (indexTable 13 2)).isSome
#guard (j2k3 N₀ 4 17 (indexTable 17 3)).isSome
#guard (j2k3 N₀ 3 41 (indexTable 41 6)).isSome
#guard (jTest N₀ 2 4 17 (indexTable 17 3)).isSome

end Guards

end APRCL

end Azurite
