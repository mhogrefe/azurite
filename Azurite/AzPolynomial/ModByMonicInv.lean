/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.DivModByMonic

/-!
# Remainder modulo a monic polynomial by a precomputed inverse

For a monic `f` of degree `d`, the reversed polynomial `Xᵈ f(1/X)` has constant term `1`, so
it has an inverse `g` modulo `X^(d−1)` as a power series (`invRev f`, computed once).  For
`P` of degree at most `2d − 2` — a product of two reduced residues — the quotient of `P` by
`f` is then read off one product: its reversal is `rev(P) · g mod X^(d−1)`, which only
involves the top `d − 1` coefficients of `P`; and the remainder is `P − q · f`.  Two
polynomial products per reduction instead of the `d²` coefficient operations of the
schoolbook division.

`modByMonicInv f g P` falls back to `modByMonic` outside the range above, and equals
`modByMonic P f` for monic `f` and `g = invRev f` (`Equiv/ModByMonicInv.lean`).
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- `h 0 + ⋯ + h (n − 1)`. -/
def sumTo (h : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => sumTo h n + h n

/-- The power-series inverse of the reversed `f`, one coefficient at a time: with
`aₘ = f.coeff (d − m)` (so `a₀ = 1` for monic `f` of degree `d`),
`g_k = −(a₁ g_(k−1) + ⋯ + a_k g₀)`. -/
def invRevCoeffs (f : AzPolynomial R) (d : ℕ) : ℕ → Array R → Array R
  | 0, g => g
  | n + 1, g =>
    invRevCoeffs f d n
      (g.push (-(sumTo (fun i => f.coeff (d - (i + 1)) * (g[g.size - (i + 1)]?).getD 0) g.size)))

/-- **The inverse of the reversed `f` modulo `X^(d−1)`**, for monic `f` of degree `d`. -/
def invRev (f : AzPolynomial R) : AzPolynomial R :=
  normalize (invRevCoeffs f f.natDegree (f.natDegree - 2) #[1])

variable [AzPolynomialMulConfig R]

/-- The quotient of `P` (of degree at most `2d − 2`) by the monic `f` of degree `d`, from the
inverse `g` of the reversed `f`. -/
def quotByInv (g P : AzPolynomial R) (d : ℕ) : AzPolynomial R :=
  let H : AzPolynomial R :=
    normalize (Array.ofFn fun (i : Fin (d - 1)) => P.coeff (2 * d - 2 - i.val))
  let T := H * g
  normalize (Array.ofFn fun (i : Fin (d - 1)) => T.coeff (d - 2 - i.val))

/-- **The remainder of `P` modulo the monic `f`, by the inverse `g` of the reversed `f`**:
`P − q · f` with `q` from `quotByInv`, when `deg f ≥ 1` and `deg f ≤ deg P ≤ 2 deg f − 2`;
`modByMonic P f` otherwise. -/
def modByMonicInv (f g P : AzPolynomial R) : AzPolynomial R :=
  if f.coeffs.size < 2 ∨ P.coeffs.size < f.coeffs.size ∨
      2 * f.natDegree - 1 < P.coeffs.size then
    modByMonic P f
  else P - quotByInv g P f.natDegree * f

-- ── Tests ───────────────────────────────────────────────────────────────────

/-- A monic test polynomial of degree `d`, and a test polynomial with `len` coefficients. -/
private def tMonic (d seed : Nat) : AzPolynomial AzInt :=
  monomial d 1 + normalize ((Array.range d).map fun (i : Nat) =>
    AzInt.ofInt (((i : Int) * 37 + seed) % 23 - 11))

private def tPoly (len seed : Nat) : AzPolynomial AzInt :=
  normalize ((Array.range len).map fun (i : Nat) =>
    AzInt.ofInt (((i : Int) * (i : Int) * 5 + (i : Int) * seed + 3) % 41 - 20))

/-- The remainder by the inverse against the second component of `divModByMonic`. -/
private def invAgrees (d lenP : Nat) : Bool :=
  let f := tMonic d 4
  let P := tPoly lenP 9
  modByMonicInv f (invRev f) P == (divModByMonic P f).2

#guard invAgrees 2 3
#guard invAgrees 3 4
#guard invAgrees 3 5
#guard invAgrees 5 6
#guard invAgrees 5 9
#guard invAgrees 20 21
#guard invAgrees 20 30
#guard invAgrees 20 39
-- outside the range: reduced already, too long, and degree one
#guard invAgrees 20 12
#guard invAgrees 20 45
#guard invAgrees 1 2
#guard invAgrees 1 7
-- products of two reduced residues
#guard (List.range 6).all fun k =>
  let f := tMonic 17 k
  let P := tPoly 17 (k + 1) * tPoly 16 (k + 2)
  modByMonicInv f (invRev f) P == (divModByMonic P f).2

end Azurite.AzPolynomial
