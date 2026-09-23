/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

/-!
# Root Negation

Computes `P(−X)` for a univariate polynomial `P ∈ R[X]`: the roots of the result
are the roots of `P`, each negated. (The name `negate` is taken by coefficient
negation `-P`, which has the *same* roots; this operation negates the roots.)

Implemented as the O(n) alternate-sign coefficient map — the coefficient of `X^i`
is multiplied by `(−1)^i` — with no polynomial composition. Negation preserves
zeroness of each coefficient, so the trailing-nonzero invariant is preserved
without renormalizing, and the degree is unchanged definitionally.

## Main definitions

- `AzPolynomial.negateRoots p` — computes `P(−X)`

Basic coefficient-level facts (`coeff_negateRoots`, `natDegree_negateRoots`,
`leadingCoeff_negateRoots`, `negateRoots_zero`) are proved here; the `toPoly`
bridge and the root-negation property live in `Equiv/NegateRoots.lean`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Ring R]

private lemma Array_back?_mapIdx {α β : Type _} (a : Array α) (f : ℕ → α → β) :
    (a.mapIdx f).back? = Option.map (f (a.size - 1)) a.back? := by
  unfold Array.back?
  rw [Array.size_mapIdx, Array.getElem?_mapIdx]

/-- **Root negation.** Computes `P(−X)` by negating the odd-index coefficients.
The roots of the result are the roots of `P`, each negated. -/
def negateRoots (p : AzPolynomial R) : AzPolynomial R :=
  ⟨p.coeffs.mapIdx (fun i a => if i % 2 = 1 then -a else a), by
    intro h
    rw [Array_back?_mapIdx] at h
    rcases hb : p.coeffs.back? with _ | b
    · rw [hb, Option.map_none] at h; simp at h
    · rw [hb] at h
      simp only [Option.map_some] at h
      have hb0 : b = 0 := by
        have h' := Option.some.inj h
        split at h'
        · exact neg_eq_zero.mp h'
        · exact h'
      exact p.last_ne_zero (by rw [hb, hb0])⟩

/-- The coefficient of `X^n` in `P(−X)` is `(−1)^n` times that of `P`. -/
@[simp] theorem coeff_negateRoots (p : AzPolynomial R) (n : ℕ) :
    (p.negateRoots).coeff n = (-1) ^ n * p.coeff n := by
  show ((p.coeffs.mapIdx (fun i a => if i % 2 = 1 then -a else a))[n]?).getD 0 = _
  rw [Array.getElem?_mapIdx]
  rcases hb : p.coeffs[n]? with _ | b
  · simp [AzPolynomial.coeff, hb]
  · simp only [Option.map_some, Option.getD_some, AzPolynomial.coeff, hb]
    rcases Nat.even_or_odd n with he | ho
    · have h2 := Nat.even_iff.mp he
      rw [ite_eq_right (by omega : ¬ n % 2 = 1), he.neg_one_pow, one_mul]
    · rw [ite_eq_left (Nat.odd_iff.mp ho), ho.neg_one_pow, neg_one_mul]

/-- Root negation preserves the degree (the coefficient array size is unchanged). -/
theorem natDegree_negateRoots (p : AzPolynomial R) :
    (p.negateRoots).natDegree = p.natDegree := by
  show (p.coeffs.mapIdx _).size - 1 = p.coeffs.size - 1
  rw [Array.size_mapIdx]

/-- The leading coefficient of `P(−X)` is `(−1)^(deg P)` times that of `P`. -/
theorem leadingCoeff_negateRoots (p : AzPolynomial R) :
    (p.negateRoots).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  show (p.negateRoots).coeff (p.negateRoots).natDegree = _
  rw [natDegree_negateRoots, coeff_negateRoots]
  rfl

@[simp] theorem negateRoots_zero : (0 : AzPolynomial R).negateRoots = 0 :=
  AzPolynomial.ext rfl

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- (x+1)(x+2) = x² + 3x + 2 with roots −1, −2 becomes (x−1)(x−2) = x² − 3x + 2
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+3*x+2").get!.negateRoots)
    == "x^2-3*x+2"

-- Odd degree flips the sign of the polynomial: x³ ↦ −x³
#guard toChars ((parseAzPolynomial (R := AzInt) "x^3").get!.negateRoots)
    == "-x^3"

-- Root 5 becomes root −5 (up to overall sign): x − 5 ↦ −x − 5
#guard toChars ((parseAzPolynomial (R := AzInt) "x-5").get!.negateRoots)
    == "-x-5"

-- Constants unchanged
#guard toChars ((parseAzPolynomial (R := AzInt) "7").get!.negateRoots)
    == "7"

-- Zero unchanged
#guard toChars ((0 : AzPolynomial AzInt).negateRoots) == "0"

-- Involution
#guard toChars ((parseAzPolynomial (R := AzInt) "x^4-2*x^3+x-11").get!.negateRoots.negateRoots)
    == "x^4-2*x^3+x-11"

end Tests

end Azurite.AzPolynomial
