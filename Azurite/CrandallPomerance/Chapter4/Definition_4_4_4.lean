/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Definition 4.4.4: the content `c(α)` of an
  element of `ℤ[ζ_p, ζ_q]` — the gcd of its coefficients in the
  standard representation
  `α = ∑_(i≤p−2) ∑_(k≤q−2) a_(ik) ζ_p^i ζ_q^k`, with `c(0) = 0`.

  This is where the book's ring `ℤ[ζ_p, ζ_q]` needs a concrete model:
  we build it as the SYMBOLIC tower the book itself prescribes —
  `CycPQ p q := ℤ[x]/(Φ_p)[y]/(Φ_q)` via a double `AdjoinRoot` (for
  primes, `Φ_m = 1 + x + ⋯ + x^(m−1)`, `Polynomial.cyclotomic_prime`).
  The book's UNIQUE-REPRESENTATION claim is then a theorem for free:
  the product of the two monic power bases is a `ℤ`-basis of the
  tower (`cycBasis`, via `AdjoinRoot.powerBasis'` and
  `Basis.smulTower`), whose basis vectors are exactly the monomials
  `ζ_p^i ζ_q^k` (`cycBasis_apply`).

  The content is the gcd of the coordinate grid (`content`; the
  `c(0) = 0` convention is automatic, the gcd of zeros being `0`).
  Its raison d'être is `natCast_dvd_iff_dvd_content`: divisibility by
  `n` IN THE RING is divisibility of the content — the bridge between
  the ring-divisibility congruences of Lemmas 4.4.1–4.4.3 and the
  book's coefficientwise congruence mod `n`.

  Deferred (until the Gauss sums test needs them): `IsDomain (CycPQ p q)`
  and primitivity of `zetaP`/`zetaQ` — the facts that connect this
  model to the abstract-`R` lemmas; they amount to the irreducibility
  of `Φ_q` over `ℤ[ζ_p]` for distinct primes.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower

namespace Azurite

namespace CP

open Polynomial Module

variable (p q : ℕ)

/-- The symbolic model of `ℤ[ζ_p]`: adjoin a root of the cyclotomic
polynomial (for `p` prime, `1 + x + ⋯ + x^(p−1)`). -/
abbrev CycP := AdjoinRoot (cyclotomic p ℤ)

/-- The symbolic model of `ℤ[ζ_p, ζ_q]`: adjoin a root of `Φ_q` over
`ℤ[ζ_p]`. -/
abbrev CycPQ := AdjoinRoot (cyclotomic q (CycP p))

/-- The symbol `ζ_p` in the tower. -/
noncomputable def zetaP : CycPQ p q :=
  algebraMap (CycP p) (CycPQ p q) (AdjoinRoot.root (cyclotomic p ℤ))

/-- The symbol `ζ_q` in the tower. -/
noncomputable def zetaQ : CycPQ p q := AdjoinRoot.root (cyclotomic q (CycP p))

section Basis

variable [Fact p.Prime] [Fact q.Prime]

/-- The power basis `1, ζ_p, …, ζ_p^(p−2)` of `ℤ[ζ_p]` over `ℤ`. -/
noncomputable def cycPBasis : Basis (Fin (p - 1)) ℤ (CycP p) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic p ℤ)).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic,
        Nat.totient_prime (Fact.out (p := p.Prime))]))

instance : Nontrivial (CycP p) := by
  have hb := (cycPBasis p).ne_zero ⟨0, by
    have := (Fact.out (p := p.Prime)).two_le
    omega⟩
  exact nontrivial_of_ne _ _ hb

/-- The power basis `1, ζ_q, …, ζ_q^(q−2)` of the tower over
`ℤ[ζ_p]`. -/
noncomputable def cycQBasis : Basis (Fin (q - 1)) (CycP p) (CycPQ p q) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic q (CycP p))).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic,
        Nat.totient_prime (Fact.out (p := q.Prime))]))

/-- **The book's unique representation** (Definition 4.4.4's setup):
the monomials `ζ_p^i ζ_q^k` (`i ≤ p−2`, `k ≤ q−2`) form a `ℤ`-basis
of `ℤ[ζ_p, ζ_q]`. -/
noncomputable def cycBasis :
    Basis (Fin (p - 1) × Fin (q - 1)) ℤ (CycPQ p q) :=
  (cycPBasis p).smulTower (cycQBasis p q)

/-- The basis vectors are the book's monomials. -/
theorem cycBasis_apply (i : Fin (p - 1)) (k : Fin (q - 1)) :
    cycBasis p q (i, k) = zetaP p q ^ (i : ℕ) * zetaQ p q ^ (k : ℕ) := by
  rw [cycBasis, Basis.smulTower_apply]
  rw [Algebra.smul_def]
  congr 1
  · rw [cycPBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen, map_pow]
    rfl
  · rw [cycQBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen]
    rfl

/-- **Definition 4.4.4**: the content `c(α)` — the gcd of the
coefficients in the standard representation (`c(0) = 0` is automatic:
the gcd of an all-zero family is `0`). -/
noncomputable def content (α : CycPQ p q) : ℕ :=
  Finset.univ.gcd fun ik => ((cycBasis p q).repr α ik).natAbs

/-- **Congruence mod `n` is coefficientwise**: divisibility by `n` in
the ring `ℤ[ζ_p, ζ_q]` is divisibility of the content — the bridge
between the ring-divisibility congruences of Lemmas 4.4.1–4.4.3 and
the book's coefficientwise congruence. -/
theorem natCast_dvd_iff_dvd_content (n : ℕ) (α : CycPQ p q) :
    (n : CycPQ p q) ∣ α ↔ n ∣ content p q α := by
  constructor
  · rintro ⟨β, rfl⟩
    refine Finset.dvd_gcd fun ik _ => ?_
    have hsmul : (n : CycPQ p q) * β = (n : ℤ) • β := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [hsmul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul,
      Int.natAbs_natCast]
    exact Dvd.intro _ rfl
  · intro h
    have hall : ∀ ik, (n : ℤ) ∣ (cycBasis p q).repr α ik := by
      intro ik
      have h1 : n ∣ ((cycBasis p q).repr α ik).natAbs :=
        h.trans (Finset.gcd_dvd (Finset.mem_univ ik))
      have h2 : ((n : ℤ)).natAbs ∣ ((cycBasis p q).repr α ik).natAbs := by
        rwa [Int.natAbs_natCast]
      exact Int.natAbs_dvd_natAbs.mp h2
    refine ⟨∑ ik : Fin (p - 1) × Fin (q - 1),
      ((cycBasis p q).repr α ik / n) • cycBasis p q ik, ?_⟩
    conv_lhs => rw [← (cycBasis p q).sum_repr α]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ik _ => ?_
    have hzs : (n : CycPQ p q)
        * (((cycBasis p q).repr α ik / n) • cycBasis p q ik)
        = ((n : ℤ) * ((cycBasis p q).repr α ik / n)) • cycBasis p q ik := by
      simp only [← smul_smul, zsmul_eq_mul, Int.cast_natCast]
    rw [hzs, Int.mul_ediv_cancel' (hall ik)]

end Basis

end CP

end Azurite
