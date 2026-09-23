/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra Remarks (11.4): justification of Procedure
  (11.2).**

  (a) For non-`p`-th-power `n`, the primes `q` satisfying (11.3)
  have density `1/p` (splitting completely in `ℚ(ζ_p)` but not in
  `ℚ(ζ_p, n^(1/p))`, by the splitting-density theorem), and under
  GRH the least such `q` is `≤ c·p²(log p + log n)²`.  This is
  generator-side termination/runtime commentary — the checker only
  ever *verifies* a found `q` — and is recorded as prose.

  (b) The composite-verdicts of (11.2)(e).  The formal core, proved
  here: for a character `χ` mod `q` of order `p^k` and `q ∤ n`,
  condition (11.3) — `n^((q−1)/p) ≢ 1 (mod q)` — forces `χ(n)` to
  be a *primitive* `p^k`-th root of unity
  (`isPrimitiveRoot_chi_natCast`; writing `n = g^j` for a
  generator `g`, (11.3) says exactly `p ∤ j`, and `χ(g)` has order
  `p^k`).  Combined with the completeness half — a *prime* `n`
  satisfies (7.9) with `ζ = χ(n)^(-nβ)`-primitive, the
  (7.5)-side, deferred to the model-instantiation stage along
  with the other completeness halves — a failure of (7.9) with
  primitive `ζ` proves `n` composite; in particular so does the
  (11.2)(b)-discovered failure when `q ∣ s`.

  (c) Practical remark: parts (c)–(e) of (11.2) are rarely needed
  (e.g. when `n` is a prime congruent to a `p`-th power mod
  `p²s`), and for probable primes the search in (d) may be
  restricted to `q ∤ s`.  Prose.
-/
import Azurite.CohenLenstra.Characters

namespace Azurite

namespace CL

/-- **The (11.4)(b) character-value fact**: for `χ` of order `p^k`
mod `q` and `q ∤ n`, condition (11.3) — `n^((q−1)/p) ≢ 1 (mod q)`
— makes `χ(n)` a primitive `p^k`-th root of unity. -/
theorem isPrimitiveRoot_chi_natCast {R : Type _} [CommRing R]
    [IsDomain R] {q p k n : ℕ} [Fact q.Prime]
    {χ : MulChar (ZMod q) R}
    (hp : p.Prime) (hord : orderOf χ = p ^ k)
    (hdvd : p ∣ q - 1) (hqn : ¬ q ∣ n)
    (h113 : ((n : ℕ) : ZMod q) ^ ((q - 1) / p) ≠ 1) :
    IsPrimitiveRoot (χ ((n : ℕ) : ZMod q)) (p ^ k) := by
  have hq := Fact.out (p := q.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hgord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units]
  -- `χ(g)` has order exactly `p^k`
  have hχg_ord : orderOf (χ ↑g) = p ^ k := by
    have h1 : (χ ↑g) ^ p ^ k = 1 := by
      rw [← MulChar.pow_apply_coe, ← hord, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    have h2 : χ ^ orderOf (χ ↑g) = 1 := by
      refine MulChar.ext fun u => ?_
      rw [MulChar.one_apply_coe]
      obtain ⟨mm, hmm⟩ := mem_powers_iff_mem_zpowers.mpr (hg u)
      have hmm' : g ^ mm = u := hmm
      rw [MulChar.pow_apply_coe, ← hmm', Units.val_pow_eq_pow_val,
        map_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one,
        one_pow]
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1)
      (hord ▸ orderOf_dvd_of_pow_eq_one h2)
  have hχg : IsPrimitiveRoot (χ ↑g) (p ^ k) :=
    hχg_ord ▸ IsPrimitiveRoot.orderOf (χ ↑g)
  -- write `n = g^j`
  have hun : IsUnit ((n : ℕ) : ZMod q) := by
    refine (ZMod.isUnit_iff_coprime n q).mpr ?_
    exact ((hq.coprime_iff_not_dvd.mpr hqn)).symm
  obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.mpr (hg hun.unit)
  have hj' : g ^ j = hun.unit := hj
  have hcastn : ((n : ℕ) : ZMod q) = ↑(g ^ j) := by
    rw [hj', IsUnit.unit_spec]
  -- (11.3) says `p ∤ j`
  have hpj : ¬ p ∣ j := by
    rintro ⟨j', rfl⟩
    apply h113
    rw [hcastn, ← Units.val_pow_eq_pow_val, ← pow_mul]
    have hexp : g ^ (p * j' * ((q - 1) / p)) = 1 := by
      have he : p * j' * ((q - 1) / p) = (q - 1) * j' := by
        rw [mul_comm p j', mul_assoc, Nat.mul_div_cancel' hdvd]
        ring
      rw [he, pow_mul, ← hgord, pow_orderOf_eq_one, one_pow]
    rw [hexp, Units.val_one]
  -- conclude by coprime power
  have hχn : χ ((n : ℕ) : ZMod q) = (χ ↑g) ^ j := by
    rw [hcastn, Units.val_pow_eq_pow_val, map_pow]
  rw [hχn]
  exact hχg.pow_of_coprime j
    (Nat.Coprime.pow_right k ((hp.coprime_iff_not_dvd.mpr hpj).symm))

end CL

end Azurite
