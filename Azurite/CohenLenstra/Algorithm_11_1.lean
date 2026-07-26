/-
  **Cohen–Lenstra (11.1): the central stage of the algorithm.**

  The second stage receives `n > 1` and `t, s` satisfying
  (2.1)–(2.4) with `gcd(st, n) = 1`, and either proves `n`
  composite or proves (2.5).  Its three steps, mapped onto the
  formal inventory:

  (a) For every prime power `p^k ∥ t`, select an ideal
      `𝔪_{p,k} ⊆ ℤ[ζ_{p^k}]` satisfying (10.1) — either the
      trivial `𝔪 = nℤ[ζ_{p^k}]` or one produced by Methods
      (10.2)/(10.3) (`mIdeal`, `mKernel`).  This file supplies the
      fallback: the trivial ideal always satisfies (10.1)
      (`span_natCast_natCast_imp_dvd`, `span_natCast_sigmaN_mem`,
      `span_natCast_sigmaN_map_eq`) — no luck required, at the
      price of the largest quotient.

  (b) For every `χ = χ_{p,q} ∈ Y_s` (our `Characters.lean`
      inventory), verify (7.9) by the Jacobi-sum congruences:
      (8.8) via Theorem (8.5) for odd `p`, and (9.2)/(9.4)/(9.6)/
      (9.11)/(9.20) via Theorems (9.1)–(9.19) for `p = 2`.  A
      failed congruence proves `n` composite and the algorithm
      halts — the soundness halves are `theorem_8_5`,
      `theorem_9_1`, `theorem_9_3`, `theorem_9_5`,
      `theorem_9_10`, `theorem_9_19`.

  (c) For every prime `p ∣ t`, establish condition (6.4) — by the
      procedures (11.2) (odd `p`) and (11.5) (`p = 2`), which
      draw on Propositions (7.18)/(7.24)/(7.25)/(10.7)/(10.8) and
      Theorem (7.19).  Theorem (7.8) then upgrades each verified
      (7.9) to the character condition (6.5), and Theorem (6.3)
      concludes (2.5).

  The detailed procedures (11.2)–(11.5) and the assembly of the
  `(7.8) ⟹ (6.5) ⟹ (6.3)`-chain (the `χ(n) = η` alignment across
  the prime divisors of `s`) follow with the next pieces of the
  paper.
-/
import Azurite.CohenLenstra.Method_10_2

namespace Azurite

namespace CL

open Azurite.CP

variable {m n : ℕ}

/-- **The (11.1)(a) fallback, first (10.1)-condition**: the trivial
ideal `nℤ[ζ_m]` meets `ℤ` in `nℤ` — in the `hIZ`-shape of
Theorem (7.8), via the faithfulness of the integers in the
model. -/
theorem span_natCast_natCast_imp_dvd (hm : 0 < m) :
    ∀ a : ℕ, ((a : ℕ) : CycM m) ∈ Ideal.span {((n : ℕ) : CycM m)}
      → n ∣ a := by
  intro a ha
  rw [Ideal.mem_span_singleton] at ha
  exact (natCast_dvd_natCast_iff_cycM hm n a).mp ha

/-- **The (11.1)(a) fallback, σ-stability inclusion**: `σ_n` maps
`nℤ[ζ_m]` into itself. -/
theorem span_natCast_sigmaN_mem (hm : 0 < m) (hco : Nat.Coprime n m) :
    ∀ x ∈ Ideal.span {((n : ℕ) : CycM m)},
      sigmaN hm hco x ∈ Ideal.span {((n : ℕ) : CycM m)} := by
  intro x hx
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_natCast]
  exact Dvd.intro _ rfl

/-- **The (11.1)(a) fallback, second (10.1)-condition**:
`σ_n[nℤ[ζ_m]] = nℤ[ζ_m]`, by the finite-order upgrade of
Method (10.2). -/
theorem span_natCast_sigmaN_map_eq (hm : 0 < m)
    (hco : Nat.Coprime n m) :
    Ideal.map (sigmaN hm hco) (Ideal.span {((n : ℕ) : CycM m)})
      = Ideal.span {((n : ℕ) : CycM m)} :=
  map_sigmaN_eq_of_mem hm hco _ (span_natCast_sigmaN_mem hm hco)

end CL

end Azurite
