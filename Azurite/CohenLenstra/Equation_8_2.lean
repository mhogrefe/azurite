/-
  **Cohen–Lenstra §8, opening: Jacobi sums and the relation (8.2)/(8.3).**

  The purpose of the paper's §8 is to reformulate the tested
  congruence (7.9) so that it only involves elements of the subring
  `ℤ[ζ_{p^k}]` of `B` — Jacobi sums — rather than the Gauss sums,
  which live in the larger ring `ℤ[ζ_{p^k}, ζ_q]`.

  The Jacobi sum `j(χ^a, χ^b) = Σ_x χ^a(x)·χ^b(1−x)` is Mathlib's
  `jacobiSum (χ^a) (χ^b)`.  The paper's relations

    (8.2)  `j(χ^a, χ^b) = τ(χ^a)τ(χ^b)/τ(χ^(a+b))`
           (for `a + b ≢ 0 mod p^k`), and
    (8.3)  `j(χ^a, χ^b) = τ(χ)^(σ_a + σ_b − σ_(a+b))`
           (for `ab(a+b) ≢ 0 mod p`)

  coalesce, in our unit-free Galois-free rendering
  (`τ(χ)^(σ_x) = τ(χ^x)`), into the single multiplied-out identity

    `τ(χ^(a+b)) · j(χ^a, χ^b) = τ(χ^a) · τ(χ^b)`,

  which is Mathlib's `jacobiSum_mul_nontrivial` — cited by the paper
  to Washington and Ireland–Rosen, and needing only
  `χ^(a+b) ≠ 1`.  The structural point that `j(χ^a, χ^b)` lies in
  `ℤ[ζ_{p^k}]` is Mathlib's
  `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`, restated here for the
  power family of a character of order `p^k`.

  The paper's (8.4) introduces, for `p > 3`, the index set
  `M = {x : 1 ≤ x ≤ p^k, x ≢ 0 mod p}`; its formalization is
  deferred to the α/β-constructions of the following pieces that
  consume it.
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.GaussSum

namespace Azurite

namespace CL

open Finset

/-- **Cohen–Lenstra (8.2)/(8.3)**, unit-free: for a character `χ` of
order `p^k` mod `q` and exponents with `a + b ≢ 0 (mod p^k)`,

`τ(χ^(a+b), ψ) · j(χ^a, χ^b) = τ(χ^a, ψ) · τ(χ^b, ψ)`.

In the paper's notation this is
`j(χ^a, χ^b) = τ(χ)^(σ_a + σ_b − σ_(a+b))` after division by the
unit `τ(χ^(a+b))`. -/
theorem eq_8_2 {R : Type _} [CommRing R] [IsDomain R]
    {q p k : ℕ} [Fact q.Prime]
    {χ : MulChar (ZMod q) R} (hord : orderOf χ = p ^ k)
    (ψ : AddChar (ZMod q) R) {a b : ℕ} (hab : ¬ p ^ k ∣ a + b) :
    gaussSum (χ ^ (a + b)) ψ * jacobiSum (χ ^ a) (χ ^ b)
      = gaussSum (χ ^ a) ψ * gaussSum (χ ^ b) ψ := by
  have hne : χ ^ a * χ ^ b ≠ 1 := by
    rw [← pow_add]
    intro h1
    exact hab (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  have h := jacobiSum_mul_nontrivial hne ψ
  rwa [← pow_add] at h

/-- **Jacobi sums live in `ℤ[ζ_{p^k}]`**: for a character `χ` of
order `p^k` and a primitive `p^k`-th root of unity `μ` in a domain
`R`, every `j(χ^a, χ^b)` lies in the subring `ℤ[μ]` — the structural
fact that makes the Jacobi-sum reformulation computable without
`ζ_q`. -/
theorem jacobiSum_pow_mem {R : Type _} [CommRing R] [IsDomain R]
    {q p k : ℕ} [Fact q.Prime] [NeZero (p ^ k)]
    {χ : MulChar (ZMod q) R} (hord : orderOf χ = p ^ k)
    {μ : R} (hμ : IsPrimitiveRoot μ (p ^ k)) (a b : ℕ) :
    jacobiSum (χ ^ a) (χ ^ b) ∈ Algebra.adjoin ℤ {μ} := by
  have hχpk : χ ^ p ^ k = 1 := hord ▸ pow_orderOf_eq_one χ
  have hχa : (χ ^ a) ^ p ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hχpk, one_pow]
  have hχb : (χ ^ b) ^ p ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hχpk, one_pow]
  exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχa hχb hμ

end CL

end Azurite
