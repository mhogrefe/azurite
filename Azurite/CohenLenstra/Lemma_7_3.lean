/-
  **Cohen–Lenstra Lemma (7.3): the Gauss-sum Frobenius congruence.**

  The paper works in `B = ℤ[ζ_{p^k}, ζ_q][1/q]` with the Galois group
  `G = Gal(K/ℚ(ζ_q)) ≅ (ℤ/p^k)^*` acting through `σ_x(ζ_{p^k}) =
  ζ_{p^k}^x`, and states (7.3) as: for prime `n`,

    `τ(χ)^(n − σ_n) ≡ χ(n)^(−n)  (mod nB)`.

  Two reductions make this statable in any commutative ring, with no
  Galois action and no localization at `q`:

  * `σ_n` fixes `ζ_q` and raises the character values (powers of
    `ζ_{p^k}`) to the `n`-th power, so `σ_n(τ(χ)) = τ(χ^n)` — the
    Galois twist of a Gauss sum is the Gauss sum of the powered
    character;
  * multiplying the paper's congruence by the unit
    `χ(n)^n · τ(χ)^{σ_n}` clears all inverses, leaving

    `χ(n)^n · τ(χ)^n ≡ τ(χ^n)  (mod n)`,

    which is exactly the displayed line of the paper's proof.  (The
    localization `B` exists in the paper only to make `τ(χ)` a unit;
    the unit-free form never needs it.)

  We prove that form, for an arbitrary multiplicative character `χ`
  and additive character `ψ` of `ℤ/q` with values in any commutative
  ring: `(1.3)` (freshman's dream in `R/nR`) gives
  `τ(χ,ψ)^n ≡ Σ_x χ(x)^n ψ(nx) = τ(χ^n, ψ.mulShift n)`, and
  Mathlib's `gaussSum_mulShift` converts the shifted sum at the cost
  of `(χ^n)(n)^(−1) = χ(n)^(−n)`, i.e. multiplied out:
  `(χ^n)(n) · τ(χ^n, ψ.mulShift n) = τ(χ^n, ψ)`.  This mirrors the
  quotient-ring Frobenius pattern of the Crandall–Pomerance
  Lemma 4.4.2 (which is the `k = 1` congruence for the exponent
  `n^(p−1) − 1`); the character here need not have prime-power order.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.Data.ZMod.Basic

namespace Azurite

namespace CL

open Finset

/-- **Cohen–Lenstra Lemma (7.3)**, unit-free form: for a prime `n`
not divisible by `q`, and any characters `χ` (multiplicative) and `ψ`
(additive) of `ℤ/q` with values in a commutative ring `R`,

`χ(n)^n · τ(χ,ψ)^n ≡ τ(χ^n, ψ)  (mod nR)`.

The paper's `τ(χ)^(n−σ_n) ≡ χ(n)^(−n) (mod nB)` follows by dividing
by the unit `χ(n)^n · τ(χ)^{σ_n}` in `B`, since `σ_n(τ(χ)) = τ(χ^n)`. -/
theorem lemma_7_3 {R : Type _} [CommRing R] {q n : ℕ} [Fact q.Prime]
    (hn : n.Prime) (hqn : ¬ q ∣ n)
    (χ : MulChar (ZMod q) R) (ψ : AddChar (ZMod q) R) :
    (n : R) ∣ χ (n : ZMod q) ^ n * gaussSum χ ψ ^ n - gaussSum (χ ^ n) ψ := by
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  have hnq0 : (n : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqn
  have hnu : IsUnit (n : ZMod q) := isUnit_iff_ne_zero.mpr hnq0
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set π := Ideal.Quotient.mk (Ideal.span {(n : R)}) with hπdef
  rcases subsingleton_or_nontrivial (R ⧸ Ideal.span {(n : R)}) with hS | hS
  · exact Subsingleton.elim _ _
  have hnS : ((n : ℕ) : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [show ((n : ℕ) : R ⧸ Ideal.span {(n : R)}) = π (n : R) from
      (map_natCast π n).symm, hπdef, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have : CharP (R ⧸ Ideal.span {(n : R)}) n := by
    have hdvd : ringChar (R ⧸ Ideal.span {(n : R)}) ∣ n := ringChar.dvd hnS
    rcases hn.eq_one_or_self_of_dvd _ hdvd with h1 | hcharn
    · exfalso
      have h0 := CharP.cast_eq_zero (R ⧸ Ideal.span {(n : R)})
        (ringChar (R ⧸ Ideal.span {(n : R)}))
      rw [h1, Nat.cast_one] at h0
      exact one_ne_zero h0
    · exact CharP.congr (ringChar (R ⧸ Ideal.span {(n : R)})) hcharn
  have : Fact n.Prime := ⟨hn⟩
  -- Frobenius: `π(τ(χ,ψ))^n = π(τ(χ^n, ψ.mulShift n))`
  have hfrob : π (gaussSum χ ψ) ^ n
      = π (gaussSum (χ ^ n) (ψ.mulShift ((hnu.unit : (ZMod q)ˣ) : ZMod q))) := by
    rw [gaussSum, gaussSum, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_pow, mul_pow, ← MulChar.pow_apply' χ hn.pos.ne' m,
      AddChar.mulShift_apply, IsUnit.unit_spec, ← nsmul_eq_mul,
      AddChar.map_nsmul_eq_pow]
  -- the shift costs exactly `(χ^n)(n)`
  have hshift := gaussSum_mulShift (χ ^ n) ψ hnu.unit
  have hfinal : π (χ (n : ZMod q) ^ n * gaussSum χ ψ ^ n)
      = π (gaussSum (χ ^ n) ψ) := by
    rw [map_mul, map_pow (π) (gaussSum χ ψ), hfrob, ← map_mul,
      show χ (n : ZMod q) ^ n
          = (χ ^ n) ((hnu.unit : (ZMod q)ˣ) : ZMod q) from by
        rw [IsUnit.unit_spec, MulChar.pow_apply' χ hn.pos.ne'],
      hshift]
  rw [map_sub, hfinal, sub_self]

end CL

end Azurite
