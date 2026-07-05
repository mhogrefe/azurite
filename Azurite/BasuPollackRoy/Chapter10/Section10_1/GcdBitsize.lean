import Azurite.BasuPollackRoy.Chapter10.Section10_1.Corollary_10_12

/-!
# Bitsize of Algorithm 10.1's outputs over `ℤ`

BPR (after Algorithm 10.1): when `P ∈ ℤ[X]` with the bitsizes of its
coefficients bounded by `τ`, using Corollary 10.12, the bitsize of the output
is `j + τ + bit(p+1)` (the gcd, of degree `j`) and `p − j + τ + bit(p+1)`
(the gcd-free part, of degree `p − j`).

Both bounds are immediate from Corollary 10.12 because both outputs — in the
exactly-normalized form computed by `gcd`/`gcdGcdFreePart` over `AzInt` —
are genuine divisors of `P`:

* `gcd_coeff_bitsize` — the gcd divides `P`, so its coefficients have
  bitsize at most `j + τ + bit(p+1)`;
* `gcdFreePart_coeff_bitsize` — the gcd-free part `D` (the exact cofactor,
  `gcd(P,Q)·D = P`) divides `P` and has degree `p − j`, so its coefficients
  have bitsize at most `(p − j) + τ + bit(p+1)`.

(BPR's raw outputs `a_p·sResP_j/s_j` and `a_p·sResV_{j−1}/lcof` carry an
additional factor `a_p`, so read literally their coefficients can be up to
`τ` bits larger; the bounds hold exactly for the normalized divisors.)
-/

namespace Azurite.BPR

open Polynomial

/-- **Bitsize of the gcd output.** If the coefficients of `P ≠ 0` have
bitsize at most `τ` and `deg(gcd(P, Q)) = j`, then every coefficient of
`gcd(P, Q)` has bitsize at most `j + τ + bit(p+1)`. -/
theorem gcd_coeff_bitsize {P Q : ℤ[X]} (hP : P ≠ 0) {τ : ℕ}
    (hτ : ∀ i, (P.coeff i).natAbs.size ≤ τ) {j : ℕ}
    (hj : (GCDMonoid.gcd P Q).natDegree = j) (i : ℕ) :
    ((GCDMonoid.gcd P Q).coeff i).natAbs.size
      ≤ j + τ + Nat.size (P.natDegree + 1) := by
  have h := corollary_10_12 hP (gcd_dvd_left P Q) hτ i
  rwa [hj] at h

/-- **Bitsize of the gcd-free-part output.** If the coefficients of `P ≠ 0`
have bitsize at most `τ`, `deg(gcd(P, Q)) = j`, and `D` is the exact
cofactor (`gcd(P, Q) · D = P`, as returned by `gcdGcdFreePart`), then every
coefficient of `D` has bitsize at most `(p − j) + τ + bit(p+1)`. -/
theorem gcdFreePart_coeff_bitsize {P Q D : ℤ[X]} (hP : P ≠ 0) {τ : ℕ}
    (hτ : ∀ i, (P.coeff i).natAbs.size ≤ τ) {j : ℕ}
    (hj : (GCDMonoid.gcd P Q).natDegree = j)
    (hD : GCDMonoid.gcd P Q * D = P) (i : ℕ) :
    (D.coeff i).natAbs.size
      ≤ (P.natDegree - j) + τ + Nat.size (P.natDegree + 1) := by
  have hDdvd : D ∣ P := Dvd.intro_left _ hD
  have hgcd0 : GCDMonoid.gcd P Q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hD
    exact hP hD.symm
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, mul_zero] at hD
    exact hP hD.symm
  -- the degrees add along `gcd · D = P`
  have hdeg : D.natDegree = P.natDegree - j := by
    have h1 := congrArg Polynomial.natDegree hD
    rw [Polynomial.natDegree_mul hgcd0 hD0, hj] at h1
    omega
  have h := corollary_10_12 hP hDdvd hτ i
  rwa [hdeg] at h

end Azurite.BPR
