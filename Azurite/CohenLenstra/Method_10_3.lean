/-
  **Cohen–Lenstra §10, Method (10.3): the ideal `𝔪 = ker λ` for a
  homomorphism `λ : ℤ[ζ_{p^k}] → F`.**

  The second construction avoids the large coefficients of (10.2)'s
  `h`: build a ring `F` with `n^f` elements containing `ℤ/nℤ`
  (a field when `n` is prime, e.g. `F = (ℤ/n)[T]/(g)` for `g` monic
  of degree `f` with small coefficients), a ring endomorphism
  `ρ : F → F` (which is `α ↦ α^n` when `n` is prime), and an element
  `β ∈ F` passing the checks (10.4):

    `β^(n^f−1) = 1`,  `β^((n^f−1)/p) − 1 ∈ F^*`,  `ρ(β) = β^n`.

  Then `ζ̄ = β^((n^f−1)/p^k)` is a zero of
  `Σ_{i<p} X^(i·p^(k−1)) = Φ_{p^k}`, so `λ(ζ_{p^k}) = ζ̄` defines
  `λ : ℤ[ζ_{p^k}] → F` with `λ ∘ σ_n = ρ ∘ λ`, and `𝔪 = ker λ`
  satisfies (10.1).  No generators of `𝔪` are needed: congruences
  mod `𝔪` are checked by applying `λ` and comparing in `F`.

  Formalized over `CycM m` with `F` an abstract commutative ring:

  * `eval₂_cyclotomic_prime_pow_eq_zero` — the `ζ̄`-root lemma:
    `(ζ̄^(p^(k−1)) − 1)·Σ_i ζ̄^(i·p^(k−1)) = ζ̄^(p^k) − 1 = 0` and the
    first factor is a *unit* (this is why (10.4) demands a unit, not
    mere nonvanishing), via `cyclotomic_prime_pow_eq_geom_sum` and
    `geom_sum_mul`.
  * `lambdaHom` — `λ` by `AdjoinRoot.lift`; `mKernel = ker λ`.
  * `natCast_mem_mKernel` / `mKernel_natCast_imp_dvd` — the
    (10.1)-condition `𝔪 ∩ ℤ = nℤ` from `ℤ/nℤ ⊆ F`, rendered as the
    two hypotheses `(n : F) = 0` and `(a : F) = 0 → n ∣ a`.
  * `lambdaHom_sigmaN` — the intertwining `λ ∘ σ_n = ρ ∘ λ` from
    `ρ(ζ̄) = ζ̄^n` (which follows from `ρ(β) = β^n`: `rho_pow`);
    `mKernel_sigmaN_mem` / `mKernel_sigmaN_map_eq` give σ-stability,
    the equality again via the finite-order upgrade
    `map_sigmaN_eq_of_mem` of Method (10.2).

  Deferred: surjectivity of `λ` (hence `ℤ[ζ_{p^k}]/𝔪 ≅ F`) awaits
  (10.5), per the paper.  The computable instantiation
  (`F` = our `AzPolyMod` quotient rings; unit-recognition by the
  Euclidean algorithm = our `gcdOrFactor`, which factors `n` on
  failure exactly as the paper remarks; irreducibility of `g` for
  prime `n` = our Ben-Or `irreducibleOrFactor`) is §12–13 material.
-/
import Azurite.CohenLenstra.Method_10_2

namespace Azurite

namespace CL

open Polynomial Azurite.CP

variable {F : Type _} [CommRing F] {m n : ℕ}

/-- Any ring homomorphism commutes with evaluation of an integer
polynomial. -/
theorem ringHom_aeval {A B : Type _} [CommRing A] [CommRing B]
    (φ : A →+* B) (x : A) (U : Polynomial ℤ) :
    φ (aeval x U) = aeval (φ x) U :=
  (Polynomial.aeval_algHom_apply φ.toIntAlgHom x U).symm

/-- **The `ζ̄`-root lemma of (10.3)**: if `β^N = 1` and
`β^(N/P) − 1` is a *unit* (`P^k ∣ N`), then `ζ̄ = β^(N/P^k)` is a
zero of `Φ_(P^k)`: the geometric sum
`Σ_{i<P} ζ̄^(i·P^(k−1))` times the unit is `ζ̄^(P^k) − 1 = 0`. -/
theorem eval₂_cyclotomic_prime_pow_eq_zero {P k N : ℕ} (hp : P.Prime)
    (hk : 0 < k) {β : F} (hdvd : P ^ k ∣ N) (hβN : β ^ N = 1)
    (hunit : IsUnit (β ^ (N / P) - 1)) :
    Polynomial.eval₂ (Int.castRingHom F) (β ^ (N / P ^ k))
      (cyclotomic (P ^ k) ℤ) = 0 := by
  obtain ⟨t, rfl⟩ := hdvd
  have hP0 : 0 < P := hp.pos
  have hPk0 : (0 : ℕ) < P ^ k := pow_pos hP0 k
  have hsplit : P ^ k = P * P ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hNP : P ^ k * t / P = P ^ (k - 1) * t := by
    rw [hsplit, mul_assoc, Nat.mul_div_cancel_left _ hP0]
  rw [Nat.mul_div_cancel_left t hPk0]
  -- the cyclotomic polynomial as a geometric sum
  have hcyc : cyclotomic (P ^ k) ℤ
      = ∑ i ∈ Finset.range P, (X ^ P ^ (k - 1)) ^ i := by
    have hgs := cyclotomic_prime_pow_eq_geom_sum (R := ℤ)
      (n := k - 1) hp
    rwa [show k - 1 + 1 = k from by omega] at hgs
  rw [hcyc, Polynomial.eval₂_finsetSum]
  have hterm : ∀ i, Polynomial.eval₂ (Int.castRingHom F) (β ^ t)
      ((X ^ P ^ (k - 1)) ^ i) = ((β ^ t) ^ P ^ (k - 1)) ^ i := by
    intro i
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X_pow]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- kill the geometric sum against the unit `w − 1`
  set w := (β ^ t) ^ P ^ (k - 1) with hw
  have hwP : w ^ P = 1 := by
    rw [hw, ← pow_mul, ← pow_mul]
    rw [show t * (P ^ (k - 1) * P) = P ^ k * t from by
      rw [← pow_succ, show k - 1 + 1 = k from by omega]
      ring]
    exact hβN
  have hwunit : IsUnit (w - 1) := by
    have hwe : w = β ^ (P ^ k * t / P) := by
      rw [hw, ← pow_mul, hNP]
      congr 1
      ring
    rw [hwe]
    exact hunit
  have hgeom := geom_sum_mul w P
  rw [hwP, sub_self] at hgeom
  exact (IsUnit.mul_left_eq_zero hwunit).mp hgeom

/-! ### The homomorphism `λ` and its kernel -/

/-- **The paper's `λ : ℤ[ζ_m] → F`**, determined by `ζ_m ↦ z` for a
zero `z` of `Φ_m` in `F`. -/
noncomputable def lambdaHom (m : ℕ) {z : F}
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0) :
    CycM m →+* F :=
  AdjoinRoot.lift (Int.castRingHom F) z hz

variable {z : F}
  {hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0}

theorem lambdaHom_zetaM
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0) :
    lambdaHom m hz (zetaM m) = z :=
  AdjoinRoot.lift_root hz

/-- **The paper's `𝔪 = ker λ`.**  No generators are needed:
membership is checked by applying `λ`. -/
noncomputable def mKernel (m : ℕ) {z : F}
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0) :
    Ideal (CycM m) :=
  RingHom.ker (lambdaHom m hz)

/-- `n ∈ 𝔪`, from `(n : F) = 0` (i.e. `ℤ/nℤ ⊆ F`). -/
theorem natCast_mem_mKernel
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0)
    (hn0 : ((n : ℕ) : F) = 0) :
    ((n : ℕ) : CycM m) ∈ mKernel m hz := by
  rw [mKernel, RingHom.mem_ker, map_natCast]
  exact hn0

/-- **`𝔪 ∩ ℤ = nℤ`** (the first (10.1)-condition, in the
`hIZ`-shape of Theorem (7.8)), from the faithfulness of
`ℤ/nℤ ⊆ F`. -/
theorem mKernel_natCast_imp_dvd
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0)
    (hchar : ∀ a : ℕ, ((a : ℕ) : F) = 0 → n ∣ a) :
    ∀ a : ℕ, ((a : ℕ) : CycM m) ∈ mKernel m hz → n ∣ a := by
  intro a ha
  rw [mKernel, RingHom.mem_ker, map_natCast] at ha
  exact hchar a ha

/-- `ρ(β) = β^n` propagates to every power of `β`. -/
theorem rho_pow (ρ : F →+* F) {β : F} (hρβ : ρ β = β ^ n) (s : ℕ) :
    ρ (β ^ s) = (β ^ s) ^ n := by
  rw [map_pow, hρβ, ← pow_mul, ← pow_mul, mul_comm]

/-- **The intertwining `λ ∘ σ_n = ρ ∘ λ`**, from `ρ(z) = z^n`. -/
theorem lambdaHom_sigmaN (hm : 0 < m) (hco : Nat.Coprime n m)
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0)
    (ρ : F →+* F) (hρz : ρ z = z ^ n) (α : CycM m) :
    lambdaHom m hz (sigmaN hm hco α) = ρ (lambdaHom m hz α) := by
  obtain ⟨U, rfl⟩ := exists_aeval_rep α
  have h1 : lambdaHom m hz (aeval (zetaM m ^ n) U)
      = aeval (lambdaHom m hz (zetaM m ^ n)) U := ringHom_aeval _ _ _
  have h2 : lambdaHom m hz (aeval (zetaM m) U)
      = aeval (lambdaHom m hz (zetaM m)) U := ringHom_aeval _ _ _
  have h3 : ρ (aeval z U) = aeval (ρ z) U := ringHom_aeval _ _ _
  rw [sigmaN_aeval, sigmaN_zetaM, h1, h2, map_pow, lambdaHom_zetaM,
    h3, hρz]

/-- σ-stability of `𝔪 = ker λ` (the `hσI`-shape of
Theorem (7.8)). -/
theorem mKernel_sigmaN_mem (hm : 0 < m) (hco : Nat.Coprime n m)
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0)
    (ρ : F →+* F) (hρz : ρ z = z ^ n) :
    ∀ x ∈ mKernel m hz, sigmaN hm hco x ∈ mKernel m hz := by
  intro x hx
  rw [mKernel, RingHom.mem_ker] at hx ⊢
  rw [lambdaHom_sigmaN hm hco hz ρ hρz, hx, map_zero]

/-- **The second (10.1)-condition** `σ_n[𝔪] = 𝔪` for `𝔪 = ker λ`,
by the finite-order upgrade. -/
theorem mKernel_sigmaN_map_eq (hm : 0 < m) (hco : Nat.Coprime n m)
    (hz : Polynomial.eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0)
    (ρ : F →+* F) (hρz : ρ z = z ^ n) :
    Ideal.map (sigmaN hm hco) (mKernel m hz) = mKernel m hz :=
  map_sigmaN_eq_of_mem hm hco _ (mKernel_sigmaN_mem hm hco hz ρ hρz)

end CL

end Azurite
