import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.2: Euclidean Division and Greatest Common Divisor

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

In this section, C is an algebraically closed field, D is a subring of C,
and K is the quotient field of D.

### Polynomial Basics in Mathlib

The **degree** of a polynomial is defined in `Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.degree : Polynomial R → WithBot ℕ :=
  fun p ↦ p.support.max
```

The degree uses `WithBot ℕ`, so the zero polynomial has degree `⊥` (minus infinity).
There is also `natDegree`, which maps `⊥` to `0`:

```
def Polynomial.natDegree : Polynomial R → ℕ :=
  fun p ↦ WithBot.unbotD 0 p.degree
```

The **coefficient** of Xⁿ in a polynomial is defined in
`Mathlib.Algebra.Polynomial.Defs`:

```
def Polynomial.coeff : Polynomial R → ℕ → R :=
  fun x ↦ match x with
  | { toFinsupp := p } => ⇑p
```

A polynomial is represented as a `Finsupp ℕ R` (a finitely-supported
function ℕ → R), so `coeff p n` is just evaluation of that function at `n`.

The **leading coefficient** is defined in `Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.leadingCoeff : Polynomial R → R :=
  fun p ↦ p.coeff p.natDegree
```
-/

namespace Azurite.BPR

open Polynomial

/-!
C is an algebraically closed field, D is a subring of C, and K is
the quotient field of D.
-/
variable {C : Type*} [Field C] [IsAlgClosed C]
variable {D : Type*} [CommRing D] [IsDomain D] [Algebra D C]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

/-!
### Definition 1.4 (Divisor)
Suppose that P and Q are two polynomials in D[X]. The polynomial Q is a
*divisor* of P if P = AQ for some A ∈ K[X].

This is **not** a separate definition in Mathlib. It is simply standard
divisibility `∣` in K[X] applied after mapping P and Q from D[X] into K[X]
via `Polynomial.map (algebraMap D K)`:

```
Dvd.dvd : α → α → Prop
a ∣ b  ↔  ∃ c, b = a * c
```
-/

/-- BPR Definition 1.4: `Q` is a divisor of `P` over `K` if `Q ∣ P`
    after embedding both into `K[X]`.  Equivalently, there exists
    `A : K[X]` such that `P.map = A * Q.map`. -/
def Polynomial.DivisorOver
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (Q P : D[X]) : Prop :=
  (Q.map (algebraMap D K)) ∣ (P.map (algebraMap D K))

omit [IsDomain D] in
theorem divisorOver_zero (P : D[X]) : Polynomial.DivisorOver K P 0 := by
  simp [Polynomial.DivisorOver, Polynomial.map_zero]

omit [IsDomain D] in
/-- 0 divides P over K if and only if P = 0. -/
theorem zero_divisorOver_iff (P : D[X]) :
    Polynomial.DivisorOver K (0 : D[X]) P ↔ P = 0 := by
  constructor
  · intro h
    simp only [Polynomial.DivisorOver, Polynomial.map_zero, zero_dvd_iff] at h
    exact Polynomial.map_injective _ (IsFractionRing.injective D K) (by simp [h])
  · rintro rfl; simp [Polynomial.DivisorOver]

/-!
### Euclidean Division (Proposition 1.5)

If Q ≠ 0, the *remainder* Rem(P, Q) is the unique polynomial R ∈ K[X]
of degree smaller than deg Q such that P = A Q + R for some A ∈ K[X].
The *quotient* Quo(P, Q) is A.

In Mathlib, Euclidean division for polynomials over a field is provided by
the `EuclideanDomain` instance on `Polynomial K` (via `Polynomial.instEuclideanDomain`).
The operators `/` and `%` give quotient and remainder, with:

- `EuclideanDomain.div_add_mod`: `P = Q * (P / Q) + P % Q`
- `Polynomial.degree_mod_lt`: `(P % Q).degree < Q.degree` for `Q ≠ 0`

See: `Mathlib.Algebra.Polynomial.FieldDivision`

There is also `Polynomial.divByMonic` (`/ₘ`) and `Polynomial.modByMonic`
(`%ₘ`) which work over any ring but require the divisor to be monic.
-/

/-- Quo(P, Q): the quotient in the Euclidean division of P by Q,
    computed in K[X] after mapping from D[X]. -/
noncomputable def Quo (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (P Q : D[X]) : K[X] :=
  (P.map (algebraMap D K)) / (Q.map (algebraMap D K))

/-- Rem(P, Q): the remainder in the Euclidean division of P by Q,
    computed in K[X] after mapping from D[X]. -/
noncomputable def Rem (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (P Q : D[X]) : K[X] :=
  (P.map (algebraMap D K)) % (Q.map (algebraMap D K))

omit [IsDomain D] in
/-- Euclidean division equation: P = Q · Quo(P,Q) + Rem(P,Q) in K[X]. -/
theorem map_eq_mul_quo_add_rem (P Q : D[X]) :
    P.map (algebraMap D K) =
    Q.map (algebraMap D K) * Quo K P Q + Rem K P Q :=
  (EuclideanDomain.div_add_mod _ _).symm

omit [IsDomain D] in
/-- deg(Rem(P, Q)) < deg(Q) when Q ≠ 0. -/
theorem degree_rem_lt (P Q : D[X]) (hQ : Q ≠ 0) :
    (Rem K P Q).degree < (Q.map (algebraMap D K)).degree :=
  Polynomial.degree_mod_lt _
    ((Polynomial.map_ne_zero_iff (IsFractionRing.injective D K)).mpr hQ)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Exercise 1.5: If Q ≠ 0, there exists a unique pair (A, R) in K[X]²
    such that P = AQ + R and deg(R) < deg(Q). -/
theorem exercise_1_5 (P Q : K[X]) (hQ : Q ≠ 0) :
    ∃! p : K[X] × K[X],
      P = p.1 * Q + p.2 ∧ p.2.degree < Q.degree := by
  -- p.1 = A (quotient), p.2 = R (remainder)
  have hmod : Q * (P / Q) + P % Q = P := EuclideanDomain.div_add_mod P Q
  -- Existence
  refine ⟨(P / Q, P % Q), ⟨?_, Polynomial.degree_mod_lt P hQ⟩, ?_⟩
  · show P = P / Q * Q + P % Q
    rw [mul_comm]; exact hmod.symm
  -- Uniqueness
  · rintro ⟨A, R⟩ ⟨hAR : P = A * Q + R, hDeg : R.degree < Q.degree⟩
    have hEq : A * Q + R = P / Q * Q + P % Q :=
      hAR.symm.trans (by rw [mul_comm]; exact hmod.symm)
    suffices hA : A = P / Q from
      Prod.ext hA (add_left_cancel (show P / Q * Q + R = P / Q * Q + P % Q from
        hA ▸ hEq))
    by_contra hne
    have hsub : (A - P / Q) * Q = P % Q - R := by
      have : A * Q - P / Q * Q = P % Q - R :=
        calc A * Q - P / Q * Q
            = (A * Q + R) - R - P / Q * Q := by ring
          _ = (P / Q * Q + P % Q) - R - P / Q * Q := by rw [hEq]
          _ = P % Q - R := by ring
      rwa [← sub_mul] at this
    have hDegSub : (P % Q - R).degree < Q.degree :=
      lt_of_le_of_lt (degree_sub_le _ _)
        (max_lt (Polynomial.degree_mod_lt P hQ) hDeg)
    rw [← hsub] at hDegSub
    have hDegProd : Q.degree ≤ ((A - P / Q) * Q).degree := by
      rw [degree_mul]
      have h1 := degree_eq_bot.not.mpr (sub_ne_zero.mpr hne)
      cases hd : (A - P / Q).degree with
      | bot => exact absurd hd h1
      | coe n =>
        cases hq : Q.degree with
        | bot => exact absurd (degree_eq_bot.mp hq) hQ
        | coe m => exact_mod_cast Nat.le_add_left m n
    exact absurd hDegSub (not_lt.mpr hDegProd)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Rem(aP, bQ) = a · Rem(P, Q) for a, b ∈ K with b ≠ 0. -/
theorem rem_C_mul_C_mul (a b : K) (hb : b ≠ 0) (P Q : K[X]) (hQ : Q ≠ 0) :
    Polynomial.C a * P % (Polynomial.C b * Q) = Polynomial.C a * (P % Q) := by
  simp only [mod_def, leadingCoeff_mul, leadingCoeff_C]
  rw [mul_inv, Polynomial.C_mul]
  have hNorm : Polynomial.C b * Q * (Polynomial.C b⁻¹ * Polynomial.C Q.leadingCoeff⁻¹) =
      Q * Polynomial.C Q.leadingCoeff⁻¹ := by
    calc Polynomial.C b * Q * (Polynomial.C b⁻¹ * Polynomial.C Q.leadingCoeff⁻¹)
        = (Polynomial.C b * Polynomial.C b⁻¹) *
          (Q * Polynomial.C Q.leadingCoeff⁻¹) := by ring
      _ = Q * Polynomial.C Q.leadingCoeff⁻¹ := by
          rw [← Polynomial.C_mul, mul_inv_cancel₀ hb, Polynomial.C_1, one_mul]
  rw [hNorm]
  set M := Q * Polynomial.C Q.leadingCoeff⁻¹
  have hM : M.Monic := monic_mul_leadingCoeff_inv hQ
  have hdvd : M ∣ (Polynomial.C a * P - Polynomial.C a * (P %ₘ M)) := by
    rw [← mul_sub]
    have : P - P %ₘ M = M * (P /ₘ M) := by
      have h := modByMonic_add_div P M
      calc P - P %ₘ M = (P %ₘ M + M * (P /ₘ M)) - P %ₘ M := by rw [h]
        _ = M * (P /ₘ M) := by ring
    rw [this]; exact ⟨Polynomial.C a * (P /ₘ M), by ring⟩
  rw [modByMonic_eq_of_dvd_sub hM hdvd, modByMonic_eq_self_iff hM]
  calc (Polynomial.C a * (P %ₘ M)).degree
      ≤ (P %ₘ M).degree := by
        by_cases ha : a = 0 <;> simp_all
    _ < M.degree := degree_modByMonic_lt P hM

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- At a root x of Q, Rem(P, Q)(x) = P(x). -/
theorem eval_mod_at_root (P Q : K[X]) (x : K) (hx : Polynomial.eval x Q = 0) :
    Polynomial.eval x (P % Q) = Polynomial.eval x P := by
  have h := EuclideanDomain.div_add_mod P Q
  have : Polynomial.eval x P = Polynomial.eval x (Q * (P / Q) + P % Q) := by rw [h]
  rw [this, eval_add, eval_mul, hx, zero_mul, zero_add]

end Azurite.BPR
