import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.EuclideanDomain
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

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Exercise 1.6: x is a root of P iff (X − x) divides P in K[X]. -/
theorem exercise_1_6 (P : K[X]) (x : K) :
    Polynomial.eval x P = 0 ↔ (X - Polynomial.C x) ∣ P :=
  dvd_iff_isRoot.symm

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Exercise 1.7: Over an algebraically closed field, every polynomial factors as
    P = C(leadingCoeff P) * ∏ (X − C x) for x ∈ P.roots.
    The multiset `P.roots` records roots with multiplicity, so this encodes the
    factorization P = a(X−x₁)^μ₁⋯(X−xₖ)^μₖ. Uniqueness is automatic since
    `P.roots` is uniquely determined by P. -/
theorem exercise_1_7 (P : C[X]) :
    P = Polynomial.C P.leadingCoeff *
      (Multiset.map (fun a => X - Polynomial.C a) P.roots).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.splits P).natDegree_eq_card_roots.symm).symm

/-!
### Greatest Common Divisor (Definition 1.8)

A *greatest common divisor* of P and Q is a polynomial G ∈ K[X] such that
G divides both P and Q, and any common divisor of P and Q divides G.
This is a relation, not a function — GCDs are unique only up to units (nonzero scalars in K[X]).

In Mathlib, `GCDMonoid.gcd` picks a canonical representative via the
`EuclideanDomain` instance on `K[X]`.
-/

open Classical in
noncomputable instance gcdMonoidPolynomial : GCDMonoid K[X] :=
  EuclideanDomain.gcdMonoid K[X]

/-- BPR Definition 1.8: G is a greatest common divisor of P and Q. -/
def IsGCD (G P Q : K[X]) : Prop :=
  G ∣ P ∧ G ∣ Q ∧ ∀ D : K[X], D ∣ P → D ∣ Q → D ∣ G

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Mathlib's `gcd P Q` satisfies the BPR IsGCD relation. -/
theorem gcd_isGCD (P Q : K[X]) : IsGCD (gcd P Q) P Q :=
  ⟨gcd_dvd_left P Q, gcd_dvd_right P Q, fun _ hP hQ => dvd_gcd hP hQ⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any two GCDs in the BPR sense are associates (differ by a unit in K[X]). -/
theorem isGCD_associated {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    Associated G₁ G₂ :=
  associated_of_dvd_dvd (h₂.2.2 G₁ h₁.1 h₁.2.1) (h₁.2.2 G₂ h₂.1 h₂.2.1)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- P is a GCD of P and 0. -/
theorem isGCD_self_zero (P : K[X]) : IsGCD P P 0 :=
  ⟨dvd_refl P, dvd_zero P, fun _ hP _ => hP⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any two GCDs of P and Q divide each other. -/
theorem isGCD_dvd_dvd {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    G₁ ∣ G₂ ∧ G₂ ∣ G₁ :=
  ⟨h₂.2.2 G₁ h₁.1 h₁.2.1, h₁.2.2 G₂ h₂.1 h₂.2.1⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any two GCDs of P and Q have the same degree. -/
theorem isGCD_degree_eq {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    G₁.degree = G₂.degree := by
  have ⟨h12, h21⟩ := isGCD_dvd_dvd h₁ h₂
  exact degree_eq_degree_of_associated (associated_of_dvd_dvd h12 h21)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- The degree of the GCD of P and Q. Well-defined since any two GCDs
    have the same degree (by `isGCD_degree_eq`). -/
noncomputable def degGcd (P Q : K[X]) : WithBot ℕ := (gcd P Q).degree

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any IsGCD witness has the same degree as `degGcd P Q`. -/
theorem isGCD_degree_eq_degGcd {G P Q : K[X]} (h : IsGCD G P Q) :
    G.degree = degGcd P Q :=
  isGCD_degree_eq h (gcd_isGCD P Q)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Definition: P and Q are coprime if their GCD is a nonzero element of K
    (equivalently, a unit in K[X]). -/
def AreCoprime (P Q : K[X]) : Prop :=
  ∀ G : K[X], IsGCD G P Q → IsUnit G

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- `AreCoprime` is equivalent to Mathlib's `IsCoprime`. -/
theorem areCoprime_iff_isCoprime (P Q : K[X]) :
    AreCoprime P Q ↔ IsCoprime P Q := by
  constructor
  · intro h
    exact (gcd_isUnit_iff P Q).mp
      (h (gcd P Q) ⟨gcd_dvd_left P Q, gcd_dvd_right P Q,
        fun _ h1 h2 => dvd_gcd h1 h2⟩)
  · intro ⟨u, v, h⟩ G ⟨hGP, hGQ, _⟩
    rw [isUnit_iff_dvd_one]
    exact h ▸ dvd_add (dvd_mul_of_dvd_right hGP u) (dvd_mul_of_dvd_right hGQ v)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR: G is a least common multiple of P and Q if
    G is a multiple of both P and Q, and any common multiple of P and Q
    is a multiple of G. -/
def IsLCM (G P Q : K[X]) : Prop :=
  P ∣ G ∧ Q ∣ G ∧ ∀ M : K[X], P ∣ M → Q ∣ M → G ∣ M

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Mathlib's `lcm P Q` satisfies the BPR IsLCM relation. -/
theorem lcm_isLCM (P Q : K[X]) : IsLCM (lcm P Q) P Q :=
  ⟨dvd_lcm_left P Q, dvd_lcm_right P Q, fun _ hP hQ => lcm_dvd hP hQ⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any two LCMs of P and Q are associates (differ by a unit). -/
theorem isLCM_associated {G₁ G₂ P Q : K[X]}
    (h₁ : IsLCM G₁ P Q) (h₂ : IsLCM G₂ P Q) :
    Associated G₁ G₂ :=
  associated_of_dvd_dvd (h₁.2.2 G₂ h₂.1 h₂.2.1) (h₂.2.2 G₁ h₁.1 h₁.2.1)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- The degree of the LCM of P and Q. Well-defined since any two LCMs
    have the same degree (by `isLCM_associated`). -/
noncomputable def degLcm (P Q : K[X]) : WithBot ℕ := (lcm P Q).degree

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Any IsLCM witness has the same degree as `degLcm P Q`. -/
theorem isLCM_degree_eq_degLcm {G P Q : K[X]} (h : IsLCM G P Q) :
    G.degree = degLcm P Q :=
  degree_eq_degree_of_associated
    (associated_of_dvd_dvd
      (h.2.2 _ (dvd_lcm_left P Q) (dvd_lcm_right P Q))
      ((lcm_isLCM P Q).2.2 _ h.1 h.2.1))

/-!
### Proposition 1.5
-/

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- `IsLCM` is preserved under `Associated`. -/
private theorem isLCM_of_associated {L L' P Q : K[X]}
    (hL : IsLCM L P Q) (h : Associated L L') : IsLCM L' P Q :=
  ⟨dvd_trans hL.1 h.dvd, dvd_trans hL.2.1 h.dvd,
   fun M hP hQ => dvd_trans h.symm.dvd (hL.2.2 M hP hQ)⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Dividing by associated nonzero divisors gives associated quotients. -/
private theorem div_associated {a G₁ G₂ : K[X]}
    (hG₁ : G₁ ≠ 0) (hG₁_dvd : G₁ ∣ a) (hG₂_dvd : G₂ ∣ a)
    (hAssoc : Associated G₁ G₂) : Associated (a / G₁) (a / G₂) := by
  obtain ⟨u, hu⟩ := hAssoc
  have hG₂0 : G₂ ≠ 0 := fun h =>
    hG₁ ((mul_eq_zero.mp (hu ▸ h : G₁ * ↑u = 0)).resolve_right (Units.ne_zero u))
  have h1 := EuclideanDomain.mul_div_cancel' hG₁ hG₁_dvd
  have h2 := EuclideanDomain.mul_div_cancel' hG₂0 hG₂_dvd
  have h3 : a / G₁ = ↑u * (a / G₂) :=
    mul_left_cancel₀ hG₁ (calc G₁ * (a / G₁) = a := h1
      _ = G₂ * (a / G₂) := h2.symm
      _ = (G₁ * ↑u) * (a / G₂) := by rw [hu]
      _ = G₁ * (↑u * (a / G₂)) := mul_assoc _ _ _)
  exact ⟨u⁻¹, by rw [h3]; calc ↑u * (a / G₂) * ↑u⁻¹
    = a / G₂ * (↑u * ↑u⁻¹) := by ring
    _ = a / G₂ := by simp⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Proposition 1.5 for Mathlib's canonical gcd: P * Q / gcd(P, Q) = lcm(P, Q)
    definitionally, so this is immediate. -/
theorem prop_1_5_gcd (P Q : K[X]) : IsLCM (P * Q / gcd P Q) P Q :=
  ⟨dvd_lcm_left P Q, dvd_lcm_right P Q, fun _ hP hQ => lcm_dvd hP hQ⟩

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Proposition 1.5: If G is a GCD of P and Q (with G ≠ 0),
    then P * Q / G is a least common multiple of P and Q. -/
theorem prop_1_5 {P Q G : K[X]} (hG : IsGCD G P Q) (hG0 : G ≠ 0) :
    IsLCM (P * Q / G) P Q :=
  isLCM_of_associated (prop_1_5_gcd P Q)
    (div_associated hG0 (dvd_mul_of_dvd_left hG.1 Q)
      (dvd_mul_of_dvd_left (gcd_dvd_left P Q) Q)
      (associated_of_dvd_dvd
        ((gcd_isGCD P Q).2.2 G hG.1 hG.2.1)
        (hG.2.2 (gcd P Q) (gcd_dvd_left P Q) (gcd_dvd_right P Q)))).symm

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Corollary 1.6: degGcd(P, Q) + degLcm(P, Q) = deg(P) + deg(Q).
    Stated additively since `WithBot ℕ` does not support subtraction. -/
theorem corollary_1_6 (P Q : K[X]) :
    degGcd P Q + degLcm P Q = P.degree + Q.degree := by
  have h := degree_eq_degree_of_associated (gcd_mul_lcm P Q)
  rwa [degree_mul, degree_mul] at h

/-!
### Definition 1.7: Signed Remainder Sequence
-/

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Definition 1.7: The signed remainder sequence of P and Q.
    - `SRemS P Q 0 = P`
    - `SRemS P Q 1 = Q`
    - `SRemS P Q (n+2) = −Rem(SRemS P Q n, SRemS P Q (n+1))` when `SRemS P Q (n+1) ≠ 0`
    - `SRemS P Q (n+2) = 0` when `SRemS P Q (n+1) = 0`

    The sequence stabilizes at 0 once reached. -/
noncomputable def SRemS (P Q : K[X]) : ℕ → K[X]
  | 0 => P
  | 1 => Q
  | n + 2 =>
    let prev := SRemS P Q (n + 1)
    if prev = 0 then 0
    else -(SRemS P Q n % prev)

/-!
### Proposition 1.8
-/

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
private lemma SRemS_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemS P Q (n + 2) = -(SRemS P Q n % SRemS P Q (n + 1)) := by
  simp [SRemS, hne]

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
private lemma SRemS_zero_ge (P Q : K[X]) (n : ℕ) (h : SRemS P Q (n + 1) = 0)
    (m : ℕ) (hm : m ≥ n + 1) : SRemS P Q m = 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm' : m + 1 ≤ n + 1
    · rw [show m + 1 = n + 1 from by omega]; exact h
    · have ihm : SRemS P Q m = 0 := ih (by omega)
      cases m with
      | zero => omega
      | succ p => simp [SRemS, ihm]

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Forward induction: any common divisor of P and Q divides every entry
    of the signed remainder sequence. -/
theorem dvd_SRemS (P Q D : K[X]) (hP : D ∣ P) (hQ : D ∣ Q) (n : ℕ) :
    D ∣ SRemS P Q n := by
  match n with
  | 0 => exact hP
  | 1 => exact hQ
  | n + 2 =>
    by_cases hne : SRemS P Q (n + 1) = 0
    · simp [SRemS, hne]
    · rw [SRemS_ss P Q n hne]
      exact dvd_neg.mpr ((EuclideanDomain.dvd_mod_iff
        (dvd_SRemS P Q D hP hQ (n + 1))).mpr (dvd_SRemS P Q D hP hQ n))
termination_by n

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Backward step: if G divides SRemS(n+1) and SRemS(n+2), it divides SRemS(n). -/
private lemma SRemS_back (P Q G : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0)
    (h1 : G ∣ SRemS P Q (n + 1)) (h2 : G ∣ SRemS P Q (n + 2)) :
    G ∣ SRemS P Q n := by
  rw [SRemS_ss P Q n hne] at h2
  exact (EuclideanDomain.dvd_mod_iff h1).mp (dvd_neg.mp h2)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Backward induction: when SRemS(k+1) = 0, SRemS_k divides all earlier entries. -/
private theorem SRemS_last_dvd (P Q : K[X]) (k : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (m : ℕ) (hm : m ≤ k) : SRemS P Q k ∣ SRemS P Q m := by
  by_cases hm' : m = k
  · subst hm'; exact dvd_refl _
  · have hm1 : m + 1 ≤ k := by omega
    have hne : SRemS P Q (m + 1) ≠ 0 := by
      intro heq
      cases m with
      | zero => exact hk_ne (SRemS_zero_ge P Q 0 heq k (by omega))
      | succ p => exact hk_ne (SRemS_zero_ge P Q (p + 1) heq k (by omega))
    have ih1 := SRemS_last_dvd P Q k hk hk_ne (m + 1) hm1
    have ih2 : SRemS P Q k ∣ SRemS P Q (m + 2) := by
      by_cases hm2 : m + 2 ≤ k
      · exact SRemS_last_dvd P Q k hk hk_ne (m + 2) hm2
      · rw [SRemS_zero_ge P Q k hk (m + 2) (by omega)]; exact dvd_zero _
    exact SRemS_back P Q (SRemS P Q k) m hne ih1 ih2
termination_by k - m

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Proposition 1.8: The last nonzero element of the signed remainder sequence
    is a greatest common divisor of P and Q. -/
theorem prop_1_8 {P Q : K[X]} {k : ℕ}
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0) :
    IsGCD (SRemS P Q k) P Q := by
  refine ⟨SRemS_last_dvd P Q k hk hk_ne 0 (Nat.zero_le _), ?_,
    fun D hDP hDQ => dvd_SRemS P Q D hDP hDQ k⟩
  cases k with
  | zero => simp [SRemS] at hk; rw [hk]; exact dvd_zero _
  | succ k' => exact SRemS_last_dvd P Q (k' + 1) hk hk_ne 1 (by omega)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The signed remainder sequence of P and 0 has SRemS(0) = P. -/
@[simp] theorem SRemS_zero_left (P : K[X]) : SRemS P 0 0 = P := rfl

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The signed remainder sequence of P and 0 stabilizes at 0 from index 1 onward. -/
theorem SRemS_zero_right (P : K[X]) (n : ℕ) (hn : n ≥ 1) :
    SRemS P 0 n = 0 :=
  SRemS_zero_ge P 0 0 rfl n hn

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The signed remainder sequence of 0 and Q has SRemS(0) = 0. -/
@[simp] theorem SRemS_zero_fst (Q : K[X]) : SRemS 0 Q 0 = 0 := rfl

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The signed remainder sequence of 0 and Q has SRemS(1) = Q. -/
@[simp] theorem SRemS_zero_snd (Q : K[X]) : SRemS 0 Q 1 = Q := rfl

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- When Q ≠ 0, the signed remainder sequence of 0 and Q stabilizes at 0
    from index 2 onward: SRemS(0, Q) = [0, Q, 0, 0, …]. -/
theorem SRemS_zero_left_stabilizes (Q : K[X]) (hQ : Q ≠ 0) (n : ℕ) (hn : n ≥ 2) :
    SRemS 0 Q n = 0 := by
  apply SRemS_zero_ge 0 Q 1 _ n (by omega)
  simp [SRemS, hQ]

end Azurite.BPR

