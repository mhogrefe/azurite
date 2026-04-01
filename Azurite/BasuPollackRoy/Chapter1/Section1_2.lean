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

theorem IsGCD.symm {G P Q : K[X]} (h : IsGCD G P Q) : IsGCD G Q P :=
  ⟨h.2.1, h.1, fun D hQ hP => h.2.2 D hP hQ⟩

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
/-- SRemS(P, Q, 0) = P. -/
@[simp] theorem SRemS_fst (P Q : K[X]) : SRemS P Q 0 = P := rfl

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- SRemS(P, Q, 1) = Q. -/
@[simp] theorem SRemS_snd (P Q : K[X]) : SRemS P Q 1 = Q := by simp [SRemS]

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

/-!
### Definition 1.10: Extended Signed Remainder Sequence
-/

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Definition 1.10: The U-cofactor of the extended signed remainder sequence.
    - `SRemU P Q 0 = 1`
    - `SRemU P Q 1 = 0`
    - `SRemU P Q (n+2) = −SRemU(n) + A · SRemU(n+1)` when `SRemS(n+1) ≠ 0`
    - `SRemU P Q (n+2) = 0` when `SRemS(n+1) = 0`

    where `A = Quo(SRemS(n), SRemS(n+1))` is the quotient from the Euclidean
    division step that produces `SRemS(n+2)`. -/
noncomputable def SRemU (P Q : K[X]) : ℕ → K[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
    if SRemS P Q (n + 1) = 0 then 0
    else -(SRemU P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Definition 1.10: The V-cofactor of the extended signed remainder sequence.
    - `SRemV P Q 0 = 0`
    - `SRemV P Q 1 = 1`
    - `SRemV P Q (n+2) = −SRemV(n) + A · SRemV(n+1)` when `SRemS(n+1) ≠ 0`
    - `SRemV P Q (n+2) = 0` when `SRemS(n+1) = 0`

    where `A = Quo(SRemS(n), SRemS(n+1))` is the quotient from the Euclidean
    division step that produces `SRemS(n+2)`. -/
noncomputable def SRemV (P Q : K[X]) : ℕ → K[X]
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if SRemS P Q (n + 1) = 0 then 0
    else -(SRemV P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1)

/-!
### Lemma 1.11: Extended Signed Remainder Sequence Properties
-/

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Unfolding lemma for SRemU at index n+2 when SRemS(n+1) ≠ 0. -/
lemma SRemU_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemU P Q (n + 2) =
      -(SRemU P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1) := by
  simp [SRemU, hne]

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Unfolding lemma for SRemV at index n+2 when SRemS(n+1) ≠ 0. -/
lemma SRemV_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemV P Q (n + 2) =
      -(SRemV P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1) := by
  simp [SRemV, hne]

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Lemma 1.11 (i): For all i, SRemS_i(P,Q) = SRemU_i(P,Q) · P + SRemV_i(P,Q) · Q. -/
theorem lemma_1_11_bezout (P Q : K[X]) (n : ℕ) :
    SRemS P Q n = SRemU P Q n * P + SRemV P Q n * Q := by
  match n with
  | 0 => simp [SRemS, SRemU, SRemV]
  | 1 => simp [SRemS, SRemU, SRemV]
  | n + 2 =>
    by_cases hne : SRemS P Q (n + 1) = 0
    · simp [SRemS, SRemU, SRemV, hne]
    · rw [SRemS_ss P Q n hne, SRemU_ss P Q n hne, SRemV_ss P Q n hne]
      set a := SRemS P Q n / SRemS P Q (n + 1)
      have ih0 := lemma_1_11_bezout P Q n
      have ih1 := lemma_1_11_bezout P Q (n + 1)
      have hdiv : SRemS P Q n % SRemS P Q (n + 1) =
          SRemS P Q n - SRemS P Q (n + 1) * a := by
        have h := EuclideanDomain.div_add_mod (SRemS P Q n) (SRemS P Q (n + 1))
        linear_combination h
      rw [hdiv, ih0, ih1]; ring

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The degree of SRemS strictly decreases at each step: when SRemS(n+1) ≠ 0,
    deg(SRemS(n+2)) < deg(SRemS(n+1)). -/
theorem degree_SRemS_lt (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    (SRemS P Q (n + 2)).degree < (SRemS P Q (n + 1)).degree := by
  rw [SRemS_ss P Q n hne]
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt _ hne

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- For consecutive nonzero entries in SRemS with n ≥ 1, the degrees
    strictly decrease: deg(SRemS(n+1)) < deg(SRemS(n)). -/
theorem degree_SRemS_chain_lt (P Q : K[X]) (n : ℕ)
    (hn : n ≥ 1)
    (hne : SRemS P Q n ≠ 0) :
    (SRemS P Q (n + 1)).degree < (SRemS P Q n).degree := by
  cases n with
  | zero => omega
  | succ m => exact degree_SRemS_lt P Q m hne

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Entries of SRemS between 0 and k are nonzero when the sequence terminates at k+1. -/
theorem SRemS_ne_zero_of_le (P Q : K[X]) (k : ℕ) (j : ℕ)
    (_ : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hj1 : 1 ≤ j) (hj2 : j ≤ k) : SRemS P Q j ≠ 0 := by
  intro heq
  cases j with
  | zero => omega
  | succ p =>
    exact hk_ne (SRemS_zero_ge P Q p heq k (by omega))

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The quotient SRemS(n) / SRemS(n+1) is nonzero when both entries are nonzero
    and the degree decreases. -/
theorem SRemS_div_ne_zero (P Q : K[X]) (n : ℕ)
    (hne0 : SRemS P Q n ≠ 0) (hne : SRemS P Q (n + 1) ≠ 0)
    (hle : (SRemS P Q (n + 1)).degree ≤ (SRemS P Q n).degree) :
    SRemS P Q n / SRemS P Q (n + 1) ≠ 0 := by
  intro heq
  have h := Polynomial.degree_add_div hne hle
  simp [heq] at h
  exact hne0 (Polynomial.degree_eq_bot.mp h.symm)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- natDegree of the quotient SRemS(n) / SRemS(n+1) when both are nonzero
    and deg(SRemS(n+1)) ≤ deg(SRemS(n)). -/
theorem natDegree_SRemS_div (P Q : K[X]) (n : ℕ)
    (hne0 : SRemS P Q n ≠ 0)
    (hne : SRemS P Q (n + 1) ≠ 0)
    (hle : (SRemS P Q (n + 1)).degree ≤ (SRemS P Q n).degree) :
    (SRemS P Q n / SRemS P Q (n + 1)).natDegree =
      (SRemS P Q n).natDegree - (SRemS P Q (n + 1)).natDegree := by
  have h := Polynomial.degree_add_div hne hle
  have hne_div := SRemS_div_ne_zero P Q n hne0 hne hle
  rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hne_div,
      Polynomial.degree_eq_natDegree hne0] at h
  exact_mod_cast Nat.eq_sub_of_add_eq (by rw [add_comm]; exact_mod_cast h)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- natDegree of SRemS is strictly decreasing: for m < n with all entries nonzero,
    natDegree(SRemS(n+1)) < natDegree(SRemS(m+1)). -/
theorem natDegree_SRemS_lt_of_lt (P Q : K[X]) (m n : ℕ)
    (hmn : m < n)
    (hne : ∀ j, m + 1 ≤ j → j ≤ n + 1 → SRemS P Q j ≠ 0) :
    (SRemS P Q (n + 1)).natDegree < (SRemS P Q (m + 1)).natDegree := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hmn' : m < n
    · have h1 : (SRemS P Q (n + 1 + 1)).natDegree < (SRemS P Q (n + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree (hne (n + 1 + 1) (by omega) (by omega))
          (degree_SRemS_lt P Q n (hne (n + 1) (by omega) (by omega)))
      exact lt_trans h1 (ih hmn' (fun j hj1 hj2 => hne j hj1 (by omega)))
    · have hm : m = n := by omega
      subst hm
      exact Polynomial.natDegree_lt_natDegree (hne (m + 1 + 1) (by omega) (by omega))
        (degree_SRemS_lt P Q m (hne (m + 1) (by omega) (by omega)))

set_option maxHeartbeats 800000 in
omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Lemma 1.11 (ii): For 1 ≤ i ≤ k, natDeg(SRemU_{i+1}(P,Q)) = natDeg(Q) − natDeg(SRemS_i),
    where the SRemS sequence terminates at index k+1. -/
theorem lemma_1_11_degU (P Q : K[X]) (k : ℕ) (i : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hi : 1 ≤ i) (hik : i ≤ k)
    (_hP : P ≠ 0) (hQ : Q ≠ 0)
    (_hle : Q.degree ≤ P.degree) :
    (SRemU P Q (i + 1)).natDegree = Q.natDegree - (SRemS P Q i).natDegree := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    match i, hi, hik with
    | 1, _, _ =>
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS]; exact hQ
      rw [SRemU_ss P Q 0 h1]
      simp [SRemU, SRemS]
    | i + 2, _, _ =>
      have hsi : SRemS P Q (i + 2) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 2) hk hk_ne (by omega) (by omega)
      have hsi1 : SRemS P Q (i + 1) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 1) hk hk_ne (by omega) (by omega)
      rw [SRemU_ss P Q (i + 1) hsi]
      have hle_deg : (SRemS P Q (i + 2)).degree ≤ (SRemS P Q (i + 1)).degree :=
        le_of_lt (degree_SRemS_lt P Q i hsi1)
      have hdq := natDegree_SRemS_div P Q (i + 1) hsi1 hsi hle_deg
      have hne_div := SRemS_div_ne_zero P Q (i + 1) hsi1 hsi hle_deg
      have ih_cur := ih (i + 1) (by omega) (by omega) (by omega)
      have hnd_dec : (SRemS P Q (i + 2)).natDegree < (SRemS P Q (i + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hsi (degree_SRemS_lt P Q i hsi1)
      cases i with
      | zero =>
        have hne_u : SRemU P Q 2 ≠ 0 := by
          intro heq; simp [SRemU, SRemS] at heq; exact hQ heq
        show (-SRemU P Q 1 + _ * SRemU P Q 2).natDegree = _
        simp only [show SRemU P Q 1 = 0 from rfl, neg_zero, zero_add]
        rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur]
        simp [SRemS]
      | succ j =>
        have hnd_le_q : (SRemS P Q (j + 1 + 1)).natDegree < Q.natDegree := by
          have := natDegree_SRemS_lt_of_lt P Q 0 (j + 1) (by omega) (fun l hl1 hl2 =>
            SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
          simp [SRemS_snd] at this; exact this
        have hnd_le_q2 : (SRemS P Q (j + 1 + 2)).natDegree < Q.natDegree :=
          lt_trans hnd_dec hnd_le_q
        have hne_u : SRemU P Q (j + 1 + 1 + 1) ≠ 0 := by
          intro heq; rw [heq, Polynomial.natDegree_zero] at ih_cur; omega
        have ih_prev := ih (j + 1) (by omega) (by omega) (by omega)
        have hnd_le_q_j : (SRemS P Q (j + 1)).natDegree ≤ Q.natDegree := by
          cases j with
          | zero => simp [SRemS_snd]
          | succ j' =>
            have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
              SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
            simp [SRemS_snd] at this; exact le_of_lt this
        have hne_u_prev : SRemU P Q (j + 1 + 1) ≠ 0 := by
          cases j with
          | zero => simp [SRemU, SRemS]; exact hQ
          | succ j' =>
            have hlt_j' : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
              have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
              simp [SRemS_snd] at this; exact this
            intro heq; rw [heq, Polynomial.natDegree_zero] at ih_prev
            exact absurd ih_prev (ne_of_gt (Nat.sub_pos_of_lt hlt_j')).symm
        have hsi_j : SRemS P Q (j + 1) ≠ 0 :=
          SRemS_ne_zero_of_le P Q k (j + 1) hk hk_ne (by omega) (by omega)
        have hd_step : (SRemS P Q (j + 1 + 1)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          Polynomial.natDegree_lt_natDegree hsi1 (degree_SRemS_lt P Q j hsi_j)
        have hd_skip : (SRemS P Q (j + 1 + 2)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          lt_trans hnd_dec hd_step
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · -- natDeg(quot * SRemU(j+3)) = Q - SRemS(j+3)
          rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur]
          -- (d₂ - d₃) + (Q - d₂) = Q - d₃
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel (le_of_lt hnd_le_q) (le_of_lt hnd_dec)
        · -- deg(-SRemU(j+2)) < deg(quot * SRemU(j+3))
          apply Polynomial.degree_lt_degree
          calc Polynomial.natDegree (-SRemU P Q (j + 1 + 1))
              = (SRemU P Q (j + 1 + 1)).natDegree := Polynomial.natDegree_neg _
            _ = Q.natDegree - (SRemS P Q (j + 1)).natDegree := ih_prev
            _ < Q.natDegree - (SRemS P Q (j + 1 + 2)).natDegree :=
                Nat.sub_lt_sub_left (lt_of_lt_of_le hd_skip hnd_le_q_j) hd_skip
            _ = Polynomial.natDegree (SRemS P Q (j + 1 + 1) / SRemS P Q (j + 1 + 1 + 1) *
                SRemU P Q (j + 1 + 1 + 1)) := by
                rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur]
                exact (Nat.sub_add_sub_cancel (le_of_lt hnd_le_q) (le_of_lt hnd_dec)).symm ▸
                  (Nat.add_comm _ _).symm ▸ rfl

set_option maxHeartbeats 800000 in
omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Lemma 1.11 (iii): For 1 ≤ i ≤ k, natDeg(SRemV_{i+1}(P,Q)) = natDeg(P) − natDeg(SRemS_i),
    where the SRemS sequence terminates at index k+1. -/
theorem lemma_1_11_degV (P Q : K[X]) (k : ℕ) (i : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hi : 1 ≤ i) (hik : i ≤ k)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hle : Q.degree ≤ P.degree) :
    (SRemV P Q (i + 1)).natDegree = P.natDegree - (SRemS P Q i).natDegree := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    match i, hi, hik with
    | 1, _, _ =>
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS]; exact hQ
      rw [SRemV_ss P Q 0 h1]
      simp [SRemV, SRemS]
      -- natDeg(P / Q) = P.natDeg - Q.natDeg = P.natDeg - SRemS(1).natDeg
      exact natDegree_SRemS_div P Q 0 hP hQ (by simp [SRemS]; exact hle)
    | i + 2, _, _ =>
      have hsi : SRemS P Q (i + 2) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 2) hk hk_ne (by omega) (by omega)
      have hsi1 : SRemS P Q (i + 1) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 1) hk hk_ne (by omega) (by omega)
      rw [SRemV_ss P Q (i + 1) hsi]
      have hle_deg : (SRemS P Q (i + 2)).degree ≤ (SRemS P Q (i + 1)).degree :=
        le_of_lt (degree_SRemS_lt P Q i hsi1)
      have hdq := natDegree_SRemS_div P Q (i + 1) hsi1 hsi hle_deg
      have hne_div := SRemS_div_ne_zero P Q (i + 1) hsi1 hsi hle_deg
      have ih_cur := ih (i + 1) (by omega) (by omega) (by omega)
      have hnd_dec : (SRemS P Q (i + 2)).natDegree < (SRemS P Q (i + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hsi (degree_SRemS_lt P Q i hsi1)
      -- Need SRemS(l).natDeg ≤ P.natDeg for various l
      have hp_ge_q : Q.natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_natDegree hle
      cases i with
      | zero =>
        -- SRemV 2 = -SRemV 0 + (SRemS 0 / SRemS 1) * SRemV 1 = 0 + (P/Q) * 1 = P/Q
        -- which is hne_div (SRemS 0 / SRemS 1 ≠ 0)
        have hne_v : SRemV P Q 2 ≠ 0 := by
          simp only [SRemV, show SRemS P Q 1 = Q from rfl, hQ, ↓reduceIte,
                     show SRemS P Q 0 = P from rfl, neg_zero, zero_add, mul_one]
          exact SRemS_div_ne_zero P Q 0 hP hQ (by simp [SRemS]; exact hle)
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel hp_ge_q
            (le_of_lt (Polynomial.natDegree_lt_natDegree hsi
              (degree_SRemS_lt P Q 0 hsi1)))
        · rw [Polynomial.degree_neg]
          calc (1 : K[X]).degree = (0 : ℕ) := Polynomial.degree_one
            _ < ↑((SRemS P Q (0 + 1) / SRemS P Q (0 + 1 + 1) * SRemV P Q (0 + 1 + 1)).natDegree) := by
                rw [Nat.cast_lt, Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
                -- 0 < (P.natDeg - SRemS(1).natDeg) + (SRemS(1).natDeg - SRemS(2).natDeg)
                have hsrem1_le : (SRemS P Q (0 + 1)).natDegree ≤ P.natDegree := by
                  simp [SRemS_snd]; exact hp_ge_q
                rw [Nat.add_comm, Nat.sub_add_sub_cancel hsrem1_le (le_of_lt hnd_dec)]
                -- 0 < P.natDeg - SRemS(2).natDeg
                omega
            _ = (SRemS P Q (0 + 1) / SRemS P Q (0 + 1 + 1) * SRemV P Q (0 + 1 + 1)).degree :=
                (Polynomial.degree_eq_natDegree (mul_ne_zero hne_div hne_v)).symm
      | succ j =>
        have hnd_le_p : (SRemS P Q (j + 1 + 1)).natDegree < P.natDegree := by
          have : (SRemS P Q (j + 1 + 1)).natDegree < Q.natDegree := by
            have := natDegree_SRemS_lt_of_lt P Q 0 (j + 1) (by omega) (fun l hl1 hl2 =>
              SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
            simp [SRemS_snd] at this; exact this
          exact lt_of_lt_of_le this hp_ge_q
        have hnd_le_p2 : (SRemS P Q (j + 1 + 2)).natDegree < P.natDegree :=
          lt_trans hnd_dec hnd_le_p
        have hne_v : SRemV P Q (j + 1 + 1 + 1) ≠ 0 := by
          intro heq; rw [heq, Polynomial.natDegree_zero] at ih_cur; omega
        have ih_prev := ih (j + 1) (by omega) (by omega) (by omega)
        have hnd_le_p_j : (SRemS P Q (j + 1)).natDegree ≤ P.natDegree := by
          cases j with
          | zero => simp [SRemS_snd]; exact hp_ge_q
          | succ j' =>
            have : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
              have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
              simp [SRemS_snd] at this; exact this
            exact le_of_lt (lt_of_lt_of_le this hp_ge_q)
        have hne_v_prev : SRemV P Q (j + 1 + 1) ≠ 0 := by
          cases j with
          | zero => simp [SRemV, SRemS]; exact ⟨hQ, SRemS_div_ne_zero P Q 0 hP hQ (by simp [SRemS]; exact hle)⟩
          | succ j' =>
            have hlt_j' : (SRemS P Q (j' + 2)).natDegree < P.natDegree := by
              have : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
                have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                  SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
                simp [SRemS_snd] at this; exact this
              exact lt_of_lt_of_le this hp_ge_q
            intro heq; rw [heq, Polynomial.natDegree_zero] at ih_prev
            exact absurd ih_prev (ne_of_gt (Nat.sub_pos_of_lt hlt_j')).symm
        have hsi_j : SRemS P Q (j + 1) ≠ 0 :=
          SRemS_ne_zero_of_le P Q k (j + 1) hk hk_ne (by omega) (by omega)
        have hd_step : (SRemS P Q (j + 1 + 1)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          Polynomial.natDegree_lt_natDegree hsi1 (degree_SRemS_lt P Q j hsi_j)
        have hd_skip : (SRemS P Q (j + 1 + 2)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          lt_trans hnd_dec hd_step
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · -- natDeg(quot * SRemV(j+3)) = P - SRemS(j+3)
          rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel (le_of_lt hnd_le_p) (le_of_lt hnd_dec)
        · -- deg(-SRemV(j+2)) < deg(quot * SRemV(j+3))
          apply Polynomial.degree_lt_degree
          calc Polynomial.natDegree (-SRemV P Q (j + 1 + 1))
              = (SRemV P Q (j + 1 + 1)).natDegree := Polynomial.natDegree_neg _
            _ = P.natDegree - (SRemS P Q (j + 1)).natDegree := ih_prev
            _ < P.natDegree - (SRemS P Q (j + 1 + 2)).natDegree :=
                Nat.sub_lt_sub_left (lt_of_lt_of_le hd_skip hnd_le_p_j) hd_skip
            _ = Polynomial.natDegree (SRemS P Q (j + 1 + 1) / SRemS P Q (j + 1 + 1 + 1) *
                SRemV P Q (j + 1 + 1 + 1)) := by
                rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
                exact (Nat.sub_add_sub_cancel (le_of_lt hnd_le_p) (le_of_lt hnd_dec)).symm ▸
                  (Nat.add_comm _ _).symm ▸ rfl

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- Every signed remainder sequence terminates. -/
lemma SRemS_terminates (P Q : K[X]) (hP : P ≠ 0) :
    ∃ k : ℕ, SRemS P Q (k + 1) = 0 ∧ SRemS P Q k ≠ 0 := by
  by_contra h
  push_neg at h
  by_cases hQ : Q = 0
  · have h0 := h 0 (by simp [SRemS_snd, hQ])
    exact absurd h0 (by simp [SRemS_fst, hP])
  · have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS_snd, hQ]
    have h_all : ∀ k, SRemS P Q (k + 1) ≠ 0 := by
      intro k; induction k with
      | zero => exact h1
      | succ n ih =>
        intro heq
        exact absurd (h (n + 1) heq) ih
    have h_dec : ∀ k, (SRemS P Q (k + 2)).natDegree < (SRemS P Q (k + 1)).natDegree := by
      intro k
      exact Polynomial.natDegree_lt_natDegree (h_all (k + 1)) (degree_SRemS_lt P Q k (h_all k))
    have h_le : ∀ k, (SRemS P Q (k + 1)).natDegree + k ≤ (SRemS P Q 1).natDegree := by
      intro k; induction k with
      | zero => exact Nat.le_refl _
      | succ n ih =>
        have hstep : (SRemS P Q (n + 1 + 1)).natDegree < (SRemS P Q (n + 1)).natDegree := h_dec n
        omega
    have h_out := h_le ((SRemS P Q 1).natDegree + 1)
    omega

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- The termination index k where SRemS(k+1) = 0 -/
noncomputable def sremTermIndex (P Q : K[X]) : ℕ :=
  if hP : P = 0 then 0 else Classical.choose (SRemS_terminates P Q hP)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
lemma SRemS_sremTermIndex_succ_eq_zero (P Q : K[X]) (hP : P ≠ 0) :
    SRemS P Q (sremTermIndex P Q + 1) = 0 := by
  rw [sremTermIndex, dif_neg hP]
  exact (Classical.choose_spec (SRemS_terminates P Q hP)).1

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
lemma SRemS_sremTermIndex_ne_zero (P Q : K[X]) (hP : P ≠ 0) :
    SRemS P Q (sremTermIndex P Q) ≠ 0 := by
  rw [sremTermIndex, dif_neg hP]
  exact (Classical.choose_spec (SRemS_terminates P Q hP)).2

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
lemma SRemS_ne_zero_of_le_sremTermIndex (P Q : K[X]) (hP : P ≠ 0) (i : ℕ) (hi : i ≤ sremTermIndex P Q) :
    SRemS P Q i ≠ 0 := by
  cases i with
  | zero => simp [SRemS_fst, hP]
  | succ p =>
    exact SRemS_ne_zero_of_le P Q _ _ (SRemS_sremTermIndex_succ_eq_zero P Q hP) (SRemS_sremTermIndex_ne_zero P Q hP) (by omega) hi

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
open Classical in
/-- BPR Proposition 1.9 (Helper): Assumes deg Q ≤ deg P -/
theorem proposition_1_9_aux {P Q G : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hle : Q.degree ≤ P.degree)
    (hG : IsGCD G P Q)
    (hnd_g : G.natDegree < Q.natDegree) :
    ∃ U V : K[X],
      U * P + V * Q = G ∧
      U.natDegree < Q.natDegree - G.natDegree ∧
      V.natDegree < P.natDegree - G.natDegree := by
  obtain ⟨k, hk_def⟩ : ∃ k, k = sremTermIndex P Q := ⟨_, rfl⟩
  have hk : SRemS P Q (k + 1) = 0 := hk_def ▸ SRemS_sremTermIndex_succ_eq_zero P Q hP
  have hk_ne : SRemS P Q k ≠ 0 := hk_def ▸ SRemS_sremTermIndex_ne_zero P Q hP
  have hGk := prop_1_8 hk hk_ne
  have hassoc := isGCD_associated hG hGk
  obtain ⟨c, hc⟩ := hassoc.symm
  have hG_nd : G.natDegree = (SRemS P Q k).natDegree := by
    rw [← hc, Polynomial.natDegree_mul hk_ne (Units.ne_zero c),
        Polynomial.natDegree_coe_units c]; omega
  have hk2 : k ≥ 2 := by

    cases k with
    | zero =>
      have : G.natDegree = P.natDegree := by simp [SRemS_fst] at hG_nd; exact hG_nd
      have h1 := Polynomial.natDegree_le_natDegree hle
      omega
    | succ k' =>
      cases k' with
      | zero =>
        have : G.natDegree = Q.natDegree := by simp [SRemS_snd] at hG_nd; exact hG_nd
        omega
      | succ k'' => omega
  refine ⟨SRemU P Q k * ↑c, SRemV P Q k * ↑c, ?_, ?_, ?_⟩
  · have hbez := lemma_1_11_bezout P Q k
    calc SRemU P Q k * ↑c * P + SRemV P Q k * ↑c * Q
      _ = (SRemU P Q k * P + SRemV P Q k * Q) * ↑c := by ring
      _ = SRemS P Q k * ↑c := by rw [hbez]
      _ = G := hc
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hk1_ne : SRemS P Q (k' + 1) ≠ 0 :=
      SRemS_ne_zero_of_le P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega)
    have hdegU := lemma_1_11_degU P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega) hP hQ hle
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- k = 2
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS_snd]; exact hQ
      have hne_u : SRemU P Q 2 ≠ 0 := by
        rw [SRemU_ss P Q 0 h1]
        simp [SRemU, SRemS]
      rw [Polynomial.natDegree_mul hne_u (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegU, hG_nd]
      -- Goal: Q.natDegree - SRemS P Q 1.natDegree < Q.natDegree - SRemS P Q 2.natDegree
      -- SRemS P Q 1 is Q, so Q.natDegree - Q.natDegree = 0
      -- We need 0 < Q.natDegree - SRemS P Q 2.natDegree, which is SRemS(2) < Q
      have hqnd : (SRemS P Q 1).natDegree = Q.natDegree := by simp [SRemS_snd]
      rw [hqnd, Nat.sub_self]
      apply Nat.sub_pos_of_lt
      rw [← hG_nd]; exact hnd_g
    · -- k > 2 (so k' > 0)
      have hk1_lt_q : (SRemS P Q (k' + 1)).natDegree < Q.natDegree := by
        have := natDegree_SRemS_lt_of_lt P Q 0 k' hk' (fun l hl1 hl2 =>
          SRemS_ne_zero_of_le P Q (k' + 2) l hk hk_ne (by omega) (by omega))
        simp [SRemS_snd] at this; exact this
      have hne_u : SRemU P Q (k' + 2) ≠ 0 := by
        intro heq; rw [heq, Polynomial.natDegree_zero] at hdegU
        exact absurd hdegU (ne_of_gt (Nat.sub_pos_of_lt hk1_lt_q)).symm
      rw [Polynomial.natDegree_mul hne_u (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegU, hG_nd]
      have h_strict : (SRemS P Q (k' + 2)).natDegree < (SRemS P Q (k' + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hk_ne (degree_SRemS_lt P Q k' hk1_ne)
      exact Nat.sub_lt_sub_left (lt_trans h_strict hk1_lt_q) h_strict
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hk1_ne : SRemS P Q (k' + 1) ≠ 0 :=
      SRemS_ne_zero_of_le P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega)
    have hdegV := lemma_1_11_degV P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega) hP hQ hle
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- k = 2
      -- We must show (SRemV 2 * c).natDegree < P.natDegree - G.natDegree
      have h1 : (SRemS P Q 1).natDegree = Q.natDegree := by simp [SRemS_snd]
      have hG_lt_P : G.natDegree < P.natDegree :=
        lt_of_lt_of_le hnd_g (Polynomial.natDegree_le_natDegree hle)
      by_cases hV : SRemV P Q 2 = 0
      · rw [hV, zero_mul, Polynomial.natDegree_zero]
        exact Nat.sub_pos_of_lt hG_lt_P
      · rw [Polynomial.natDegree_mul hV (Units.ne_zero c),
            Polynomial.natDegree_coe_units c, add_zero, hdegV, h1]
        exact Nat.sub_lt_sub_left hG_lt_P hnd_g
    · -- k > 2 (so k' > 0)
      have hk1_lt_q : (SRemS P Q (k' + 1)).natDegree < Q.natDegree := by
        have := natDegree_SRemS_lt_of_lt P Q 0 k' hk' (fun l hl1 hl2 =>
          SRemS_ne_zero_of_le P Q (k' + 2) l hk hk_ne (by omega) (by omega))
        simp [SRemS_snd] at this; exact this
      have hk1_lt_p : (SRemS P Q (k' + 1)).natDegree < P.natDegree :=
        lt_of_lt_of_le hk1_lt_q (Polynomial.natDegree_le_natDegree hle)
      have hne_v : SRemV P Q (k' + 2) ≠ 0 := by
        intro heq; rw [heq, Polynomial.natDegree_zero] at hdegV
        exact absurd hdegV (ne_of_gt (Nat.sub_pos_of_lt hk1_lt_p)).symm
      rw [Polynomial.natDegree_mul hne_v (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegV, hG_nd]
      have h_strict : (SRemS P Q (k' + 2)).natDegree < (SRemS P Q (k' + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hk_ne (degree_SRemS_lt P Q k' hk1_ne)
      exact Nat.sub_lt_sub_left (lt_trans h_strict hk1_lt_p) h_strict

/-- BPR Proposition 1.9: If G is a greatest common divisor of P and Q,
    and G is a proper divisor in terms of degree (deg G < deg P and deg G < deg Q),
    then there exist U and V with U·P + V·Q = G such that
    natDeg(U) < natDeg(Q) − natDeg(G) and natDeg(V) < natDeg(P) − natDeg(G). -/
theorem proposition_1_9 {P Q G : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hG : IsGCD G P Q)
    (hnd_gP : G.natDegree < P.natDegree)
    (hnd_gQ : G.natDegree < Q.natDegree) :
    ∃ U V : K[X],
      U * P + V * Q = G ∧
      U.natDegree < Q.natDegree - G.natDegree ∧
      V.natDegree < P.natDegree - G.natDegree := by
  by_cases hle : Q.degree ≤ P.degree
  · exact proposition_1_9_aux hP hQ hle hG hnd_gQ
  · have hle' : P.degree ≤ Q.degree := by
      push_neg at hle; exact le_of_lt hle
    have hG' : IsGCD G Q P := hG.symm
    obtain ⟨U, V, hbez, hdegU, hdegV⟩ := proposition_1_9_aux hQ hP hle' hG' hnd_gP
    refine ⟨V, U, ?_, hdegV, hdegU⟩
    rw [add_comm, hbez]

/-- BPR Lemma 1.10 (b): U_i V_{i+1} - V_i U_{i+1} = 1.
    Note: BPR states this is (-1)^i, but this was due to an error in their recursion
    for U and V which omitted the signed remainder negation. -/
lemma lemma_1_10_b {P Q : K[X]} (n : ℕ) (hn : ∀ i ≤ n, SRemS P Q i ≠ 0) :
    SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) = 1 := by
  induction n generalizing P Q with
  | zero =>
    dsimp [SRemU, SRemV]
    ring
  | succ n ih =>
    have hn_ne : SRemS P Q (n + 1) ≠ 0 := hn (n + 1) (by omega)
    have hn_ne' : ∀ i ≤ n, SRemS P Q i ≠ 0 := fun i hi => hn i (by omega)
    have ih_app := ih hn_ne'
    have H_U : SRemU P Q (n + 2) = - SRemU P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1) := by
      rw [SRemU, if_neg hn_ne]
    have H_V : SRemV P Q (n + 2) = - SRemV P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1) := by
      rw [SRemV, if_neg hn_ne]
    rw [H_U, H_V]
    calc SRemU P Q (n + 1) * (-SRemV P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemV P Q (n + 1)) - SRemV P Q (n + 1) * (-SRemU P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemU P Q (n + 1))
      _ = SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) := by ring
      _ = 1 := by rw [ih_app]

theorem proposition_1_12 {P Q: K[X]} (hP : P ≠ 0) (_hQ : Q ≠ 0) :
    (SRemU P Q (sremTermIndex P Q + 1) * P = - SRemV P Q (sremTermIndex P Q + 1) * Q) ∧
    IsLCM (SRemU P Q (sremTermIndex P Q + 1) * P) P Q := by
  obtain ⟨k, hk_def⟩ : ∃ x, x = sremTermIndex P Q := ⟨_, rfl⟩
  have hk : SRemS P Q (k + 1) = 0 := hk_def ▸ SRemS_sremTermIndex_succ_eq_zero P Q hP
  have hk_ne : SRemS P Q k ≠ 0 := hk_def ▸ SRemS_sremTermIndex_ne_zero P Q hP
  have h_le : ∀ i ≤ k, SRemS P Q i ≠ 0 := hk_def ▸ SRemS_ne_zero_of_le_sremTermIndex P Q hP
  rw [← hk_def]
  constructor
  · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
      lemma_1_11_bezout P Q (k + 1)
    rw [hk] at hbez
    calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
      _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
      _ = - SRemV P Q (k + 1) * Q := by ring
  · constructor
    · exact dvd_mul_left P (SRemU P Q (k + 1))
    · constructor
      · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemU P Q (k + 1) * P = - SRemV P Q (k + 1) * Q := by
          calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
            _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
            _ = - SRemV P Q (k + 1) * Q := by ring
        rw [H1]
        exact dvd_mul_left Q (- SRemV P Q (k + 1))
      · intro D hDP hDQ
        obtain ⟨A, hA⟩ := hDP
        obtain ⟨B, hB⟩ := hDQ
        have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemV P Q (k + 1) * Q = - SRemU P Q (k + 1) * P := by
          calc SRemV P Q (k + 1) * Q = SRemV P Q (k + 1) * Q + SRemU P Q (k + 1) * P - SRemU P Q (k + 1) * P := by ring
            _ = (SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q) - SRemU P Q (k + 1) * P := by ring
            _ = 0 - SRemU P Q (k + 1) * P := by rw [← hbez]
            _ = - SRemU P Q (k + 1) * P := by ring
        have H_alg : D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by
          calc D = D * 1 := by ring
            _ = D * (SRemU P Q k * SRemV P Q (k + 1) - SRemV P Q k * SRemU P Q (k + 1)) := by
                rw [← lemma_1_10_b k h_le]
            _ = D * SRemU P Q k * SRemV P Q (k + 1) - D * SRemV P Q k * SRemU P Q (k + 1) := by ring
            _ = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) - (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by
                have h1 : D * SRemU P Q k * SRemV P Q (k + 1) = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) := by rw [hB]
                have h2 : D * SRemV P Q k * SRemU P Q (k + 1) = (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by rw [hA]
                rw [h1, h2]
            _ = B * SRemU P Q k * (SRemV P Q (k + 1) * Q) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by ring
            _ = B * SRemU P Q k * (- SRemU P Q (k + 1) * P) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by
                rw [H1]
            _ = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by ring
        have H_d : D = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by
          calc D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := H_alg
            _ = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by ring
        exact ⟨_, H_d⟩


omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Definition 1.13: Greatest common divisor of a finite family of polynomials. -/
def IsListGCD (G : K[X]) (Ps : List K[X]) : Prop :=
  (∀ P ∈ Ps, G ∣ P) ∧ (∀ D, (∀ P ∈ Ps, D ∣ P) → D ∣ G)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Algorithm to obtain the GCD of a family inductively. -/
noncomputable def listGcd (Ps : List K[X]) : K[X] :=
  Ps.foldr gcd 0

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- The algorithm `listGcd` satisfies the `IsListGCD` specification. -/
theorem listGcd_isListGCD (Ps : List K[X]) : IsListGCD (listGcd Ps) Ps := by
  induction Ps with
  | nil =>
    simp [IsListGCD, listGcd]
  | cons P Ps ih =>
    simp [IsListGCD, listGcd] at *
    constructor
    · constructor
      · exact (gcd_isGCD P (Ps.foldr gcd 0)).1
      · intro P' hP'
        have hG := (gcd_isGCD P (Ps.foldr gcd 0)).2.1
        exact dvd_trans hG (ih.1 P' hP')
    · intro D h1 h2
      exact (gcd_isGCD P (Ps.foldr gcd 0)).2.2 D h1 (ih.2 D h2)

omit [IsAlgClosed C] in
/-- Helper lemma: x is a root of gcd A B iff x is a root of A and B. -/
lemma aeval_gcd_eq_zero_iff [Algebra K C] (A B : K[X]) (x : C) :
    aeval x (gcd A B) = 0 ↔ (aeval x A = 0 ∧ aeval x B = 0) := by
  constructor
  · intro h
    have ⟨CA, hpA⟩ : gcd A B ∣ A := gcd_dvd_left A B
    have ⟨CB, hpB⟩ : gcd A B ∣ B := gcd_dvd_right A B
    have h1 : aeval x A = 0 := by
      calc
        aeval x A = aeval x (gcd A B * CA) := congrArg _ hpA
        _ = aeval x (gcd A B) * aeval x CA := map_mul _ _ _
        _ = 0 * aeval x CA := by rw [h]
        _ = 0 := zero_mul _
    have h2 : aeval x B = 0 := by
      calc
        aeval x B = aeval x (gcd A B * CB) := congrArg _ hpB
        _ = aeval x (gcd A B) * aeval x CB := map_mul _ _ _
        _ = 0 * aeval x CB := by rw [h]
        _ = 0 := zero_mul _
    exact ⟨h1, h2⟩
  · rintro ⟨hA, hB⟩
    have hspan : gcd A B ∈ Ideal.span {A, B} :=
      span_gcd A B ▸ Ideal.mem_span_singleton.mpr (dvd_refl (gcd A B))
    have ⟨U, V, hUV⟩ := Submodule.mem_span_pair.mp hspan
    have hUV' : aeval x (U * A + V * B) = aeval x (gcd A B) := congrArg _ hUV
    calc
      aeval x (gcd A B) = aeval x (U * A + V * B) := hUV'.symm
      _ = aeval x U * aeval x A + aeval x V * aeval x B := by simp
      _ = aeval x U * 0 + aeval x V * 0 := by rw [hA, hB]
      _ = 0 := by ring

omit [IsAlgClosed C] in
/-- Unnumbered Theorem (post Prop 1.13): x ∈ C is a root of every polynomial in 𝒫 if and only if it is a root of gcd(𝒫). -/
theorem isRoot_listGcd_iff_forall_isRoot [Algebra K C] {Ps : List K[X]} {x : C} :
    aeval x (listGcd Ps) = 0 ↔ ∀ P ∈ Ps, aeval x P = 0 := by
  induction Ps with
  | nil =>
    simp [listGcd]
  | cons P Ps ih =>
    simp [listGcd, aeval_gcd_eq_zero_iff]
    intro _
    rwa [← listGcd]

omit [IsAlgClosed C] in
/-- Unnumbered Theorem (post Prop 1.13): x ∈ C is not a root of any polynomial in 𝒬 if and only if it is not a root of ∏ 𝒬. -/
theorem not_isRoot_listProd_iff_forall_not_isRoot [Algebra K C] {Qs : List K[X]} {x : C} :
    aeval x (Qs.prod) ≠ 0 ↔ (∀ Q ∈ Qs, aeval x Q ≠ 0) := by
  induction Qs with
  | nil =>
    simp
  | cons Q Qs ih =>
    simp [List.prod_cons]
    intro _
    exact ih

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Unnumbered Theorem (post Prop 1.13): Every root of P in C is a root of Q if and only if P ∣ Q^(deg P). Explicitly requires P ≠ 0. -/
theorem isRoot_subset_iff_dvd_pow [Algebra K C] [DecidableEq K] [DecidableEq C] {P Q : K[X]} (hP : P ≠ 0) :
    (∀ x : C, aeval x P = 0 → aeval x Q = 0) ↔ P ∣ Q ^ P.natDegree := by
  constructor
  · intro h
    by_cases hQ : Q = 0
    · simp [hQ]
      by_cases hP0 : P.natDegree = 0
      · have hDeg : P.degree = 0 := by rw [degree_eq_natDegree hP, hP0, Nat.cast_zero]
        have hUnit : IsUnit P := isUnit_iff_degree_eq_zero.mpr hDeg
        exact IsUnit.dvd hUnit
      · have hPowPos : 0 < P.natDegree := by omega
        have hPow : (0 : K[X]) ^ P.natDegree = 0 := zero_pow hPowPos.ne'
        rw [hPow]
        exact dvd_zero P
    · have Hdvd : P.map (algebraMap K C) ∣ (Q.map (algebraMap K C)) ^ P.natDegree := by
        have hP' : P.map (algebraMap K C) ≠ 0 := by
          intro contra
          have := Polynomial.map_eq_zero_iff (RingHom.injective (algebraMap K C)) |>.mp contra
          exact hP this
        have hQ' : Q.map (algebraMap K C) ≠ 0 := by
          intro contra
          have := Polynomial.map_eq_zero_iff (RingHom.injective (algebraMap K C)) |>.mp contra
          exact hQ this
        have H : ∀ x : C, x ∈ (P.map (algebraMap K C)).roots → x ∈ (Q.map (algebraMap K C)).roots := by
          intro x hx
          have hx' : eval x (P.map (algebraMap K C)) = 0 := (mem_roots hP').mp hx
          have hx_aeval : aeval x P = 0 := by
            change eval₂ (algebraMap K C) x P = 0
            rw [← eval_map]
            exact hx'
          have hQx : aeval x Q = 0 := h x hx_aeval
          have hQx_eval : eval₂ (algebraMap K C) x Q = 0 := hQx
          exact (mem_roots hQ').mpr (by rwa [← eval_map] at hQx_eval)
        rw [IsAlgClosed.dvd_iff_roots_le_roots hP' (pow_ne_zero _ hQ')]
        rw [roots_pow _ P.natDegree]
        apply Multiset.le_iff_count.mpr
        intro x
        rw [Multiset.count_nsmul]
        by_cases hx : x ∈ (P.map (algebraMap K C)).roots
        · have hQx := H x hx
          have h1 : 1 ≤ Multiset.count x (Q.map (algebraMap K C)).roots := Multiset.count_pos.mpr hQx
          have h3 : Multiset.count x (P.map (algebraMap K C)).roots ≤ (P.map (algebraMap K C)).roots.card := Multiset.count_le_card x _
          have h4 : (P.map (algebraMap K C)).roots.card ≤ (P.map (algebraMap K C)).natDegree := card_roots' (P.map (algebraMap K C))
          have h5 : (P.map (algebraMap K C)).natDegree = P.natDegree := natDegree_map_eq_of_injective (RingHom.injective _) P
          have h6 : Multiset.count x (P.map (algebraMap K C)).roots ≤ P.natDegree := by omega
          have h7 : P.natDegree ≤ P.natDegree * Multiset.count x (Q.map (algebraMap K C)).roots := Nat.le_mul_of_pos_right _ h1
          omega
        · have h0 : Multiset.count x (P.map (algebraMap K C)).roots = 0 := Multiset.count_eq_zero.mpr hx
          omega
      have Hpow : (Q.map (algebraMap K C)) ^ P.natDegree = (Q ^ P.natDegree).map (algebraMap K C) := by
        simp only [Polynomial.map_pow]
      rw [Hpow] at Hdvd
      exact (Polynomial.map_dvd_map' (algebraMap K C)).mp Hdvd
  · intro h x hx
    have H_dvd : aeval x P ∣ aeval x (Q ^ P.natDegree) := map_dvd (aeval x) h
    rw [hx] at H_dvd
    have H_0 : aeval x (Q ^ P.natDegree) = 0 := zero_dvd_iff.mp H_dvd
    rw [map_pow] at H_0
    exact eq_zero_of_pow_eq_zero H_0


end Azurite.BPR
