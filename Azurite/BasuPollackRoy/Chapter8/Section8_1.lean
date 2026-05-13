import Azurite.BasuPollackRoy.Chapter8.Section8_1.ComputationStructures
import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeBounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.CompareEmbed
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 8: Complexity of Basic Algorithms
## Section 8.1: Definition of Complexity

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006, pp. 281–284.

The hierarchy of BPR's seven algebraic computation structures and the
auxiliary classes `HasIntDiv` and `HasExactDiv` live in
`Section8_1.ComputationStructures`. This file covers the algorithms and
size bounds that follow.
-/

namespace Azurite.BPR

-- Algorithms 8.1 (addition), 8.2 (multiplication), and 8.3 (Euclidean
-- division) are exposition-only: they describe Azurite's existing
-- `AzPolynomial` operations and their equivalences with Mathlib's
-- `Polynomial`. They live in the blueprint
-- (`chapter8/section8_1/algorithm8_*.tex`) and reference the
-- corresponding Lean definitions in `Azurite.AzPolynomial.{Add, Mul,
-- QuoRem}` and the equivalence files under `Azurite.AzPolynomial.Equiv.*`.

/-!
## Algorithm 8.4. Addition of Multivariate Polynomials

Given multivariate polynomials `P` and `Q` over a ring `D` in `k`
variables, compute `P + Q` by merging their monomial lists and
combining like terms.

**Azurite implementation:** `Azurite.AzMvPolynomial`

See: `Azurite.AzMvPolynomial.Add`

The equivalence with Mathlib's `MvPolynomial` addition is proved in
`Azurite.AzMvPolynomial.Equiv.Add`.
-/

/-!
## Lemma 8.6. Counting monomials by degree

The number of monomials of degree `≤ d` in `k` variables is `(d + k).choose k`.

We construct the actual `Finset` of exponent tuples `Fin k → ℕ` with sum `≤ d`,
prove a membership characterisation, and compute its cardinality. The proof
uses the hockey-stick identity (`Nat.sum_range_add_choose`) from Mathlib.

We then lift the result to `MonicMonomial`, Azurite's concrete monomial type.
-/

open Matrix MonomialOrder

/-- The finite set of exponent tuples `Fin k → ℕ` whose sum is `≤ d`.
    These are the exponent vectors of monic monomials of degree `≤ d`
    in `k` variables. -/
def monicMonomials : (k : ℕ) → (d : ℕ) → Finset (Fin k → ℕ)
  | 0, _ => {Fin.elim0}
  | k + 1, d => (Finset.range (d + 1)).biUnion fun j =>
      (monicMonomials k (d - j)).image (vecCons j)

/-- An exponent tuple belongs to `monicMonomials k d` iff its sum is `≤ d`. -/
theorem mem_monicMonomials {k d : ℕ} {f : Fin k → ℕ} :
    f ∈ monicMonomials k d ↔ ∑ i, f i ≤ d := by
  induction k generalizing d with
  | zero =>
    simp only [monicMonomials, Finset.mem_singleton, Fintype.sum_empty]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Subsingleton.elim _ _⟩
  | succ k ih =>
    simp only [monicMonomials, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, g, hg, rfl⟩
      simp only [vecCons, Fin.sum_cons]; rw [ih] at hg; omega
    · intro hle
      have hsum : ∑ i, f i = f 0 + ∑ i, Fin.tail f i := by
        conv_lhs => rw [← Fin.cons_self_tail f]; rw [Fin.sum_cons]
      refine ⟨f 0, ?_, Fin.tail f, ?_, Fin.cons_self_tail f⟩
      · omega
      · rw [ih]; omega

private theorem vecCons_injective_right {n : ℕ} (j : ℕ) :
    Function.Injective (vecCons j : (Fin n → ℕ) → Fin (n + 1) → ℕ) := by
  intro a b h; ext i; have := congr_fun h i.succ
  simp [vecCons, Fin.cons] at this; exact this

private theorem monicMonomials_pairwiseDisjoint (k d : ℕ) :
    Set.PairwiseDisjoint (Finset.range (d + 1) : Set ℕ)
      (fun j => (monicMonomials k (d - j)).image (vecCons j)) := by
  intro j₁ _ j₂ _ hne
  simp only [Finset.disjoint_left, Finset.mem_image]
  rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
  exact hne (by have := congr_fun h 0; simp [vecCons, Fin.cons] at this; exact this.symm)

/-- **BPR Lemma 8.6.** The number of monic monomials of degree `≤ d` in `k`
    variables is `(d + k).choose k`. -/
theorem card_monicMonomials (k d : ℕ) :
    (monicMonomials k d).card = (d + k).choose k := by
  induction k generalizing d with
  | zero => simp [monicMonomials]
  | succ k ih =>
    rw [monicMonomials, Finset.card_biUnion (monicMonomials_pairwiseDisjoint k d)]
    simp only [Finset.card_image_of_injective _ (vecCons_injective_right _), ih]
    rw [show d + (k + 1) = d + k + 1 from by omega, ← Nat.sum_range_add_choose d k]
    apply Finset.sum_bij' (fun i _ => d - i) (fun i _ => d - i)
    · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intros; rfl

-- Sanity checks
#guard (monicMonomials 0 5).card = 1
#guard (monicMonomials 1 3).card = 4
#guard (monicMonomials 2 2).card = 6   -- 1, x₀, x₁, x₀², x₀x₁, x₁²
#guard (monicMonomials 3 1).card = 4
#guard (monicMonomials 3 3).card = 20

/-! ### MonicMonomial bridge -/

variable {n : ℕ} (ord : MonomialOrder)

private theorem ofFn_mk_injective :
    Function.Injective (fun f : Fin n → ℕ => (⟨Vector.ofFn f⟩ : MonicMonomial n ord)) := by
  intro a b h
  simp only [MonicMonomial.mk.injEq] at h
  exact funext (fun i => by
    have : (Vector.ofFn a)[i] = (Vector.ofFn b)[i] := by rw [h]
    simpa using this)

/-- The finite set of `MonicMonomial`s of total degree `≤ d`. -/
def MonicMonomial.finsetLeD (d : ℕ) : Finset (MonicMonomial n ord) :=
  (monicMonomials n d).image (fun f => ⟨Vector.ofFn f⟩)

/-- A `MonicMonomial` belongs to `finsetLeD` iff its total degree is `≤ d`. -/
theorem MonicMonomial.mem_finsetLeD {d : ℕ} {m : MonicMonomial n ord} :
    m ∈ MonicMonomial.finsetLeD ord d ↔ m.totalDegree ≤ d := by
  simp only [finsetLeD, Finset.mem_image, mem_monicMonomials]
  constructor
  · rintro ⟨f, hf, hm⟩
    rw [MonicMonomial.totalDegree, ← hm, totalDeg_eq_finsum]
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]; exact hf
  · intro hle
    refine ⟨fun i => m.exponents[i], ?_, ?_⟩
    · rw [MonicMonomial.totalDegree, totalDeg_eq_finsum] at hle
      convert hle using 1
    · ext : 1; ext i : 1; simp

/-- **BPR Lemma 8.6 (MonicMonomial form).** The number of monic monomials
    of total degree `≤ d` in `n` variables is `(d + n).choose n`. -/
theorem MonicMonomial.card_finsetLeD (d : ℕ) :
    (MonicMonomial.finsetLeD ord d : Finset (MonicMonomial n ord)).card =
    (d + n).choose n := by
  rw [finsetLeD, Finset.card_image_of_injective _ (ofFn_mk_injective (ord := ord)),
      card_monicMonomials]

/-! ### Upper bound on binomial coefficient -/

/-- `(d + n).choose n ≤ (d + 1) ^ n`.
    Proof: by induction on `n`, using the hockey-stick identity to decompose
    `(d + n + 1).choose (n + 1) = ∑ i ≤ d, (i + n).choose n ≤ (d + 1) · (d + n).choose n`. -/
theorem choose_add_le_pow (d n : ℕ) : (d + n).choose n ≤ (d + 1) ^ n := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    rw [show d + (n + 1) = d + n + 1 from by omega, ← Nat.sum_range_add_choose d n]
    calc ∑ i ∈ Finset.range (d + 1), (i + n).choose n
        ≤ ∑ _i ∈ Finset.range (d + 1), (d + n).choose n := by
          apply Finset.sum_le_sum
          intro i hi; apply Nat.choose_le_choose
          simp only [Finset.mem_range] at hi; omega
      _ = (d + 1) * (d + n).choose n := by
          simp [Finset.sum_const, Finset.card_range]
      _ ≤ (d + 1) * (d + 1) ^ n := Nat.mul_le_mul_left _ (ih d)
      _ = (d + 1) ^ (n + 1) := by ring

/-- Corollary: the number of monic monomials of degree `≤ d` in `k` variables
    is at most `(d + 1) ^ k`. -/
theorem card_monicMonomials_le_pow (k d : ℕ) :
    (monicMonomials k d).card ≤ (d + 1) ^ k :=
  card_monicMonomials k d ▸ choose_add_le_pow d k

/-- Corollary (MonicMonomial form): the number of monic monomials of total
    degree `≤ d` in `n` variables is at most `(d + 1) ^ n`. -/
theorem MonicMonomial.card_finsetLeD_le_pow (d : ℕ) :
    (MonicMonomial.finsetLeD ord d : Finset (MonicMonomial n ord)).card ≤
      (d + 1) ^ n := by
  rw [MonicMonomial.card_finsetLeD]; exact choose_add_le_pow d n

/-!
### Bitsize of summing two polynomials

BPR (unnumbered lemma, §8.1): if the bitsizes of the coefficients of
multivariate polynomials `P` and `Q` over `ℤ` are bounded by `τ`,
the bitsizes of the coefficients of their sum `P + Q` are bounded by `τ + 1`.

Proof: for each monomial `m`, `coeff m (P + Q) = coeff m P + coeff m Q`.
Since `|a + b| ≤ |a| + |b| < 2^τ + 2^τ = 2^{τ+1}`.
-/

/-- `bitsize(a + b) ≤ τ + 1` when `bitsize a ≤ τ` and `bitsize b ≤ τ`. -/
theorem Int.size_add_le (a b : ℤ) (τ : ℕ)
    (ha : a.natAbs.size ≤ τ) (hb : b.natAbs.size ≤ τ) :
    (a + b).natAbs.size ≤ τ + 1 := by
  rw [Nat.size_le] at ha hb ⊢
  have hab : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have : 2 ^ τ + 2 ^ τ = 2 ^ (τ + 1) := by rw [pow_succ]; omega
  omega

/-- **BPR §8.1 (unnumbered lemma).** Adding two multivariate polynomials
    over `ℤ` whose coefficient bitsizes are bounded by `τ` produces a
    polynomial whose coefficient bitsizes are bounded by `τ + 1`. -/
theorem MvPolynomial.bitsize_coeff_add_le {σ : Type _}
    {P Q : MvPolynomial σ ℤ} {τ : ℕ}
    (hP : ∀ m, (MvPolynomial.coeff m P).natAbs.size ≤ τ)
    (hQ : ∀ m, (MvPolynomial.coeff m Q).natAbs.size ≤ τ) :
    ∀ m, (MvPolynomial.coeff m (P + Q)).natAbs.size ≤ τ + 1 := by
  intro m
  rw [MvPolynomial.coeff_add]
  exact Int.size_add_le _ _ τ (hP m) (hQ m)

/-!
### Algorithm 8.5. Multiplication of Multivariate Polynomials

Given multivariate polynomials `P` and `Q` over a ring `D` in `k`
variables, compute `P * Q`.

**Azurite implementation:** `Azurite.AzMvPolynomial`

See: `Azurite.AzMvPolynomial.Mul`
-/

/-!
### Algorithm 8.6. Exact Division of Multivariate Polynomials

Given multivariate polynomials `P` and `Q` over a field `K` in `k`
variables, where `Q` divides `P`, compute `C` such that `P = C * Q`.

The algorithm repeatedly subtracts `(leadTerm R / leadTerm Q) * Q`
from the remainder `R`, accumulating the quotient monomials in `C`.

**Azurite implementation:** `Azurite.AzMvPolynomial.ExactDiv`

See: `Azurite.AzMvPolynomial.exactDiv`
-/

/-!
### Bitsize of multiplying two polynomials

BPR (unnumbered lemma, §8.1): if `P` and `Q` are multivariate polynomials
over `ℤ` in `k` variables, with coefficient bitsizes bounded by `τ` and `σ`
respectively, and `totalDegree Q ≤ q`, then the coefficient bitsizes of
`P * Q` are bounded by `τ + σ + k * Nat.size (q + 1)`.

Proof by induction on `k` using `MvPolynomial.finSuccEquiv`.
-/

/-- `bitsize(a * b) ≤ τ + σ` when `bitsize a ≤ τ` and `bitsize b ≤ σ`. -/
theorem Int.size_mul_le (a b : ℤ) (τ σ : ℕ)
    (ha : a.natAbs.size ≤ τ) (hb : b.natAbs.size ≤ σ) :
    (a * b).natAbs.size ≤ τ + σ := by
  rw [Nat.size_le] at ha hb ⊢
  rw [Int.natAbs_mul, show 2 ^ (τ + σ) = 2 ^ τ * 2 ^ σ from pow_add 2 τ σ]
  exact Nat.mul_lt_mul_of_lt_of_lt ha hb

/-- Triangle inequality for `Finset` sums of integers (`natAbs`). -/
theorem Int.natAbs_finset_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ihs _)

/-- Bitsize of a `Finset` sum of integers, bounded by element bound + `Nat.size` of card. -/
theorem Int.size_finset_sum_le {ι : Type _} {s : Finset ι} {f : ι → ℤ} {B : ℕ}
    (hB : ∀ i ∈ s, (f i).natAbs.size ≤ B) :
    (∑ i ∈ s, f i).natAbs.size ≤ B + Nat.size s.card := by
  rw [Nat.size_le]
  calc (∑ i ∈ s, f i).natAbs
      ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_finset_sum_le s f
    _ ≤ ∑ _i ∈ s, (2 ^ B : ℕ) :=
        Finset.sum_le_sum fun i hi => Nat.le_of_lt (Nat.size_le.mp (hB i hi))
    _ = s.card * 2 ^ B := by simp [Finset.sum_const, smul_eq_mul]
    _ < 2 ^ s.card.size * 2 ^ B :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.two_pow_pos _)
    _ = 2 ^ (B + s.card.size) := by rw [← pow_add]; congr 1; omega

private theorem Finsupp.antidiag_fin0 :
    Finset.antidiagonal (0 : Fin 0 →₀ ℕ) = {(0, 0)} := by
  ext ⟨a, b⟩; simp only [Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
  exact ⟨fun _ => ⟨Finsupp.ext (fun i => i.elim0), Finsupp.ext (fun i => i.elim0)⟩,
         fun ⟨ha, hb⟩ => by subst ha; subst hb; simp⟩

private theorem Finset.antidiag_filter_snd_le (l q : ℕ) :
    ((Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q)).card ≤ q + 1 := by
  have h := Finset.card_le_card_of_injOn (f := Prod.snd)
    (s := ((Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q) : Finset _))
    (t := Finset.range (q + 1))
    (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_range]; omega)
    (fun x₁ hx₁ x₂ hx₂ heq => by
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
      ext <;> [omega; exact heq])
  rwa [Finset.card_range] at h

/-- **BPR §8.1 (unnumbered lemma).** If `P, Q : MvPolynomial (Fin k) ℤ` with
    coefficient bitsizes bounded by `τ` and `σ` respectively, and
    `totalDegree Q ≤ q`, then the coefficient bitsizes of `P * Q` are
    bounded by `τ + σ + k * Nat.size (q + 1)`. Proved by induction on `k`
    using `MvPolynomial.finSuccEquiv`. -/
theorem MvPolynomial.bitsize_coeff_mul_le :
    ∀ (k : ℕ) (P Q : MvPolynomial (Fin k) ℤ) (τ σ q : ℕ),
    (∀ m, (MvPolynomial.coeff m P).natAbs.size ≤ τ) →
    (∀ m, (MvPolynomial.coeff m Q).natAbs.size ≤ σ) →
    MvPolynomial.totalDegree Q ≤ q →
    ∀ m, (MvPolynomial.coeff m (P * Q)).natAbs.size ≤ τ + σ + k * Nat.size (q + 1) := by
  intro k; induction k with
  | zero =>
    intro P Q τ σ q hP hQ _hq m
    have : m = 0 := Finsupp.ext (fun i => i.elim0)
    subst this; simp only [Nat.zero_mul, Nat.add_zero]
    rw [MvPolynomial.coeff_mul, Finsupp.antidiag_fin0, Finset.sum_singleton]
    exact Int.size_mul_le _ _ τ σ (hP 0) (hQ 0)
  | succ k ih =>
    intro P Q τ σ q hP hQ hq m
    rw [show m = Finsupp.cons (m 0) (Finsupp.tail m) from by
      ext i; cases i using Fin.cases <;> simp [Finsupp.cons, Finsupp.tail]]
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff,
        show (MvPolynomial.finSuccEquiv ℤ k) (P * Q) =
            (MvPolynomial.finSuccEquiv ℤ k) P * (MvPolynomial.finSuccEquiv ℤ k) Q
          from map_mul _ P Q,
        Polynomial.coeff_mul, MvPolynomial.coeff_sum]
    set l := m 0; set m' := Finsupp.tail m
    have hndQ : ((MvPolynomial.finSuccEquiv ℤ k) Q).natDegree ≤ q := by
      rw [MvPolynomial.natDegree_finSuccEquiv]
      exact le_trans (MvPolynomial.degreeOf_le_totalDegree Q 0) hq
    -- Filter sum to x.2 ≤ q: terms with x.2 > q have Q-coeff = 0
    rw [show ∑ x ∈ Finset.antidiagonal l,
          MvPolynomial.coeff m' (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
            ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2)
        = ∑ x ∈ (Finset.antidiagonal l).filter (fun x => x.2 ≤ q),
          MvPolynomial.coeff m' (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
            ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2) from by
      symm; apply Finset.sum_filter_of_ne
      intro x _ hne; by_contra hgt; push Not at hgt
      have : ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      exact hne (by simp [this])]
    set s := (Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q)
    -- Each term bounded by IH
    have hB : ∀ x ∈ s, (MvPolynomial.coeff m'
        (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
         ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2)).natAbs.size
        ≤ τ + σ + k * Nat.size (q + 1) := by
      intro x _hx
      apply ih _ _ τ σ q
      · intro m''; rw [MvPolynomial.finSuccEquiv_coeff_coeff]; exact hP _
      · intro m''; rw [MvPolynomial.finSuccEquiv_coeff_coeff]; exact hQ _
      · by_cases hne : ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2 = 0
        · simp [hne]
        · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q x.2 hne; omega
    calc (∑ x ∈ s, MvPolynomial.coeff m'
            (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
             ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2)).natAbs.size
        ≤ (τ + σ + k * Nat.size (q + 1)) + Nat.size s.card :=
          Int.size_finset_sum_le hB
      _ ≤ (τ + σ + k * Nat.size (q + 1)) + Nat.size (q + 1) :=
          Nat.add_le_add_left (Nat.size_le_size (Finset.antidiag_filter_snd_le l q)) _
      _ = τ + σ + (k + 1) * Nat.size (q + 1) := by ring


/-!
### Algorithm 8.6. [Exact Division of Multivariate Polynomials]

Implemented in `Azurite.AzMvPolynomial.ExactDiv`.
Correctness proofs (including the MonomialOrder bridge) are in
`Azurite.AzMvPolynomial.Equiv.ExactDiv`.
-/

end Azurite.BPR

/-!
## Notation 8.7. Horner Polynomials

Let `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]`, where `A` is a ring.
The **Horner polynomials** associated to `P` are defined inductively by

  `Hor₀(P, X) = aₚ`,
  `Horᵢ(P, X) = X · Horᵢ₋₁(P, X) + aₚ₋ᵢ`,

for `0 ≤ i ≤ p`, so that

  `Horᵢ(P, X) = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`.

In particular, `Horₚ(P, X) = P`.

Reference: BPR §8.1, Notation 8.7, p. 284.
-/

section Horner

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Notation 8.7 (Horner polynomials).** Given `P ∈ R[X]` with
    `p = natDegree P`, the `i`-th Horner polynomial is defined by:
    - `Hor₀(P, X) = C(aₚ)` (the leading coefficient as a constant polynomial)
    - `Horᵢ₊₁(P, X) = X · Horᵢ(P, X) + C(aₚ₋ᵢ₋₁)` -/
noncomputable def Polynomial.horner (P : R[X]) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => X * P.horner i + C (P.coeff (P.natDegree - (i + 1)))

/-- The base case: `Hor₀(P, X) = C(leadingCoeff P)`. -/
theorem Polynomial.horner_zero (P : R[X]) :
    P.horner 0 = C P.leadingCoeff := by
  unfold Polynomial.horner; rw [leadingCoeff]

/-- The recurrence: `Horᵢ₊₁(P, X) = X · Horᵢ(P, X) + C(aₚ₋ᵢ₋₁)`. -/
theorem Polynomial.horner_succ (P : R[X]) (i : ℕ) :
    P.horner (i + 1) = X * P.horner i + C (P.coeff (P.natDegree - (i + 1))) :=
  rfl

/-- **Closed-form characterization.**
    `Horᵢ(P, X) = ∑ j ∈ range (i+1), C(aₚ₋ⱼ) · X^{i−j}`
    `         = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`. -/
theorem Polynomial.horner_eq_sum (P : R[X]) (i : ℕ) :
    P.horner i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j)) * X ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.horner]
  | succ n ih =>
    rw [Polynomial.horner, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm X (C _ * X ^ _), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

/-- **`Horₚ(P, X) = P`.** The last Horner polynomial recovers `P`. -/
theorem Polynomial.horner_natDegree (P : R[X]) :
    P.horner P.natDegree = P := by
  rw [Polynomial.horner_eq_sum]
  conv_rhs => rw [Polynomial.as_sum_range P]
  rw [← Finset.sum_flip]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega,
      C_mul_X_pow_eq_monomial]

end Horner

/-!
## Algorithm 8.7. Evaluation of a Univariate Polynomial [Horner]

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ D[X]` and `c ∈ D`, compute `P(c)` using
Horner's method: set `b := aₚ`, then for `i = 1, …, p` update
`b := c · b + aₚ₋ᵢ`. The final value of `b` is `P(c)`.

Equivalently, this computes `Hor₀(P, c), Hor₁(P, c), …, Horₚ(P, c) = P(c)`
using Notation 8.7.

**Complexity (BPR):** `p` multiplications and `p` additions in the ring.

**Structure required:** Ring (D₀).

**Azurite implementation:** `Azurite.AzPolynomial.eval`

See: `Azurite.AzPolynomial.Eval`

The implementation uses `Array.foldr` with the Horner accumulator
`fun a acc => a + acc * x`, which is exactly Horner's method.

The equivalence with Mathlib's `Polynomial.eval` is proved in
`Azurite.AzPolynomial.Equiv.Eval`.
-/

/-!
## Algorithm 8.8. Special Evaluation of a Univariate Polynomial

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ ℤ[X]` and `b/c ∈ ℚ` with `b, c ∈ ℤ`,
compute `cᵖ P(b/c)` without leaving `ℤ`.

The algorithm is a variant of Horner's method (Algorithm 8.7) that
keeps track of a running power `d = cⁱ`:

  - Initialize `HorSpecial₀(P, b) := aₚ`,  `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `HorSpecialᵢ(P, b) := b · HorSpecialᵢ₋₁(P, b) + d · aₚ₋ᵢ`
  - Output `HorSpecialₚ(P, b) = cᵖ P(b/c)`.

**Complexity:** `2p` multiplications and `p` additions in the ring.

**Structure required:** Ring (D₀).

**Azurite implementation:** `Azurite.AzPolynomial.evalSpecial`

See: `Azurite.AzPolynomial.Eval`
-/

section HorSpecial

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.8 (Special Horner evaluation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, computes
    `cᵖ · P(b/c)` without division:
    - `horSpecial P b c 0 = aₚ`
    - `horSpecial P b c (i+1) = b · horSpecial P b c i + c^{i+1} · aₚ₋ᵢ₋₁` -/
noncomputable def Polynomial.horSpecial (P : R[X]) (b c : R) : ℕ → R
  | 0 => P.coeff P.natDegree
  | i + 1 => b * P.horSpecial b c i + c ^ (i + 1) * P.coeff (P.natDegree - (i + 1))

/-- The base case: `horSpecial P b c 0 = leadingCoeff P`. -/
theorem Polynomial.horSpecial_zero (P : R[X]) (b c : R) :
    P.horSpecial b c 0 = P.leadingCoeff := by
  unfold Polynomial.horSpecial; rw [leadingCoeff]

/-- The recurrence for `horSpecial`. -/
theorem Polynomial.horSpecial_succ (P : R[X]) (b c : R) (i : ℕ) :
    P.horSpecial b c (i + 1) =
      b * P.horSpecial b c i + c ^ (i + 1) * P.coeff (P.natDegree - (i + 1)) :=
  rfl

/-- **Closed-form characterization.**
    `horSpecial P b c i = ∑ j ∈ range (i+1), aₚ₋ⱼ · b^{i−j} · c^j`. -/
theorem Polynomial.horSpecial_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.horSpecial b c i = ∑ j ∈ range (i + 1),
      P.coeff (P.natDegree - j) * b ^ (i - j) * c ^ j := by
  induction i with
  | zero => simp [Polynomial.horSpecial]
  | succ n ih =>
    rw [Polynomial.horSpecial, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro j hj; rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 from by omega, pow_succ]; ring
    · ring

/-- **Reindexed closed form at `i = natDegree P`.**
    `horSpecial P b c p = ∑ k ∈ range (p+1), aₖ · bᵏ · c^{p−k}`. -/
theorem Polynomial.horSpecial_natDegree_eq_sum (P : R[X]) (b c : R) :
    P.horSpecial b c P.natDegree = ∑ k ∈ range (P.natDegree + 1),
      P.coeff k * b ^ k * c ^ (P.natDegree - k) := by
  rw [horSpecial_eq_sum, ← Finset.sum_flip]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega]

/-- **BPR Algorithm 8.8 (main result, over a field).**
    `horSpecial P b c p = cᵖ · P.eval(b · c⁻¹)` when `c ≠ 0`. -/
theorem Polynomial.horSpecial_natDegree_eq_eval {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) :
    P.horSpecial b c P.natDegree = c ^ P.natDegree * P.eval (b * c⁻¹) := by
  rw [horSpecial_natDegree_eq_sum, eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  rw [mul_pow, inv_pow]
  calc P.coeff k * b ^ k * c ^ (P.natDegree - k)
      = P.coeff k * (b ^ k * c ^ (P.natDegree - k)) := by ring
    _ = P.coeff k * (c ^ P.natDegree * (b ^ k * (c ^ k)⁻¹)) := by
        congr 1; rw [pow_sub₀ c hc (by omega : k ≤ P.natDegree)]; ring
    _ = c ^ P.natDegree * (P.coeff k * (b ^ k * (c ^ k)⁻¹)) := by ring

end HorSpecial

/-! ### Bitsize bound on HorSpecial -/

section HorSpecialBitsize

open Polynomial Finset

-- Each summand `a_{p-j} · b^{i-j} · c^j` has bitsize ≤ τ + i · τ'.
-- This is the product of one coefficient (bitsize ≤ τ) with i factors
-- (b or c, each of bitsize ≤ τ').
private theorem bitsize_coeff_mul_pow_le (a b c : ℤ) (i j τ τ' : ℕ)
    (hj : j ≤ i) (ha : a.natAbs.size ≤ τ)
    (hb : b.natAbs.size ≤ τ') (hc : c.natAbs.size ≤ τ') :
    (a * b ^ (i - j) * c ^ j).natAbs.size ≤ τ + i * τ' := by
  by_cases hi : i = 0
  · simp [show j = 0 from by omega, hi, ha]
  · -- The product b^{i-j} * c^j is a product of i integers each of bitsize ≤ τ'
    set L := List.replicate (i - j) b ++ List.replicate j c with hL_def
    have hne : L ≠ [] := by simp [hL_def]; omega
    have hlen : L.length = i := by simp [hL_def]; omega
    have heq : L.prod = b ^ (i - j) * c ^ j := by simp [hL_def, List.prod_replicate]
    have hprod : L.prod.natAbs.size ≤ i * τ' := by
      have := Azurite.BPR.Int.size_list_prod_le L τ' hne
        (by intro x hx; simp [hL_def, List.mem_append, List.mem_replicate] at hx
            rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
      simp [hlen, Azurite.BPR.Int.size] at this; exact this
    rw [mul_assoc, ← heq]
    exact Azurite.BPR.Int.size_mul_le a _ τ (i * τ') ha hprod

/-- **BPR §8.1 (bitsize of HorSpecial).**
    Let `P ∈ ℤ[X]` with `p = natDegree P` and coefficient bitsizes bounded by `τ`.
    Let `b, c ∈ ℤ` with `bitsize(b), bitsize(c) ≤ τ'`. Then for `i ≤ p`:

      `bitsize(horSpecial P b c i) ≤ τ + i · τ' + bitsize(p + 1)`.

    The bound comes from the closed-form sum
    `horSpecial P b c i = ∑_{j=0}^{i} a_{p-j} · b^{i-j} · c^j`:
    each summand has bitsize `≤ τ + i · τ'` (product of one coefficient of
    bitsize `τ` and `i` factors of bitsize `τ'`), and the sum of `i + 1 ≤ p + 1`
    terms adds `bitsize(p + 1)`. -/
theorem Polynomial.bitsize_horSpecial_le (P : ℤ[X]) (b c : ℤ) (i τ τ' : ℕ)
    (hi : i ≤ P.natDegree)
    (hτ : ∀ k, (P.coeff k).natAbs.size ≤ τ)
    (hb : b.natAbs.size ≤ τ') (hc : c.natAbs.size ≤ τ') :
    (P.horSpecial b c i).natAbs.size ≤ τ + i * τ' + Nat.size (P.natDegree + 1) := by
  -- Unfold horSpecial to the closed-form sum
  rw [Polynomial.horSpecial_eq_sum]
  -- Each summand has bitsize ≤ τ + i*τ'
  have hB : ∀ j ∈ range (i + 1),
      (P.coeff (P.natDegree - j) * b ^ (i - j) * c ^ j).natAbs.size ≤ τ + i * τ' := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact bitsize_coeff_mul_pow_le _ b c i j τ τ' (by omega) (hτ _) hb hc
  -- Sum of i+1 terms each of bitsize ≤ B adds Nat.size(i+1)
  have h1 := Azurite.BPR.Int.size_finset_sum_le hB
  rw [Finset.card_range] at h1
  -- Since i ≤ p, Nat.size(i+1) ≤ Nat.size(p+1)
  exact le_trans h1 (Nat.add_le_add_left (Nat.size_le_size (by omega)) _)

/-!
## Algorithm 8.9. Translation

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]` and `c ∈ A`, compute `P(X - c)`.

The algorithm simply composes `P` with the linear polynomial `X - c`
using Algorithm 8.7 (Horner composition).

**Complexity (BPR):** Dominated by the composition cost.

**Structure required:** Ring (D₀).

**Azurite implementation:** `Azurite.AzPolynomial.translate`

See: `Azurite.AzPolynomial.Translate`

The equivalence `toPoly (translate p c) = (toPoly p).comp (X - C c)`
is proved in `Azurite.AzPolynomial.Equiv.Translate`, along with the
root translation theorem: `r` is a root of `P(X-c)` iff `r-c` is a
root of `P`.
-/

end HorSpecialBitsize

/-!
## Algorithm 8.10. [Special Translation]

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]` and `b, c ∈ A`, compute the
polynomial `Q = cᵖ P((X − b)/c)` without leaving `A`:

  - Initialize `result := aₚ`, `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `result := result · (cX − b) + (d · aₚ₋ᵢ)`
  - Output `result = cᵖ P((X − b)/c)`.

**Complexity (BPR):** `O(p)` polynomial multiplications and additions.

**Structure required:** Ring (D₀).

**Azurite implementation:** `Azurite.AzPolynomial.specialTranslate`

See: `Azurite.AzPolynomial.SpecialTranslate`

The equivalence proofs are in `Azurite.AzPolynomial.Equiv.SpecialTranslate`:

- `toPoly_cXSubB` — `toPoly (cXSubB b c) = C c * X - C b`
- `eval_specialTranslate` — integral evaluation identity
- `eval_specialTranslate_field` — field identity: `= c^deg · eval(z − b/c) P`
- `isRoot_specialTranslate_iff` — root iff root of original at shifted point
- `isRoot_specialTranslate_map_iff` — root translation across a ring hom `f : R →+* K`
-/

section SpecialTranslation

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.10 (Special Translation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, the `i`-th
    intermediate polynomial is:
    - `specialTrans P b c 0 = C(aₚ)`
    - `specialTrans P b c (i+1) = (C c * X - C b) * specialTrans P b c i
                                    + C(c^{i+1} * aₚ₋ᵢ₋₁)`

    The output `specialTrans P b c p = cᵖ P((X − b)/c)`. -/
noncomputable def Polynomial.specialTrans (P : R[X]) (b c : R) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => (C c * X - C b) * P.specialTrans b c i +
      C (c ^ (i + 1) * P.coeff (P.natDegree - (i + 1)))

/-- The base case: `specialTrans P b c 0 = C(leadingCoeff P)`. -/
theorem Polynomial.specialTrans_zero (P : R[X]) (b c : R) :
    P.specialTrans b c 0 = C P.leadingCoeff := by
  unfold Polynomial.specialTrans; rw [leadingCoeff]

/-- The recurrence for `specialTrans`. -/
theorem Polynomial.specialTrans_succ (P : R[X]) (b c : R) (i : ℕ) :
    P.specialTrans b c (i + 1) =
      (C c * X - C b) * P.specialTrans b c i +
      C (c ^ (i + 1) * P.coeff (P.natDegree - (i + 1))) :=
  rfl
/-- **Closed-form characterization.**
    `specialTrans P b c i = ∑ j ∈ range (i+1), C(aₚ₋ⱼ · cʲ) · (cX − b)^{i−j}`. -/
theorem Polynomial.specialTrans_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.specialTrans b c i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j) * c ^ j) * (C c * X - C b) ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.specialTrans]
  | succ n ih =>
    rw [Polynomial.specialTrans, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one,
        show c ^ (n + 1) * P.coeff (P.natDegree - (n + 1)) =
          P.coeff (P.natDegree - (n + 1)) * c ^ (n + 1) from by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm (C c * X - C b), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

private theorem cx_sub_b_eq {K : Type*} [Field K] (b c : K) (hc : c ≠ 0) :
    X - C (b * c⁻¹) = C c⁻¹ * (C c * X - C b) := by
  have h1 : C c⁻¹ * (C c * X) = X := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  have h2 : C c⁻¹ * C b = C (b * c⁻¹) := by
    rw [← map_mul, mul_comm]
  rw [mul_sub, h1, h2]

/-- **BPR Algorithm 8.10 (field characterization).**
    Over a field with `c ≠ 0`:

    `specialTrans P b c i = C(cⁱ) · Horᵢ(P, X − b·c⁻¹)`,

    i.e. `SpecialTransᵢ = cⁱ (aₚ(X − b/c)ⁱ + ⋯ + aₚ₋ᵢ)`. -/
theorem Polynomial.specialTrans_eq_horner_comp {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) (i : ℕ) :
    P.specialTrans b c i =
      C (c ^ i) * (P.horner i).comp (X - C (b * c⁻¹)) := by
  rw [Polynomial.horner_eq_sum, Polynomial.specialTrans_eq_sum]
  show _ = C (c ^ i) * eval₂ C (X - C (b * c⁻¹)) _
  rw [eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj; rw [Finset.mem_range] at hj
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [cx_sub_b_eq b c hc, mul_pow]
  simp only [← C_pow, ← mul_assoc, ← map_mul]
  congr 1; congr 1
  rw [show c⁻¹ ^ (i - j) = (c ^ (i - j))⁻¹ from inv_pow c (i - j)]
  rw [show c ^ i * P.coeff (P.natDegree - j) * (c ^ (i - j))⁻¹ =
    P.coeff (P.natDegree - j) * (c ^ i * (c ^ (i - j))⁻¹) from by ring]
  rw [← pow_sub₀ c hc (by omega : i - j ≤ i),
      show i - (i - j) = j from by omega]

end SpecialTranslation

/-! ### Bitsize bound on SpecialTrans coefficients -/

section SpecialTransBitsize

open Polynomial Finset Azurite.BPR

/-- The bitsize of a coefficient of `(cX − b)^n` is at most `n(1 + τ')`
    when `n ≥ 1` and `bitsize(b), bitsize(c) ≤ τ'`. -/
private theorem bitsize_coeff_cX_sub_b_pow (b c : ℤ) (n m τ' : ℕ)
    (hn : 0 < n)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    Int.size (((C c * X - C b) ^ n).coeff m) ≤ n * (1 + τ') := by
  -- By the binomial theorem, coeff m ((cX-b)^n) = choose(n,m) · c^m · (-b)^{n-m}.
  -- bitsize(choose(n,m)) ≤ n and bitsize(c^m · (-b)^{n-m}) ≤ n·τ', giving n·(1+τ').
  by_cases hm : n < m
  · -- m > n: coefficient is 0
    have hdeg : natDegree ((C c * X - C b) ^ n) ≤ n := by
      calc natDegree ((C c * X - C b) ^ n)
          ≤ n * natDegree (C c * X - C b) := Polynomial.natDegree_pow_le
        _ ≤ n * 1 := Nat.mul_le_mul_left _ (by
            rw [sub_eq_add_neg, ← map_neg]; exact Polynomial.natDegree_linear_le)
        _ = n := Nat.mul_one _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [Int.size]
  · push Not at hm
    -- m ≤ n: expand via binomial theorem, only the j = m term survives
    rw [sub_eq_add_neg, ← map_neg, Commute.add_pow (Commute.all _ _)]
    simp only [finsetSum_coeff, coeff_mul_natCast, mul_pow, ← C_pow, coeff_mul_C, coeff_C_mul,
               coeff_X_pow]

    rw [Finset.sum_eq_single_of_mem m (mem_range.mpr (by omega))]
    · -- j = m term
      simp only [if_true, mul_one]
      unfold Int.size at *
      -- bitsize(c^m · (-b)^{n-m} · choose(n,m)) ≤ n·τ' + n = n·(1+τ')
      have hprod : (c ^ m * (-b) ^ (n - m)).natAbs.size ≤ n * τ' := by
        have hbm : (-b).natAbs.size ≤ τ' := by rwa [Int.natAbs_neg]
        set L := List.replicate m c ++ List.replicate (n - m) (-b)
        have hLne : L ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp only [L, List.length_append, List.length_replicate]; omega
        have hLlen : L.length = n := by
          simp only [L, List.length_append, List.length_replicate]; omega
        have hprod_eq : L.prod = c ^ m * (-b) ^ (n - m) := by
          simp only [L, List.prod_append, List.prod_replicate]
        rw [← hprod_eq, ← Int.size, ← hLlen]
        exact Int.size_list_prod_le L τ' hLne (by
          intro x hx
          simp only [L, List.mem_append, List.mem_replicate] at hx
          rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact hc
          · exact hbm)
      have hchoose : (↑(n.choose m) : ℤ).natAbs.size ≤ n := by
        simp only [Int.natAbs_natCast, Nat.size_le]
        exact_mod_cast Nat.choose_lt_two_pow n m hn
      calc (c ^ m * (-b) ^ (n - m) * ↑(n.choose m)).natAbs.size
          ≤ (c ^ m * (-b) ^ (n - m)).natAbs.size + (↑(n.choose m) : ℤ).natAbs.size :=
            Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
        _ ≤ n * τ' + n := Nat.add_le_add hprod hchoose
        _ = n * (1 + τ') := by ring
    · intro j _ hjm
      simp only [if_neg (Ne.symm hjm), mul_zero, zero_mul]

/-- The bitsize of the coefficient of `X^m` in the `k`-th summand
    `C(aₚ₋ₖ · cᵏ) · (cX − b)^{i−k}` is at most `τ + i(1 + τ')`. -/
private theorem bitsize_specialTrans_summand (P : ℤ[X]) (b c : ℤ)
    (i k m τ τ' : ℕ) (hk : k ≤ i)
    (hτ : ∀ j, Int.size (P.coeff j) ≤ τ)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    Int.size ((C (P.coeff (P.natDegree - k) * c ^ k) *
      (C c * X - C b) ^ (i - k)).coeff m) ≤ τ + i * (1 + τ') := by
  -- coeff m (C(a_{p-k} * c^k) * (cX-b)^{i-k}) = a_{p-k} * c^k * coeff m ((cX-b)^{i-k})
  simp only [coeff_C_mul]
  unfold Int.size at *
  -- Helper: (c^j).natAbs.size ≤ j * τ'
  -- Helper: (a * c^j).natAbs.size ≤ a.natAbs.size + j * τ'
  have hmul_c_pow : ∀ (a : ℤ) (j : ℕ),
      (a * c ^ j).natAbs.size ≤ a.natAbs.size + j * τ' := by
    intro a j; rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · calc (a * c ^ j).natAbs.size
          ≤ a.natAbs.size + (c ^ j).natAbs.size :=
            Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
        _ ≤ a.natAbs.size + j * τ' := by
            apply Nat.add_le_add_left
            rw [Int.natAbs_pow, Nat.size_le, show j * τ' = τ' * j from by ring, pow_mul]
            exact Nat.pow_lt_pow_left (Nat.size_le.mp hc) (Nat.pos_iff_ne_zero.mp hj)
  by_cases hik : i - k = 0
  · -- i = k: (cX-b)^0 = 1
    have hki : k = i := by omega
    simp only [hik, pow_zero, coeff_one]
    split
    · -- m = 0
      simp only [mul_one]
      calc (P.coeff (P.natDegree - k) * c ^ k).natAbs.size
          ≤ (P.coeff (P.natDegree - k)).natAbs.size + k * τ' :=
            hmul_c_pow _ k
        _ ≤ τ + k * τ' := Nat.add_le_add (hτ _) (le_refl _)
        _ ≤ τ + i * (1 + τ') := by nlinarith
    · -- m ≠ 0
      simp
  · -- i - k > 0: use bitsize_coeff_cX_sub_b_pow
    have hik_pos : 0 < i - k := by omega
    calc (P.coeff (P.natDegree - k) * c ^ k * ((C c * X - C b) ^ (i - k)).coeff m).natAbs.size
        ≤ (P.coeff (P.natDegree - k) * c ^ k).natAbs.size +
          (((C c * X - C b) ^ (i - k)).coeff m).natAbs.size :=
          Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
      _ ≤ (τ + k * τ') + ((i - k) * (1 + τ')) := by
          apply Nat.add_le_add
          · calc (P.coeff (P.natDegree - k) * c ^ k).natAbs.size
                ≤ (P.coeff (P.natDegree - k)).natAbs.size + k * τ' :=
                  hmul_c_pow _ k
              _ ≤ τ + k * τ' := Nat.add_le_add (hτ _) (le_refl _)
          · exact bitsize_coeff_cX_sub_b_pow b c (i - k) m τ' hik_pos hb hc
      _ ≤ τ + i * (1 + τ') := by
          -- k*τ' + (i-k)*(1+τ') ≤ i*(1+τ')
          suffices h : k * τ' + (i - k) * (1 + τ') ≤ i * (1 + τ') by omega
          calc k * τ' + (i - k) * (1 + τ')
              = k * τ' + (i - k) + (i - k) * τ' := by ring
            _ = (i - k) + (k + (i - k)) * τ' := by ring
            _ = (i - k) + i * τ' := by rw [Nat.add_sub_cancel' hk]
            _ ≤ i + i * τ' := by omega
            _ = i * (1 + τ') := by ring

/-- **BPR §8.1 (bitsize of SpecialTrans coefficients).**
    Let `P ∈ ℤ[X]` with `p = natDegree P` and coefficient bitsizes bounded by `τ`.
    Let `b, c ∈ ℤ` with bitsizes bounded by `τ'`. Then for `i ≤ p`:

      `bitsize(coeff m (specialTrans P b c i)) ≤ τ + i(1 + τ') + bitsize(p + 1)`. -/
theorem Polynomial.bitsize_specialTrans_coeff_le (P : ℤ[X]) (b c : ℤ) (i τ τ' : ℕ)
    (hi : i ≤ P.natDegree)
    (hτ : ∀ k, Int.size (P.coeff k) ≤ τ)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    ∀ m, Int.size ((P.specialTrans b c i).coeff m) ≤
      τ + i * (1 + τ') + Nat.size (P.natDegree + 1) := by
  intro m
  rw [Polynomial.specialTrans_eq_sum, finsetSum_coeff]
  unfold Int.size at *
  -- Each summand has coeff of bitsize ≤ τ + i*(1+τ')
  have hB : ∀ j ∈ range (i + 1),
      ((C (P.coeff (P.natDegree - j) * c ^ j) *
        (C c * X - C b) ^ (i - j)).coeff m).natAbs.size ≤ τ + i * (1 + τ') := by
    intro j hj
    have hji : j ≤ i := by simp [Finset.mem_range] at hj; omega
    exact bitsize_specialTrans_summand P b c i j m τ τ' hji hτ hb hc
  calc (∑ j ∈ range (i + 1), ((C (P.coeff (P.natDegree - j) * c ^ j) *
          (C c * X - C b) ^ (i - j)).coeff m)).natAbs.size
      ≤ (τ + i * (1 + τ')) + Nat.size (range (i + 1)).card :=
        Int.size_finset_sum_le hB
    _ = τ + i * (1 + τ') + Nat.size (i + 1) := by simp [Finset.card_range]
    _ ≤ τ + i * (1 + τ') + Nat.size (P.natDegree + 1) := by
        apply Nat.add_le_add_left
        exact Nat.size_le_size (by omega)

end SpecialTransBitsize
