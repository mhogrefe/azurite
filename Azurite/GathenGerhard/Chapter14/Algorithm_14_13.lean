/-
  Spec-level lemmas for the complete factorization over `F_q`
  (GG Algorithm 14.13-style; the algorithm is
  `Azurite.AzPolynomial.factorization`, and its correctness proof lives
  with the other `AzPolynomial` bridges in
  `Azurite/AzPolynomial/Equiv/Factorization.lean`).

  Contents:

  * products over subsets of the prime-factor set (monic, dividing, with
    the expected factor sets);
  * the GENERALIZED crux `gcd(x^(qⁱ) − x, v) = ∏ (degree-i primes of v)`
    for ANY monic `v` whose prime factors have degree `≥ i` — the
    Algorithm 14.3 crux without squarefreeness of the target (the left
    argument supplies squarefreeness of the gcd, so `v` may carry
    multiplicities), which is what makes multiplicity-by-division sound;
  * the leaf criterion: a monic `g ≠ 1` whose prime factors all have
    degree `d` and whose own degree is `d` IS irreducible (it is its
    single prime factor).
-/
import Azurite.GathenGerhard.Chapter14.Algorithm_14_3

namespace Azurite

namespace GG

open Polynomial UniqueFactorizationMonoid

/- Prefer Mathlib's `NormalizedGCDMonoid` gcd (same as the sibling files). -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

/-! ### Spec level: subset products and the generalized crux -/

section Spec

variable {F : Type*} [Field F] [DecidableEq F]

/-- A product over a subset of the prime factors divides the polynomial
(it divides the radical). -/
theorem prod_subset_primeFactors_dvd {w : F[X]} {S : Finset F[X]}
    (hS : S ⊆ primeFactors w) : S.prod id ∣ w :=
  (Finset.prod_dvd_prod_of_subset _ _ id hS).trans radical_dvd_self

/-- A product over a subset of the prime factors is monic. -/
theorem monic_prod_subset_primeFactors {w : F[X]} {S : Finset F[X]}
    (hS : S ⊆ primeFactors w) : (S.prod id).Monic :=
  Polynomial.monic_prod_of_monic _ _
    (fun _ hp => monic_of_mem_primeFactors (hS hp))

/-- The prime factors of a product over a subset of the prime factors are
exactly that subset (the `mem_primeFactors_ddTail` argument, for an
arbitrary subset). -/
theorem mem_primeFactors_prod_subset {w : F[X]} (hw0 : w ≠ 0)
    {S : Finset F[X]} (hS : S ⊆ primeFactors w) {p : F[X]} :
    p ∈ primeFactors (S.prod id) ↔ p ∈ S := by
  rw [mem_primeFactors_iff'' (monic_prod_subset_primeFactors hS).ne_zero]
  constructor
  · rintro ⟨hirr, hnorm, hdvd⟩
    obtain ⟨g, hgS, hpg⟩ :=
      ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr).dvd_finsetProd_iff
        id).mp hdvd
    have hgf' := (mem_primeFactors_iff'' hw0).mp (hS hgS)
    have hpg' : p = g := by
      have hassoc := hirr.associated_of_dvd hgf'.1 hpg
      calc p = normalize p := hnorm.symm
        _ = normalize g := normalize_eq_normalize hpg hassoc.symm.dvd
        _ = g := hgf'.2.1
    rw [hpg']
    exact hgS
  · intro hpS
    have hpf' := (mem_primeFactors_iff'' hw0).mp (hS hpS)
    exact ⟨hpf'.1, hpf'.2.1, Finset.dvd_prod_of_mem id hpS⟩

/-- **The generalized crux** (the 14.3 crux without squarefreeness of the
target): for monic `v` all of whose prime factors have degree `≥ i`,
`gcd(x^(qⁱ) − x, v)` is the product of the DISTINCT degree-`i` prime
factors of `v`, each once.  Squarefreeness of the gcd comes from the LEFT
argument (`x^(qⁱ) − x` is squarefree), so `v` may carry multiplicities. -/
theorem gcd_X_pow_card_pow_sub_X_eq_prod_filter [Fintype F] {v : F[X]}
    (hv : v.Monic) {i : ℕ} (hi : i ≠ 0)
    (hall : ∀ p ∈ primeFactors v, i ≤ p.natDegree) :
    gcd (X ^ Fintype.card F ^ i - X) v
      = ((primeFactors v).filter (fun p => p.natDegree = i)).prod id := by
  have hA0 : (X ^ Fintype.card F ^ i - X : F[X]) ≠ 0 :=
    (monic_X_pow_card_pow_sub_X hi).ne_zero
  have hg0 : gcd (X ^ Fintype.card F ^ i - X) v ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]
    rintro ⟨h, -⟩
    exact hA0 h
  have hgm : (gcd (X ^ Fintype.card F ^ i - X) v).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hg0).mp (normalize_gcd _ _)
  have hgsq : Squarefree (gcd (X ^ Fintype.card F ^ i - X) v) :=
    (squarefree_X_pow_card_pow_sub_X hi).squarefree_of_dvd (gcd_dvd_left _ _)
  have hset : primeFactors (gcd (X ^ Fintype.card F ^ i - X) v)
      = (primeFactors v).filter (fun p => p.natDegree = i) := by
    ext p
    rw [mem_primeFactors_iff'' hg0, Finset.mem_filter]
    constructor
    · rintro ⟨hirr, hnorm, hdvd⟩
      rw [dvd_gcd_iff] at hdvd
      obtain ⟨hdA, hdv⟩ := hdvd
      have hdd : p.natDegree ∣ i :=
        (irreducible_dvd_X_pow_card_pow_sub_X_iff hirr).mp hdA
      have hmem : p ∈ primeFactors v :=
        (mem_primeFactors_iff'' hv.ne_zero).mpr ⟨hirr, hnorm, hdv⟩
      have hge := hall p hmem
      have hle : p.natDegree ≤ i := Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hdd
      exact ⟨hmem, by omega⟩
    · rintro ⟨hpf, hdeg⟩
      have hpf' := (mem_primeFactors_iff'' hv.ne_zero).mp hpf
      refine ⟨hpf'.1, hpf'.2.1, dvd_gcd ?_ hpf'.2.2⟩
      exact (irreducible_dvd_X_pow_card_pow_sub_X_iff hpf'.1).mpr
        (hdeg ▸ dvd_refl _)
  calc gcd (X ^ Fintype.card F ^ i - X) v
      = (primeFactors (gcd (X ^ Fintype.card F ^ i - X) v)).prod id :=
        (prod_primeFactors_eq hgm hgsq).symm
    _ = ((primeFactors v).filter (fun p => p.natDegree = i)).prod id := by
        rw [hset]

omit [DecidableEq F] in
/-- Monic non-one polynomials have positive degree — via a prime factor. -/
theorem one_le_natDegree_of_monic_ne_one {g : F[X]} (hm : g.Monic)
    (h1 : g ≠ 1) : 1 ≤ g.natDegree := by
  by_contra h
  exact h1 ((hm.natDegree_eq_zero).mp (by omega))

/-- A monic `g ≠ 1` whose prime factors all have degree `d` has degree at
least `d`. -/
theorem natDegree_ge_of_factors_natDegree_eq {g : F[X]} (hm : g.Monic)
    (h1 : g ≠ 1) {d : ℕ}
    (hall : ∀ p ∈ primeFactors g, p.natDegree = d) :
    d ≤ g.natDegree := by
  obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hm.ne_zero
    (fun hu => h1 (hm.isUnit_iff.mp hu))
  have hpf : p ∈ primeFactors g := mem_primeFactors.mpr hp
  have hpd := hall p hpf
  have hdvd := ((mem_primeFactors_iff'' hm.ne_zero).mp hpf).2.2
  calc d = p.natDegree := hpd.symm
    _ ≤ g.natDegree := Polynomial.natDegree_le_of_dvd hdvd hm.ne_zero

/-- **The leaf criterion**: a monic `g ≠ 1` whose prime factors all have
degree `d` and whose own degree is `d` is itself irreducible (it IS its
single prime factor). -/
theorem irreducible_of_natDegree_eq_of_factors {g : F[X]} (hm : g.Monic)
    (h1 : g ≠ 1) {d : ℕ}
    (hall : ∀ p ∈ primeFactors g, p.natDegree = d)
    (hdeg : g.natDegree = d) : Irreducible g := by
  obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hm.ne_zero
    (fun hu => h1 (hm.isUnit_iff.mp hu))
  have hpf : p ∈ primeFactors g := mem_primeFactors.mpr hp
  obtain ⟨hirr, hnorm, hdvd⟩ := (mem_primeFactors_iff'' hm.ne_zero).mp hpf
  obtain ⟨c, hc⟩ := hdvd
  have hp0 : p ≠ 0 := hirr.ne_zero
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact hm.ne_zero hc
  have hpm : p.Monic := monic_of_mem_primeFactors hpf
  have hcm : c.Monic := hpm.of_mul_monic_left (hc ▸ hm)
  have hdegs : p.natDegree + c.natDegree = d := by
    have := Polynomial.natDegree_mul hp0 hc0
    rw [← hc, hdeg] at this
    omega
  have hcd : c.natDegree = 0 := by
    have := hall p hpf
    omega
  have hc1 : c = 1 := (hcm.natDegree_eq_zero).mp hcd
  rw [hc1, mul_one] at hc
  rw [hc]
  exact hirr

end Spec

end GG

end Azurite
