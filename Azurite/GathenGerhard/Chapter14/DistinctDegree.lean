/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Gathen–Gerhard, Chapter 14: the DISTINCT-DEGREE DECOMPOSITION.

  For nonconstant `f ∈ F_q[x]`, the distinct-degree decomposition is the
  sequence `(g_1, …, g_s)` where `g_i` is the product of all monic
  irreducible polynomials of degree `i` dividing `f` (each once — the
  decomposition sees each irreducible factor once, regardless of
  multiplicity), and `g_s ≠ 1` (though earlier `g_i` may be `1`).

  Formalized on Mathlib polynomials (the spec layer): `ddFactor f i` is the
  product over the degree-`i` slice of `f`'s prime-factor SET
  (`UniqueFactorizationMonoid.primeFactors`), `ddLength f` the largest
  factor degree, and `distinctDegreeDecomposition f` the sequence
  `(g_1, …, g_s)`. Basic theory: each part is monic and divides `f` (the
  slice is a subset of the prime factors, whose product is the radical);
  the last part is not `1`; degree-`0` slices are empty (irreducibles over
  a field have positive degree); and for MONIC SQUAREFREE `f` — the
  situation after the squarefree step of the factorization pipeline — the
  parts multiply back to `f` (fiberwise partition of the factor set by
  degree).

  The book's `F_3` example — the decomposition of
  `f = x(x+1)(x²+1)(x²+x+2)` is `(x²+x, x⁴+x³+x+2)` — is verified
  computationally on `AzPolynomial (AzZMod 3)` in the guards: the products
  assemble as claimed, and the two quadratics are irreducible since they
  have no zeros in `F_3` (checked by evaluating over the EXHAUSTIVE
  generator of the coefficient field — degree ≤ 3 plus no roots forces
  irreducibility).
-/
import Azurite.GathenGerhard.Chapter14.Theorem_14_2
import Azurite.ExhaustiveGenerator.Polynomials
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Eval
import Mathlib.RingTheory.Radical.Basic

namespace Azurite

namespace GG

open Polynomial UniqueFactorizationMonoid

variable {F : Type*} [Field F] [DecidableEq F]

/-- The degree-`i` part of `f`: the product of all monic irreducible
polynomials of degree `i` dividing `f`, each once (the degree-`i` slice of
the prime-factor set). -/
noncomputable def ddFactor (f : F[X]) (i : ℕ) : F[X] :=
  ((primeFactors f).filter (fun g => g.natDegree = i)).prod id

/-- The length `s` of the distinct-degree decomposition: the largest degree
of an irreducible factor of `f`. -/
noncomputable def ddLength (f : F[X]) : ℕ :=
  (primeFactors f).sup natDegree

/-- **The distinct-degree decomposition** `(g_1, …, g_s)` of `f`. -/
noncomputable def distinctDegreeDecomposition (f : F[X]) : List F[X] :=
  (List.range (ddLength f)).map (fun i => ddFactor f (i + 1))

/-- Prime factors are monic (they are normalized). -/
theorem monic_of_mem_primeFactors {f g : F[X]} (hg : g ∈ primeFactors f) :
    g.Monic := by
  rw [mem_primeFactors] at hg
  exact (Polynomial.normalize_eq_self_iff_monic
    (irreducible_of_normalized_factor g hg).ne_zero).mp
    (normalize_normalized_factor g hg)

/-- Prime factors are irreducible. -/
theorem irreducible_of_mem_primeFactors {f g : F[X]} (hg : g ∈ primeFactors f) :
    Irreducible g := by
  rw [mem_primeFactors] at hg
  exact irreducible_of_normalized_factor g hg

/-- Each part of the decomposition is monic. -/
theorem ddFactor_monic (f : F[X]) (i : ℕ) : (ddFactor f i).Monic := by
  refine Polynomial.monic_prod_of_monic _ _ ?_
  intro g hg
  exact monic_of_mem_primeFactors (Finset.mem_filter.mp hg).1

/-- Each part of the decomposition divides `f`: the slice is a subset of
the prime factors, whose product — the radical — divides `f`. -/
theorem ddFactor_dvd (f : F[X]) (i : ℕ) : ddFactor f i ∣ f :=
  (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
    radical_dvd_self

/-- The degree-`0` part is always `1`: irreducible polynomials over a field
have positive degree. -/
theorem ddFactor_zero (f : F[X]) : ddFactor f 0 = 1 := by
  unfold ddFactor
  rw [Finset.filter_false_of_mem, Finset.prod_empty]
  intro g hg
  exact (irreducible_of_mem_primeFactors hg).natDegree_pos.ne'

/-- The LAST part of the decomposition is not `1` (for `f` with an
irreducible factor, i.e. nonconstant): a factor of maximal degree divides
it. -/
theorem ddFactor_ddLength_ne_one {f : F[X]} (hf0 : f ≠ 0) (hfu : ¬IsUnit f) :
    ddFactor f (ddLength f) ≠ 1 := by
  classical
  -- there is a prime factor, and one of maximal degree
  obtain ⟨g, hgmem⟩ := exists_mem_normalizedFactors hf0 hfu
  have hne : (primeFactors f).Nonempty := ⟨g, mem_primeFactors.mpr hgmem⟩
  obtain ⟨m, hmmem, hmax⟩ := Finset.exists_mem_eq_sup _ hne natDegree
  intro h1
  -- the maximal-degree factor divides the (unit) product
  have hdvd : m ∣ ddFactor f (ddLength f) := by
    refine Finset.dvd_prod_of_mem id ?_
    rw [Finset.mem_filter]
    exact ⟨hmmem, by rw [ddLength, hmax]⟩
  rw [h1] at hdvd
  exact (irreducible_of_mem_primeFactors hmmem).not_isUnit (isUnit_of_dvd_one hdvd)

/-- **The decomposition identity**: a monic squarefree polynomial is the
product of the parts of its distinct-degree decomposition (the fiberwise
partition of its factor set by degree). This is the situation after the
squarefree step of the factorization pipeline. -/
theorem prod_distinctDegreeDecomposition {f : F[X]} (hm : f.Monic)
    (hsq : Squarefree f) :
    (distinctDegreeDecomposition f).prod = f := by
  classical
  have h0 : f ≠ 0 := hm.ne_zero
  -- `f` is the product of its (duplicate-free) factor set
  have hset : (primeFactors f).prod id = f := by
    have hrad := radical_associated hsq.isRadical h0
    exact Polynomial.eq_of_monic_of_associated
      (Polynomial.monic_prod_of_monic _ _
        (fun g hg => monic_of_mem_primeFactors hg)) hm hrad
  -- partition the factor set by degree
  have hfiber : ∏ i ∈ Finset.range (ddLength f + 1), ddFactor f i
      = (primeFactors f).prod id := by
    refine Finset.prod_fiberwise_of_maps_to ?_ id
    intro g hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup hg
  -- the list product is the range product
  have hlist : ∀ n : ℕ, ((List.range n).map fun i => ddFactor f (i + 1)).prod
      = ∏ i ∈ Finset.range n, ddFactor f (i + 1) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]
  -- strip the trivial degree-`0` part and assemble
  have hpeel : ∏ i ∈ Finset.range (ddLength f + 1), ddFactor f i
      = ∏ i ∈ Finset.range (ddLength f), ddFactor f (i + 1) := by
    rw [Finset.prod_range_succ', ddFactor_zero, mul_one]
  rw [distinctDegreeDecomposition, hlist, ← hpeel, hfiber, hset]

end GG

end Azurite

/-! ### The book's example, computationally (`F_3`)

`f = x(x+1)(x²+1)(x²+x+2) ∈ F_3[x]` has distinct-degree decomposition
`(x²+x, x⁴+x³+x+2)`: the two linear factors assemble the degree-`1` part,
the two quadratics the degree-`2` part — irreducible because they have no
zeros in `F_3` (checked over the EXHAUSTIVE generator of the field). -/

namespace Azurite

open ExhaustiveGenerator AzPolynomial

private def p3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  (parseAzPolynomial s).get!

-- the degree-1 part: x(x+1) = x²+x
#guard toChars (p3 "x" * p3 "x+1") == "x^2+x"

-- the degree-2 part: (x²+1)(x²+x+2) = x⁴+x³+x+2 (the `3x²` term vanishes)
#guard toChars (p3 "x^2+1" * p3 "x^2+x+2") == "x^4+x^3+x+2"

-- the parts multiply to f
#guard toChars (p3 "x^2+x" * p3 "x^4+x^3+x+2")
  == toChars (p3 "x" * p3 "x+1" * p3 "x^2+1" * p3 "x^2+x+2")

-- the quadratics are irreducible: no zeros in `F_3` (degree `≤ 3` with no
-- roots forces irreducibility), the test points drawn from the exhaustive
-- field enumeration
#guard (firstN (AzZMod (AzNat.ofNat 3)) 3).all fun c =>
  ((p3 "x^2+1").eval c).val.toNat != 0
#guard (firstN (AzZMod (AzNat.ofNat 3)) 3).all fun c =>
  ((p3 "x^2+x+2").eval c).val.toNat != 0

-- while the linear factors and f itself of course do have roots
#guard ((firstN (AzZMod (AzNat.ofNat 3)) 3).all fun c =>
  ((p3 "x" * p3 "x+1" * p3 "x^2+1" * p3 "x^2+x+2").eval c).val.toNat != 0) == false

end Azurite
