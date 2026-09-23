/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Complete polynomial factorization over `F_q` (Gathen–Gerhard, "Modern
  Computer Algebra", Algorithm 14.13-style), computable: distinct-degree
  sweep + multiplicity extraction by division + equal-degree splitting.

  Input: a monic `f ∈ F_q[x]`.  Output (`factorization`): the CANONICAL
  factorization — the list of `(monic irreducible factor, multiplicity)`
  pairs, sorted strictly increasingly by factor in the canonical
  `AzPolynomial` order (degree, then top-down lexicographic on
  coefficients).  For arbitrary `f`, `canonicalFactorization` additionally
  returns the leading coefficient out front — the associate-class
  representatives are the MONIC polynomials (= Mathlib's `normalize` over
  a field), and the one remaining unit is carried explicitly, exactly as
  sign–magnitude does for integers: `f = C(lc f) · ∏ uᵢ^eᵢ` (and `0`
  yields `(0, [])`).

  ## Why no Yun stage

  The classical squarefree-first pipeline (Yun → DDF → EDS) is only
  correct in characteristic zero: over `F_q`, Yun's algorithm silently
  loses `p`-th-power factors (`f = u^p` has `f' = 0`, so
  `f / gcd(f, f') = 1` — e.g. `x³+1 = (x+1)³` over `F_3`).  GG's own
  complete algorithm therefore replaces the squarefree stage with
  MULTIPLICITY BY DIVISION, which is what we do: the outer loop
  (`factorizationLoop`) runs the DDF-style sweep `u := gcd(x^(qⁱ) − x, v)`
  — `u` is the (automatically squarefree) product of the DISTINCT
  degree-`i` prime factors of the remaining part `v` — splits `u` into
  irreducibles, divides `v` by `u`, and repeats AT THE SAME `i` until the
  degree-`i` factors are exhausted (each pass removes one copy of each),
  only then advancing `i`.  The `x³+1` example runs in the guards.

  ## Equal-degree factorization

  `equalDegreeFactorization` splits an equal-degree product `g` (all prime
  factors of degree `d`) into its irreducible factors by recursive
  splitting.  Each split (`edsSearch`) tries the pseudorandom candidates of
  the hybrid stream first (64 attempts, each succeeding with probability
  ≈ 1/2 for a genuine product), then falls back to a DETERMINISTIC sweep
  of ALL monic degree-`d` polynomials (`sweepCandidate`, via the capped
  exhaustive vector enumeration, `card K ^ d` of them): any prime factor
  of `g` is itself a splitting candidate through the `gcd(a, f)` path, so
  the sweep provably succeeds — termination and correctness are theorems
  (`Azurite.GG.factorization_correct` in
  `Azurite/GathenGerhard/Chapter14/Algorithm_14_13.lean`), not
  expectations.

  Correctness (for monic `f`, `q = card K`): the outputs are monic
  irreducible and their product is `f`.  No oddness of `q` is needed for
  correctness — the `±1` power path only affects how often the
  pseudorandom attempts succeed, and the `gcd` path backstop is
  characteristic-agnostic.
-/
import Azurite.AzPolynomial.EqualDegreeSplitting
import Azurite.AzPolynomial.Equiv.Compare
import Azurite.AzZMod.Order

namespace Azurite

/-- Collapse ADJACENT equal elements into `(element, count)` pairs
(run-length encoding).  On a sorted list this groups ALL equal elements,
producing strictly increasing firsts with positive counts. -/
def runLengths {A : Type _} [DecidableEq A] : List A → List (A × ℕ)
  | [] => []
  | a :: rest =>
    match runLengths rest with
    | [] => [(a, 1)]
    | (b, e) :: t => if a = b then (b, e + 1) :: t else (a, 1) :: (b, e) :: t

namespace AzPolynomial

open Azurite.ExhaustiveGenerator

variable {K : Type _} [Field K] [DecidableEq K]

/-! ### The deterministic candidate sweep -/

/-- The monic polynomial of degree `d` with low coefficients `v`. -/
def monicOfVec {d : ℕ} (v : List.Vector K d) : AzPolynomial K :=
  ⟨(v.toList ++ [1]).toArray, by
    intro h
    rw [← Array.getLast?_toList] at h
    simp only [List.getLast?_concat] at h
    exact one_ne_zero (Option.some.inj h)⟩

omit [DecidableEq K] in
theorem natDegree_monicOfVec {d : ℕ} (v : List.Vector K d) :
    (monicOfVec v).natDegree = d := by
  show ((v.toList ++ [1]).toArray).size - 1 = d
  have hv : v.toList.length = d := v.property
  simp [hv]

/-- The `j`-th monic degree-`d` candidate: the `j`-th vector of the capped
exhaustive enumeration of `K^d`, as low coefficients under a leading `1`
(the constant `1` past the end of the enumeration — harmless, the
splitting step rejects constants). -/
def sweepCandidate (K : Type _) [Field K] [DecidableEq K]
    [ExhaustiveGenerator K] [FiniteGenerator K] (d j : ℕ) : AzPolynomial K :=
  ((ExhaustiveGenerator.gen (T := List.Vector K d) j).map monicOfVec).getD 1

/-! ### Equal-degree factorization -/

/-- One splitting search: try the pseudorandom hybrid candidates for the
first 64 indices (each attempt succeeds with probability ≈ 1/2 on a
genuine product), then sweep ALL monic degree-`d` polynomials — a sweep
candidate that is a prime factor of `g` splits it through the
`gcd(a, g)` path, so the search provably succeeds within the fuel
`64 + card K ^ d` supplied by `edsSearchFuel`. -/
def edsSearch (q : AzNat) (d : ℕ) (g : AzPolynomial K) (seed : UInt64)
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    (fuel i : ℕ) → Option (AzPolynomial K)
  | 0, _ => none
  | fuel + 1, i =>
    match equalDegreeSplittingStep q d g
      (if i < 64 then hybridPolyCandidate K seed g.natDegree i
       else sweepCandidate K d (i - 64)) with
    | some h => some h
    | none => edsSearch q d g seed fuel (i + 1)

/-- Fuel for `edsSearch`: the pseudorandom attempts plus the full sweep. -/
def edsSearchFuel (K : Type _) [Field K] [DecidableEq K]
    [ExhaustiveGenerator K] [FiniteGenerator K] (d : ℕ) : ℕ :=
  64 + FiniteGenerator.card (T := List.Vector K d)

/-- **Equal-degree factorization** by recursive splitting: given `g` all of
whose prime factors have degree `d`, return them all (with multiplicity).
A leaf (`deg g ≤ d`) is itself irreducible; otherwise split off a proper
factor and recurse on both parts.  Fueled by `deg g` (each split strictly
decreases the degree). -/
def equalDegreeFactorizationLoop (q : AzNat) (d : ℕ) (seed : UInt64)
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    (fuel : ℕ) → AzPolynomial K → List (AzPolynomial K)
  | 0, g => [g]
  | fuel + 1, g =>
    if g.natDegree ≤ d then [g]
    else
      match edsSearch q d g seed (edsSearchFuel K d) 0 with
      | some h =>
          equalDegreeFactorizationLoop q d seed fuel h ++
            equalDegreeFactorizationLoop q d seed fuel (divByMonic g h)
      | none => [g]

/-- Equal-degree factorization (GG Algorithm 14.10-style, on the provably
terminating search). -/
def equalDegreeFactorization (q : AzNat) (d : ℕ) (g : AzPolynomial K)
    (seed : UInt64) [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    List (AzPolynomial K) :=
  equalDegreeFactorizationLoop q d seed g.natDegree g

/-! ### The complete factorization -/

/-- The outer loop: a DDF-style sweep with multiplicity extraction.  State:
the round `i`, the power `h ≡ x^(qⁱ) mod f`, and the remaining part `v`
(all of whose prime factors have degree `≥ i`).  Each round computes
`u := gcd(h − x, v)` — the product of the distinct degree-`i` prime
factors of `v`, each ONCE — splits it into irreducibles, divides `v` by
`u`, and repeats at the same `i` (extracting one copy of each degree-`i`
factor per pass) until `u = 1`, then advances `i`.  Fuel `2·deg f + 1`
suffices: each iteration either advances `i` (at most `deg f` times) or
strictly decreases `deg v`. -/
def factorizationLoop (q : AzNat) (f : AzPolynomial K) (seed : UInt64)
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    (fuel i : ℕ) → (h v : AzPolynomial K) → List (AzPolynomial K)
  | 0, _, _, _ => []
  | fuel + 1, i, h, v =>
    if v = 1 then []
    else
      let u := gcdMonic (h - X) v
      if u = 1 then
        factorizationLoop q f seed fuel (i + 1) (powModByMonic h q f) v
      else
        equalDegreeFactorization q i u seed ++
          factorizationLoop q f seed fuel i h (divByMonic v u)

/-- **Complete factorization over `F_q`** (GG Algorithm 14.13-style):
distinct-degree sweep + multiplicity by division + equal-degree
splitting, the flat factor list then canonicalized — sorted in the
canonical `AzPolynomial` order and run-length encoded.  For a monic `f`,
returns the `(monic irreducible factor, multiplicity)` pairs with
strictly increasing factors; correctness is
`Azurite.AzPolynomial.factorization_correct`. -/
def factorization (q : AzNat) (f : AzPolynomial K) (seed : UInt64)
    [LinearOrder K] [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    List (AzPolynomial K × ℕ) :=
  runLengths ((factorizationLoop q f seed (2 * f.natDegree + 1) 1
    (powModByMonic X q f) f).mergeSort (· ≤ ·))

/-- **The canonical factorization of an arbitrary `f`**: the leading
coefficient (the one unit of the factorization, the associate-class
representatives being the monic polynomials), and the sorted
`(monic irreducible, multiplicity)` pairs of the monicized `f`.  `0`
yields `(0, [])`.  So `f = C(lc f) · ∏ uᵢ^eᵢ`
(`canonicalFactorization_correct`). -/
def canonicalFactorization (q : AzNat) (f : AzPolynomial K) (seed : UInt64)
    [LinearOrder K] [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})] :
    K × List (AzPolynomial K × ℕ) :=
  if f = 0 then (0, [])
  else (f.leadingCoeff, factorization q (monicize f) seed)

end AzPolynomial

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! ### Complete factorizations over `F_3`

The distinct-degree example `x(x+1)(x²+1)(x²+x+2)`; the Yun-killer
`x³+1 = (x+1)³` (a `p`-th power, whose derivative vanishes — the case a
characteristic-zero squarefree stage would silently lose); mixed
multiplicities `x²(x+1)(x²+1)³`; GG Example 14.5; and the degenerate
inputs `1` (no factors) and an irreducible quartic (itself). -/

section Tests

open Azurite Azurite.AzPolynomial

private instance : Fact (Nat.Prime (AzNat.ofNat 3).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def r3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  (parseAzPolynomial s).get!

private def showPairs (l : List (AzPolynomial (AzZMod (AzNat.ofNat 3)) × ℕ)) :
    List (String × ℕ) :=
  l.map (fun p => (toChars p.1, p.2))

-- four distinct factors, two degrees, canonically sorted
#guard showPairs (factorization (AzNat.ofNat 3) (r3 "x^6+2*x^5+x^4+x^3+2*x") 0)
  == [("x", 1), ("x+1", 1), ("x^2+1", 1), ("x^2+x+2", 1)]

-- the Yun-killer: (x+1)³ over F_3, multiplicity 3 recovered by division
#guard showPairs (factorization (AzNat.ofNat 3) (r3 "x^3+1") 0)
  == [("x+1", 3)]

-- mixed multiplicities: x²·(x+1)·(x²+1)³
#guard showPairs (factorization (AzNat.ofNat 3)
    (r3 "x^2" * r3 "x+1" * r3 "x^2+1" * r3 "x^2+1" * r3 "x^2+1") 0)
  == [("x", 2), ("x+1", 1), ("x^2+1", 3)]

-- GG Example 14.5's polynomial, fully factored
#guard showPairs (factorization (AzNat.ofNat 3)
    (r3 "x^8+x^7+2*x^6+x^5+2*x^3+2*x^2+2*x") 0)
  == [("x", 1), ("x^2+1", 1), ("x^2+x+2", 1), ("x^3+2*x+1", 1)]

-- degenerate inputs
#guard (factorization (AzNat.ofNat 3) (r3 "1") 0) == []
#guard showPairs (factorization (AzNat.ofNat 3) (r3 "x^4+x+2") 0)
  == [("x^4+x+2", 1)]

-- the canonical factorization of a NON-monic input: the unit out front
-- (`2x³+2 = 2·(x+1)³`), the associate representatives monic
#guard (canonicalFactorization (AzNat.ofNat 3) (r3 "2*x^3+2") 0).1.val.toNat == 2
#guard showPairs (canonicalFactorization (AzNat.ofNat 3) (r3 "2*x^3+2") 0).2
  == [("x+1", 3)]

-- and of zero: `(0, [])`
#guard (canonicalFactorization (AzNat.ofNat 3) (r3 "0") 0).1.val.toNat == 0
#guard (canonicalFactorization (AzNat.ofNat 3) (r3 "0") 0).2 == []

/-! #### Over `F_2` and `F_5`

Correctness needs no oddness of `q`, so `F_2` works — including an
equal-degree split of the two quartics, where the characteristic-2-dead
power path falls through to the (here at most 16-candidate) deterministic
sweep.  Each factorization is also multiplied back to its input. -/

private instance : Fact (Nat.Prime (AzNat.ofNat 2).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private instance : Fact (Nat.Prime (AzNat.ofNat 5).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def r2 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 2)) :=
  (parseAzPolynomial s).get!

private def r5 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 5)) :=
  (parseAzPolynomial s).get!

private def f2ex : AzPolynomial (AzZMod (AzNat.ofNat 2)) :=
  r2 "x^26+x^24+x^22+x^11+x^10+x^9+x^7+x^5+1"

private def f5ex : AzPolynomial (AzZMod (AzNat.ofNat 5)) :=
  r5 "x^11+x^10+4*x^9+4*x^8+3*x^7+2*x^6+2*x^5+2*x^3+3*x+4"

#guard ((factorization (AzNat.ofNat 2) f2ex 0).map (fun p => (toChars p.1, p.2)))
  == [("x^2+x+1", 1), ("x^3+x+1", 1), ("x^4+x+1", 1), ("x^4+x^3+1", 1),
      ("x^5+x^2+1", 1), ("x^8+x^4+x^3+x+1", 1)]

#guard toChars (((factorization (AzNat.ofNat 2) f2ex 0).flatMap
    (fun p => List.replicate p.2 p.1)).foldl (· * ·) 1) == toChars f2ex

#guard ((factorization (AzNat.ofNat 5) f5ex 0).map (fun p => (toChars p.1, p.2)))
  == [("x^2+2", 1), ("x^2+x+1", 1), ("x^3+x+1", 1), ("x^4+2", 1)]

#guard toChars (((factorization (AzNat.ofNat 5) f5ex 0).flatMap
    (fun p => List.replicate p.2 p.1)).foldl (· * ·) 1) == toChars f5ex

-- two coprime factors of distinct degrees over F_2
private def f2ex' : AzPolynomial (AzZMod (AzNat.ofNat 2)) :=
  r2 "x^12+x^9+x^7+x^6+x^4+x^3+1"

#guard ((factorization (AzNat.ofNat 2) f2ex' 0).map (fun p => (toChars p.1, p.2)))
  == [("x^5+x^4+x^3+x^2+1", 1), ("x^7+x^6+x^4+x^2+1", 1)]

#guard toChars (((factorization (AzNat.ofNat 2) f2ex' 0).flatMap
    (fun p => List.replicate p.2 p.1)).foldl (· * ·) 1) == toChars f2ex'

-- a `p`-th-power content case over F_2: `f = g(x²) = g(x)²` in
-- characteristic 2, here `(x+1)²(x²+x+1)⁴` — multiplicities recovered by
-- division, where a characteristic-zero squarefree stage would fail
private def f2ex'' : AzPolynomial (AzZMod (AzNat.ofNat 2)) :=
  r2 "x^10+x^8+x^6+x^4+x^2+1"

#guard ((factorization (AzNat.ofNat 2) f2ex'' 0).map (fun p => (toChars p.1, p.2)))
  == [("x+1", 2), ("x^2+x+1", 4)]

#guard toChars (((factorization (AzNat.ofNat 2) f2ex'' 0).flatMap
    (fun p => List.replicate p.2 p.1)).foldl (· * ·) 1) == toChars f2ex''

/-! #### Over `F_1009` — a larger prime modulus (limb-level throughout) -/

set_option maxRecDepth 4096 in
private instance : Fact (Nat.Prime (AzNat.ofNat 1009).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def r1009 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 1009)) :=
  (parseAzPolynomial s).get!

private def f1009ex : AzPolynomial (AzZMod (AzNat.ofNat 1009)) :=
  r1009 "x^6+3*x^5+508*x^4+7*x^3+511*x^2+1005*x+1007"

#guard ((factorization (AzNat.ofNat 1009) f1009ex 0).map
    (fun p => (toChars p.1, p.2)))
  == [("x+2", 1), ("x+139", 1), ("x^4+871*x^3+517*x^2+789*x+813", 1)]

#guard toChars (((factorization (AzNat.ofNat 1009) f1009ex 0).flatMap
    (fun p => List.replicate p.2 p.1)).foldl (· * ·) 1) == toChars f1009ex

end Tests
