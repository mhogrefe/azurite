/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Computable version of BPR's `posgcd` (Definition 1.20).

  The set of possible greatest common divisors of a finite family
  `𝒫 ⊂ D[Y₁, …, Y_k][X]`: a list of pairs `(G, 𝒞)` where `G` is a
  polynomial and `𝒞` is a formula such that `y ∈ Reali(𝒞)` implies
  `gcd(𝒫_y) = G_y`.
-/
import Azurite.AzFormula.LeafFormula
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-- Auxiliary for `azPathLeafParent`: follows a path to find the last
nonzero polynomial. -/
def azPathLeafParentAux
    (cur : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) →
    AzPolynomial (AzMvPolynomial k D ord)
  | [] => cur
  | next :: rest =>
    if next == 0 then cur
    else azPathLeafParentAux next rest

/-- The leaf parent of a path in `TRems(P, Q)`: the last nonzero
polynomial before the terminal `0` leaf. Returns `P` when
`Q_y = 0` (the path is `[0]` or `[]`).

Computable version of BPR's `pathLeafParent`. -/
def azPathLeafParent
    (P : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) →
    AzPolynomial (AzMvPolynomial k D ord)
  | [] => P
  | q :: rest =>
    if q == 0 then P
    else azPathLeafParentAux q rest

/-- BPR Definition 1.20: the set of possible greatest common divisors
of a finite family `𝒫 ⊂ D[Y₁, …, Yₖ][X]`, computed using smart
conjunction to absorb trivial atoms.

Each element is a pair `(G, 𝒞)` where `G` is a polynomial and `𝒞`
is a formula such that `y ∈ Reali(𝒞)` implies `gcd(𝒫_y) = G_y`. -/
def azPosgcd :
    List (AzPolynomial (AzMvPolynomial k D ord)) →
    List (AzPolynomial (AzMvPolynomial k D ord) ×
      Formula (Fin k) (AzFieldAtom k D ord))
  | [] => [(0, azTrueFormula)]
  | P :: rest =>
    (azPosgcd rest).flatMap fun (Q, C) =>
      (AzPolynomial.tremsTree P Q).leafPaths.map fun path =>
        (azPathLeafParent P path,
         azSmartAnd C (azLeafFormula P Q path))

/-! ### Tests -/

section Tests

private abbrev MvInt3 := AzMvPolynomial 3 AzInt .Degrevlex
private instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def p (s : String) : AzPolynomial MvInt3 :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := AzInt)
    (ord := .Degrevlex) s).getD 0
private def s (q : AzPolynomial MvInt3) : String :=
  q.toStrMvCoeffWith (AbcVar 3)

-- Empty family: one pair (0, True)
private def emptyResult := azPosgcd (k := 3) (D := AzInt) (ord := .Degrevlex) []
#guard emptyResult.length == 1
#guard emptyResult.map (·.1) == [0]
#guard emptyResult.all (isAzTrue ·.2)

-- Singleton family {P}: gcd is P itself (up to specialization)
-- posgcd [P] processes TRems(P, 0), which has one leaf path [0]
-- pathLeafParent P [0] = P, leafFormula P 0 [0] = degFormula 0 ⊥ = trueFormula
-- azSmartAnd trueFormula trueFormula = trueFormula
private def singletonResult := azPosgcd [p "x+(a)"]
#guard singletonResult.length == 1
#guard singletonResult.map (fun pair => s pair.1) == ["x+(a)"]
-- The formula should simplify to true (azSmartAnd absorbs trueFormula)
#guard singletonResult.all (isAzTrue ·.2)

-- Two linear polynomials: P = x+(a), Q = x+(b)
private def ex_pq := azPosgcd [p "x+(a)", p "x+(b)"]
#guard ex_pq.length ≥ 1
-- All formulas are simplified
#guard ex_pq.all (isAzSimplified ·.2)

-- BPR Example 1.17 polynomials as a singleton
private def ex117P := p "x^4+(a)*x^2+(b)*x+(c)"
private def ex117Q := p "(4)*x^3+(2*a)*x+(b)"

-- posgcd of singleton: result is the polynomial itself with true formula
private def ex117single := azPosgcd [ex117P]
#guard ex117single.length == 1
#guard ex117single.map (fun pair => s pair.1) == ["x^4+(a)*x^2+(b)*x+(c)"]

-- posgcd of {P, Q}: 9 leaf paths in TRems(P, Q) → 9 pairs
#guard (azPosgcd [ex117P, ex117Q]).length == 9
-- All formulas are simplified
#guard (azPosgcd [ex117P, ex117Q]).all (isAzSimplified ·.2)

/-! #### BPR Example 1.21

`Posgcd({P, P'})` where `P = X⁴ + aX² + bX + c` and
`P' = 4X³ + 2aX + b`. The 9 elements `(Gᵢ, Cᵢ)` correspond to the
9 leaf paths of `TRems(P, P')`.

The leaf parents (the `G` components) are exactly the non-zero nodes
of `TRems(P, P')`:

| i | Gᵢ | leaf path ending |
|---|-----|------------------|
| 1 | P  | root 0-sentinel  |
| 2 | P' | P'-level 0-sentinel |
| 3 | (−8a)X² + (−12b)X + (−16c) | level-2 0-sentinel |
| 4 | (−128a³ − 576b² + 512ac)X + (−64a²b − 768bc) | level-3 0-sentinel |
| 5 | big degree-0 poly | deepest non-leaf |
| 6 | (−64a²b − 768bc) | level-3 truncation |
| 7 | (−12b)X + (−16c) | level-2 truncation |
| 8 | (−20736b⁵ + …) | level-3 via [0,1] |
| 9 | (−16c) | level-2 truncation |
-/

private def ex121 := azPosgcd [ex117P, ex117Q]

-- 9 elements total
#guard ex121.length == 9

-- The G-components are the leaf parents of TRems(P, P'), enumerated
-- depth-first (deepest leaf first, root 0-sentinel last).
#guard ex121.map (fun pair => s pair.1) ==
  [ "(-65536*a^5*b^2+262144*a^6*c-442368*a^2*b^4+2359296*a^3*b^2*c-2097152*a^4*c^2+4194304*a^2*c^3)",
    "(-128*a^3-576*b^2+512*a*c)*x+(-64*a^2*b-768*b*c)",
    "(-64*a^2*b-768*b*c)",
    "(-8*a)*x^2+(-12*b)*x+(-16*c)",
    "(-20736*b^5+55296*a*b^3*c+196608*b*c^3)",
    "(-12*b)*x+(-16*c)",
    "(-16*c)",
    "(4)*x^3+(2*a)*x+(b)",
    "x^4+(a)*x^2+(b)*x+(c)" ]

-- All formulas are simplified
#guard ex121.all (isAzSimplified ·.2)

-- The last element (G₉ = P): when P' specializes to 0, gcd = P itself.
#guard s (ex121.getD 8 (0, azTrueFormula)).1 == "x^4+(a)*x^2+(b)*x+(c)"

end Tests

end Azurite
