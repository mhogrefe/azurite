import Azurite.BasuPollackRoy.Chapter1.Section1_3.LeafFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Lemma1_19
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems

/-! # BPR Section 1.3 — Set of possible greatest common divisors `posgcd`

The *set of possible greatest common divisors* of a finite family
`𝒫 ⊂ D[Y₁, …, Y_k][X]` is a finite list of pairs `(G, 𝒞)` where
`G ∈ D[Y₁, …, Y_k][X]` and `𝒞` is a formula, such that for each pair,
`y ∈ Reali(𝒞)` implies `gcd(𝒫_y) = G_y`.

Defined recursively:
- `posgcd(∅) = {(0, True)}`
- `posgcd(𝒫 ∪ {P}) = {(Pol(p(L)), 𝒞 ∧ 𝒞_L) | (Q, 𝒞) ∈ posgcd(𝒫),
   L leaf of TRems(P, Q)}`

This construction is named in BPR's prose but not assigned a numbered
definition. The correctness theorems (covering, uniqueness, gcd
identification) live in
`Azurite.BasuPollackRoy.Chapter1.Section1_3.Lemma1_20`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

section PosGcd

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- BPR's set of possible greatest common divisors of a finite family
`𝒫 ⊂ D[Y₁, …, Yₖ][X]`.

Each element is a pair `(G, 𝒞)` where `G` is a polynomial and `𝒞`
is a formula such that `y ∈ Reali(𝒞)` implies `gcd(𝒫_y) = G_y`. -/
noncomputable def posgcd :
    List (Polynomial (MvPolynomial (Fin k) D)) →
    List (Polynomial (MvPolynomial (Fin k) D) ×
      Formula (Fin k) (FieldAtom (Fin k) D))
  | [] => [(0, Formula.trueFormula)]
  | P :: rest =>
    (posgcd rest).flatMap fun (Q, 𝒞) =>
      (TRems P Q).leafPaths.map fun path =>
        (pathLeafParent P path, 𝒞.and (leafFormula P Q path))

end PosGcd

end Azurite.BPR
