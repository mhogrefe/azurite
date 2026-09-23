/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Algorithm 4.3.2, computable**: finding a principal generator in
  `Z_m[x]` — the executable counterpart of the proven reference
  implementation `Azurite.CP.gcdOrFactor`
  (`CrandallPomerance/Chapter4/Algorithm_4_3_2.lean`).

  Given `f, g` over `AzZMod m`, run the Euclidean algorithm: while
  `f ≠ 0`, compute the extended GCD of `f`'s leading coefficient `c`
  with `m` (limb-level `AzInt.egcd`); if `gcd(c, m) = 1` the Bézout
  coefficient reduces to the modular inverse of `c`, so `f` can be
  made monic and `g` reduced mod `f` (`modByMonic`, which needs no
  further inverses); otherwise `gcd(c, m)` is a nontrivial factor of
  `m`, and the algorithm reports it instead.

  The recursion is fuel-based (the reference uses well-founded
  recursion on `deg f`): each Euclidean step strictly drops the dense
  coefficient size of the first argument, so `f.coeffs.size + 1`
  steps always suffice — fuel sufficiency is part of the bridge proof
  (`Azurite/AzPolynomial/Equiv/GcdOrFactor.lean`), which shows the
  result maps to `CP.gcdOrFactor m.toNat` under
  `toNat`/`toPoly`-plus-coefficient transport, so the reference
  specification (factor verdicts are nontrivial divisors of `m`; gcd
  verdicts are monic and generate the pair ideal) transfers verbatim.
-/
import Azurite.AzPolynomial.DivModByMonic
import Azurite.AzPolynomial.SMul
import Azurite.AzZMod.Conversion
import Azurite.AzZMod.Instances
import Azurite.AzMvPolynomial.ParsableCoeff.AzZMod
import Azurite.AzZMod.ToString
import Azurite.AzInt.ExtendedGcd

namespace Azurite.AzPolynomial

/-- Fuel-driven core of Algorithm 4.3.2.  Each recursive step strictly
shrinks `f.coeffs.size`, so the fuel-out branch is never reached when
started with `f.coeffs.size + 1` fuel (proved in the bridge). -/
def gcdOrFactorAux (m : AzNat) [NeZero m.toNat] :
    ℕ → AzPolynomial (AzZMod m) → AzPolynomial (AzZMod m) →
    AzNat ⊕ AzPolynomial (AzZMod m)
  | 0, _, g => .inr g
  | fuel + 1, f, g =>
    if f = 0 then .inr g
    else if (AzInt.egcd f.leadingCoeff.val m).1 = 1 then
      gcdOrFactorAux m fuel
        (modByMonic g
          (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f))
        (AzZMod.ofAzInt m (AzInt.egcd f.leadingCoeff.val m).2.1 • f)
    else .inl (AzInt.egcd f.leadingCoeff.val m).1

/-- **Algorithm 4.3.2 (finding a principal generator), computable**:
either a nontrivial factor of `m`, or (for monic `g`) a monic `h`
with `(f, g) = (h)` as ideals of `Z_m[x]` — see
`Azurite.AzPolynomial.gcdOrFactor_factor` /
`Azurite.AzPolynomial.gcdOrFactor_gcd` for the transported
specification. -/
def gcdOrFactor (m : AzNat) [NeZero m.toNat]
    (f g : AzPolynomial (AzZMod m)) : AzNat ⊕ AzPolynomial (AzZMod m) :=
  gcdOrFactorAux m (f.coeffs.size + 1) f g

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

/-- Render a verdict for the guards: `"factor d"` or the gcd string. -/
private def showVerdict {m : AzNat} [NeZero m.toNat] [Fact (1 < m.toNat)]
    (r : AzNat ⊕ AzPolynomial (AzZMod m)) : String :=
  match r with
  | .inl d => "factor " ++ toString d
  | .inr h => toChars h

private instance : Fact (1 < (AzNat.ofNat 6).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private instance : Fact (1 < (AzNat.ofNat 5).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private instance : Fact (1 < (AzNat.ofNat 91).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def r6 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 6)) :=
  (parseAzPolynomial s).get!

private def r5 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 5)) :=
  (parseAzPolynomial s).get!

private def r91 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 91)) :=
  (parseAzPolynomial s).get!

-- shared factor: gcd(x + 1, x² + 3x + 2) = x + 1 over Z_6
#guard showVerdict (gcdOrFactor (AzNat.ofNat 6) (r6 "x+1") (r6 "x^2+3*x+2"))
  == "x+1"

-- a non-invertible leading coefficient reports the factor gcd(2, 6) = 2
#guard showVerdict (gcdOrFactor (AzNat.ofNat 6) (r6 "2*x+1") (r6 "x^2"))
  == "factor 2"

-- coprime pair over the field Z_5: the generator is the unit 1
#guard showVerdict (gcdOrFactor (AzNat.ofNat 5) (r5 "x+1") (r5 "x+2"))
  == "1"

-- non-monic f is normalized on the way: 2x + 2 = 2(x + 1) over Z_5
#guard showVerdict (gcdOrFactor (AzNat.ofNat 5) (r5 "2*x+2") (r5 "x^2+3*x+2"))
  == "x+1"

-- Z_91 = Z_7·Z_13: leading coefficient 7 betrays the factor 7
#guard showVerdict (gcdOrFactor (AzNat.ofNat 91) (r91 "7*x+1") (r91 "x^2"))
  == "factor 7"

-- f = 0 returns g unchanged
#guard showVerdict (gcdOrFactor (AzNat.ofNat 6) (r6 "0") (r6 "x^3+x"))
  == "x^3+x"

end Tests
