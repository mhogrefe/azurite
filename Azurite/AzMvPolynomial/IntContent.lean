/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Gcd
import Azurite.AzNat.Gcd
import Azurite.AzInt.Conversion
import Azurite.AzInt.Compare
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToString

/-!
# Integer content and primitive part of an `AzMvPolynomial` over `AzInt`

Multivariate analogues of the `AzPolynomial AzInt` content helpers, needed
for the factored canonical form of `AzMvRationalFunction`:

* `leadingCoeff P` — the coefficient of the `ord`-largest monomial (total,
  `0` for the zero polynomial);
* `intContent P` — the **full integer content**: the (nonnegative) `AzNat`
  gcd of the magnitudes of *all* term coefficients (`intContent 0 = 0`);
* `signedIntContent P` — the integer content carrying the sign of the
  leading coefficient;
* `primPos P` — the primitive, positive-leading representative: `P` divided
  (exactly) by `C (signedIntContent P)`, so that (for nonzero `P`)
  `P = C (signedIntContent P) * primPos P`, `primPos P` has `intContent = 1`
  and `leadingCoeff > 0`.

This file provides only the definitions and a few computational `#guard`s;
the algebraic specifications are proven in a later turn.
-/

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The leading coefficient: the coefficient of the `ord`-largest monomial
(`terms[0]` by the sorted invariant), or `0` for the zero polynomial. -/
def leadingCoeff (P : AzMvPolynomial n AzInt ord) : AzInt :=
  P.leadCoeff.elim 0 Subtype.val

/-- The **full integer content**: the nonnegative gcd of the magnitudes of
all term coefficients (`intContent 0 = 0`; positive for nonzero `P`). -/
def intContent (P : AzMvPolynomial n AzInt ord) : AzNat :=
  P.terms.foldl (fun acc m => AzNat.gcd acc m.coeff.val.abs) 0

/-- The integer content carrying the sign of the leading coefficient. -/
def signedIntContent (P : AzMvPolynomial n AzInt ord) : AzInt :=
  if (0 : AzInt) < leadingCoeff P then (intContent P).toAzInt
  else -(intContent P).toAzInt

/-- The **primitive, positive-leading representative**: `P` divided
(exactly) by `C (signedIntContent P)`. For nonzero `P` this is primitive
(`intContent = 1`) with positive leading coefficient; `primPos 0 = 0`. -/
def primPos (P : AzMvPolynomial n AzInt ord) : AzMvPolynomial n AzInt ord :=
  Azurite.ExactDiv.exactDiv P (AzMvPolynomial.C (signedIntContent P))

/-- The **sign-normalized representative**: `P` if its `ord`-leading
coefficient is positive, else `-P`. For nonzero `P` this is an associate of
`P` with positive leading coefficient. Used to normalize the (tower-normalized,
not `ord`-leading-positive) multivariate `gcd` before dividing out cofactors. -/
def signNorm (P : AzMvPolynomial n AzInt ord) : AzMvPolynomial n AzInt ord :=
  if (0 : AzInt) < leadingCoeff P then P else -P

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 2) s).getD 0

-- leadingCoeff: the ord-largest monomial's coefficient
#guard leadingCoeff (p2 "3*x^2*y-2*x+5") == (3 : AzInt)
#guard leadingCoeff (p2 "-6*x-4*y") == (-6 : AzInt)
#guard leadingCoeff (p2 "0") == (0 : AzInt)

-- intContent: gcd of coefficient magnitudes
#guard intContent (p2 "6*x+4*y") == (AzNat.parse "2").get!
#guard intContent (p2 "3*x+5") == (AzNat.parse "1").get!
#guard intContent (p2 "-2*x-2") == (AzNat.parse "2").get!
#guard intContent (p2 "0") == (AzNat.parse "0").get!

-- signedIntContent: content with the sign of the leading coefficient
#guard signedIntContent (p2 "6*x+4*y") == (2 : AzInt)
#guard signedIntContent (p2 "-2*x-2") == (-2 : AzInt)

-- primPos: primitive, positive leading coefficient
#guard (primPos (p2 "6*x+4*y")).toStrWith (XyzVar 2) == "3*x+2*y"
#guard (primPos (p2 "-2*x-2")).toStrWith (XyzVar 2) == "x+1"
#guard (primPos (p2 "0")).toStrWith (XyzVar 2) == "0"

end Tests

end Azurite.AzMvPolynomial
