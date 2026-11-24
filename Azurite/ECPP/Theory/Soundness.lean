/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.Criterion
import Azurite.ECPP.Theory.ManinHasse

/-!
# Elliptic curve primality proving: soundness, unconditionally

The criterion of `Theory/Criterion.lean` with the Hasse bound supplied
(`hasseBound`, `Theory/ManinHasse.lean`): a step with a prime `q` proves `N` prime
(`EcppStep.isPrime`), and so does a chain of steps down to a prime (`EcppProof.isPrime`).
This is what the checker on `Az*` types has to establish: an `EcppProof`.
-/

namespace Azurite.ECPP

/-- **One step proves primality**: `EcppStep N q` and `q` prime give `N` prime. -/
theorem EcppStep.isPrime {N q : ℕ} (h : EcppStep N q) (hq : q.Prime) : N.Prime :=
  h.prime hasseBound hq

/-- **A proof by elliptic curves proves primality.** -/
theorem EcppProof.isPrime {N : ℕ} (h : EcppProof N) : N.Prime :=
  h.prime hasseBound

end Azurite.ECPP
