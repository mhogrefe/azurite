/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.Results.Conclusions
import Azurite.Transcendental.Catalan

/-!
# Catalan's constant is irrational

`irrational_catalanConstant`: the irrationality of `G = ∑_{j≥0} (−1)^j/(2j+1)²`, proved in 2026
by an OpenAI model and formalized in the OpenAI mathematics repository
(<https://github.com/openai/math>, family 005, "Catalan's constant is irrational").  The import
closure of that proof (489 files, including a proof of the prime number theorem adapted from the
PrimeNumberTheoremAnd project) is vendored unchanged, up to import paths, in
`Azurite/CatalanIrrational/`; its conclusion is `OAI.InternalCatalan.catalan_irrational`.

This is what makes the Ziv loop of the `AzFloat` Catalan constant fuel-free
(`Azurite/AzFloat/Catalan.lean`).
-/

namespace Azurite

/-- **Catalan's constant is irrational.** -/
theorem irrational_catalanConstant : Irrational catalanConstant :=
  OAI.InternalCatalan.catalan_irrational

end Azurite
