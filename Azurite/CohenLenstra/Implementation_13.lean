/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra §13: the implementation.**

  The paper closes with the Cohen–A. K. Lenstra implementation
  (Pascal and Fortran, CDC Cyber, Winter's Compass multiprecision
  routines), forerunner of the "forthcoming publication" — the
  practical-improvements paper that our own implementation phase
  waits for.  The concrete capacity claims are certified here
  against our computable `e`:

  * Pascal: `t = 5040`, `e(5040) > 1.5·10^52` — 104 decimal
    digits (guarded here; the full factorization is already a
    guard in `Proposition_4_1.lean`);
  * Fortran: `t = 55440`, `e(55440) > 4.9·10^106` — 213 decimal
    digits (guarded here).

  Implementation notes recorded for our own rail (prose):

  * The 1984 programs use §10 only in the `f = 1` case
    (`F = ℤ/nℤ`, `ρ = id`), plus an `n²`-element ring `F` to
    combine with the `n² − 1`-factor tests of [16, §8] — the
    Lucas-sequence connection of our Lucas–Lehmer arc.  Our
    formalized §10 covers the general case, and the cert design
    may use it fully.
  * The Fortran program *recomputes* the Step-1 tables per `n`
    rather than storing them — the memory/time trade our
    implementation will face too.
  * The hot loop is multiplication in `ℤ[ζ_{p^k}]/(n)`:
    polynomials of degree `< m = (p−1)p^(k−1)` with `ℤ/n`
    coefficients, reduced mod `Φ_{p^k}`.  Naively `m²` integer
    multiplications; Winograd's `2m − 1` is impractical; the
    paper uses hand-tuned per-`p^k` formulae (e.g. `p^k = 16`:
    27 multiplications instead of 64, and 18 for a squaring)
    and expects further improvement — the design space for our
    `AzPolynomial`/`AzZMod` kernels (Karatsuba, dedicated
    squaring, lazy carry/reduction) at implementation time.
-/
import Azurite.CohenLenstra.Proposition_4_1

namespace Azurite

namespace CL

/-! The capacity claims, certified as build-time guards against the
computable `e` (interpreter-evaluated, like the Table 1/2 guards of
`Proposition_4_1.lean`; kernel reduction of `e` at these sizes is
infeasible, and guards carry no proof obligations). -/

-- Pascal: `t = 5040` handles up to 104 decimal digits.
#guard 15 * 10 ^ 51 < Azurite.CL.e 5040

-- Fortran: `t = 55440` handles up to 213 decimal digits.
#guard 49 * 10 ^ 105 < Azurite.CL.e 55440

end CL

end Azurite
