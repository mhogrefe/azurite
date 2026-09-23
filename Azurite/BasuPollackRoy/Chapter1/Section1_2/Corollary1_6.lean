/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm

/-!
# Corollary 1.6

The degrees of the GCD and the LCM of $P$ and $Q$ in $K[X]$ sum to
$\deg P + \deg Q$. We state this additively because $\lcode{WithBot}\,\mathbb{N}$
does not support subtraction.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- BPR Corollary 1.6: degGcd(P, Q) + degLcm(P, Q) = deg(P) + deg(Q).
    Stated additively since `WithBot ℕ` does not support subtraction. -/
theorem corollary_1_6 (P Q : K[X]) :
    degGcd P Q + degLcm P Q = P.degree + Q.degree := by
  have h := degree_eq_degree_of_associated (gcd_mul_lcm P Q)
  rwa [degree_mul, degree_mul] at h

end Azurite.BPR
