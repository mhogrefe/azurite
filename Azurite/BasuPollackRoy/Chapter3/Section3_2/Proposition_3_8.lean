/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_2.ConvexProduct
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_7

/-! # BPR §3.2, Proposition 3.8 — the open cube is semialgebraically connected

The open cube `(0,1)^k` is convex (Proposition `isConvex_openCube`), hence semialgebraically
connected (Proposition 3.7). -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Proposition 3.8.** The open cube `(0,1)^k` is semialgebraically connected. -/
theorem isSemialgebraicallyConnected_openCube :
    IsSemialgebraicallyConnected (openCube k R) :=
  proposition_3_7 isConvex_openCube

end Azurite.BPR
