/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/ZetaFive/Identities/Endpoints.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.ZetaFive.Arithmetic.LargePrimeTable

namespace OAI

namespace Zeta5.Workers.W20

theorem endpoint_46_5 : largePrimeLimit (46/5) = -273/5 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_19_2 : largePrimeLimit (19/2) = -105/2 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_10 : largePrimeLimit (10) = -45 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_11 : largePrimeLimit (11) = -26 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_12 : largePrimeLimit (12) = -9 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_15 : largePrimeLimit (15) = 36 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_16 : largePrimeLimit (16) = 18 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

theorem endpoint_18 : largePrimeLimit (18) = 30 := by
  norm_num [largePrimeLimit, fInf, gInf, j0, nbad, ib, hs, ha, ns, nd, nm]

end Zeta5.Workers.W20

end OAI
