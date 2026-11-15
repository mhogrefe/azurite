/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CatalanBracket

/-!
## Catalan's constant

`G = ∑_{j≥0} (−1)^j/(2j+1)² = 0.9159655941772190150546035149323841107741493742816721342664…`,
from the bracket of `CatalanBracket.lean` (two rational series summed exactly by binary
splitting, `π` and `√3`), rounded by the certified Ziv loop: `G` is irrational
(`irrational_catalanConstant`, the 2026 theorem of an OpenAI model, vendored in
`Azurite/CatalanIrrational/`) and the bracket width is at most `2^(−w)`
(`catalanBracket_spec`), so `zivLoopCertified` needs no fuel and `catalanConstantPrecRound` is
total and proven correctly rounded (`Equiv/Catalan.lean`).
-/

namespace Azurite.AzFloat

/-- Catalan's constant `G` rounded to precision `p` with `mode`, and the comparison with the
exact value (`NaN` at precision `0`). -/
def catalanConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified catalanApprox p mode (p + zivGuardBits)
      (catalanApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- Catalan's constant `G` rounded to nearest at precision `p`. -/
def catalanConstant (p : Nat) : AzFloat := (catalanConstantPrecRound p .Nearest).1

end Azurite.AzFloat
