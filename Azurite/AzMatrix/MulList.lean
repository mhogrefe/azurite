/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Multiplication of several square `AzMatrix` values.

  `mulList Ms` multiplies a list of `n × n` matrices left-to-right, returning
  the identity matrix when the list is empty. The current implementation is a
  simple left fold over `mul`; a future revision may swap in a more efficient
  algorithm (e.g. balanced reductions or matrix-chain ordering).
-/
import Azurite.AzMatrix.Mul
import Azurite.AzInt.Instances
import Azurite.AzMatrix.Operations

namespace Azurite
variable {R : Type _} {n : Nat}

/-- `mulList Ms = M_1 * M_2 * ⋯ * M_m` for a list `Ms = [M_1, …, M_m]`,
    via a left fold over `mul` starting from the identity matrix. The empty
    list returns the identity. -/
def AzMatrix.mulList [Mul R] [Add R] [Zero R] [One R]
    (Ms : List (AzMatrix R n n)) : AzMatrix R n n :=
  Ms.foldl AzMatrix.mul AzMatrix.identity

end Azurite

-- Sanity checks.

namespace Azurite

private def testA : AzMatrix AzInt 2 2 := AzMatrix.ofLists [[1, 2], [3, 4]]
private def testB : AzMatrix AzInt 2 2 := AzMatrix.ofLists [[5, 6], [7, 8]]
private def testC : AzMatrix AzInt 2 2 := AzMatrix.ofLists [[9, 10], [11, 12]]

-- Empty list → identity.
#guard AzMatrix.mulList ([] : List (AzMatrix AzInt 2 2)) = AzMatrix.identity
-- Single matrix → itself.
#guard AzMatrix.mulList [testA] = testA
-- Three matrices: A * B * C.
#guard AzMatrix.mulList [testA, testB, testC] = testA * testB * testC

end Azurite
