/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Matrix-vector and vector-matrix multiplication for AzMatrix.
-/
import Azurite.AzMatrix.RowCol
import Azurite.AzVector.Dot

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Matrix-vector product: `(M *ᵥ v)ᵢ = Σⱼ Mᵢⱼ · vⱼ`. -/
def AzMatrix.mulVec [Mul R] [Add R] [Zero R] (M : AzMatrix R m n) (v : AzVector R n) :
    AzVector R m :=
  AzVector.ofFn (fun i => (M.row i).dot v)

/-- Vector-matrix product: `(v ᵥ* M)ⱼ = Σᵢ vᵢ · Mᵢⱼ`. -/
def AzMatrix.vecMul [Mul R] [Add R] [Zero R] (v : AzVector R m) (M : AzMatrix R m n) :
    AzVector R n :=
  AzVector.ofFn (fun j => v.dot (M.col j))

end Azurite
