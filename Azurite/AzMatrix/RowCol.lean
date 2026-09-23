/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Row and column access for AzMatrix.
-/
import Azurite.AzMatrix.Basic
import Azurite.AzVector.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Extract the `i`-th row as an `AzVector`. -/
def AzMatrix.row (M : AzMatrix R m n) (i : Fin m) : AzVector R n :=
  ⟨M.data.get i⟩

/-- Extract the `j`-th column as an `AzVector`. -/
def AzMatrix.col (M : AzMatrix R m n) (j : Fin n) : AzVector R m :=
  ⟨Vector.ofFn (fun i => M.get i j)⟩

/-- Construct a matrix from a vector of row vectors. -/
def AzMatrix.ofRows (rows : Vector (AzVector R n) m) : AzMatrix R m n :=
  ⟨rows.map (fun v => v.data)⟩

/-- Construct a matrix from a vector of column vectors. -/
def AzMatrix.ofCols (cols : Vector (AzVector R m) n) : AzMatrix R m n :=
  AzMatrix.ofFn (fun i j => (cols.get j).data.get i)

end Azurite
