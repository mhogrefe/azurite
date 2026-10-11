/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Fibonacci
import Azurite.AzNat.Sub

/-!
## Lucas numbers

`lucasNumber n = L_n` (`L_0 = 2`, `L_1 = 1`, `L_{n+2} = L_n + L_{n+1}`) and
`lucasNumberPair n = (L_n, L_{n−1})`.  Mathlib has no Lucas numbers, so the reference
`Nat.lucas` is defined here by the recurrence.

The Lucas numbers ride on the Fibonacci pair: with `(a, b) = (F_n, F_{n−1})`,
`L_n = F_{n−1} + F_{n+1} = a + 2b` and `L_{n−1} = F_{n−2} + F_n = 2a − b`, so one call of the
fast-doubling `fibonacciPair` and two shifts give the pair at the same `O(M(F_n))` cost.  Since
`L_{−1} = −1` is not a natural number, the second component of `lucasNumberPair 0` is the
truncated `0`: `lucasNumberPair 0 = (2, 0)`.
-/

namespace Nat

/-- The Lucas numbers `L_0 = 2`, `L_1 = 1`, `L_{n+2} = L_n + L_{n+1}`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

end Nat

namespace Azurite.AzNat

/-- **The Lucas pair** `(L_n, L_{n−1})`; `lucasNumberPair 0 = (2, 0)`. -/
def lucasNumberPair (n : Nat) : AzNat × AzNat :=
  let p := fibonacciPair n
  (p.1 + (p.2 <<< 1), (p.1 <<< 1) - p.2)

/-- **The Lucas number** `L_n`. -/
def lucasNumber (n : Nat) : AzNat := (lucasNumberPair n).1

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def L (n : Nat) : String := AzNat.toString (lucasNumber n)
private def LP (n : Nat) : String × String :=
  (AzNat.toString (lucasNumberPair n).1, AzNat.toString (lucasNumberPair n).2)

#guard (List.range 12).map L
  == ["2", "1", "3", "4", "7", "11", "18", "29", "47", "76", "123", "199"]
#guard L 20 == "15127"
#guard L 50 == "28143753123"
#guard L 100 == "792070839848372253127"
#guard (L 1000).length == 209
#guard (L 1000).take 30 == "971941777359081752079819820793"
#guard (L 1000).drop (209 - 30) == "681531675707666695323797578127"
#guard LP 0 == ("2", "0")
#guard LP 1 == ("1", "2")
#guard LP 2 == ("3", "1")
#guard LP 3 == ("4", "3")
#guard LP 10 == ("123", "76")
#guard LP 11 == ("199", "123")
#guard LP 100 == ("792070839848372253127", "489526700523968661124")
-- agreement with the iteration, and with `L_n = F_{n−1} + F_{n+1}`
private def naive (n : Nat) : AzNat × AzNat :=
  (List.range n).foldl (fun (p : AzNat × AzNat) _ => (p.1 + p.2, p.1)) (1, ofNat 2)
#guard (List.range 400).all fun n => lucasNumberPair (n + 1) == naive n
#guard lucasNumberPair 3001 == naive 3000
#guard (List.range 300).all fun n => lucasNumber (n + 1) == fibonacci n + fibonacci (n + 2)

end Tests
