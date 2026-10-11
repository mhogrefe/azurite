/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.AzNat.Square
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ToStringBase
import Azurite.AzNat.ParseBase

/-!
## Fibonacci numbers

`fibonacci n = F_n` (`F_0 = 0`, `F_1 = 1`, `F_{n+2} = F_n + F_{n+1}`) and
`fibonacciPair n = (F_n, F_{n−1})`, with `fibonacciPair 0 = (0, 1)` (the value `F_{−1} = 1` that
continues the recurrence backwards).

**Fast doubling.**  From the pair `(a, b) = (F_m, F_{m−1})`, so that `F_{m+1} = a + b`,
`F_{2m} = F_m (2 F_{m+1} − F_m) = a (a + 2b)` and `F_{2m+1} = F_{m+1}² + F_m² = (a + b)² + a²`,
hence `F_{2m−1} = F_{2m+1} − F_{2m} = a² + b²`.  Descending through the binary digits of `n`
(one recursive call on `n / 2`, then one doubling step and, for an odd `n`, one addition) costs
one multiplication and two squarings per bit — `O(M(F_n))` in total, since the sizes double at
each level — against `n` additions of growing numbers for the iteration.

Correctness: `Equiv/Fibonacci.lean` (`toNat_fibonacci`, `toNat_fibonacciPair`).
-/

namespace Azurite.AzNat

/-- One doubling step: `(F_m, F_{m−1}) ↦ (F_{2m}, F_{2m−1})`, and the extra step to
`(F_{2m+1}, F_{2m})` when `odd`. -/
def fibonacciDouble (a b : AzNat) (odd : Bool) : AzNat × AzNat :=
  let c := a * (a + (b <<< 1))
  let d := square a + square b
  if odd then (c + d, c) else (c, d)

/-- The recursion on the binary digits of `n`; `fuel` bounds the depth (`n` itself suffices). -/
def fibonacciPair.go : Nat → Nat → AzNat × AzNat
  | 0, _ => (0, 1)
  | fuel + 1, n =>
    if n = 0 then (0, 1)
    else
      let p := fibonacciPair.go fuel (n / 2)
      fibonacciDouble p.1 p.2 (n % 2 = 1)

/-- **The Fibonacci pair** `(F_n, F_{n−1})`; `fibonacciPair 0 = (0, 1)`. -/
def fibonacciPair (n : Nat) : AzNat × AzNat := fibonacciPair.go n n

/-- **The Fibonacci number** `F_n`. -/
def fibonacci (n : Nat) : AzNat := (fibonacciPair n).1

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def F (n : Nat) : String := AzNat.toString (fibonacci n)
private def FP (n : Nat) : String × String :=
  (AzNat.toString (fibonacciPair n).1, AzNat.toString (fibonacciPair n).2)

#guard F 0 == "0"
#guard F 1 == "1"
#guard F 2 == "1"
#guard F 3 == "2"
#guard F 4 == "3"
#guard F 5 == "5"
#guard F 6 == "8"
#guard F 7 == "13"
#guard F 10 == "55"
#guard F 12 == "144"
#guard F 20 == "6765"
#guard F 50 == "12586269025"
#guard F 100 == "354224848179261915075"
#guard F 200 == "280571172992510140037611932413038677189525"
#guard (F 1000).length == 209
#guard (F 1000).take 30 == "434665576869374564356885276750"
#guard (F 1000).drop (209 - 30) == "516003704476137795166849228875"
#guard FP 0 == ("0", "1")
#guard FP 1 == ("1", "0")
#guard FP 2 == ("1", "1")
#guard FP 3 == ("2", "1")
#guard FP 10 == ("55", "34")
#guard FP 11 == ("89", "55")
#guard FP 100 == ("354224848179261915075", "218922995834555169026")
-- agreement with the iteration
private def naive (n : Nat) : AzNat × AzNat :=
  (List.range n).foldl (fun (p : AzNat × AzNat) _ => (p.1 + p.2, p.1)) (0, 1)
#guard (List.range 400).all fun n => fibonacciPair n == naive n
#guard fibonacciPair 5000 == naive 5000

end Tests
