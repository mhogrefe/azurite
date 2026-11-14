/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRatBracket
import Azurite.AzFloat.SinRatBracket

/-!
## The joint bracket of `sin q` and `cos q` for a rational `q`

`sinCosRatBracket q w` encloses `sin |q|` and `cos q` together for an `AzRat` `q` at Ziv level
`w`: with `eq = ratExpBound q` and `W = cosWork eq w`, one evaluation of `sinCosBracket c eq w`
at the float `c` nearer zero among `⌊q⌋_W`, `⌈q⌉_W`, both components widened by the Lipschitz
bound `E ≥ ⌈q⌉_W − ⌊q⌋_W`.  Its components are `sinRatBracket q w` and `cosRatBracket q w`
(`sinCosRatBracket_fst`, `sinCosRatBracket_snd`, by `rfl`), so their specifications apply.
`sinCosRatApprox` is the pair of pairs of `Roundable`s for the joint Ziv loop
(`AzFloat/SinCosRat.lean`); its components are `sinRatApprox q w` and `cosRatApprox q w`.
-/

namespace Azurite.AzFloat

/-- The joint bracket `([sin |q|], [cos q])` at Ziv level `w` for a rational `q`. -/
def sinCosRatBracket (q : AzRat) (w : Nat) : Encl × Encl :=
  let eq := ratExpBound q
  let W := cosWork eq w
  let xlo := (ofAzRatRound q W .Floor).1
  let xhi := (ofAzRatRound q W .Ceiling).1
  let E := (subPrecRound xhi xlo 64 .Ceiling).1
  let b := sinCosBracket (if q.sign then xlo else xhi) eq w
  (Encl.widen W b.1 (Encl.exact E), Encl.widen W b.2 (Encl.exact E))

theorem sinCosRatBracket_fst (q : AzRat) (w : Nat) :
    (sinCosRatBracket q w).1 = sinRatBracket q w := rfl

theorem sinCosRatBracket_snd (q : AzRat) (w : Nat) :
    (sinCosRatBracket q w).2 = cosRatBracket q w := rfl

/-- `sinCosRatBracket` as `Roundable`s for the joint Ziv loop: the bracket of `sin q` (negated
and swapped for `q < 0`) and the bracket of `cos q`. -/
def sinCosRatApprox (q : AzRat) (w : Nat) : (Roundable × Roundable) × (Roundable × Roundable) :=
  let b := sinCosRatBracket q w
  (if q.sign then (fun p mode => setPrecRound b.1.1 p mode, fun p mode => setPrecRound b.1.2 p mode)
    else (fun p mode => setPrecRound (-b.1.2) p mode, fun p mode => setPrecRound (-b.1.1) p mode),
    (fun p mode => setPrecRound b.2.1 p mode, fun p mode => setPrecRound b.2.2 p mode))

theorem sinCosRatApprox_fst (q : AzRat) (w : Nat) :
    (sinCosRatApprox q w).1 = sinRatApprox q w := rfl

theorem sinCosRatApprox_snd (q : AzRat) (w : Nat) :
    (sinCosRatApprox q w).2 = cosRatApprox q w := rfl

end Azurite.AzFloat
