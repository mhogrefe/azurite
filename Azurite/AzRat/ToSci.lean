/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Sci.Number
import Azurite.AzRat.LengthAfterPoint
import Azurite.AzRat.LogBase
import Azurite.AzRat.Round
import Azurite.AzInt.DivRound
import Azurite.AzInt.Conversion
import Azurite.AzNat.Pow
import Azurite.AzNat.Mul
import Azurite.AzNat.LimbDigits

/-!
# `AzRat.toSci`: scientific-notation output

Port of the author's `Rational::to_sci` (Malachite), in the two stages of
`docs/to_sci_plan.md`:

* `toSciNumber q opts : Option SciNumber` does the arithmetic: the base-`b` exponent
  (`floorLogBaseAbs`), the scale and digit count from the size option, the rounding of
  `q · b^scale` to an integer (`AzRat.round`), and the adjustment when that rounds up to a
  power of the base.  It is `none` only when the request cannot be met: invalid options, or
  `complete` for a value whose base-`b` expansion does not terminate.
* `toSci q opts : Option String` renders the `SciNumber` (`SciNumber.toString`, digits only).

`toSciExact q opts` is Malachite's `RoundingMode::Exact` as a predicate: `true` iff the value
needs no rounding at the requested size (so `toSci` prints it exactly).
-/

namespace Azurite.AzRat

/-- The `scale` recorded for a zero result: how many zeros after the point to print when
trailing zeros are requested (`fmt_zero` in Malachite). -/
def zeroScale (size : SciSizeOptions) : Int :=
  match size with
  | .complete => 0
  | .scale s => s
  | .precision p => (p : Int) - 1

/-- The scale (digits after the point) and digit count requested by a size option, given the
base-`b` exponent `log` of the value; `none` when `complete` is requested for a
non-terminating expansion. -/
def sizeScale (b : UInt64) (q : AzRat) (size : SciSizeOptions) (log : Int) : Option (Int × Int) :=
  match size with
  | .complete => (lengthAfterPoint b q).map fun (L : ℕ) => ((L : Int), (L : Int) + log + 1)
  | .scale s => some ((s : Int), (s : Int) + log + 1)
  | .precision p => some ((p : Int) - 1 - log, (p : Int))

/-- `q · b^scale`, rounded to an integer with `mode` (with the `Ordering` tag of
`AzInt.divRound`).  Computed as one signed division — `(num · b^scale) / den` for
`scale ≥ 0`, `num / (den · b^(−scale))` otherwise — so no gcd of huge operands is formed. -/
def scaledRound (q : AzRat) (b : UInt64) (scale : Int) (mode : RoundingMode) :
    AzInt × Ordering :=
  let bN := AzNat.ofNat b.toNat
  match scale with
  | .ofNat s => AzInt.divRound (AzInt.mkNorm q.sign (q.num * bN.pow s)) q.den.toAzInt mode
  | .negSucc s =>
    AzInt.divRound (AzInt.mkNorm q.sign q.num) (q.den * bN.pow (s + 1)).toAzInt mode

/-- Stage 1 of `toSci`: the rounded value in positional form, or `none` when the request
cannot be met. -/
def toSciNumber (q : AzRat) (o : SciOptions) : Option SciNumber :=
  if !o.valid then none
  else if q.num = 0 then
    some { negative := false, base := o.base, digits := #[], scale := zeroScale o.size }
  else
    let log := floorLogBaseAbs o.base q
    match sizeScale o.base q o.size log with
    | none => none
    | some (scale, _precision) =>
      let r := scaledRound q o.base scale o.mode
      let n := r.1.abs
      if n = 0 then
        some { negative := !q.sign, base := o.base, digits := #[], scale := zeroScale o.size }
      else
        let ds := (n.limbDigits o.base).reverse
        let neg := !r.1.sign
        match o.size with
        | .precision p =>
          if ds.size = p + 1 then
            -- rounded up to a power of the base: one digit too many, the last one `0`
            some { negative := neg, base := o.base, digits := ds.pop, scale := scale - 1 }
          else
            some { negative := neg, base := o.base, digits := ds, scale := scale }
        | _ => some { negative := neg, base := o.base, digits := ds, scale := scale }

/-- Malachite's `fmt_sci_valid` for `RoundingMode::Exact`: the value needs no rounding at the
requested size (and, for `complete`, its expansion terminates). -/
def toSciExact (q : AzRat) (o : SciOptions) : Bool :=
  o.valid && (q.num = 0 ||
    match o.size with
    | .complete => (lengthAfterPoint o.base q).isSome
    | _ =>
      match sizeScale o.base q o.size (floorLogBaseAbs o.base q) with
      | none => false
      | some (scale, _) => (scaledRound q o.base scale o.mode).2 == .eq)

/-- `toSci q o`: `q` in base `o.base`, rounded to the requested size with `o.mode`, rendered
per `o.format`; `none` when the request cannot be met (see `toSciNumber`). -/
def toSci (q : AzRat) (o : SciOptions := {}) : Option String :=
  (q.toSciNumber o).map (·.toString o.format)

/-- `toSci` with the default options, as a `String` (`""` never happens: the defaults are
valid and never `complete`). -/
def toSciString (q : AzRat) : String :=
  (q.toSci {}).getD ""

end Azurite.AzRat
