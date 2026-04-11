/-
  Pure character-list conversions for coefficient types (`ℕ`, `ℤ`, `ℚ`, `ZMod n`).

  These definitions are shared by the display layer (`AzMvPolynomial.ToString` /
  `AzPolynomial.ToString` via `ParsableCoeff`) and the parsing layer. They do
  not reference `AzPolynomial R` / `AzMvPolynomial n R ord`, so they live
  below those modules in the import graph and can be freely used by both.
-/
import Azurite.AzNat.ToString
import Azurite.AzNat.Parse
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.AzPolynomial

/-! ### Integer → char list -/

def intToChars (z : ℤ) : List Char :=
  if z < 0 then
    let n := z.natAbs
    if n = 0 then ['0']
    else '-' :: natToCharsAux n n []
  else
    let n := z.natAbs
    if n = 0 then ['0']
    else natToCharsAux n n []

/-! ### Rational → char list -/

def ratToChars (q : ℚ) : List Char :=
  if q.den = 1 then intToChars q.num
  else intToChars q.num ++ ['/'] ++ natToChars q.den

/-! ### ZMod n → char list -/

def zmodToChars {n : ℕ} [NeZero n] (c : ZMod n) : List Char := natToChars c.val

/-! ### char list → ℤ -/

def parseIntChars (cs : List Char) : Option ℤ :=
  match cs with
  | [] => none
  | '-' :: cs => (parseNatChars cs).map (fun n => - (n : ℤ))
  | _ => (parseNatChars cs).map (fun n => (n : ℤ))

/-! ### char list → ℚ -/

def parseRatChars (cs : List Char) : Option ℚ :=
  match cs.splitOn '/' with
  | [num_cs] =>
    (parseIntChars num_cs).map (fun n => (n : ℚ))
  | [num_cs, den_cs] =>
    match parseIntChars num_cs, parseNatChars den_cs with
    | some num, some den =>
      if den = 0 then none
      else some ((num : ℚ) / (den : ℚ))
    | _, _ => none
  | _ => none

end Azurite.AzPolynomial
