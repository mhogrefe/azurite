import Azurite.DensePoly.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.DensePoly

/-- A typeclass for types whose elements can be parsed from a monomial string coefficient. -/
class DensePolyParsable (R : Type _) where
  parse : List Char → Option R

def parseNatCharsAux (cs : List Char) (acc : ℕ) : Option ℕ :=
  match cs with
  | [] => some acc
  | c :: cs =>
    if c.isDigit then
      parseNatCharsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

def parseNatChars (cs : List Char) : Option ℕ :=
  match cs with
  | [] => none
  | _ => parseNatCharsAux cs 0

def natToCharsAux (fuel : ℕ) (n : ℕ) (acc : List Char) : List Char :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if n = 0 then acc
    else
      let digit := Char.ofNat ('0'.toNat + (n % 10))
      natToCharsAux f (n / 10) (digit :: acc)

def natToChars (n : ℕ) : List Char :=
  if n = 0 then ['0']
  else natToCharsAux n n []

def parseIntChars (cs : List Char) : Option ℤ :=
  match cs with
  | [] => none
  | '-' :: cs => (parseNatChars cs).map (fun n => - (n : ℤ))
  | _ => (parseNatChars cs).map (fun n => (n : ℤ))

def intToChars (z : ℤ) : List Char :=
  if z < 0 then
    let n := z.natAbs
    if n = 0 then ['0']
    else '-' :: natToCharsAux n n []
  else
    let n := z.natAbs
    if n = 0 then ['0']
    else natToCharsAux n n []

instance : DensePolyParsable ℕ where
  parse cs := parseNatChars cs

instance : DensePolyParsable ℤ where
  parse cs := parseIntChars cs

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

def ratToChars (q : ℚ) : List Char :=
  if q.den = 1 then intToChars q.num
  else intToChars q.num ++ ['/'] ++ natToChars q.den

instance : DensePolyParsable ℚ where
  parse cs := parseRatChars cs

instance {n : ℕ} [NeZero n] : DensePolyParsable (ZMod n) where
  parse cs := (String.ofList cs).toInt?.map (fun x => (x : ZMod n))

/-- A typeclass for types whose elements can be formatted as a list of characters for polynomial coefficients. -/
class DensePolyToChars (R : Type _) where
  toChars : R → List Char

instance : DensePolyToChars ℕ where
  toChars := natToChars

instance : DensePolyToChars ℤ where
  toChars := intToChars

instance : DensePolyToChars ℚ where
  toChars := ratToChars

instance {n : ℕ} [NeZero n] : DensePolyToChars (ZMod n) where
  toChars x := natToChars x.val

/--
Formats a monomial with degree `d` and coefficient `c` as a `List Char`.
Handles "1" and "-1" intuitively based on `DensePolyToChars R`.
-/
def monomialToChars {R : Type _} [DecidableEq R] [Zero R] [DensePolyToChars R] (d : ℕ) (c : R) : List Char :=
  if c = 0 then
    ['0']
  else if d = 0 then
    DensePolyToChars.toChars c
  else
    let s := DensePolyToChars.toChars c
    let pfx := if s == ['1'] then [] else if s == ['-', '1'] then ['-'] else s ++ ['*']
    let sfx := if d = 1 then ['x'] else ['x', '^'] ++ natToChars d
    pfx ++ sfx

/--
Parses a monomial list of characters into its degree and coefficient.
Returns `none` if the string cannot be parsed.
Supported coefficients: `ℕ`, `ℤ`, `ℚ`, and `ZMod n`.
-/


instance {n : ℕ} [NeZero n] : ToString (ZMod n) where
  toString x := toString x.val

end Azurite.DensePoly
