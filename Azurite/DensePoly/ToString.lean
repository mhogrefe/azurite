import Azurite.DensePoly.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

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

def intToChars (z : ℤ) : List Char :=
  if z < 0 then
    let n := z.natAbs
    if n = 0 then ['0']
    else '-' :: natToCharsAux n n []
  else
    let n := z.natAbs
    if n = 0 then ['0']
    else natToCharsAux n n []

def ratToChars (q : ℚ) : List Char :=
  if q.den = 1 then intToChars q.num
  else intToChars q.num ++ ['/'] ++ natToChars q.den

/-- A typeclass for types whose elements can be formatted as a list of characters for polynomial coefficients. -/
class DensePolyToChars (R : Type _) where
  toChars : R → List Char

instance : DensePolyToChars ℕ where
  toChars := natToChars

instance : DensePolyToChars ℤ where
  toChars := intToChars

instance : DensePolyToChars ℚ where
  toChars := ratToChars

def zmodToChars {n : ℕ} [NeZero n] (c : ZMod n) : List Char := natToChars c.val

instance {n : ℕ} [NeZero n] : DensePolyToChars (ZMod n) where
  toChars := zmodToChars

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

instance {n : ℕ} [NeZero n] : ToString (ZMod n) where
  toString x := toString x.val

def listEnum {α : Type _} (l : List α) : List (ℕ × α) :=
  let rec aux (acc : List (ℕ × α)) (n : ℕ) (rem : List α) : List (ℕ × α) :=
    match rem with
    | [] => acc.reverse
    | x :: xs => aux ((n, x) :: acc) (n + 1) xs
  aux [] 0 l

-- Removing DensePolyParsableValid constraint for pure toString computation
def toChars {R : Type _} [DecidableEq R] [Semiring R] [DensePolyToChars R] [DensePolyParsable R] (p : DensePoly R) : String :=
  if p = 0 then
    "0"
  else
    let coeffs : List R := p.coeffs.toList
    let indexed : List (ℕ × R) := listEnum coeffs
    let nonZero : List (ℕ × R) := indexed.filter (fun (_, c) => c ≠ 0)
    let monomials : List (List Char) := nonZero.map (fun (d, c) => monomialToChars d c)
    let reversed : List (List Char) := monomials.reverse
    let withSigns : List (List Char) := (listEnum reversed).map (fun (i, m) =>
      if i = 0 then m
      else match m with
      | '-' :: _ => m
      | _ => '+' :: m
    )
    let flat : List Char := withSigns.flatten
    String.ofList flat

instance {R : Type _} [DecidableEq R] [Semiring R] [DensePolyToChars R] [DensePolyParsable R] : ToString (DensePoly R) where
  toString := toChars

end Azurite.DensePoly
