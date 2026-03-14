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

def parseIntChars (cs : List Char) : Option ℤ :=
  match cs with
  | [] => none
  | '-' :: cs => (parseNatChars cs).map (fun n => - (n : ℤ))
  | _ => (parseNatChars cs).map (fun n => (n : ℤ))

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

instance : DensePolyParsable ℚ where
  parse cs := parseRatChars cs

instance {n : ℕ} [NeZero n] : DensePolyParsable (ZMod n) where
  parse cs := (parseIntChars cs).map (fun x => (x : ZMod n))

def parseMonomial_c_opt_prefix (cs : List Char) : List Char :=
  match cs with
  | [] => ['1']
  | ['-'] => ['-', '1']
  | x => if x.getLast? = some '*' then x.dropLast else []

/--
Parses a monomial list of characters into its degree and coefficient.
Returns `none` if the string cannot be parsed.
Supported coefficients: `ℕ`, `ℤ`, `ℚ`, and `ZMod n`.
-/
def parseMonomial {R : Type _} [DensePolyParsable R] (cs : List Char) : Option (ℕ × R) :=
  match cs.splitOn 'x' with
  | [c_cs] => do
    let c ← DensePolyParsable.parse c_cs
    some (0, c)
  | [prefix_cs, suffix_cs] => do
    let d ← match suffix_cs with
      | [] => some 1
      | '^' :: rest =>
        parseNatChars rest
      | _ => none
    let c_cs := parseMonomial_c_opt_prefix prefix_cs
    let c ← DensePolyParsable.parse c_cs
    some (d, c)
  | _ => none

def splitPolynomialChars (cs : List Char) : List (List Char) :=
  let rec aux (acc : List (List Char)) (current : List Char) (rem : List Char) : List (List Char) :=
    match rem with
    | [] => (current.reverse) :: acc
    | '+' :: xs => aux ((current.reverse) :: acc) [] xs
    | '-' :: xs =>
      if current = [] then
        aux acc ['-'] xs
      else
        aux ((current.reverse) :: acc) ['-'] xs
    | x :: xs => aux acc (x :: current) xs
  if cs = [] then []
  else (aux [] [] cs).reverse

def listMax (l : List ℕ) : ℕ := 
  l.foldl (fun maxVal x => if x > maxVal then x else maxVal) 0

def listToPoly {R : Type _} [DecidableEq R] [Semiring R] (l : List (ℕ × R)) : DensePoly R :=
  let maxDegree := listMax (l.map Prod.fst)
  let arr := Id.run do
    let mut a : Array R := Array.empty
    for d in [0:maxDegree+1] do
      let coeff := match l.find? (fun (d', _) => d' = d) with
                   | some (_, c) => c
                   | none => 0
      a := a.push coeff
    a
  normalize arr

def hasDuplicateExponents {R} (l : List (ℕ × R)) : Bool :=
  let exps := l.map Prod.fst
  exps.eraseDups.length ≠ exps.length

-- Note: Removing DensePolyParsableValid from variables here since it depends on lemmas,
-- and parseDensePoly doesn't strictly need it for computation unless we want to enforce it.
-- But since it's a Prop, maybe we don't need it. We will have to see.
def parseDensePoly {R : Type _} [DecidableEq R] [Semiring R] [DensePolyParsable R] (s : String) : Option (DensePoly R) :=
  if s = "0" then some 0
  else
    let parts := splitPolynomialChars s.toList
    let parsedParts := parts.map (fun p => parseMonomial (R := R) p)
    if parsedParts.any (fun x => x.isNone) then none
    else
      let unwrapped := parsedParts.filterMap id
      if hasDuplicateExponents unwrapped then none
      else some (listToPoly unwrapped)

end Azurite.DensePoly
