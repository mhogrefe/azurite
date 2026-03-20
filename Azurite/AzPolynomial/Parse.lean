import Azurite.AzPolynomial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.AzPolynomial

/-- A typeclass for types whose elements can be parsed from a monomial string coefficient. -/
class AzPolynomialParsable (R : Type _) where
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

instance : AzPolynomialParsable ℕ where
  parse cs := parseNatChars cs

instance : AzPolynomialParsable ℤ where
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

instance : AzPolynomialParsable ℚ where
  parse cs := parseRatChars cs

instance {n : ℕ} [NeZero n] : AzPolynomialParsable (ZMod n) where
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
def parseMonomial {R : Type _} [AzPolynomialParsable R] (cs : List Char) : Option (ℕ × R) :=
  match cs.splitOn 'x' with
  | [c_cs] => do
    let c ← AzPolynomialParsable.parse c_cs
    some (0, c)
  | [prefix_cs, suffix_cs] => do
    let d ← match suffix_cs with
      | [] => some 1
      | '^' :: rest =>
        parseNatChars rest
      | _ => none
    let c_cs := parseMonomial_c_opt_prefix prefix_cs
    let c ← AzPolynomialParsable.parse c_cs
    some (d, c)
  | _ => none

def splitPolynomialCharsAux (acc : List (List Char)) (current : List Char) (rem : List Char) : List (List Char) :=
  match rem with
  | [] => (current.reverse) :: acc
  | '+' :: xs => splitPolynomialCharsAux ((current.reverse) :: acc) [] xs
  | '-' :: xs =>
    if current = [] then
      splitPolynomialCharsAux acc ['-'] xs
    else
      splitPolynomialCharsAux ((current.reverse) :: acc) ['-'] xs
  | x :: xs => splitPolynomialCharsAux acc (x :: current) xs

def splitPolynomialChars (cs : List Char) : List (List Char) :=
  if cs = [] then []
  else (splitPolynomialCharsAux [] [] cs).reverse

def listMax (l : List ℕ) : ℕ := 
  l.foldl (fun maxVal x => if x > maxVal then x else maxVal) 0

def listToPoly {R : Type _} [DecidableEq R] [Semiring R] (l : List (ℕ × R)) : AzPolynomial R :=
  let maxDegree := listMax (l.map Prod.fst)
  let coeff := fun d => match l.find? (fun (d', _) => d' = d) with
                        | some (_, c) => c
                        | none => (0 : R)
  let arr := ((List.range (maxDegree + 1)).map coeff).toArray
  normalize arr

def hasDuplicateExponents {R} (l : List (ℕ × R)) : Bool :=
  let exps := l.map Prod.fst
  exps.eraseDups.length ≠ exps.length

-- Note: Removing AzPolynomialParsableValid from variables here since it depends on lemmas,
-- and parseAzPolynomial doesn't strictly need it for computation unless we want to enforce it.
-- But since it's a Prop, maybe we don't need it. We will have to see.
def parseAzPolynomial {R : Type _} [DecidableEq R] [Semiring R] [AzPolynomialParsable R] (s : String) : Option (AzPolynomial R) :=
  if s = "0" then some 0
  else
    let parts := splitPolynomialChars s.toList
    let parsedParts := parts.map (fun p => parseMonomial (R := R) p)
    if parsedParts.any (fun x => x.isNone) then none
    else
      let unwrapped := parsedParts.filterMap id
      if hasDuplicateExponents unwrapped then none
      else some (listToPoly unwrapped)

end Azurite.AzPolynomial
