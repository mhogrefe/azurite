import Azurite.DensePoly.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.DensePoly

/--
Formats a monomial with degree `d` and coefficient `c` as a `String`.
Handles "1" and "-1" intuitively based on `ToString R`.
-/
def monomialToString {R : Type _} [DecidableEq R] [Zero R] [ToString R] (d : ℕ) (c : R) : String :=
  if c = 0 then
    "0"
  else if d = 0 then
    toString c
  else
    let s := toString c
    let pfx := if s == "1" then "" else if s == "-1" then "-" else s ++ "*"
    let sfx := if d = 1 then "x" else s!"x^{d}"
    pfx ++ sfx

/-- A typeclass for types whose elements can be parsed from a monomial string coefficient. -/
class DensePolyParsable (R : Type _) where
  parse : String → Option R

instance : DensePolyParsable ℕ where
  parse s := s.toNat?

instance : DensePolyParsable ℤ where
  parse s := s.toInt?

def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [n] => n.toInt?.map (fun x : ℤ => (x : ℚ))
  | [n, d] => do
    let num ← n.toInt?
    let den ← d.toInt?
    if den == 0 then none
    else some ((num : ℚ) / (den : ℚ))
  | _ => none

instance : DensePolyParsable ℚ where
  parse s := parseRat s

instance {n : ℕ} [NeZero n] : DensePolyParsable (ZMod n) where
  parse s := s.toInt?.map (fun x => (x : ZMod n))

/--
Parses a monomial string (produced by `monomialToString`) into its degree and coefficient.
Returns `none` if the string cannot be parsed.
Supported coefficients: `ℕ`, `ℤ`, `ℚ`, and `ZMod n`.
-/
def parseMonomial {R : Type _} [DensePolyParsable R] (s : String) : Option (ℕ × R) :=
  match s.splitOn "x" with
  | [c_str] => do
    let c ← DensePolyParsable.parse c_str
    some (0, c)
  | [prefix_str, suffix_str] => do
    let d ← match suffix_str with
      | "" => some 1
      | _ =>
        if suffix_str.front == '^' then
          (suffix_str.drop 1).toNat?
        else
          none
    let c_str := match prefix_str with
      | "" => "1"
      | "-" => "-1"
      | _ =>
        if prefix_str.back == '*' then
          (prefix_str.toRawSubstring.dropRight 1).toString
        else
          "invalid"
    let c ← DensePolyParsable.parse c_str
    some (d, c)
  | _ => none

end Azurite.DensePoly
