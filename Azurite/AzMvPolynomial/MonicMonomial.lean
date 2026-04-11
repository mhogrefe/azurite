/-
  Monic monomials for multivariate polynomials.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Vector.Defs
import Azurite.AzMvPolynomial.New.Var
import Azurite.AzMvPolynomial.New.MonomialOrder

namespace Azurite

/-- A monic monomial in `n` variables under a given `MonomialOrder` —
    a product of variables raised to nonneg integer powers, with no coefficient.
    Uses `Vector ℕ n` for efficient O(1) exponent access.

    For example, with variables x₀, x₁, x₂, the monomial x₀² x₂³
    has exponents `#v[2, 0, 3]`. -/
@[ext]
structure MonicMonomial (σ : Type _) {n : ℕ} [LinearOrder σ] [Var σ n]
    (ord : MonomialOrder := .Degrevlex) where
  /-- The exponent of each variable, indexed by position in `Fin n`. -/
  exponents : Vector ℕ n
  deriving DecidableEq

namespace MonicMonomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- The constant monomial `1` (all exponents zero). -/
def one : MonicMonomial σ ord := ⟨Vector.replicate n 0⟩

/-- The monomial consisting of a single variable to the first power. -/
def ofVar (v : σ) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => if Var.toFin v = i then 1 else 0)⟩

/-- Get the exponent of a specific variable. -/
def exponent (m : MonicMonomial σ ord) (v : σ) : ℕ :=
  m.exponents[Var.toFin v]

/-- The total degree of the monomial (sum of all exponents). -/
def totalDegree (m : MonicMonomial σ ord) : ℕ :=
  MonomialOrder.totalDeg m.exponents

/-- Evaluate a monic monomial at a point given by `f : σ → R`.
    Computes the product `∏ i, f(var_i) ^ exp_i`. -/
def eval [CommMonoid R] [Var σ n] (m : MonicMonomial σ ord) (f : σ → R) : R :=
  Finset.univ.prod (fun i : Fin n => f (Var.ofFin i) ^ m.exponents[i])

/-- Rename variables via a map `f : σ₁ → σ₂`.
    Each exponent at source index `i` is added to the target index
    `Var.toFin (f (Var.ofFin i))`. Non-injective maps merge exponents:
    e.g., renaming both `x` and `y` to `z` in `x²y` yields `z³`. -/
def rename {σ₂ : Type _} {n₂ : ℕ} [LinearOrder σ₂] [v₁ : Var σ n] [v₂ : Var σ₂ n₂]
    (m : MonicMonomial σ ord) (f : σ → σ₂) (ord₂ : MonomialOrder := ord) :
    MonicMonomial σ₂ ord₂ :=
  ⟨Vector.ofFn (fun j : Fin n₂ =>
    Finset.univ.sum (fun i : Fin n =>
      if v₂.toFin (f (v₁.ofFin i)) = j then m.exponents[i] else 0))⟩


/-- Multiply two monic monomials (add exponents pointwise). -/
def mul (a b : MonicMonomial σ ord) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => a.exponents[i] + b.exponents[i])⟩

instance : One (MonicMonomial σ ord) := ⟨one⟩
instance : Mul (MonicMonomial σ ord) := ⟨mul⟩

instance : Ord (MonicMonomial σ ord) where
  compare a b := ord.compareExponents a.exponents b.exponents

@[simp] theorem one_exponents :
    (1 : MonicMonomial σ ord).exponents = Vector.replicate n 0 := rfl
@[simp] theorem mul_exponents (a b : MonicMonomial σ ord) :
    (a * b).exponents = Vector.ofFn (fun i => a.exponents[i] + b.exponents[i]) := rfl

theorem mul_assoc (a b c : MonicMonomial σ ord) : a * b * c = a * (b * c) := by
  ext1; simp only [mul_exponents]; ext i hi; simp; omega

theorem one_mul (a : MonicMonomial σ ord) : 1 * a = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_one (a : MonicMonomial σ ord) : a * 1 = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_comm (a b : MonicMonomial σ ord) : a * b = b * a := by
  ext1; simp only [mul_exponents]; ext i hi; simp [Nat.add_comm]

instance : CommMonoid (MonicMonomial σ ord) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Convert a monic monomial to use a different monomial ordering.
    The exponent vector is unchanged. -/
def withOrder (m : MonicMonomial σ ord) (ord' : MonomialOrder) :
    MonicMonomial σ ord' :=
  ⟨m.exponents⟩

@[simp] theorem withOrder_exponents (m : MonicMonomial σ ord) (ord' : MonomialOrder) :
    (m.withOrder ord').exponents = m.exponents := rfl

/-- Convert a monic monomial to a list of characters.
    Formats as `x₀*x₁^2*x₂` — variables with exponent 0 are omitted,
    exponent 1 is implicit, and `^e` is appended for higher exponents.
    The all-zero monomial (i.e. `1`) produces the empty list. -/
def toChars [pv : ParsableVar σ n] (m : MonicMonomial σ ord) : List Char :=
  let parts : List (List Char) := (List.finRange n).filterMap fun i =>
    let e := m.exponents[i]
    if e = 0 then none
    else
      let varChars := pv.toChars (pv.ofFin i)
      if e = 1 then some varChars
      else some (varChars ++ '^' :: natToChars e)
  List.intercalate ['*'] parts

instance [ParsableVar σ n] : ToString (MonicMonomial σ ord) where
  toString m := String.ofList m.toChars

instance [ParsableVar σ n] : Repr (MonicMonomial σ ord) where
  reprPrec m _ := toString m

/-- Parse a single factor like `x` or `x^3` into an exponent vector update.
    Uses explicit pattern matching for proof-friendliness. -/
def parseFactor [pv : ParsableVar σ n] (factor : List Char) (exps : Vector ℕ n) :
    Option (Vector ℕ n) :=
  if factor.isEmpty then none
  else match factor.splitOn '^' with
    | [vp] => match pv.parseChars vp with
      | some v => let idx := pv.toFin v
        if exps.get idx ≠ 0 then none else some (exps.set idx.val 1 idx.isLt)
      | none => none
    | [vp, ep] => match parseNatChars ep with
      | some e => if e = 0 then none else match pv.parseChars vp with
        | some v => let idx := pv.toFin v
          if exps.get idx ≠ 0 then none else some (exps.set idx.val e idx.isLt)
        | none => none
      | none => none
    | _ => none

/-- Process a list of factors left-to-right, accumulating into an exponent vector. -/
def parseFactorList [ParsableVar σ n] :
    List (List Char) → Vector ℕ n → Option (Vector ℕ n)
  | [], exps => some exps
  | f :: fs, exps => match parseFactor (σ := σ) f exps with
    | some exps' => parseFactorList fs exps'
    | none => none

/-- Parse a character list in the format `x₀*x₁^2*x₂` into a monic monomial.
    Variables may appear in any order and are placed at their correct index
    via `ParsableVar.toFin`. Duplicate variables are rejected.
    An empty input produces the identity monomial (`1`). -/
def parse [ParsableVar σ n] (cs : List Char) : Option (MonicMonomial σ ord) :=
  if cs.isEmpty then some ⟨Vector.replicate n 0⟩
  else match parseFactorList (σ := σ) (cs.splitOn '*') (Vector.replicate n 0) with
    | some exps => some ⟨exps⟩
    | none => none

end MonicMonomial

section MonicMonomialGuards

-- Use AbcVar with 3 variables: a, b, c
instance : Fact (3 ≤ 26) := ⟨by omega⟩

private def mm (v : Vector ℕ 3) : MonicMonomial (AbcVar 3) := ⟨v⟩

-- toChars examples
#guard (mm (Vector.mk #[1, 0, 0] rfl)).toChars == "a".toList
#guard (mm (Vector.mk #[2, 0, 0] rfl)).toChars == "a^2".toList
#guard (mm (Vector.mk #[1, 1, 0] rfl)).toChars == "a*b".toList
#guard (mm (Vector.mk #[2, 0, 3] rfl)).toChars == "a^2*c^3".toList
#guard (mm (Vector.mk #[1, 2, 1] rfl)).toChars == "a*b^2*c".toList
#guard (mm (Vector.mk #[0, 0, 0] rfl)).toChars == "".toList

-- parse examples
#guard MonicMonomial.parse (σ := AbcVar 3) "a".toList == some (mm (Vector.mk #[1, 0, 0] rfl))
#guard MonicMonomial.parse (σ := AbcVar 3) "a^2".toList == some (mm (Vector.mk #[2, 0, 0] rfl))
#guard MonicMonomial.parse (σ := AbcVar 3) "a*b".toList == some (mm (Vector.mk #[1, 1, 0] rfl))
#guard MonicMonomial.parse (σ := AbcVar 3) "a^2*c^3".toList == some (mm (Vector.mk #[2, 0, 3] rfl))
#guard MonicMonomial.parse (σ := AbcVar 3) "c*a".toList == some (mm (Vector.mk #[1, 0, 1] rfl))
#guard MonicMonomial.parse (σ := AbcVar 3) "".toList == some (mm (Vector.mk #[0, 0, 0] rfl))

-- parse rejects invalid input
#guard MonicMonomial.parse (σ := AbcVar 3) "d".toList == (none : Option (MonicMonomial (AbcVar 3)))
#guard MonicMonomial.parse (σ := AbcVar 3) "a*a".toList == (none : Option (MonicMonomial (AbcVar 3)))
#guard MonicMonomial.parse (σ := AbcVar 3) "a^0".toList == (none : Option (MonicMonomial (AbcVar 3)))

end MonicMonomialGuards

end Azurite
