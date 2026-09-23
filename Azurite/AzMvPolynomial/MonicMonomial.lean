/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Monic monomials — Fin-indexed math core.

  `MonicMonomial n ord` carries no `Var` / `LinearOrder` typeclass — the
  variable type is fixed to `Fin n`.  Display (`toCharsWith`/`parseWith`)
  factors through an explicit `[ParsableVar F n]` display type parameter.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Vector.Defs
import Azurite.AzMvPolynomial.Var
import Azurite.AzMvPolynomial.MonomialOrder

namespace Azurite

/-- Monic monomial in `n` variables — product of variables raised to nonneg
    integer powers, with no coefficient.  Exponents are stored as a
    `Vector ℕ n` for O(1) access.  The variable type is fixed to `Fin n`;
    naming is a display-layer concern. -/
@[ext]
structure MonicMonomial (n : ℕ) (ord : MonomialOrder := .Degrevlex) where
  /-- The exponent of each variable, indexed by position in `Fin n`. -/
  exponents : Vector ℕ n
  deriving DecidableEq

namespace MonicMonomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The constant monomial `1` (all exponents zero). -/
def one : MonicMonomial n ord := ⟨Vector.replicate n 0⟩

/-- The monomial consisting of a single variable to the first power. -/
def ofVar (i : Fin n) : MonicMonomial n ord :=
  ⟨Vector.ofFn (fun j => if i = j then 1 else 0)⟩

/-- Get the exponent of a specific variable. -/
def exponent (m : MonicMonomial n ord) (i : Fin n) : ℕ :=
  m.exponents[i]

/-- The total degree of the monomial (sum of all exponents). -/
def totalDegree (m : MonicMonomial n ord) : ℕ :=
  MonomialOrder.totalDeg m.exponents

/-- Evaluate a monic monomial at a point given by `f : Fin n → R`.
    Computes the product `∏ i, f i ^ exp_i`. -/
def eval {R : Type _} [CommMonoid R] (m : MonicMonomial n ord) (f : Fin n → R) : R :=
  Finset.univ.prod (fun i : Fin n => f i ^ m.exponents[i])

/-- Rename variables via a map `f : Fin n → Fin n₂`.
    Each exponent at source index `i` is added to the target index `f i`.
    Non-injective maps merge exponents. -/
def rename {n₂ : ℕ} (m : MonicMonomial n ord) (f : Fin n → Fin n₂)
    (ord₂ : MonomialOrder := ord) : MonicMonomial n₂ ord₂ :=
  ⟨Vector.ofFn (fun j : Fin n₂ =>
    Finset.univ.sum (fun i : Fin n =>
      if f i = j then m.exponents[i] else 0))⟩

/-- Multiply two monic monomials (add exponents pointwise). -/
def mul (a b : MonicMonomial n ord) : MonicMonomial n ord :=
  ⟨Vector.ofFn (fun i => a.exponents[i] + b.exponents[i])⟩

instance : One (MonicMonomial n ord) := ⟨one⟩
instance : Mul (MonicMonomial n ord) := ⟨mul⟩

instance instOrdMonicMonomial : Ord (MonicMonomial n ord) where
  compare a b := ord.compareExponents a.exponents b.exponents

@[simp] theorem one_exponents :
    (1 : MonicMonomial n ord).exponents = Vector.replicate n 0 := rfl
@[simp] theorem mul_exponents (a b : MonicMonomial n ord) :
    (a * b).exponents = Vector.ofFn (fun i => a.exponents[i] + b.exponents[i]) := rfl

theorem mul_assoc (a b c : MonicMonomial n ord) : a * b * c = a * (b * c) := by
  ext1; simp only [mul_exponents]; ext i hi; simp; omega

theorem one_mul (a : MonicMonomial n ord) : 1 * a = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_one (a : MonicMonomial n ord) : a * 1 = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_comm (a b : MonicMonomial n ord) : a * b = b * a := by
  ext1; simp only [mul_exponents]; ext i hi; simp [Nat.add_comm]

instance instCommMonoidMonicMonomial : CommMonoid (MonicMonomial n ord) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Convert a monic monomial to use a different monomial ordering.
    The exponent vector is unchanged. -/
def withOrder (m : MonicMonomial n ord) (ord' : MonomialOrder) :
    MonicMonomial n ord' :=
  ⟨m.exponents⟩

@[simp] theorem withOrder_exponents (m : MonicMonomial n ord) (ord' : MonomialOrder) :
    (m.withOrder ord').exponents = m.exponents := rfl

/-! ### Display layer: parameterized over a display type `F`

    The math core above does not reference `Var` / `ParsableVar`.  Displaying
    a monomial requires a choice of naming scheme, which is captured by a
    `[ParsableVar F n]` instance on some display type `F`.  The default
    display uses `IndexedVar n` (prints `x₀, x₁, …`).
-/

section Display

variable (F : Type _) [LinearOrder F] [pv : ParsableVar F n]

/-- Convert a monic monomial to a list of characters using the display
    naming scheme carried by `F`.  Variables with exponent 0 are omitted;
    exponent 1 is implicit; `^e` is appended for higher exponents.  The
    all-zero monomial produces the empty list. -/
def toCharsWith (m : MonicMonomial n ord) : List Char :=
  let parts : List (List Char) := (List.finRange n).filterMap fun i =>
    let e := m.exponents[i]
    if e = 0 then none
    else
      let varChars := pv.toChars (pv.ofFin i)
      if e = 1 then some varChars
      else some (varChars ++ '^' :: natToChars e)
  List.intercalate ['*'] parts

/-- Parse a single factor like `x` or `x^3`, updating the exponent vector.  -/
def parseFactorWith (factor : List Char) (exps : Vector ℕ n) :
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
def parseFactorListWith : List (List Char) → Vector ℕ n → Option (Vector ℕ n)
  | [], exps => some exps
  | f :: fs, exps => match parseFactorWith F f exps with
    | some exps' => parseFactorListWith fs exps'
    | none => none

/-- Parse a character list (e.g. `x₀*x₁^2*x₂`) into a monic monomial using
    the naming scheme `F`.  Variables may appear in any order.  Duplicate
    variables are rejected.  Empty input produces the identity monomial. -/
def parseWith (cs : List Char) : Option (MonicMonomial n ord) :=
  if cs.isEmpty then some ⟨Vector.replicate n 0⟩
  else match parseFactorListWith F (cs.splitOn '*') (Vector.replicate n 0) with
    | some exps => some ⟨exps⟩
    | none => none

end Display

/-! ### Default display: uses `IndexedVar n` (`x₀, x₁, …`) -/

/-- Default `toChars`: uses `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def toChars (m : MonicMonomial n ord) : List Char :=
  m.toCharsWith (IndexedVar n)

/-- Default `parse`: accepts the `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def parse (cs : List Char) : Option (MonicMonomial n ord) :=
  parseWith (IndexedVar n) cs

instance : ToString (MonicMonomial n ord) where
  toString m := String.ofList m.toChars

instance : Repr (MonicMonomial n ord) where
  reprPrec m _ := toString m

end MonicMonomial

/-! ### Round-trip examples at `IndexedVar` -/

section MonicMonomialGuards

private def mmN (v : Vector ℕ 3) : MonicMonomial 3 := ⟨v⟩

-- `toChars` with default (`IndexedVar`) display
#guard (mmN (Vector.mk #[1, 0, 0] rfl)).toChars == "x₀".toList
#guard (mmN (Vector.mk #[2, 0, 0] rfl)).toChars == "x₀^2".toList
#guard (mmN (Vector.mk #[1, 1, 0] rfl)).toChars == "x₀*x₁".toList
#guard (mmN (Vector.mk #[0, 0, 0] rfl)).toChars == "".toList

-- `toCharsWith (AbcVar 3)` — same underlying Fin-indexed monomial,
-- different printing scheme (requires `Fact (3 ≤ 26)` for `AbcVar`).
instance : Fact (3 ≤ 26) := ⟨by omega⟩
#guard (mmN (Vector.mk #[1, 0, 0] rfl)).toCharsWith (AbcVar 3) == "a".toList
#guard (mmN (Vector.mk #[2, 0, 3] rfl)).toCharsWith (AbcVar 3) == "a^2*c^3".toList

-- `parseWith` round-trip
#guard MonicMonomial.parseWith (n := 3) (ord := .Degrevlex) (AbcVar 3) "a".toList
    == some (mmN (Vector.mk #[1, 0, 0] rfl))
#guard MonicMonomial.parseWith (n := 3) (ord := .Degrevlex) (AbcVar 3) "c*a".toList
    == some (mmN (Vector.mk #[1, 0, 1] rfl))

-- default `parse` uses `IndexedVar`
#guard MonicMonomial.parse (n := 3) (ord := .Degrevlex) "x₀*x₂^3".toList
    == some (mmN (Vector.mk #[1, 0, 3] rfl))

end MonicMonomialGuards

end Azurite
