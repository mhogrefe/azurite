import Azurite.AzPolynomial.DivModByMonic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.ToString
import Azurite.Algorithm.SlidingWindowPow
import Azurite.Algorithm.SlidingWindowPowAzNat
import Azurite.AzZMod.Instances
import Azurite.AzMvPolynomial.ParsableCoeff.AzZMod

/-!
# `AzPolyMod f` — the quotient ring `R[x] / (f)` for a monic `f`

`AzPolyMod f` is the computational analogue of [`AzZMod`](../AzZMod/Basic.lean)
(= `ℤ / m`), with the modulus a **monic** polynomial `f : AzPolynomial R` in place
of an `AzNat`.  An element is a polynomial `val` reduced modulo `f`, i.e. of
degree strictly below `deg f`.

The reduction primitive is
[`modByMonic`](../AzPolynomial/DivModByMonic.lean), the field-free division-by-a-
monic-polynomial algorithm (the polynomial `AzNat.mod`).  Because that primitive
always returns a remainder of size below `f` (for any nonzero `f`), the reduced
invariant `isReduced` is establishable without a monic hypothesis — exactly as
`AzZMod`'s `isLt` uses `Nat.mod_lt` — so the operations are total in `f` and are
correct when `f` is monic.

## Phase status

This is **Phase 1**: the type, the reduction constructor `ofPoly`, and the ring
*operations* (`Zero`/`One`/`Neg`/`Add`/`Sub`/`Mul`/`Pow`) as **data only**, with
`#guard` tests over `AzInt` and `AzZMod`.  The `CommRing` **laws** and the ring
isomorphism `AzPolyMod f ≃+* AdjoinRoot f` (`Polynomial R ⧸ span {f}`), which need
the monic hypothesis, are deferred to Phase 2, mirroring how `AzZMod` was built.
-/

namespace Azurite

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- An element of `R[x] / (f)`: a representative polynomial `val` reduced modulo
the (intended monic) polynomial `f`.

`isReduced` records that `val` has size — hence degree — below `f`, except in the
degenerate `f = 0` case (where no nonzero degree bound exists); the disjunct keeps
the type total in `f` while pinning the canonical reduced representative for every
nonzero `f`. -/
structure AzPolyMod (f : AzPolynomial R) where
  /-- The reduced representative polynomial. -/
  val : AzPolynomial R
  /-- Canonicity: `val` is reduced modulo `f` (degree below `deg f`), or `f = 0`. -/
  isReduced : val.coeffs.size < f.coeffs.size ∨ f.coeffs.size = 0
deriving DecidableEq

namespace AzPolyMod

variable {f : AzPolynomial R}

omit [DecidableEq R] in
@[ext] theorem ext {a b : AzPolyMod f} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

open AzPolynomial in
/-- The canonical `isReduced` witness for the reduction `modByMonic p f`, for any
`f` (monic or not). -/
theorem modByMonic_isReduced (p : AzPolynomial R) :
    (AzPolynomial.modByMonic p f).coeffs.size < f.coeffs.size ∨ f.coeffs.size = 0 := by
  by_cases hf : f.coeffs.size = 0
  · exact Or.inr hf
  · exact Or.inl (AzPolynomial.modByMonic_coeffs_size_lt p f (Nat.pos_of_ne_zero hf))

omit [DecidableEq R] in
/-- `0` (as a reduced polynomial) is reduced modulo any `f`. -/
theorem zero_isReduced :
    (0 : AzPolynomial R).coeffs.size < f.coeffs.size ∨ f.coeffs.size = 0 := by
  by_cases hf : f.coeffs.size = 0
  · exact Or.inr hf
  · exact Or.inl (by rw [AzPolynomial.coeffs_zero, Array.size_empty]; exact Nat.pos_of_ne_zero hf)

/-- Reduce an arbitrary polynomial `p` into `R[x] / (f)` (the class of `p`). -/
def ofPoly (p : AzPolynomial R) : AzPolyMod f :=
  ⟨AzPolynomial.modByMonic p f, modByMonic_isReduced p⟩

/-- The representative polynomial of a class. -/
def toPoly (a : AzPolyMod f) : AzPolynomial R := a.val

/-- The image of a coefficient `c : R` in `R[x] / (f)` (the class of the constant
polynomial `C c`). -/
def ofCoeff (c : R) : AzPolyMod f := ofPoly (AzPolynomial.C c)

instance : Zero (AzPolyMod f) := ⟨⟨0, zero_isReduced⟩⟩
instance : One (AzPolyMod f) := ⟨ofPoly 1⟩
instance : Inhabited (AzPolyMod f) := ⟨0⟩

/-- **Negation** in `R[x] / (f)`: negate the representative (degree unchanged, so
still reduced — routed through `ofPoly`, which short-circuits for an already
reduced input). -/
def neg (a : AzPolyMod f) : AzPolyMod f := ofPoly (-a.val)

instance : Neg (AzPolyMod f) := ⟨neg⟩

/-- **Addition** in `R[x] / (f)`: add representatives (degrees do not grow). -/
def add (a b : AzPolyMod f) : AzPolyMod f := ofPoly (a.val + b.val)

instance : Add (AzPolyMod f) := ⟨add⟩

/-- **Subtraction** in `R[x] / (f)`. -/
def sub (a b : AzPolyMod f) : AzPolyMod f := ofPoly (a.val - b.val)

instance : Sub (AzPolyMod f) := ⟨sub⟩

/-- **Multiplication** in `R[x] / (f)`: multiply representatives, then reduce the
(possibly higher-degree) product back modulo `f`. -/
def mul (a b : AzPolyMod f) : AzPolyMod f := ofPoly (a.val * b.val)

instance : Mul (AzPolyMod f) := ⟨mul⟩

/-- **Exponentiation** in `R[x] / (f)` via sliding-window exponentiation over the
quotient-ring operations, so `a ^ n` costs `O(log n)` reduced multiplications. -/
def pow (a : AzPolyMod f) (n : ℕ) : AzPolyMod f := Azurite.slidingWindowPow a n

instance : Pow (AzPolyMod f) ℕ := ⟨pow⟩

/-- **Exponentiation with an `AzNat` exponent** in `R[x] / (f)`.  The exponent is read at the
limb level (never through `AzNat.toNat`), so huge exponents like `p^k` (used in factorization)
stay limb-level.  Coexists with the `ℕ`-exponent `pow`; the `Monoid`/`CommRing` `npow` remains
`ℕ`-indexed. -/
def powAzNat (a : AzPolyMod f) (n : AzNat) : AzPolyMod f := Azurite.slidingWindowPowAzNat a n

instance : Pow (AzPolyMod f) AzNat := ⟨powAzNat⟩

/-- Render the reduced representative of a class as a string (for tests). -/
def render {R : Type _} [CommRing R] [DecidableEq R] [NeZero (1 : R)]
    [ParsableCoeff R] {f : AzPolynomial R} (a : AzPolyMod f) : String :=
  AzPolynomial.toChars a.val

end AzPolyMod

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolyMod Azurite.AzPolynomial

/-! ### Over `AzInt`, modulo `x² + 1` (so `x² ≡ -1`) -/

private def fI : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) "x^2+1").get!
private def pI (s : String) : AzPolyMod fI := ofPoly (parseAzPolynomial (R := AzInt) s).get!

-- Reduction of higher powers: `x² ≡ -1`, `x³ ≡ -x`.
#guard render (pI "x^2") == "-1"
#guard render (pI "x^3") == "-x"
-- A multiplication that genuinely wraps: `x · x = x² ≡ -1` (product degree ≥ deg f).
#guard render ((pI "x") * (pI "x")) == "-1"
-- `(x+2)(x+3) = x²+5x+6 ≡ 5x+5`.
#guard render ((pI "x+2") * (pI "x+3")) == "5*x+5"
-- Addition stays reduced: `(x+2)+(x+3) = 2x+5`.
#guard render ((pI "x+2") + (pI "x+3")) == "2*x+5"
-- Powers cycle: `x³ ≡ -x`, `x⁴ ≡ 1`.
#guard render ((pI "x") ^ 3) == "-x"
#guard render ((pI "x") ^ 4) == "1"

/-! ### Over `AzInt`, modulo `x³ - x - 1` (so `x³ ≡ x + 1`) -/

private def fC : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) "x^3-x-1").get!
private def qC (s : String) : AzPolyMod fC := ofPoly (parseAzPolynomial (R := AzInt) s).get!

#guard render (qC "x^3") == "x+1"
#guard render (qC "x^4") == "x^2+x"
-- Wrapping multiplication: `x² · x² = x⁴ ≡ x² + x`.
#guard render ((qC "x^2") * (qC "x^2")) == "x^2+x"
#guard render ((qC "x^2+1") + (qC "x^2+x")) == "2*x^2+x+1"

/-! ### Over `AzZMod 7` (prime field), modulo `x² + 1` (so `x² ≡ 6`) -/

private instance azPolyMod_fact_lt_7 : Fact (1 < (AzNat.ofNat 7).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private def f7 : AzPolynomial (AzZMod (AzNat.ofNat 7)) :=
  (parseAzPolynomial (R := AzZMod (AzNat.ofNat 7)) "x^2+1").get!
private def r7 (s : String) : AzPolyMod f7 :=
  ofPoly (parseAzPolynomial (R := AzZMod (AzNat.ofNat 7)) s).get!

-- `x² ≡ -1 ≡ 6 (mod 7)`; the wrapping product `x·x` reduces the same way.
#guard render (r7 "x^2") == "6"
#guard render ((r7 "x") * (r7 "x")) == "6"
#guard render (r7 "x^3") == "6*x"
-- Coefficients reduce mod 7 too: `(3x+4)+(5x+6) = 8x+10 ≡ x+3`.
#guard render ((r7 "3*x+4") + (r7 "5*x+6")) == "x+3"
-- `x⁴ = (x²)² ≡ (-1)² ≡ 1`.
#guard render ((r7 "x") ^ 4) == "1"

/-! #### Very large (`AzNat`) exponents — limb-level, `x^n` has period 4 (`x² ≡ -1`)

The exponents below are 40-to-48-digit numbers; `x ^ (N : AzNat)` reads `N`'s bits at the limb
level (never through `AzNat.toNat`), so these `#guard`s elaborate instantly.  Each `N`'s residue
mod `4` is pinned by its last two digits, giving a clean `1`/`x`/`6`/`6*x` (`x⁰`/`x¹`/`x²`/`x³`). -/

-- `…00` ⟹ `N ≡ 0 (mod 4)` ⟹ `x^N = 1`.
#guard render ((r7 "x") ^ (AzNat.parse "1234567890123456789012345678901234567800").get!) == "1"
-- `…13` ⟹ `N ≡ 1` ⟹ `x`.
#guard render ((r7 "x") ^ (AzNat.parse "1234567890123456789012345678901234567813").get!) == "x"
-- `…22` ⟹ `N ≡ 2` ⟹ `x² ≡ 6`.
#guard render ((r7 "x") ^ (AzNat.parse "1234567890123456789012345678901234567822").get!) == "6"
-- `…31` ⟹ `N ≡ 3` ⟹ `x³ ≡ 6x`.
#guard render ((r7 "x") ^ (AzNat.parse "1234567890123456789012345678901234567831").get!) == "6*x"
-- A `p^k`-style exponent: `3^100` (48 digits, `≡ (-1)^100 = 1 (mod 4)`) ⟹ `x`.
#guard render ((r7 "x") ^ ((AzNat.parse "3").get!.pow 100)) == "x"

/-! ### Over `AzZMod 8` (prime power, not a field), modulo `x² + 1` (so `x² ≡ 7`) -/

private instance azPolyMod_fact_lt_8 : Fact (1 < (AzNat.ofNat 8).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private def f8 : AzPolynomial (AzZMod (AzNat.ofNat 8)) :=
  (parseAzPolynomial (R := AzZMod (AzNat.ofNat 8)) "x^2+1").get!
private def r8 (s : String) : AzPolyMod f8 :=
  ofPoly (parseAzPolynomial (R := AzZMod (AzNat.ofNat 8)) s).get!

-- `x² ≡ -1 ≡ 7 (mod 8)`; `x³ ≡ 7x`.
#guard render (r8 "x^2") == "7"
#guard render (r8 "x^3") == "7*x"
-- Wrapping product with coefficient reduction: `(x+1)² = x²+2x+1 ≡ 2x+8 ≡ 2x`.
#guard render ((r8 "x+1") * (r8 "x+1")) == "2*x"
-- `(3x)(3x) = 9x² ≡ x² ≡ 7 (mod 8)` (both degree and coefficient wrap).
#guard render ((r8 "3*x") * (r8 "3*x")) == "7"

end Tests
