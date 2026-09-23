/-
  **The computable quadratic ring `A = (ℤ/nℤ)[T]/(T² − uT − a)`** — Phase A2
  of the APR-CL implementation plan (`docs/aprcl_implementation_plan.md`).

  Elements are coordinate pairs `x₀ + x₁α` over `AzZMod n` (`QuadT n u a`),
  with the arithmetic of Remark (4.9) of the implementation paper:

  * `mul`: `(x₀ + x₁α)(y₀ + y₁α) = (x₀y₀ + a·x₁y₁) + (x₀y₁ + x₁y₀ + u·x₁y₁)α`,
    computed with the three-multiplication scheme `p₀ = x₀y₀`, `p₁ = x₁y₁`,
    `s = (x₀+x₁)(y₀+y₁)`, `z₀ = p₀ + a·p₁`, `z₁ = s − p₀ − p₁ + u·p₁`
    (the paper's `n ≡ 1`/`n ≡ 3 (mod 4)` schemes are the cases `u = 0`,
    `a = 1`; the multiplications by the small constants `u`, `a` are
    Phase-D targets);
  * `norm`: `N(x₀ + x₁α) = x₀² + u·x₀x₁ − a·x₁²`, `conj`: `ᾱ = u − α`;
  * `squareNormOne`: for `N(x) = 1`, `x² = (x₀s − 1) + (x₁s)α` with
    `s = u·x₁ + 2x₀` — two multiplications.  Packaged as the `Square`
    instance of the subtype `NormOne n u a` of norm-one elements, so the
    generic proven `slidingWindowPow` is the paper's "(3.6) with the
    squaring and multiplication in `A`" (Remark (4.8)); `powNormOne`.
  * `pow`: the general power (default squaring), for `α^(n+1)` in (4.4)(c2)
    — or via `alphaSq`, `α² = a + uα` of norm one, `α^(n+1) = (α²)^((n+1)/2)`.
  * `normOneCandidate m`: Remark (4.10), `(α + m)/(ᾱ + m) =
    ((m² + a) + (2m + u)α)/(m(m + u) − a)`, `none` when the denominator is
    not invertible (a composite verdict, `norm_one_denominator_isUnit`);
    the result's norm is *checked*, not assumed.
  * `tryInv`: the modular inverse with a gcd test (`none` = non-unit).

  Specifications in `Equiv/Quad.lean`, through the coordinate map into
  `QuadRing (ZMod n) u a` of `Impl_4_3.lean`.
-/
import Azurite.AzZMod.Instances
import Azurite.AzZMod.Inv
import Azurite.AzNat.InvMod
import Azurite.AzNat.Gcd
import Azurite.Algorithm.SlidingWindowPow
import Azurite.Algorithm.SlidingWindowPowAzNat

namespace Azurite

namespace AzZMod

variable {m : AzNat} [NeZero m.toNat]

/-- **Fallible modular inverse**: `some x⁻¹` if `gcd(x, m) = 1`, else `none`. -/
def tryInv (x : AzZMod m) : Option (AzZMod m) :=
  if AzNat.gcd x.val m = 1 then some (ofAzNat m (AzNat.invMod x.val m)) else none

/-- **`x₀ + x₁α ∈ (ℤ/mℤ)[T]/(T² − uT − a)`** as a coordinate pair. -/
@[ext] structure QuadT (m : AzNat) (u a : AzZMod m) where
  x₀ : AzZMod m
  x₁ : AzZMod m
deriving DecidableEq

namespace QuadT

variable {u a : AzZMod m}

/-- `α`. -/
def alpha : QuadT m u a := ⟨0, 1⟩

/-- Constants. -/
def const (c : AzZMod m) : QuadT m u a := ⟨c, 0⟩

instance : Zero (QuadT m u a) := ⟨⟨0, 0⟩⟩
instance : One (QuadT m u a) := ⟨⟨1, 0⟩⟩
instance : Inhabited (QuadT m u a) := ⟨0⟩

/-- Componentwise addition. -/
def add (x y : QuadT m u a) : QuadT m u a := ⟨x.x₀ + y.x₀, x.x₁ + y.x₁⟩
instance : Add (QuadT m u a) := ⟨add⟩

/-- Componentwise subtraction. -/
def sub (x y : QuadT m u a) : QuadT m u a := ⟨x.x₀ - y.x₀, x.x₁ - y.x₁⟩
instance : Sub (QuadT m u a) := ⟨sub⟩

/-- Negation. -/
def neg (x : QuadT m u a) : QuadT m u a := ⟨-x.x₀, -x.x₁⟩
instance : Neg (QuadT m u a) := ⟨neg⟩

/-- **The (4.9) product**, three big multiplications. -/
def mul (x y : QuadT m u a) : QuadT m u a :=
  let p₀ := x.x₀ * y.x₀
  let p₁ := x.x₁ * y.x₁
  let s := (x.x₀ + x.x₁) * (y.x₀ + y.x₁)
  ⟨p₀ + a * p₁, s - p₀ - p₁ + u * p₁⟩
instance : Mul (QuadT m u a) := ⟨mul⟩

/-- **The general power** (default squaring `x * x`). -/
def pow (x : QuadT m u a) (n : ℕ) : QuadT m u a := Azurite.slidingWindowPow x n
instance : Pow (QuadT m u a) ℕ := ⟨pow⟩

/-- The general power with an `AzNat` exponent (bits read at limb level). -/
def powAzNat (x : QuadT m u a) (n : AzNat) : QuadT m u a := Azurite.slidingWindowPowAzNat x n

/-- **The norm** `N(x₀ + x₁α) = x₀² + u·x₀x₁ − a·x₁²`. -/
def norm (x : QuadT m u a) : AzZMod m :=
  x.x₀ * x.x₀ + u * x.x₀ * x.x₁ - a * x.x₁ * x.x₁

/-- **The conjugate**: `x₀ + x₁ᾱ` with `ᾱ = u − α`, i.e. `(x₀ + u·x₁) − x₁α`. -/
def conj (x : QuadT m u a) : QuadT m u a := ⟨x.x₀ + u * x.x₁, -x.x₁⟩

/-- **Combined squaring for norm-one elements** (Remark (4.9)):
`s = u·x₁ + 2x₀`, `x² = (x₀s − 1) + (x₁s)α`. -/
def squareNormOne (x : QuadT m u a) : QuadT m u a :=
  let s := u * x.x₁ + x.x₀ + x.x₀
  ⟨x.x₀ * s - 1, x.x₁ * s⟩

/-- `α² = a + uα`, an element of norm one (for `a = 1`). -/
def alphaSq : QuadT m u a := ⟨a, u⟩

end QuadT

/-- **Norm-one elements** — the subtype on which the shortcut squaring is
a genuine `Square`. -/
def NormOne (m : AzNat) [NeZero m.toNat] (u a : AzZMod m) : Type :=
  {x : QuadT m u a // QuadT.norm x = 1}

namespace QuadT

variable {u a : AzZMod m}

/-- **The norm is multiplicative** (coordinate identity). -/
theorem norm_mul (x y : QuadT m u a) : norm (x * y) = norm x * norm y := by
  show norm (mul x y) = norm x * norm y
  simp only [norm, mul]
  ring

theorem norm_one : norm (1 : QuadT m u a) = 1 := by
  show norm ⟨1, 0⟩ = 1
  simp only [norm]
  ring

/-- **The shortcut squaring is the square on norm-one elements.** -/
theorem squareNormOne_eq (x : QuadT m u a) (h : norm x = 1) : squareNormOne x = x * x := by
  show squareNormOne x = mul x x
  simp only [norm] at h
  refine QuadT.ext ?_ ?_
  · simp only [squareNormOne, mul]
    linear_combination h
  · simp only [squareNormOne, mul]
    ring

/-- `α² = a + uα` has norm one when `a = 1`. -/
theorem norm_alphaSq_one : norm (alphaSq : QuadT m u 1) = 1 := by
  simp only [norm, alphaSq]
  ring

/-- **Remark (4.10)**: `(α + c)/(ᾱ + c) = ((c² + a) + (2c + u)α)/(c(c + u) − a)`,
`none` if the denominator is not invertible or the result is not of norm
one (neither happens for prime `m`). -/
def normOneCandidate (c : AzZMod m) : Option (NormOne m u a) :=
  match tryInv (c * (c + u) - a) with
  | none => none
  | some d =>
    let x : QuadT m u a := ⟨(c * c + a) * d, (c + c + u) * d⟩
    if h : norm x = 1 then some ⟨x, h⟩ else none

end QuadT

namespace NormOne

variable {u a : AzZMod m}

instance : One (NormOne m u a) := ⟨⟨1, QuadT.norm_one⟩⟩

instance : Mul (NormOne m u a) :=
  ⟨fun x y => ⟨x.1 * y.1, by rw [QuadT.norm_mul, x.2, y.2, one_mul]⟩⟩

/-- The shortcut squaring, a lawful `Square` on norm-one elements. -/
instance : Azurite.Square (NormOne m u a) where
  square x := ⟨QuadT.squareNormOne x.1, by
    rw [QuadT.squareNormOne_eq x.1 x.2, QuadT.norm_mul, x.2, one_mul]⟩
  square_eq x := Subtype.ext (QuadT.squareNormOne_eq x.1 x.2)

/-- **Powers of norm-one elements** by the sliding-window method with the
two-multiplication squaring (Remarks (4.8), (4.9)). -/
def pow (x : NormOne m u a) (n : ℕ) : NormOne m u a := Azurite.slidingWindowPow x n

/-- Powers of norm-one elements with an `AzNat` exponent. -/
def powAzNat (x : NormOne m u a) (n : AzNat) : NormOne m u a :=
  Azurite.slidingWindowPowAzNat x n

end NormOne

/-! ### Sanity guards -/

section Guards

private abbrev n101 : AzNat := AzNat.ofNat 101
private abbrev n103 : AzNat := AzNat.ofNat 103
private abbrev n15 : AzNat := AzNat.ofNat 15

-- `tryInv`
#guard tryInv (5 : AzZMod n101) = some 81
#guard tryInv (0 : AzZMod n101) = none
#guard tryInv (3 : AzZMod n15) = none
#guard tryInv (2 : AzZMod n15) = some 8

-- `n = 101 ≡ 1 (mod 4)`, `u = 0`, `a = 2` (a nonresidue): `α^(n+1) = N(α) = −a`
#guard (QuadT.alpha : QuadT n101 0 2) ^ 102 = QuadT.const (-2)
-- `n = 103 ≡ 3 (mod 4)`, `u = 1`, `a = 1`, `((u²+4)/n) = (5/103) = −1`: `α^(n+1) = −1`,
-- also via `(α²)^((n+1)/2)` with the norm-one squaring
#guard (QuadT.alpha : QuadT n103 1 1) ^ 104 = QuadT.const (-1)
#guard (NormOne.pow (⟨QuadT.alphaSq, QuadT.norm_alphaSq_one⟩ : NormOne n103 1 1) 52).1
  = QuadT.const (-1)
-- Remark (4.10): norm-one candidates, and Test (4.3)'s `x^(n+1) = 1` for prime `n`
#guard ((QuadT.normOneCandidate 1 : Option (NormOne n103 1 1)).map
  fun x => decide ((NormOne.pow x 104).1 = 1)) = some true
#guard ((QuadT.normOneCandidate 7 : Option (NormOne n101 0 2)).map
  fun x => decide ((NormOne.pow x 102).1 = 1)) = some true
#guard ((QuadT.normOneCandidate 3 : Option (NormOne n101 0 2)).map
  fun x => decide ((NormOne.pow x 51).1 = 1)) = some false

end Guards

end AzZMod

end Azurite
