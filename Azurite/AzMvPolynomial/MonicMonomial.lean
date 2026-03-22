/-
  Monic monomials for multivariate polynomials.
-/
import Azurite.AzMvPolynomial.Var

namespace Azurite

/-- A monic monomial in `n` variables — a product of variables raised to
    nonneg integer powers, with no coefficient.
    Uses `Vector ℕ n` for efficient O(1) exponent access.

    For example, with variables x₀, x₁, x₂, the monomial x₀² x₂³
    has exponents `#v[2, 0, 3]`. -/
@[ext]
structure MonicMonomial (σ : Type _) (n : ℕ) [LinearOrder σ] [Var σ n] where
  /-- The exponent of each variable, indexed by position in `Fin n`. -/
  exponents : Vector ℕ n
  deriving DecidableEq

namespace MonicMonomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]

/-- The constant monomial `1` (all exponents zero). -/
def one : MonicMonomial σ n := ⟨Vector.replicate n 0⟩

/-- The monomial consisting of a single variable to the first power. -/
def ofVar (v : σ) : MonicMonomial σ n :=
  ⟨Vector.ofFn (fun i => if Var.toFin v = i then 1 else 0)⟩

/-- Get the exponent of a specific variable. -/
def exponent (m : MonicMonomial σ n) (v : σ) : ℕ :=
  m.exponents[Var.toFin v]

/-- The total degree of the monomial (sum of all exponents). -/
def totalDegree (m : MonicMonomial σ n) : ℕ :=
  m.exponents.toArray.foldl (· + ·) 0

/-- Multiply two monic monomials (add exponents pointwise). -/
def mul (a b : MonicMonomial σ n) : MonicMonomial σ n :=
  ⟨Vector.ofFn (fun i => a.exponents[i] + b.exponents[i])⟩

instance : One (MonicMonomial σ n) := ⟨one⟩
instance : Mul (MonicMonomial σ n) := ⟨mul⟩

@[simp] theorem one_exponents : (1 : MonicMonomial σ n).exponents = Vector.replicate n 0 := rfl
@[simp] theorem mul_exponents (a b : MonicMonomial σ n) :
    (a * b).exponents = Vector.ofFn (fun i => a.exponents[i] + b.exponents[i]) := rfl

theorem mul_assoc (a b c : MonicMonomial σ n) : a * b * c = a * (b * c) := by
  ext1; simp only [mul_exponents]; ext i hi; simp; omega

theorem one_mul (a : MonicMonomial σ n) : 1 * a = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_one (a : MonicMonomial σ n) : a * 1 = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_comm (a b : MonicMonomial σ n) : a * b = b * a := by
  ext1; simp only [mul_exponents]; ext i hi; simp [Nat.add_comm]

instance : CommMonoid (MonicMonomial σ n) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end MonicMonomial

end Azurite
