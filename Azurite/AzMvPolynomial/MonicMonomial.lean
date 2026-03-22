/-
  Monic monomials for multivariate polynomials.
-/
import Azurite.AzMvPolynomial.Var

namespace Azurite

/-- Monomial orderings for multivariate polynomials.
    - `Lex`: pure lexicographic (compare exponents left-to-right)
    - `Deglex`: total degree first, then lex to break ties
    - `Degrevlex`: total degree first, then reverse lex with flipped comparison -/
inductive MonomialOrder
  | Lex
  | Deglex
  | Degrevlex
  deriving DecidableEq, Repr

namespace MonomialOrder

/-- Lexicographic comparison of exponent vectors, starting at index `i`. -/
def lexCompareAux (a b : Vector ℕ n) (i : ℕ) : Ordering :=
  if h : i < n then
    match compare a[i] b[i] with
    | .eq => lexCompareAux a b (i + 1)
    | ord => ord
  else .eq
termination_by n - i

/-- Lexicographic comparison of exponent vectors. -/
def lexCompare (a b : Vector ℕ n) : Ordering := lexCompareAux a b 0

/-- Reverse lexicographic comparison with flipped result, starting at
    offset `i` from the end.
    The monomial with the *smaller* exponent at the rightmost differing
    position is considered *greater*. -/
def revlexCompareAux (a b : Vector ℕ n) (i : ℕ) : Ordering :=
  if h : i < n then
    let j := n - 1 - i
    match compare a[j] b[j] with
    | .eq => revlexCompareAux a b (i + 1)
    | .lt => .gt
    | .gt => .lt
  else .eq
termination_by n - i

/-- Reverse lexicographic comparison (right-to-left, flipped). -/
def revlexCompare (a b : Vector ℕ n) : Ordering := revlexCompareAux a b 0

/-- Total degree of an exponent vector. -/
def totalDeg (v : Vector ℕ n) : ℕ := v.toArray.foldl (· + ·) 0

/-- Compare exponent vectors according to the given monomial ordering. -/
def compareExponents (ord : MonomialOrder) (a b : Vector ℕ n) : Ordering :=
  match ord with
  | .Lex => lexCompare a b
  | .Deglex =>
    match compare (totalDeg a) (totalDeg b) with
    | .eq => lexCompare a b
    | r => r
  | .Degrevlex =>
    match compare (totalDeg a) (totalDeg b) with
    | .eq => revlexCompare a b
    | r => r

end MonomialOrder

/-- A monic monomial in `n` variables under a given `MonomialOrder` —
    a product of variables raised to nonneg integer powers, with no coefficient.
    Uses `Vector ℕ n` for efficient O(1) exponent access.

    For example, with variables x₀, x₁, x₂, the monomial x₀² x₂³
    has exponents `#v[2, 0, 3]`. -/
@[ext]
structure MonicMonomial (σ : Type _) (n : ℕ) [LinearOrder σ] [Var σ n]
    (ord : MonomialOrder := .Degrevlex) where
  /-- The exponent of each variable, indexed by position in `Fin n`. -/
  exponents : Vector ℕ n
  deriving DecidableEq

namespace MonicMonomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- The constant monomial `1` (all exponents zero). -/
def one : MonicMonomial σ n ord := ⟨Vector.replicate n 0⟩

/-- The monomial consisting of a single variable to the first power. -/
def ofVar (v : σ) : MonicMonomial σ n ord :=
  ⟨Vector.ofFn (fun i => if Var.toFin v = i then 1 else 0)⟩

/-- Get the exponent of a specific variable. -/
def exponent (m : MonicMonomial σ n ord) (v : σ) : ℕ :=
  m.exponents[Var.toFin v]

/-- The total degree of the monomial (sum of all exponents). -/
def totalDegree (m : MonicMonomial σ n ord) : ℕ :=
  MonomialOrder.totalDeg m.exponents

/-- Multiply two monic monomials (add exponents pointwise). -/
def mul (a b : MonicMonomial σ n ord) : MonicMonomial σ n ord :=
  ⟨Vector.ofFn (fun i => a.exponents[i] + b.exponents[i])⟩

instance : One (MonicMonomial σ n ord) := ⟨one⟩
instance : Mul (MonicMonomial σ n ord) := ⟨mul⟩

instance : Ord (MonicMonomial σ n ord) where
  compare a b := ord.compareExponents a.exponents b.exponents

@[simp] theorem one_exponents :
    (1 : MonicMonomial σ n ord).exponents = Vector.replicate n 0 := rfl
@[simp] theorem mul_exponents (a b : MonicMonomial σ n ord) :
    (a * b).exponents = Vector.ofFn (fun i => a.exponents[i] + b.exponents[i]) := rfl

theorem mul_assoc (a b c : MonicMonomial σ n ord) : a * b * c = a * (b * c) := by
  ext1; simp only [mul_exponents]; ext i hi; simp; omega

theorem one_mul (a : MonicMonomial σ n ord) : 1 * a = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_one (a : MonicMonomial σ n ord) : a * 1 = a := by
  ext1; simp only [mul_exponents, one_exponents]; ext i hi; simp

theorem mul_comm (a b : MonicMonomial σ n ord) : a * b = b * a := by
  ext1; simp only [mul_exponents]; ext i hi; simp [Nat.add_comm]

instance : CommMonoid (MonicMonomial σ n ord) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end MonicMonomial

end Azurite
