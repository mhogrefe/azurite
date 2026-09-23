/-
  **Dedicated arithmetic in the cyclotomic ring `CycT n p k`** — Phase D of
  `docs/aprcl_implementation_plan.md`.

  The generic `AzPolyMod` multiplication reduces the product polynomial modulo
  `Φ_{p^k}` by polynomial division, which for a modulus with coefficients in
  `{0, 1}` wastes more than half of the time in coefficient multiplications.
  Here the reduction is additive (`reduceCyc`): with `m = (p−1)p^(k−1)` and
  `P = p^(k−1)`, a monomial `x^j` reduces via `x^(p^k) = 1` to `x^l`, `l = j mod
  p^k`, and for `l ≥ m` via `Σ_{i<p} x^(iP) = 0` to `−Σ_{i<p−1} x^((l mod P) + iP)`.
  So the coefficient of `x^i` (`i < m`) in the reduction is
  `Σ_{j ≡ i} c_j − Σ_{j : m ≤ j mod p^k, j ≡ i (mod P)} c_j` — additions only.
  `cycMul` is the raw polynomial product followed by `reduceCyc`; the wrapper
  type `CycF` carries `cycMul` as its multiplication and squaring so that the
  generic sliding-window exponentiation (`cycPow`) uses it.  Correctness
  (`cycMul_eq`, `cycPow_eq`) is in `Azurite/AzPolyMod/Equiv/CycArith.lean`.
-/
import Azurite.AzPolyMod.Cyclotomic
import Azurite.Algorithm.SlidingWindowPowAzNat

namespace Azurite

namespace AzPolyMod

open _root_.Azurite.AzPolynomial

variable (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)]

/-- **Additive reduction modulo `Φ_{p^k}`** of a polynomial given by its coefficients. -/
def reduceCyc (c : AzPolynomial (AzZMod n)) : CycT n p k :=
  let m := (p - 1) * p ^ (k - 1)
  let P := p ^ (k - 1)
  let N := c.coeffs.size
  ofCoeffFn m fun i =>
    (∑ j ∈ (Finset.range N).filter (fun j => j % p ^ k = i), c.coeff j)
      - ∑ j ∈ (Finset.range N).filter (fun j => m ≤ j % p ^ k ∧ j % p ^ k % P = i % P), c.coeff j

/-- **Multiplication with additive `Φ`-reduction.** -/
def cycMul (a b : CycT n p k) : CycT n p k := reduceCyc n p k (a.val * b.val)

/-- **The wrapper type** whose ring operations are the dedicated ones. -/
def CycF (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)] := CycT n p k

/-- Into the wrapper. -/
def toF (a : CycT n p k) : CycF n p k := a

/-- Out of the wrapper. -/
def ofF (a : CycF n p k) : CycT n p k := a

instance : Mul (CycF n p k) := ⟨fun a b => cycMul n p k (ofF n p k a) (ofF n p k b)⟩
instance : One (CycF n p k) := ⟨toF n p k 1⟩
instance : Pow (CycF n p k) ℕ := ⟨fun a e => toF n p k (ofF n p k a ^ e)⟩
instance : Azurite.Square (CycF n p k) where
  square a := a * a
  square_eq _ := rfl

/-- **The `u`-th power in `CycT` with the dedicated multiplication** (sliding window,
`AzNat` exponent). -/
def cycPow (a : CycT n p k) (u : AzNat) : CycT n p k :=
  ofF n p k (Azurite.slidingWindowPowAzNat (toF n p k a) u)

end AzPolyMod

end Azurite
