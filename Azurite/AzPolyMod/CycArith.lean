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
  `cycMul` is the polynomial product over unreduced `AzNat` coefficients (one
  reduction modulo `n` per product coefficient instead of one per coefficient
  product) followed by `reduceCyc`; the wrapper type `CycF` carries `cycMul`
  as its multiplication and squaring so that the fixed-window exponentiation
  (`cycPow`, `windowPowAzNat`) uses it.  Correctness
  (`cycMul_eq`, `cycPow_eq`) is in `Azurite/AzPolyMod/Equiv/CycArith.lean`.
-/
import Azurite.AzPolyMod.Cyclotomic
import Azurite.Algorithm.SlidingWindowPowAzNat
import Azurite.Algorithm.WindowPowAzNat
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolyMod.Equiv.Cyclotomic

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

/-- Each coefficient reduced modulo `n` (once). -/
def reduceCoeffs (P : AzPolynomial AzNat) : AzPolynomial (AzZMod n) :=
  AzPolynomial.normalize (Array.ofFn fun i : Fin P.coeffs.size => AzZMod.ofAzNat n (P.coeff i))

/-- The coefficients lifted to `AzNat` (their canonical residues), for the lazy product. -/
def liftNat (a : CycT n p k) : AzPolynomial AzNat :=
  AzPolynomial.normalize (Array.ofFn fun i : Fin a.val.coeffs.size => (a.val.coeff i).val)

/-- **Multiplication with lazy coefficient reduction and additive `Φ`-reduction**: the
polynomial product is taken over unreduced `AzNat` coefficients, each of the `2m − 1`
product coefficients is reduced modulo `n` once, then `Φ` is reduced additively. -/
def cycMul (a b : CycT n p k) : CycT n p k :=
  reduceCyc n p k (reduceCoeffs n (liftNat n p k a * liftNat n p k b))

/-- The coefficient of `x^d` in the square of `Σ c_i x^i`: `2·Σ_{i<j, i+j=d} c_i c_j` plus
`c_{d/2}²` for even `d` (the `AzNat` fast squaring). -/
def coeffSq (c : ℕ → AzNat) (d : ℕ) : AzNat :=
  let t := ∑ x ∈ (Finset.antidiagonal d).filter (fun x => x.1 < x.2), c x.1 * c x.2
  t + t + (if d % 2 = 0 then Azurite.Square.square (c (d / 2)) else 0)

/-- **Symmetric squaring** of an `AzNat` polynomial: `m(m+1)/2` coefficient products. -/
def squareNat (P : AzPolynomial AzNat) : AzPolynomial AzNat :=
  AzPolynomial.normalize (Array.ofFn fun d : Fin (2 * P.coeffs.size - 1) => coeffSq P.coeff d)

open Finset in
/-- The symmetric-square identity on the antidiagonal: for `f` symmetric,
`Σ_{i+j=d} f i j = 2·Σ_{i<j} f i j + [d even]·f (d/2) (d/2)`. -/
theorem sum_antidiagonal_symm {M : Type _} [AddCommMonoid M] (f : ℕ → ℕ → M)
    (hf : ∀ i j, f i j = f j i) (d : ℕ) :
    ∑ x ∈ antidiagonal d, f x.1 x.2
      = (∑ x ∈ (antidiagonal d).filter (fun x => x.1 < x.2), f x.1 x.2)
        + (∑ x ∈ (antidiagonal d).filter (fun x => x.1 < x.2), f x.1 x.2)
        + (if d % 2 = 0 then f (d / 2) (d / 2) else 0) := by
  have hB : ∑ x ∈ (antidiagonal d).filter (fun x => ¬ x.1 < x.2), f x.1 x.2
      = (∑ x ∈ (antidiagonal d).filter (fun x => x.1 < x.2), f x.1 x.2)
        + (if d % 2 = 0 then f (d / 2) (d / 2) else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not ((antidiagonal d).filter (fun x => ¬ x.1 < x.2))
      (fun x => x.2 < x.1), Finset.filter_filter, Finset.filter_filter]
    congr 1
    · -- the `i > j` part is the swap of the `i < j` part
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hx ⊢
        omega
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hx ⊢
        omega
      · intro x _; rfl
      · intro x _; rfl
      · intro x _
        exact hf _ _
    · -- the diagonal
      by_cases hd : d % 2 = 0
      · rw [if_pos hd]
        rw [Finset.sum_eq_single (d / 2, d / 2)]
        · intro x hx hne
          exfalso
          simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
          apply hne
          ext <;> simp only <;> omega
        · intro h
          exfalso
          apply h
          simp only [Finset.mem_filter, Finset.mem_antidiagonal]
          omega
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro x hx
        exfalso
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        omega
  rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal d) (fun x => x.1 < x.2), hB, add_assoc]

/-- **The symmetric square is the product** (as `AzNat` polynomials). -/
theorem squareNat_eq_mul (P : AzPolynomial AzNat) : squareNat P = P * P := by
  rw [← toPoly_inj, toPoly_mul, squareNat, toPoly_normalize_ofFn _ (coeffSq P.coeff)]
  apply Polynomial.ext
  intro d
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_mul]
  simp only [Polynomial.coeff_C_mul_X_pow, coeff_toPoly_eq]
  rw [Finset.sum_ite_eq]
  have hvan : ∀ x ∈ Finset.antidiagonal d, 2 * P.coeffs.size - 1 ≤ d → P.coeff x.1 * P.coeff x.2 = 0 := by
    intro x hx hd
    rw [Finset.mem_antidiagonal] at hx
    rcases Nat.lt_or_ge x.1 P.coeffs.size with h1 | h1
    · rw [coeff_eq_zero_of_size_le P (by omega : P.coeffs.size ≤ x.2), mul_zero]
    · rw [coeff_eq_zero_of_size_le P h1, zero_mul]
  split_ifs with hd
  · rw [coeffSq, sum_antidiagonal_symm (fun i j => P.coeff i * P.coeff j) (fun i j => mul_comm _ _)]
    simp only [Azurite.Square.square_eq]
  · rw [Finset.mem_range, not_lt] at hd
    exact (Finset.sum_eq_zero fun x hx => hvan x hx hd).symm

/-- **Squaring with lazy reduction and additive `Φ`-reduction.** -/
def cycSquare (a : CycT n p k) : CycT n p k :=
  reduceCyc n p k (reduceCoeffs n (squareNat (liftNat n p k a)))

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
  square a := toF n p k (cycSquare n p k (ofF n p k a))
  square_eq a := by
    show cycSquare n p k (ofF n p k a) = cycMul n p k (ofF n p k a) (ofF n p k a)
    rw [cycSquare, cycMul, squareNat_eq_mul]

/-- **The `u`-th power in `CycT` with the dedicated multiplication** (sliding window,
`AzNat` exponent). -/
def cycPow (a : CycT n p k) (u : AzNat) : CycT n p k :=
  ofF n p k (Azurite.windowPowAzNat (toF n p k a) u)

end AzPolyMod

end Azurite
