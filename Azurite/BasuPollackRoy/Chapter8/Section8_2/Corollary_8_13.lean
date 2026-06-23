import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_12
import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BPR §8.2.1 Corollary 8.13: bitsize of a determinant

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.

**Corollary 8.13.** Let `M` be an `n × n` matrix with integer entries of bitsizes
at most `τ`. Then the bitsize of `det(M)` is bounded by `n (τ + bit(n)/2)`.

BPR's proof: if `|m_{i,j}| < 2^τ` then `√(∑ⱼ m_{j,i}²) < √n · 2^τ < 2^{τ + bit(n)/2}`,
so by Hadamard (Proposition 8.12) `|det(M)| < 2^{n (τ + bit(n)/2)}`.

The rigorous content of that last inequality is what we formalize. Working with
squares to stay over `ℕ` and clear the `/2`, the core bound is
`|det(M)|² < 2^{n (2τ + bit(n))}` (`corollary_8_13_sq`), proved from the squared
form of Hadamard (`det_sq_le_prod_dotProduct_col`). The literal real-exponent
statement `|det(M)| < 2^{n (τ + bit(n)/2)}` (`corollary_8_13`) follows by taking
square roots. (The phrasing "the bitsize is bounded by `n(τ + bit(n)/2)`" is the
standard reading of this magnitude bound: `bit(N) = ⌊log₂|N|⌋ + 1`, so a bound on
`|det|` is the substantive statement; `bit(N) ≤ X` would be off by the usual `±1`
for non-integer `X`.)

Here `bit(N) = Int.size N` is BPR Definition 8.4 (`Int.size N = N.natAbs.size`,
with `Nat.size n` = number of bits of `n`).
-/

namespace Azurite.BPR

open Matrix

variable {n : ℕ}

/-- **BPR Corollary 8.13, squared form.** If every entry of the integer matrix `M`
has bitsize at most `τ`, then `|det(M)|² < 2^{n (2τ + bit(n))}`. This is the
square-root-free, `ℕ`-valued content of the corollary, equivalent to
`|det(M)| < 2^{n (τ + bit(n)/2)}`. -/
theorem corollary_8_13_sq (M : Matrix (Fin n) (Fin n) ℤ) {τ : ℕ}
    (hn : 0 < n) (hτ : ∀ i j, Int.size (M i j) ≤ τ) :
    M.det.natAbs ^ 2 < 2 ^ (n * (2 * τ + Nat.size n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Squared Hadamard for the real matrix `M.map cast`, transferred back to `ℤ`.
  have hcore := det_sq_le_prod_dotProduct_col (M.map (Int.cast : ℤ → ℝ))
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    have hm := RingHom.map_det (Int.castRingHom ℝ) M
    simpa [RingHom.mapMatrix_apply] using hm.symm
  have hdotcol : ∀ i, (M.map (Int.cast : ℤ → ℝ))ᵀ i ⬝ᵥ (M.map (Int.cast : ℤ → ℝ))ᵀ i
      = ∑ k, ((M k i : ℝ)) ^ 2 := by
    intro i; rw [dotProduct]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [Matrix.transpose_apply, Matrix.map_apply, sq])
  rw [hdet] at hcore
  simp only [hdotcol] at hcore
  -- Cast back to `ℤ`, then to `ℕ` via `natAbs`.
  have hint : M.det ^ 2 ≤ ∏ i, ∑ k, (M k i) ^ 2 := by exact_mod_cast hcore
  have hnat : M.det.natAbs ^ 2 ≤ ∏ i, ∑ k, (M k i).natAbs ^ 2 := by
    have h2 : (M.det.natAbs ^ 2 : ℤ) ≤ ((∏ i, ∑ k, (M k i).natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact hint.trans (le_of_eq (Finset.prod_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun k _ => (sq_abs _).symm))))
    exact_mod_cast h2
  -- Per-entry, per-column, and product bounds over `ℕ`.
  have hentry : ∀ i k, (M k i).natAbs ^ 2 < 2 ^ (2 * τ) := by
    intro i k
    have hs : (M k i).natAbs.size ≤ τ := hτ k i
    have h1 : (M k i).natAbs < 2 ^ τ := Nat.size_le.mp hs
    calc (M k i).natAbs ^ 2 < (2 ^ τ) ^ 2 := Nat.pow_lt_pow_left h1 two_ne_zero
      _ = 2 ^ (2 * τ) := by rw [← pow_mul, Nat.mul_comm]
  have hcolsum : ∀ i, ∑ k, (M k i).natAbs ^ 2 < n * 2 ^ (2 * τ) := by
    intro i
    calc ∑ k, (M k i).natAbs ^ 2 < ∑ _k : Fin n, 2 ^ (2 * τ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hentry i k)
      _ = n * 2 ^ (2 * τ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hBpos : 0 < n * 2 ^ (2 * τ) := Nat.mul_pos hn (pow_pos (by norm_num) _)
  have hprod : (∏ i, ∑ k, (M k i).natAbs ^ 2) < (n * 2 ^ (2 * τ)) ^ n := by
    calc (∏ i, ∑ k, (M k i).natAbs ^ 2) ≤ ∏ _i : Fin n, (n * 2 ^ (2 * τ) - 1) :=
          Finset.prod_le_prod' (fun i _ => Nat.le_pred_of_lt (hcolsum i))
      _ = (n * 2 ^ (2 * τ) - 1) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ < (n * 2 ^ (2 * τ)) ^ n := Nat.pow_lt_pow_left (Nat.sub_lt hBpos Nat.one_pos) hn.ne'
  have hfin : (n * 2 ^ (2 * τ)) ^ n < 2 ^ (n * (2 * τ + Nat.size n)) := by
    have hn2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
    calc (n * 2 ^ (2 * τ)) ^ n = n ^ n * 2 ^ (2 * τ * n) := by rw [Nat.mul_pow, ← pow_mul]
      _ < (2 ^ Nat.size n) ^ n * 2 ^ (2 * τ * n) := by
          have hb : n ^ n < (2 ^ Nat.size n) ^ n := Nat.pow_lt_pow_left hn2 hn.ne'
          exact mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2 ^ (Nat.size n * n + 2 * τ * n) := by rw [← pow_mul, ← pow_add]
      _ = 2 ^ (n * (2 * τ + Nat.size n)) := by ring_nf
  calc M.det.natAbs ^ 2 ≤ ∏ i, ∑ k, (M k i).natAbs ^ 2 := hnat
    _ < (n * 2 ^ (2 * τ)) ^ n := hprod
    _ < 2 ^ (n * (2 * τ + Nat.size n)) := hfin

/-- **BPR Corollary 8.13.** If every entry of the integer matrix `M` has bitsize at
most `τ`, then `|det(M)| < 2^{n (τ + bit(n)/2)}` — the magnitude bound BPR's proof
concludes (so the bitsize of `det(M)` is bounded by `n (τ + bit(n)/2)`). -/
theorem corollary_8_13 (M : Matrix (Fin n) (Fin n) ℤ) {τ : ℕ}
    (hn : 0 < n) (hτ : ∀ i j, Int.size (M i j) ≤ τ) :
    |(M.det : ℝ)| < (2 : ℝ) ^ ((n : ℝ) * (τ + Nat.size n / 2)) := by
  have hsq := corollary_8_13_sq M hn hτ
  have hsqR : (M.det.natAbs : ℝ) ^ 2 < (2 : ℝ) ^ (n * (2 * τ + Nat.size n)) := by
    exact_mod_cast hsq
  have hrpow : ((2 : ℝ) ^ ((n : ℝ) * (τ + Nat.size n / 2))) ^ 2
      = (2 : ℝ) ^ (n * (2 * τ + Nat.size n)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) * (τ + Nat.size n / 2))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_natCast (2 : ℝ) (n * (2 * τ + Nat.size n))]
    congr 1
    push_cast
    ring
  have habs : (M.det.natAbs : ℝ) = |(M.det : ℝ)| := by
    have h1 : ((M.det.natAbs : ℤ) : ℝ) = ((|M.det| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    exact h1
  rw [← habs]
  refine lt_of_pow_lt_pow_left₀ 2 (Real.rpow_nonneg (by norm_num) _) ?_
  rw [hrpow]
  exact hsqR

end Azurite.BPR
