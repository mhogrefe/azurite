import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_11
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_10
import Mathlib.Data.Nat.Size

/-!
# BPR Corollary 10.12: bitsize bound for the coefficients of integer factors

`corollary_10_12`: if `Q ∈ ℤ[X]` divides `P ∈ ℤ[X]` (with `P ≠ 0`) and the
coefficients of `P` have bitsize at most `τ`, then every coefficient of `Q`
has bitsize at most `q + τ + bit(p + 1)`, where `q = deg Q` and `p = deg P`.

BPR's proof: `∥P∥ < √(p+1)·2^τ ≤ 2^{bit(p+1)}·2^τ`, every coefficient of `Q`
is bounded by `Len(Q)`, and `Len(Q) ≤ 2^q·∥P∥` by Proposition 10.11. (The
book phrases the descent through `2^{τ'−1} ≤ Len(Q)` for `τ'` the maximal
coefficient bitsize of `Q`; the formalization bounds each coefficient
directly and converts by `Nat.size_le`.)

The statement is purely about `ℤ[X]` and bitsizes; the proof routes through
the norm over `C = ℝ[i]`, instantiating the real closed field at `ℝ`
(Exercise 2.10 provides `IsRealClosed ℝ`).
-/

namespace Azurite.BPR

open Polynomial Finset

/-- **BPR Corollary 10.12.** If `Q ∈ ℤ[X]` divides `P ∈ ℤ[X]` and the
coefficients of `P` have bitsize at most `τ`, then every coefficient of `Q`
has bitsize at most `q + τ + bit(p + 1)`. -/
theorem corollary_10_12 {P Q : ℤ[X]} (hP : P ≠ 0) (hQP : Q ∣ P) {τ : ℕ}
    (hτ : ∀ i, (P.coeff i).natAbs.size ≤ τ) (i : ℕ) :
    (Q.coeff i).natAbs.size ≤ Q.natDegree + τ + Nat.size (P.natDegree + 1) := by
  set q := Q.natDegree with hq
  set p := P.natDegree with hp
  set s := Nat.size (p + 1) with hs
  rw [Nat.size_le]
  -- work in `C = ℝ[i]`
  haveI : CharZero (Ri ℝ) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℝ (Ri ℝ))
  have hcast : Function.Injective (Int.castRingHom (Ri ℝ)) := fun a b h => by simpa using h
  set P' := P.map (Int.castRingHom (Ri ℝ)) with hP'
  set Q' := Q.map (Int.castRingHom (Ri ℝ)) with hQ'
  -- the coefficient modulus is the cast of the integer absolute value
  have hcoeffabs : ∀ (T : ℤ[X]) (j : ℕ),
      Ri.abs ((T.map (Int.castRingHom (Ri ℝ))).coeff j) = ((T.coeff j).natAbs : ℝ) := by
    intro T j
    rw [Polynomial.coeff_map, show (Int.castRingHom (Ri ℝ)) (T.coeff j)
      = ((T.coeff j : ℤ) : Ri ℝ) from rfl, Ri.abs_intCast]
    exact (Nat.cast_natAbs _).symm
  have hps : ((p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    have h := Nat.lt_size_self (p + 1)
    rw [← hs] at h
    calc ((p + 1 : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
          apply Nat.cast_le.mpr
          omega
      _ = (2 : ℝ) ^ s := by push_cast; ring
  -- the norm of `P` is strictly below `2^{s+τ}`
  have hnormP : polyNorm P' < (2 : ℝ) ^ (s + τ) := by
    apply sqrt_lt_of_lt_sq (by positivity)
    have hdegP' : P'.natDegree = p := Polynomial.natDegree_map_eq_of_injective hcast P
    have hterm : ∀ j, Ri.normSqR (P'.coeff j) < ((2 : ℝ) ^ τ) ^ 2 := by
      intro j
      have h1 : Ri.normSqR (P'.coeff j) = (Ri.abs (P'.coeff j)) ^ 2 := (Ri.abs_sq _).symm
      rw [h1, hP', hcoeffabs P j]
      have h2 : (P.coeff j).natAbs < 2 ^ τ := Nat.size_le.mp (hτ j)
      have h3 : ((P.coeff j).natAbs : ℝ) < (2 : ℝ) ^ τ := by exact_mod_cast h2
      have h4 : (0 : ℝ) ≤ ((P.coeff j).natAbs : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc polyNormSq P'
        < ∑ _j ∈ Finset.range (P'.natDegree + 1), ((2 : ℝ) ^ τ) ^ 2 := by
          rw [polyNormSq]
          exact Finset.sum_lt_sum_of_nonempty Finset.nonempty_range_add_one
            (fun j _ => hterm j)
      _ = ((P'.natDegree + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ τ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ s * ((2 : ℝ) ^ τ) ^ 2 := by
          rw [hdegP']
          exact mul_le_mul_of_nonneg_right hps (by positivity)
      _ ≤ ((2 : ℝ) ^ (s + τ)) ^ 2 := by
          have hexp : ((2 : ℝ) ^ (s + τ)) ^ 2 = 2 ^ s * (2 ^ s * ((2 : ℝ) ^ τ) ^ 2) := by
            rw [pow_add]
            ring
          rw [hexp]
          nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) s,
            pow_pos (show (0:ℝ) < 2 by norm_num) τ,
            one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := s)]
  -- the chain: coefficient ≤ length ≤ 2^q·norm < 2^{q+τ+s}
  have key : ((Q.coeff i).natAbs : ℝ) < (2 : ℝ) ^ (q + τ + s) := by
    calc ((Q.coeff i).natAbs : ℝ) = Ri.abs (Q'.coeff i) := (hcoeffabs Q i).symm
      _ ≤ polyLength Q' := abs_coeff_le_polyLength Q' i
      _ ≤ 2 ^ q * polyNorm P' := proposition_10_11_length hP hQP
      _ < 2 ^ q * (2 : ℝ) ^ (s + τ) :=
          mul_lt_mul_of_pos_left hnormP (by positivity)
      _ = (2 : ℝ) ^ (q + τ + s) := by
          rw [← pow_add]
          congr 1
          omega
  have hfin : ((Q.coeff i).natAbs : ℝ) < ((2 ^ (q + τ + s) : ℕ) : ℝ) := by
    calc ((Q.coeff i).natAbs : ℝ) < (2 : ℝ) ^ (q + τ + s) := key
      _ = ((2 ^ (q + τ + s) : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast hfin

end Azurite.BPR
