/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Bell
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.Div.DivMod
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Intervals

/-!
## Correctness of `AzNat.bellNumbersPrefix`

`bellNumbersPrefix_spec`: entry `i` is Mathlib's `Nat.bell i`.  The triangle invariant
(`BellRow n r`) is `r[k] = Σ_{i ≤ k} C(k, i) B_{n−i}` for the `n + 1` entries of row `n`
(`bellTri`); it holds for `[1]`, is preserved by `bellRowNext` (Pascal's rule, `bellTri_succ`),
and gives `r[0] = Bₙ` and `r[n] = B_{n+1}` (`bellTri_self`, from `Nat.bell_succ`).

`bellNumber_spec`: the single-value function is `Nat.bell n`.  Mathlib relates neither its Bell
numbers nor its Stirling numbers to each other, so `Nat.bell_eq_sum_stirlingSecond`
(`Bₙ = Σ_k S(n, k)`) is proven here from `S(n+1, k+1) = Σ_i C(n, i) S(i, k)`
(`Nat.stirlingSecond_succ_succ_eq_sum`), and `Nat.bell_le_pow` (`Bₙ ≤ nⁿ`) from the binomial
theorem.  Dobinski's truncation is then exact algebra: with `f m = N!/m!` and
`kⁿ = Σ_j S(n, j) k^{(j)}` (Mathlib's `pow_eq_sum_stirlingSecond_mul_descFactorial`),
`k^{(j)} f k = f (k − j)`, so `Q Bₙ = P + R` with `R = Σ_j S(n, j) Σ_{N−j < m ≤ N} f m`, and
`R < Q` because each `f m ≤ N!/(N−n+1)!` while `Q ≥ N! = (N−n+1)! · N!/(N−n+1)!` with
`(N−n+1)! > n^{n+1} ≥ n Bₙ`.
-/

namespace Azurite.AzNat

open Finset

/-! ### The triangle entries -/

/-- `Σ_{i ≤ k} C(k, i) B_{n−i}`, the entry `(n, k)` of the Bell triangle. -/
def bellTri (n k : ℕ) : ℕ := ∑ i ∈ range (k + 1), k.choose i * Nat.bell (n - i)

@[simp] theorem bellTri_zero_right (n : ℕ) : bellTri n 0 = Nat.bell n := by
  simp [bellTri]

/-- The last entry of row `n` is `B_{n+1}`. -/
theorem bellTri_self (n : ℕ) : bellTri n n = Nat.bell (n + 1) := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, bellTri]

/-- Pascal's rule for the triangle: `a(n+1, k+1) = a(n+1, k) + a(n, k)`. -/
theorem bellTri_succ (n k : ℕ) : bellTri (n + 1) (k + 1) = bellTri (n + 1) k + bellTri n k := by
  unfold bellTri
  rw [sum_range_succ' (fun i => (k + 1).choose i * Nat.bell (n + 1 - i))]
  simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib, Nat.choose_zero_right, one_mul,
    Nat.sub_zero, Nat.add_sub_add_right]
  have h2 : ∑ i ∈ range (k + 1), k.choose (i + 1) * Nat.bell (n + 1 - (i + 1))
        + k.choose 0 * Nat.bell (n + 1 - 0)
      = ∑ i ∈ range (k + 1), k.choose i * Nat.bell (n + 1 - i) := by
    rw [← sum_range_succ' (fun i => k.choose i * Nat.bell (n + 1 - i)) (k + 1),
      sum_range_succ (fun i => k.choose i * Nat.bell (n + 1 - i)) (k + 1), Nat.choose_succ_self,
      zero_mul, add_zero]
  simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero, Nat.add_sub_add_right] at h2
  omega

/-! ### The rows -/

/-- Row `n` of the triangle: `n + 1` entries with values `bellTri n k`. -/
def BellRow (n : ℕ) (r : List AzNat) : Prop :=
  r.length = n + 1 ∧ ∀ k (hk : k < r.length), r[k].toNat = bellTri n k

theorem bellRow_init : BellRow 0 [1] := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have : k = 0 := by simp at hk; omega
  subst this
  simp [toNat_one]

theorem bellRow_next {n : ℕ} {r : List AzNat} (h : BellRow n r) :
    BellRow (n + 1) (bellRowNext r) := by
  obtain ⟨hlen, hval⟩ := h
  have hlast : (r[r.length - 1]?.getD 1).toNat = Nat.bell (n + 1) := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hval, hlen, Nat.add_sub_cancel,
      bellTri_self]
  unfold bellRowNext
  refine ⟨by rw [List.length_scanl, hlen], ?_⟩
  intro k hk
  induction k with
  | zero => rw [List.getElem_scanl_zero, hlast, bellTri_zero_right]
  | succ k ih =>
    rw [List.getElem_succ_scanl, toNat_add,
      ih (by rw [List.length_scanl] at hk ⊢; omega),
      hval k (by rw [List.length_scanl, hlen] at hk; omega), bellTri_succ]

theorem bellNumbersPrefix.go_spec : ∀ (k n : ℕ) (r : List AzNat) (acc : Array AzNat),
    BellRow n r → acc.size = n → (∀ i (hi : i < acc.size), acc[i].toNat = Nat.bell i) →
    (bellNumbersPrefix.go k r acc).size = n + k ∧
      ∀ i (hi : i < (bellNumbersPrefix.go k r acc).size),
        (bellNumbersPrefix.go k r acc)[i].toNat = Nat.bell i
  | 0, n, r, acc, _, hsize, hacc => ⟨by show acc.size = n + 0; omega, fun i hi => hacc i hi⟩
  | k + 1, n, r, acc, hrow, hsize, hacc => by
    have hhead : (r[0]?.getD 1).toNat = Nat.bell n := by
      rw [List.getElem?_eq_getElem (by rw [hrow.1]; omega), Option.getD_some, hrow.2 0 _,
        bellTri_zero_right]
    have hacc' : ∀ i (hi : i < (acc.push (r[0]?.getD 1)).size),
        (acc.push (r[0]?.getD 1))[i].toNat = Nat.bell i := by
      intro i hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · rw [Array.getElem_push_lt hlt, hacc i hlt]
      · subst heq
        rw [Array.getElem_push_eq, hhead, hsize]
    have := bellNumbersPrefix.go_spec k (n + 1) (bellRowNext r) (acc.push (r[0]?.getD 1))
      (bellRow_next hrow) (by rw [Array.size_push, hsize]) hacc'
    rw [show n + 1 + k = n + (k + 1) by ring] at this
    exact this

/-- **Correctness of `bellNumbersPrefix`**: `n` entries, entry `i` being `Nat.bell i`. -/
theorem bellNumbersPrefix_spec (n : ℕ) :
    (bellNumbersPrefix n).length = n ∧
      ∀ i (hi : i < (bellNumbersPrefix n).length),
        ((bellNumbersPrefix n)[i]).toNat = Nat.bell i := by
  obtain ⟨hsize, hval⟩ := bellNumbersPrefix.go_spec n 0 [1] #[] bellRow_init rfl
    (fun i hi => by simp at hi)
  unfold bellNumbersPrefix
  refine ⟨by rw [Array.length_toList, hsize, zero_add], ?_⟩
  intro i hi
  rw [Array.getElem_toList]
  exact hval i (by simpa using hi)

theorem length_bellNumbersPrefix (n : ℕ) : (bellNumbersPrefix n).length = n :=
  (bellNumbersPrefix_spec n).1

end Azurite.AzNat

/-! ### Bell numbers and Stirling numbers of the second kind -/

namespace Nat

/-- `S(n+1, k+1) = Σ_{i ≤ n} C(n, i) S(i, k)`: the block containing the new element consists of it
and `n − i` of the old ones. -/
theorem stirlingSecond_succ_succ_eq_sum : ∀ n k : ℕ,
    stirlingSecond (n + 1) (k + 1) = ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond i k
  | 0, k => by simp [stirlingSecond_succ_succ]
  | n + 1, k => by
    rw [Finset.sum_range_succ' (fun i => (n + 1).choose i * stirlingSecond i k)]
    simp only [Nat.choose_succ_succ', add_mul, Finset.sum_add_distrib, Nat.choose_zero_right,
      one_mul]
    cases k with
    | zero =>
      rw [stirlingSecond_one_right, stirlingSecond_zero]
      have h1 : ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond (i + 1) 0 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [stirlingSecond_succ_zero, mul_zero]
      have h2 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) * stirlingSecond (i + 1) 0 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [stirlingSecond_succ_zero, mul_zero]
      omega
    | succ k =>
      rw [stirlingSecond_succ_succ, stirlingSecond_succ_succ_eq_sum n (k + 1),
        stirlingSecond_succ_succ_eq_sum n k, stirlingSecond_zero_succ, add_zero]
      have h1 : ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond (i + 1) (k + 1)
          = (k + 1) * ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond i (k + 1)
            + ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond i k := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [stirlingSecond_succ_succ]
        ring
      have h2 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) * stirlingSecond (i + 1) (k + 1)
          = ∑ i ∈ Finset.range (n + 1), n.choose i * stirlingSecond i (k + 1) := by
        have := Finset.sum_range_succ' (fun i => n.choose i * stirlingSecond i (k + 1)) (n + 1)
        rw [Finset.sum_range_succ (fun i => n.choose i * stirlingSecond i (k + 1)) (n + 1),
          Nat.choose_succ_self, zero_mul, add_zero, Nat.choose_zero_right, one_mul,
          stirlingSecond_zero_succ, add_zero] at this
        exact this.symm
      rw [h1, h2]
      ring

/-- **`Bₙ = Σ_{k ≤ n} S(n, k)`.** -/
theorem bell_eq_sum_stirlingSecond (n : ℕ) :
    Nat.bell n = ∑ k ∈ Finset.range (n + 1), stirlingSecond n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Nat.bell_zero]
    | succ n =>
      rw [Finset.sum_range_succ' (fun k => stirlingSecond (n + 1) k), stirlingSecond_succ_zero,
        add_zero]
      simp only [stirlingSecond_succ_succ_eq_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1), n.choose i * stirlingSecond i k
            = n.choose i * Nat.bell i := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [← Finset.mul_sum, ih i hi]
        congr 1
        symm
        apply Finset.sum_subset (fun x hx => Finset.mem_range.mpr
          (by rw [Finset.mem_range] at hx; omega))
        intro k hk hk'
        rw [Finset.mem_range] at hk hk'
        exact stirlingSecond_eq_zero_of_lt (by omega)
      rw [Finset.sum_congr rfl hinner, Nat.bell_succ, ← Nat.range_succ_eq_Iic,
        ← Finset.sum_range_reflect (fun i => n.choose i * Nat.bell (n - i)) (n + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.add_sub_cancel, Nat.sub_sub_self (by omega), Nat.choose_symm (by omega)]

/-- **`Bₙ ≤ nⁿ`.** -/
theorem bell_le_pow (n : ℕ) : Nat.bell n ≤ n ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [Nat.bell_zero]
    | succ n =>
      rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic]
      calc ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell (n - i)
          ≤ ∑ i ∈ Finset.range (n + 1), 1 ^ i * n ^ (n - i) * n.choose i := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            rw [one_pow, one_mul, mul_comm]
            exact Nat.mul_le_mul_right _
              ((ih (n - i) (by omega)).trans (Nat.pow_le_pow_left (Nat.sub_le n i) _))
        _ = (1 + n) ^ n := (add_pow 1 n n).symm
        _ ≤ (n + 1) ^ (n + 1) := by rw [add_comm]; exact Nat.pow_le_pow_right (by omega) (by omega)

end Nat

namespace Azurite.AzNat

open Finset

/-! ### Dobinski's truncation -/

/-- `d N i ≤ d N i'` for `i ≤ i' ≤ N`. -/
theorem descFactorial_mono (N : ℕ) {i i' : ℕ} (h : i ≤ i') (h' : i' ≤ N) :
    N.descFactorial i ≤ N.descFactorial i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    rw [Nat.descFactorial_succ]
    have := ih (by omega)
    have hN : 1 ≤ N - k := by omega
    nlinarith

/-- `m^{(j)} · N!/m! = N!/(m−j)!` for `j ≤ m ≤ N`, as descending factorials. -/
theorem descFactorial_mul_descFactorial_sub {N m j : ℕ} (hj : j ≤ m) (hm : m ≤ N) :
    m.descFactorial j * N.descFactorial (N - m) = N.descFactorial (N - (m - j)) := by
  have h1 := Nat.factorial_mul_descFactorial hj
  have h2 := Nat.factorial_mul_descFactorial (Nat.sub_le N m)
  have h3 := Nat.factorial_mul_descFactorial (Nat.sub_le N (m - j))
  rw [Nat.sub_sub_self hm] at h2
  rw [Nat.sub_sub_self (hm.trans' (Nat.sub_le m j))] at h3
  have hpos : 0 < (m - j).factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (m - j).factorial * (m.descFactorial j * N.descFactorial (N - m))
      = ((m - j).factorial * m.descFactorial j) * N.descFactorial (N - m) := by ring
    _ = m.factorial * N.descFactorial (N - m) := by rw [h1]
    _ = N.factorial := h2
    _ = (m - j).factorial * N.descFactorial (N - (m - j)) := h3.symm

/-- The terms of Dobinski's truncated sums as natural numbers: `P` and `Q` with `f m = N!/m!`
written as `N.descFactorial (N − m)`. -/
def dobinskiP (n N : ℕ) : ℕ := ∑ m ∈ Finset.range (N + 1), m ^ n * N.descFactorial (N - m)
def dobinskiQ (N : ℕ) : ℕ := ∑ m ∈ Finset.range (N + 1), N.descFactorial (N - m)
def dobinskiR (n N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.stirlingSecond n j *
    ∑ m ∈ Finset.Ico (N + 1 - j) (N + 1), N.descFactorial (N - m)

/-- **The exact Dobinski identity**: `Q Bₙ = P + R`. -/
theorem dobinskiQ_mul_bell (n N : ℕ) (hN : n ≤ N) :
    dobinskiQ N * Nat.bell n = dobinskiP n N + dobinskiR n N := by
  -- expand `mⁿ` with the Stirling numbers and swap the sums
  have hP : dobinskiP n N = ∑ j ∈ Finset.range (n + 1), Nat.stirlingSecond n j *
      ∑ m ∈ Finset.range (N + 1 - j), N.descFactorial (N - m) := by
    unfold dobinskiP
    simp only [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mul_sum]
    -- the terms with `m < j` vanish; the others shift by `j`
    rw [← Finset.sum_range_add_sum_Ico _ (show j ≤ N + 1 by omega)]
    rw [Finset.sum_eq_zero (fun m hm => by
      rw [Finset.mem_range] at hm
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hm, mul_zero, zero_mul]), zero_add,
      Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [mul_assoc, descFactorial_mul_descFactorial_sub (by omega) (by omega),
      Nat.add_sub_cancel_left]
  rw [Nat.bell_eq_sum_stirlingSecond, Finset.mul_sum, hP, dobinskiR, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [← mul_add, mul_comm (dobinskiQ N), dobinskiQ,
    Finset.sum_range_add_sum_Ico _ (show N + 1 - j ≤ N + 1 by omega)]

/-- **The remainder is small**: `R < Q` once `(N − n + 1)! > n^{n+1}`. -/
theorem dobinskiR_lt (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (hfac : n ^ (n + 1) < (N - n + 1).factorial) : dobinskiR n N < dobinskiQ N := by
  set D := N.descFactorial (n - 1) with hD
  have hDpos : 0 < D := by
    rw [hD]; by_contra h
    exact absurd (Nat.descFactorial_eq_zero_iff_lt.mp (Nat.eq_zero_of_not_pos h)) (by omega)
  -- every tail term is at most `D`, and each inner sum has `j ≤ n` terms
  have hinner : ∀ j ∈ Finset.range (n + 1),
      ∑ m ∈ Finset.Ico (N + 1 - j) (N + 1), N.descFactorial (N - m) ≤ n * D := by
    intro j hj
    rw [Finset.mem_range] at hj
    calc ∑ m ∈ Finset.Ico (N + 1 - j) (N + 1), N.descFactorial (N - m)
        ≤ ∑ _m ∈ Finset.Ico (N + 1 - j) (N + 1), D := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_Ico] at hm
          exact descFactorial_mono N (by omega) (by omega)
      _ = j * D := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; congr 1; omega
      _ ≤ n * D := Nat.mul_le_mul_right D (by omega)
  have hR : dobinskiR n N ≤ n ^ (n + 1) * D := by
    calc dobinskiR n N
        ≤ ∑ j ∈ Finset.range (n + 1), Nat.stirlingSecond n j * (n * D) :=
          Finset.sum_le_sum fun j hj => Nat.mul_le_mul_left _ (hinner j hj)
      _ = Nat.bell n * (n * D) := by rw [← Finset.sum_mul, Nat.bell_eq_sum_stirlingSecond]
      _ ≤ n ^ n * (n * D) := Nat.mul_le_mul_right _ (Nat.bell_le_pow n)
      _ = n ^ (n + 1) * D := by ring
  -- `Q ≥ f 0 = N! = (N − n + 1)! · D`
  have hQ : (N - n + 1).factorial * D ≤ dobinskiQ N := by
    have hfacD : (N - (n - 1)).factorial * N.descFactorial (n - 1) = N.factorial :=
      Nat.factorial_mul_descFactorial (by omega)
    rw [show N - (n - 1) = N - n + 1 by omega, ← hD] at hfacD
    rw [hfacD]
    unfold dobinskiQ
    have := Finset.single_le_sum (f := fun m => N.descFactorial (N - m))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos N))
    simpa [Nat.descFactorial_self] using this
  calc dobinskiR n N ≤ n ^ (n + 1) * D := hR
    _ < (N - n + 1).factorial * D := Nat.mul_lt_mul_of_pos_right hfac hDpos
    _ ≤ dobinskiQ N := hQ

/-- **`Bₙ = ⌈P / Q⌉ = (P + Q − 1) / Q`.** -/
theorem bell_eq_dobinski_div (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (hfac : n ^ (n + 1) < (N - n + 1).factorial) :
    (dobinskiP n N + dobinskiQ N - 1) / dobinskiQ N = Nat.bell n := by
  have hid := dobinskiQ_mul_bell n N hN
  have hR := dobinskiR_lt n N hn hN hfac
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm]; omega
  · rw [add_mul, one_mul, mul_comm]; omega

/-! ### The implementation computes `P`, `Q` and the truncation -/

theorem dobinskiTerms.go_spec (bound : AzNat) : ∀ (fuel : ℕ) (fact : AzNat) (M : ℕ),
    fact.toNat = M.factorial → bound.toNat < (M + fuel).factorial →
    bound.toNat < (dobinskiTerms.go bound fuel fact M).factorial
  | 0, _, _, _, h => h
  | fuel + 1, fact, M, hfact, h => by
    unfold dobinskiTerms.go
    split_ifs with hlt
    · rw [lt_iff_toNat_lt, hfact] at hlt; exact hlt
    · apply dobinskiTerms.go_spec bound fuel _ (M + 1)
      · rw [toNat_mul, hfact, toNat_ofNat, Nat.factorial_succ, mul_comm]
      · rw [show M + 1 + fuel = M + (fuel + 1) by ring]; exact h

/-- `n^(n+1) < (2n+2)!`. -/
theorem pow_lt_factorial_two_mul (n : ℕ) : n ^ (n + 1) < (2 * n + 2).factorial := by
  have h1 : (2 * n + 2 + 1 - (n + 1)) ^ (n + 1) ≤ (2 * n + 2).descFactorial (n + 1) :=
    Nat.pow_sub_le_descFactorial _ _
  have h2 : (2 * n + 2).descFactorial (n + 1) ≤ (2 * n + 2).factorial := by
    have := Nat.factorial_mul_descFactorial (show n + 1 ≤ 2 * n + 2 by omega)
    have hpos := Nat.factorial_pos (2 * n + 2 - (n + 1))
    nlinarith
  have h3 : n ^ (n + 1) < (2 * n + 2 + 1 - (n + 1)) ^ (n + 1) := by
    rw [show 2 * n + 2 + 1 - (n + 1) = n + 2 by omega]
    exact Nat.pow_lt_pow_left (by omega) (Nat.succ_ne_zero n)
  omega

theorem dobinskiTerms_spec (n : ℕ) : n ^ (n + 1) < (dobinskiTerms n).factorial := by
  have := dobinskiTerms.go_spec ((ofNat n).pow (n + 1)) (2 * n + 2) 1 0 (by simp [toNat_one])
    (by rw [toNat_pow, toNat_ofNat, zero_add]; exact pow_lt_factorial_two_mul n)
  rwa [toNat_pow, toNat_ofNat] at this

theorem one_le_dobinskiTerms {n : ℕ} (hn : 1 ≤ n) : 1 ≤ dobinskiTerms n := by
  by_contra h
  have h0 : dobinskiTerms n = 0 := by omega
  have := dobinskiTerms_spec n
  rw [h0, Nat.factorial_zero] at this
  have : 1 ≤ n ^ (n + 1) := Nat.one_le_pow _ _ hn
  omega

theorem dobinskiSums.go_spec (n N : ℕ) : ∀ (k i : ℕ) (F P Q : AzNat),
    F.toNat = N.descFactorial i →
    P.toNat = ∑ i' ∈ Finset.range i, (N - i') ^ n * N.descFactorial i' →
    Q.toNat = ∑ i' ∈ Finset.range i, N.descFactorial i' →
    (dobinskiSums.go n N k i F P Q).1.toNat
        = ∑ i' ∈ Finset.range (i + k), (N - i') ^ n * N.descFactorial i' ∧
      (dobinskiSums.go n N k i F P Q).2.toNat = ∑ i' ∈ Finset.range (i + k), N.descFactorial i'
  | 0, i, F, P, Q, _, hP, hQ => by simpa using ⟨hP, hQ⟩
  | k + 1, i, F, P, Q, hF, hP, hQ => by
    have := dobinskiSums.go_spec n N k (i + 1) (F * ofNat (N - i))
      (P + (ofNat (N - i)).pow n * F) (Q + F)
      (by rw [toNat_mul, hF, toNat_ofNat, Nat.descFactorial_succ, mul_comm])
      (by rw [toNat_add, toNat_mul, toNat_pow, toNat_ofNat, hF, hP, Finset.sum_range_succ])
      (by rw [toNat_add, hF, hQ, Finset.sum_range_succ])
    rw [show i + 1 + k = i + (k + 1) by ring] at this
    exact this

theorem dobinskiSums_spec (n N : ℕ) :
    (dobinskiSums n N).1.toNat = dobinskiP n N ∧ (dobinskiSums n N).2.toNat = dobinskiQ N := by
  obtain ⟨hP, hQ⟩ := dobinskiSums.go_spec n N (N + 1) 0 1 0 0 (by simp [toNat_one])
    (by simp [toNat_zero]) (by simp [toNat_zero])
  rw [zero_add] at hP hQ
  unfold dobinskiSums dobinskiP dobinskiQ
  refine ⟨?_, ?_⟩
  · rw [hP, ← Finset.sum_range_reflect (fun m => m ^ n * N.descFactorial (N - m)) (N + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.add_sub_cancel, Nat.sub_sub_self (by omega)]
  · rw [hQ, ← Finset.sum_range_reflect (fun m => N.descFactorial (N - m)) (N + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.add_sub_cancel, Nat.sub_sub_self (by omega)]

/-- **Correctness of `bellNumber`.** -/
theorem bellNumber_spec (n : ℕ) : (bellNumber n).toNat = Nat.bell n := by
  unfold bellNumber
  split_ifs with h0
  · rw [h0, toNat_one, Nat.bell_zero]
  · have hn : 1 ≤ n := Nat.pos_of_ne_zero h0
    have hM := one_le_dobinskiTerms hn
    set M := dobinskiTerms n with hMdef
    set N := n + M - 1 with hNdef
    obtain ⟨hP, hQ⟩ := dobinskiSums_spec n N
    have hQpos : 0 < dobinskiQ N := by
      have := dobinskiR_lt n N hn (by omega)
        (by rw [show N - n + 1 = M by omega]; exact dobinskiTerms_spec n)
      omega
    rw [toNat_div, toNat_sub, toNat_add, toNat_one, hP, hQ,
      bell_eq_dobinski_div n N hn (by omega)
        (by rw [show N - n + 1 = M by omega]; exact dobinskiTerms_spec n)]

end Azurite.AzNat
