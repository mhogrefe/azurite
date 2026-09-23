/-
  `ruler_sequence` — the ruler sequence (Malachite `ruler_sequence`,
  OEIS A007814): `0, 1, 0, 2, 0, 1, 0, 3, …`, where term `n` is the number of
  times `2` divides `n + 1`.

  Malachite's iterator increments a counter `i` and emits
  `i.trailing_zeros()`; the port is `rulerSequence n = twoAdicVal (n + 1)`,
  with `twoAdicVal` the recursive strip-a-factor-of-two loop (the arbitrary-
  precision `trailing_zeros`). The Mathlib spec is
  `rulerSequence n = padicValNat 2 (n + 1)` — proved by pinning the value
  between the two divisibility facts `2 ^ v ∣ n + 1` and `¬ 2 ^ (v+1) ∣ n + 1`.

  The three claims of Malachite's documentation are all formalized:
  * **logarithmic growth** — `2 ^ rulerSequence n ≤ n + 1`, i.e.
    `rulerSequence n ≤ Nat.log 2 (n + 1)`, and the bound is TIGHT: position
    `2 ^ k - 1` attains value `k`;
  * **every value infinitely often** — value `k` appears exactly at the
    positions `2^k - 1 + m * 2^(k+1)` (`m = 0, 1, 2, …`; membership is
    `rulerSequence_two_pow_sub_one_add_mul`, giving both
    `Set.Infinite {n | rulerSequence n = k}` and the unbounded-occurrence
    form);
  * **first occurrences are ordered** — before position `2 ^ k - 1` only
    values `< k` appear (`rulerSequence_lt_of_lt_two_pow`, the contrapositive
    of growth), so value `k` first appears at `2 ^ k - 1`, after every
    smaller value.

  The sequence is Malachite's LENGTH ITERATOR for the fair all-length vec
  enumeration (`exhaustive_vecs` builds on
  `exhaustive_vecs_from_length_iterator(ruler_sequence(), xs)`): the log
  growth is what keeps output lengths logarithmic in the position, and
  every-value-infinitely-often is what lets every length keep producing vecs.
  Ported ahead of that generator. Values stay tiny (≤ log₂ of the position),
  so plain `ℕ` is the right carrier.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Basic

namespace Azurite

/-- The 2-adic valuation of `n` (the number of trailing zero bits — Rust
`trailing_zeros`), by repeatedly stripping a factor of `2`; junk value `0` at
`n = 0` (where the Rust counter never sits). The computational engine of
`rulerSequence`. -/
def twoAdicVal (n : ℕ) : ℕ :=
  if h : n = 0 ∨ n % 2 = 1 then 0
  else twoAdicVal (n / 2) + 1
decreasing_by exact Nat.div_lt_self (by omega) Nat.one_lt_two

theorem twoAdicVal_of_odd {n : ℕ} (h : n % 2 = 1) : twoAdicVal n = 0 := by
  rw [twoAdicVal]
  exact dite_eq_left (Or.inr h)

theorem twoAdicVal_two_mul {n : ℕ} (h : 0 < n) :
    twoAdicVal (2 * n) = twoAdicVal n + 1 := by
  rw [twoAdicVal]
  rw [dite_eq_right (by omega), Nat.mul_div_cancel_left n (by norm_num)]

/-- The valuation is honest, lower half: `2 ^ twoAdicVal n` divides `n`. -/
theorem two_pow_twoAdicVal_dvd (n : ℕ) : 2 ^ twoAdicVal n ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [twoAdicVal]
    split_ifs with h
    · simp
    · -- `n` is even and positive: recurse into `n / 2`.
      obtain ⟨c, hc⟩ := ih (n / 2) (Nat.div_lt_self (by omega) Nat.one_lt_two)
      refine ⟨c, ?_⟩
      rw [pow_succ]
      calc n = 2 * (n / 2) := by omega
        _ = 2 * (2 ^ twoAdicVal (n / 2) * c) := by rw [← hc]
        _ = 2 ^ twoAdicVal (n / 2) * 2 * c := by ring

/-- The valuation is honest, upper half: `2 ^ (twoAdicVal n + 1)` does NOT
divide a positive `n`. -/
theorem not_two_pow_twoAdicVal_succ_dvd {n : ℕ} (hn : n ≠ 0) :
    ¬2 ^ (twoAdicVal n + 1) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hdvd
    rw [twoAdicVal] at hdvd
    by_cases h : n = 0 ∨ n % 2 = 1
    · -- `n` odd: `2 ^ (0 + 1) = 2` would divide it.
      rw [dite_eq_left h, zero_add, pow_one] at hdvd
      obtain ⟨c, rfl⟩ := hdvd
      omega
    · -- `n` even: strip the factor of `2` and recurse.
      rw [dite_eq_right h] at hdvd
      refine ih (n / 2) (Nat.div_lt_self (by omega) Nat.one_lt_two) (by omega) ?_
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c, ?_⟩
      have hkey : n = 2 ^ (twoAdicVal (n / 2) + 1) * c * 2 := by
        conv_lhs => rw [hc]
        ring
      omega

/-- The closed form on the 2-adic normal form: `twoAdicVal (2^k · odd) = k`. -/
theorem twoAdicVal_two_pow_mul_odd (k m : ℕ) :
    twoAdicVal (2 ^ k * (2 * m + 1)) = k := by
  induction k with
  | zero => rw [pow_zero, one_mul]; exact twoAdicVal_of_odd (by omega)
  | succ k ih =>
    have h : 2 ^ (k + 1) * (2 * m + 1) = 2 * (2 ^ k * (2 * m + 1)) := by ring
    rw [h, twoAdicVal_two_mul (by positivity), ih]

/-- `twoAdicVal` agrees with Mathlib's `padicValNat 2` on positive inputs
(pinned between the two divisibility halves). -/
theorem twoAdicVal_eq_padicValNat {n : ℕ} (hn : n ≠ 0) :
    twoAdicVal n = padicValNat 2 n := by
  have hle : twoAdicVal n ≤ padicValNat 2 n :=
    ((padicValNat_dvd_iff_of_ne_one (by norm_num) _ _).mp
      (two_pow_twoAdicVal_dvd n)).resolve_left hn
  have hge : padicValNat 2 n ≤ twoAdicVal n := by
    by_contra hlt
    exact not_two_pow_twoAdicVal_succ_dvd hn
      ((pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd)
  omega

namespace ExhaustiveGenerator

/-- **The ruler sequence** (Malachite `ruler_sequence`, OEIS A007814):
`0, 1, 0, 2, 0, 1, 0, 3, …` — term `n` is the number of times `2` divides
`n + 1` (the Rust iterator emits `trailing_zeros` of its incremented
counter). This is the length iterator pacing Malachite's fair all-length vec
enumeration. -/
def rulerSequence (n : ℕ) : ℕ :=
  twoAdicVal (n + 1)

/-- The Mathlib spec: term `n` is the 2-adic valuation of `n + 1`. -/
theorem rulerSequence_eq_padicValNat (n : ℕ) :
    rulerSequence n = padicValNat 2 (n + 1) :=
  twoAdicVal_eq_padicValNat (Nat.succ_ne_zero n)

/-! ### Logarithmic growth -/

/-- Growth, power form: `2 ^ rulerSequence n ≤ n + 1` (the valuation's power
of two divides `n + 1`). -/
theorem two_pow_rulerSequence_le (n : ℕ) : 2 ^ rulerSequence n ≤ n + 1 :=
  Nat.le_of_dvd (Nat.succ_pos n) (two_pow_twoAdicVal_dvd (n + 1))

/-- **Logarithmic growth** (Malachite: "The `n`th term of this sequence is no
greater than `log₂(n + 1)`"). -/
theorem rulerSequence_le_log (n : ℕ) : rulerSequence n ≤ Nat.log 2 (n + 1) :=
  Nat.le_log_of_pow_le Nat.one_lt_two (two_pow_rulerSequence_le n)

/-- The log bound is TIGHT: position `2 ^ k - 1` attains value `k` (this is
value `k`'s first occurrence, by `rulerSequence_lt_of_lt_two_pow`). -/
theorem rulerSequence_two_pow_sub_one (k : ℕ) : rulerSequence (2 ^ k - 1) = k := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h : 2 ^ k - 1 + 1 = 2 ^ k * (2 * 0 + 1) := by omega
  rw [rulerSequence, h, twoAdicVal_two_pow_mul_odd]

/-- Before position `2 ^ k - 1` only values below `k` appear (the
contrapositive of growth). With `rulerSequence_two_pow_sub_one` this is
Malachite's third claim: "any number's first occurrence is after all smaller
numbers have occurred" — value `k` first appears at position `2 ^ k - 1`. -/
theorem rulerSequence_lt_of_lt_two_pow {k n : ℕ} (h : n + 1 < 2 ^ k) :
    rulerSequence n < k := by
  by_contra hge
  have h1 : 2 ^ k ≤ 2 ^ rulerSequence n := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 := two_pow_rulerSequence_le n
  omega

/-! ### Every value occurs infinitely often -/

/-- Value `k`'s occurrence positions: `rulerSequence` is `k` at
`2^k - 1 + m * 2^(k+1)` for every `m` (there `n + 1 = 2^k · (2m + 1)`). -/
theorem rulerSequence_two_pow_sub_one_add_mul (k m : ℕ) :
    rulerSequence (2 ^ k - 1 + m * 2 ^ (k + 1)) = k := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h : 2 ^ k - 1 + m * 2 ^ (k + 1) + 1 = 2 ^ k * (2 * m + 1) := by
    calc 2 ^ k - 1 + m * 2 ^ (k + 1) + 1 = m * (2 ^ k * 2) + 2 ^ k := by
          rw [← pow_succ]; omega
      _ = 2 ^ k * (2 * m + 1) := by ring
  rw [rulerSequence, h, twoAdicVal_two_pow_mul_odd]

/-- **Every value occurs infinitely often** (Malachite: "Every number occurs
infinitely many times"): the fiber `{n | rulerSequence n = k}` is infinite. -/
theorem infinite_setOf_rulerSequence_eq (k : ℕ) :
    {n | rulerSequence n = k}.Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => 2 ^ k - 1 + m * 2 ^ (k + 1))
    (fun a b hab => by
      have h : 2 ^ k - 1 + a * 2 ^ (k + 1) = 2 ^ k - 1 + b * 2 ^ (k + 1) := hab
      have h2 : a * 2 ^ (k + 1) = b * 2 ^ (k + 1) := by omega
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      exact Nat.eq_of_mul_eq_mul_right hpos h2)
    (fun m => rulerSequence_two_pow_sub_one_add_mul k m)

/-- Unbounded-occurrence form: past any point there is another `k`. -/
theorem exists_le_and_rulerSequence_eq (k N : ℕ) :
    ∃ n, N ≤ n ∧ rulerSequence n = k := by
  refine ⟨2 ^ k - 1 + N * 2 ^ (k + 1), ?_, rulerSequence_two_pow_sub_one_add_mul k N⟩
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  have h : N ≤ N * 2 ^ (k + 1) := Nat.le_mul_of_pos_right N hpos
  omega

end ExhaustiveGenerator

/-! ### Guards

The 20-value table is Malachite's `ruler_sequence` doctest verbatim
(`num/iterators/mod.rs`); the spot checks pin the tightness and occurrence
positions at depth. -/

open ExhaustiveGenerator

-- The Malachite doctest, verbatim.
#guard (List.range 20).map rulerSequence
  = [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2]

-- Tightness at depth: position `2^20 - 1` attains `20`.
#guard rulerSequence (2 ^ 20 - 1) == 20

-- Occurrence positions: value `5` at `2^5 - 1 + m * 2^6` for `m = 0, 3, 100`.
#guard rulerSequence (2 ^ 5 - 1) == 5
#guard rulerSequence (2 ^ 5 - 1 + 3 * 2 ^ 6) == 5
#guard rulerSequence (2 ^ 5 - 1 + 100 * 2 ^ 6) == 5

-- Growth: the whole first `2^10`-block stays within `log₂`.
#guard (List.range 1024).all fun n => rulerSequence n ≤ Nat.log 2 (n + 1)

-- Density sanity: in any `2^k`-block, half the values are `0`.
#guard ((List.range 64).map rulerSequence).count 0 == 32
#guard ((List.range 64).map rulerSequence).count 1 == 16

end Azurite
