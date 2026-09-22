import Azurite.AzNat.RootInt
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.SqrtRem
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Azurite.AzNat

/-!
Correctness of `rootInt` (MCA Algorithm 1.14, Theorem 1.7).

  1. `tangent_ineq`: the integer form of the AM–GM step,
     `k·r·s^(k−1) ≤ r^k + (k−1)·s^k`, from Bernoulli's inequality over
     `ℚ` at `a = r/s − 1`.
  2. `step_upper_bound`: if `y^k ≤ m` then `y ≤ ⌊((k−1)s + ⌊m/s^(k−1)⌋)/k⌋`
     — the Newton iterate stays above every root.
  3. `step_exit`: if the iterate is `≥ s` then `s^k ≤ m`.
  4. `rootIntNat.loop_spec`: by induction on fuel, with the invariant
     "`s` bounds every `y` with `y^k ≤ m`", the loop returns `s` with
     `s^k ≤ m < (s+1)^k`.
  5. `toNat_rootInt_loop` / `toNat_rootInt`: the `AzNat` loop mirrors the
     ℕ loop step by step through the `toNat_` lemmas.
-/

/-- **The tangent-line (Bernoulli) inequality**: `k·r·s^(k−1) ≤ r^k + (k−1)s^k`
for `s > 0` — the integer form of `f(s) ≥ m^(1/k)`. -/
theorem tangent_ineq (r s k : ℕ) (hs : 0 < s) (hk : 1 ≤ k) :
    k * r * s ^ (k - 1) ≤ r ^ k + (k - 1) * s ^ k := by
  have hsq : (0 : ℚ) < s := by exact_mod_cast hs
  have hs0 : (s : ℚ) ≠ 0 := hsq.ne'
  have hrs : (0 : ℚ) ≤ (r : ℚ) / s := by positivity
  have hB := one_add_mul_le_pow (show (-2 : ℚ) ≤ (r : ℚ) / s - 1 by linarith) k
  have h1 : (1 : ℚ) + ((r : ℚ) / s - 1) = r / s := by ring
  rw [h1, div_pow] at hB
  have hsk : (0 : ℚ) < (s : ℚ) ^ k := pow_pos hsq k
  have hmul := (le_div_iff₀ hsk).mp hB
  have hexp : ((s : ℚ)) ^ k = s * s ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hcancel : (r : ℚ) / s * s = r := div_mul_cancel₀ _ hs0
  have hlhs : (1 + (k : ℚ) * ((r : ℚ) / s - 1)) * (s : ℚ) ^ k
      = (s : ℚ) ^ k + k * r * s ^ (k - 1) - k * s ^ k := by
    rw [hexp]
    linear_combination ((k : ℚ) * (s : ℚ) ^ (k - 1)) * hcancel
  rw [hlhs] at hmul
  have hq : ((k * r * s ^ (k - 1) : ℕ) : ℚ) ≤ ((r ^ k + (k - 1) * s ^ k : ℕ) : ℚ) := by
    push_cast
    rw [Nat.cast_sub hk, Nat.cast_one]
    linarith
  exact_mod_cast hq

/-- **The iterate bounds every root**: `y^k ≤ m` ⟹
`y ≤ ⌊((k−1)s + ⌊m/s^(k−1)⌋)/k⌋` for `s > 0`. -/
theorem step_upper_bound {m y s k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) (hy : y ^ k ≤ m) :
    y ≤ ((k - 1) * s + m / s ^ (k - 1)) / k := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hX : 0 < s ^ (k - 1) := pow_pos hs _
  have hsk : s ^ k = s * s ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have h1 := tangent_ineq y s k hs hk
  rw [hsk] at h1
  have e1 : k * y * s ^ (k - 1) = y * k * s ^ (k - 1) := by ring
  have e2 : (k - 1) * (s * s ^ (k - 1)) = (k - 1) * s * s ^ (k - 1) := by ring
  rw [e1, e2] at h1
  obtain ⟨q, hq⟩ : ∃ q, q = m / s ^ (k - 1) := ⟨_, rfl⟩
  rw [← hq]
  by_cases hc : y * k ≤ (k - 1) * s
  · omega
  · have h2 : (y * k - (k - 1) * s) * s ^ (k - 1) ≤ m := by
      rw [Nat.sub_mul]
      omega
    have h3 : y * k - (k - 1) * s ≤ q := by
      rw [hq]
      exact (Nat.le_div_iff_mul_le hX).mpr h2
    omega

/-- **The exit test certifies the lower bound**: if the iterate is `≥ s`
then `s^k ≤ m`. -/
theorem step_exit {m s k : ℕ} (hs : 0 < s) (hk : 1 ≤ k)
    (h : s ≤ ((k - 1) * s + m / s ^ (k - 1)) / k) : s ^ k ≤ m := by
  rw [Nat.le_div_iff_mul_le (by omega)] at h
  have hX : 0 < s ^ (k - 1) := pow_pos hs _
  have e : (k - 1) * s + s = s * k := by
    rw [Nat.sub_one_mul, mul_comm s k]
    have := Nat.le_mul_of_pos_left s (by omega : 0 < k)
    omega
  have h2 : s ≤ m / s ^ (k - 1) := by omega
  have h3 := (Nat.le_div_iff_mul_le hX).mp h2
  rw [show s ^ k = s * s ^ (k - 1) by rw [← pow_succ', Nat.sub_add_cancel hk]]
  exact h3

/-- **MCA Theorem 1.7 for the loop**: with enough fuel and an initial `s`
bounding every `y` with `y^k ≤ m`, the loop returns `⌊m^(1/k)⌋`. -/
theorem rootIntNat.loop_spec (m k : ℕ) (hk : 1 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ fuel → (∀ y, y ^ k ≤ m → y ≤ s) →
      rootIntNat.loop m k fuel s ^ k ≤ m
        ∧ m < (rootIntNat.loop m k fuel s + 1) ^ k := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hinv
    have hs0 : s = 0 := by omega
    subst hs0
    rw [rootIntNat.loop]
    refine ⟨by rw [zero_pow (by omega)]; exact Nat.zero_le _, ?_⟩
    rw [zero_add, one_pow]
    by_contra hcon
    have := hinv 1 (by rw [one_pow]; omega)
    omega
  | succ fuel ih =>
    intro s hs hinv
    rw [rootIntNat.loop]
    split_ifs with hlt
    · have hspos : 0 < s := Nat.pos_of_ne_zero fun h0 => by
        subst h0
        exact Nat.not_lt_zero _ hlt
      exact ih _ (Nat.le_of_lt_succ (lt_of_lt_of_le hlt hs))
        fun y hy => step_upper_bound hspos hk hy
    · push Not at hlt
      rcases Nat.eq_zero_or_pos s with hs0 | hspos
      · subst hs0
        refine ⟨by rw [zero_pow (by omega)]; exact Nat.zero_le _, ?_⟩
        rw [zero_add, one_pow]
        by_contra hcon
        have := hinv 1 (by rw [one_pow]; omega)
        omega
      · refine ⟨step_exit hspos hk hlt, ?_⟩
        by_contra hcon
        push Not at hcon
        have := hinv (s + 1) hcon
        omega

/-- The initial guess `2^⌈b/k⌉` bounds every root: `y^k ≤ m` ⟹ `y ≤ 2^⌈b/k⌉`. -/
theorem initialGuess_bound {m k y : ℕ} (hk : 1 ≤ k) (hy : y ^ k ≤ m) :
    y ≤ 2 ^ ((m.size + k - 1) / k) := by
  have hm : m < 2 ^ m.size := Nat.lt_size_self m
  have he : m.size ≤ k * ((m.size + k - 1) / k) := by
    have h1 := Nat.div_add_mod (m.size + k - 1) k
    have h2 := Nat.mod_lt (m.size + k - 1) (by omega : 0 < k)
    omega
  have hlt : y ^ k < (2 ^ ((m.size + k - 1) / k)) ^ k :=
    calc y ^ k ≤ m := hy
      _ < 2 ^ m.size := hm
      _ ≤ 2 ^ (k * ((m.size + k - 1) / k)) := Nat.pow_le_pow_right (by norm_num) he
      _ = (2 ^ ((m.size + k - 1) / k)) ^ k := by rw [← pow_mul, mul_comm]
  exact le_of_lt ((Nat.pow_lt_pow_iff_left (by omega)).mp hlt)

/-- **MCA Theorem 1.7 (ℕ reference)**: `rootIntNat m k = ⌊m^(1/k)⌋`, i.e.
`s^k ≤ m < (s+1)^k`. -/
theorem rootIntNat_spec (m k : ℕ) (hk : 1 ≤ k) :
    rootIntNat m k ^ k ≤ m ∧ m < (rootIntNat m k + 1) ^ k := by
  unfold rootIntNat
  split_ifs with hk1
  · have : k = 1 := by omega
    subst this
    simp
  · exact rootIntNat.loop_spec m k hk _ _ (Nat.le_succ _) fun y hy => initialGuess_bound hk hy

/-- **Uniqueness of the integer root**: `s^k ≤ m < (s+1)^k` pins `s`. -/
theorem eq_of_pow_le_of_lt_pow {m k s t : ℕ} (hk : 1 ≤ k) (hs1 : s ^ k ≤ m)
    (hs2 : m < (s + 1) ^ k) (ht1 : t ^ k ≤ m) (ht2 : m < (t + 1) ^ k) : s = t := by
  have h1 : s < t + 1 := (Nat.pow_lt_pow_iff_left (by omega)).mp (lt_of_le_of_lt hs1 ht2)
  have h2 : t < s + 1 := (Nat.pow_lt_pow_iff_left (by omega)).mp (lt_of_le_of_lt ht1 hs2)
  omega

/-- **The perfect-power criterion (ℕ)**: `m` is a `k`-th power iff
`(rootIntNat m k)^k = m`. -/
theorem rootIntNat_pow_eq_iff (m k : ℕ) (hk : 1 ≤ k) :
    rootIntNat m k ^ k = m ↔ ∃ y, y ^ k = m := by
  obtain ⟨h1, h2⟩ := rootIntNat_spec m k hk
  refine ⟨fun h => ⟨_, h⟩, fun ⟨y, hy⟩ => ?_⟩
  have hyk : m < (y + 1) ^ k := by
    rw [← hy]
    exact Nat.pow_lt_pow_left (by omega) (by omega)
  have := eq_of_pow_le_of_lt_pow hk hy.le hyk h1 h2
  rw [← this]
  exact hy

/-! ### The `AzNat` loop mirrors the ℕ loop -/

private theorem toNat_step (m s : AzNat) (k : ℕ) :
    ((ofNat (k - 1) * s + m / s.pow (k - 1)) / ofNat k).toNat
      = ((k - 1) * s.toNat + m.toNat / s.toNat ^ (k - 1)) / k := by
  rw [toNat_div, toNat_add, toNat_mul, toNat_div, toNat_pow, toNat_ofNat, toNat_ofNat]

theorem toNat_rootInt_loop (m : AzNat) (k : ℕ) :
    ∀ (fuel : ℕ) (s : AzNat),
      (rootInt.loop m k fuel s).toNat = rootIntNat.loop m.toNat k fuel s.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    rfl
  | succ fuel ih =>
    intro s
    simp only [rootInt.loop, rootIntNat.loop]
    by_cases hlt : (ofNat (k - 1) * s + m / s.pow (k - 1)) / ofNat k < s
    · have hlt' := (lt_iff_toNat_lt _ _).mp hlt
      rw [toNat_step] at hlt'
      rw [if_pos hlt, if_pos hlt', ih, toNat_step]
    · have hlt' : ¬ ((k - 1) * s.toNat + m.toNat / s.toNat ^ (k - 1)) / k < s.toNat := by
        rw [← toNat_step]
        exact mt (lt_iff_toNat_lt _ _).mpr hlt
      rw [if_neg hlt, if_neg hlt']

private theorem toNat_initialGuess (m : AzNat) (k : ℕ) :
    (rootInt.initialGuess m k).toNat = 2 ^ ((m.size + k - 1) / k) := by
  show ((1 : AzNat) <<< ((m.size + k - 1) / k)).toNat = _
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq]
  show (1 : AzNat).toNat * 2 ^ ((m.size + k - 1) / k) = _
  rw [show ((1 : AzNat).toNat = 1) from rfl, Nat.one_mul]

/-- **`rootInt` agrees with the ℕ reference.** -/
theorem toNat_rootInt (m : AzNat) (k : ℕ) : (rootInt m k).toNat = rootIntNat m.toNat k := by
  unfold rootInt rootIntNat
  split_ifs with hk
  · rfl
  · rw [toNat_rootInt_loop, toNat_initialGuess, size_toNat, Nat.shiftLeft_eq, Nat.one_mul]

/-- **MCA Theorem 1.7 on `AzNat`**: `rootInt m k = ⌊m^(1/k)⌋`. -/
theorem rootInt_spec (m : AzNat) (k : ℕ) (hk : 1 ≤ k) :
    (rootInt m k).toNat ^ k ≤ m.toNat ∧ m.toNat < ((rootInt m k).toNat + 1) ^ k := by
  rw [toNat_rootInt]
  exact rootIntNat_spec _ _ hk

/-- **The perfect-power test is correct**: `isPow m k = true` iff `m` is a
`k`-th power. -/
theorem isPow_eq_true_iff (m : AzNat) (k : ℕ) (hk : 1 ≤ k) :
    isPow m k = true ↔ ∃ y, y ^ k = m.toNat := by
  rw [isPow, decide_eq_true_iff, ← rootIntNat_pow_eq_iff _ _ hk, ← toNat_rootInt]
  constructor
  · intro h
    rw [← toNat_pow, h]
  · intro h
    apply toNat_injective
    rw [toNat_pow, h]

/-- `rootInt m 2` is the integer square root. -/
theorem rootInt_two (m : AzNat) : rootInt m 2 = sqrt m := by
  apply toNat_injective
  rw [toNat_sqrt]
  obtain ⟨h1, h2⟩ := rootInt_spec m 2 (by norm_num)
  exact eq_of_pow_le_of_lt_pow (by norm_num) h1 h2
    (by rw [pow_two]; exact Nat.sqrt_le _)
    (by rw [pow_two]; exact Nat.lt_succ_sqrt _)

end Azurite.AzNat
