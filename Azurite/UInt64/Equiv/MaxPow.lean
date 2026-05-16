import Azurite.UInt64.Equiv.Digits
import Azurite.UInt64.MaxPow
import Mathlib.Data.Nat.Digits.Lemmas

namespace UInt64

/-- Invariant for the `maxPow.go` loop: entering with `acc = b^e` and
    enough fuel that `b^(e + fuel + 1)` already exceeds `2^64`, the
    output `(p, q)` satisfies `p = b^q` and `b^(q+1) ≥ 2^64`. -/
private theorem maxPow.go_correct (b cap : UInt64) (hb : 2 ≤ b.toNat)
    (hcap : cap.toNat = (2 ^ 64 - 1) / b.toNat) :
    ∀ (fuel : Nat) (acc : UInt64) (e : Nat),
      acc.toNat = b.toNat ^ e →
      2 ^ 64 ≤ b.toNat ^ (e + fuel + 1) →
      (maxPow.go b cap fuel acc e).1.toNat = b.toNat ^ (maxPow.go b cap fuel acc e).2 ∧
      2 ^ 64 ≤ b.toNat ^ ((maxPow.go b cap fuel acc e).2 + 1) := by
  intro fuel acc e
  induction fuel, acc, e using maxPow.go.induct b cap with
  | case1 acc e =>
    intro h_acc h_over
    rw [maxPow.go]
    refine ⟨h_acc, ?_⟩
    simpa using h_over
  | case2 f acc e h_le ih =>
    intro h_acc h_over
    rw [maxPow.go, if_pos h_le]
    apply ih
    · have h_acc_le : acc.toNat ≤ cap.toNat := UInt64.le_iff_toNat_le_toNat.mp h_le
      have h_acc_b_le : acc.toNat * b.toNat ≤ 2 ^ 64 - 1 := by
        calc acc.toNat * b.toNat
            ≤ cap.toNat * b.toNat := Nat.mul_le_mul_right _ h_acc_le
          _ = (2 ^ 64 - 1) / b.toNat * b.toNat := by rw [hcap]
          _ ≤ 2 ^ 64 - 1 := Nat.div_mul_le_self _ _
      rw [UInt64.toNat_mul, h_acc, ← Nat.pow_succ]
      apply Nat.mod_eq_of_lt
      have h_pow_eq : b.toNat ^ (e + 1) = acc.toNat * b.toNat := by
        rw [Nat.pow_succ, ← h_acc]
      rw [h_pow_eq]; omega
    · show 2 ^ 64 ≤ b.toNat ^ (e + 1 + f + 1)
      have : e + 1 + f + 1 = e + (f + 1) + 1 := by ring
      rw [this]; exact h_over
  | case3 f acc e h_gt =>
    intro h_acc _h_over
    rw [maxPow.go, if_neg h_gt]
    refine ⟨h_acc, ?_⟩
    have h_b_pos : 0 < b.toNat := by omega
    have h_cap_lt : cap.toNat < acc.toNat := by
      rw [UInt64.le_iff_toNat_le_toNat] at h_gt
      omega
    rw [hcap] at h_cap_lt
    have h_lt : 2 ^ 64 - 1 < acc.toNat * b.toNat :=
      (Nat.div_lt_iff_lt_mul h_b_pos).mp h_cap_lt
    have h_pow_eq : b.toNat ^ (e + 1) = acc.toNat * b.toNat := by
      rw [Nat.pow_succ, ← h_acc]
    rw [h_pow_eq]; omega

/-- **Correctness of `maxPow`.** For `b.toNat ≥ 2`, the first component
    `p` of `maxPow b` satisfies `p.toNat = b^e` (where `e` is the second
    component), and `b^(e+1)` exceeds `2^64` --- i.e., one more multiplication
    by `b` would overflow. -/
theorem maxPow_correct (b : UInt64) (hb : 2 ≤ b.toNat) :
    (maxPow b).1.toNat = b.toNat ^ (maxPow b).2 ∧
    2 ^ 64 ≤ b.toNat ^ ((maxPow b).2 + 1) := by
  have hb_uint : ¬ b < 2 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt_toNat] at h
    have h2 : (2 : UInt64).toNat = 2 := rfl
    omega
  unfold maxPow
  rw [if_neg hb_uint]
  refine maxPow.go_correct b _ hb ?hcap 64 1 0 ?h_acc ?h_over
  case hcap =>
    rw [UInt64.toNat_div]
    have : (0 - 1 : UInt64).toNat = 2 ^ 64 - 1 := by decide
    rw [this]
  case h_acc =>
    show (1 : UInt64).toNat = b.toNat ^ 0
    simp
  case h_over =>
    show 2 ^ 64 ≤ b.toNat ^ (0 + 64 + 1)
    have h1 : (2 : Nat) ^ 65 ≤ b.toNat ^ 65 := Nat.pow_le_pow_left hb 65
    have h2 : (2 : Nat) ^ 64 ≤ 2 ^ 65 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 64 ≤ 65)
    have h3 : (0 + 64 + 1 : Nat) = 65 := by omega
    rw [h3]; omega

/-- **Array length bound for `digits`.** A `UInt64` has at most
    `(maxPow b).2 + 1` digits in base `b` --- the `+1` accounts for
    values up to (but excluding) `b^((maxPow b).2 + 1) ≥ 2^64`. -/
theorem digits_size_le (b u : UInt64) (hb : 2 ≤ b.toNat) :
    (digits b u).size ≤ (maxPow b).2 + 1 := by
  rw [Array.size_eq_length_toList]
  have h_eq := digits_eq b u hb
  have h_len : (digits b u).toList.length = (Nat.digits b.toNat u.toNat).length := by
    have := congrArg List.length h_eq
    simpa using this
  rw [h_len, Nat.digits_length_le_iff (by omega : 1 < b.toNat)]
  have h_correct := maxPow_correct b hb
  have h_u : u.toNat < 2 ^ 64 := UInt64.toNat_lt u
  omega

end UInt64
