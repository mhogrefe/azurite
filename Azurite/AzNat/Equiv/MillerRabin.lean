/-
  **Soundness of the Miller–Rabin filter**: primes pass every base
  (`millerRabinBase_eq_true_of_prime`), hence every `false` verdict is a
  PROOF of compositeness (`millerRabin_eq_false_imp_not_prime`).

  The mathematics is fully deterministic — the probabilistic reputation of
  Miller–Rabin attaches only to how often the filter catches composites,
  which is not part of this statement.  For prime `n`, working in the
  field `ZMod n`:

  * Fermat gives `a^(n−1) = 1` for `a ≢ 0`;
  * `n − 1 = 2^s·d` (the `trailingZeros` split), so the chain
    `a^d, a^(2d), …, a^(2^s·d)` ends at `1`;
  * descending from the first `1` in the chain, the predecessor is a
    square root of `1`, hence `±1` over a field (`mul_self_eq_one_iff` —
    the same dichotomy as GG Lemma 14.7); if it is `−1`, the test's
    `−1`-hunt finds it, and if the chain starts at `1`, the `x = 1` check
    fires.

  Everything is transported along `toZMod : AzZMod n ≃+* ZMod n.toNat`.
-/
import Azurite.AzNat.MillerRabin
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub
import Azurite.AzZMod.Equiv.RingEquiv
import Mathlib.FieldTheory.Finite.Basic

namespace Azurite

namespace AzNat

variable {n : AzNat}

/-- The chain finds a `−1` that is provably there: if
`(toZMod x)^(2^i) = toZMod negOne` for some `i < fuel`, the chain returns
`true`. -/
private theorem mrChain_eq_true [NeZero n.toNat] {negOne : AzZMod n}
    : ∀ (fuel : ℕ) (x : AzZMod n) (i : ℕ), i < fuel →
      (AzZMod.toZMod x) ^ (2 ^ i) = AzZMod.toZMod negOne →
      mrChain n negOne fuel x = true := by
  intro fuel
  induction fuel with
  | zero => intro x i hi _; omega
  | succ fuel ih =>
    intro x i hi hx
    rw [mrChain]
    by_cases hxn : x = negOne
    · rw [ite_eq_left hxn]
    · rw [ite_eq_right hxn]
      cases i with
      | zero =>
        exfalso
        apply hxn
        apply AzZMod.toZMod_injective
        simpa using hx
      | succ i =>
        refine ih (x * x) i (by omega) ?_
        rw [AzZMod.toZMod_mul, ← sq, ← pow_mul, ← pow_succ']
        exact hx

/-- **Primes pass every base.** -/
theorem millerRabinBase_eq_true_of_prime (hp : Nat.Prime n.toNat)
    (a : AzNat) : millerRabinBase n a = true := by
  have h1 : 1 < n.toNat := hp.one_lt
  have : NeZero n.toNat := ⟨by omega⟩
  have : Fact (Nat.Prime n.toNat) := ⟨hp⟩
  rw [millerRabinBase, dite_eq_left h1]
  set s := ((n - 1).trailingZeros).getD 0 with hs
  set d := (n - 1).shiftRight s with hd
  set a' := AzZMod.ofAzNat n a with ha'
  set negOne := AzZMod.ofAzNat n (n - 1) with hneg
  -- the value of `negOne` in `ZMod`
  have hM1 : (n - 1).toNat = n.toNat - 1 := by
    rw [toNat_sub, toNat_one]
  have hnegval : AzZMod.toZMod negOne = (-1 : ZMod n.toNat) := by
    rw [hneg, AzZMod.toZMod_ofAzNat, hM1, Nat.cast_sub (by omega),
      ZMod.natCast_self, Nat.cast_one, zero_sub]
  by_cases htriv : a' = 0 ∨ a' = 1 ∨ a' = negOne
  · rw [ite_eq_left htriv]
  rw [ite_eq_right htriv]
  -- the arithmetic of the `2^s·d` split
  have hM0 : (n - 1).toNat ≠ 0 := by omega
  have hsval : s = padicValNat 2 (n - 1).toNat := by
    rw [hs, trailingZeros_eq_padicValNat _ (by
      intro h0
      apply hM0
      rw [h0]
      rfl)]
    rfl
  have hdval : d.toNat = (n - 1).toNat / 2 ^ s := by
    rw [hd, toNat_shiftRight]
  have hsplit : 2 ^ s * d.toNat = (n - 1).toNat := by
    rw [hdval, hsval]
    exact Nat.mul_div_cancel' pow_padicValNat_dvd
  -- Fermat: the chain ends at `1`
  have ha0 : AzZMod.toZMod a' ≠ 0 := by
    intro h0
    apply htriv
    left
    apply AzZMod.toZMod_injective
    rw [h0, AzZMod.toZMod_zero]
  have hfermat : (AzZMod.toZMod a') ^ ((n - 1).toNat) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one ha0
    rwa [← hM1] at this
  -- descend from the first `1`
  set x := a'.powAzNat d with hx
  have hxval : AzZMod.toZMod x = (AzZMod.toZMod a') ^ d.toNat := by
    rw [hx, AzZMod.toZMod_powAzNat]
  -- main claim: if `(toZMod x)^(2^j) = 1` with `j ≤ s`, the test passes
  have hclaim : ∀ j : ℕ, j ≤ s → (AzZMod.toZMod x) ^ (2 ^ j) = 1 →
      (if x = 1 ∨ x = negOne then true
       else mrChain n negOne (s - 1) (x * x)) = true := by
    intro j
    induction j with
    | zero =>
      intro _ hone
      have hx1 : x = 1 := by
        apply AzZMod.toZMod_injective
        rw [AzZMod.toZMod_one]
        simpa using hone
      rw [ite_eq_left (Or.inl hx1)]
    | succ j ih =>
      intro hj hone
      -- the predecessor is a square root of `1`
      have hsq : ((AzZMod.toZMod x) ^ (2 ^ j))
          * ((AzZMod.toZMod x) ^ (2 ^ j)) = 1 := by
        rw [← pow_add]
        rw [show 2 ^ j + 2 ^ j = 2 ^ (j + 1) from by rw [pow_succ]; omega]
        exact hone
      rcases mul_self_eq_one_iff.mp hsq with hy1 | hym1
      · exact ih (by omega) hy1
      · -- a genuine `−1` in the chain
        by_cases hx1 : x = 1 ∨ x = negOne
        · rw [ite_eq_left hx1]
        rw [ite_eq_right hx1]
        cases j with
        | zero =>
          exfalso
          apply hx1
          right
          apply AzZMod.toZMod_injective
          rw [hnegval]
          simpa using hym1
        | succ j =>
          -- `(x²)^(2^j) = −1` with `j < s − 1`
          refine mrChain_eq_true (s - 1) (x * x) j (by omega) ?_
          rw [AzZMod.toZMod_mul, ← sq, ← pow_mul, ← pow_succ', hnegval]
          exact hym1
  exact hclaim s le_rfl (by
    rw [hxval, ← pow_mul, Nat.mul_comm, hsplit]
    exact hfermat)

/-- **Primes pass any base list.** -/
theorem millerRabinBases_eq_true_of_prime (hp : Nat.Prime n.toNat)
    (bases : List AzNat) : millerRabinBases n bases = true := by
  rw [millerRabinBases, List.all_eq_true]
  intro a _
  exact millerRabinBase_eq_true_of_prime hp a

/-- **Primes pass the driver** — equivalently, every `false` verdict is a
proof of compositeness. -/
theorem millerRabin_eq_true_of_prime (hp : Nat.Prime n.toNat)
    (rounds : ℕ) (seed : UInt64) : millerRabin n rounds seed = true :=
  millerRabinBases_eq_true_of_prime hp _

/-- **The filter contract**: a `false` verdict proves compositeness. -/
theorem millerRabin_eq_false_imp_not_prime {rounds : ℕ} {seed : UInt64}
    (h : millerRabin n rounds seed = false) : ¬ Nat.Prime n.toNat := by
  intro hp
  rw [millerRabin_eq_true_of_prime hp rounds seed] at h
  exact Bool.noConfusion h

end AzNat

end Azurite
