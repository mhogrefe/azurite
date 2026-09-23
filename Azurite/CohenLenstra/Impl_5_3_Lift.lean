/-
  **The Lucas–Lehmer confinement (5.3), part 2: lifting to all levels
  and the parity of the `2`-adic exponent.**

  * `cond_6_4_of_test_4_3`: for an odd prime `p ∣ n + 1`, the base
    confinement `test_4_3_confinement` (at level `v_p(n+1) = v_p(n² − 1)`)
    feeds Proposition (10.7) with `f = 2`, giving condition (6.4) at `p`
    for every depth — the `f⁺` half of Remark (4.5), companion of
    `cond_6_4_of_test_4_2`.
  * `pow_modEq_one_two_pow_iff` / `parity_of_modEq_two_pow`: when
    `n² ≡ 1 (mod 2^(v+1))` but `n ≢ 1 (mod 2^(v+1))`, the residue of `n^l`
    modulo `2^(v+1)` determines the parity of `l`; so any exponent `l` with
    `r ≡ n^l (mod 2^(v+1))` has the parity forced by `r mod 2^(v+1)`.
  * `c1_parity`, `c2_parity`: with `v = v₂(n ∓ 1)` exactly, that parity is
    the splitting type `ε(r)` of `c1_two_adic`/`c2_two_adic` — the
    coherence hypothesis `(p = 2 → l % 2 = ε)` of `theorem_6_3_LL`.
  * `pow_sub_one_modEq_of_modEq`: the (6.4) shape
    `r^(p−1) ≡ (n^(p−1))^l` from `r ≡ n^l`.
-/
import Azurite.CohenLenstra.Impl_5_3
import Azurite.CohenLenstra.Impl_4_5
import Azurite.CohenLenstra.Theorem_6_3_LL

namespace Azurite

namespace CL

open Polynomial

/-! ### Lifting the `f⁺` confinement -/

/-- For an odd prime `p ∣ n + 1` (`n ≥ 2`), `v_p(n² − 1) = v_p(n + 1)`. -/
theorem factorization_sq_sub_one_eq_add_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (hpd : p ∣ n + 1) : (n ^ 2 - 1).factorization p = (n + 1).factorization p := by
  have hsplit : n ^ 2 - 1 = (n - 1) * (n + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
    omega
  have hn1 : n - 1 ≠ 0 := by omega
  rw [hsplit, Nat.factorization_mul hn1 (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (n := n - 1) (p := p) ?_, zero_add]
  intro hd
  have h2 : p ∣ (n + 1) - (n - 1) := Nat.dvd_sub hpd hd
  rw [show n + 1 - (n - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- **(6.4) at odd `p ∣ f⁺` from Test (4.3)**: the base confinement lifts to
every depth by Proposition (10.7) (`f = 2`). -/
theorem cond_6_4_of_test_4_3 {n r p : ℕ} (hn2 : ¬ 2 ∣ n) (hn1 : 1 < n) (hr : r.Prime)
    (hrn : r ∣ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ n + 1) {u a x₀ x₁ : ZMod n}
    (hN : quadNorm u a x₀ x₁ = 1) (hx1 : quadElt u a x₀ x₁ ^ (n + 1) = 1)
    (hunit : ∃ c₀ c₁ : ZMod n, quadElt u a x₀ x₁ ^ ((n + 1) / p) - 1 = quadElt u a c₀ c₁
      ∧ (IsUnit c₀ ∨ IsUnit c₁)) :
    ∀ D : ℕ, ∃ l : ℕ, r ≡ n ^ l [MOD p ^ D] := by
  classical
  have hpn : ¬ p ∣ n := by
    intro hd
    have h1 : p ∣ (n + 1) - n := Nat.dvd_sub hpd hd
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hv : 0 < (n + 1).factorization p := hp.factorization_pos_of_dvd (by omega) hpd
  have hpv : p ^ (n + 1).factorization p ∣ n + 1 := Nat.ordProj_dvd _ _
  have hconf := test_4_3_confinement hn2 hr hrn hp hp2 hv hpv hN hx1 hunit
  refine proposition_10_7 hp hn1 hpn two_pos ?_ (fun h2 => absurd h2 hp2) ?_
  · have : p ∣ (n - 1) * (n + 1) := dvd_mul_of_dvd_right hpd _
    have hsq : n ^ 2 - 1 = (n - 1) * (n + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      omega
    rw [hsq]
    exact this
  · refine ⟨if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4 * ZMod.castHom hrn (ZMod r) a)
      then 0 else 1, by split_ifs <;> omega, ?_⟩
    rw [factorization_sq_sub_one_eq_add_one hp hp2 (by omega) hpd]
    exact hconf

/-- The (6.4) shape from a plain congruence. -/
theorem pow_sub_one_modEq_of_modEq {r n l p M : ℕ} (h : r ≡ n ^ l [MOD M]) :
    r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD M] := by
  rw [← pow_mul, mul_comm (p - 1) l, pow_mul]
  exact h.pow _

/-! ### The parity of the `2`-adic exponent -/

/-- If `n² ≡ 1` but `n ≢ 1 (mod 2^(v+1))`, then `n^l ≡ 1 (mod 2^(v+1))` iff
`l` is even. -/
theorem pow_modEq_one_two_pow_iff {n v l : ℕ} (hn2 : n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)])
    (hn1 : ¬ n ≡ 1 [MOD 2 ^ (v + 1)]) :
    n ^ l ≡ 1 [MOD 2 ^ (v + 1)] ↔ l % 2 = 0 := by
  have hred : n ^ l ≡ n ^ (l % 2) [MOD 2 ^ (v + 1)] :=
    pow_modEq_pow_of_sq_modEq_one hn2 (Nat.mod_mod l 2).symm
  constructor
  · intro h
    by_contra hodd
    have hl1 : l % 2 = 1 := by omega
    rw [hl1, pow_one] at hred
    exact hn1 (hred.symm.trans h)
  · intro h
    rw [h, pow_zero] at hred
    exact hred

/-- **The parity is forced**: if `r ≡ n^l (mod 2^(v+1))` under the same
hypotheses, then `l` is even iff `r ≡ 1 (mod 2^(v+1))`. -/
theorem parity_of_modEq_two_pow {n r v l : ℕ} (hn2 : n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)])
    (hn1 : ¬ n ≡ 1 [MOD 2 ^ (v + 1)]) (hr : r ≡ n ^ l [MOD 2 ^ (v + 1)]) :
    l % 2 = 0 ↔ r ≡ 1 [MOD 2 ^ (v + 1)] := by
  rw [← pow_modEq_one_two_pow_iff hn2 hn1]
  exact ⟨fun h => hr.trans h, fun h => hr.symm.trans h⟩

/-- `2^v ∣ n + 1` with `v ≥ 1` gives `n² ≡ 1 (mod 2^(v+1))`. -/
theorem sq_modEq_one_of_dvd_add_one {n v : ℕ} (hv : 1 ≤ v) (h : 2 ^ v ∣ n + 1) :
    n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)] := by
  obtain ⟨w, hw⟩ := h
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have h1 : 2 ^ v ∣ 1 := ⟨w, by simpa using hw⟩
      have := Nat.le_of_dvd one_pos h1
      have := Nat.one_lt_two_pow (by omega : v ≠ 0)
      omega
    · exact h0
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn0
  refine ((Nat.modEq_iff_dvd' hn1).mpr ?_).symm
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  refine ⟨w * (2 ^ v' * w - 1), ?_⟩
  have hn : n = 2 ^ (v' + 1) * w - 1 := Nat.eq_sub_of_add_eq hw
  have hw1 : 1 ≤ 2 ^ v' * w := by
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0
        simp at hw
      · exact h0
    exact Nat.mul_pos (Nat.pow_pos (by norm_num)) hw0
  have hw2 : 1 ≤ 2 ^ (v' + 1) * w := by
    have : 2 ^ (v' + 1) * w = 2 * (2 ^ v' * w) := by ring
    rw [this]
    omega
  zify [hn1, hw1, hw2] at hn ⊢
  rw [hn]
  ring

/-- `2^v ∣ n − 1` with `v ≥ 1`, `1 ≤ n`, gives `n² ≡ 1 (mod 2^(v+1))`. -/
theorem sq_modEq_one_of_dvd_sub_one {n v : ℕ} (hv : 1 ≤ v) (hn : 1 ≤ n) (h : 2 ^ v ∣ n - 1) :
    n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)] := by
  obtain ⟨w, hw⟩ := h
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ((Nat.modEq_iff_dvd' hn1).mpr ?_).symm
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  refine ⟨w * (2 ^ v' * w + 1), ?_⟩
  have hn' : n = 2 ^ (v' + 1) * w + 1 := Nat.eq_add_of_sub_eq hn hw
  zify [hn1] at hn' ⊢
  rw [hn']
  ring

open Classical in
/-- **(c2): the parity of any `2`-adic exponent is the splitting type.**
With `2^v ∣ n + 1`, `v ≥ 2`, for any `l` with
`r ≡ n^l (mod 2^(v+1))`, `l % 2 = ε(r)`. -/
theorem c2_parity {n r : ℕ} (hn3 : n % 4 = 3) (hr : r.Prime) (hrn : r ∣ n) {u : ZMod n}
    (hα : (AdjoinRoot.root (X ^ 2 - C u * X - C (1 : ZMod n) : Polynomial (ZMod n))) ^ (n + 1)
      = -1) {v : ℕ} (hv : 2 ≤ v) (h2v : 2 ^ v ∣ n + 1)
    {l : ℕ} (hl : r ≡ n ^ l [MOD 2 ^ (v + 1)]) :
    l % 2 = if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) then 0 else 1 := by
  obtain ⟨hbase, hsplit, -⟩ := c2_two_adic hn3 hr hrn hα hv h2v
  have hn2 : n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)] := sq_modEq_one_of_dvd_add_one (by omega) h2v
  have hn1 : ¬ n ≡ 1 [MOD 2 ^ (v + 1)] := by
    intro h
    have h1 : 2 ^ (v + 1) ∣ n - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h.symm
    have h2 : 4 ∣ n - 1 := (pow_dvd_pow 2 (by omega : 2 ≤ v + 1)).trans h1
    omega
  have hpar := parity_of_modEq_two_pow hn2 hn1 hl
  split_ifs with hsq
  · exact hpar.mpr (((Nat.modEq_iff_dvd' hr.one_lt.le).mpr (hsplit hsq)).symm)
  · by_contra hcon
    have hl0 : l % 2 = 0 := by omega
    have hr1 := hpar.mp hl0
    rw [if_neg hsq, pow_one] at hbase
    -- `r ≡ n (mod 2^v)` and `r ≡ 1 (mod 2^(v+1))` force `2^v ∣ 2`
    have h1 : n ≡ 1 [MOD 2 ^ v] :=
      hbase.symm.trans (Nat.ModEq.of_dvd (pow_dvd_pow 2 (Nat.le_succ v)) hr1)
    have h2 : 2 ^ v ∣ n - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    have h3 : 2 ^ v ∣ (n + 1) - (n - 1) := Nat.dvd_sub h2v h2
    rw [show n + 1 - (n - 1) = 2 by omega] at h3
    have h4 := Nat.le_of_dvd two_pos h3
    have h5 : 4 ≤ 2 ^ v := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
    omega

open Classical in
/-- **(c1): the parity of any `2`-adic exponent is the splitting type.**
With `v = v₂(n − 1)` (`n ≡ 1 (mod 4)`, so `v ≥ 2`), for any `l` with
`r ≡ n^l (mod 2^(v+1))`, `l % 2 = ε(r)`. -/
theorem c1_parity {n r : ℕ} (hn : Odd n) (hr : r.Prime) (hrn : r ∣ n) {a : ℤ}
    (ha : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1)) (hv : 1 ≤ (n - 1).factorization 2)
    {l : ℕ} (hl : r ≡ n ^ l [MOD 2 ^ ((n - 1).factorization 2 + 1)]) :
    l % 2 = if IsSquare ((ZMod.castHom hrn (ZMod r) (0 : ZMod n)) ^ 2
        + 4 * ZMod.castHom hrn (ZMod r) ((a : ℤ) : ZMod n)) then 0 else 1 := by
  obtain ⟨hdvd, hiff⟩ := c1_two_adic hn hr hrn ha
  set v := (n - 1).factorization 2 with hvdef
  have hn1' : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (h0 ▸ hn) (by decide)
    · exact h0
  have hn0 : n - 1 ≠ 0 := by
    intro h
    have : n = 1 := by omega
    subst this
    exact hr.one_lt.ne' (Nat.dvd_one.mp hrn)
  have hn2 : n ^ 2 ≡ 1 [MOD 2 ^ (v + 1)] :=
    sq_modEq_one_of_dvd_sub_one hv hn1' (Nat.ordProj_dvd _ _)
  have hn1 : ¬ n ≡ 1 [MOD 2 ^ (v + 1)] := by
    intro h
    have h1 : 2 ^ (v + 1) ∣ n - 1 := (Nat.modEq_iff_dvd' hn1').mp h.symm
    exact Nat.pow_succ_factorization_not_dvd hn0 Nat.prime_two h1
  have hpar := parity_of_modEq_two_pow hn2 hn1 hl
  have hr1 : r ≡ 1 [MOD 2 ^ (v + 1)] ↔ 2 ^ (v + 1) ∣ r - 1 := by
    constructor
    · intro h
      exact (Nat.modEq_iff_dvd' hr.one_lt.le).mp h.symm
    · intro h
      exact ((Nat.modEq_iff_dvd' hr.one_lt.le).mpr h).symm
  split_ifs with hsq
  · exact hpar.mpr (hr1.mpr (by_contra fun h => (hiff.mp h) hsq))
  · by_contra hcon
    have hl0 : l % 2 = 0 := by omega
    exact (hiff.mpr hsq) (hr1.mp (hpar.mp hl0))

end CL

end Azurite
