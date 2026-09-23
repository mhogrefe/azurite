/-
  **Cohen–Lenstra Proposition (7.18) and the finite (5.1) engine.**

  Proposition (7.18): if `p ≥ 3` and `n^(p−1) ≢ 1 (mod p²)`, then
  condition (6.4) holds.  The paper's proof: by (5.1), the hypotheses
  give `(n^(p−1))^(ℤ_p) = 1 + pℤ_p`, and `r^(p−1)` lies in `1 + pℤ_p`
  for every divisor `r` of `n`.

  In our finite-level framework, (6.4) is consumed as: for every
  depth `D` there is an exponent `l` with `r^(p−1) ≡ (n^(p−1))^l
  (mod p^D)` — the hypotheses of Theorems (6.3) and (7.8) are
  instances at the depths `v_p(s)` and `v_p(N)`.  This file builds
  the general engine behind (5.1) at finite level, for odd `p`:

  * `dvd_pow_p_sub_one_step` — lifting the exponent, one step: if
    `v_p(A − 1) = c ≥ 1` exactly, then `v_p(A^p − 1) = c + 1`
    exactly (this is where `p > 2` enters, via `v_p(C(p,2)) = 1`);
  * `dvd_pow_p_pow_sub_one` — the iterate
    `v_p(A^(p^j) − 1) = c + j` exactly;
  * `exists_pow_modEq_of_exact` — the engine: if `v_p(a − 1) = c ≥ 1`
    exactly and `p^c ∣ b − 1`, then for every `D` there is `l` with
    `b ≡ a^l (mod p^D)` — `a` generates the `1`-units of level `c`
    at every finite depth.  The proof lifts `l` one digit at a time:
    if `b ≡ a^l (mod p^D)` with `D ≥ c`, write `b − a^l = p^D s` and
    `a^(p^(D−c)) = 1 + p^D u` with `p ∤ u` (the LTE iterate), and
    correct by `l ↦ l + j·p^(D−c)` where `a^l·u·j ≡ s (mod p)`.

  Proposition (7.18) is the instance `c = 1`: Fermat gives
  `p ∣ n^(p−1) − 1` and `p ∣ r^(p−1) − 1`, and the hypothesis says
  `v_p(n^(p−1) − 1) = 1` exactly.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace Azurite

namespace CL

open Finset

/-- `X² ∣ (1 + X)^j − 1 − j·X`: the first-order binomial expansion. -/
theorem sq_dvd_one_add_pow (X : ℤ) (j : ℕ) :
    X ^ 2 ∣ (1 + X) ^ j - 1 - j * X := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : (1 + X) ^ (j + 1) - 1 - (j + 1 : ℕ) * X
        = (1 + X) * ((1 + X) ^ j - 1 - j * X) + j * X ^ 2 := by
      push_cast
      ring
    rw [hstep]
    exact dvd_add (Dvd.dvd.mul_left ih _) (Dvd.dvd.mul_left dvd_rfl _)

/-- **Lifting the exponent, one step** (odd `p`): if `v_p(A − 1) = c`
exactly, with `c ≥ 1`, then `v_p(A^p − 1) = c + 1` exactly. -/
theorem dvd_pow_p_sub_one_step {p : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    {c : ℕ} (hc : 1 ≤ c) {A : ℤ}
    (h1 : (p : ℤ) ^ c ∣ A - 1) (h2 : ¬ (p : ℤ) ^ (c + 1) ∣ A - 1) :
    (p : ℤ) ^ (c + 1) ∣ A ^ p - 1 ∧ ¬ (p : ℤ) ^ (c + 2) ∣ A ^ p - 1 := by
  obtain ⟨t, ht⟩ := h1
  have hpt : ¬ (p : ℤ) ∣ t := by
    intro hd
    obtain ⟨t', rfl⟩ := hd
    exact h2 ⟨t', by rw [ht]; ring⟩
  have hA : A = 1 + (p : ℤ) ^ c * t := by omega
  -- the key congruence: `A^p ≡ 1 + p^(c+1)·t  (mod p^(c+2))`
  have hkey : (p : ℤ) ^ (c + 2) ∣ A ^ p - 1 - (p : ℤ) ^ (c + 1) * t := by
    -- split the binomial sum after the linear term
    have hbin := sq_dvd_one_add_pow ((p : ℤ) ^ c * t) p
    -- (p^c t)² is divisible by p^(c+2)⁻...: 2c ≥ c+1; we need one more p
    -- from the multinomial structure, so redo the sum directly
    have hsum : A ^ p = ∑ i ∈ Finset.range (p + 1),
        ((p : ℤ) ^ c * t) ^ i * (p.choose i : ℤ) := by
      rw [hA, add_comm]
      rw [add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one]
    have hsplit : Finset.range (p + 1)
        = insert 0 (insert 1 (Finset.Ico 2 (p + 1))) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have h01 : (0 : ℕ) ∉ insert 1 (Finset.Ico 2 (p + 1)) := by
      simp
    have h11 : (1 : ℕ) ∉ Finset.Ico 2 (p + 1) := by
      simp
    rw [hsum, hsplit, Finset.sum_insert h01, Finset.sum_insert h11]
    have hterm0 : ((p : ℤ) ^ c * t) ^ 0 * (p.choose 0 : ℤ) = 1 := by
      simp
    have hterm1 : ((p : ℤ) ^ c * t) ^ 1 * (p.choose 1 : ℤ)
        = (p : ℤ) ^ (c + 1) * t := by
      rw [Nat.choose_one_right, pow_one, pow_succ]
      ring
    rw [hterm0, hterm1]
    have hrest : ∀ i ∈ Finset.Ico 2 (p + 1),
        (p : ℤ) ^ (c + 2) ∣ ((p : ℤ) ^ c * t) ^ i * (p.choose i : ℤ) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi.2) with hilt | hieq
      · -- `2 ≤ i < p`: use `p ∣ C(p,i)` and `p^(2c) ∣ (p^c t)^i`
        obtain ⟨d, hd⟩ := Nat.Prime.dvd_choose_self hp (by omega : i ≠ 0) hilt
        have hdd : ((p : ℤ) ^ c * t) ^ i * (p.choose i : ℤ)
            = (p : ℤ) ^ (c * i + 1)
              * (t ^ i * d) := by
          rw [hd]
          push_cast
          rw [mul_pow, ← pow_mul]
          ring
        rw [hdd]
        refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _
        have : 2 * c ≤ c * i := by
          have := hi.1
          nlinarith
        omega
      · -- `i = p`: `p^(cp) ∣ (p^c t)^p` and `cp ≥ c + 2`
        subst hieq
        rw [mul_pow, ← pow_mul]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
          (pow_dvd_pow _ (by nlinarith)) _) _
    obtain ⟨v, hv⟩ := Finset.dvd_sum hrest
    rw [hv]
    ring_nf
    exact ⟨v, by ring⟩
  constructor
  · -- `p^(c+1) ∣ A^p − 1`
    obtain ⟨v, hv⟩ := hkey
    exact ⟨(p : ℤ) * v + t, by
      rw [show A ^ p - 1 = (p : ℤ) ^ (c + 2) * v + (p : ℤ) ^ (c + 1) * t
        from by omega]
      ring⟩
  · -- `¬ p^(c+2) ∣ A^p − 1`
    intro hdvd
    have hd2 : (p : ℤ) ^ (c + 2) ∣ (p : ℤ) ^ (c + 1) * t := by
      obtain ⟨v, hv⟩ := hkey
      obtain ⟨w, hw⟩ := hdvd
      exact ⟨w - v, by linear_combination hw - hv⟩
    have : (p : ℤ) ∣ t := by
      obtain ⟨w, hw⟩ := hd2
      have hpne : ((p : ℤ)) ^ (c + 1) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast hp.pos.ne')
      refine ⟨w, ?_⟩
      have : (p : ℤ) ^ (c + 1) * t = (p : ℤ) ^ (c + 1) * ((p : ℤ) * w) := by
        rw [hw, pow_succ]
        ring
      exact mul_left_cancel₀ hpne this
    exact hpt this

/-- **The LTE iterate**: `v_p(A^(p^j) − 1) = c + j` exactly. -/
theorem dvd_pow_p_pow_sub_one {p : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    {c : ℕ} (hc : 1 ≤ c) {A : ℤ}
    (h1 : (p : ℤ) ^ c ∣ A - 1) (h2 : ¬ (p : ℤ) ^ (c + 1) ∣ A - 1) :
    ∀ j, (p : ℤ) ^ (c + j) ∣ A ^ p ^ j - 1
      ∧ ¬ (p : ℤ) ^ (c + j + 1) ∣ A ^ p ^ j - 1 := by
  intro j
  induction j with
  | zero => simpa using ⟨h1, h2⟩
  | succ j ih =>
    have hstep := dvd_pow_p_sub_one_step hp hp3
      (by omega : 1 ≤ c + j) ih.1 ih.2
    rw [← pow_mul, ← pow_succ] at hstep
    exact ⟨by
        have := hstep.1
        rwa [show c + j + 1 = c + (j + 1) by omega] at this,
      by
        have := hstep.2
        rwa [show c + j + 2 = c + (j + 1) + 1 by omega] at this⟩

/-- The `p`-part of an order: if `ω ∣ M·p` but `ω ∤ M`, then
`v_p(ω) = v_p(M) + 1`. -/
theorem factorization_eq_succ_of_dvd_mul_prime {ω M p : ℕ}
    (hp : p.Prime) (hM0 : M ≠ 0) (hω0 : ω ≠ 0) (h1 : ω ∣ M * p)
    (h2 : ¬ ω ∣ M) : ω.factorization p = M.factorization p + 1 := by
  have hMp0 : M * p ≠ 0 := Nat.mul_ne_zero hM0 hp.pos.ne'
  have hle := (Nat.factorization_le_iff_dvd hω0 hMp0).mpr h1
  have hmul : (M * p).factorization p = M.factorization p + 1 := by
    rw [Nat.factorization_mul hM0 hp.pos.ne']
    simp [Nat.Prime.factorization_self hp]
  refine le_antisymm (by
    have := Finsupp.le_def.mp hle p
    omega) ?_
  by_contra hlt
  push Not at hlt
  refine h2 ((Nat.factorization_le_iff_dvd hω0 hM0).mp ?_)
  refine Finsupp.le_def.mpr fun ℓ => ?_
  rcases eq_or_ne ℓ p with rfl | hℓ
  · omega
  · have h3 := Finsupp.le_def.mp hle ℓ
    rw [Nat.factorization_mul hM0 hp.pos.ne'] at h3
    have h4 : p.factorization ℓ = 0 := by
      rw [Nat.Prime.factorization hp, Finsupp.single_apply,
        ite_eq_right (fun h => hℓ h.symm)]
    simp only [Finsupp.coe_add, Pi.add_apply] at h3
    omega

/-- Exact `p`-valuation from exact integer divisibilities. -/
theorem factorization_eq_of_int_dvd {p M e : ℕ} (hp : p.Prime)
    (hM0 : M ≠ 0) (h1 : (p : ℤ) ^ e ∣ (M : ℤ))
    (h2 : ¬ (p : ℤ) ^ (e + 1) ∣ (M : ℤ)) : M.factorization p = e := by
  have h1' : p ^ e ∣ M := by exact_mod_cast h1
  have h2' : ¬ p ^ (e + 1) ∣ M := fun hd => h2 (by exact_mod_cast hd)
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp hM0).mp h1'
  have hlt : ¬ e + 1 ≤ M.factorization p := fun hcon =>
    h2' ((Nat.Prime.pow_dvd_iff_le_factorization hp hM0).mpr hcon)
  omega

/-- The digit-lifting core of the finite (5.1) engine, parameterized
by the exact lifting-the-exponent iterate. -/
private theorem exists_pow_modEq_core {p a b c : ℕ} (hp : p.Prime)
    (hc : 1 ≤ c) (hpa : ¬ p ∣ a)
    (hiter : ∀ j, (p : ℤ) ^ (c + j) ∣ (a : ℤ) ^ p ^ j - 1
      ∧ ¬ (p : ℤ) ^ (c + j + 1) ∣ (a : ℤ) ^ p ^ j - 1)
    (hb : (p : ℤ) ^ c ∣ (b : ℤ) - 1) :
    ∀ D, ∃ l, b ≡ a ^ l [MOD p ^ D] := by
  have : Fact p.Prime := ⟨hp⟩
  intro D
  induction D with
  | zero => exact ⟨0, by simpa using Nat.modEq_one⟩
  | succ D ihD =>
    by_cases hle : D + 1 ≤ c
    · -- shallow depths: `b ≡ 1 = a^0`
      refine ⟨0, ?_⟩
      rw [pow_zero, Nat.modEq_iff_dvd]
      have hbd : ((p : ℤ)) ^ (D + 1) ∣ (b : ℤ) - 1 :=
        dvd_trans (pow_dvd_pow _ hle) hb
      push_cast
      exact dvd_sub_comm.mp hbd
    · -- the digit-lifting step, `D ≥ c`
      have hDc : c ≤ D := by omega
      have hD1 : 1 ≤ D := by omega
      clear hle
      obtain ⟨l, hl⟩ := ihD
      -- `b − a^l = p^D·s`
      have hlZ : ((p : ℤ)) ^ D ∣ (b : ℤ) - (a : ℤ) ^ l := by
        have hdd := hl.dvd
        push_cast at hdd
        exact dvd_sub_comm.mp hdd
      obtain ⟨s, hs⟩ := hlZ
      -- `a^(p^(D−c)) = 1 + p^D·u` with `p ∤ u`
      obtain ⟨hu1, hu2⟩ := hiter (D - c)
      rw [show c + (D - c) = D from by omega] at hu1
      rw [show c + (D - c) + 1 = D + 1 from by omega] at hu2
      obtain ⟨u, hu⟩ := hu1
      have hpu : ¬ (p : ℤ) ∣ u := by
        intro hd
        obtain ⟨u', rfl⟩ := hd
        exact hu2 ⟨u', by rw [hu]; ring⟩
      -- choose the correcting digit `j` with `a^l·u·j ≡ s (mod p)`
      have hA0 : ((a : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hpa
      have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hpu
      have hexists : ∃ j : ℕ, (p : ℤ) ∣ s - (a : ℤ) ^ l * u * (j : ℕ) := by
        refine ⟨((s : ZMod p)
          * (((a : ℕ) : ZMod p) ^ l * ((u : ℤ) : ZMod p))⁻¹).val, ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
        rw [show ((a : ℕ) : ZMod p) ^ l * ((u : ℤ) : ZMod p)
              * ((s : ZMod p)
                * (((a : ℕ) : ZMod p) ^ l * ((u : ℤ) : ZMod p))⁻¹)
            = (s : ZMod p)
              * ((((a : ℕ) : ZMod p) ^ l * ((u : ℤ) : ZMod p))
                * (((a : ℕ) : ZMod p) ^ l * ((u : ℤ) : ZMod p))⁻¹)
          from by ring,
          mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero l hA0) hu0),
          mul_one, sub_self]
      obtain ⟨j, hj⟩ := hexists
      obtain ⟨sc, hsc⟩ := hj
      refine ⟨l + j * p ^ (D - c), ?_⟩
      rw [Nat.modEq_iff_dvd]
      push_cast
      -- goal : (p:ℤ)^(D+1) ∣ (a:ℤ)^(l + j·p^(D−c)) − b
      have hu' : (a : ℤ) ^ p ^ (D - c) = 1 + (p : ℤ) ^ D * u := by
        omega
      have hupow : ((a : ℤ) ^ p ^ (D - c)) ^ j
          = (1 + (p : ℤ) ^ D * u) ^ j := by rw [hu']
      obtain ⟨w, hw⟩ := sq_dvd_one_add_pow ((p : ℤ) ^ D * u) j
      have hxw : (1 + (p : ℤ) ^ D * u) ^ j
          = 1 + (j : ℤ) * ((p : ℤ) ^ D * u) + ((p : ℤ) ^ D * u) ^ 2 * w := by
        omega
      have hbz : (b : ℤ) = (a : ℤ) ^ l + (p : ℤ) ^ D * s := by omega
      have hsz : s = (a : ℤ) ^ l * u * (j : ℕ) + (p : ℤ) * sc := by omega
      have hDD : (p : ℤ) ^ (D + 1) * (p : ℤ) ^ (D - 1)
          = (p : ℤ) ^ D * (p : ℤ) ^ D := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      refine ⟨(a : ℤ) ^ l * u ^ 2 * w * (p : ℤ) ^ (D - 1) - sc, ?_⟩
      rw [pow_add, pow_mul', hupow, hxw, hbz, hsz]
      linear_combination (-((a : ℤ) ^ l * u ^ 2 * w)) * hDD

/-- **The finite (5.1) engine** (odd `p`): if `v_p(a − 1) = c ≥ 1`
exactly, then every `b ≡ 1 (mod p^c)` is a power of `a` modulo `p^D`
for every depth `D`. -/
theorem exists_pow_modEq_of_exact {p a b c : ℕ} (hp : p.Prime)
    (hp3 : 2 < p) (hc : 1 ≤ c) (hpa : ¬ p ∣ a)
    (ha1 : (p : ℤ) ^ c ∣ (a : ℤ) - 1)
    (ha2 : ¬ (p : ℤ) ^ (c + 1) ∣ (a : ℤ) - 1)
    (hb : (p : ℤ) ^ c ∣ (b : ℤ) - 1) :
    ∀ D, ∃ l, b ≡ a ^ l [MOD p ^ D] :=
  exists_pow_modEq_core hp hc hpa
    (dvd_pow_p_pow_sub_one hp hp3 hc ha1 ha2) hb

/-- **Lifting the exponent at `p = 2`, one step**: if
`v_2(A − 1) = c ≥ 2` exactly, then `v_2(A² − 1) = c + 1` exactly —
via `A² − 1 = (A − 1)(A + 1)` with `v_2(A + 1) = 1`. -/
theorem dvd_two_pow_sub_one_step {c : ℕ} (hc : 2 ≤ c) {A : ℤ}
    (h1 : (2 : ℤ) ^ c ∣ A - 1) (h2 : ¬ (2 : ℤ) ^ (c + 1) ∣ A - 1) :
    (2 : ℤ) ^ (c + 1) ∣ A ^ 2 - 1 ∧ ¬ (2 : ℤ) ^ (c + 2) ∣ A ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := h1
  have hto : ¬ (2 : ℤ) ∣ t := by
    intro hd
    obtain ⟨t', rfl⟩ := hd
    exact h2 ⟨t', by rw [ht]; ring⟩
  -- `A² − 1 = 2^(c+1)·t·(1 + 2^(c−1)·t)` with odd cofactor
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  have hkey : A ^ 2 - 1
      = (2 : ℤ) ^ (c' + 2 + 1) * (t * (1 + (2 : ℤ) ^ (c' + 1) * t)) := by
    have hA : A = 1 + (2 : ℤ) ^ (c' + 2) * t := by omega
    rw [hA]
    ring
  constructor
  · exact ⟨t * (1 + (2 : ℤ) ^ (c' + 1) * t), hkey⟩
  · intro hd
    rw [hkey] at hd
    obtain ⟨w, hw⟩ := hd
    have hcan : t * (1 + (2 : ℤ) ^ (c' + 1) * t) = 2 * w := by
      have hpne : ((2 : ℤ)) ^ (c' + 2 + 1) ≠ 0 := by positivity
      refine mul_left_cancel₀ hpne ?_
      rw [hw]
      ring
    -- but the left side is odd
    have hodd : ¬ (2 : ℤ) ∣ t * (1 + (2 : ℤ) ^ (c' + 1) * t) := by
      intro hd2
      rcases Int.even_mul.mp (even_iff_two_dvd.mpr hd2) with h | h
      · exact hto (even_iff_two_dvd.mp h)
      · obtain ⟨y, hy⟩ := even_iff_two_dvd.mp h
        have h2c : ((2 : ℤ)) ^ (c' + 1) = 2 * (2 : ℤ) ^ c' := by
          rw [pow_succ]; ring
        refine absurd (⟨y - (2 : ℤ) ^ c' * t, by
          linear_combination hy - t * h2c⟩ : (2 : ℤ) ∣ 1) ?_
        intro hcon
        obtain ⟨x, hx⟩ := hcon
        omega
    exact hodd ⟨w, hcan⟩

/-- **The LTE iterate at `p = 2`**: `v_2(A^(2^j) − 1) = c + j`
exactly, for `c ≥ 2`. -/
theorem dvd_two_pow_pow_sub_one {c : ℕ} (hc : 2 ≤ c) {A : ℤ}
    (h1 : (2 : ℤ) ^ c ∣ A - 1) (h2 : ¬ (2 : ℤ) ^ (c + 1) ∣ A - 1) :
    ∀ j, (2 : ℤ) ^ (c + j) ∣ A ^ 2 ^ j - 1
      ∧ ¬ (2 : ℤ) ^ (c + j + 1) ∣ A ^ 2 ^ j - 1 := by
  intro j
  induction j with
  | zero => simpa using ⟨h1, h2⟩
  | succ j ih =>
    have hstep := dvd_two_pow_sub_one_step (by omega : 2 ≤ c + j)
      ih.1 ih.2
    rw [← pow_mul, ← pow_succ] at hstep
    exact ⟨by
        have := hstep.1
        rwa [show c + j + 1 = c + (j + 1) by omega] at this,
      by
        have := hstep.2
        rwa [show c + j + 2 = c + (j + 1) + 1 by omega] at this⟩

/-- **The finite (5.1) engine at `p = 2`**: if `v_2(a − 1) = c ≥ 2`
exactly (the paper's "`m ≥ 2` in the case `p = 2`"), then every
`b ≡ 1 (mod 2^c)` is a power of `a` modulo `2^D` for every `D`. -/
theorem exists_pow_modEq_of_exact_two {a b c : ℕ} (hc : 2 ≤ c)
    (ha0 : ¬ 2 ∣ a)
    (ha1 : (2 : ℤ) ^ c ∣ (a : ℤ) - 1)
    (ha2 : ¬ (2 : ℤ) ^ (c + 1) ∣ (a : ℤ) - 1)
    (hb : (2 : ℤ) ^ c ∣ (b : ℤ) - 1) :
    ∀ D, ∃ l, b ≡ a ^ l [MOD 2 ^ D] :=
  exists_pow_modEq_core Nat.prime_two (by omega) ha0
    (by exact_mod_cast dvd_two_pow_pow_sub_one hc ha1 ha2) hb

/-- **Cohen–Lenstra Proposition (7.18)**: if `p ≥ 3` and
`n^(p−1) ≢ 1 (mod p²)`, then condition (6.4) is satisfied — at
finite level: for every `r` coprime to `p` (in particular every
divisor of `n`) and every depth `D`, there is an exponent `l` with
`r^(p−1) ≡ (n^(p−1))^l (mod p^D)`. -/
theorem proposition_7_18 {p n r : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hpn : ¬ p ∣ n) (hn2 : ¬ n ^ (p - 1) ≡ 1 [MOD p ^ 2])
    (hpr : ¬ p ∣ r) :
    ∀ D, ∃ l, r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ D] := by
  have : Fact p.Prime := ⟨hp⟩
  have hfermat : ∀ {x : ℕ}, ¬ p ∣ x → (p : ℤ) ^ 1 ∣ (x : ℤ) ^ (p - 1) - 1 := by
    intro x hx
    have hz : ((x : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hx
    have h1 : ((x : ℕ) : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hz
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1, sub_self]
  have ha2 : ¬ (p : ℤ) ^ (1 + 1) ∣ (n : ℤ) ^ (p - 1) - 1 := by
    intro hd
    refine hn2 ?_
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact dvd_sub_comm.mp (by exact_mod_cast hd)
  have hpnp : ¬ p ∣ n ^ (p - 1) := fun hd => hpn (hp.dvd_of_dvd_pow hd)
  have hcast : ∀ D, (∀ l', r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l' [MOD p ^ D]
      → True) := fun _ _ _ => trivial
  intro D
  obtain ⟨l, hl⟩ := exists_pow_modEq_of_exact hp hp3 (le_refl 1) hpnp
    (by exact_mod_cast hfermat hpn)
    (by exact_mod_cast ha2)
    (by exact_mod_cast hfermat hpr) D
  exact ⟨l, hl⟩

end CL

end Azurite
