/-
  **Cohen–Lenstra (7.23)–(7.25): the `p = 2` methods for
  condition (6.4).**

  For `p = 2` (so `n` odd), the tested congruence with `ζ = −1` is
  replaced by the Solovay–Strassen-shaped `a^((n−1)/2) ≡ −1 (mod n)`,
  and (6.4) at `p = 2` reads, at finite level: for every prime
  `r ∣ n` and every depth `D` there is `l` with
  `r ≡ n^l (mod 2^D)`.

  * **Lemma (7.23)** (stated for prime divisors, the form the two
    propositions consume): if `a^((n−1)/2) ≡ −1 (mod n)`, then every
    prime `r ∣ n` has `v_2(r − 1) ≥ v_2(n − 1)`, with equality if
    and only if the Legendre symbol `(a/r)` is `−1`.  The proof is
    the paper's: the order `ω` of `a` mod `r` has
    `v_2(ω) = v_2(n − 1)` exactly (it divides `n − 1` but not
    `(n−1)/2`), and `ω ∣ r − 1`; equality is governed by whether
    `ω ∣ (r−1)/2`, i.e. by Euler's criterion.  (The paper states the
    lemma for all divisors, with the Jacobi symbol; that extension is
    multiplicativity bookkeeping that nothing downstream consumes,
    and is omitted.)
  * **Proposition (7.24)**: `n ≡ 1 (mod 4)` plus a witness
    `a^((n−1)/2) ≡ −1 (mod n)` give (6.4) for `p = 2` — by (7.23),
    `v_2(r − 1) ≥ v_2(n − 1) ≥ 2`, and the `2`-adic (5.1) engine
    with base `n` finishes.
  * **Proposition (7.25)**: `n ≡ 3 (mod 8)` plus
    `2^((n−1)/2) ≡ −1 (mod n)` give (6.4) for `p = 2` — by (7.23)
    with the supplementary law for `(2/r)`, every prime `r ∣ n` is
    `≡ 1` or `≡ n (mod 8)`; since `v_2(n² − 1) = 3` exactly, the
    `2`-adic engine with base `n²` captures `r` (directly, or after
    multiplying by `n`).
-/
import Azurite.CohenLenstra.Proposition_7_18
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Azurite

namespace CL

open Finset

/-- **Cohen–Lenstra Lemma (7.23)** (prime-divisor form): if
`a^((n−1)/2) ≡ −1 (mod n)` then every prime `r ∣ n` satisfies
`v_2(r − 1) ≥ v_2(n − 1)`, with equality iff `(a/r) = −1`. -/
theorem lemma_7_23 {n r : ℕ} [hrF : Fact r.Prime] {a : ℤ}
    (hodd : Odd n)
    (ha : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1))
    (hrn : r ∣ n) :
    2 ^ ((n - 1).factorization 2) ∣ r - 1
    ∧ (¬ 2 ^ ((n - 1).factorization 2 + 1) ∣ r - 1
        ↔ legendreSym r a = -1) := by
  have hr : r.Prime := hrF.out
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hrn
    obtain ⟨j, hj⟩ := hodd
    omega
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hn3 : 3 ≤ n := le_trans hr3 (Nat.le_of_dvd (by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hodd (by decide)
    · exact h) hrn)
  have hhalf2 : (n - 1) / 2 * 2 = n - 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hhalf0 : (n - 1) / 2 ≠ 0 := by omega
  -- reduce the hypothesis mod r and move to `ZMod r`
  have har : Int.ModEq (r : ℤ) (a ^ ((n - 1) / 2)) (-1) :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hrn) ha
  have hAhalf : ((a : ZMod r)) ^ ((n - 1) / 2) = -1 := by
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).mpr har
    push_cast at hc
    exact hc
  have hA0 : ((a : ZMod r)) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hhalf0] at hAhalf
    have h1 : ((1 : ZMod r)) = 0 := by
      have := congrArg Neg.neg hAhalf
      simpa using this.symm
    exact one_ne_zero h1
  have hM : ((a : ZMod r)) ^ (n - 1) = 1 := by
    rw [← hhalf2, pow_mul, hAhalf]
    ring
  have hM2 : ((a : ZMod r)) ^ ((n - 1) / 2) ≠ 1 := by
    rw [hAhalf]
    haveI : Fact (2 < r) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  -- the order of `a` mod `r` and its 2-part
  have hω0 : orderOf ((a : ZMod r)) ≠ 0 := by
    have hfin : IsOfFinOrder ((a : ZMod r)) :=
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨n - 1, by omega, hM⟩
    exact hfin.orderOf_pos.ne'
  have hωdvd : orderOf ((a : ZMod r)) ∣ (n - 1) / 2 * 2 := by
    rw [hhalf2]
    exact orderOf_dvd_of_pow_eq_one hM
  have hωndvd : ¬ orderOf ((a : ZMod r)) ∣ (n - 1) / 2 := fun hd =>
    hM2 (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hvω : (orderOf ((a : ZMod r))).factorization 2
      = ((n - 1) / 2).factorization 2 + 1 :=
    factorization_eq_succ_of_dvd_mul_prime Nat.prime_two hhalf0 hω0
      hωdvd hωndvd
  have hvn : (n - 1).factorization 2
      = ((n - 1) / 2).factorization 2 + 1 := by
    rw [← hhalf2, Nat.factorization_mul hhalf0 (by omega)]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  -- `ω ∣ r − 1`
  have hωr : orderOf ((a : ZMod r)) ∣ r - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hA0)
  have hr10 : r - 1 ≠ 0 := by omega
  have hrhalf2 : (r - 1) / 2 * 2 = r - 1 := by
    have hro := hr.odd_of_ne_two hr2
    obtain ⟨j, hj⟩ := hro
    omega
  have hrhalf0 : (r - 1) / 2 ≠ 0 := by omega
  -- the key equivalence: `ω ∣ (r−1)/2 ↔ 2^(v_2(n−1)+1) ∣ r−1`
  have hkey : orderOf ((a : ZMod r)) ∣ (r - 1) / 2
      ↔ 2 ^ ((n - 1).factorization 2 + 1) ∣ r - 1 := by
    constructor
    · intro hd
      have hdd : (2 : ℕ) ^ ((n - 1).factorization 2)
          ∣ (r - 1) / 2 := by
        refine dvd_trans ?_ hd
        rw [show (n - 1).factorization 2
            = (orderOf ((a : ZMod r))).factorization 2 from by omega]
        exact Nat.ordProj_dvd _ 2
      obtain ⟨w, hw⟩ := hdd
      refine ⟨w, ?_⟩
      rw [← hrhalf2, hw, pow_succ]
      ring
    · intro hd
      refine (Nat.factorization_le_iff_dvd hω0 hrhalf0).mp ?_
      refine Finsupp.le_def.mpr fun ℓ => ?_
      have hfr : (r - 1).factorization
          = (2 : ℕ).factorization + ((r - 1) / 2).factorization := by
        rw [← Nat.factorization_mul (by omega) hrhalf0,
          mul_comm, hrhalf2]
      rcases eq_or_ne ℓ 2 with rfl | hℓ
      · have hv2 : (n - 1).factorization 2 + 1
            ≤ (r - 1).factorization 2 :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
            hr10).mp hd
        have h2 := congrArg (fun f => f 2) hfr
        simp only [Finsupp.coe_add, Pi.add_apply,
          Nat.Prime.factorization_self Nat.prime_two] at h2
        omega
      · have hle := (Nat.factorization_le_iff_dvd hω0 hr10).mpr hωr
        have h3 := Finsupp.le_def.mp hle ℓ
        have h2 := congrArg (fun f => f ℓ) hfr
        have h4 : (2 : ℕ).factorization ℓ = 0 := by
          rw [Nat.Prime.factorization Nat.prime_two,
            Finsupp.single_apply, if_neg (fun h => hℓ h.symm)]
        simp only [Finsupp.coe_add, Pi.add_apply, h4] at h2
        omega
  constructor
  · -- part (i)
    calc (2 : ℕ) ^ ((n - 1).factorization 2)
        = 2 ^ ((orderOf ((a : ZMod r))).factorization 2) := by
          rw [hvω, hvn]
      _ ∣ orderOf ((a : ZMod r)) := Nat.ordProj_dvd _ 2
      _ ∣ r - 1 := hωr
  · -- part (ii)
    have heuler : legendreSym r a = 1
        ↔ ((a : ZMod r)) ^ ((r - 1) / 2) = 1 := by
      rw [legendreSym.eq_one_iff r hA0,
        ZMod.euler_criterion r hA0,
        show r / 2 = (r - 1) / 2 from by omega]
    constructor
    · intro hnd
      rcases legendreSym.eq_one_or_neg_one r (a := a) hA0 with h1 | h1
      · exfalso
        refine hnd (hkey.mp ?_)
        exact orderOf_dvd_iff_pow_eq_one.mpr (heuler.mp h1)
      · exact h1
    · intro hleg hd
      have hdiv := hkey.mpr hd
      have h1 : legendreSym r a = 1 :=
        heuler.mpr (orderOf_dvd_iff_pow_eq_one.mp hdiv)
      rw [h1] at hleg
      exact absurd hleg (by norm_num)

/-- **Cohen–Lenstra Proposition (7.24)**: if `n ≡ 1 (mod 4)` and
some `a` satisfies `a^((n−1)/2) ≡ −1 (mod n)`, then condition (6.4)
holds for `p = 2` — at finite level, every prime `r ∣ n` is a power
of `n` modulo `2^D` for every depth `D`. -/
theorem proposition_7_24 {n : ℕ} (hn1 : 1 < n) (hmod : n % 4 = 1)
    {a : ℤ} (ha : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1))
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n) :
    ∀ D, ∃ l, r ≡ n ^ l [MOD 2 ^ D] := by
  have hodd : Odd n := by
    rw [Nat.odd_iff]
    omega
  haveI : Fact r.Prime := ⟨hr⟩
  have h723 := (lemma_7_23 hodd ha hrn).1
  have hn10 : n - 1 ≠ 0 := by omega
  have hv2 : 2 ≤ (n - 1).factorization 2 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      hn10).mp ?_
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]
    omega
  have hr1 : 1 ≤ r := hr.pos
  have hn1' : 1 ≤ n := by omega
  have ha1 : (2 : ℤ) ^ ((n - 1).factorization 2) ∣ (n : ℤ) - 1 := by
    have hd := Nat.ordProj_dvd (n - 1) 2
    have hd' : ((2 ^ ((n - 1).factorization 2) : ℕ) : ℤ)
        ∣ ((n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hd
    push_cast [hn1'] at hd'
    exact_mod_cast hd'
  have ha2 : ¬ (2 : ℤ) ^ ((n - 1).factorization 2 + 1)
      ∣ (n : ℤ) - 1 := by
    intro hd
    have hd' : (2 : ℕ) ^ ((n - 1).factorization 2 + 1) ∣ n - 1 := by
      have hdd : ((2 ^ ((n - 1).factorization 2 + 1) : ℕ) : ℤ)
          ∣ ((n - 1 : ℕ) : ℤ) := by
        push_cast [hn1']
        exact_mod_cast hd
      exact_mod_cast hdd
    exact Nat.pow_succ_factorization_not_dvd hn10 Nat.prime_two hd'
  have hb : (2 : ℤ) ^ ((n - 1).factorization 2) ∣ (r : ℤ) - 1 := by
    have hd' : ((2 ^ ((n - 1).factorization 2) : ℕ) : ℤ)
        ∣ ((r - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h723
    push_cast [hr1] at hd'
    exact_mod_cast hd'
  have h2n : ¬ 2 ∣ n := by omega
  exact exists_pow_modEq_of_exact_two hv2 h2n ha1 ha2 hb

/-- **Cohen–Lenstra Proposition (7.25)**: if `n ≡ 3 (mod 8)` and
`2^((n−1)/2) ≡ −1 (mod n)`, then condition (6.4) holds for `p = 2`.
Every prime `r ∣ n` is `≡ 1` or `≡ n (mod 8)` (by (7.23) and the
supplementary law), and the `2`-adic engine with base `n²` (whose
`v_2(n² − 1) = 3` exactly) captures `r` or `r·n`. -/
theorem proposition_7_25 {n : ℕ} (hmod : n % 8 = 3)
    (ha : Int.ModEq (n : ℤ) ((2 : ℤ) ^ ((n - 1) / 2)) (-1))
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n) :
    ∀ D, ∃ l, r ≡ n ^ l [MOD 2 ^ D] := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hodd : Odd n := by
    rw [Nat.odd_iff]
    omega
  have hn3 : 3 ≤ n := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hrn
    omega
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hrodd : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  -- `v_2(n−1) = 1`
  have hv1 : (n - 1).factorization 2 = 1 := by
    refine le_antisymm ?_ ?_
    · by_contra hlt
      push Not at hlt
      have hd := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (by omega : n - 1 ≠ 0)).mpr hlt
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4] at hd
      omega
    · refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (by omega : n - 1 ≠ 0)).mp ?_
      have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
      rw [h2]
      omega
  obtain ⟨h723a, h723b⟩ := lemma_7_23 hodd ha hrn
  rw [hv1] at h723b
  -- the supplementary law forces `r ≡ 1` or `r ≡ 3 (mod 8)`
  have h20 : (((2 : ℤ)) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have hle : (r : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
    have hle' : r ≤ 2 := by exact_mod_cast hle
    omega
  have hsq : IsSquare ((2 : ZMod r)) ↔ r % 8 = 1 ∨ r % 8 = 7 :=
    ZMod.exists_sq_eq_two_iff hr2
  have hcast2 : (((2 : ℤ)) : ZMod r) = (2 : ZMod r) := by
    push_cast
    rfl
  have hleg1 : legendreSym r 2 = 1 ↔ IsSquare ((2 : ZMod r)) := by
    rw [legendreSym.eq_one_iff r h20, hcast2]
  have hcase : r % 8 = 1 ∨ r % 8 = 3 := by
    have hr8 : r % 8 = 1 ∨ r % 8 = 3 ∨ r % 8 = 5 ∨ r % 8 = 7 := by
      omega
    rcases hr8 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · -- `r ≡ 5 (mod 8)`: `4 ∣ r − 1`, so `(2/r) = 1`, so `r ≡ ±1` —
      -- contradiction
      exfalso
      have h4 : (2 : ℕ) ^ (1 + 1) ∣ r - 1 := by
        have : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
        rw [this]
        omega
      have hnot : ¬ legendreSym r 2 = -1 := by
        intro hcon
        exact (h723b.mpr hcon) h4
      rcases legendreSym.eq_one_or_neg_one r (a := 2) h20 with h1 | h1
      · have := hsq.mp (hleg1.mp h1)
        omega
      · exact hnot h1
    · -- `r ≡ 7 (mod 8)`: `4 ∤ r − 1`, so `(2/r) = −1`, but the
      -- supplementary law gives `(2/r) = 1` — contradiction
      exfalso
      have h4 : ¬ (2 : ℕ) ^ (1 + 1) ∣ r - 1 := by
        have h4' : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
        rw [h4']
        omega
      have hleg := h723b.mp h4
      have := hsq.mpr (Or.inr h)
      have h1 := hleg1.mpr this
      rw [h1] at hleg
      exact absurd hleg (by norm_num)
  -- the base `n²` has `v_2(n² − 1) = 3` exactly
  obtain ⟨m, hm⟩ : ∃ m, n = 8 * m + 3 := ⟨n / 8, by omega⟩
  have hsq1 : ((n ^ 2 : ℕ) : ℤ) - 1
      = (2 : ℤ) ^ 3 * (8 * (m : ℤ) ^ 2 + 6 * m + 1) := by
    rw [hm]
    push_cast
    ring
  have ha1 : (2 : ℤ) ^ 3 ∣ ((n ^ 2 : ℕ) : ℤ) - 1 :=
    ⟨8 * (m : ℤ) ^ 2 + 6 * m + 1, hsq1⟩
  have ha2 : ¬ (2 : ℤ) ^ (3 + 1) ∣ ((n ^ 2 : ℕ) : ℤ) - 1 := by
    intro hd
    obtain ⟨w, hw⟩ := hd
    rw [hsq1] at hw
    have hodd8 : 8 * (m : ℤ) ^ 2 + 6 * m + 1 = 2 * w := by
      have h8 : ((2 : ℤ)) ^ 3 ≠ 0 := by norm_num
      refine mul_left_cancel₀ h8 ?_
      rw [hw]
      ring
    omega
  have h2n2 : ¬ 2 ∣ n ^ 2 := by
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
    omega
  have hengine : ∀ b : ℕ, (2 : ℤ) ^ 3 ∣ (b : ℤ) - 1 →
      ∀ D, ∃ l, b ≡ (n ^ 2) ^ l [MOD 2 ^ D] := fun b hb =>
    exists_pow_modEq_of_exact_two (by norm_num) h2n2 ha1 ha2 hb
  rcases hcase with h8 | h8
  · -- `r ≡ 1 (mod 8)`: the engine captures `r` directly
    have hb : (2 : ℤ) ^ 3 ∣ (r : ℤ) - 1 := by
      have h8d : (8 : ℕ) ∣ r - 1 := by omega
      have hc : ((8 : ℕ) : ℤ) ∣ ((r - 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr h8d
      push_cast [hr.one_lt.le] at hc
      rw [show ((2 : ℤ)) ^ 3 = 8 from by norm_num]
      exact_mod_cast hc
    intro D
    obtain ⟨l, hl⟩ := hengine r hb D
    refine ⟨2 * l, ?_⟩
    rw [pow_mul]
    exact hl
  · -- `r ≡ 3 ≡ n (mod 8)`: the engine captures `r·n`
    obtain ⟨u, hu⟩ : ∃ u, r = 8 * u + 3 := ⟨r / 8, by omega⟩
    have hb : (2 : ℤ) ^ 3 ∣ ((r * n : ℕ) : ℤ) - 1 := by
      refine ⟨8 * (u : ℤ) * m + 3 * u + 3 * m + 1, ?_⟩
      rw [hu, hm]
      push_cast
      ring
    intro D
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · exact ⟨0, by simpa using Nat.modEq_one⟩
    obtain ⟨l, hl⟩ := hengine (r * n) hb D
    -- hl : r * n ≡ (n²)^l (mod 2^D); divide by the unit `n`
    have hco : Nat.Coprime n (2 ^ D) := by
      refine Nat.Coprime.pow_right _ ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (by omega)
    have heuler : n ^ 2 ^ (D - 1) ≡ 1 [MOD 2 ^ D] := by
      have ht := Nat.ModEq.pow_totient hco
      rwa [Nat.totient_prime_pow Nat.prime_two hD,
        show (2 : ℕ) - 1 = 1 from rfl, mul_one] at ht
    refine ⟨2 * l + 2 ^ (D - 1) - 1, ?_⟩
    have hpow1 : 1 ≤ 2 ^ (D - 1) := Nat.one_le_pow _ _ (by omega)
    have hLL : n * n ^ (2 * l + 2 ^ (D - 1) - 1)
        = n ^ (2 * l) * n ^ 2 ^ (D - 1) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    have hcanc : n * r ≡ n * n ^ (2 * l + 2 ^ (D - 1) - 1)
        [MOD 2 ^ D] := by
      calc n * r = r * n := mul_comm n r
        _ ≡ (n ^ 2) ^ l [MOD 2 ^ D] := hl
        _ = n ^ (2 * l) * 1 := by rw [← pow_mul, mul_one]
        _ ≡ n ^ (2 * l) * n ^ 2 ^ (D - 1) [MOD 2 ^ D] :=
            (heuler.symm.mul_left _)
        _ = n * n ^ (2 * l + 2 ^ (D - 1) - 1) := hLL.symm
    exact Nat.ModEq.cancel_left_of_coprime hco.symm hcanc

end CL

end Azurite
