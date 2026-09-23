/-
  **Cohen–Lenstra §4 (Selection of auxiliary numbers): the function
  `e(t)` and Proposition (4.1).**

  The auxiliary numbers `t, s` of the algorithm must satisfy condition
  (2.3): `a^t ≡ 1 (mod s)` for every integer `a` coprime to `s` — that
  is, the exponent of `(ℤ/s)^*` divides `t`.  The paper packages the
  admissible `s` through

    `e(t) = 2`                                        for `t` odd,
    `e(t) = 2 · ∏_{q prime, q−1 ∣ t} q^(v_q(t)+1)`    for `t` even,

  and proves **(4.1): condition (2.3) holds iff `s ∣ e(t)`** — for odd
  `t` by evaluating at `a = −1`, and for even `t` by reduction to prime
  powers `s = q^m` using the structure of `(ℤ/q^m)^*` (cyclic of order
  `(q−1)q^(m−1)` for `q` odd; `C₂ × C_{2^(m−2)}` for `q = 2, m ≥ 3`).

  We state the condition on the unit group (`∀ u : (ZMod s)ˣ, u^t = 1`)
  and derive the coprime-naturals congruence form.  The proof follows
  the paper: the odd case via `−1`; the even case by
  `Nat.recOnPosPrimePosCoprime` with the CRT splitting of the unit
  group, Mathlib's cyclicity of `(ZMod (p^k))ˣ` for odd `p`, and for
  `p = 2` the element `5` of order `2^(k−2)` (Mathlib) against an
  elementary two-adic upper bound `a^(2^(k−2)) ≡ 1 (mod 2^k)` for odd
  `a`.  Table 1 spot-checks appear as guards.
-/
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient

namespace Azurite

namespace CL

open Finset

/-- **The Cohen–Lenstra `e(t)`**: `2` for odd `t`, and
`2 · ∏_{q prime, q−1 ∣ t} q^(v_q(t)+1)` for even `t` (the product taken
over the primes `q` with `q − 1` dividing `t`, indexed here by the
divisors `d = q − 1` of `t`).  By Proposition (4.1) the admissible
moduli `s` for condition (2.3) are exactly the divisors of `e(t)`. -/
def e (t : ℕ) : ℕ :=
  if Odd t then 2
  else 2 * ∏ d ∈ t.divisors.filter (fun d => (d + 1).Prime),
      (d + 1) ^ (t.factorization (d + 1) + 1)

theorem e_ne_zero (t : ℕ) : e t ≠ 0 := by
  rw [e]
  split_ifs
  · exact two_ne_zero
  · exact mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.mpr
      fun d _ => pow_ne_zero _ (Nat.succ_ne_zero d))

/-! ### The prime factorization of `e(t)` (even `t`) -/

/-- For even `t ≠ 0`, the factorization of `e t` as a `Finsupp`-sum. -/
private theorem factorization_e_eq (t : ℕ) (ht2 : ¬ Odd t) {p : ℕ}
    (_hp : p.Prime) :
    (e t).factorization p
      = (if p = 2 then 1 else 0)
        + ∑ d ∈ t.divisors.filter (fun d => (d + 1).Prime),
            if d + 1 = p then t.factorization (d + 1) + 1 else 0 := by
  rw [e, ite_eq_right ht2,
    Nat.factorization_mul two_ne_zero (Finset.prod_ne_zero_iff.mpr
      fun d _ => pow_ne_zero _ (Nat.succ_ne_zero d)),
    Nat.factorization_prod fun d _ => pow_ne_zero _ (Nat.succ_ne_zero d)]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply]
  congr 1
  · rw [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.Prime.factorization_pow (Finset.mem_filter.mp hd).2,
      Finsupp.single_apply]

/-- For even `t ≠ 0` and an odd prime `p`:
`v_p(e t) = v_p(t) + 1` if `p − 1 ∣ t`, and `0` otherwise. -/
theorem factorization_e_odd_prime {t p : ℕ} (ht2 : ¬ Odd t) (ht0 : t ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (e t).factorization p
      = if (p - 1) ∣ t then t.factorization p + 1 else 0 := by
  rw [factorization_e_eq t ht2 hp, ite_eq_right hp2, zero_add]
  by_cases hdvd : (p - 1) ∣ t
  · rw [ite_eq_left hdvd,
      Finset.sum_eq_single_of_mem (p - 1)
        (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, ht0⟩, by
          rw [Nat.sub_add_cancel hp.one_lt.le]; exact hp⟩)
        (fun d _ hd => ite_eq_right fun h => hd (by omega)),
      ite_eq_left (Nat.sub_add_cancel hp.one_lt.le),
      Nat.sub_add_cancel hp.one_lt.le]
  · rw [ite_eq_right hdvd]
    refine Finset.sum_eq_zero fun d hd => ite_eq_right fun h => hdvd ?_
    have hdt := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hdp : d = p - 1 := by omega
    rwa [← hdp]

/-- For even `t ≠ 0`: `v_2(e t) = v_2(t) + 2` (the leading `2` plus the
`q = 2` factor, present since `1 = 2 − 1` always divides `t`). -/
theorem factorization_e_two {t : ℕ} (ht2 : ¬ Odd t) (ht0 : t ≠ 0) :
    (e t).factorization 2 = t.factorization 2 + 2 := by
  rw [factorization_e_eq t ht2 Nat.prime_two, ite_eq_left rfl,
    Finset.sum_eq_single_of_mem 1
      (Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr ht0,
        show ((1 : ℕ) + 1).Prime from Nat.prime_two⟩)
      (fun d _ hd => ite_eq_right fun h => hd (by omega)),
    ite_eq_left rfl, show (1 : ℕ) + 1 = 2 from rfl]
  omega

/-! ### An upper bound for `e(t)` -/

/-- The paper's growth bound `e(t) ≤ 2t · ∏_{d ∣ t} (d + 1)` (used with
divisor-function estimates to bound how small `t` can be chosen with
`e(t) > n^(1/2)`): each factor `q^(v_q(t)+1)` splits as `q^(v_q(t)) · q`;
the first parts are powers of distinct primes each dividing `t`, so their
product divides `t`, while the second parts are among the `d + 1` for
`d ∣ t`. -/
theorem e_le {t : ℕ} (ht : 0 < t) :
    e t ≤ 2 * t * ∏ d ∈ t.divisors, (d + 1) := by
  have hone : (1 : ℕ) ≤ ∏ d ∈ t.divisors, (d + 1) :=
    Finset.one_le_prod fun d _ => Nat.le_add_left 1 d
  rw [e]
  split_ifs with h
  · calc (2 : ℕ) = 2 * 1 * 1 := by ring
      _ ≤ 2 * t * ∏ d ∈ t.divisors, (d + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht) hone
  · set D := t.divisors.filter (fun d => (d + 1).Prime) with hD
    have hsplit : ∏ d ∈ D, (d + 1) ^ (t.factorization (d + 1) + 1)
        = (∏ d ∈ D, (d + 1) ^ t.factorization (d + 1)) * ∏ d ∈ D, (d + 1) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun d _ => pow_succ _ _
    -- the prime-power parts multiply to a divisor of `t`
    have hdvd : (∏ d ∈ D, (d + 1) ^ t.factorization (d + 1)) ∣ t := by
      rw [show ∏ d ∈ D, (d + 1) ^ t.factorization (d + 1)
            = ∏ p ∈ D.image (· + 1), p ^ t.factorization p from
          (Finset.prod_image (g := fun d => d + 1)
            (f := fun p => p ^ t.factorization p)
            (add_left_injective 1).injOn).symm,
        ← Finset.prod_filter_of_ne
          (p := fun p => t.factorization p ≠ 0)
          (fun p _ hp1 => fun h0 => hp1 (by rw [h0, pow_zero]))]
      calc ∏ p ∈ (D.image (· + 1)).filter (fun p => t.factorization p ≠ 0),
              p ^ t.factorization p
          ∣ ∏ p ∈ t.primeFactors, p ^ t.factorization p := by
            refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
            obtain ⟨hpi, hp0⟩ := Finset.mem_filter.mp hp
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hpi
            exact Nat.mem_primeFactors.mpr
              ⟨(Finset.mem_filter.mp hd).2,
                Nat.dvd_of_factorization_pos hp0, ht.ne'⟩
        _ = t := by
            rw [← Nat.support_factorization, ← Finsupp.prod]
            exact Nat.prod_factorization_pow_eq_self ht.ne'
    calc 2 * ∏ d ∈ D, (d + 1) ^ (t.factorization (d + 1) + 1)
        = 2 * (∏ d ∈ D, (d + 1) ^ t.factorization (d + 1)) * ∏ d ∈ D, (d + 1) := by
          rw [hsplit, mul_assoc]
      _ ≤ 2 * t * ∏ d ∈ t.divisors, (d + 1) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul_left 2 (Nat.le_of_dvd ht hdvd))
            (Finset.prod_le_prod_of_subset_of_one_le
              (Finset.filter_subset _ _) fun d _ _ => Nat.le_add_left 1 d)

/-! ### The unit-group condition at prime powers -/

/-- If the unit-group order divides `t`, every unit satisfies
`u^t = 1`. -/
private theorem pow_eq_one_of_card_dvd {G : Type _} [Group G] [Fintype G]
    {t : ℕ} (h : Fintype.card G ∣ t) (u : G) : u ^ t = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, pow_card_eq_one, one_pow]

/-- **Odd prime powers**: the condition at `s = p^k` is equivalent to
`p^(k−1)(p−1) ∣ t` — the unit group is cyclic of that order. -/
theorem forall_units_pow_eq_one_prime_pow_iff {p k t : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 0 < k) :
    (∀ u : (ZMod (p ^ k))ˣ, u ^ t = 1) ↔ p ^ (k - 1) * (p - 1) ∣ t := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hcard : Fintype.card (ZMod (p ^ k))ˣ = p ^ (k - 1) * (p - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]
  constructor
  · intro h
    have := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ k))ˣ)
    have hord : orderOf g = p ^ (k - 1) * (p - 1) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        hcard]
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (h g)
  · intro h u
    exact pow_eq_one_of_card_dvd (hcard ▸ h) u

/-- Two-adic congruence: for odd `a` and `m ≥ 1`,
`a^(2^m) ≡ 1 (mod 2^(m+2))`. -/
private theorem two_pow_dvd_pow_sub_one {m : ℕ} (hm : 1 ≤ m) (a : ℤ)
    (ha : Odd a) : (2 ^ (m + 2) : ℤ) ∣ a ^ 2 ^ m - 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨j, rfl⟩ := ha
    have h2 : Even (j * (j + 1)) := Int.even_mul_succ_self j
    obtain ⟨c, hc⟩ := h2
    refine ⟨c, by push_cast; ring_nf; nlinarith [hc]⟩
  | succ m hm ih =>
    have hsplit : a ^ 2 ^ (m + 1) - 1
        = (a ^ 2 ^ m - 1) * (a ^ 2 ^ m + 1) := by
      rw [pow_succ, pow_mul]; ring
    have heven : (2 : ℤ) ∣ a ^ 2 ^ m + 1 := by
      have : Odd (a ^ 2 ^ m) := ha.pow
      obtain ⟨c, hc⟩ := this
      exact ⟨c + 1, by omega⟩
    rw [hsplit, show m + 1 + 2 = (m + 2) + 1 from rfl, pow_succ]
    exact mul_dvd_mul ih heven

/-- Upper bound at `2^k`, `k ≥ 3`: every unit satisfies
`u^(2^(k−2)) = 1`. -/
private theorem units_two_pow_pow_eq_one {k : ℕ} (hk : 3 ≤ k)
    (u : (ZMod (2 ^ k))ˣ) : u ^ 2 ^ (k - 2) = 1 := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hodd : Odd (((u : ZMod (2 ^ k)).val : ℤ)) := by
    have hco := ZMod.val_coe_unit_coprime u
    rw [Int.odd_iff]
    have h2 : ¬ (2 ∣ (u : ZMod (2 ^ k)).val) := by
      intro h2
      have : (2 : ℕ) ∣ Nat.gcd (u : ZMod (2 ^ k)).val (2 ^ k) :=
        Nat.dvd_gcd h2 (dvd_pow_self 2 (by omega))
      rw [hco] at this
      omega
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨c, hc⟩ := two_pow_dvd_pow_sub_one (m := m) (by omega)
    (((u : ZMod (2 ^ (m + 2))).val : ℤ)) hodd
  have hA : (((u : ZMod (2 ^ (m + 2))).val : ℤ)) ^ 2 ^ m
      = 1 + 2 ^ (m + 2) * c := by omega
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  calc (u : ZMod (2 ^ (m + 2))) ^ 2 ^ (m + 2 - 2)
      = ((((u : ZMod (2 ^ (m + 2))).val : ℤ) ^ 2 ^ m : ℤ)
          : ZMod (2 ^ (m + 2))) := by
        rw [show m + 2 - 2 = m from rfl, Int.cast_pow]
        congr 1
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
    _ = ((1 + 2 ^ (m + 2) * c : ℤ) : ZMod (2 ^ (m + 2))) := by rw [hA]
    _ = 1 := by
        rw [Int.cast_add, Int.cast_one, Int.cast_mul]
        have h0 : ((2 ^ (m + 2) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
          exact_mod_cast ZMod.natCast_self (2 ^ (m + 2))
        rw [h0, zero_mul, add_zero]

/-- **The prime `2`**: for even `t ≠ 0`, the condition at `s = 2^k` is
equivalent to `k ≤ v_2(t) + 2`. -/
theorem forall_units_pow_eq_one_two_pow_iff {k t : ℕ} (ht2 : ¬ Odd t)
    (ht0 : t ≠ 0) :
    (∀ u : (ZMod (2 ^ k))ˣ, u ^ t = 1) ↔ k ≤ t.factorization 2 + 2 := by
  have hv : 1 ≤ t.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ht0).mp
      (by simpa using (Nat.not_odd_iff_even.mp ht2).two_dvd)
  by_cases hk : k ≤ 3
  · -- small `k`: every unit of `ZMod (2^k)` squares to `1`, and `t` is
    -- even, so both sides always hold
    refine iff_of_true (fun u => ?_) (by omega)
    obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp ht2
    have hsq : u ^ 2 = 1 := by
      interval_cases k <;> revert u <;> decide
    calc u ^ t = (u ^ 2) ^ c := by rw [← pow_mul]; congr 1; omega
    _ = 1 := by rw [hsq, one_pow]
  · -- `k ≥ 4 ≥ 3`: exact characterization via `5` and the upper bound
    have hk3 : 3 ≤ k := by omega
    constructor
    · intro h
      -- the unit `5` has order `2^(k−2)`
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      have : NeZero (2 ^ (m + 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      have h5 : IsUnit (5 : ZMod (2 ^ (m + 2))) := by
        have h5c : ((5 : ℕ) : ZMod (2 ^ (m + 2))) = 5 := by push_cast; ring
        rw [← h5c, ZMod.isUnit_iff_coprime]
        have hpos : 0 < m + 2 := by omega
        exact (Nat.coprime_pow_right_iff hpos 5 2).mpr (by norm_num)
      have h5t : (5 : ZMod (2 ^ (m + 2))) ^ t = 1 := by
        have := h h5.unit
        have hcoe := congrArg (Units.val) this
        rwa [Units.val_pow_eq_pow_val, h5.unit_spec, Units.val_one] at hcoe
      have hdvd : orderOf (5 : ZMod (2 ^ (m + 2))) ∣ t :=
        orderOf_dvd_of_pow_eq_one h5t
      rw [ZMod.orderOf_five] at hdvd
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        ht0).mp hdvd
      omega
    · intro h u
      have hdvd : 2 ^ (k - 2) ∣ t :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ht0).mpr
          (by omega)
      obtain ⟨c, rfl⟩ := hdvd
      rw [pow_mul, units_two_pow_pow_eq_one hk3, one_pow]

/-! ### CRT splitting of the condition -/

/-- The unit group of `ZMod (a·b)` splits along coprimality. -/
noncomputable def unitsCRT {a b : ℕ} (h : a.Coprime b) :
    (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits

/-- The condition (2.3) splits along coprime factorizations of `s`. -/
theorem forall_units_pow_eq_one_mul_iff {a b t : ℕ} (h : a.Coprime b) :
    (∀ u : (ZMod (a * b))ˣ, u ^ t = 1)
      ↔ (∀ u : (ZMod a)ˣ, u ^ t = 1) ∧ (∀ u : (ZMod b)ˣ, u ^ t = 1) := by
  constructor
  · intro hab
    constructor
    · intro u
      have := hab ((unitsCRT h).symm (u, 1))
      have hmap := congrArg (unitsCRT h) this
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at hmap
      exact congrArg Prod.fst hmap
    · intro u
      have := hab ((unitsCRT h).symm (1, u))
      have hmap := congrArg (unitsCRT h) this
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at hmap
      exact congrArg Prod.snd hmap
  · rintro ⟨ha, hb⟩ u
    have : (unitsCRT h) (u ^ t) = 1 := by
      rw [map_pow]
      exact Prod.ext (by simpa using ha ((unitsCRT h) u).1)
        (by simpa using hb ((unitsCRT h) u).2)
    have := congrArg (unitsCRT h).symm this
    rwa [MulEquiv.symm_apply_apply, map_one] at this

/-! ### The odd-`t` case -/

/-- For odd `t`, the condition holds iff `s ∣ 2` — evaluate at
`a = −1`. -/
theorem forall_units_pow_eq_one_iff_of_odd {s t : ℕ} (hto : Odd t) :
    (∀ u : (ZMod s)ˣ, u ^ t = 1) ↔ s ∣ 2 := by
  constructor
  · intro h
    have hneg := h (-1)
    rw [hto.neg_one_pow] at hneg
    have hcoe := congrArg (Units.val) hneg
    rw [Units.val_neg, Units.val_one] at hcoe
    have h2 : ((2 : ℕ) : ZMod s) = 0 := by
      push_cast
      linear_combination -hcoe
    exact (ZMod.natCast_eq_zero_iff 2 s).mp h2
  · intro hs u
    rcases (Nat.dvd_prime Nat.prime_two).mp hs with rfl | rfl
    · exact Subsingleton.elim _ _
    · refine pow_eq_one_of_card_dvd ?_ u
      rw [ZMod.card_units_eq_totient, Nat.totient_prime Nat.prime_two]
      exact one_dvd t

/-! ### Proposition (4.1) -/

/-- **Cohen–Lenstra Proposition (4.1)**, unit-group form: for positive
`t` and `s`, `a^t ≡ 1 (mod s)` holds for all `a` coprime to `s` iff
`s ∣ e(t)`. -/
theorem proposition_4_1 {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    (∀ u : (ZMod s)ˣ, u ^ t = 1) ↔ s ∣ e t := by
  rcases Nat.even_or_odd t with hte | hto
  case inr =>
    rw [e, ite_eq_left hto]
    exact forall_units_pow_eq_one_iff_of_odd hto
  have ht2 : ¬ Odd t := Nat.not_odd_iff_even.mpr hte
  have ht0 : t ≠ 0 := ht.ne'
  induction s using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd hs (lt_irrefl 0)
  | one =>
    exact iff_of_true (fun u => Subsingleton.elim _ _) (one_dvd _)
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [forall_units_pow_eq_one_two_pow_iff ht2 ht0,
        Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
          (e_ne_zero t), factorization_e_two ht2 ht0]
    · rw [forall_units_pow_eq_one_prime_pow_iff hp' hp2 hk,
        Nat.Prime.pow_dvd_iff_le_factorization hp' (e_ne_zero t),
        factorization_e_odd_prime ht2 ht0 hp' hp2]
      have hcop : (p ^ (k - 1)).Coprime (p - 1) := by
        refine Nat.Coprime.pow_left _ ?_
        rw [Nat.coprime_self_sub_right hp'.pos]
        simp
      constructor
      · intro h
        have h1 : p ^ (k - 1) ∣ t := (dvd_mul_right _ _).trans h
        have h2 : (p - 1) ∣ t := (dvd_mul_left _ _).trans h
        rw [ite_eq_left h2]
        have := (Nat.Prime.pow_dvd_iff_le_factorization hp' ht0).mp h1
        omega
      · intro h
        by_cases h2 : (p - 1) ∣ t
        · rw [ite_eq_left h2] at h
          refine hcop.mul_dvd_of_dvd_of_dvd ?_ h2
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp' ht0).mpr
            (by omega)
        · rw [ite_eq_right h2] at h
          omega
  | coprime a b ha hb hab iha ihb =>
    have iha' := iha (by omega)
    have ihb' := ihb (by omega)
    rw [forall_units_pow_eq_one_mul_iff hab]
    constructor
    · rintro ⟨h1, h2⟩
      exact hab.mul_dvd_of_dvd_of_dvd (iha'.mp h1) (ihb'.mp h2)
    · intro h
      exact ⟨iha'.mpr ((dvd_mul_right a b).trans h),
        ihb'.mpr ((dvd_mul_left b a).trans h)⟩

/-- **Proposition (4.1)**, coprime-naturals congruence form: for
positive `t` and `s`, `a^t ≡ 1 (mod s)` for every natural `a` coprime
to `s` iff `s ∣ e(t)`. -/
theorem proposition_4_1' {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    (∀ a : ℕ, a.Coprime s → a ^ t ≡ 1 [MOD s]) ↔ s ∣ e t := by
  have : NeZero s := ⟨hs.ne'⟩
  rw [← proposition_4_1 hs ht]
  constructor
  · intro h u
    have hval := h (u : ZMod s).val (ZMod.val_coe_unit_coprime u)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hcast : (((u : ZMod s).val ^ t : ℕ) : ZMod s) = ((1 : ℕ) : ZMod s) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hval
    rw [Nat.cast_pow, ZMod.natCast_val, ZMod.cast_id, Nat.cast_one] at hcast
    exact hcast
  · intro h a hco
    have hu := h (ZMod.unitOfCoprime a hco)
    have hcoe := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
      at hcoe
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    rw [Nat.cast_pow, Nat.cast_one]
    exact hcoe

end CL

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

-- Table 1 spot checks (exact values; the paper prints approximations
-- from `e(60)` onward)
#guard Azurite.CL.e 2 = 24
#guard Azurite.CL.e 12 = 65520
#guard Azurite.CL.e 60 = 6814407600

-- Table 2: the complete prime factorization of `e(5040)`
-- (`5040 = 2^4·3^2·5·7`; the 27 primes `q` with `q − 1 ∣ 5040`)
#guard Azurite.CL.e 5040
  = 2^6 * 3^3 * 5^2 * 7^2 * 11 * 13 * 17 * 19 * 29 * 31 * 37 * 41 * 43
    * 61 * 71 * 73 * 113 * 127 * 181 * 211 * 241 * 281 * 337 * 421
    * 631 * 1009 * 2521

end Tests
