/-
  Crandall–Pomerance, Theorem 4.1.3 (Pocklington): suppose `n − 1 = F·R`
  with the complete prime factorization of `F` known, and `a` satisfies

    `a^(n−1) ≡ 1 (mod n)`  and  `gcd(a^((n−1)/q) − 1, n) = 1`
                                 for each prime `q ∣ F`.

  Then every prime factor of `n` is congruent to `1 (mod F)`.

  This is the workhorse behind partial-factorization `n − 1` tests: with
  `F > √n − 1` it forces primality outright (every prime factor exceeds
  `√n`), and it is the direct ancestor of the APR-CL idea — conditions on
  powers of a witness confining every prime divisor of `n` to an explicit
  residue class.

  The gcd condition is stated structurally: `a^((n−1)/q) − 1` is a UNIT
  of `ZMod n` (for integers, being a unit mod `n` is exactly being
  coprime to `n`).  Proof: map into `ZMod p` along `ZMod.castHom`, let
  `b` be the image of `a` and `d = orderOf b`.  Units map to units, so
  `b^((n−1)/q) ≠ 1` (else the image of the unit would be `0`).  For each
  prime `q ∣ F` with `e = v_q(F)`, the element `c = b^((n−1)/q^e)` has
  `c^(q^e) = 1` but `c^(q^(e−1)) = b^((n−1)/q) ≠ 1`, so `orderOf c` is
  exactly `q^e`; since `orderOf (b^m) ∣ orderOf b` this gives
  `q^e ∣ d`, and running over all `q` yields `F ∣ d`.  Fermat gives
  `d ∣ p − 1`, hence `F ∣ p − 1`.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace Azurite

namespace CP

/-- **Pocklington's theorem** (Crandall–Pomerance Theorem 4.1.3): if
`n − 1 = F·R` and the witness `a` satisfies `a^(n−1) = 1` in `ZMod n`
with `a^((n−1)/q) − 1` a unit of `ZMod n` for every prime `q ∣ F`, then
every prime factor of `n` is congruent to `1` mod `F`. -/
theorem pocklington {n F R : ℕ} (hn : 1 < n) (hsplit : n - 1 = F * R)
    (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1)) :
    ∀ p : ℕ, p.Prime → p ∣ n → p ≡ 1 [MOD F] := by
  intro p hp hpn
  have : Fact p.Prime := ⟨hp⟩
  have hM : n - 1 ≠ 0 := by omega
  have hF : F ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hsplit
    omega
  have hFM : F ∣ n - 1 := ⟨R, hsplit⟩
  -- move the witness into `ZMod p`
  set φ := ZMod.castHom hpn (ZMod p) with hφ
  set b := φ a with hb
  have hb1 : b ^ (n - 1) = 1 := by rw [hb, ← map_pow, ha, map_one]
  -- the gcd conditions become non-identities in `ZMod p`
  have hbq : ∀ q : ℕ, q.Prime → q ∣ F → b ^ ((n - 1) / q) ≠ 1 := by
    intro q hq hqF h1
    have hu := (hunit q hq hqF).map φ
    rw [map_sub, map_pow, map_one, ← hb, h1, sub_self] at hu
    exact not_isUnit_zero hu
  -- the order of `b` is finite, nonzero, and divides `p − 1` (Fermat)
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hb1
    exact zero_ne_one hb1
  have hdpos : 0 < orderOf b :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n - 1, by omega, hb1⟩).orderOf_pos
  have hdp : orderOf b ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0)
  -- the crux: `F` divides the order of `b`
  have hFd : F ∣ orderOf b := by
    rw [← Nat.factorization_le_iff_dvd hF hdpos.ne', Finsupp.le_def]
    intro q
    set e := F.factorization q with he
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · omega
    have hqmem : q ∈ F.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr (by omega)
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqF : q ∣ F := Nat.dvd_of_mem_primeFactors hqmem
    -- `q^e` exactly divides `F`, hence divides `n − 1`
    have hqe_dvd : q ^ e ∣ n - 1 := (Nat.ordProj_dvd F q).trans hFM
    have hq_dvd : q ∣ n - 1 := (dvd_pow_self q (by omega)).trans hqe_dvd
    obtain ⟨m, hm⟩ := hqe_dvd
    -- `c = b^m` has order exactly `q^e`
    set c := b ^ m with hc
    have hce : c ^ q ^ e = 1 := by
      rw [hc, ← pow_mul, mul_comm, ← hm, hb1]
    have hce1 : c ^ q ^ (e - 1) ≠ 1 := by
      have harith : m * q ^ (e - 1) = (n - 1) / q := by
        have : (n - 1) / q * q = n - 1 := Nat.div_mul_cancel hq_dvd
        have hqe : q ^ e = q ^ (e - 1) * q := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hqe] at hm
        have := hq.pos
        nlinarith [Nat.div_mul_cancel hq_dvd]
      rw [hc, ← pow_mul, harith]
      exact hbq q hq hqF
    obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow hq).mp
      (orderOf_dvd_of_pow_eq_one hce)
    have hje : j = e := by
      by_contra hne
      exact hce1 (orderOf_dvd_iff_pow_eq_one.mp
        (hcj ▸ pow_dvd_pow q (by omega)))
    -- `q^e = orderOf c ∣ orderOf b`
    have hdvd := orderOf_pow_dvd (x := b) m
    rw [← hc, hcj, hje] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hdpos.ne').mp hdvd
  -- assemble: `F ∣ orderOf b ∣ p − 1`
  exact ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr (hFd.trans hdp)).symm

end CP

end Azurite
