/-
  **Soundness of the Lucas–Lehmer stage** (`Azurite/APRCL/LucasLehmer.lean`):
  `llCheck n cert = some true` implies `n` prime and `llCheck n cert = some false`
  implies `n` composite.

  The primality half is the generalized Theorem (6.3) `theorem_6_3_LL` with
  `s₁ = F`, `s₂ = 1`, `t' = 2` followed by the final trial division
  `step5_prime`.  Its per-prime-factor hypothesis is assembled from

  * Pocklington (`CP.pocklington`) for the odd primes of `n − 1` (Test (4.2)),
  * `test_4_3_confinement` for the odd primes of `n + 1` (Test (4.3)), with
    the same `ε(r)` (the Legendre symbol of the discriminant at `r`),
  * the strengthened `2`-adic statements `c1_two_adic_strong` /
    `c2_two_adic_strong` for the full `2`-part of `n² − 1`.

  The compositeness half is the collection of "computed value contradicts
  a theorem about prime `n`" facts transported through `toZMod`/`toQuad`.
-/
import Azurite.APRCL.LucasLehmer
import Azurite.AzZMod.Equiv.Quad
import Azurite.AzNat.Equiv.JacobiSym
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.Square
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Compare
import Azurite.CohenLenstra.Theorem_6_3_LL
import Azurite.CohenLenstra.Algorithm_12_1
import Azurite.CohenLenstra.Impl_5_3_Lift
import Azurite.CohenLenstra.Impl_4_5
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3

namespace Azurite

namespace APRCL

open AzZMod Polynomial

/-! ### Two-adic strengthening -/

/-- Two numbers `≡ 1 (mod 2^v)` but `≢ 1 (mod 2^(v+1))` agree modulo `2^(v+1)`. -/
theorem modEq_two_pow_succ_of_not_dvd {r n v : ℕ} (hr1 : 1 ≤ r) (hn1 : 1 ≤ n)
    (hr : 2 ^ v ∣ r - 1) (hr' : ¬ 2 ^ (v + 1) ∣ r - 1)
    (hn : 2 ^ v ∣ n - 1) (hn' : ¬ 2 ^ (v + 1) ∣ n - 1) : r ≡ n [MOD 2 ^ (v + 1)] := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hn
  have ha2 : a % 2 = 1 := by
    by_contra h
    apply hr'
    rw [ha, pow_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega))
  have hb2 : b % 2 = 1 := by
    by_contra h
    apply hn'
    rw [hb, pow_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega))
  obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' + 1 := ⟨a / 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' + 1 := ⟨b / 2, by omega⟩
  have hr' : r = 2 ^ v + 1 + 2 ^ (v + 1) * a' := by
    have : 2 ^ v * (2 * a' + 1) = 2 ^ v + 2 ^ (v + 1) * a' := by ring
    omega
  have hn'' : n = 2 ^ v + 1 + 2 ^ (v + 1) * b' := by
    have : 2 ^ v * (2 * b' + 1) = 2 ^ v + 2 ^ (v + 1) * b' := by ring
    omega
  rw [hr', hn'']
  simp [Nat.ModEq, Nat.add_mul_mod_self_left]

/-- `2^(e+1) ∣ 2·(m·k)` with `m` odd forces `e ≤ v₂(k)`. -/
theorem le_factorization_two_of_dvd {e m k : ℕ} (hm : ¬ 2 ∣ m) (hk : k ≠ 0)
    (h : 2 ^ (e + 1) ∣ 2 * (m * k)) : e ≤ k.factorization 2 := by
  have h1 : 2 ^ e ∣ m * k := by
    rw [pow_succ, mul_comm 2 (m * k)] at h
    exact Nat.dvd_of_mul_dvd_mul_right two_pos h
  have h2 : 2 ^ e ∣ k :=
    (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)).dvd_of_dvd_mul_left
      h1
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hk).mp h2

open Classical in
/-- **(c1), full `2`-part**: for `n ≡ 1 (mod 4)` with `a^((n−1)/2) ≡ −1`, every prime
`r ∣ n` satisfies `r ≡ n^ε(r) (mod 2^e)` for every `2^e ∣ n² − 1`. -/
theorem two_adic_c1 {n r : ℕ} (hn4 : n % 4 = 1) (hn1 : 1 < n) (hr : r.Prime) (hrn : r ∣ n)
    {a : ℤ} (ha : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1)) {e : ℕ} (he : 2 ^ e ∣ n ^ 2 - 1) :
    r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) (0 : ZMod n)) ^ 2
        + 4 * ZMod.castHom hrn (ZMod r) ((a : ℤ) : ZMod n)) then 0 else 1) [MOD 2 ^ e] := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  obtain ⟨hdvd, hiff⟩ := CL.c1_two_adic hodd hr hrn ha
  set v := (n - 1).factorization 2 with hv
  -- the congruence modulo `2^(v+1)`
  have hstrong : r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) (0 : ZMod n)) ^ 2
      + 4 * ZMod.castHom hrn (ZMod r) ((a : ℤ) : ZMod n)) then 0 else 1) [MOD 2 ^ (v + 1)] := by
    by_cases hsq : IsSquare ((ZMod.castHom hrn (ZMod r) (0 : ZMod n)) ^ 2
      + 4 * ZMod.castHom hrn (ZMod r) ((a : ℤ) : ZMod n))
    · rw [if_pos hsq, pow_zero]
      have h1 : 2 ^ (v + 1) ∣ r - 1 := by
        by_contra h
        exact hiff.mp h hsq
      exact ((Nat.modEq_iff_dvd' hr.one_lt.le).mpr h1).symm
    · rw [if_neg hsq, pow_one]
      exact modEq_two_pow_succ_of_not_dvd hr.one_lt.le hn1.le hdvd (hiff.mpr hsq)
        (Nat.ordProj_dvd (n - 1) 2) (Nat.pow_succ_factorization_not_dvd (by omega) Nat.prime_two)
  -- `e ≤ v + 1`
  have hev : e ≤ v + 1 := by
    rcases e with _ | e
    · omega
    obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 1 := ⟨n / 4, by omega⟩
    have hsplit : (4 * q + 1) ^ 2 - 1 = 2 * ((2 * q + 1) * (4 * q + 1 - 1)) := by
      rw [show 4 * q + 1 - 1 = 4 * q by omega]
      have : (4 * q + 1) ^ 2 = 2 * ((2 * q + 1) * (4 * q)) + 1 := by ring
      omega
    rw [hsplit] at he
    have := le_factorization_two_of_dvd (by omega) (by omega) he
    omega
  exact Nat.ModEq.of_dvd (pow_dvd_pow 2 hev) hstrong

open Classical in
/-- **(c2), full `2`-part**: for `n ≡ 3 (mod 4)` with `α^(n+1) = −1`, every prime `r ∣ n`
satisfies `r ≡ n^ε(r) (mod 2^e)` for every `2^e ∣ n² − 1`. -/
theorem two_adic_c2 {n r : ℕ} (hn3 : n % 4 = 3) (hr : r.Prime) (hrn : r ∣ n) {u : ZMod n}
    (hα : (AdjoinRoot.root (X ^ 2 - C u * X - C (1 : ZMod n) : Polynomial (ZMod n))) ^ (n + 1)
      = -1) {e : ℕ} (he : 2 ^ e ∣ n ^ 2 - 1) :
    r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) then 0 else 1) [MOD 2 ^ e] := by
  set v := (n + 1).factorization 2 with hv
  have hv2 : 2 ≤ v :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega)
  obtain ⟨hbase, hsplit, hinert⟩ := CL.c2_two_adic hn3 hr hrn hα hv2 (Nat.ordProj_dvd (n + 1) 2)
  have hstrong : r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) then 0 else 1)
      [MOD 2 ^ (v + 1)] := by
    by_cases hsq : IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4)
    · rw [if_pos hsq, pow_zero]
      exact ((Nat.modEq_iff_dvd' hr.one_lt.le).mpr (hsplit hsq)).symm
    · rw [if_neg hsq, pow_one]
      exact hinert hsq
  have hev : e ≤ v + 1 := by
    rcases e with _ | e
    · omega
    obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 3 := ⟨n / 4, by omega⟩
    have hsplit' : (4 * q + 3) ^ 2 - 1 = 2 * ((2 * q + 1) * (4 * q + 3 + 1)) := by
      have : (4 * q + 3) ^ 2 = 2 * ((2 * q + 1) * (4 * q + 3 + 1)) + 1 := by ring
      omega
    rw [hsplit'] at he
    have := le_factorization_two_of_dvd (by omega) (by omega) he
    omega
  exact Nat.ModEq.of_dvd (pow_dvd_pow 2 hev) hstrong

/-! ### Products of prime powers given as lists -/

/-- `∏ p^e` over a list of `(p, e)` pairs. -/
def prodPow (L : List (ℕ × ℕ)) : ℕ := (L.map fun pe => pe.1 ^ pe.2).prod

@[simp] theorem prodPow_nil : prodPow [] = 1 := rfl

@[simp] theorem prodPow_cons (pe : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    prodPow (pe :: L) = pe.1 ^ pe.2 * prodPow L := by
  simp [prodPow]

theorem prodPow_append (L₁ L₂ : List (ℕ × ℕ)) :
    prodPow (L₁ ++ L₂) = prodPow L₁ * prodPow L₂ := by
  simp [prodPow]

theorem prodPow_pos {L : List (ℕ × ℕ)} (hp : ∀ pe ∈ L, 0 < pe.1) : 0 < prodPow L := by
  induction L with
  | nil => simp
  | cons pe L ih =>
    rw [prodPow_cons]
    exact Nat.mul_pos (pow_pos (hp pe (List.mem_cons_self ..)) _)
      (ih fun x hx => hp x (List.mem_cons_of_mem _ hx))

theorem dvd_prodPow_of_mem {L : List (ℕ × ℕ)} {pe : ℕ × ℕ} (h : pe ∈ L) :
    pe.1 ^ pe.2 ∣ prodPow L :=
  List.dvd_prod (List.mem_map_of_mem h)

/-- A prime dividing `∏ p^e` (all `p` prime) is one of the `p` with `e > 0`. -/
theorem prime_dvd_prodPow {L : List (ℕ × ℕ)} (hp : ∀ pe ∈ L, pe.1.Prime) {q : ℕ}
    (hq : q.Prime) (h : q ∣ prodPow L) : ∃ pe ∈ L, q = pe.1 ∧ 0 < pe.2 := by
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hq)).mp h
  obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp hx
  refine ⟨pe, hpe, (Nat.prime_dvd_prime_iff_eq hq (hp pe hpe)).mp (hq.dvd_of_dvd_pow hqx), ?_⟩
  rcases Nat.eq_zero_or_pos pe.2 with h0 | h0
  · rw [h0, pow_zero] at hqx
    exact absurd (Nat.dvd_one.mp hqx) hq.one_lt.ne'
  · exact h0

theorem coprime_prodPow {L : List (ℕ × ℕ)} {q : ℕ} (hq : q.Prime)
    (h : ∀ pe ∈ L, pe.1.Prime ∧ pe.1 ≠ q) : Nat.Coprime q (prodPow L) := by
  refine Nat.coprime_list_prod_right_iff.mpr fun x hx => ?_
  obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp hx
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq (h pe hpe).1).mpr (h pe hpe).2.symm)

/-- With distinct primes, `∏ p^e ∣ m` follows from `p^e ∣ m` for each factor. -/
theorem prodPow_dvd {L : List (ℕ × ℕ)} (hp : ∀ pe ∈ L, pe.1.Prime)
    (hnd : (L.map Prod.fst).Nodup) {m : ℕ} (h : ∀ pe ∈ L, pe.1 ^ pe.2 ∣ m) : prodPow L ∣ m := by
  induction L with
  | nil => simp
  | cons pe L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [prodPow_cons]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h pe (List.mem_cons_self ..))
      (ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hnd.2
        fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine Nat.Coprime.pow_left _ (coprime_prodPow (hp pe (List.mem_cons_self ..)) fun x hx =>
      ⟨hp x (List.mem_cons_of_mem _ hx), fun hxe => hnd.1 ?_⟩)
    rw [← hxe]
    exact List.mem_map_of_mem hx

theorem factorization_prodPow_of_not_mem {L : List (ℕ × ℕ)} (hp : ∀ pe ∈ L, pe.1.Prime) {q : ℕ}
    (hq : q.Prime) (h : ∀ pe ∈ L, pe.1 ≠ q) : (prodPow L).factorization q = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  obtain ⟨pe, hpe, hqe, -⟩ := prime_dvd_prodPow hp hq hd
  exact h pe hpe hqe.symm

/-- With distinct primes, the `p`-adic valuation of `∏ p^e` is the listed `e`. -/
theorem factorization_prodPow_of_mem {L : List (ℕ × ℕ)} (hp : ∀ pe ∈ L, pe.1.Prime)
    (hnd : (L.map Prod.fst).Nodup) {pe : ℕ × ℕ} (hmem : pe ∈ L) :
    (prodPow L).factorization pe.1 = pe.2 := by
  induction L with
  | nil => simp at hmem
  | cons pe' L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have hp' := hp pe' (List.mem_cons_self ..)
    have hpL : ∀ x ∈ L, x.1.Prime := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    have hpos : 0 < prodPow L := prodPow_pos fun x hx => (hpL x hx).pos
    rw [prodPow_cons, Nat.factorization_mul (pow_pos hp'.pos _).ne' hpos.ne', Finsupp.add_apply,
      hp'.factorization_pow, Finsupp.single_apply]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [if_pos rfl, factorization_prodPow_of_not_mem hpL hp' fun x hx hxe => hnd.1 ?_]
      · simp
      · rw [← hxe]
        exact List.mem_map_of_mem hx
    · rw [ih hpL hnd.2 hmem', if_neg fun hxe => hnd.1 ?_, zero_add]
      rw [hxe]
      exact List.mem_map_of_mem hmem'

/-! ### The core primality argument -/

theorem sub_one_dvd_sq_sub_one {N : ℕ} (hN : 1 ≤ N) : N - 1 ∣ N ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  refine ⟨m + 2, ?_⟩
  rw [Nat.add_sub_cancel]
  have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
  omega

theorem add_one_dvd_sq_sub_one (N : ℕ) : N + 1 ∣ N ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  refine ⟨m, ?_⟩
  have : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
  omega

/-- **Pocklington for one prime power** `p^e ∣ n − 1`: Test (4.2) confines every prime
factor `r` of `n` to `r ≡ 1 (mod p^e)`. -/
theorem pocklington_prime_pow {N p e : ℕ} (hN : 1 < N) (hp : p.Prime) (hpe : p ^ e ∣ N - 1)
    {X : ZMod N} (hx1 : X ^ (N - 1) = 1) (hunit : IsUnit (X ^ ((N - 1) / p) - 1)) :
    ∀ r, r.Prime → r ∣ N → r ≡ 1 [MOD p ^ e] :=
  CP.pocklington hN (Nat.mul_div_cancel' hpe).symm X hx1 fun q hq hqF => by
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqF)]
    exact hunit

open Classical in
/-- **The Lucas–Lehmer stage proves primality**: with the checks decoded into their
mathematical content, `n < F²` and the `t' = 2` trial division give `n` prime. -/
theorem prime_of_ll {N : ℕ} (hN : 2 < N) (hodd : N % 2 = 1) {U A : ZMod N}
    (hring : (N % 4 = 1 ∧ U = 0 ∧ ∃ a : ℤ, A = (a : ZMod N) ∧
        Int.ModEq (N : ℤ) (a ^ ((N - 1) / 2)) (-1)) ∨
      (N % 4 = 3 ∧ A = 1 ∧ ∃ w : ℕ, U = (w : ZMod N) ∧
        (AdjoinRoot.root (X ^ 2 - C (w : ZMod N) * X - C 1 : Polynomial (ZMod N))) ^ (N + 1)
          = -1))
    {Lm Lp : List (ℕ × ℕ)} {e2 : ℕ}
    (hnd : ((Lm ++ Lp).map Prod.fst).Nodup)
    (hm : ∀ pe ∈ Lm, pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ N - 1)
    (hp : ∀ pe ∈ Lp, pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ N + 1)
    (he2 : 1 ≤ e2) (he2d : 2 ^ e2 ∣ N ^ 2 - 1)
    (h42 : ∀ pe ∈ Lm, ∀ r, r.Prime → r ∣ N → r ≡ 1 [MOD pe.1 ^ pe.2])
    (h43 : ∀ pe ∈ Lp, ∀ r, (hr : r.Prime) → (hrn : r ∣ N) →
      r ≡ N ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) U) ^ 2 + 4 * ZMod.castHom hrn (ZMod r) A)
        then 0 else 1) [MOD pe.1 ^ pe.2])
    {F : ℕ} (hF : F = 2 ^ e2 * prodPow (Lm ++ Lp)) (hsize : N < F ^ 2)
    (hfinal : N % F = 1 ∨
      (N % F ≠ 0 ∧ N % F ≠ 1 ∧ ¬ (N % (N % F) = 0 ∧ N % F < N))) : N.Prime := by
  have hN1 : 1 < N := by omega
  set L := Lm ++ Lp with hL
  have hLp : ∀ pe ∈ L, pe.1.Prime := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).1
    · exact (hp pe h).1
  have hL2 : ∀ pe ∈ L, pe.1 ≠ 2 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.1
    · exact (hp pe h).2.1
  have hLe : ∀ pe ∈ L, 1 ≤ pe.2 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.2.1
    · exact (hp pe h).2.2.1
  have hLd : ∀ pe ∈ L, pe.1 ^ pe.2 ∣ N ^ 2 - 1 := fun pe hpe => by
    rcases List.mem_append.mp hpe with h | h
    · exact (hm pe h).2.2.2.trans (sub_one_dvd_sq_sub_one hN1.le)
    · exact (hp pe h).2.2.2.trans (add_one_dvd_sq_sub_one N)
  have hLn : ∀ pe ∈ L, ¬ pe.1 ∣ N := fun pe hpe hd => by
    have hpp := hLp pe hpe
    have h1 : pe.1 ∣ pe.1 ^ pe.2 := dvd_pow_self _ (by have := hLe pe hpe; omega)
    rcases List.mem_append.mp hpe with h | h
    · have h2 : pe.1 ∣ N - 1 := h1.trans (hm pe h).2.2.2
      have h3 : pe.1 ∣ N - (N - 1) := Nat.dvd_sub hd h2
      rw [show N - (N - 1) = 1 by omega] at h3
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h3)
    · have h2 : pe.1 ∣ N + 1 := h1.trans (hp pe h).2.2.2
      have h3 : pe.1 ∣ N + 1 - N := Nat.dvd_sub h2 hd
      rw [show N + 1 - N = 1 by omega] at h3
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h3)
  -- the factored part `F`
  have hP0 : 0 < prodPow L := prodPow_pos fun pe hpe => (hLp pe hpe).pos
  have hF0 : 0 < F := by rw [hF]; exact Nat.mul_pos (pow_pos two_pos _) hP0
  have hF2 : 2 ≤ F := by
    rw [hF]
    calc 2 = 2 ^ 1 * 1 := by norm_num
      _ ≤ 2 ^ e2 * prodPow L := Nat.mul_le_mul (Nat.pow_le_pow_right two_pos he2) hP0
  have hcop2 : Nat.Coprime (2 ^ e2) (prodPow L) :=
    Nat.Coprime.pow_left _ (coprime_prodPow Nat.prime_two fun pe hpe => ⟨hLp pe hpe, hL2 pe hpe⟩)
  have hFdvd : F ∣ N ^ 2 - 1 := by
    rw [hF]
    exact hcop2.mul_dvd_of_dvd_of_dvd he2d (prodPow_dvd hLp hnd hLd)
  have hpow : N ^ 2 ≡ 1 [MOD F] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr hFdvd).symm
  have hprimeF : ∀ q, q.Prime → q ∣ F → q = 2 ∨ ∃ pe ∈ L, q = pe.1 := fun q hq hqF => by
    rw [hF] at hqF
    rcases (Nat.Prime.dvd_mul hq).mp hqF with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · obtain ⟨pe, hpe, hqe, -⟩ := prime_dvd_prodPow hLp hq h
      exact Or.inr ⟨pe, hpe, hqe⟩
  have hns : N.Coprime F := Nat.coprime_of_dvd fun k hk hkN hkF => by
    rcases hprimeF k hk hkF with rfl | ⟨pe, hpe, rfl⟩
    · omega
    · exact hLn pe hpe hkN
  have hfact2 : F.factorization 2 = e2 := by
    rw [hF, Nat.factorization_mul (pow_pos two_pos _).ne' hP0.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      factorization_prodPow_of_not_mem hLp Nat.prime_two hL2, add_zero]
  have hfactp : ∀ pe ∈ L, F.factorization pe.1 = pe.2 := fun pe hpe => by
    rw [hF, Nat.factorization_mul (pow_pos two_pos _).ne' hP0.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_apply, if_neg (hL2 pe hpe).symm, zero_add,
      factorization_prodPow_of_mem hLp hnd hpe]
  -- the confinement of every prime factor of `N`
  have hconf : ∀ r, r ∣ N → ∃ i < 2, r ≡ N ^ i [MOD F * 1] := by
    refine CL.theorem_6_3_LL hN1 hF0 one_pos two_pos dvd_rfl (by rwa [mul_one])
      (Nat.coprime_one_right F) (by rwa [mul_one]) (by simp) ?_ ?_ (fun _ _ => 1) (by simp) ?_
    · intro p hpF
      exact (Nat.dvd_of_mem_primeFactors hpF).trans hFdvd
    · intro p hpF _
      exact (Nat.ordProj_dvd F p).trans hFdvd
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrn : r ∣ N := Nat.dvd_of_mem_primeFactors hr
    have hrodd : r % 2 = 1 := by
      have := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).of_dvd_nat hrn)
      exact this
    set ε : ℕ := if IsSquare ((ZMod.castHom hrn (ZMod r) U) ^ 2
      + 4 * ZMod.castHom hrn (ZMod r) A) then 0 else 1 with hε
    have hε2 : ε < 2 := by
      rw [hε]
      split_ifs <;> norm_num
    -- the congruence modulo the full prime power, for the odd primes
    have hoddp : ∀ pe ∈ L, r ≡ N ^ ε [MOD pe.1 ^ pe.2] := fun pe hpe => by
      rcases List.mem_append.mp hpe with h | h
      · have h1 : N ≡ 1 [MOD pe.1 ^ pe.2] :=
          ((Nat.modEq_iff_dvd' hN1.le).mpr (hm pe h).2.2.2).symm
        exact (h42 pe h r hrp hrn).trans ((h1.pow ε).trans (by rw [one_pow])).symm
      · exact h43 pe h r hrp hrn
    -- the `2`-adic congruence
    have h2adic : r ≡ N ^ ε [MOD 2 ^ e2] := by
      rcases hring with ⟨hn4, hU, a, hA, ha⟩ | ⟨hn3, hA, w, hU, hα⟩
      · have := two_adic_c1 hn4 hN1 hrp hrn ha he2d
        rw [hε, hU, hA]
        exact this
      · have := two_adic_c2 hn3 hrp hrn hα he2d
        rw [hε, hA, hU, map_one, mul_one]
        exact this
    refine ⟨ε, hε2, ?_, ?_, ?_⟩
    · intro p hpF
      rcases hprimeF p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · show r % 2 = N ^ ε % 2
        rw [hrodd, Nat.pow_mod, hodd, one_pow, Nat.one_mod_eq_one.mpr (by norm_num)]
      · exact Nat.ModEq.of_dvd (dvd_pow_self _ (by have := hLe pe hpe; omega)) (hoddp pe hpe)
    · intro p hpF hp2
      rcases hprimeF p (Nat.prime_of_mem_primeFactors hpF) (Nat.dvd_of_mem_primeFactors hpF)
        with rfl | ⟨pe, hpe, rfl⟩
      · exact absurd dvd_rfl hp2
      · rw [hfactp pe hpe]
        exact hoddp pe hpe
    · intro p hp2
      rw [Nat.prime_two.primeFactors, Finset.mem_singleton] at hp2
      subst hp2
      refine ⟨ε, fun _ => Nat.mod_eq_of_lt hε2, by simp, ?_⟩
      rw [mul_one, hfact2]
      simpa using h2adic
  -- the final trial division
  have h25 : ∀ r, r ∣ N → ∃ j < 2, r ≡ N ^ j [MOD F] := by
    simpa using hconf
  rcases hfinal with h1 | ⟨h0, h1, h2⟩
  · exact CL.step5_prime hN1 hsize h25 (i := 1) le_rfl (by rwa [pow_one]) fun j hj hj1 => by omega
  · refine CL.step5_prime hN1 hsize h25 (i := 2) (by norm_num) ?_ fun j hj hj2 => ?_
    · have : N ^ 2 % F = 1 % F := hpow
      rwa [Nat.mod_eq_of_lt (by omega : 1 < F)] at this
    · obtain rfl : j = 1 := by omega
      rw [pow_one]
      rintro ⟨hd, hlt⟩
      exact h2 ⟨Nat.mod_eq_zero_of_dvd hd, hlt⟩

/-! ### Decoding the checker -/

theorem isPrimeNat_eq_true_iff {p : ℕ} : isPrimeNat p = true ↔ p.Prime := by
  rw [Nat.prime_def_minFac, isPrimeNat, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

theorem Outcome.all_pass {l : List (Outcome Unit)} (h : Outcome.all l = .pass ()) :
    ∀ o ∈ l, o = .pass () := by
  unfold Outcome.all at h
  split_ifs at h with h1 h2
  simp at h1 h2
  intro o ho
  rcases o with _ | _ | ⟨⟩
  · exact absurd ho h2
  · exact absurd ho h1
  · rfl

theorem Outcome.all_composite {l : List (Outcome Unit)} (h : Outcome.all l = .composite) :
    ∃ o ∈ l, o = .composite := by
  unfold Outcome.all at h
  split_ifs at h with h1
  obtain ⟨o, ho, ho'⟩ := List.any_eq_true.mp h1
  exact ⟨o, ho, by simpa using ho'⟩

variable {n : AzNat}

theorem toZMod_ofNat [NeZero n.toNat] (w : ℕ) :
    toZMod (AzZMod.ofNat n w) = (w : ZMod n.toNat) := by
  rw [AzZMod.ofNat, toZMod_ofAzNat, AzNat.toNat_ofNat]

theorem toNat_add_one (n : AzNat) : (n + 1).toNat = n.toNat + 1 := by
  rw [AzNat.toNat_add]; rfl

theorem toNat_sub_one (n : AzNat) : (n - 1).toNat = n.toNat - 1 := by
  rw [AzNat.toNat_sub]; rfl

theorem toZMod_val [NeZero n.toNat] (x : AzZMod n) : (toZMod x).val = x.val.toNat := by
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]

theorem toZMod_eq_zero_iff [NeZero n.toNat] (x : AzZMod n) : toZMod x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply toZMod_injective
    rw [h, toZMod_zero]
  · rintro rfl
    exact toZMod_zero

theorem toZMod_eq_one_iff [NeZero n.toNat] (x : AzZMod n) : toZMod x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply toZMod_injective
    rw [h, toZMod_one]
  · rintro rfl
    exact toZMod_one

theorem val_toNat_ne_zero [NeZero n.toNat] {x : AzZMod n} (h : x ≠ 0) : x.val.toNat ≠ 0 := by
  intro h0
  apply h
  rw [← toZMod_eq_zero_iff, toZMod, h0, Nat.cast_zero]

/-- The gcd check gives a unit; a failed gcd check with a nonzero value gives a factor. -/
theorem gcd_eq_one_iff_coprime (x : AzZMod n) :
    AzNat.gcd x.val n = 1 ↔ Nat.Coprime x.val.toNat n.toNat := gcd_val_eq_one_iff x

theorem not_prime_of_gcd_ne_one [NeZero n.toNat] {x : AzZMod n} (hx : x ≠ 0)
    (h : AzNat.gcd x.val n ≠ 1) : ¬ n.toNat.Prime := by
  intro hN
  apply h
  apply AzNat.toNat_injective
  rw [AzNat.toNat_gcd]
  show Nat.gcd x.val.toNat n.toNat = 1
  rcases hN.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right x.val.toNat n.toNat) with h1 | h1
  · exact h1
  · exfalso
    have h2 : n.toNat ∣ x.val.toNat := h1 ▸ Nat.gcd_dvd_left _ _
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero (val_toNat_ne_zero hx)) h2
    exact absurd x.isLt (not_lt.mpr h3)

section Tests

variable [NeZero n.toNat]

/-- **Test (4.2) decoded.** -/
theorem test42_pass {p x : ℕ} (h : test42 n p x = .pass ()) :
    (x : ZMod n.toNat) ^ (n.toNat - 1) = 1 ∧
      IsUnit ((x : ZMod n.toNat) ^ ((n.toNat - 1) / p) - 1) := by
  unfold test42 at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  push Not at h2
  refine ⟨?_, ?_⟩
  · have := congrArg toZMod h2
    rwa [toZMod_powAzNat, toZMod_one, toZMod_ofNat, toNat_sub_one] at this
  · have h5 : Nat.Coprime (toZMod (AzZMod.powAzNat (AzZMod.ofNat n x)
        ((n - 1) / AzNat.ofNat p) - 1)).val n.toNat := by
      rw [toZMod_val]
      exact (gcd_eq_one_iff_coprime _).mp h3
    have := CL.isUnit_of_val_coprime h5
    rwa [toZMod_sub, toZMod_one, toZMod_powAzNat, AzNat.toNat_div, toNat_sub_one, AzNat.toNat_ofNat,
      toZMod_ofNat] at this

/-- **Test (4.2) `composite` verdicts are sound.** -/
theorem test42_composite {p x : ℕ} (h : test42 n p x = .composite) : ¬ n.toNat.Prime := by
  intro hN
  haveI : Fact n.toNat.Prime := ⟨hN⟩
  unfold test42 at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  · apply h2
    apply toZMod_injective
    rw [toZMod_powAzNat, toZMod_one, toNat_sub_one]
    exact ZMod.pow_card_sub_one_eq_one (by rwa [Ne, toZMod_eq_zero_iff])
  · refine not_prime_of_gcd_ne_one ?_ h3 hN
    intro h0
    apply h4
    rw [h0]
    apply AzNat.toNat_injective
    rw [AzNat.toNat_gcd, ← toZMod_val, toZMod_zero, ZMod.val_zero, Nat.gcd_zero_left]

/-- **Test (4.3) decoded**: the hypotheses of `test_4_3_confinement`. -/
theorem test43_pass {u a : AzZMod n} {p c : ℕ} (h : test43 n u a p c = .pass ()) :
    ∃ x₀ x₁ : ZMod n.toNat, CL.quadNorm (toZMod u) (toZMod a) x₀ x₁ = 1 ∧
      CL.quadElt (toZMod u) (toZMod a) x₀ x₁ ^ (n.toNat + 1) = 1 ∧
      ∃ c₀ c₁ : ZMod n.toNat, CL.quadElt (toZMod u) (toZMod a) x₀ x₁ ^ ((n.toNat + 1) / p) - 1
        = CL.quadElt (toZMod u) (toZMod a) c₀ c₁ ∧ (IsUnit c₀ ∨ IsUnit c₁) := by
  unfold test43 at h
  split at h
  · cases h
  rename_i x hx
  dsimp only at h
  have hcop : ∀ y : AzZMod n, AzNat.gcd y.val n = 1 → IsUnit (toZMod y) := fun y hy =>
    CL.isUnit_of_val_coprime (by rw [toZMod_val]; exact (gcd_eq_one_iff_coprime y).mp hy)
  have h1 : (NormOne.powAzNat x (n + 1)).1 = 1 := by
    by_contra h1
    rw [if_pos h1] at h
    cases h
  rw [if_neg (not_not.mpr h1)] at h
  refine ⟨toZMod x.1.x₀, toZMod x.1.x₁, NormOne.quadNorm_toQuad x, ?_,
    toZMod ((NormOne.powAzNat x ((n + 1) / AzNat.ofNat p)).1 - 1).x₀,
    toZMod ((NormOne.powAzNat x ((n + 1) / AzNat.ofNat p)).1 - 1).x₁, ?_, ?_⟩
  · have := congrArg QuadT.toQuad h1
    rwa [NormOne.toQuad_powAzNat, QuadT.toQuad_one, toNat_add_one] at this
  · show _ = QuadT.toQuad ((NormOne.powAzNat x ((n + 1) / AzNat.ofNat p)).1 - 1)
    rw [QuadT.toQuad_sub, QuadT.toQuad_one, NormOne.toQuad_powAzNat, AzNat.toNat_div,
      toNat_add_one, AzNat.toNat_ofNat]
    rfl
  · split_ifs at h with h2 h3
    · rename_i h4
      exact Or.inl (hcop _ h4)
    · rename_i h4
      exact Or.inr (hcop _ h4)

/-- **Test (4.3) `composite` verdicts are sound** (for a nonsquare discriminant). -/
theorem test43_composite [Fact (1 < n.toNat)] {u a : AzZMod n} {p c : ℕ}
    (hns : ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a))
    (h : test43 n u a p c = .composite) : ¬ n.toNat.Prime := by
  intro hN
  unfold test43 at h
  split at h
  · rename_i hx
    have := NormOne.normOneCandidate_isSome (u := u) (a := a) hN hns (AzZMod.ofNat n c)
    rw [hx] at this
    exact Bool.false_ne_true this
  rename_i x hx
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · exact h1 (NormOne.powAzNat_card_succ_eq_one hN hns x)
  · rename_i h4
    exact not_prime_of_gcd_ne_one h3 h4 hN
  · rename_i h4
    exact not_prime_of_gcd_ne_one (fun h5 => h2 ⟨not_not.mp h3, h5⟩) h4 hN

omit [NeZero n.toNat] in
theorem modPow2_two_eq_one_iff : n.modPow2 2 = AzNat.ofNat 1 ↔ n.toNat % 4 = 1 := by
  constructor
  · intro h
    have := congrArg AzNat.toNat h
    rwa [AzNat.toNat_modPow2, AzNat.toNat_ofNat] at this
  · intro h
    apply AzNat.toNat_injective
    rw [AzNat.toNat_modPow2, AzNat.toNat_ofNat]
    exact h

/-- **The ring parameters decoded.** -/
theorem ringParams_pass (hodd : n.toNat % 2 = 1) {w : ℕ} {u a : AzZMod n}
    (h : ringParams n w = .pass (u, a)) :
    (n.toNat % 4 = 1 ∧ toZMod u = 0 ∧ toZMod a = (w : ZMod n.toNat) ∧
        (w : ZMod n.toNat) ^ ((n.toNat - 1) / 2) = -1) ∨
      (n.toNat % 4 = 3 ∧ toZMod a = 1 ∧ toZMod u = (w : ZMod n.toNat) ∧
        jacobiSym (w * w + 4) n.toNat = -1 ∧
        (AdjoinRoot.root (X ^ 2 - C (w : ZMod n.toNat) * X - C 1 :
          Polynomial (ZMod n.toNat))) ^ (n.toNat + 1) = -1) := by
  unfold ringParams at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · left
    obtain ⟨rfl, rfl⟩ := Outcome.pass.inj h |> Prod.mk.inj
    refine ⟨modPow2_two_eq_one_iff.mp h1, toZMod_zero, toZMod_ofNat w, ?_⟩
    have := congrArg toZMod h3
    rwa [toZMod_powAzNat, toZMod_neg, toZMod_one, toZMod_ofNat, AzNat.toNat_div, toNat_sub_one,
      AzNat.toNat_ofNat] at this
  · right
    obtain ⟨rfl, rfl⟩ := Outcome.pass.inj h |> Prod.mk.inj
    push Not at h5 h6
    have hn3 : n.toNat % 4 = 3 := by
      have := mt modPow2_two_eq_one_iff.mpr h1
      omega
    refine ⟨hn3, toZMod_one, toZMod_ofNat w, ?_, ?_⟩
    · rw [AzNat.jacobi_eq _ _ hodd, AzNat.toNat_ofNat] at h5
      exact_mod_cast h5
    · have := congrArg QuadT.toQuad h6
      rw [QuadT.toQuad_powAzNat, QuadT.toQuad_alpha, QuadT.toQuad_const, toZMod_neg, toZMod_one,
        toZMod_ofNat, toNat_add_one] at this
      rw [this]
      simp

/-- **`ringParams` `composite` verdicts are sound.** -/
theorem ringParams_composite [Fact (1 < n.toNat)] (hodd : n.toNat % 2 = 1) {w : ℕ}
    (h : ringParams n w = .composite) : ¬ n.toNat.Prime := by
  intro hN
  haveI : Fact n.toNat.Prime := ⟨hN⟩
  unfold ringParams at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · -- (c1): `e² = a^(n−1) = 1` forces `e = ±1`
    set e := (AzZMod.ofNat n w).powAzNat ((n - 1) / AzNat.ofNat 2) with he
    have hsq : toZMod e * toZMod e = 1 := by
      rw [he, toZMod_powAzNat, ← pow_add, AzNat.toNat_div, toNat_sub_one, AzNat.toNat_ofNat,
        show (n.toNat - 1) / 2 + (n.toNat - 1) / 2 = n.toNat - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one (by rwa [Ne, toZMod_eq_zero_iff])
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h4 ((toZMod_eq_one_iff e).mp h)
    · exact h3 (toZMod_injective (by rw [h, toZMod_neg, toZMod_one]))
  · -- (c2): `α^(n+1) = −1` for prime `n` and a nonsquare discriminant
    push Not at h5
    apply h6
    have hns : ¬ IsSquare (toZMod (AzZMod.ofNat n w) ^ 2 + 4 * toZMod (1 : AzZMod n)) := by
      rw [toZMod_one, mul_one, toZMod_ofNat]
      have := ZMod.nonsquare_of_jacobiSym_eq_neg_one (a := w * w + 4) (b := n.toNat)
        (by rw [AzNat.jacobi_eq _ _ hodd, AzNat.toNat_ofNat] at h5; exact_mod_cast h5)
      push_cast at this
      rwa [pow_two]
    exact QuadT.alpha_powAzNat_card_succ hN hns

end Tests


/-- The `(p, e)` pairs of a certificate. -/
def certPairs (cert : LLCert) : List (ℕ × ℕ) :=
  cert.minus.map (fun t => (t.1, t.2.1)) ++ cert.plus.map (fun t => (t.1, t.2.1))

theorem toNat_listProd (l : List AzNat) : l.prod.toNat = (l.map AzNat.toNat).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.prod_cons, AzNat.toNat_mul, ih, List.map_cons, List.prod_cons]

theorem toNat_llF (cert : LLCert) : (llF cert).toNat = 2 ^ cert.e2 * prodPow (certPairs cert) := by
  simp [llF, AzNat.toNat_mul, toNat_listProd, List.map_map, Function.comp_def, AzNat.toNat_ofNat,
    prodPow, certPairs, mul_assoc]

theorem dvd_of_mod_ofNat_eq_zero {m : AzNat} {k : ℕ} (h : m % AzNat.ofNat k = 0) : k ∣ m.toNat := by
  have := congrArg AzNat.toNat h
  rw [AzNat.toNat_mod, AzNat.toNat_ofNat] at this
  exact Nat.dvd_of_mod_eq_zero this

/-- **The structural checks decoded.** -/
theorem structOK_eq_true {cert : LLCert} (h : structOK n cert = true) :
    ((certPairs cert).map Prod.fst).Nodup ∧
    (∀ pe ∈ cert.minus.map (fun t => (t.1, t.2.1)),
      pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ n.toNat - 1) ∧
    (∀ pe ∈ cert.plus.map (fun t => (t.1, t.2.1)),
      pe.1.Prime ∧ pe.1 ≠ 2 ∧ 1 ≤ pe.2 ∧ pe.1 ^ pe.2 ∣ n.toNat + 1) ∧
    1 ≤ cert.e2 ∧ 2 ^ cert.e2 ∣ n.toNat ^ 2 - 1 := by
  simp only [structOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hnd, hm⟩, hp⟩, he⟩, hd⟩ := h
  refine ⟨?_, ?_, ?_, he, ?_⟩
  · simpa [certPairs, List.map_map, Function.comp_def] using hnd
  · intro pe hpe
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm t ht
    refine ⟨isPrimeNat_eq_true_iff.mp h1, h2, h3, ?_⟩
    have := dvd_of_mod_ofNat_eq_zero h4
    rwa [toNat_sub_one] at this
  · intro pe hpe
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp t ht
    refine ⟨isPrimeNat_eq_true_iff.mp h1, h2, h3, ?_⟩
    have := dvd_of_mod_ofNat_eq_zero h4
    rwa [toNat_add_one] at this
  · have := congrArg AzNat.toNat hd
    rw [AzNat.toNat_modPow2, AzNat.toNat_sub, AzNat.toNat_square] at this
    exact Nat.dvd_of_mod_eq_zero this

section Stage

variable [NeZero n.toNat]

/-- **The stage `pass` decoded.** -/
theorem llStage_pass {cert : LLCert} {ua : AzZMod n × AzZMod n} (h : llStage n cert = .pass ua) :
    ringParams n cert.w = .pass ua ∧ (∀ t ∈ cert.minus, test42 n t.1 t.2.2 = .pass ()) ∧
      (∀ t ∈ cert.plus, test43 n ua.1 ua.2 t.1 t.2.2 = .pass ()) := by
  unfold llStage at h
  split at h <;> try cases h
  rename_i ua' hring
  split at h <;> try cases h
  rename_i hall
  have hall' := Outcome.all_pass hall
  refine ⟨hring, fun t ht => ?_, fun t ht => ?_⟩
  · exact hall' _ (List.mem_append_left _ (List.mem_map_of_mem ht))
  · exact hall' _ (List.mem_append_right _ (List.mem_map_of_mem ht))

/-- **The stage `composite` decoded.** -/
theorem llStage_composite {cert : LLCert} (h : llStage n cert = .composite) :
    ringParams n cert.w = .composite ∨ ∃ ua : AzZMod n × AzZMod n, ringParams n cert.w = .pass ua ∧
      ((∃ t ∈ cert.minus, test42 n t.1 t.2.2 = .composite) ∨
        (∃ t ∈ cert.plus, test43 n ua.1 ua.2 t.1 t.2.2 = .composite)) := by
  unfold llStage at h
  split at h <;> try cases h
  · rename_i hring
    exact Or.inl hring
  rename_i ua hring
  split at h <;> try cases h
  rename_i hall
  obtain ⟨o, ho, rfl⟩ := Outcome.all_composite hall
  refine Or.inr ⟨ua, hring, ?_⟩
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨t, ht, hto⟩ := List.mem_map.mp ho
    exact Or.inl ⟨t, ht, hto⟩
  · obtain ⟨t, ht, hto⟩ := List.mem_map.mp ho
    exact Or.inr ⟨t, ht, hto⟩

end Stage

/-! ### The soundness theorems -/

/-- The nonsquare discriminant for prime `n`, from the ring-parameter checks. -/
theorem not_isSquare_of_ringParams [NeZero n.toNat] (hN : n.toNat.Prime) (hodd : n.toNat % 2 = 1)
    {w : ℕ} {u a : AzZMod n} (h : ringParams n w = .pass (u, a)) :
    ¬ IsSquare (toZMod u ^ 2 + 4 * toZMod a) := by
  rcases ringParams_pass hodd h with ⟨hn4, hU, hA, hw⟩ | ⟨hn3, hA, hU, hj, -⟩
  · rw [hU, hA]
    have := ZMod.nonsquare_of_jacobiSym_eq_neg_one
      (CL.jacobiSym_c1_of_euler hN hn4 (a := (w : ℤ)) (by push_cast; exact hw))
    push_cast at this
    simpa using this
  · rw [hU, hA, mul_one, pow_two]
    have := ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
    push_cast at this
    exact this

/-- **Soundness of `some true`**: the Lucas–Lehmer stage certifies primality. -/
theorem llCheck_true {cert : LLCert} (h : llCheck n cert = some true) : n.toNat.Prime := by
  unfold llCheck at h
  split_ifs at h with h2 hodd hstruct heq
  · cases h
  · haveI : NeZero n.toNat := ⟨by omega⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hodd hstruct
    have hodd' : n.toNat % 2 = 1 := Nat.odd_iff.mp ((AzNat.isOdd_iff n).mp hodd)
    obtain ⟨hnd, hm, hp, he2, he2d⟩ := structOK_eq_true hstruct
    split at h <;> try cases h
    rename_i ua hstage
    obtain ⟨hring, h42, h43⟩ := llStage_pass hstage
    dsimp only at h
    -- the assembled primality argument, given the final trial-division outcome
    have key : n.toNat < (llF cert).toNat ^ 2 →
        (n.toNat % (llF cert).toNat = 1 ∨
          (n.toNat % (llF cert).toNat ≠ 0 ∧ n.toNat % (llF cert).toNat ≠ 1 ∧
            ¬ (n.toNat % (n.toNat % (llF cert).toNat) = 0 ∧
              n.toNat % (llF cert).toNat < n.toNat))) → n.toNat.Prime := by
      intro hsize hfinal
      refine prime_of_ll h2 hodd' (U := toZMod ua.1) (A := toZMod ua.2) ?_ hnd hm hp he2 he2d
        ?_ ?_ (toNat_llF cert) hsize hfinal
      · rcases ringParams_pass hodd' hring with ⟨hn4, hU, hA, hw⟩ | ⟨hn3, hA, hU, hj, hα⟩
        · refine Or.inl ⟨hn4, hU, (cert.w : ℤ), by rw [hA, Int.cast_natCast], ?_⟩
          exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (by push_cast; exact hw)
        · exact Or.inr ⟨hn3, hA, cert.w, hU, hα⟩
      · intro pe hpe r hr hrn
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
        obtain ⟨hx1, hunit⟩ := test42_pass (h42 t ht)
        exact pocklington_prime_pow (by omega) (hm _ hpe).1 (hm _ hpe).2.2.2 hx1 hunit r hr hrn
      · intro pe hpe r hr hrn
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hpe
        obtain ⟨x₀, x₁, hN, hx1, hunit⟩ := test43_pass (h43 t ht)
        exact CL.test_4_3_confinement (by omega) hr hrn (hp _ hpe).1 (hp _ hpe).2.1
          (hp _ hpe).2.2.1 (hp _ hpe).2.2.2 hN hx1 hunit
    split_ifs at h with hsize hr1 hr0 hdiv
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hsize
      refine key ?_ (Or.inl ?_)
      · have := (AzNat.lt_iff_toNat_lt _ _).mp hsize
        rwa [AzNat.toNat_square] at this
      · have := congrArg AzNat.toNat hr1
        rwa [AzNat.toNat_mod] at this
    · cases h
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hsize
      refine key ?_ (Or.inr ⟨?_, ?_, ?_⟩)
      · have := (AzNat.lt_iff_toNat_lt _ _).mp hsize
        rwa [AzNat.toNat_square] at this
      · intro h0
        apply hr0
        apply AzNat.toNat_injective
        rw [AzNat.toNat_mod]
        exact h0
      · intro h1
        apply hr1
        apply AzNat.toNat_injective
        rw [AzNat.toNat_mod]
        exact h1
      · rintro ⟨hd, hlt⟩
        apply hdiv
        refine ⟨?_, ?_⟩
        · apply AzNat.toNat_injective
          rw [AzNat.toNat_mod, AzNat.toNat_mod]
          exact hd
        · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_mod]
          exact hlt
  · rw [heq]
    exact Nat.prime_two
  · cases h

/-- **Soundness of `some false`**: every compositeness verdict is correct. -/
theorem llCheck_false {cert : LLCert} (h : llCheck n cert = some false) : ¬ n.toNat.Prime := by
  intro hN
  unfold llCheck at h
  split_ifs at h with h2 hodd hstruct heq
  · -- even `n > 2`
    simp only [Bool.not_eq_true'] at hodd
    have hnodd : ¬ Odd n.toNat := fun ho => by
      have := (AzNat.isOdd_iff n).mpr ho
      rw [hodd] at this
      exact Bool.false_ne_true this
    have h2d : 2 ∣ n.toNat := Nat.dvd_of_mod_eq_zero (by have := Nat.odd_iff.not.mp hnodd; omega)
    have := hN.eq_one_or_self_of_dvd 2 h2d
    omega
  · haveI : NeZero n.toNat := ⟨by omega⟩
    haveI : Fact (1 < n.toNat) := ⟨by omega⟩
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hodd hstruct
    have hodd' : n.toNat % 2 = 1 := Nat.odd_iff.mp ((AzNat.isOdd_iff n).mp hodd)
    split at h <;> try cases h
    · -- a `composite` verdict from the stage
      rename_i hstage
      rcases llStage_composite hstage with hring | ⟨ua, hring, ⟨t, ht, h42⟩ | ⟨t, ht, h43⟩⟩
      · exact ringParams_composite hodd' hring hN
      · exact test42_composite h42 hN
      · exact test43_composite (not_isSquare_of_ringParams hN hodd' hring) h43 hN
    · -- the trial division found a factor
      rename_i ua hstage
      dsimp only at h
      split_ifs at h with hsize hr1 hr0 hdiv
      · cases h
      · obtain ⟨hd, hlt⟩ := hdiv
        have hd' : (n % llF cert).toNat ∣ n.toNat := by
          have := congrArg AzNat.toNat hd
          rw [AzNat.toNat_mod] at this
          exact Nat.dvd_of_mod_eq_zero this
        rcases hN.eq_one_or_self_of_dvd _ hd' with h1 | h1
        · exact hr1 (AzNat.toNat_injective h1)
        · exact absurd ((AzNat.lt_iff_toNat_lt _ _).mp hlt) (by rw [h1]; exact lt_irrefl _)
      · cases h
  · cases h
  · have : n.toNat ≤ 1 := by omega
    interval_cases hn : n.toNat
    · exact Nat.not_prime_zero hN
    · exact Nat.not_prime_one hN

/-- **The generated-certificate test is sound**: `some true` means prime. -/
theorem llTest_true {B : ℕ} (h : llTest n B = some true) : n.toNat.Prime := llCheck_true h

/-- **The generated-certificate test is sound**: `some false` means composite. -/
theorem llTest_false {B : ℕ} (h : llTest n B = some false) : ¬ n.toNat.Prime := llCheck_false h

end APRCL

end Azurite
