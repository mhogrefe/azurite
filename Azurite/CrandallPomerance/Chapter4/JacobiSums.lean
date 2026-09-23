/-
  **Jacobi sums — the structural upgrade motivating APR-CL** (the
  book's closing passage of §4.4 before AKS): the Gauss sums
  `G(p, q)` live in `ℤ[ζ_p, ζ_q]` — vectors of `(p−1)(q−1)`
  residues mod `n` — while the Jacobi sums `J(p, q)` live in the
  much smaller `ℤ[ζ_p]` (`p−1` coordinates; in practice `p` is tiny
  while `q` can be much larger).  The bridge is the classical
  Gauss–Jacobi machinery, most of which Mathlib already has
  (`jacobiSum_mul_nontrivial`, `gaussSum_pow_eq_prod_jacobiSum`,
  `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`); our contribution:

  * `bValue p` — the book's auxiliary `b(p)`, the LEAST positive
    `b` with `(b+1)^p ≢ b^p + 1 (mod p²)`, with an existence proof
    (some `b < p` always works: if every one failed, telescoping
    gives `b^p ≡ b (mod p²)` up to `b = p`, but
    `p^p ≡ 0 ≢ p (mod p²)`) — so the definition is computable and
    total.  Note `b(p) = 1` exactly when `p` is NOT a Wieferich
    prime (`2^(p−1) ≡ 1 (mod p²)` — only `1093` and `3511` are
    known); the book's remark that one "may take `b = 2`" describes
    valid choices, not the least one.
  * `chi_neg_one_eq_one` — a character of ODD order kills `−1`
    (its value has order dividing both `2` and an odd number).
  * `jacobiSum_pow_eq_sum` — the book's displayed
    `J(p,q) = Σ_m χ(m^b (m−1))` IS `jacobiSum (χ^b) χ`, since
    `χ(m−1) = χ(−1)·χ(1−m) = χ(1−m)` for odd-order `χ`.
  * `gaussSum_mul_eq_jacobiSum_mul` — the fundamental relation
    `G(χ)·G(χ^k) = J(χ, χ^k)·G(χ^(k+1))` at `χ_{p,q}`.
  * `gaussSum_pow_eq_card_mul_prod` — the payoff:
    `G(χ_{p,q})^p = q · J(χ,χ)·J(χ,χ²) ⋯ J(χ,χ^(p−2))`, an element
    of `ℤ[ζ_p]` (`jacobiSum_mem_adjoin_zetaP`).  Since every
    step-3/4 exponent `p^w·u` of the Gauss sums test has `w ≥ 1`,
    the tested powers `G^(p^w·u) = (G^p)^(p^(w−1)·u)` are entirely
    Jacobi-sum expressions — the reason the Jacobi sums test
    computes in the small ring.

  The passage's ideal-theoretic connection (the splitting
  `(n) = N_1 ⋯ N_((p−1)/f)` in `ℤ[ζ_p]` with `f = ord_p(n)`, norms
  `n^f`, and the residue congruences `α^((n^f−1)/p) ≡ ζ_p^(a_j)`)
  is stated by the book without proof and is DEFERRED to the
  APR-CL-paper phase, where the exact form needed by the
  correctness proof will be fixed (Mathlib's Kummer–Dedekind and
  cyclotomic-integer machinery covers the inputs if required; the
  algorithmic side — factoring `Φ_p` mod `n` — already has rails in
  our Gathen–Gerhard Chapter 14 layer).
-/
import Azurite.CrandallPomerance.Chapter4.GaussSums
import Mathlib.NumberTheory.JacobiSum.Basic

namespace Azurite

namespace CP

open MulChar Finset

/-! ### The auxiliary base `b(p)` -/

section BValue

/-- The Fermat-quotient condition on the auxiliary base `b`:
`(b+1)^p ≢ b^p + 1 (mod p²)`. -/
def bCond (p b : ℕ) : Prop := ¬((b + 1) ^ p ≡ b ^ p + 1 [MOD p ^ 2])

instance (p b : ℕ) : Decidable (bCond p b) := by
  unfold bCond Nat.ModEq
  infer_instance

/-- Some positive `b < p` always satisfies the condition: if every
one failed, telescoping would give `b^p ≡ b (mod p²)` for all
`b ≤ p`, but `p^p ≡ 0 ≢ p (mod p²)`. -/
theorem exists_bCond {p : ℕ} (hp : p.Prime) :
    ∃ b, 0 < b ∧ b < p ∧ bCond p b := by
  by_contra hall
  push Not at hall
  have key : ∀ b, b ≤ p → b ^ p ≡ b [MOD p ^ 2] := by
    intro b hb
    induction b with
    | zero =>
      rw [Nat.zero_pow hp.pos]
    | succ b ih =>
      have hbp : b < p := Nat.lt_of_succ_le hb
      by_cases hb0 : b = 0
      · subst hb0
        rw [Nat.zero_add, one_pow]
      · have hcong := hall b (Nat.pos_of_ne_zero hb0) hbp
        rw [bCond, not_not] at hcong
        calc (b + 1) ^ p ≡ b ^ p + 1 [MOD p ^ 2] := hcong
          _ ≡ b + 1 [MOD p ^ 2] :=
            Nat.ModEq.add_right 1 (ih (Nat.le_of_succ_le hb))
  have hpp := key p le_rfl
  obtain ⟨c, hc⟩ := pow_dvd_pow p hp.two_le
  have hlt : p < p ^ 2 := by
    have h2 := hp.two_le
    rw [pow_two]
    nlinarith
  rw [Nat.ModEq, hc, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt] at hpp
  exact hp.pos.ne' hpp.symm

/-- **The book's `b(p)`**: the least positive `b` with
`(b+1)^p ≢ b^p + 1 (mod p²)` (junk value `0` at non-primes).
Equals `1` exactly when `p` is not a Wieferich prime. -/
def bValue (p : ℕ) : ℕ :=
  if hp : p.Prime then
    Nat.find (⟨_, (exists_bCond hp).choose_spec.1,
      (exists_bCond hp).choose_spec.2.2⟩ :
      ∃ b, 0 < b ∧ bCond p b)
  else 0

theorem bValue_pos {p : ℕ} (hp : p.Prime) : 0 < bValue p := by
  rw [bValue, dite_eq_left hp]
  exact (Nat.find_spec (p := fun b => 0 < b ∧ bCond p b) _).1

theorem bValue_spec {p : ℕ} (hp : p.Prime) : bCond p (bValue p) := by
  rw [bValue, dite_eq_left hp]
  exact (Nat.find_spec (p := fun b => 0 < b ∧ bCond p b) _).2

/-- Minimality: no smaller positive `b` satisfies the condition. -/
theorem bValue_min {p : ℕ} (hp : p.Prime) {b : ℕ} (hb : 0 < b)
    (hlt : b < bValue p) : ¬bCond p b := by
  rw [bValue, dite_eq_left hp] at hlt
  intro hc
  exact Nat.find_min (p := fun b => 0 < b ∧ bCond p b) _ hlt ⟨hb, hc⟩

theorem bValue_lt {p : ℕ} (hp : p.Prime) : bValue p < p := by
  obtain ⟨b, hb0, hbp, hbc⟩ := exists_bCond hp
  calc bValue p ≤ b := by
        rw [bValue, dite_eq_left hp]
        exact Nat.find_le ⟨hb0, hbc⟩
    _ < p := hbp

end BValue

/-! ### Jacobi sums and the Gauss–Jacobi relations at `χ_{p,q}` -/

section JacobiSums

variable {q : ℕ} [Fact q.Prime] {R : Type _} [CommRing R]

/-- A multiplicative character of ODD order sends `−1` to `1`: its
value there has order dividing both `2` and the odd order. -/
theorem chi_neg_one_eq_one {χ : MulChar (ZMod q) R}
    (hodd : Odd (orderOf χ)) : χ (-1) = 1 := by
  have h2 : χ (-1) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, neg_mul_neg, one_mul, map_one]
  have hn : χ (-1) ^ orderOf χ = 1 := by
    have h := pow_orderOf_eq_one χ
    have h2' := congrArg
      (fun ξ : MulChar (ZMod q) R => ξ (((-1 : (ZMod q)ˣ) : ZMod q))) h
    simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h2'
    rwa [Units.val_neg, Units.val_one] at h2'
  have hd : orderOf (χ (-1)) ∣ Nat.gcd 2 (orderOf χ) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one hn)
  rw [Nat.Coprime.gcd_eq_one (by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hdvd
    have := Nat.odd_iff.mp hodd
    omega), Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

/-- **The book's Jacobi sum display**:
`J(p,q) = Σ_m χ(m^b (m−1))` IS the standard `jacobiSum (χ^b) χ` —
for odd-order `χ`, since `χ(m−1) = χ(−1)·χ(1−m) = χ(1−m)`. -/
theorem jacobiSum_pow_eq_sum {χ : MulChar (ZMod q) R}
    (hodd : Odd (orderOf χ)) {b : ℕ} (hb : b ≠ 0) :
    jacobiSum (χ ^ b) χ = ∑ m : ZMod q, χ (m ^ b * (m - 1)) := by
  rw [jacobiSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_pow, MulChar.pow_apply' χ hb]
  congr 1
  have h1m : (1 : ZMod q) - m = -1 * (m - 1) := by ring
  rw [h1m, map_mul, chi_neg_one_eq_one hodd, one_mul]

variable [IsDomain R] {p : ℕ} {ζp : Rˣ}
  (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
  {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- **The fundamental Gauss–Jacobi relation at `χ_{p,q}`**:
`G(χ)·G(χ^k) = J(χ, χ^k)·G(χ^(k+1))` for `0 < k < p − 1` — the
relation that expresses Gauss-sum products through the small-ring
Jacobi sums (Mathlib's `jacobiSum_mul_nontrivial`, with the
nontriviality of `χ^(k+1)` from the exact order `p`). -/
theorem gaussSum_mul_eq_jacobiSum_mul (hζp : IsPrimitiveRoot ζp p)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q) {k : ℕ} (hk0 : 0 < k)
    (hk : k < p - 1) :
    gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one)
      * gaussSum (MulChar.ofRootOfUnity hζmem hg ^ k)
        (AddChar.zmodChar q hζq.pow_eq_one)
      = jacobiSum (MulChar.ofRootOfUnity hζmem hg)
          (MulChar.ofRootOfUnity hζmem hg ^ k)
        * gaussSum (MulChar.ofRootOfUnity hζmem hg ^ (k + 1))
          (AddChar.zmodChar q hζq.pow_eq_one) := by
  set χ := MulChar.ofRootOfUnity hζmem hg with hχdef
  have hord : orderOf χ = p := orderOf_ofRootOfUnity_eq hζp hζmem hg
  have hne : χ * χ ^ k ≠ 1 := by
    rw [← pow_succ']
    exact pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero k) (by omega)
  have h := jacobiSum_mul_nontrivial hne
    (AddChar.zmodChar q hζq.pow_eq_one)
  rw [← h, ← pow_succ']
  ring

/-- **`G(χ_{p,q})^p` lives in `ℤ[ζ_p]`** — the structural heart of
the Jacobi sums upgrade: for `p` an odd prime (dividing `q − 1`),
`G(χ)^p = q · J(χ,χ)·J(χ,χ²) ⋯ J(χ,χ^(p−2))` (Mathlib's
`gaussSum_pow_eq_prod_jacobiSum`, with `χ(−1) = 1` since the order
`p` is odd).  Every step-3/4 exponent `p^w·u` of the Gauss sums
test has `w ≥ 1`, so the tested powers
`G^(p^w·u) = (G^p)^(p^(w−1)·u)` are entirely Jacobi-sum
expressions in the small ring. -/
theorem gaussSum_pow_eq_card_mul_prod (hp : Odd p) (hp1 : 1 < p)
    (hζp : IsPrimitiveRoot ζp p) {ζq : R} (hζq : IsPrimitiveRoot ζq q) :
    gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ p
      = (q : R) * ∏ k ∈ Ico 1 (p - 1),
          jacobiSum (MulChar.ofRootOfUnity hζmem hg)
            (MulChar.ofRootOfUnity hζmem hg ^ k) := by
  set χ := MulChar.ofRootOfUnity hζmem hg with hχdef
  have hord : orderOf χ = p := orderOf_ofRootOfUnity_eq hζp hζmem hg
  have hψ : (AddChar.zmodChar q hζq.pow_eq_one).IsPrimitive := by
    have h := AddChar.zmodChar_primitive_of_primitive_root q hζq
    convert h using 2
  have h := gaussSum_pow_eq_prod_jacobiSum
    (χ := χ) (ψ := AddChar.zmodChar q hζq.pow_eq_one)
    (by omega) hψ
  rw [hord, chi_neg_one_eq_one (by rw [hord]; exact hp), one_mul,
    ZMod.card] at h
  exact h

/-- Every Jacobi sum of powers of `χ_{p,q}` lies in `ℤ[ζ_p]` — the
small ring where the Jacobi sums test computes
(`(p−1)`-coordinate vectors instead of `(p−1)(q−1)`). -/
theorem jacobiSum_mem_adjoin_zetaP [NeZero p]
    (hζp : IsPrimitiveRoot ζp p) (a c : ℕ) :
    jacobiSum (MulChar.ofRootOfUnity hζmem hg ^ a)
        (MulChar.ofRootOfUnity hζmem hg ^ c)
      ∈ Algebra.adjoin ℤ {(ζp : R)} := by
  set χ := MulChar.ofRootOfUnity hζmem hg with hχdef
  have hχp : χ ^ p = 1 := by
    rw [← orderOf_ofRootOfUnity_eq hζp hζmem hg]
    exact pow_orderOf_eq_one χ
  have hpow : ∀ e : ℕ, (χ ^ e) ^ p = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul, hχp, one_pow]
  exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one (hpow a) (hpow c)
    (IsPrimitiveRoot.coe_units_iff.mpr hζp)

end JacobiSums

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite.CP

-- `b(p) = 1` for non-Wieferich primes (all known primes except
-- `1093` and `3511`)
#guard bValue 3 = 1
#guard bValue 5 = 1
#guard bValue 7 = 1
#guard bValue 13 = 1
#guard bValue 101 = 1

end Tests
