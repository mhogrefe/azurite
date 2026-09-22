/-
  **The tables of (1.1) — Phase A4 of the implementation plan.**

  * `qPrimes t` — the `q`-primes: primes `q` with `q − 1 ∣ t`
    (`mem_qPrimes`), the prime divisors of `e(t)`.
  * `checkGenerator q g` — the runtime certificate that `g` generates
    `(ℤ/qℤ)ˣ` (`g^(q−1) = 1` and `g^((q−1)/r) ≠ 1` for the primes
    `r ∣ q − 1`); `checkGenerator_spec` produces the generator hypothesis
    of `jacobiSum_eq_sum_gen_pow`.  `findGenerator` searches for one.
  * `checkIndexTable q g f` — the runtime certificate that the index table
    satisfies `g^(f x) = 1 − g^x` for `1 ≤ x ≤ q − 2` (the (1.1)(b1)
    defining property); `indexTable` builds it from a discrete-log table.
    Only the *checks* are proven; the constructors are generator-side.
  * `jacobiSumT n p k q f a b ∈ CycT n p k` — the (1.1)(b2) coefficient
    vector of `Σ_{x=1}^{q−2} ζ^(a·x + b·f(x))`, reduced modulo `Φ_{p^k}`
    coordinatewise (`zetaCoeff`: a unit vector for exponents `< m`, the
    `−1`-pattern for exponents `≥ m`, as in (6.2)).  The three tables of
    the paper are `j = jacobiSumT … 1 1`, `j* = jacobiSumT … 2 1`, and
    `j# = jacobiSumT … (3·2^(k−3)) 2^(k−3)`.

  **Correctness**: `jacobiSumT_eq_reduce` — for `g` a certified generator
  and `f` a certified index table, the computable table is the reduction
  modulo `n` of the abstract Jacobi sum `j(χ^a, χ^b)` for the character
  `χ = chiT` with `χ(g) = ζ_{p^k}` (`MulChar.ofRootOfUnity`), via
  `CL.jacobiSum_eq_sum_gen_pow` and the (6.2) pattern lemmas.  So every
  Jacobi-sum congruence of the 1984 chain (Theorems (8.5), (9.10), (9.19),
  …) is an equality between elements computed by `jacobiSumT` and the
  `CycT` operations.
-/
import Azurite.AzPolyMod.Equiv.Cyclotomic
import Azurite.CohenLenstra.Algorithm_12_1
import Azurite.CrandallPomerance.Chapter4.GaussSums

namespace Azurite

namespace CL

open Finset Polynomial AzPolyMod

/-! ### `q`-primes -/

/-- **The `q`-primes of `t`**: primes `q` with `q − 1 ∣ t`, increasing. -/
def qPrimes (t : ℕ) : List ℕ :=
  (((Nat.divisors t).filter fun d => (d + 1).Prime).sort (· ≤ ·)).map (· + 1)

theorem mem_qPrimes {t q : ℕ} (ht : t ≠ 0) : q ∈ qPrimes t ↔ q.Prime ∧ (q - 1) ∣ t := by
  simp only [qPrimes, List.mem_map, Finset.mem_sort, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨d, ⟨⟨hd, -⟩, hp⟩, rfl⟩
    exact ⟨hp, by simpa using hd⟩
  · rintro ⟨hp, hd⟩
    refine ⟨q - 1, ⟨⟨hd, ht⟩, ?_⟩, Nat.sub_add_cancel hp.one_lt.le⟩
    rwa [Nat.sub_add_cancel hp.one_lt.le]

#guard qPrimes 12 = [2, 3, 5, 7, 13]
#guard (qPrimes 55440).length = 45

/-! ### Generators of `(ℤ/qℤ)ˣ` -/

/-- **Generator certificate**: `g ≠ 0`, `g^(q−1) = 1`, and `g^((q−1)/r) ≠ 1`
for every prime `r ∣ q − 1`. -/
def checkGenerator (q g : ℕ) : Bool :=
  decide ((g : ZMod q) ≠ 0) && decide ((g : ZMod q) ^ (q - 1) = 1)
    && (q - 1).primeFactorsList.all fun r => decide ((g : ZMod q) ^ ((q - 1) / r) ≠ 1)

/-- The least generator (generator-side search). -/
def findGenerator (q : ℕ) : Option ℕ := (List.range q).find? fun g => checkGenerator q g

/-- **A certified `g` generates `(ℤ/qℤ)ˣ`**. -/
theorem checkGenerator_spec {q g : ℕ} [Fact q.Prime] (h : checkGenerator q g = true) :
    ∃ gu : (ZMod q)ˣ, (gu : ZMod q) = g ∧ ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu := by
  have hq := Fact.out (p := q.Prime)
  simp only [checkGenerator, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hne, hpow⟩, hd⟩ := h
  refine ⟨Units.mk0 _ hne, Units.val_mk0 _, ?_⟩
  have hq1 : 0 < q - 1 := by have := hq.two_le; omega
  have hord : orderOf (Units.mk0 (g : ZMod q) hne) = q - 1 := by
    refine orderOf_eq_of_pow_and_pow_div_prime hq1 ?_ ?_
    · ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact hpow
    · intro r hr hrd hcon
      have hmem : r ∈ (q - 1).primeFactorsList :=
        (Nat.mem_primeFactorsList (by omega)).mpr ⟨hr, hrd⟩
      apply hd r hmem
      have hval := congrArg Units.val hcon
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at hval
  intro u
  have htop : Subgroup.zpowers (Units.mk0 (g : ZMod q) hne) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [htop]
  exact Subgroup.mem_top u

#guard checkGenerator 13 2 = true
#guard checkGenerator 13 3 = false
#guard findGenerator 13 = some 2
#guard findGenerator 19 = some 2
#guard (findGenerator 55441).isSome = true

/-! ### The index table `1 − g^x = g^(f x)` -/

/-- **Index-table certificate**: `g^(f x) = 1 − g^x` for `1 ≤ x ≤ q − 2`. -/
def checkIndexTable (q g : ℕ) (f : ℕ → ℕ) : Bool :=
  (List.range (q - 2)).all fun i =>
    decide ((g : ZMod q) ^ f (i + 1) = 1 - (g : ZMod q) ^ (i + 1))

theorem checkIndexTable_spec {q g : ℕ} {f : ℕ → ℕ} (h : checkIndexTable q g f = true) :
    ∀ x ∈ Finset.Icc 1 (q - 2), (g : ZMod q) ^ f x = 1 - (g : ZMod q) ^ x := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  have := List.all_eq_true.mp h (x - 1) (List.mem_range.mpr (by omega))
  rw [decide_eq_true_eq, Nat.sub_add_cancel hx.1] at this
  exact this

/-- The discrete-log table `dlog[g^i mod q] = i` (generator-side). -/
def dlogTable (q g : ℕ) : Array ℕ :=
  (List.range (q - 1)).foldl (fun arr i => arr.setIfInBounds ((g : ZMod q) ^ i).val i)
    (Array.replicate q 0)

/-- The index table `f x = dlog(1 − g^x)` (generator-side; certify with
`checkIndexTable`). -/
def indexTable (q g : ℕ) : ℕ → ℕ :=
  let tbl := dlogTable q g
  fun x => tbl.getD (1 - (g : ZMod q) ^ x).val 0

#guard checkIndexTable 13 2 (indexTable 13 2) = true
#guard checkIndexTable 19 2 (indexTable 19 2) = true
#guard checkIndexTable 13 2 (fun _ => 0) = false

/-! ### The Jacobi-sum tables -/

/-- **The coordinate vector of `ζ^l`** (`l < p^k`) in the power basis of
`ℤ[ζ_{p^k}]`: the unit vector at `l` if `l < m = (p−1)p^(k−1)`, else `−1`
at the positions `≡ l (mod p^(k−1))` (the (1.1)(b2) reduction rule). -/
def zetaCoeff (p k l i : ℕ) : ℤ :=
  if l < (p - 1) * p ^ (k - 1) then (if i = l then 1 else 0)
  else (if i % p ^ (k - 1) = l % p ^ (k - 1) then -1 else 0)

/-- **The (1.1)(b2) table** `Σ_{x=1}^{q−2} ζ^(a·x + b·f(x))` in `CycT n p k`,
as a coefficient vector. -/
def jacobiSumT (n : AzNat) (p k q : ℕ) [Fact (1 < n.toNat)] (f : ℕ → ℕ) (a b : ℕ) :
    CycT n p k :=
  ofCoeffFn ((p - 1) * p ^ (k - 1)) fun i =>
    ((∑ x ∈ Finset.Icc 1 (q - 2), zetaCoeff p k ((a * x + b * f x) % p ^ k) i : ℤ) : AzZMod n)

section Correctness

variable {R : Type _} [CommRing R] {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {z : R}
  (hz : eval₂ (Int.castRingHom R) z (cyclotomic (p ^ k) ℤ) = 0)
include hp hk hz

/-- **`zetaCoeff` is the coordinate vector of `z^l`** for `l < p^k`. -/
theorem sum_zetaCoeff {l : ℕ} (hl : l < p ^ k) :
    ∑ i ∈ Finset.range ((p - 1) * p ^ (k - 1)), ((zetaCoeff p k l i : ℤ) : R) * z ^ i = z ^ l := by
  have hN : p ^ k = (p - 1) * p ^ (k - 1) + p ^ (k - 1) := by
    have h1 : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
    have h2 : (p - 1) * p ^ (k - 1) = p * p ^ (k - 1) - p ^ (k - 1) := Nat.sub_one_mul _ _
    have h3 : p ^ (k - 1) ≤ p * p ^ (k - 1) := Nat.le_mul_of_pos_left _ hp.pos
    omega
  by_cases hlm : l < (p - 1) * p ^ (k - 1)
  · have hc : ∀ i, ((zetaCoeff p k l i : ℤ) : R) = if i = l then 1 else 0 := fun i => by
      rw [zetaCoeff, if_pos hlm]
      split_ifs <;> simp
    simp_rw [hc]
    exact unitVec_sum z hlm
  · have hc : ∀ i, ((zetaCoeff p k l i : ℤ) : R)
        = if i % p ^ (k - 1) = l % p ^ (k - 1) then (-1 : R) else 0 := fun i => by
      rw [zetaCoeff, if_neg hlm]
      split_ifs <;> simp
    simp_rw [hc]
    have hP : 0 < p ^ (k - 1) := pow_pos hp.pos _
    have hlP : l % p ^ (k - 1) < p ^ (k - 1) := Nat.mod_lt _ hP
    have hl' : l % p ^ (k - 1) + (p - 1) * p ^ (k - 1) = l := by
      obtain ⟨r, hr⟩ : ∃ r, l = (p - 1) * p ^ (k - 1) + r := ⟨l - (p - 1) * p ^ (k - 1), by omega⟩
      have hrP : r < p ^ (k - 1) := by omega
      rw [hr, mul_comm (p - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hrP, add_comm]
    rw [negPattern_sum hp hk hz hlP, hl']

end Correctness

section Model

open CP

variable (n : AzNat) {p k q : ℕ} [Fact (1 < n.toNat)] (hp : p.Prime) (hk : 0 < k)
  [Fact q.Prime]
include hp hk

omit [Fact q.Prime] in
/-- **The table is `Σ_x ζ^(a·x + b·f(x))`** in the `AdjoinRoot` model of `CycT`. -/
theorem toAdjoin_jacobiSumT (f : ℕ → ℕ) (a b : ℕ) :
    toAdjoin (jacobiSumT n p k q f a b)
      = ∑ x ∈ Finset.Icc 1 (q - 2), toAdjoin (zetaT n p k) ^ (a * x + b * f x) := by
  have hf := AzPolynomial.monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  have hz := eval₂_root_cyclotomic_int n p k hp hk
  have hz1 := pow_eq_one_of_cyclotomic hz
  rw [jacobiSumT, toAdjoin_ofCoeffFn hf, toAdjoin_zetaT]
  have h1 : ∀ i, AdjoinRoot.of (AzPolynomial.toPoly (AzPolynomial.cyclotomicPrimePow (AzZMod n) p k))
      ((∑ x ∈ Finset.Icc 1 (q - 2), zetaCoeff p k ((a * x + b * f x) % p ^ k) i : ℤ) : AzZMod n)
      = ∑ x ∈ Finset.Icc 1 (q - 2),
          ((zetaCoeff p k ((a * x + b * f x) % p ^ k) i : ℤ)
            : AdjoinRoot (AzPolynomial.toPoly (AzPolynomial.cyclotomicPrimePow (AzZMod n) p k))) :=
      fun i => by
    rw [map_intCast, Int.cast_sum]
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_zetaCoeff hp hk hz (Nat.mod_lt _ (pow_pos hp.pos k))]
  exact (pow_eq_pow_of_modEq hz1 (Nat.mod_modEq _ _).symm).symm

omit hk in
/-- **The character `χ` with `χ(g) = ζ_{p^k}`** into the model `ℤ[ζ_{p^k}]`. -/
noncomputable def chiT (hpk : p ^ k ∣ q - 1) {gu : (ZMod q)ˣ}
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) : MulChar (ZMod q) (CycM (p ^ k)) :=
  MulChar.ofRootOfUnity
    (CP.mem_rootsOfUnity_card_units_of_dvd (zetaMUnit_pow_eq_one (pow_pos hp.pos k)) hpk) hg

omit hk in
theorem chiT_gen (hpk : p ^ k ∣ q - 1) {gu : (ZMod q)ˣ}
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) :
    chiT hp hpk hg gu = zetaM (p ^ k) := by
  rw [chiT, MulChar.ofRootOfUnity_spec]
  rfl

/-- **The computable table is the reduction of the abstract Jacobi sum**:
for a certified generator `g` and index table `f`,
`jacobiSumT n p k q f a b = reduceCycT (j(χ^a, χ^b))` with `χ(g) = ζ_{p^k}`. -/
theorem jacobiSumT_eq_reduce (hpk : p ^ k ∣ q - 1) {gu : (ZMod q)ˣ}
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) {f : ℕ → ℕ}
    (hf : ∀ x ∈ Finset.Icc 1 (q - 2), ((gu : ZMod q)) ^ f x = 1 - ((gu : ZMod q)) ^ x)
    (a b : ℕ) :
    jacobiSumT n p k q f a b
      = reduceCycT n p k hp hk (jacobiSum (chiT hp hpk hg ^ a) (chiT hp hpk hg ^ b)) := by
  have hfm := AzPolynomial.monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  apply toAdjoin_injective hfm hfm.ne_zero
  rw [toAdjoin_jacobiSumT n hp hk, jacobiSum_eq_sum_gen_pow hg hf, chiT_gen, map_sum]
  have hsum : toAdjoin (∑ x ∈ Finset.Icc 1 (q - 2),
        reduceCycT n p k hp hk (zetaM (p ^ k) ^ (a * x + b * f x)))
      = ∑ x ∈ Finset.Icc 1 (q - 2),
          toAdjoin (reduceCycT n p k hp hk (zetaM (p ^ k) ^ (a * x + b * f x))) := by
    rw [← ringEquivAdjoinRoot_apply, map_sum]
    rfl
  rw [hsum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_pow, reduceCycT_zetaM,
    show zetaT n p k ^ (a * x + b * f x) = (zetaT n p k).pow (a * x + b * f x) from rfl,
    toAdjoin_pow hfm hfm.ne_zero]

end Model

/-! ### Guards: `j(χ,χ)·j(χ̄,χ̄) = q` for `χ² ≠ 1`, computed in `CycT` at `n = 101` -/

section Guards

instance : Fact (1 < (AzNat.ofNat 101).toNat) := ⟨by rw [AzNat.toNat_ofNat]; norm_num⟩

private abbrev n101 : AzNat := AzNat.ofNat 101

-- `p^k = 3`, `q = 13`: `σ₂ = conjugation`
#guard let j := jacobiSumT n101 3 1 13 (indexTable 13 2) 1 1
       j * sigmaT 2 j = (13 : CycT n101 3 1)
-- `p^k = 4`, `q = 13`: `σ₃ = conjugation`
#guard let j := jacobiSumT n101 2 2 13 (indexTable 13 2) 1 1
       j * sigmaT 3 j = (13 : CycT n101 2 2)
-- `p^k = 9`, `q = 19`: `σ₈ = conjugation`
#guard let j := jacobiSumT n101 3 2 19 (indexTable 19 2) 1 1
       j * sigmaT 8 j = (19 : CycT n101 3 2)
-- `p^k = 16`, `q = 17`
#guard let j := jacobiSumT n101 2 4 17 (indexTable 17 3) 1 1
       j * sigmaT 15 j = (17 : CycT n101 2 4)

end Guards

end CL

end Azurite
