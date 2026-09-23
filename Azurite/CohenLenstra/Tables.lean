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
  ((List.range (q - 1)).foldl
    (fun (st : Array ℕ × ZMod q) i => (st.1.setIfInBounds st.2.val i, st.2 * (g : ZMod q)))
    (Array.replicate q 0, 1)).1

/-- The index table as an array: `f x = dlog(1 − g^x)` for `x < q − 1` (generator-side;
certify with `checkIndexTable`).  Materialized once — a partially applied function would
recompute the discrete-log table at every lookup. -/
def indexTableArr (q g : ℕ) : Array ℕ :=
  let tbl := dlogTable q g
  ((List.range (q - 1)).foldl
    (fun (st : Array ℕ × ZMod q) x => (st.1.setIfInBounds x (tbl.getD (1 - st.2).val 0), st.2 * (g : ZMod q)))
    (Array.replicate (q - 1) 0, 1)).1

/-- Lookup in a materialized index table. -/
def indexTableOf (tbl : Array ℕ) (x : ℕ) : ℕ := tbl.getD x 0

/-- The index table as a function (for guards and generators; checkers should bind
`indexTableArr` once and use `indexTableOf`). -/
def indexTable (q g : ℕ) : ℕ → ℕ := indexTableOf (indexTableArr q g)

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
as a coefficient vector — the specification form, one sum per coefficient. -/
def jacobiSumTSum (n : AzNat) (p k q : ℕ) [Fact (1 < n.toNat)] (f : ℕ → ℕ) (a b : ℕ) :
    CycT n p k :=
  ofCoeffFn ((p - 1) * p ^ (k - 1)) fun i =>
    ((∑ x ∈ Finset.Icc 1 (q - 2), zetaCoeff p k ((a * x + b * f x) % p ^ k) i : ℤ) : AzZMod n)

/-- **The exponent-class counts** `c_l = #{1 ≤ x ≤ q − 2 : a·x + b·f(x) ≡ l (mod p^k)}`,
in one pass over `x`. -/
def expCounts (p k q : ℕ) (f : ℕ → ℕ) (a b : ℕ) : Array ℕ :=
  (List.range (q - 2)).foldl
    (fun arr x' => arr.modify ((a * (x' + 1) + b * f (x' + 1)) % p ^ k) (· + 1))
    (Array.replicate (p ^ k) 0)

/-- **The (1.1)(b2) table**, computed from the exponent-class counts: the coefficient of
`ζ^i` (`i < m = (p−1)p^(k−1)`) is `c_i − c_(m + (i mod p^(k−1)))`, since the class
`l = m + (i mod p^(k−1))` is the unique `l ≥ m` with `ζ^l` having `−1` at position `i`.
Cost `O(q + p^k)` instead of `O(m·q)`; equal to `jacobiSumTSum` (`jacobiSumT_eq_sum`). -/
def jacobiSumT (n : AzNat) (p k q : ℕ) [Fact (1 < n.toNat)] (f : ℕ → ℕ) (a b : ℕ) :
    CycT n p k :=
  let c := expCounts p k q f a b
  let m := (p - 1) * p ^ (k - 1)
  ofCoeffFn m fun i => (((c.getD i 0 : ℤ) - (c.getD (m + i % p ^ (k - 1)) 0 : ℤ) : ℤ) : AzZMod n)

section Counts

/-- The fold invariant of `expCounts`: entry `l` counts the `x ≤ t` in class `l`. -/
theorem foldl_modify_count {P : ℕ} (e : ℕ → ℕ) (he : ∀ x, e x < P) (init : Array ℕ)
    (hsize : init.size = P) {l : ℕ} (hl : l < P) :
    ∀ t : ℕ, ((List.range t).foldl (fun arr x' => arr.modify (e (x' + 1)) (· + 1)) init).getD l 0
      = init.getD l 0 + ((Finset.Icc 1 t).filter fun x => e x = l).card
  | 0 => by simp
  | t + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsz : ∀ t, ((List.range t).foldl (fun arr x' => arr.modify (e (x' + 1)) (· + 1)) init).size
        = P := by
      intro t
      induction t with
      | zero => simpa using hsize
      | succ t ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          Array.size_modify, ih]
    set A := (List.range t).foldl (fun arr x' => arr.modify (e (x' + 1)) (· + 1)) init with hA
    have hIcc : (Finset.Icc 1 (t + 1)).filter (fun x => e x = l)
        = ((Finset.Icc 1 t).filter fun x => e x = l) ∪
          (if e (t + 1) = l then {t + 1} else ∅) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      split_ifs with h <;> simp only [Finset.mem_singleton, Finset.notMem_empty, or_false]
      · constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases Nat.lt_or_ge x (t + 1) with h4 | h4
          · exact Or.inl ⟨⟨h1, by omega⟩, h3⟩
          · exact Or.inr (by omega)
        · rintro (⟨⟨h1, h2⟩, h3⟩ | rfl)
          · exact ⟨⟨h1, by omega⟩, h3⟩
          · exact ⟨⟨by omega, le_rfl⟩, h⟩
      · constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨⟨h1, ?_⟩, h3⟩
          rcases Nat.lt_or_ge x (t + 1) with h4 | h4
          · omega
          · exfalso
            exact h (by rw [show x = t + 1 by omega] at h3; exact h3)
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h1, by omega⟩, h3⟩
    have hdisj : Disjoint ((Finset.Icc 1 t).filter fun x => e x = l)
        (if e (t + 1) = l then {t + 1} else ∅) := by
      split_ifs
      · rw [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_Icc]
        omega
      · exact Finset.disjoint_empty_right _
    rw [hIcc, Finset.card_union_of_disjoint hdisj, ← add_assoc,
      ← foldl_modify_count e he init hsize hl t]
    have hlA : l < A.size := by rw [hA, hsz]; exact hl
    have hlA' : l < (A.modify (e (t + 1)) (· + 1)).size := by rw [Array.size_modify]; exact hlA
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlA',
      Array.getElem?_eq_getElem hlA, Option.getD_some, Option.getD_some, Array.getElem_modify]
    split_ifs with h1 <;> simp

theorem expCounts_getD {p k q : ℕ} (hp : 0 < p ^ k) (f : ℕ → ℕ) (a b : ℕ) {l : ℕ} (hl : l < p ^ k) :
    (expCounts p k q f a b).getD l 0
      = ((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ k = l).card := by
  have := foldl_modify_count (fun x => (a * x + b * f x) % p ^ k) (fun x => Nat.mod_lt _ hp)
    (Array.replicate (p ^ k) 0) (by simp) hl (q - 2)
  rw [expCounts, this, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hl,
    Option.getD_some, zero_add]

variable {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
include hp hk

/-- **The coefficient identity**: the per-coefficient sum of `zetaCoeff` over the classes
equals `c_i − c_(m + (i mod p^(k−1)))`. -/
theorem sum_zetaCoeff_eq_counts (q : ℕ) (f : ℕ → ℕ) (a b : ℕ) {i : ℕ}
    (hi : i < (p - 1) * p ^ (k - 1)) :
    ∑ x ∈ Finset.Icc 1 (q - 2), zetaCoeff p k ((a * x + b * f x) % p ^ k) i
      = (((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ k = i).card : ℤ)
        - (((Finset.Icc 1 (q - 2)).filter fun x =>
            (a * x + b * f x) % p ^ k = (p - 1) * p ^ (k - 1) + i % p ^ (k - 1)).card : ℤ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hi ⊢
  set m := (p - 1) * p ^ k' with hm
  set P := p ^ k' with hP
  have hP0 : 0 < P := pow_pos hp.pos _
  have hpk : p ^ (k' + 1) = m + P := by
    rw [pow_succ, hm, hP, Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hp.pos),
      mul_comm]
  have hiP : i % P < P := Nat.mod_lt i hP0
  have hmaps : ∀ x ∈ Finset.Icc 1 (q - 2),
      (a * x + b * f x) % p ^ (k' + 1) ∈ Finset.range (p ^ (k' + 1)) := fun x _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos hp.pos _))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ y ∈ Finset.range (p ^ (k' + 1)),
      ∑ x ∈ (Finset.Icc 1 (q - 2)).filter (fun x => (a * x + b * f x) % p ^ (k' + 1) = y),
          zetaCoeff p (k' + 1) ((a * x + b * f x) % p ^ (k' + 1)) i
        = ((((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ (k' + 1) = y).card : ℤ))
          * zetaCoeff p (k' + 1) y i := by
    intro y _
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le m)
    (by omega : m ≤ p ^ (k' + 1))]
  -- the low part
  have hlow : ∑ y ∈ Finset.Ico 0 m,
      ((((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ (k' + 1) = y).card : ℤ))
        * zetaCoeff p (k' + 1) y i
      = (((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ (k' + 1) = i).card : ℤ) := by
    rw [Finset.sum_eq_single i]
    · rw [zetaCoeff, Nat.add_sub_cancel, if_pos hi, if_pos rfl, mul_one]
    · intro y hy hyi
      rw [zetaCoeff, Nat.add_sub_cancel, if_pos (Finset.mem_Ico.mp hy).2, if_neg (Ne.symm hyi), mul_zero]
    · intro h
      exact absurd (Finset.mem_Ico.mpr ⟨Nat.zero_le _, hi⟩) h
  -- the high part
  have hhigh : ∑ y ∈ Finset.Ico m (p ^ (k' + 1)),
      ((((Finset.Icc 1 (q - 2)).filter fun x => (a * x + b * f x) % p ^ (k' + 1) = y).card : ℤ))
        * zetaCoeff p (k' + 1) y i
      = -(((Finset.Icc 1 (q - 2)).filter fun x =>
          (a * x + b * f x) % p ^ (k' + 1) = m + i % P).card : ℤ) := by
    have hmP : m % P = 0 := by rw [hm]; exact Nat.mul_mod_left _ _
    rw [Finset.sum_eq_single (m + i % P)]
    · rw [zetaCoeff, Nat.add_sub_cancel, if_neg (by omega), if_pos (by rw [Nat.add_mod, hmP, zero_add,
        Nat.mod_mod, Nat.mod_eq_of_lt hiP]), mul_neg_one]
    · intro y hy hyi
      rw [Finset.mem_Ico] at hy
      rw [zetaCoeff, Nat.add_sub_cancel, if_neg (by omega), if_neg, mul_zero]
      intro heq
      apply hyi
      obtain ⟨r, hr⟩ : ∃ r, y = m + r := ⟨y - m, by omega⟩
      have hrP : r < P := by omega
      rw [hr, Nat.add_mod, hmP, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hrP] at heq
      rw [hr, ← heq]
    · intro h
      exact absurd (Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩) h
  rw [hlow, hhigh, sub_eq_add_neg]

end Counts

/-- **The fast table is the specification table.** -/
theorem jacobiSumT_eq_sum (n : AzNat) {p k : ℕ} (q : ℕ) [Fact (1 < n.toNat)] (hp : p.Prime)
    (hk : 0 < k) (f : ℕ → ℕ) (a b : ℕ) :
    jacobiSumT n p k q f a b = jacobiSumTSum n p k q f a b := by
  unfold jacobiSumT jacobiSumTSum ofCoeffFn
  dsimp only
  refine congrArg (fun F => ofPoly (AzPolynomial.normalize (Array.ofFn F))) (funext fun ⟨i, hi⟩ => ?_)
  simp only
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  have hpk : (p - 1) * p ^ (k - 1) + p ^ (k - 1) = p ^ k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hp.pos), mul_comm]
  have hiP := Nat.mod_lt i (pow_pos hp.pos (k - 1))
  rw [expCounts_getD hpk0 f a b (by omega), expCounts_getD hpk0 f a b (by omega),
    sum_zetaCoeff_eq_counts hp hk q f a b hi]

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
  rw [jacobiSumT_eq_sum n q hp hk, jacobiSumTSum, toAdjoin_ofCoeffFn hf, toAdjoin_zetaT]
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
