/-
  Crandall–Pomerance, Exercise 4.24, and the product-character engine
  of Theorem 4.4.6 (correctness of the Gauss sums primality test,
  Algorithm 4.4.5).

  Exercise 4.24: a character mod `q` of maximal order `q − 1` is
  one-to-one on `Z_q` (`exercise_4_24`).  The unit group is cyclic;
  the character's order equals the order of its value at a generator
  (`orderOf_mulChar_eq`, the abstract form of the
  `orderOf_ofRootOfUnity` computation in `GaussSums.lean`), so that
  value is a primitive `(q−1)`-th root of unity and the powers
  `χ(g^k) = χ(g)^k` are pairwise distinct; nonunits go to `0`, which
  no root of unity equals.

  The engine (`eq_of_forall_primeFactor_char_eq`): for `q − 1`
  squarefree, characters `χ_p` of order `p` for each prime
  `p ∣ q − 1` multiply into a character of order
  `∏ p = q − 1` (coprime orders in the commutative monoid of
  characters, `orderOf_prod_primes`) — Exercise 4.24 then makes the
  product injective, so units agreeing under every `χ_p` are EQUAL.
  This is the final step of the proof of Theorem 4.4.6: from
  `χ_(p,q)(r) = χ_(p,q)(l^a)` for all primes `p ∣ q − 1` conclude
  `r ≡ l^a (mod q)` — for every prime `q ∣ F`, whence `r ≡ l^a
  (mod F)` by the CRT and the divisor search finds `r`.  (The book
  runs this for odd `q` and special-cases `l(2) = 0`; here `q = 2`
  needs no special case — the empty product is the trivial
  character, injective on the trivial unit group.)
-/
import Azurite.CrandallPomerance.Chapter4.GaussSums
import Mathlib.Data.Nat.Squarefree

namespace Azurite

namespace CP

open Finset

section OrderOf

variable {M : Type _} [CommMonoid M] {R : Type _} [CommMonoidWithZero R]

/-- The order of a character on a monoid with cyclic unit group is
the order of its value at a generator (the abstract form of
`orderOf_ofRootOfUnity`). -/
theorem orderOf_mulChar_eq {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (χ : MulChar M R) : orderOf χ = orderOf (χ (g : M)) := by
  rw [orderOf_eq_orderOf_iff]
  intro k
  constructor
  · intro h
    have happ := congrArg (fun χ' : MulChar M R => χ' (g : M)) h
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using happ
  · intro h
    rw [MulChar.eq_iff hg, MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact h

end OrderOf

variable {q : ℕ} [Fact q.Prime] {R : Type _} [CommMonoidWithZero R]
  [NoZeroDivisors R] [Nontrivial R]

/-- **Exercise 4.24**: a character mod `q` of order `q − 1` is
one-to-one on `Z_q`. -/
theorem exercise_4_24 (χ : MulChar (ZMod q) R)
    (hχ : orderOf χ = q - 1) : Function.Injective χ := by
  have hq := Fact.out (p := q.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hgord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hq]
  have hζord : orderOf (χ (g : ZMod q)) = q - 1 := by
    rw [← orderOf_mulChar_eq hg, hχ]
  have hζfin : IsOfFinOrder (χ (g : ZMod q)) := by
    rw [← orderOf_pos_iff, hζord]
    have := hq.two_le
    omega
  have hζ0 : χ (g : ZMod q) ≠ 0 := by
    intro h0
    have h2 := hq.two_le
    have := pow_orderOf_eq_one (χ (g : ZMod q))
    rw [hζord, h0, zero_pow (by omega : q - 1 ≠ 0)] at this
    exact zero_ne_one this
  -- a unit value is a power of `χ g`, hence nonzero
  have hval : ∀ x : (ZMod q)ˣ, ∃ i : ℕ, χ (x : ZMod q) = χ (g : ZMod q) ^ i
      ∧ g ^ i = x := by
    intro x
    have hmem : x ∈ Submonoid.powers g :=
      (mem_powers_iff_mem_zpowers ..).mpr (hg x)
    obtain ⟨i, hi⟩ := hmem
    have hi' : g ^ i = x := hi
    refine ⟨i, ?_, hi'⟩
    rw [← hi', Units.val_pow_eq_pow_val, map_pow]
  intro x y hxy
  by_cases hx : IsUnit x <;> by_cases hy : IsUnit y
  · lift x to (ZMod q)ˣ using hx
    lift y to (ZMod q)ˣ using hy
    obtain ⟨i, hix, hgx⟩ := hval x
    obtain ⟨j, hjy, hgy⟩ := hval y
    rw [hix, hjy] at hxy
    have hij : i ≡ j [MOD q - 1] := by
      have := (hζfin.pow_eq_pow_iff_modEq).mp hxy
      rwa [hζord] at this
    have hgfin : IsOfFinOrder g := by
      rw [← orderOf_pos_iff, hgord]
      have := hq.two_le
      omega
    have : g ^ i = g ^ j := by
      rw [hgfin.pow_eq_pow_iff_modEq, hgord]
      exact hij
    rw [← hgx, ← hgy, this]
  · exfalso
    obtain ⟨xu, rfl⟩ := hx
    obtain ⟨i, hix, -⟩ := hval xu
    rw [MulChar.map_nonunit χ hy, hix] at hxy
    exact pow_ne_zero i hζ0 hxy
  · exfalso
    obtain ⟨yu, rfl⟩ := hy
    obtain ⟨j, hjy, -⟩ := hval yu
    rw [MulChar.map_nonunit χ hx, hjy] at hxy
    exact pow_ne_zero j hζ0 hxy.symm
  · rw [isUnit_iff_ne_zero, not_not] at hx hy
    rw [hx, hy]

/-- The order of a product of commuting elements of pairwise distinct
prime orders is the product of the orders. -/
theorem orderOf_prod_primes {M : Type _} [CommMonoid M] (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (f : ℕ → M)
    (hord : ∀ p ∈ s, orderOf (f p) = p) :
    orderOf (∏ p ∈ s, f p) = ∏ p ∈ s, p := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime,
      hord a (mem_insert_self a s),
      ih (fun p hp => hs p (mem_insert_of_mem hp))
        (fun p hp => hord p (mem_insert_of_mem hp))]
    rw [hord a (mem_insert_self a s),
      ih (fun p hp => hs p (mem_insert_of_mem hp))
        (fun p hp => hord p (mem_insert_of_mem hp))]
    exact Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes (hs a (mem_insert_self a s))
        (hs p (mem_insert_of_mem hp))).mpr
        (fun h => ha (h ▸ hp))

omit [NoZeroDivisors R] [Nontrivial R] in
/-- Evaluating a product of characters at a unit is the product of
the values.  (False at nonunits for the empty product: the trivial
character sends nonunits to `0`.) -/
theorem prod_mulChar_apply_isUnit {ι : Type _} [DecidableEq ι] (s : Finset ι)
    (χ : ι → MulChar (ZMod q) R) {x : ZMod q} (hx : IsUnit x) :
    (∏ p ∈ s, χ p) x = ∏ p ∈ s, χ p x := by
  obtain ⟨u, rfl⟩ := hx
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    rfl

/-- **The product-character engine of Theorem 4.4.6**: for `q − 1`
squarefree and characters `χ_p` of order `p` for every prime
`p ∣ q − 1`, units agreeing under every `χ_p` are equal — the step
concluding `r ≡ l^a (mod q)` from the per-`p` congruences
`χ_(p,q)(r) = χ_(p,q)(l^a)`. -/
theorem eq_of_forall_primeFactor_char_eq (hsq : Squarefree (q - 1))
    (χ : ℕ → MulChar (ZMod q) R)
    (hord : ∀ p ∈ (q - 1).primeFactors, orderOf (χ p) = p)
    {x y : ZMod q} (hx : IsUnit x) (hy : IsUnit y)
    (h : ∀ p ∈ (q - 1).primeFactors, χ p x = χ p y) : x = y := by
  have hinj : Function.Injective ⇑(∏ p ∈ (q - 1).primeFactors, χ p) := by
    apply exercise_4_24
    rw [orderOf_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      _ hord, Nat.prod_primeFactors_of_squarefree hsq]
  apply hinj
  rw [prod_mulChar_apply_isUnit _ _ hx, prod_mulChar_apply_isUnit _ _ hy]
  exact Finset.prod_congr rfl h

end CP

end Azurite
