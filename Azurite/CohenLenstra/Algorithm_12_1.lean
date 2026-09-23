/-
  **Cohen–Lenstra (12.1), Step 1: preparation of tables.**

  The detailed description of the algorithm begins.  Step 1
  prepares tables depending only on the bound `N` — mapped onto
  the formal inventory:

  (a) Select `t` with `e(t) > N^(1/2)` — our computable `e` of
      Proposition (4.1) (Table 1 = our `e(2) = 24`,
      `e(12) = 65520`, `e(60) = 6814407600`, `e(5040)` guards).

  (b1) For each odd prime `q ∣ e(t)`: a primitive root `g` mod `q`
      and the *index table* `f : {1,…,q−2} → {1,…,q−2}` with
      `1 − g^x ≡ g^(f(x)) (mod q)` (well-defined: `g^x ≠ 1` for
      `1 ≤ x ≤ q−2`, so `1 − g^x` is a nonzero, non-unity power of
      `g`; construction is generator-side, the table is certified
      by its defining property).

  (b2) For each prime `p ∣ q − 1`, `k = v_p(q−1)`: the Jacobi-sum
      tables.  The correctness content, proved here
      (`jacobiSum_eq_sum_gen_pow`): for the character `χ` with
      `χ(g) = ζ` and ANY exponents `a, b`,

        `j(χ^a, χ^b) = Σ_{x=1}^{q−2} ζ^(a·x + b·f(x))`,

      identifying the table sums with Mathlib's `jacobiSum` — at
      `(a,b) = (1,1)` this is (b2b)'s `j_{p,q} = j(χ,χ)`; at
      `(2,1)` it gives the second factor of (b2f)'s
      `j*_{2,q} = j(χ,χ)·j(χ,χ²) = j(χ,χ,χ)` (our (9.7)-form,
      via `jacobiSum_comm`); at `(3·2^(k−3), 2^(k−3))` it gives
      `j#_{2,q} = j(φ,φ³)²` with `φ = χ^(2^(k−3))`
      (`ζ_8 = ζ_{2^k}^(2^(k−3))`).

      The tabulated powers are exactly the products consumed by
      our test theorems: (b2c)'s `j_{v,p,q} = j_{p,q}^(α(v))`
      (odd `p`; the paper fixes `(a,b) = (1,1)`, which satisfies
      (8.6) for `p > 2`) is the (8.8)-product of Theorem (8.5) at
      `n := v`; (b2d)/(b2e) (`p = 2`, `k ≤ 2`) are the
      (9.2)/(9.4)/(9.6)-quantities of Theorems (9.1)–(9.5); and
      (b2f)'s `(j*)^(α(v))` for `v ∈ M` resp.
      `(j*)^(α(v))·j#` for `v ∈ L − M` are the (9.11)- resp.
      (9.20)-products of Theorems (9.10)/(9.19).  The element
      representation `Σ aᵢζ^i ↔ (aᵢ)_{i<φ(p^k)}` is our
      `CycM`-power-basis (`cycMBasis`).

  **Step 2: preliminary tests** (given `1 < n ≤ N`).

  (c) Optionally test for small divisors or run Miller–Rabin —
      our layered `isPrime` (proven-sound MR rejection).

  (d) Check `gcd(t·e(t), n) = 1`; a nontrivial gcd yields a prime
      divisor of `n` from the complete factorization of `t·e(t)`
      (bookkeeping; this establishes the `gcd(st, n) = 1`
      hypothesis of the central stage).

  (e) Select `s ∣ e(t)` with `s > n^(1/2)` and replace `t` by the
      least `t'` with `s ∣ e(t')`.  The paper's parenthetical —
      the new `t` is the exponent of `(ℤ/sℤ)ˣ` and divides the
      old `t` — is proved here (`dvd_e_iff_exponent_dvd`,
      `dvd_e_exponent_least`): by Proposition (4.1),
      `s ∣ e(t') ⟺ exponent((ℤ/s)ˣ) ∣ t'`, so the least such `t'`
      is the exponent itself, and it divides anything `s ∣ e(·)`
      admits — in particular the old `t`.  (This also re-verifies
      (2.3) for the new pair `(s, t)`.)

  **Step 3: pseudoprime tests with Jacobi sums** (for each prime
  `p ∣ t`).

  (f) The boolean `λ_p` records whether (6.4) is established;
      initialized `true` iff `p` is odd and `n^(p−1) ≢ 1 (mod p²)`
      — the Proposition (7.18) branch.

  (g) Write `n = u_k·p^k + v_k`, `0 ≤ v_k < p^k` — i.e.
      `u_k = n / p^k`, `v_k = n % p^k`.

  (h1) For each `q ∣ s` with `p ∣ q − 1`, `k = v_p(q−1)`: compute
      `j_{0,p,q}^u · j_{v,p,q} mod nℤ[ζ_{p^k}]` and demand it be
      `ζ_{p^k}^h` for some `h < p^k`; otherwise `n` is composite.
      The identity making the tables sufficient, proved here
      (`alphac_decomp`, `prod_pow_alphac_decomp`): the group-ring
      exponent splits *exactly* as `α(n) = u·θ + α(v)` —
      coefficient-wise `[nx/p^k] = u·x + [vx/p^k]` — so
      `j^(α(n)) = (j^θ)^u · j^(α(v)) = j₀^u · j_v`, stated
      generically over any commutative monoid so that one lemma
      covers the (8.8)-product of Theorem (8.5) (odd `p`,
      `a = b = 1`), and the (9.11)/(9.20)-products of
      Theorems (9.10)/(9.19) (`p = 2`, `k ≥ 3`; for `v ∈ L − M`
      the tabulated `j_v` carries the extra `j#`-factor, matching
      (9.20)).  For `p^k ∈ {2, 4}` the tests are
      (9.2)/(9.4)/(9.6) of Theorem (9.1).  The verdict `≡ ζ^h`
      is the `ζ'`-hypothesis of those theorems at `ζ' = ζ^h`.

  (h2) If `h ≢ 0 (mod p)` and (`p` odd, or `p^k = 2` with
      `n ≡ 1 (mod 4)`): set `λ_p := true` — the root `ζ^h` is
      primitive, so Theorem (7.19) applies for odd `p`; for
      `p^k = 2` the passed (9.2) with `h = 1` says
      `q^((n−1)/2) ≡ −1 (mod n)`, which is Proposition (7.24)'s
      witness at `a = q`.

  (h3) If `h` is odd, `p = 2`, `k ≥ 2` and `λ₂` is still false:
      test `q^((n−1)/2) ≡ −1 (mod n)` — failure proves `n`
      composite, success sets `λ₂ := true`.  This is the deferred
      Theorem (7.26) (used here purely as an *optimization*: our
      pipeline establishes `λ₂` via Procedure (11.5)/(10.8)
      regardless, so (h3) remains non-load-bearing and (7.26)
      stays deferred with its recorded reversal recipe).

  **Step 4: additional tests** (for each `p ∣ t` with `λ_p` still
  false) — Procedure (11.2)(d)/(e) in computational form; no new
  lemmas are needed, every branch mapping onto proven inventory.

  (i) Find a small prime `q ∤ s` with `q ≡ 1 (mod p)`,
      additionally `q ≡ 1 (mod 4)` when `p = 2, n ≡ 3 (mod 4)`,
      and `n^((q−1)/p) ≢ 1 (mod q)` — condition (11.3), the input
      of `isPrimitiveRoot_chi_natCast`.  If none is found below a
      reasonable limit: test whether `n` is a `p`-th power — if
      so, composite (`not_prime_of_eq_pow`); otherwise halt
      "unable" (the honest incompleteness of the unconditional
      algorithm, cf. (11.4)(a); a certificate-based checker never
      meets this branch).  Halt too if `q ∣ n` (then `n = q` or
      composite).

  (j) With `k = 2` if `p = 2, n ≡ 3 (mod 4)` and `k = 1`
      otherwise (the `q ≡ 1 mod 4` condition guarantees
      `4 ∣ q − 1`, so order-4 characters exist), build the mini
      tables `j_{0,p,q}`, `j_{v_k,p,q}` for the new `q` and test
      `j₀^(u_k)·j_(v_k) ≡ ζ_{p^k}^h` with `h ≢ 0 (mod p)` —
      the same `alphac_decomp` identity, now with the
      *primitivity* demand of (11.2)(e).  Failure proves `n`
      composite by Remark (11.4)(b); success runs (h2)/(h3).

      Note a genuine fork against §11: for `p = 2, n ≡ 3 (mod 4)`
      the detailed algorithm routes through the deferred (7.26)
      (via (h3) at `k = 2`), whereas Procedure (11.5) used the
      proven (10.8)-route (the `ξ`-test).  Both are sound; our
      certificate design resolves the fork in favor of (10.8), so
      (7.26) remains non-load-bearing.

  **Step 5: final trial divisions** — the (2.5)-consumer, and the
  capstone of the abstract pipeline.  With `r₀ = 1` and
  `r_i ≡ n·r_(i−1) (mod s)`, `0 ≤ r_i < s` (so `r_i = n^i mod s`):
  if `r_i = 1`, declare `n` prime ((l2)); if `r_i ∣ n` with
  `r_i < n`, declare `n` composite ((l3)); one of the two occurs
  for some `i ≤ t` since `n^t ≡ 1 (mod s)`
  (`pow_t_mod_eq_one`, from (2.3)).

  Soundness, proved here: (l3) is `not_prime_of_dvd_lt`; (l2) is
  **`step5_prime`** — given `n < s²` (condition (2.4)), the
  (2.5)-conclusion of Theorem (6.3), a clean sweep
  (no (l3)-hit for `1 ≤ j < i`), and `n^i mod s = 1`, the number
  `n` is prime: a composite `n` has a prime divisor
  `r ≤ √n < s`; by (2.5), `r ≡ n^j (mod s)`, and by the
  `n^i ≡ 1`-cycle `r ≡ n^(j mod i)`, so `r < s` pins
  `r = n^(j mod i) mod s` — either `j mod i = 0`, making `r = 1`
  (impossible), or the sweep already tested this candidate.  With
  this, the abstract soundness chain is complete end-to-end:
  Jacobi-sum congruences ⟹ (7.9) ⟹ Theorem (7.8) ⟹ (6.5) ⟹
  Theorem (6.3) ⟹ (2.5) ⟹ `n.Prime`.

  **Remarks (12.2)** (prose).  (a) Since `(a,b) = (1,1)` is fixed
  in (h1), condition (8.6) becomes `2^p ≢ 2 (mod p²)` — `p` not a
  Wieferich prime — which the checker verifies per `p ∣ t` (cheap;
  holds for all `p < 1093`, and in practice `p < 20`; cf. the
  `bValue`-guards of the C&P arc).  (b) The description leaves out
  the §10 ideals, the (3.1)-algorithm and the combination with the
  older tests of [26] — the improvements paper's territory; our
  pipeline has §10 formalized and the cert design will use it.
-/
import Azurite.CohenLenstra.Characters
import Azurite.CohenLenstra.Proposition_4_1
import Azurite.CohenLenstra.Theorem_8_5
import Mathlib.NumberTheory.JacobiSum.Basic

namespace Azurite

namespace CL

open Finset

/-- **The (12.1)(b1)-table computes the Jacobi sums**: if `g`
generates `(ℤ/q)ˣ` and the index table `f` satisfies
`1 − g^x = g^(f(x))` for `1 ≤ x ≤ q − 2`, then for any character
`χ` mod `q` and any exponents `a, b`,
`j(χ^a, χ^b) = Σ_{x=1}^{q−2} χ(g)^(a·x + b·f(x))` — the sums of
steps (b2b) and (b2f) are Jacobi sums. -/
theorem jacobiSum_eq_sum_gen_pow {R : Type _} [CommRing R] {q : ℕ}
    [Fact q.Prime] {gu : (ZMod q)ˣ}
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)
    {χ : MulChar (ZMod q) R} {f : ℕ → ℕ}
    (hf : ∀ x ∈ Finset.Icc 1 (q - 2),
      ((gu : ZMod q)) ^ f x = 1 - ((gu : ZMod q)) ^ x)
    (a b : ℕ) :
    jacobiSum (χ ^ a) (χ ^ b)
      = ∑ x ∈ Finset.Icc 1 (q - 2), (χ ↑gu) ^ (a * x + b * f x) := by
  have hq := Fact.out (p := q.Prime)
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  have hq2 : 2 ≤ q := hq.two_le
  have hgord : orderOf gu = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units]
  -- the sum over `ℤ/q` restricts to `u ∉ {0, 1}`
  have hzero1 : ∀ u : ZMod q, ¬ IsUnit u → (χ ^ a) u = 0 :=
    fun u hu => MulChar.map_nonunit _ hu
  have hrestrict : jacobiSum (χ ^ a) (χ ^ b)
      = ∑ u ∈ (Finset.univ : Finset (ZMod q)) \ {0, 1},
          (χ ^ a) u * (χ ^ b) (1 - u) := by
    rw [jacobiSum]
    refine (Finset.sum_subset (Finset.sdiff_subset) fun u _ hu => ?_).symm
    rw [Finset.mem_sdiff, not_and, not_not] at hu
    have hu01 : u = 0 ∨ u = 1 := by
      have := hu (Finset.mem_univ u)
      simpa using this
    have h0nu : ¬ IsUnit (0 : ZMod q) := not_isUnit_zero
    rcases hu01 with rfl | rfl
    · rw [hzero1 0 h0nu, zero_mul]
    · rw [sub_self, MulChar.map_nonunit (χ ^ b) h0nu, mul_zero]
  rw [hrestrict]
  -- reindex by powers of the generator
  refine (Finset.sum_nbij (fun x => ((gu ^ x : (ZMod q)ˣ) : ZMod q))
    ?_ ?_ ?_ ?_).symm
  · -- membership: `g^x ∉ {0, 1}` for `1 ≤ x ≤ q − 2`
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · exact Units.ne_zero _
    · intro h1
      have hunit : gu ^ x = 1 := Units.ext (by simpa using h1)
      have hdvd := orderOf_dvd_of_pow_eq_one hunit
      rw [hgord] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  · -- injectivity
    intro x hx y hy hxy
    rw [Finset.coe_Icc, Set.mem_Icc] at hx hy
    have hu : gu ^ x = gu ^ y := Units.ext (by simpa using hxy)
    have hmod := pow_eq_pow_iff_modEq.mp hu
    rw [hgord] at hmod
    have hxlt : x < q - 1 := by omega
    have hylt : y < q - 1 := by omega
    have := hmod
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at this
    exact this
  · -- surjectivity onto `univ \ {0, 1}`
    intro u hu
    rw [Finset.coe_sdiff, Set.mem_sdiff] at hu
    obtain ⟨-, hu01⟩ := hu
    simp only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu01
    obtain ⟨hu0, hu1⟩ := hu01
    have huu : IsUnit u := (isUnit_iff_ne_zero (a := u)).mpr hu0
    obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.mpr (hg huu.unit)
    have hj' : gu ^ j = huu.unit := hj
    have hred : gu ^ (j % (q - 1)) = gu ^ j := by
      conv_rhs => rw [← Nat.div_add_mod j (q - 1)]
      rw [pow_add, pow_mul, ← hgord, pow_orderOf_eq_one, one_pow,
        one_mul]
    have hjlt : j % (q - 1) < q - 1 := Nat.mod_lt _ (by omega)
    have hjne : j % (q - 1) ≠ 0 := by
      intro h0
      apply hu1
      have : gu ^ j = 1 := by
        rw [← hred, h0, pow_zero]
      rw [hj'] at this
      have := congrArg (fun w : (ZMod q)ˣ => (w : ZMod q)) this
      simpa [huu.unit_spec] using this
    refine ⟨j % (q - 1), ?_, ?_⟩
    · rw [Finset.coe_Icc, Set.mem_Icc]
      omega
    · show ((gu ^ (j % (q - 1)) : (ZMod q)ˣ) : ZMod q) = u
      rw [hred, hj']
      exact huu.unit_spec
  · -- the terms match
    intro x hx
    show (χ ↑gu) ^ (a * x + b * f x)
        = (χ ^ a) ((gu ^ x : (ZMod q)ˣ) : ZMod q)
          * (χ ^ b) (1 - ((gu ^ x : (ZMod q)ˣ) : ZMod q))
    rw [Finset.mem_Icc] at hx
    have hval : ((gu ^ x : (ZMod q)ˣ) : ZMod q)
        = ((gu : ZMod q)) ^ x := Units.val_pow_eq_pow_val _ _
    have hterm1 : (χ ^ a) ((gu ^ x : (ZMod q)ˣ) : ZMod q)
        = (χ ↑gu) ^ (a * x) := by
      rw [MulChar.pow_apply_coe, hval, map_pow, ← pow_mul, mul_comm]
    have hterm2 : (χ ^ b) (1 - ((gu ^ x : (ZMod q)ˣ) : ZMod q))
        = (χ ↑gu) ^ (b * f x) := by
      rw [hval, ← hf x (Finset.mem_Icc.mpr hx),
        show ((gu : ZMod q)) ^ f x = ((gu ^ f x : (ZMod q)ˣ) : ZMod q)
          from (Units.val_pow_eq_pow_val _ _).symm,
        MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow,
        ← pow_mul, mul_comm]
    rw [hterm1, hterm2, ← pow_add]

/-! ### Step 2(e): the replacement `t` is the unit-group exponent -/

/-- **Proposition (4.1), exponent form**: `s ∣ e(t') ⟺` the
exponent of `(ℤ/sℤ)ˣ` divides `t'`. -/
theorem dvd_e_iff_exponent_dvd {s t' : ℕ} (hs : 0 < s)
    (ht' : 0 < t') :
    s ∣ e t' ↔ Monoid.exponent (ZMod s)ˣ ∣ t' := by
  rw [← proposition_4_1 hs ht']
  exact ⟨fun h => Monoid.exponent_dvd.mpr
      fun g => orderOf_dvd_iff_pow_eq_one.mpr (h g),
    fun h g => orderOf_dvd_iff_pow_eq_one.mp
      (Monoid.exponent_dvd.mp h g)⟩

/-- The unit-group exponent is positive. -/
theorem exponent_units_pos {s : ℕ} (hs : 0 < s) :
    0 < Monoid.exponent (ZMod s)ˣ := by
  haveI : NeZero s := ⟨hs.ne'⟩
  exact Monoid.exponent_pos_of_exists (Fintype.card (ZMod s)ˣ)
    Fintype.card_pos fun g => pow_card_eq_one

/-- **The (12.1)(e)-replacement**: the least `t'` with
`s ∣ e(t')` is the exponent `E` of `(ℤ/sℤ)ˣ` — `s ∣ e(E)`, `E`
divides the old `t`, and `E` divides every admissible `t'`. -/
theorem dvd_e_exponent_least {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hdvd : s ∣ e t) :
    s ∣ e (Monoid.exponent (ZMod s)ˣ)
      ∧ Monoid.exponent (ZMod s)ˣ ∣ t
      ∧ ∀ t' : ℕ, 0 < t' → s ∣ e t'
          → Monoid.exponent (ZMod s)ˣ ∣ t' :=
  ⟨(dvd_e_iff_exponent_dvd hs (exponent_units_pos hs)).mpr dvd_rfl,
    (dvd_e_iff_exponent_dvd hs ht).mp hdvd,
    fun _t' ht' h => (dvd_e_iff_exponent_dvd hs ht').mp h⟩

/-! ### Step 3(h1): the table decomposition `α(n) = u·θ + α(v)` -/

/-- **The exponent decomposition of (12.1)(h1)**, coefficient-wise:
with `n = u·p^k + v` (`u = n/p^k`, `v = n%p^k`), the
`α`-coefficients split exactly: `[nx/p^k] = u·x + [vx/p^k]`. -/
theorem alphac_decomp {n p k x : ℕ} (hpk : 0 < p ^ k) :
    αc n p k x = n / p ^ k * x + αc (n % p ^ k) p k x := by
  rw [αc, αc]
  conv_lhs => rw [← Nat.div_add_mod n (p ^ k)]
  rw [show (p ^ k * (n / p ^ k) + n % p ^ k) * x
      = p ^ k * (n / p ^ k * x) + n % p ^ k * x from by ring]
  rw [Nat.mul_add_div hpk]

/-- **The (12.1)(h1) table identity**, generically: for any family
`F` over any commutative monoid,
`∏ F(x)^(α(n)ₓ) = (∏ F(x)^x)^(n/p^k) · ∏ F(x)^(α(n%p^k)ₓ)` —
i.e. `j^(α(n)) = (j^θ)^u · j^(α(v)) = j₀^u · j_v`: the tabulated
`θ`- and `α(v)`-powers of Step 1 assemble the test quantities of
Theorems (8.5)/(9.10)/(9.19). -/
theorem prod_pow_alphac_decomp {R : Type _} [CommMonoid R]
    {S : Finset ℕ} (F : ℕ → R) (n p k : ℕ) (hpk : 0 < p ^ k) :
    ∏ x ∈ S, F x ^ αc n p k x
      = (∏ x ∈ S, F x ^ x) ^ (n / p ^ k)
        * ∏ x ∈ S, F x ^ αc (n % p ^ k) p k x := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [alphac_decomp hpk, pow_add]
  congr 1
  rw [mul_comm (n / p ^ k) x, pow_mul]

/-! ### Step 5: the final trial divisions consume (2.5) -/

/-- **The (l3)-verdict**: a proper nontrivial divisor refutes
primality. -/
theorem not_prime_of_dvd_lt {n d : ℕ} (hd : d ∣ n) (h1 : 1 < d)
    (hlt : d < n) : ¬ n.Prime := fun hp => by
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- **Loop termination**: by (2.3), `n^t mod s = 1`, so (l2) fires
by `i = t` at the latest. -/
theorem pow_t_mod_eq_one {n s t : ℕ} (hs : 1 < s)
    (hco : n.Coprime s) (h23 : ∀ u : (ZMod s)ˣ, u ^ t = 1) :
    n ^ t % s = 1 := by
  haveI : NeZero s := ⟨by omega⟩
  have hu : IsUnit ((n : ℕ) : ZMod s) :=
    (ZMod.isUnit_iff_coprime n s).mpr hco
  have h1 : ((n ^ t : ℕ) : ZMod s) = ((1 : ℕ) : ZMod s) := by
    push_cast
    have hpow := h23 hu.unit
    have hval := congrArg (fun u : (ZMod s)ˣ => (u : ZMod s)) hpow
    simpa [hu.unit_spec] using hval
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt hs] at hmod

/-- **The (l2)-verdict — the capstone `step5_prime`**: if `n < s²`
(condition (2.4)), every divisor of `n` is `≡ n^j (mod s)` (the
(2.5)-conclusion of Theorem (6.3)), the sweep found no divisor
among `n^j mod s` for `1 ≤ j < i` (the sweep stops at `r = 1`, step (l2)), and `n^i mod s = 1`, then `n`
is prime.  This closes the abstract pipeline end-to-end. -/
theorem step5_prime {n s t : ℕ} (hn : 1 < n) (hs2 : n < s ^ 2)
    (h25 : ∀ r, r ∣ n → ∃ j < t, r ≡ n ^ j [MOD s])
    {i : ℕ} (hi1 : 1 ≤ i) (hri : n ^ i % s = 1)
    (hloop : ∀ j, 1 ≤ j → j < i
      → ¬ (n ^ j % s ∣ n ∧ n ^ j % s < n)) :
    n.Prime := by
  have hs1 : 1 < s := by
    by_contra hc
    push Not at hc
    interval_cases s <;> simp_all
  by_contra hnp
  -- the least prime factor is `≤ √n < s`
  have hr := Nat.minFac_prime (by omega : n ≠ 1)
  have hrdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hrsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hrlt_s : n.minFac < s := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  have hrlt_n : n.minFac < n := by
    have h2 := hr.two_le
    have hsq : n.minFac ^ 2 = n.minFac * n.minFac := sq n.minFac
    nlinarith
  obtain ⟨j, hjt, hjcong⟩ := h25 n.minFac hrdvd
  -- reduce along the `n^i ≡ 1` cycle
  have hni : n ^ i ≡ 1 [MOD s] := by
    unfold Nat.ModEq
    rw [hri, Nat.mod_eq_of_lt hs1]
  have hcyc : n.minFac ≡ n ^ (j % i) [MOD s] := by
    refine hjcong.trans ?_
    have hj' : j = i * (j / i) + j % i := (Nat.div_add_mod j i).symm
    calc n ^ j = (n ^ i) ^ (j / i) * n ^ (j % i) := by
          conv_lhs => rw [hj']
          rw [pow_add, pow_mul]
      _ ≡ 1 ^ (j / i) * n ^ (j % i) [MOD s] :=
          ((hni.pow _).mul_right _)
      _ = n ^ (j % i) := by rw [one_pow, one_mul]
  have hreq : n.minFac = n ^ (j % i) % s := by
    have hm := hcyc
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt hrlt_s] at hm
  rcases Nat.eq_zero_or_pos (j % i) with h0 | h1
  · rw [h0, pow_zero, Nat.mod_eq_of_lt hs1] at hreq
    have := hr.one_lt
    omega
  · have hjmi : j % i < i := Nat.mod_lt _ (by omega)
    exact hloop (j % i) h1 hjmi ⟨hreq ▸ hrdvd, hreq ▸ hrlt_n⟩

end CL

end Azurite
