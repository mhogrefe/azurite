/-
  **Cohen–Lenstra (11.5)/(11.6): the `p = 2` procedure for
  condition (6.4), and its justification.**

  For even `t`: either prove that `p = 2` satisfies (6.4) or prove
  `n` composite.

  For `n ≡ 1 (mod 4)`: find `a` with Jacobi symbol `(a/n) = −1`
  and test `a^((n−1)/2) ≡ −1 (mod n)`.  A pass gives (6.4) by
  Proposition (7.24); a failure proves `n` composite by (1.2) —
  the Euler-criterion verdict `euler_verdict_of_prime` proved
  here: for *prime* `n`, `(a/n) = −1` forces
  `a^((n−1)/2) ≡ −1`.  (If no `a` is found, test whether `n` is a
  square — `not_prime_of_eq_pow` at `k = 2`.)

  For `n ≡ 3 (mod 4)`: find `u` with `((u²+4)/n) = −1` and test
  `ξ^(n+1) = −1` in `(ℤ/n)[T]/(T² − uT − 1)`.  A pass gives (6.4)
  by Proposition (10.8); a failure proves `n` composite by the
  remark preceding (10.8) — the finite-field verdict
  `xi_pow_eq_neg_one_of_prime` proved here: for *prime* `n`, the
  nonsquare discriminant `u² + 4` makes `T² − uT − 1` irreducible,
  `F = 𝔽_(n²)` a field, and the Frobenius sends `ξ` to the other
  root `u − ξ = −ξ^(−1)` (it cannot fix `ξ`: the polynomial
  `X^n − X` of degree `n` would otherwise have the `n + 1`
  distinct roots `𝔽_n ∪ {ξ}`), whence
  `ξ^(n+1) = ξ(u − ξ) = −1`.  Both verdicts are stated
  polynomial-level, matching Proposition (10.8).

  Alternatives (7.25)/(7.26) noted by the paper; our inventory
  covers `n ≡ 3 (mod 8)` by (7.25) already, and (10.8) covers all
  of `n ≡ 3 (mod 4)`.

  **Remarks (11.6)** (prose).  (a) The (11.4)(a)-remarks apply to
  the search for `a`; for `n ≡ 3 (mod 4)` a `u` with
  `((u²+4)/n) = −1` always *exists* (via the least nonresidue
  mod a prime `r ∥ n` of odd multiplicity and a CRT choice), and
  under GRH the least one is `O((log n)²)` for `n` without small
  prime factors (Odlyzko).  Existence and size are generator-side
  — the checker verifies the found `u` (a computable Jacobi
  symbol is a §12–13 rail item).  (b) The searches for `q`, `a`,
  `u` are the only obstacles to a proven
  `(log n)^(c·log log log n)` running time; under GRH one takes
  `𝔪 = nℤ[ζ_{p^k}]`, while the Pomerance–Odlyzko average-case
  result wants Method (10.3) with Proposition (10.7) — whose
  `k ≥ 2` proviso is harmless (cf. (7.28)).
-/
import Azurite.CohenLenstra.Proposition_10_7
import Azurite.CohenLenstra.Procedure_11_2
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.Algebra

namespace Azurite

namespace CL

open Polynomial

/-- **The (11.5) verdict for `n ≡ 1 (mod 4)`** (the paper's appeal
to (1.2)): for *prime* `n` and Jacobi symbol `(a/n) = −1`, Euler's
criterion forces `a^((n−1)/2) ≡ −1 (mod n)`.  Contrapositive: a
witnessed failure proves `n` composite. -/
theorem euler_verdict_of_prime {n : ℕ} (hn : n.Prime)
    (hodd : n % 2 = 1) {a : ℤ} (hJ : jacobiSym a n = -1) :
    ((a : ZMod n)) ^ ((n - 1) / 2) = (-1 : ZMod n) := by
  have : Fact n.Prime := ⟨hn⟩
  have hleg : legendreSym n a = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact hJ
  have hpow := legendreSym.eq_pow n a
  rw [hleg] at hpow
  have he : (n - 1) / 2 = n / 2 := by omega
  rw [he, ← hpow]
  push_cast
  ring

/-- **The (11.5) verdict for `n ≡ 3 (mod 4)`** (the remark
preceding (10.8)): for *prime* `n` and `((u²+4)/n) = −1`, the ring
`F = (ℤ/n)[T]/(T² − uT − 1)` is the field `𝔽_(n²)` and
`ξ^(n+1) = −1` — stated polynomial-level as
`(X² − uX − 1) ∣ X^(n+1) + 1`, matching Proposition (10.8).
Contrapositive: a witnessed failure proves `n` composite. -/
theorem xi_pow_eq_neg_one_of_prime {n : ℕ} (hn : n.Prime)
    (hn3 : n % 4 = 3) {u : ℤ} (hJ : jacobiSym (u ^ 2 + 4) n = -1) :
    (X ^ 2 - C ((u : ZMod n)) * X - 1 : Polynomial (ZMod n))
      ∣ X ^ (n + 1) + 1 := by
  have : Fact n.Prime := ⟨hn⟩
  have hn1 : 1 < n := hn.one_lt
  have : Fact (1 < n) := ⟨hn1⟩
  have hn3le : 3 ≤ n := by omega
  set u' : ZMod n := ((u : ℤ) : ZMod n) with hu'
  set f : Polynomial (ZMod n) := X ^ 2 - C u' * X - 1 with hf
  -- the discriminant is a nonsquare
  have hns : ¬ IsSquare (u' ^ 2 + 4 : ZMod n) := by
    have hleg : legendreSym n (u ^ 2 + 4) = -1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact hJ
    have hnsq := (legendreSym.eq_neg_one_iff (p := n)).mp hleg
    have hcast : (((u ^ 2 + 4 : ℤ)) : ZMod n) = u' ^ 2 + 4 := by
      push_cast
      rfl
    rwa [hcast] at hnsq
  -- so `f` has no roots
  have hnoroot : ∀ c : ZMod n, ¬ (c ^ 2 - u' * c - 1 = 0) := by
    intro c hc
    apply hns
    refine ⟨2 * c - u', ?_⟩
    linear_combination (-4 : ZMod n) * hc
  -- `f` is monic of degree exactly 2
  have hfrw : f = X ^ 2 - (C u' * X + 1) := by
    rw [hf]
    ring
  have htail : (C u' * X + (1 : Polynomial (ZMod n))).natDegree ≤ 1 := by
    rw [show (1 : Polynomial (ZMod n)) = C 1 from C_1.symm]
    exact natDegree_linear_le
  have hfmonic : f.Monic := by
    rw [hfrw]
    have htail' : degree (C u' * X + (1 : Polynomial (ZMod n)))
        ≤ (1 : WithBot ℕ) := by
      rw [show (1 : Polynomial (ZMod n)) = C 1 from C_1.symm]
      exact degree_linear_le
    have hlt : (1 : WithBot ℕ) < ((2 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by norm_num : (1 : ℕ) < 2)
    exact monic_X_pow_sub (lt_of_le_of_lt htail' hlt)
  have hfdeg : f.natDegree = 2 := by
    rw [hfrw, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    omega
  -- irreducibility
  have hroots0 : f.roots = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro c hc
    rw [Polynomial.mem_roots hfmonic.ne_zero] at hc
    apply hnoroot c
    have he := hc
    rw [Polynomial.IsRoot, hf] at he
    simpa using he
  have hirr : Irreducible f :=
    (hfmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr hroots0
  have : Fact (Irreducible f) := ⟨hirr⟩
  have : CharP (AdjoinRoot f) n :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod n) (AdjoinRoot f)).injective n
  set ξ : AdjoinRoot f := AdjoinRoot.root f with hξ
  set uK : AdjoinRoot f := algebraMap (ZMod n) (AdjoinRoot f) u'
    with huK
  -- the defining relation
  have hzero : ξ ^ 2 - uK * ξ - 1 = 0 := by
    have h0 : aeval ξ (X ^ 2 - C u' * X - 1 : Polynomial (ZMod n))
        = 0 := by
      show aeval ξ f = 0
      rw [hξ, AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_self
    simpa [huK] using h0
  -- Frobenius fixes the base field
  have hfrobfix : ∀ c : ZMod n,
      (algebraMap (ZMod n) (AdjoinRoot f) c) ^ n
        = algebraMap (ZMod n) (AdjoinRoot f) c := by
    intro c
    rw [← map_pow, ZMod.pow_card]
  -- `ξ^n` is a root of `f`
  have hξn : (ξ ^ n) ^ 2 - uK * ξ ^ n - 1 = 0 := by
    have hφ := congrArg (frobenius (AdjoinRoot f) n) hzero
    rw [map_zero, map_sub, map_sub, map_mul, map_one] at hφ
    simp only [frobenius_def] at hφ
    rw [← pow_mul, mul_comm 2 n, pow_mul] at hφ
    have hUK : uK ^ n = uK := by
      rw [huK]
      exact hfrobfix u'
    rwa [hUK] at hφ
  -- so `ξ^n` is `ξ` or the other root
  have hswap : ξ ^ n = ξ ∨ ξ ^ n = uK - ξ := by
    have hfact : (ξ ^ n - ξ) * (ξ ^ n - (uK - ξ)) = 0 := by
      linear_combination hξn - hzero
    rcases mul_eq_zero.mp hfact with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  -- Frobenius cannot fix `ξ`: `X^n − X` would have `n+1` roots
  have hinj : Function.Injective (algebraMap (ZMod n) (AdjoinRoot f)) :=
    (algebraMap (ZMod n) (AdjoinRoot f)).injective
  have hnotfix : ξ ^ n ≠ ξ := by
    intro hfix
    have hgmonic : (X ^ n - X : Polynomial (AdjoinRoot f)).Monic := by
      refine monic_X_pow_sub ?_
      calc degree (X : Polynomial (AdjoinRoot f)) = 1 := degree_X
        _ < ((n : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : (1 : ℕ) < n)
    have hgdeg : (X ^ n - X : Polynomial (AdjoinRoot f)).natDegree
        = n := by
      rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
      rw [natDegree_X, natDegree_X_pow]
      omega
    have hξnotmem : ξ ∉ (Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f)) := by
      intro hmem
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
      apply hnoroot c
      have h1 : algebraMap (ZMod n) (AdjoinRoot f)
          (c ^ 2 - u' * c - 1) = 0 := by
        rw [map_sub, map_sub, map_pow, map_mul, map_one, hc, ← huK]
        linear_combination hzero
      exact hinj (h1.trans (map_zero _).symm)
    have hcardS : (insert ξ ((Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f)))).card = n + 1 := by
      rw [Finset.card_insert_of_notMem hξnotmem,
        Finset.card_image_of_injective _ hinj, Finset.card_univ,
        ZMod.card]
    have hsub : (insert ξ ((Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f))))
        ⊆ (X ^ n - X : Polynomial (AdjoinRoot f)).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset,
        Polynomial.mem_roots hgmonic.ne_zero]
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, hfix, sub_self]
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
        rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, hfrobfix c, sub_self]
    have hle := Finset.card_le_card hsub
    have hle2 : (X ^ n - X : Polynomial (AdjoinRoot f)).roots.toFinset.card
        ≤ Multiset.card (X ^ n - X : Polynomial (AdjoinRoot f)).roots :=
      Multiset.toFinset_card_le _
    have hle3 := Polynomial.card_roots'
      (X ^ n - X : Polynomial (AdjoinRoot f))
    omega
  -- conclude `ξ^(n+1) = −1` and translate to divisibility
  have hxin : ξ ^ n = uK - ξ := hswap.resolve_left hnotfix
  have hfinal : ξ ^ (n + 1) + 1 = 0 := by
    rw [pow_succ, hxin]
    linear_combination -hzero
  refine AdjoinRoot.mk_eq_zero.mp ?_
  rw [map_add, map_one, map_pow, AdjoinRoot.mk_X]
  exact hfinal

end CL

end Azurite
