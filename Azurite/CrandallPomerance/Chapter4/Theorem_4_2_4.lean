/-
  Crandall–Pomerance, Theorem 4.2.4 (left as an exercise there): for an
  odd prime `p`, the number `N` of pairs `a, b ∈ {0, …, p−1}` with
  `(Δ/p) = −1` and `r_f(p) = p + 1` is

    `N = (1/2)·(p − 1)·φ(p + 1)`   (stated here as `2N = (p−1)·φ(p+1)`).

  Proof (ours).  Work in a field `K` with `p²` elements.  For a pair
  with `Δ` a nonsquare, `f` is irreducible with roots `α, β = α^p ∈ K`,
  and `p ∣ U_r ↔ α^r = β^r ↔ γ^r = 1` where `γ = α^{1−p} ∈ Kˣ`; hence
  `r_f(p) = orderOf γ`.  Note `γ = u^{p² − p}` for `u = α` in `Kˣ`
  (as `u^{p²−1} = 1`).  Writing `Kˣ = ⟨g⟩`, cyclic of order
  `n = (p−1)(p+1)`, and `u = g^i`:

    `orderOf (g^{i(p²−p)}) = n / gcd(n, i·p·(p−1)) = (p+1)/gcd(p+1, i)`,

  so the rank is `p + 1` exactly when `gcd(p + 1, i) = 1`; there are
  `(p−1)·φ(p+1)` such `i < n`.  Such `u` automatically lie outside the
  prime field (`γ ≠ 1`), their trace and norm descend to `ZMod p` (the
  fixed points of Frobenius are the prime field — a root count on
  `X^p − X`), the discriminant `(α−β)²` is a nonsquare by Euler
  (`(α−β)^{p−1} = −1`), and `u ↦ (trace, norm)` is exactly 2-to-1 onto
  the counted pairs (the two preimages being the two roots `α, α^p`).
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_2
import Azurite.GathenGerhard.Chapter14.Theorem_14_2
import Mathlib.Data.Nat.Totient

namespace Azurite

namespace CP

open Polynomial

variable {p : ℕ} [Fact p.Prime]

section FieldK

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod p) K]

omit [Fintype K] in
/-- **Frobenius fixed points are the prime field**: any `x` with
`x^p = x` lies in the image of `ZMod p` — `X^p − X` has at most `p`
roots, and the prime field supplies all of them. -/
theorem mem_range_algebraMap_of_pow_card {x : K} (hx : x ^ p = x) :
    ∃ c : ZMod p, algebraMap (ZMod p) K c = x := by
  by_contra hno
  push Not at hno
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set gp : K[X] := X ^ p - X with hgp
  have hgp0 : gp ≠ 0 := by
    intro h0
    have hc : gp.coeff p = 1 := by
      rw [hgp, coeff_sub, coeff_X_pow, if_pos rfl, coeff_X]
      rw [if_neg (by omega : ¬(1 : ℕ) = p)]
      ring
    rw [h0, coeff_zero] at hc
    exact one_ne_zero hc.symm
  have hgpdeg : gp.natDegree ≤ p := by
    rw [hgp]
    refine le_trans (natDegree_sub_le _ _) ?_
    simp only [natDegree_X_pow, natDegree_X]
    omega
  have hmem : ∀ c : ZMod p, algebraMap (ZMod p) K c ∈ gp.roots := by
    intro c
    rw [mem_roots hgp0]
    simp only [hgp, IsRoot, eval_sub, eval_pow, eval_X]
    rw [← map_pow, ZMod.pow_card, sub_self]
  have hxmem : x ∈ gp.roots := by
    rw [mem_roots hgp0]
    simp only [hgp, IsRoot, eval_sub, eval_pow, eval_X]
    rw [hx, sub_self]
  set S : Finset K :=
    insert x ((Finset.univ : Finset (ZMod p)).image
      (algebraMap (ZMod p) K)) with hS
  have hScard : S.card = p + 1 := by
    rw [hS, Finset.card_insert_of_notMem (by
      rw [Finset.mem_image]
      rintro ⟨c, -, hc⟩
      exact hno c hc),
      Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective,
      Finset.card_univ, ZMod.card]
  have hSsub : S ⊆ gp.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset]
    rw [hS, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxmem
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
      exact hmem c
  have h1 := Finset.card_le_card hSsub
  have h2 := Multiset.toFinset_card_le gp.roots
  have h3 := Polynomial.card_roots' gp
  omega

omit [DecidableEq K] in
/-- **Root existence**: every monic irreducible quadratic over `ZMod p`
has a root in a field of order `p²` (via GG's divisibility criterion
`f ∣ X^(q²) − X` and the splitting of `X^(card K) − X`). -/
theorem exists_root_of_irreducible_quadratic
    (hcard : Fintype.card K = p ^ 2) {g : (ZMod p)[X]}
    (hirr : Irreducible g) (hdeg : g.natDegree = 2) :
    ∃ α : K, aeval α g = 0 := by
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  -- `g ∣ X^(p²) − X` over `ZMod p`
  have hdvd : g ∣ X ^ Fintype.card (ZMod p) ^ 2 - X :=
    Azurite.GG.dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hirr
      (by rw [hdeg])
  rw [ZMod.card] at hdvd
  -- map to `K`, where `X^(p²) − X = X^(card K) − X` splits completely
  have hdvdK : g.map (algebraMap (ZMod p) K)
      ∣ X ^ Fintype.card K - X := by
    have := Polynomial.map_dvd (algebraMap (ZMod p) K) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      ← hcard] at this
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hdegX : (X ^ Fintype.card K - X : K[X]).natDegree
      = Fintype.card K := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [natDegree_X_pow, natDegree_X]
    omega
  have hX0 : (X ^ Fintype.card K - X : K[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdegX
    omega
  have hsplits : Splits (X ^ Fintype.card K - X : K[X]) := by
    rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      hdegX]
    rfl
  have hsplitsg : Splits (g.map (algebraMap (ZMod p) K)) :=
    hsplits.of_dvd hX0 hdvdK
  have hdegg : (g.map (algebraMap (ZMod p) K)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective
      (algebraMap (ZMod p) K).injective, hdeg]
    norm_num
  have hroots := hsplitsg.roots_ne_zero hdegg
  obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hroots
  refine ⟨α, ?_⟩
  have := (Polynomial.mem_roots (by
    intro h0
    rw [h0, natDegree_zero] at hdegg
    exact hdegg rfl)).mp hα
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  exact this

/-! ### The rank of appearance as a multiplicative order -/

omit [Fact (Nat.Prime p)] [DecidableEq K] [Algebra (ZMod p) K] in
/-- Every element of a field of order `p²` satisfies `x^(p²) = x`. -/
theorem pow_card_sq (hcard : Fintype.card K = p ^ 2) (x : K) :
    x ^ p ^ 2 = x := by
  have := FiniteField.pow_card x
  rwa [hcard] at this

omit [DecidableEq K] in
/-- Traces `x + x^p` are Frobenius-stable. -/
theorem trace_pow_card (hcard : Fintype.card K = p ^ 2) {x : K} :
    (x + x ^ p) ^ p = x + x ^ p := by
  haveI : CharP K p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  rw [add_pow_char, ← pow_mul, ← pow_two, pow_card_sq hcard]
  ring

omit [Fact (Nat.Prime p)] [DecidableEq K] [Algebra (ZMod p) K] in
/-- Norms `x · x^p` are Frobenius-stable. -/
theorem norm_pow_card (hcard : Fintype.card K = p ^ 2) {x : K} :
    (x * x ^ p) ^ p = x * x ^ p := by
  rw [mul_pow, ← pow_mul, ← pow_two, pow_card_sq hcard]
  ring

omit [DecidableEq K] in
/-- **The rank of appearance is a multiplicative order**: if the values
of `a, b` match the trace and norm of a unit `u` with `(u:K)^p ≠ u`,
then `r_f(p) = orderOf (u^(p−1))⁻¹`. -/
theorem rankApp_eq_orderOf {u : Kˣ} (hu : (u : K) ^ p ≠ (u : K))
    {a b : ℤ} (ha : ((a : ℤ) : K) = (u : K) + (u : K) ^ p)
    (hb : ((b : ℤ) : K) = (u : K) * (u : K) ^ p) :
    rankApp a b p = orderOf ((u ^ (p - 1))⁻¹) := by
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set α : K := (u : K) with hα
  set β : K := (u : K) ^ p with hβ
  have hsum : α + β = ((a : ℤ) : K) := ha.symm
  have hprod : α * β = ((b : ℤ) : K) := hb.symm
  have hαβ : α - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  set γ : Kˣ := (u ^ (p - 1))⁻¹ with hγ
  -- the value of `γ` is `α/β`
  have hγval : (γ : K) * β = α := by
    rw [hγ, hβ, hα]
    push_cast
    rw [show ((u : K)) ^ p = (u : K) ^ (p - 1) * (u : K) by
      rw [← pow_succ]
      congr 1
      omega]
    field_simp
  -- the divisibility criterion
  have hcrit : ∀ r : ℕ, ((p : ℕ) : ℤ) ∣ lucasU a b r ↔ γ ^ r = 1 := by
    intro r
    have hspec := lucasU_spec hsum hprod r
    constructor
    · intro hd
      have h0 : ((lucasU a b r : ℤ) : K) = 0 := by
        have h1 : ((lucasU a b r : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
        rw [show ((lucasU a b r : ℤ) : K)
            = algebraMap (ZMod p) K ((lucasU a b r : ℤ) : ZMod p) from
            (map_intCast _ _).symm, h1, map_zero]
      rw [h0, zero_mul] at hspec
      have hαr : α ^ r = β ^ r := by
        have := hspec.symm
        rwa [sub_eq_zero] at this
      have hβr0 : β ^ r ≠ 0 := pow_ne_zero _ (by
        rw [hβ]
        exact pow_ne_zero _ (Units.ne_zero u))
      have hg1 : ((γ : K)) ^ r = 1 := by
        have hmul : ((γ : K)) ^ r * β ^ r = α ^ r := by
          rw [← mul_pow, hγval]
        rw [hαr] at hmul
        exact mul_right_cancel₀ hβr0 (by rw [hmul, one_mul])
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hg1, Units.val_one])
    · intro hg
      have hγ1 : ((γ : K)) ^ r = 1 := by
        rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]
      have hαr : α ^ r = β ^ r := by
        rw [← hγval, mul_pow, hγ1, one_mul]
      rw [show α ^ r - β ^ r = 0 by rw [hαr]; ring] at hspec
      have hU0 : ((lucasU a b r : ℤ) : K) = 0 := by
        rcases mul_eq_zero.mp hspec with h | h
        · exact h
        · exact absurd h hαβ
      have : ((lucasU a b r : ℤ) : ZMod p) = 0 := by
        rw [show ((lucasU a b r : ℤ) : K)
            = algebraMap (ZMod p) K ((lucasU a b r : ℤ) : ZMod p) from
            (map_intCast _ _).symm] at hU0
        exact (algebraMap (ZMod p) K).injective (by rw [hU0, map_zero])
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  -- both inequalities
  have hopos : 0 < orderOf γ := orderOf_pos γ
  have hex : ∃ r : ℕ, 0 < r ∧ ((p : ℕ) : ℤ) ∣ lucasU a b r :=
    ⟨orderOf γ, hopos, (hcrit _).mpr (pow_orderOf_eq_one γ)⟩
  obtain ⟨hrpos, hrdvd⟩ := rankApp_mem hex
  have hle1 : rankApp a b p ≤ orderOf γ :=
    rankApp_min hopos ((hcrit _).mpr (pow_orderOf_eq_one γ))
  have hle2 : orderOf γ ≤ rankApp a b p :=
    Nat.le_of_dvd hrpos (orderOf_dvd_of_pow_eq_one ((hcrit _).mp hrdvd))
  omega

omit [DecidableEq K] in
/-- **The discriminant is a nonsquare**: for a unit `u` with
`(u:K)^p ≠ u` and `(a, b)` matching its trace and norm,
`(Δ/p) = −1` — Euler's criterion via `(α−β)^(p−1) = −1`. -/
theorem legendreSym_disc_eq_neg_one (hcard : Fintype.card K = p ^ 2)
    (hp2 : p ≠ 2) {u : Kˣ} (hu : (u : K) ^ p ≠ (u : K))
    {a b : ℤ} (ha : ((a : ℤ) : K) = (u : K) + (u : K) ^ p)
    (hb : ((b : ℤ) : K) = (u : K) * (u : K) ^ p) :
    legendreSym p (a ^ 2 - 4 * b) = -1 := by
  haveI : CharP K p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set α : K := (u : K) with hα
  set β : K := (u : K) ^ p with hβ
  have hsum : α + β = ((a : ℤ) : K) := ha.symm
  have hprod : α * β = ((b : ℤ) : K) := hb.symm
  have hαβ : α - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hdisc := sub_sq_eq_disc hsum hprod
  -- `(α − β)^(p−1) = −1`
  have hfr : (α - β) ^ p = -(α - β) := by
    rw [sub_pow_char, hβ, ← pow_mul, ← pow_two, hα, pow_card_sq hcard]
    ring
  have hpow : (α - β) ^ (p - 1) = -1 := by
    have h1 : (α - β) ^ (p - 1) * (α - β) = -1 * (α - β) := by
      rw [← pow_succ, show p - 1 + 1 = p by omega, hfr]
      ring
    exact mul_right_cancel₀ hαβ h1
  -- Euler in `K`, then descend to `ZMod p`
  have hK : ((a ^ 2 - 4 * b : ℤ) : K) ^ ((p - 1) / 2) = -1 := by
    have hodd : p % 2 = 1 :=
      Nat.odd_iff.mp ((Fact.out (p := p.Prime)).odd_of_ne_two hp2)
    rw [← hdisc, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
    exact hpow
  have hZ : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    apply (algebraMap (ZMod p) K).injective
    rw [map_pow, map_intCast, map_neg, map_one]
    exact hK
  -- convert to the Legendre symbol
  have hΔ0 : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : (p - 1) / 2 ≠ 0)] at hZ
    have h1 : ((1 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hZ
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hEuler := legendreSym.eq_pow p (a ^ 2 - 4 * b)
  rcases legendreSym.eq_one_or_neg_one (p := p) hΔ0 with h1 | h1
  · exfalso
    have hodd : p % 2 = 1 :=
      Nat.odd_iff.mp ((Fact.out (p := p.Prime)).odd_of_ne_two hp2)
    rw [h1, show p / 2 = (p - 1) / 2 by omega, hZ] at hEuler
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast at hEuler ⊢
      linear_combination hEuler
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · exact h1

/-! ### Counting units by the order of their `(p−1)`-th power -/

/-- Coprimes to `k` in `range (m·k)`: there are `m·φ(k)` of them. -/
theorem card_range_mul_filter_coprime {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ((Finset.range (m * k)).filter (fun i => Nat.Coprime k i)).card
      = m * k.totient := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.range ((m + 1) * k)
        = Finset.range (m * k) ∪ Finset.Ico (m * k) (m * k + k) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
          (by omega : m * k ≤ m * k + k)]
      congr 1
      ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (by
      refine Finset.disjoint_filter_filter ?_
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 (m * k) (m * k + k)),
      ih, Nat.filter_coprime_Ico_eq_totient k (m * k)]
    ring

omit [Algebra (ZMod p) K] in
/-- **The unit count**: in a field of order `p²`, the units `u` with
`orderOf (u^(p−1)) = p + 1` number exactly `(p−1)·φ(p+1)`. -/
theorem card_units_orderOf_pow_sub_one (hcard : Fintype.card K = p ^ 2) :
    ((Finset.univ : Finset Kˣ).filter
      (fun u => orderOf (u ^ (p - 1)) = p + 1)).card
      = (p - 1) * Nat.totient (p + 1) := by
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hn : Fintype.card Kˣ = (p + 1) * (p - 1) := by
    rw [Fintype.card_units, hcard]
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p := by omega
    zify [h1, h2]
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have horder : orderOf g = (p + 1) * (p - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, hn]
  have hnpos : 0 < (p + 1) * (p - 1) :=
    Nat.mul_pos (by omega) (by omega)
  -- pointwise: the condition on `g^i` is coprimality of `i` to `p+1`
  have hpoint : ∀ i : ℕ, orderOf ((g ^ i) ^ (p - 1)) = p + 1
      ↔ Nat.Coprime (p + 1) i := by
    intro i
    rw [← pow_mul, orderOf_pow, horder]
    have hgcd : Nat.gcd ((p + 1) * (p - 1)) (i * (p - 1))
        = Nat.gcd (p + 1) i * (p - 1) := Nat.gcd_mul_right _ _ _
    rw [hgcd, Nat.mul_div_mul_right _ _ (by omega : 0 < p - 1)]
    constructor
    · intro h
      have hd : Nat.gcd (p + 1) i ∣ p + 1 := Nat.gcd_dvd_left _ _
      rcases (Nat.div_eq_self).mp h with h1 | h1
      · omega
      · exact h1
    · intro h
      rw [h, Nat.div_one]
  -- transfer the count along `i ↦ g^i`
  rw [show ((Finset.univ : Finset Kˣ).filter
      (fun u => orderOf (u ^ (p - 1)) = p + 1)).card
      = ((Finset.range ((p + 1) * (p - 1))).filter
        (fun i => Nat.Coprime (p + 1) i)).card from ?_]
  · rw [show (p + 1) * (p - 1) = (p - 1) * (p + 1) by ring]
    exact card_range_mul_filter_coprime (by omega) (p - 1)
  · symm
    refine Finset.card_bij (fun i _ => g ^ i) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, (hpoint i).mpr hi.2⟩
    · intro i hi j hj hij
      rw [Finset.mem_filter, Finset.mem_range] at hi hj
      have := pow_eq_pow_iff_modEq.mp hij
      rw [horder] at this
      rw [Nat.ModEq] at this
      rwa [Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] at this
    · intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
        ((mem_powers_iff_mem_zpowers).mpr (hg u))
      refine ⟨k % ((p + 1) * (p - 1)), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact Nat.mod_lt _ hnpos
        · rw [← hpoint]
          rw [show g ^ (k % ((p + 1) * (p - 1))) = g ^ k from by
            rw [← horder]; exact pow_mod_orderOf g k, hk]
          exact hu.2
      · rw [show g ^ (k % ((p + 1) * (p - 1))) = g ^ k from by
          rw [← horder]; exact pow_mod_orderOf g k, hk]

end FieldK

open scoped Classical in
/-- **Crandall–Pomerance Theorem 4.2.4** (their exercise): for an odd
prime `p`, the number `N` of pairs `a, b ∈ {0, …, p−1}` with
`(Δ/p) = −1` and `r_f(p) = p + 1` satisfies `2N = (p−1)·φ(p+1)`. -/
theorem theorem_4_2_4 (hp2 : p ≠ 2) :
    2 * ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun ab =>
        legendreSym p ((ab.1.val : ℤ) ^ 2 - 4 * (ab.2.val : ℤ)) = -1 ∧
        rankApp (ab.1.val : ℤ) (ab.2.val : ℤ) p = p + 1)).card
      = (p - 1) * Nat.totient (p + 1) := by
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  haveI : NeZero p := ⟨by omega⟩
  -- build a field `K` with `p²` elements
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  set g₀ : (ZMod p)[X] := X ^ 2 - C c with hg₀
  have hg₀deg : g₀.natDegree = 2 := by
    rw [hg₀]
    exact natDegree_X_pow_sub_C
  have hg₀irr : Irreducible g₀ := by
    refine irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hg₀deg]; decide) ?_
    intro γ hγ
    rw [hg₀, IsRoot] at hγ
    simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hγ
    exact hc ⟨γ, by rw [← hγ]; ring⟩
  haveI : Fact (Irreducible g₀) := ⟨hg₀irr⟩
  set K := AdjoinRoot g₀ with hK
  haveI : Module.Finite (ZMod p) K :=
    (AdjoinRoot.powerBasis hg₀irr.ne_zero).finite
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : DecidableEq K := Classical.decEq K
  have hcardK : Fintype.card K = p ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K),
      (AdjoinRoot.powerBasis hg₀irr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, ZMod.card, hg₀deg]
  -- descend traces and norms
  have hdesc : ∀ u : Kˣ, ∃ AB : ZMod p × ZMod p,
      algebraMap (ZMod p) K AB.1 = (u : K) + (u : K) ^ p ∧
      algebraMap (ZMod p) K AB.2 = (u : K) * (u : K) ^ p := by
    intro u
    obtain ⟨A, hA⟩ := mem_range_algebraMap_of_pow_card
      (trace_pow_card hcardK (x := (u : K)))
    obtain ⟨B, hB⟩ := mem_range_algebraMap_of_pow_card
      (norm_pow_card hcardK (x := (u : K)))
    exact ⟨(A, B), hA, hB⟩
  set θ : Kˣ → ZMod p × ZMod p := fun u => (hdesc u).choose with hθ
  have hθ1 : ∀ u : Kˣ,
      algebraMap (ZMod p) K (θ u).1 = (u : K) + (u : K) ^ p :=
    fun u => (hdesc u).choose_spec.1
  have hθ2 : ∀ u : Kˣ,
      algebraMap (ZMod p) K (θ u).2 = (u : K) * (u : K) ^ p :=
    fun u => (hdesc u).choose_spec.2
  -- the `val`-cast bridge into `K`
  have hcast : ∀ A : ZMod p, ((A.val : ℤ) : K) = algebraMap (ZMod p) K A := by
    intro A
    rw [show ((A.val : ℤ) : K) = ((A.val : ℕ) : K) from by push_cast; ring,
      show ((A.val : ℕ) : K) = algebraMap (ZMod p) K ((A.val : ℕ) : ZMod p)
        from (map_natCast _ _).symm,
      ZMod.natCast_rightInverse A]
  set Sα : Finset Kˣ := Finset.univ.filter
    (fun u => orderOf (u ^ (p - 1)) = p + 1) with hSα
  set T : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun ab =>
    legendreSym p ((ab.1.val : ℤ) ^ 2 - 4 * (ab.2.val : ℤ)) = -1 ∧
    rankApp (ab.1.val : ℤ) (ab.2.val : ℤ) p = p + 1) with hT
  -- a unit in `Sα` is not Frobenius-fixed
  have hnofix : ∀ u : Kˣ, u ∈ Sα → (u : K) ^ p ≠ (u : K) := by
    intro u hu hfix
    rw [hSα, Finset.mem_filter] at hu
    have h1 : u ^ (p - 1) = 1 := by
      have : u ^ p = u := Units.ext (by
        rw [Units.val_pow_eq_pow_val]; exact hfix)
      have h2 : u ^ (p - 1) * u = 1 * u := by
        rw [← pow_succ, show p - 1 + 1 = p by omega, this, one_mul]
      exact mul_right_cancel h2
    rw [h1, orderOf_one] at hu
    omega
  -- `θ` maps `Sα` into `T`
  have hmaps : ∀ u ∈ Sα, θ u ∈ T := by
    intro u hu
    have hne := hnofix u hu
    have ha' : (((θ u).1.val : ℤ) : K) = (u : K) + (u : K) ^ p := by
      rw [hcast, hθ1]
    have hb' : (((θ u).2.val : ℤ) : K) = (u : K) * (u : K) ^ p := by
      rw [hcast, hθ2]
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact legendreSym_disc_eq_neg_one hcardK hp2 hne ha' hb'
    · rw [rankApp_eq_orderOf hne ha' hb', orderOf_inv]
      rw [hSα, Finset.mem_filter] at hu
      exact hu.2
  -- each fiber over `T` has exactly two elements
  have hfiber : ∀ ab ∈ T, (Sα.filter (fun u => θ u = ab)).card = 2 := by
    intro ab hab
    rw [hT, Finset.mem_filter] at hab
    obtain ⟨-, hleg, hrank⟩ := hab
    set A := ab.1 with hA
    set B := ab.2 with hB
    have hΔ0 : (((A.val : ℤ) ^ 2 - 4 * (B.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      rw [(legendreSym.eq_zero_iff p _).mpr h0] at hleg
      omega
    have hΔns : ¬IsSquare (((A.val : ℤ) ^ 2 - 4 * (B.val : ℤ) : ℤ)
        : ZMod p) := by
      intro hsq
      rw [(legendreSym.eq_one_iff (p := p) hΔ0).mpr hsq] at hleg
      omega
    have hΔval : (((A.val : ℤ) ^ 2 - 4 * (B.val : ℤ) : ℤ) : ZMod p)
        = A ^ 2 - 4 * B := by
      push_cast
      rw [ZMod.natCast_rightInverse A, ZMod.natCast_rightInverse B]
    -- the pair's quadratic is irreducible; get a root `α ∈ K`
    have hnoroot : ∀ γ : ZMod p, ¬IsRoot (X ^ 2 - C A * X + C B) γ := by
      intro γ hγ
      rw [IsRoot] at hγ
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C,
        eval_X] at hγ
      apply hΔns
      rw [hΔval]
      exact ⟨2 * γ - A, by linear_combination -4 * hγ⟩
    have hgdeg : (X ^ 2 - C A * X + C B).natDegree = 2 := by
      rw [show (X ^ 2 - C A * X + C B : (ZMod p)[X])
          = C 1 * X ^ 2 + C (-A) * X + C B by rw [map_one, map_neg]; ring]
      exact natDegree_quadratic one_ne_zero
    have hgirr : Irreducible (X ^ 2 - C A * X + C B) :=
      irreducible_of_degree_le_three_of_not_isRoot
        (by rw [hgdeg]; decide) hnoroot
    obtain ⟨α, hα⟩ :=
      exists_root_of_irreducible_quadratic hcardK hgirr hgdeg
    have hroot : α ^ 2 - algebraMap (ZMod p) K A * α
        + algebraMap (ZMod p) K B = 0 := by
      have h := hα
      simp only [map_add, map_sub, map_pow, map_mul, aeval_X,
        aeval_C] at h
      exact h
    have hB0 : B ≠ 0 := by
      intro h0
      apply hΔns
      rw [hΔval, h0]
      exact ⟨A, by ring⟩
    have hα0 : α ≠ 0 := by
      intro h0
      apply hB0
      apply (algebraMap (ZMod p) K).injective
      rw [map_zero]
      have h := hroot
      rw [h0] at h
      linear_combination h
    set u : Kˣ := Units.mk0 α hα0 with hu_def
    haveI : CharP K p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
    have hAfix : (algebraMap (ZMod p) K A) ^ p
        = algebraMap (ZMod p) K A := by
      rw [← map_pow, ZMod.pow_card]
    have hBfix : (algebraMap (ZMod p) K B) ^ p
        = algebraMap (ZMod p) K B := by
      rw [← map_pow, ZMod.pow_card]
    have hfroot : (α ^ p) ^ 2 - algebraMap (ZMod p) K A * α ^ p
        + algebraMap (ZMod p) K B = 0 := by
      have h := congrArg (frobenius K p) hroot
      simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
      simp only [frobenius_def] at h
      rwa [hAfix, hBfix] at h
    have hprd : α * (algebraMap (ZMod p) K A - α)
        = algebraMap (ZMod p) K B := by
      linear_combination -hroot
    have hquad : ∀ γ : K, γ ^ 2 - algebraMap (ZMod p) K A * γ
        + algebraMap (ZMod p) K B
        = (γ - α) * (γ - (algebraMap (ZMod p) K A - α)) := by
      intro γ
      linear_combination -hprd
    have hfix_ne : α ^ p ≠ α := by
      intro hfix
      obtain ⟨γ, hγ⟩ := mem_range_algebraMap_of_pow_card (K := K) hfix
      apply hnoroot γ
      rw [IsRoot]
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
      apply (algebraMap (ZMod p) K).injective
      rw [map_zero, map_add, map_sub, map_pow, map_mul, hγ]
      exact hroot
    have hβeq : α ^ p = algebraMap (ZMod p) K A - α := by
      have h0 := hquad (α ^ p)
      rw [hfroot] at h0
      rcases mul_eq_zero.mp h0.symm with h | h
      · exact absurd (sub_eq_zero.mp h) hfix_ne
      · exact sub_eq_zero.mp h
    have hu_sum : (u : K) + (u : K) ^ p = algebraMap (ZMod p) K A := by
      rw [hu_def, Units.val_mk0, hβeq]
      ring
    have hu_prod : (u : K) * (u : K) ^ p = algebraMap (ZMod p) K B := by
      rw [hu_def, Units.val_mk0, hβeq]
      exact hprd
    have hu_ne : (u : K) ^ p ≠ (u : K) := by
      rw [hu_def, Units.val_mk0]
      exact hfix_ne
    have ha' : (((A.val : ℤ)) : K) = (u : K) + (u : K) ^ p := by
      rw [hcast, hu_sum]
    have hb' : (((B.val : ℤ)) : K) = (u : K) * (u : K) ^ p := by
      rw [hcast, hu_prod]
    have hrk := rankApp_eq_orderOf hu_ne ha' hb'
    have hu_mem : u ∈ Sα := by
      rw [hSα, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← orderOf_inv, ← hrk]
      exact hrank
    have hθu : θ u = ab := by
      have h1 : (θ u).1 = A :=
        (algebraMap (ZMod p) K).injective (by rw [hθ1, hu_sum])
      have h2 : (θ u).2 = B :=
        (algebraMap (ZMod p) K).injective (by rw [hθ2, hu_prod])
      exact Prod.ext h1 h2
    -- the conjugate root gives the second fiber element
    have hαp0 : α ^ p ≠ 0 := pow_ne_zero _ hα0
    set v : Kˣ := Units.mk0 (α ^ p) hαp0 with hv_def
    have hv_eq : v = u ^ p := Units.ext (by
      rw [hv_def, Units.val_mk0, Units.val_pow_eq_pow_val, hu_def,
        Units.val_mk0])
    have hordu : orderOf (u ^ (p - 1)) = p + 1 := by
      rw [hSα, Finset.mem_filter] at hu_mem
      exact hu_mem.2
    have hv_mem : v ∈ Sα := by
      rw [hSα, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hv_eq, ← pow_mul, mul_comm p (p - 1), pow_mul, orderOf_pow,
        hordu, show Nat.gcd (p + 1) p = 1 by simp [Nat.gcd_comm],
        Nat.div_one]
    have hvp : (v : K) ^ p = α := by
      rw [hv_def, Units.val_mk0, ← pow_mul, ← pow_two]
      exact pow_card_sq hcardK α
    have hθv : θ v = ab := by
      have h1 : (θ v).1 = A :=
        (algebraMap (ZMod p) K).injective (by
          rw [hθ1, hvp, hv_def, Units.val_mk0, hβeq]
          ring)
      have h2 : (θ v).2 = B :=
        (algebraMap (ZMod p) K).injective (by
          rw [hθ2, hvp, hv_def, Units.val_mk0, hβeq]
          linear_combination hprd)
      exact Prod.ext h1 h2
    have huv_ne : u ≠ v := by
      intro h
      apply hfix_ne
      rw [hu_def, hv_def, Units.mk0_inj] at h
      exact h.symm
    have hfib_eq : Sα.filter (fun w => θ w = ab) = {u, v} := by
      ext w
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hwS, hwθ⟩
        have hwsum : (w : K) + (w : K) ^ p = algebraMap (ZMod p) K A := by
          rw [← hθ1 w, hwθ]
        have hwprod : (w : K) * (w : K) ^ p = algebraMap (ZMod p) K B := by
          rw [← hθ2 w, hwθ]
        have hwroot : ((w : K) - α)
            * ((w : K) - (algebraMap (ZMod p) K A - α)) = 0 := by
          rw [← hquad, ← hwsum, ← hwprod]
          ring
        rcases mul_eq_zero.mp hwroot with h | h
        · left
          exact Units.ext (by
            rw [sub_eq_zero.mp h, hu_def, Units.val_mk0])
        · right
          exact Units.ext (by
            rw [sub_eq_zero.mp h, hv_def, Units.val_mk0, hβeq])
      · rintro (rfl | rfl)
        · exact ⟨hu_mem, hθu⟩
        · exact ⟨hv_mem, hθv⟩
    rw [hfib_eq, Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact huv_ne), Finset.card_singleton]
  -- assemble the count
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hST : Sα.card = 2 * T.card := by
    rw [hsum, Finset.sum_congr rfl hfiber, Finset.sum_const,
      smul_eq_mul]
    ring
  have hScard : Sα.card = (p - 1) * Nat.totient (p + 1) :=
    card_units_orderOf_pow_sub_one hcardK
  omega

end CP

end Azurite
