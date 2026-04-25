import Azurite.BasuPollackRoy.Chapter2.Theorem_2_11_a_b

/-!
# BPR Theorem 2.11 b) ⇒ c): R[i] Algebraically Closed ⟹ Intermediate Value Property

**Theorem 2.11 (b ⇒ c) (BPR).** If R is an ordered field and R[i] := R[X]/(X² + 1)
is algebraically closed, then R has the intermediate value property:
for any P ∈ R[X] and a < b with P(a)·P(b) < 0, there exists x ∈ (a,b) with P(x) = 0.

**Proof strategy.** Strong induction on the degree of P. At each step, we extract
a root α of P in R[i] (using algebraic closure). If α is real, we factor out (X − α)
and the quotient still changes sign (lower degree → IH). If α is not real, we factor
out the always-positive quadratic (X − c)² + d² and the quotient still changes sign
(lower degree → IH).
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Section 1: X² + 1 is irreducible over any ordered field -/

/-- In any ordered field, no element squares to −1. -/
private theorem not_isSquare_neg_one_ordered : ¬ IsSquare (-1 : R) := by
  rintro ⟨x, hx⟩
  linarith [mul_self_nonneg x]

/-- X² + 1 is irreducible over any ordered field R. -/
theorem irred_X_sq_add_one_ordered :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
    simp [this, Finset.mem_Icc]
  · intro x
    simp only [Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_one]
    intro h; exact not_isSquare_neg_one_ordered ⟨x, by linarith⟩

/-- Fact instance for AdjoinRoot.instField. -/
instance instFactIrredOrdered :
    Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irred_X_sq_add_one_ordered⟩

/-! ## Section 2: Conjugation for ordered fields

Key properties from the a⇒b file proved for `[CommRing R]`:
`Ri.conj`, `Ri.conj_i`, `Ri.conj_conj`, `Ri.conj_injective`, `Ri.i_sq`.

We re-derive `conj_fixed_mem_range` (originally under `[IsRealClosed R]`)
since the proof only needs `Irreducible (X² + 1)`. -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Conjugation fixes elements of R. -/
theorem Ri.conj_algebraMap_ordered (r : R) :
    (Ri.conj R) (algebraMap R (Ri R) r) = algebraMap R (Ri R) r :=
  (Ri.conj R).commutes r

/-- The imaginary unit is nonzero. -/
theorem Ri.i_ne_zero_ordered : Ri.i R ≠ 0 := by
  intro h; have := Ri.i_sq R
  rw [h, zero_pow (by norm_num : 2 ≠ 0)] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

/-- `algebraMap R (Ri R)` is injective. -/
theorem algebraMap_Ri_injective :
    Function.Injective (algebraMap R (Ri R)) :=
  (algebraMap R (Ri R)).injective

/-- If conj(c) = c, then c ∈ range(algebraMap R (Ri R)). -/
theorem Ri.conj_fixed_mem_range_ordered (c : Ri R) (hc : (Ri.conj R) c = c) :
    c ∈ Set.range (algebraMap R (Ri R)) := by
  induction c using AdjoinRoot.induction_on with
  | ih p =>
    rw [show AdjoinRoot.mk _ p = Polynomial.aeval (Ri.i R) p from
      (AdjoinRoot.aeval_eq p).symm]
    rw [show AdjoinRoot.mk _ p = Polynomial.aeval (Ri.i R) p from
      (AdjoinRoot.aeval_eq p).symm] at hc
    have hconj_aeval : (Ri.conj R) (Polynomial.aeval (Ri.i R) p) =
        Polynomial.aeval (-Ri.i R) p := by
      rw [← Polynomial.aeval_algHom_apply]
      exact congr_arg (fun x => Polynomial.aeval x p) (Ri.conj_i R)
    rw [hconj_aeval] at hc
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    have haeval_eq : Polynomial.aeval (Ri.i R) p = Polynomial.aeval (Ri.i R) r := by
      have : AdjoinRoot.mk ((X : R[X])^2+1) p = AdjoinRoot.mk ((X : R[X])^2+1) r := by
        rw [AdjoinRoot.mk_eq_mk]
        exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
      rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq] at this; exact this
    rw [haeval_eq]
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]; rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
        rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero (Fact.out : Irreducible f)),
          hnat]; norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    have haeval_neg_eq : Polynomial.aeval (-Ri.i R) r =
        Polynomial.aeval (Ri.i R) r := by
      have haeval_neg_f : Polynomial.aeval (-Ri.i R) f = 0 := by
        simp [f, Polynomial.aeval_def, eval₂_add, eval₂_pow, eval₂_one, eval₂_X]
        linear_combination Ri.i_sq R
      have haeval_neg_eq_pr : Polynomial.aeval (-Ri.i R) p =
          Polynomial.aeval (-Ri.i R) r := by
        have hpr : p - r = f * (p /ₘ f) := by
          have := modByMonic_eq_sub_mul_div p f; linear_combination -this
        have := congr_arg (Polynomial.aeval (-Ri.i R)) hpr
        simp [map_sub, map_mul, haeval_neg_f, zero_mul] at this
        linear_combination this
      rw [← haeval_neg_eq_pr, hc]; exact haeval_eq
    have hi_ne : Ri.i R ≠ 0 := Ri.i_ne_zero_ordered
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    set a := r.coeff 0; set b := r.coeff 1
    have haeval_r : ∀ x : Ri R,
        Polynomial.aeval x r = algebraMap R (Ri R) b * x + algebraMap R (Ri R) a := by
      intro x; conv_lhs => rw [hr_decomp]
      simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    have h2bi : algebraMap R (Ri R) b * Ri.i R = 0 := by
      have h1 := haeval_r (Ri.i R)
      have h2 := haeval_r (-Ri.i R)
      rw [h1, h2] at haeval_neg_eq
      have hsub : algebraMap R (Ri R) b * (-Ri.i R) -
          algebraMap R (Ri R) b * Ri.i R = 0 := by linear_combination haeval_neg_eq
      rw [mul_neg, ← neg_add', ← two_mul, neg_eq_zero, mul_eq_zero, mul_eq_zero] at hsub
      rcases hsub with h | h | h
      · exfalso; exact (two_ne_zero : (2 : R) ≠ 0)
          (algebraMap_Ri_injective (show (algebraMap R (Ri R)) 2 =
            (algebraMap R (Ri R)) 0 by rw [map_zero]; exact_mod_cast h))
      · exact mul_eq_zero_of_left h _
      · exact absurd h hi_ne
    have hb_zero : algebraMap R (Ri R) b = 0 :=
      (mul_eq_zero.mp h2bi).resolve_right hi_ne
    rw [haeval_r (Ri.i R), hb_zero, zero_mul, zero_add]
    exact ⟨a, rfl⟩

/-! ## Section 3: Conjugation root lemma -/

/-- If α is a root of (P.map ι) for P ∈ R[X], then conj(α) is also a root.
    Uses `aeval_algHom_apply`: conj(aeval α P) = aeval (conj α) P. -/
theorem conj_isRoot_of_map (P : R[X]) (α : Ri R)
    (hα : Polynomial.aeval α P = 0) :
    Polynomial.aeval ((Ri.conj R) α) P = 0 := by
  have : (Ri.conj R) (Polynomial.aeval α P) = Polynomial.aeval ((Ri.conj R) α) P := by
    rw [Polynomial.aeval_algHom_apply]
  rw [hα, map_zero] at this; exact this.symm

/-- Version using IsRoot and eval on mapped polynomial. -/
theorem conj_isRoot_of_map' (P : R[X]) (α : Ri R)
    (hα : (P.map (algebraMap R (Ri R))).IsRoot α) :
    (P.map (algebraMap R (Ri R))).IsRoot ((Ri.conj R) α) := by
  simp only [Polynomial.IsRoot, Polynomial.eval_map] at *
  exact conj_isRoot_of_map P α hα

/-! ## Section 4: Element representation -/

/-- Every element of Ri R can be decomposed as ι(a) + ι(b) * i. -/
theorem Ri.repr_exists (z : Ri R) :
    ∃ a b : R, z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f r := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]; rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
        rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero (Fact.out : Irreducible f)),
          hnat]; norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    rw [hmk, show AdjoinRoot.mk f r = Polynomial.aeval (Ri.i R) r from
      (AdjoinRoot.aeval_eq r).symm, hr_decomp]
    simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    exact ⟨r.coeff 0, r.coeff 1, by ring⟩

/-- Conjugation acts as expected on the representation. -/
theorem Ri.conj_repr (a b : R) :
    (Ri.conj R) (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) =
    algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R := by
  simp only [map_add, map_mul, Ri.conj_algebraMap_ordered, Ri.conj_i, mul_neg]
  ring

/-- α + conj(α) is in R (conj-fixed). -/
theorem Ri.add_conj_in_range (α : Ri R) :
    α + (Ri.conj R) α ∈ Set.range (algebraMap R (Ri R)) :=
  Ri.conj_fixed_mem_range_ordered _ (by
    simp only [map_add, Ri.conj_conj]; ring)

/-- α * conj(α) is in R (conj-fixed). -/
theorem Ri.mul_conj_in_range (α : Ri R) :
    α * (Ri.conj R) α ∈ Set.range (algebraMap R (Ri R)) :=
  Ri.conj_fixed_mem_range_ordered _ (by
    simp only [map_mul, Ri.conj_conj]; ring)

/-! ## Section 5: Quadratic factor and positivity -/

/-- For α ∈ Ri R not in R, α · conj(α) = ι(a² + b²) with a² + b² > 0. -/
theorem Ri.norm_pos_of_not_real (α : Ri R)
    (hα : (Ri.conj R) α ≠ α) :
    ∃ n : R, algebraMap R (Ri R) n = α * (Ri.conj R) α ∧ 0 < n := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists α
  have hb_ne : b ≠ 0 := by
    intro hb; apply hα
    rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]
  refine ⟨a ^ 2 + b ^ 2, ?_, add_pos_of_nonneg_of_pos (sq_nonneg a)
    (sq_pos_iff.mpr hb_ne)⟩
  rw [hab, Ri.conj_repr]
  have hi_sq : (Ri.i R) ^ 2 = -(1 : Ri R) := Ri.i_sq R
  rw [map_add, map_pow, map_pow]
  ring_nf
  rw [show Ri.i R ^ 2 = -(1 : Ri R) from hi_sq]
  ring

/-- The trace α + conj(α) = 2a for α = ι(a) + ι(b) * i. -/
theorem Ri.trace_repr (α : Ri R) :
    ∃ s : R, algebraMap R (Ri R) s = α + (Ri.conj R) α := by
  obtain ⟨r, hr⟩ := Ri.add_conj_in_range α; exact ⟨r, hr⟩

/-- The norm α * conj(α) ∈ R. -/
theorem Ri.norm_repr (α : Ri R) :
    ∃ n : R, algebraMap R (Ri R) n = α * (Ri.conj R) α := by
  obtain ⟨r, hr⟩ := Ri.mul_conj_in_range α; exact ⟨r, hr⟩

/-- The quadratic X² - sX + n evaluates to (x - a)² + b² when s = 2a, n = a² + b². -/
private theorem quad_eval_pos (a b x : R) (hb : b ≠ 0) :
    0 < x ^ 2 - 2 * a * x + (a ^ 2 + b ^ 2) := by
  have : x ^ 2 - 2 * a * x + (a ^ 2 + b ^ 2) = (x - a) ^ 2 + b ^ 2 := by ring
  rw [this]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_iff.mpr hb)

/-! ## Section 6: Divisibility lifting -/

/-- If M is monic and M.map ι ∣ P.map ι, then M ∣ P (over R[X]). -/
theorem dvd_of_map_dvd_monic (M P : R[X]) (hM : M.Monic)
    (hdvd : M.map (algebraMap R (Ri R)) ∣ P.map (algebraMap R (Ri R))) :
    M ∣ P := by
  -- Euclidean division: P = M * Q + T with deg T < deg M
  set Q := P /ₘ M
  set T := P %ₘ M
  have hPT : P = M * Q + T := by
    have := modByMonic_eq_sub_mul_div P M; linear_combination -this
  have hT_deg : T.degree < M.degree := degree_modByMonic_lt P hM
  -- Map to Ri R
  have hmap : P.map (algebraMap R (Ri R)) =
      M.map (algebraMap R (Ri R)) * Q.map (algebraMap R (Ri R)) +
      T.map (algebraMap R (Ri R)) := by
    conv_lhs => rw [hPT]
    simp only [Polynomial.map_add, Polynomial.map_mul]
  -- M.map ι ∣ T.map ι
  have hT_dvd : M.map (algebraMap R (Ri R)) ∣ T.map (algebraMap R (Ri R)) := by
    obtain ⟨S, hS⟩ := hdvd
    exact ⟨S - Q.map (algebraMap R (Ri R)), by linear_combination hmap.symm.trans hS⟩
  -- deg(T.map ι) < deg(M.map ι), so T.map ι = 0
  have hTmap : T.map (algebraMap R (Ri R)) = 0 := by
    by_contra hTne
    have h1 : (T.map (algebraMap R (Ri R))).degree <
        (M.map (algebraMap R (Ri R))).degree := by
      rwa [Polynomial.degree_map_eq_of_injective algebraMap_Ri_injective,
           Polynomial.degree_map_eq_of_injective algebraMap_Ri_injective]
    exact absurd (Polynomial.degree_le_of_dvd hT_dvd hTne) (not_le.mpr h1)
  -- T.map ι = 0 and ι injective ⟹ T = 0
  have hT : T = 0 :=
    Polynomial.map_injective _ algebraMap_Ri_injective (by rw [hTmap, Polynomial.map_zero])
  exact ⟨Q, by rw [hPT, hT, add_zero]⟩

/-! ## Section 7: Sign analysis helpers -/

/-- If r < a < b or a < b < r, then (a - r)(b - r) > 0. -/
private theorem pos_of_same_side {a b r : R} (hab : a < b)
    (hr : r < a ∨ b < r) :
    0 < (a - r) * (b - r) := by
  rcases hr with h | h
  · exact mul_pos (by linarith) (by linarith)
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

/-- Key sign lemma: if P = (X - C r) * Q with r ∉ (a,b) and P(a)*P(b) < 0,
    then Q(a)*Q(b) < 0. -/
private theorem sign_transfer {a b r : R} (hab : a < b)
    (hr : r < a ∨ b < r)
    {Q : R[X]} (hsign : eval a ((X - C r) * Q) * eval b ((X - C r) * Q) < 0) :
    eval a Q * eval b Q < 0 := by
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hsign ⊢
  have hpos : 0 < (a - r) * (b - r) := pos_of_same_side hab hr
  -- hsign: (a-r)*Q(a) * ((b-r)*Q(b)) < 0
  -- Rearrange: (a-r)*(b-r) * (Q(a)*Q(b)) < 0
  have h2 : (a - r) * (b - r) * (Q.eval a * Q.eval b) < 0 := by nlinarith
  nlinarith [sq_nonneg ((a - r) * (b - r))]

/-! ## Section 8: The quadratic factor divides P -/

/-- Given α ∈ Ri R a root of P.map ι with conj(α) ≠ α, the quadratic
    (X - α)(X - conj α) divides P.map ι. -/
theorem conj_pair_dvd_map (P : R[X]) (α : Ri R)
    (hα : Polynomial.aeval α P = 0)
    (hα_ne : (Ri.conj R) α ≠ α) :
    (X - C α) * (X - C ((Ri.conj R) α)) ∣ P.map (algebraMap R (Ri R)) := by
  have hα' : Polynomial.aeval ((Ri.conj R) α) P = 0 := conj_isRoot_of_map P α hα
  -- Both α and conj(α) are roots
  have hroot1 : (P.map (algebraMap R (Ri R))).IsRoot α := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact hα
  have hroot2 : (P.map (algebraMap R (Ri R))).IsRoot ((Ri.conj R) α) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact hα'
  -- (X - α) divides P.map ι
  have h1 : (X - C α) ∣ P.map (algebraMap R (Ri R)) := dvd_iff_isRoot.mpr hroot1
  obtain ⟨Q, hQ⟩ := h1
  -- conj(α) is a root of Q (since it's a root of P.map ι and ≠ α)
  have hQ_root : Q.IsRoot ((Ri.conj R) α) := by
    have : (P.map (algebraMap R (Ri R))).eval ((Ri.conj R) α) = 0 := hroot2
    rw [hQ, eval_mul, eval_sub, eval_X, eval_C] at this
    have h_ne : (Ri.conj R) α - α ≠ 0 := sub_ne_zero.mpr hα_ne
    exact (mul_eq_zero.mp this).resolve_left h_ne
  -- (X - conj(α)) divides Q
  have h2 : (X - C ((Ri.conj R) α)) ∣ Q := dvd_iff_isRoot.mpr hQ_root
  obtain ⟨S, hS⟩ := h2
  exact ⟨S, by rw [hQ, hS, mul_assoc]⟩

/-- The monic quadratic for a conjugate pair: X² - (α + conj α)X + α * conj α.
    Its image under map ι equals (X - α)(X - conj α). -/
theorem quad_of_conj_pair (α : Ri R) (hα_ne : (Ri.conj R) α ≠ α) :
    ∃ M : R[X],
      M.Monic ∧ M.natDegree = 2 ∧
      M.map (algebraMap R (Ri R)) =
        (X - C α) * (X - C ((Ri.conj R) α)) ∧
      (∀ x : R, 0 < M.eval x) := by
  -- Get trace and norm
  obtain ⟨s₀, hs₀⟩ := Ri.trace_repr α
  obtain ⟨n₀, hn₀⟩ := Ri.norm_repr α
  -- Get representation for positivity
  obtain ⟨a, b, hab⟩ := Ri.repr_exists α
  have hb_ne : b ≠ 0 := by
    intro hb; apply hα_ne
    rw [hab, hb, map_zero, zero_mul, add_zero, Ri.conj_algebraMap_ordered]
  -- The trace s₀ = 2a
  have hs₀_val : algebraMap R (Ri R) s₀ =
      algebraMap R (Ri R) (2 * a) := by
    rw [hs₀, hab, Ri.conj_repr, map_mul, map_ofNat]; ring
  have hs₀_eq : s₀ = 2 * a := algebraMap_Ri_injective hs₀_val
  -- The norm n₀ = a² + b²
  have hn₀_val : algebraMap R (Ri R) n₀ =
      algebraMap R (Ri R) (a ^ 2 + b ^ 2) := by
    rw [hn₀, hab, Ri.conj_repr]
    rw [map_add, map_pow, map_pow]
    have hi_sq : (Ri.i R) ^ 2 = -(1 : Ri R) := Ri.i_sq R
    ring_nf; rw [show Ri.i R ^ 2 = -(1 : Ri R) from hi_sq]; ring
  have hn₀_eq : n₀ = a ^ 2 + b ^ 2 := algebraMap_Ri_injective hn₀_val
  -- Define M
  set M := (X : R[X]) ^ 2 - C s₀ * X + C n₀ with hM_def
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · -- Monic
    show M.leadingCoeff = 1
    have hM_eq : M = X ^ 2 + (-C s₀ * X + C n₀) := by ring
    have hlt : (-C s₀ * X + C n₀ : R[X]).degree < (X ^ 2 : R[X]).degree := by
      have h1 : (-C s₀ * X : R[X]).degree ≤ 1 := by
        calc (-C s₀ * X : R[X]).degree = (C (-s₀) * X).degree := by rw [map_neg]
          _ ≤ 1 := degree_C_mul_X_le _
      have h2 : (C n₀ : R[X]).degree ≤ 0 := degree_C_le
      calc (-C s₀ * X + C n₀ : R[X]).degree
          ≤ max ((-C s₀ * X : R[X]).degree) ((C n₀ : R[X]).degree) := degree_add_le _ _
        _ ≤ max 1 0 := max_le_max h1 h2
        _ = 1 := by simp
        _ < 2 := by norm_num
        _ = (X ^ 2 : R[X]).degree := by simp
    rw [hM_eq, Polynomial.leadingCoeff_add_of_degree_lt' hlt]; simp
  · -- natDegree = 2
    have hM_eq : M = X ^ 2 + (-C s₀ * X + C n₀) := by ring
    have hlt : (-C s₀ * X + C n₀ : R[X]).degree < (X ^ 2 : R[X]).degree := by
      have h1 : (-C s₀ * X : R[X]).degree ≤ 1 := by
        calc (-C s₀ * X : R[X]).degree = (C (-s₀) * X).degree := by rw [map_neg]
          _ ≤ 1 := degree_C_mul_X_le _
      have h2 : (C n₀ : R[X]).degree ≤ 0 := degree_C_le
      calc (-C s₀ * X + C n₀ : R[X]).degree
          ≤ max ((-C s₀ * X : R[X]).degree) ((C n₀ : R[X]).degree) := degree_add_le _ _
        _ ≤ max 1 0 := max_le_max h1 h2
        _ = 1 := by simp
        _ < 2 := by norm_num
        _ = (X ^ 2 : R[X]).degree := by simp
    rw [hM_eq, Polynomial.natDegree_add_eq_left_of_degree_lt hlt]; simp
  · -- map equals (X - α)(X - conj α)
    simp only [hM_def, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, map_X, map_C]
    rw [hs₀, hn₀, map_add C, map_mul C]
    ring
  · -- Positive at all real points
    intro x
    simp only [hM_def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    rw [hs₀_eq, hn₀_eq]
    exact quad_eval_pos a b x hb_ne

/-! ## Section 9: Main induction -/

/-- **Core IVP lemma by strong induction on degree.** -/
theorem ivp_of_algClosed [IsAlgClosed (Ri R)]
    (P : R[X]) (a b : R) (hab : a < b)
    (hsign : P.eval a * P.eval b < 0) :
    ∃ x : R, a < x ∧ x < b ∧ P.eval x = 0 := by
  -- Strong induction on natDegree
  suffices ∀ n, ∀ P : R[X], P.natDegree = n → P.eval a * P.eval b < 0 →
      ∃ x : R, a < x ∧ x < b ∧ P.eval x = 0 from this _ P rfl hsign
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro P h_ind hsign
  -- P must be nonconstant (sign change)
  have hP_ne : P ≠ 0 := by intro h; simp [h] at hsign
  have hPa_ne : P.eval a ≠ 0 := by intro h; simp [h] at hsign
  have hPb_ne : P.eval b ≠ 0 := by intro h; simp [h] at hsign
  have hn_pos : 0 < n := by
    rw [← h_ind]; exact Nat.pos_of_ne_zero fun h => by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h] at hsign
      simp only [eval_C] at hsign; exact not_lt.mpr (mul_self_nonneg _) hsign
  -- P.map ι has a root α in Ri R
  have hP_nc : 0 < (P.map (algebraMap R (Ri R))).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective algebraMap_Ri_injective, h_ind]
  have hP_deg : (P.map (algebraMap R (Ri R))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective algebraMap_Ri_injective]
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (h_ind ▸ hn_pos))
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hP_deg
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hα
  -- Case split: is α real or not?
  by_cases hα_real : (Ri.conj R) α = α
  · -- Case A: α is real
    obtain ⟨r, hr⟩ := Ri.conj_fixed_mem_range_ordered α hα_real
    -- r is a root of P
    have hPr : P.eval r = 0 := by
      have : Polynomial.aeval (algebraMap R (Ri R) r) P = 0 := hr ▸ hα
      rw [Polynomial.aeval_algebraMap_apply] at this
      exact algebraMap_Ri_injective (this.trans (map_zero _).symm)
    -- Does r lie in (a, b)?
    by_cases hab_r : a < r ∧ r < b
    · exact ⟨r, hab_r.1, hab_r.2, hPr⟩
    · -- r ∉ (a, b). Factor P = (X - C r) * Q
      push Not at hab_r
      have hra : r ≠ a := fun h => hPa_ne (h ▸ hPr)
      have hrb : r ≠ b := fun h => hPb_ne (h ▸ hPr)
      have hr_side : r < a ∨ b < r := by
        by_cases h : r < a
        · left; exact h
        · right; push Not at h
          exact lt_of_le_of_ne (hab_r (lt_of_le_of_ne h hra.symm)) (Ne.symm hrb)
      obtain ⟨Q, hPQ⟩ := dvd_iff_isRoot.mpr hPr
      have hQ_ne : Q ≠ 0 := right_ne_zero_of_mul (hPQ ▸ hP_ne)
      have hQ_deg : Q.natDegree < n := by
        have hXr_ne : (X - C r : R[X]) ≠ 0 := (monic_X_sub_C r).ne_zero
        have : P.natDegree = (X - C r).natDegree + Q.natDegree :=
          hPQ ▸ Polynomial.natDegree_mul hXr_ne hQ_ne
        rw [natDegree_X_sub_C, h_ind] at this; omega
      have hQ_sign : Q.eval a * Q.eval b < 0 := by
        rw [hPQ] at hsign
        simp only [eval_mul, eval_sub, eval_X, eval_C] at hsign
        have hpos : 0 < (a - r) * (b - r) := by
          rcases hr_side with h | h
          · exact mul_pos (by linarith) (by linarith)
          · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
        nlinarith [sq_nonneg ((a - r) * (b - r))]
      obtain ⟨x, hxa, hxb, hQx⟩ := ih Q.natDegree hQ_deg Q rfl hQ_sign
      exact ⟨x, hxa, hxb, by rw [hPQ, eval_mul, hQx, mul_zero]⟩
  · -- Case B: α is not real
    obtain ⟨M, hM_monic, hM_deg, hM_map, hM_pos⟩ :=
      quad_of_conj_pair α hα_real
    -- M.map ι divides P.map ι
    have hM_dvd_map : M.map (algebraMap R (Ri R)) ∣
        P.map (algebraMap R (Ri R)) := by
      rw [hM_map]; exact conj_pair_dvd_map P α hα hα_real
    -- So M divides P in R[X]
    have hM_dvd : M ∣ P := dvd_of_map_dvd_monic M P hM_monic hM_dvd_map
    obtain ⟨Q, hPQ⟩ := hM_dvd
    -- Degree bookkeeping
    have hQ_deg : Q.natDegree < n := by
      have hQ_ne : Q ≠ 0 := right_ne_zero_of_mul (hPQ ▸ hP_ne)
      have : P.natDegree = M.natDegree + Q.natDegree :=
        hPQ ▸ Polynomial.natDegree_mul (ne_of_apply_ne Polynomial.leadingCoeff
          (hM_monic.leadingCoeff ▸ one_ne_zero)) hQ_ne
      rw [h_ind, hM_deg] at this; omega
    -- Sign transfer
    have hQ_sign : Q.eval a * Q.eval b < 0 := by
      rw [hPQ] at hsign
      simp only [eval_mul] at hsign
      have hMa_pos : 0 < M.eval a := hM_pos a
      have hMb_pos : 0 < M.eval b := hM_pos b
      by_contra h; push Not at h
      have h1 : 0 < M.eval a * M.eval b := mul_pos hMa_pos hMb_pos
      have h2 : M.eval a * Q.eval a * (M.eval b * Q.eval b) =
          M.eval a * M.eval b * (Q.eval a * Q.eval b) := by ring
      rw [h2] at hsign
      exact absurd hsign (not_lt.mpr (mul_nonneg (le_of_lt h1) h))
    obtain ⟨x, hxa, hxb, hQx⟩ := ih Q.natDegree hQ_deg Q rfl hQ_sign
    exact ⟨x, hxa, hxb, by rw [hPQ, eval_mul, hQx, mul_zero]⟩

/-! ## Section 10: Final theorem -/

/-- **BPR Theorem 2.11 (b ⇒ c).** If R[i] is algebraically closed,
    then R has the intermediate value property. -/
theorem theorem_2_11_b_c [IsAlgClosed (Ri R)] :
    Azurite.BPR.HasIntermediateValueProperty R :=
  fun P a b hab hsign => ivp_of_algClosed P a b hab hsign

end Azurite.BPR.Theorem2_11
