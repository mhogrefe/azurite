import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_21

/-!
# BPR Proposition 2.22: Rolle's Theorem

**Proposition 2.22 (BPR).** Let `R` be an ordered field with the intermediate
value property, `P ∈ R[X]`, `a < b`, `P(a) = P(b) = 0`. Then `P'` has a root
in `(a, b)`.

The proof factors `P` as `(X − a)^m · (X − b)^n · Q` with `Q(a), Q(b) ≠ 0`,
shows `Q` has constant sign on `[a, b]` (Proposition 2.20), and applies the
intermediate value property to a carefully constructed auxiliary polynomial
`Q₁` whose evaluations at `a` and `b` have opposite signs.
-/

namespace Azurite.BPR.Proposition2_22

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11 Azurite.BPR.Proposition2_20
  Azurite.BPR.Proposition2_21

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `Q ≠ 0` does not vanish on `[a, b]` (with `a < b`) and `R` has the IVP,
    then `sign(Q(a)) = sign(Q(b))` (constant sign on `[a, b]`). -/
private lemma sign_eq_of_no_root_Icc (hIVP : HasIntermediateValueProperty R)
    {Q : R[X]} (hQ : Q ≠ 0) {a b : R} (hab : a < b)
    (hne : ∀ x ∈ Set.Icc a b, Q.eval x ≠ 0) :
    SignType.sign (Q.eval a) = SignType.sign (Q.eval b) := by
  obtain ⟨a', ha', hne_l⟩ := exists_no_root_Ioo_left hQ a
  obtain ⟨b', hb', hne_r⟩ := exists_no_root_Ioo_right hQ b
  have hne_all : ∀ x ∈ Set.Ioo a' b', Q.eval x ≠ 0 := by
    intro x ⟨hxa', hxb'⟩
    by_cases hax : a ≤ x
    · by_cases hxb : x ≤ b
      · exact hne x ⟨hax, hxb⟩
      · exact hne_r x ⟨not_le.mp hxb, hxb'⟩
    · exact hne_l x ⟨hxa', not_le.mp hax⟩
  have ha_mem : a ∈ Set.Ioo a' b' := ⟨ha', lt_trans hab hb'⟩
  have hb_mem : b ∈ Set.Ioo a' b' := ⟨lt_trans ha' hab, hb'⟩
  rcases proposition_2_20 hIVP Q a' b' hne_all with hpos | hneg
  · rw [sign_pos (hpos a ha_mem), sign_pos (hpos b hb_mem)]
  · rw [sign_neg (hneg a ha_mem), sign_neg (hneg b hb_mem)]

/-- **Rolle's theorem, base case.** If `P(a) = P(b) = 0`, `a < b`, `P ≠ 0`, and
    `P` does not vanish on `(a, b)`, then `P'` has a root in `(a, b)`. -/
private lemma rolle_base (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a b : R} (hab : a < b)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) :
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  -- Factor P = (X - C a)^m * Q₀, Q₀(a) ≠ 0
  set m := P.rootMultiplicity a with hm_def
  set Q₀ := P /ₘ (X - C a) ^ m with hQ₀_def
  have hP₀ : (X - C a) ^ m * Q₀ = P := pow_mul_divByMonic_rootMultiplicity_eq P a
  have hQ₀a : Q₀.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hQ₀_ne : Q₀ ≠ 0 := fun h => hQ₀a (by simp [h])
  -- Evaluation lemma for P
  have hP_eval : ∀ x, P.eval x = (x - a) ^ m * Q₀.eval x := fun x => by
    have := congr_arg (Polynomial.eval x) hP₀; simp at this; linarith
  -- m ≥ 1 since P(a) = 0
  have hm_pos : 0 < m := (rootMultiplicity_pos hP).mpr hPa
  -- Q₀(b) = 0 (from P(b) = 0 and a ≠ b)
  have hQ₀b : Q₀.eval b = 0 := by
    have := hP_eval b; rw [hPb] at this
    exact (mul_eq_zero.mp this.symm).resolve_left
      (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt hab)))
  -- Factor Q₀ = (X - C b)^n * Q, Q(b) ≠ 0
  set n := Q₀.rootMultiplicity b with hn_def
  set Q := Q₀ /ₘ (X - C b) ^ n with hQ_def
  have hQ₀_fac : (X - C b) ^ n * Q = Q₀ := pow_mul_divByMonic_rootMultiplicity_eq Q₀ b
  have hQb : Q.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hQ₀_ne
  have hQ_ne : Q ≠ 0 := fun h => hQb (by simp [h])
  -- n ≥ 1
  have hn_pos : 0 < n := (rootMultiplicity_pos hQ₀_ne).mpr hQ₀b
  -- Evaluation lemma for Q₀
  have hQ₀_eval : ∀ x, Q₀.eval x = (x - b) ^ n * Q.eval x := fun x => by
    have := congr_arg (Polynomial.eval x) hQ₀_fac; simp at this; exact this.symm
  -- Q(a) ≠ 0
  have hQa : Q.eval a ≠ 0 := by
    intro h; have := hQ₀_eval a; rw [h, mul_zero] at this; exact hQ₀a this
  -- P = (X - C a)^m * (X - C b)^n * Q
  have hP_eq : P = (X - C a) ^ m * ((X - C b) ^ n * Q) := by
    calc P = (X - C a) ^ m * Q₀ := hP₀.symm
      _ = (X - C a) ^ m * ((X - C b) ^ n * Q) := by rw [← hQ₀_fac]
  -- Combined evaluation
  have hP_eval' : ∀ x, P.eval x = (x - a) ^ m * ((x - b) ^ n * Q.eval x) := fun x => by
    rw [hP_eval, hQ₀_eval]
  -- Q doesn't vanish on [a, b]
  have hQ_ne_Icc : ∀ x ∈ Set.Icc a b, Q.eval x ≠ 0 := by
    intro x ⟨hax, hxb⟩ hQx
    rcases hax.eq_or_lt with rfl | hax
    · exact hQa hQx
    · rcases hxb.eq_or_lt with rfl | hxb
      · exact hQb hQx
      · exact hne x ⟨hax, hxb⟩ (by rw [hP_eval' x, hQx, mul_zero, mul_zero])
  -- sign(Q(a)) = sign(Q(b))
  have hQ_sign : SignType.sign (Q.eval a) = SignType.sign (Q.eval b) :=
    sign_eq_of_no_root_Icc hIVP hQ_ne hab hQ_ne_Icc
  -- Q(a) * Q(b) > 0
  have hQab_pos : 0 < Q.eval a * Q.eval b := by
    rcases lt_or_gt_of_ne hQa with hQa_neg | hQa_pos
    · exact mul_pos_of_neg_of_neg hQa_neg
        (sign_eq_neg_one_iff.mp (hQ_sign ▸ sign_neg hQa_neg))
    · exact mul_pos hQa_pos
        (sign_eq_one_iff.mp (hQ_sign ▸ sign_pos hQa_pos))
  -- Write m = m' + 1, n = n' + 1
  obtain ⟨m', hm⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', hn⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- Define Q₁
  set Q₁ : R[X] :=
    C (↑m : R) * (X - C b) * Q +
    C (↑n : R) * (X - C a) * Q +
    (X - C a) * (X - C b) * derivative Q with hQ₁_def
  -- Q₁(a) * Q₁(b) < 0
  have hQ₁a : Q₁.eval a = ↑m * (a - b) * Q.eval a := by
    simp [hQ₁_def]
  have hQ₁b : Q₁.eval b = ↑n * (b - a) * Q.eval b := by
    simp [hQ₁_def]
  have hQ₁_opp : Q₁.eval a * Q₁.eval b < 0 := by
    rw [hQ₁a, hQ₁b]
    have : ↑m * (a - b) * Q.eval a * (↑n * (b - a) * Q.eval b) =
        -(↑m * ↑n * (b - a) ^ 2 * (Q.eval a * Q.eval b)) := by ring
    rw [this]
    have h_pos : (0 : R) < ↑m * ↑n * (b - a) ^ 2 * (Q.eval a * Q.eval b) :=
      mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hm_pos)
        (Nat.cast_pos.mpr hn_pos)) (sq_pos_of_pos (sub_pos.mpr hab))) hQab_pos
    linarith
  -- IVP gives c ∈ (a, b) with Q₁(c) = 0
  obtain ⟨c, hac, hcb, hQ₁c⟩ := hIVP Q₁ a b hab hQ₁_opp
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  -- It suffices to factor out (c-a)^m'*(c-b)^n' and use Q₁(c) = 0
  suffices hsuff : (derivative P).eval c =
      (c - a) ^ m' * ((c - b) ^ n' * Q₁.eval c) by
    rw [hsuff, hQ₁c, mul_zero, mul_zero]
  rw [hP_eq, hm, hn]
  simp only [derivative_mul, derivative_pow_succ, derivative_X_sub_C, mul_one,
    eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, hQ₁_def]
  push_cast [hm, hn]
  ring

/-- **BPR Proposition 2.22 (Rolle's theorem).** Let `R` be an ordered field with
    the intermediate value property, `P ∈ R[X]`, `a < b`, `P(a) = P(b) = 0`.
    Then `P'` has a root in `(a, b)`. -/
theorem proposition_2_22 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (hab : a < b)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  by_cases hP : P = 0
  · obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, ⟨hac, hcb⟩, by simp [hP]⟩
  classical
  set F := P.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) with hF_def
  have hb_in : b ∈ F := by
    rw [hF_def, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP]
    exact ⟨hPb, hab, le_refl b⟩
  set c := F.min' ⟨b, hb_in⟩
  have hc_mem := Finset.mem_filter.mp (F.min'_mem ⟨b, hb_in⟩)
  have hac : a < c := hc_mem.2.1
  have hcb : c ≤ b := hc_mem.2.2
  have hPc : P.eval c = 0 := by
    rw [Multiset.mem_toFinset, mem_roots hP] at hc_mem; exact hc_mem.1
  have hno_root : ∀ x ∈ Set.Ioo a c, P.eval x ≠ 0 := by
    intro x hx hPx
    have hxF : x ∈ F := by
      rw [hF_def, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP]
      exact ⟨hPx, hx.1, le_of_lt (lt_of_lt_of_le hx.2 hcb)⟩
    exact absurd hx.2 (not_lt.mpr (F.min'_le x hxF))
  obtain ⟨d, hd, hPd⟩ := rolle_base hIVP hP hac hPa hPc hno_root
  exact ⟨d, ⟨hd.1, lt_of_lt_of_le hd.2 hcb⟩, hPd⟩

/-- **Proposition 2.22 (Rolle's theorem), real closed form.** -/
theorem proposition_2_22_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b → P.eval a = 0 → P.eval b = 0 →
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_22 theorem_2_11_b_c P

end Azurite.BPR.Proposition2_22
