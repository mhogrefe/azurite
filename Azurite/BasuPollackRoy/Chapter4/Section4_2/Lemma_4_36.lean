import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_31
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_32
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_37

/-!
# BPR Lemma 4.36: `PmV` under a Euclidean step (in progress)

For `P` of degree `p`, `Q` of degree `q < p`, and `R = Rem(P, Q)`, BPR Lemma 4.36
relates the generalized permanences-minus-variations of the subresultant
sequences:

  `PmV(sRes(P,Q)) = PmV(sRes(Q,−R)) + sign(a_p b_q)`  if `p − q` is odd,
  `PmV(sRes(P,Q)) = PmV(sRes(Q,−R))`                  if `p − q` is even.

The proof (`lemma_4_36`) rests on Proposition 4.37: the bottom parts of the two
sequences (`sRes_r, …, sRes_0`) are proportional, hence have equal `PmV` (scaling
invariance, `PmV_smul`), and the top parts are bridged across their degree gaps
(`PmV_partialSeq_bridge`), with the gap contributions evaluated using the
determinant value `sRes_q = ε_{p-q}b_q^{p-q}` (`sRes_q_eq`).

Reusable `PmV` toolkit: `PmV_smul` (scaling invariance), `PmV_cons_zeros`
(gap-cons), `PmV_partialSeq_bridge` (bridge across a gap of zeros).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `dropWhile` commutes with `map`, transporting the predicate. -/
private theorem dropWhile_map {α β : Type*} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).dropWhile p = (l.dropWhile (fun x => p (f x))).map f
  | [] => rfl
  | a :: l => by
    by_cases h : p (f a) = true
    · rw [List.map_cons, List.dropWhile_cons_of_pos h, dropWhile_map f p l,
        List.dropWhile_cons_of_pos (p := fun x => p (f x)) (a := a) (l := l) h]
    · rw [List.map_cons, List.dropWhile_cons_of_neg (by simpa using h),
        List.dropWhile_cons_of_neg (p := fun x => p (f x)) (a := a) (l := l)
          (by simpa using h), List.map_cons]

/-- **`PmV` is invariant under scaling by a nonzero constant.** Multiplying every
entry of `s` by `c ≠ 0` preserves the zero pattern and all sign products
`sign(s_i s_j)`, so `PmV` is unchanged. -/
theorem PmV_smul {c : K} (hc : c ≠ 0) :
    ∀ l : List K, PmV (l.map (fun x => c * x)) = PmV l
  | [] => by simp
  | sp :: rest => by
    have hpred : (fun x : K => decide (c * x = 0)) = (fun x => decide (x = 0)) := by
      funext x; simp [mul_eq_zero, hc]
    have hdrop : (rest.map (fun x => c * x)).dropWhile (fun x => decide (x = 0))
        = (rest.dropWhile (fun x => decide (x = 0))).map (fun x => c * x) := by
      rw [dropWhile_map]; simp only [hpred]
    -- split on whether the next nonzero exists
    rcases hd : rest.dropWhile (fun x => decide (x = 0)) with _ | ⟨sq, tl⟩
    · rw [List.map_cons, PmV, PmV, hdrop, hd, List.map_nil]
    · rw [List.map_cons, PmV, PmV, hdrop, hd, List.map_cons]
      simp only [List.length_cons, List.length_map]
      have hsign : SignType.sign (c * sp * (c * sq)) = SignType.sign (sp * sq) := by
        rw [show c * sp * (c * sq) = c ^ 2 * (sp * sq) by ring, sign_mul,
          sign_pos (show (0 : K) < c ^ 2 by positivity), one_mul]
      rw [show (c * sq :: List.map (fun x => c * x) tl)
            = List.map (fun x => c * x) (sq :: tl) from rfl,
        PmV_smul hc (sq :: tl), hsign]
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have := List.length_dropWhile_le (fun x => decide (x = 0)) rest
    rw [hd] at this
    simp only [List.length_cons] at this
    omega

omit [IsStrictOrderedRing K] in
/-- **`PmV` gap-cons.** For `a` followed by a run of zeros and then a nonzero `b`:
the recursion skips the zeros, so `PmV(a :: 0…0 :: b :: rest) = PmV(b :: rest) +
[gap odd] ε_gap · sign(a·b)`, where `gap = #zeros + 1`. -/
theorem PmV_cons_zeros (a : K) (zeros : List K) (hz : ∀ x ∈ zeros, x = 0)
    (b : K) (hb : b ≠ 0) (rest : List K) :
    PmV (a :: (zeros ++ b :: rest)) = PmV (b :: rest) +
      (if Odd (zeros.length + 1) then
        ε (zeros.length + 1) * (SignType.sign (a * b) : ℤ) else 0) := by
  have hdrop : (zeros ++ b :: rest).dropWhile (fun x => decide (x = 0)) = b :: rest := by
    induction zeros with
    | nil =>
      simp only [List.nil_append]
      exact List.dropWhile_cons_of_neg (by simp [hb])
    | cons z zl ih =>
      rw [List.cons_append, List.dropWhile_cons_of_pos (by simp [hz z (by simp)])]
      exact ih (fun x hx => hz x (by simp [hx]))
  rw [PmV]
  split
  · next h => rw [hdrop] at h; exact absurd h (by simp)
  · next sq tl h =>
    rw [hdrop] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    rw [show (zeros ++ b :: rest).length + 1 - (b :: rest).length = zeros.length + 1 by
      simp only [List.length_append, List.length_cons]; omega]

/-- **`sRes_q(P, Q) = ε_{p-q}·b_q^{p-q}`.** For `q < p`, the `j = q` Sylvester-Habicht
square consists only of `Q`-shift rows `X^0 Q, …, X^{p-q-1} Q`, a `b_q`-anti-triangular
matrix; reversing columns makes it lower-triangular with diagonal `b_q`. -/
theorem sRes_q_eq (P Q : K[X]) (hQ : Q ≠ 0) (hqp : Q.natDegree < P.natDegree) :
    sRes P Q Q.natDegree = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
      Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
  rw [sRes, ite_eq_left (le_refl Q.natDegree)]
  -- reversed-column entry: `(X^i · Q).coeff (q + k)`
  have hentry : ∀ i k : Fin (P.natDegree + Q.natDegree - 2 * Q.natDegree),
      ((SyHaSquare P Q Q.natDegree).submatrix id Fin.revPerm) i k
        = (X ^ i.val * Q).coeff (Q.natDegree + k.val) := by
    intro i k
    have hk := k.isLt
    simp only [Matrix.submatrix_apply, id_eq, SyHaSquare, SyHa, Matrix.of_apply, Fin.val_castLE]
    rw [ite_eq_right (by omega),
      show i.val - (Q.natDegree - Q.natDegree) = i.val by omega,
      show P.natDegree + Q.natDegree - Q.natDegree - 1 - (Fin.revPerm k).val
          = Q.natDegree + k.val by
        rw [show (Fin.revPerm k) = Fin.rev k from rfl, Fin.val_rev]; omega]
  -- the reversed matrix is lower-triangular with `b_q` diagonal
  have hlow : ((SyHaSquare P Q Q.natDegree).submatrix id Fin.revPerm).det
      = Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
    rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => ?_)]
    · rw [Finset.prod_congr rfl (g := fun _ => Q.leadingCoeff) (fun i _ => ?_),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        show P.natDegree + Q.natDegree - 2 * Q.natDegree = P.natDegree - Q.natDegree by omega]
      rw [hentry i i, Polynomial.coeff_X_pow_mul]
      rfl
    · rw [hentry i j]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hQ,
        Polynomial.natDegree_X_pow]
      have : i.val < j.val := by simpa using hij
      omega
  -- relate `sign(revPerm) · det = b^{p-q}` to `det = ε · b^{p-q}`
  have hperm := Matrix.det_permute' (Fin.revPerm :
    Equiv.Perm (Fin (P.natDegree + Q.natDegree - 2 * Q.natDegree)))
    (SyHaSquare P Q Q.natDegree)
  rw [hlow] at hperm
  have hsign : (↑(Equiv.Perm.sign
      (Fin.revPerm : Equiv.Perm (Fin (P.natDegree + Q.natDegree - 2 * Q.natDegree)))) : K)
      = ((ε (P.natDegree + Q.natDegree - 2 * Q.natDegree) : ℤ) : K) := by
    rw [← sign_revPerm]
  rw [hsign] at hperm
  have hε : ((ε (P.natDegree + Q.natDegree - 2 * Q.natDegree) : ℤ) : K)
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) := by
    congr 2; omega
  rw [hε] at hperm
  -- hperm : ε(p-q) * det = b^{p-q};  ε² = 1 gives det = ε(p-q) * b^{p-q}
  have hε2 : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
      ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ε_mul_self, Int.cast_one]
  calc (SyHaSquare P Q Q.natDegree).det
      = 1 * (SyHaSquare P Q Q.natDegree).det := (one_mul _).symm
    _ = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
          (((ε (P.natDegree - Q.natDegree) : ℤ) : K) * (SyHaSquare P Q Q.natDegree).det) := by
        rw [← mul_assoc, hε2]
    _ = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
          Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by rw [hperm]

/-! ### Partial subresultant sequences and the bridging -/

/-- The partial subresultant sequence `[sRes_a, sRes_{a-1}, …, sRes_0]`. -/
noncomputable def partialSeq (P Q : K[X]) (a : ℕ) : List K :=
  (List.range (a + 1)).map (fun j => sRes P Q (a - j))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem partialSeq_succ (P Q : K[X]) (a : ℕ) :
    partialSeq P Q (a + 1) = sRes P Q (a + 1) :: partialSeq P Q a := by
  unfold partialSeq
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem partialSeq_split (P Q : K[X]) (b d : ℕ) :
    partialSeq P Q (b + d) =
      ((List.range d).map (fun i => sRes P Q (b + d - i))) ++ partialSeq P Q b := by
  induction d with
  | zero => simp [partialSeq]
  | succ n ih =>
    rw [show b + (n + 1) = (b + n) + 1 by omega, partialSeq_succ, ih,
      List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
    simp only [Nat.sub_zero]
    congr 2
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `sRes_j(P, Q) = 0` for `q < j < p` (the defective subresultants in the gap). -/
theorem sRes_eq_zero_of_gap (P Q : K[X]) {j : ℕ} (hqj : Q.natDegree < j)
    (hjp : j < P.natDegree) : sRes P Q j = 0 := by
  rw [sRes, ite_eq_right (by omega), ite_eq_left (lt_trans hqj hjp), ite_eq_right (by omega)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `partialSeq P Q b` has head `sRes_b`. -/
theorem partialSeq_eq_cons (P Q : K[X]) (b : ℕ) :
    partialSeq P Q b = sRes P Q b :: (List.range b).map (fun j => sRes P Q (b - 1 - j)) := by
  unfold partialSeq
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

omit [IsStrictOrderedRing K] in
/-- **`PmV` bridge across a gap of zeros.** If `sRes_b ≠ 0` and `sRes_j = 0` for
`b < j < a`, then `PmV(partialSeq a) = PmV(partialSeq b) + [a−b odd] ε_{a-b}·sign(sRes_a·sRes_b)`. -/
theorem PmV_partialSeq_bridge (P Q : K[X]) {a b : ℕ} (hba : b < a)
    (hsb : sRes P Q b ≠ 0)
    (hzero : ∀ j, b < j → j < a → sRes P Q j = 0) :
    PmV (partialSeq P Q a) = PmV (partialSeq P Q b) +
      (if Odd (a - b) then ε (a - b) * (SignType.sign (sRes P Q a * sRes P Q b) : ℤ) else 0) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [partialSeq_split, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
  simp only [Nat.sub_zero]
  rw [partialSeq_eq_cons P Q b,
    PmV_cons_zeros (sRes P Q (b + (d' + 1))) _ ?_ (sRes P Q b) hsb _]
  · rw [← partialSeq_eq_cons, List.length_map, List.length_range,
      show b + (d' + 1) - b = d' + 1 by omega]
  · intro x hx
    simp only [List.mem_map, List.mem_range, Function.comp_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hzero (b + (d' + 1) - (i + 1)) (by omega) (by omega)

/-! ### Sign helpers and the main lemma -/

theorem ε_eq_one_or_neg_one (n : ℕ) : ε n = 1 ∨ ε n = -1 := by
  unfold ε
  rcases Nat.even_or_odd (n * (n - 1) / 2) with he | ho
  · exact Or.inl he.neg_one_pow
  · exact Or.inr ho.neg_one_pow

theorem sign_eps (n : ℕ) : (SignType.sign ((ε n : ℤ) : K) : ℤ) = ε n := by
  rcases ε_eq_one_or_neg_one n with h | h
  · rw [h, Int.cast_one, sign_one]; decide
  · rw [h, show ((-1 : ℤ) : K) = -1 by norm_num, sign_neg (by norm_num)]; decide

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `(ε_n : K) ≠ 0`. -/
theorem eps_cast_ne (n : ℕ) : ((ε n : ℤ) : K) ≠ 0 := by
  rcases ε_eq_one_or_neg_one n with h | h <;> rw [h] <;> simp

theorem sign_pow_cast (x : K) (m : ℕ) :
    (SignType.sign (x ^ m) : ℤ) = (SignType.sign x : ℤ) ^ m := by
  induction m with
  | zero => simp
  | succ n ih => rw [pow_succ, sign_mul, SignType.coe_mul, ih, ← pow_succ]

/-- For `x ≠ 0` and `m` odd, `sign(x^m) = sign x` (in `ℤ`). -/
theorem sign_pow_odd (x : K) (hx : x ≠ 0) {m : ℕ} (hm : Odd m) :
    (SignType.sign (x ^ m) : ℤ) = (SignType.sign x : ℤ) := by
  rw [sign_pow_cast]
  rcases (show (SignType.sign x : ℤ) = 1 ∨ (SignType.sign x : ℤ) = -1 by
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inr (by rw [sign_neg h]; decide)
    · exact absurd h hx
    · exact Or.inl (by rw [sign_pos h]; decide)) with h | h
  · rw [h, one_pow]
  · rw [h, hm.neg_one_pow]

/-- **BPR Lemma 4.36.** `PmV(sRes(P, Q)) = PmV(sRes(Q, −R)) + [p−q odd]·sign(a_p b_q)`,
with `R = P % Q`. The PmV-version of the Euclidean-step recursion (Lemma 4.35),
proved by bridging the subresultant sequences across their degree gaps
(Proposition 4.37) and the determinant value `sRes_q = ε_{p-q}b_q^{p-q}`. -/
theorem lemma_4_36 (P Q : K[X]) (hQ : Q ≠ 0) (hR : P % Q ≠ 0)
    (hrq : (P % Q).natDegree < Q.natDegree) (hqp : Q.natDegree < P.natDegree) :
    PmV (sResSeq P Q) = PmV (sResSeq Q (-(P % Q)))
      + (if Odd (P.natDegree - Q.natDegree)
          then (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) else 0) := by
  have hbq : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hRn : -(P % Q) ≠ 0 := neg_ne_zero.mpr hR
  have hrneg : (-(P % Q)).natDegree = (P % Q).natDegree := Polynomial.natDegree_neg _
  show PmV (partialSeq P Q P.natDegree)
      = PmV (partialSeq Q (-(P % Q)) Q.natDegree) + _
  -- subresultant values
  have hsp : sRes P Q P.natDegree = P.leadingCoeff := by
    rw [sRes, ite_eq_right (by omega), ite_eq_left hqp, ite_eq_left rfl]
  have hsq : sRes P Q Q.natDegree
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) :=
    sRes_q_eq P Q hQ hqp
  have hsq_ne : sRes P Q Q.natDegree ≠ 0 := by
    rw [hsq]; exact mul_ne_zero (eps_cast_ne _) (pow_ne_zero _ hbq)
  have hsqQR : sRes Q (-(P % Q)) Q.natDegree = Q.leadingCoeff := by
    rw [sRes, ite_eq_right (by rw [hrneg]; omega), ite_eq_left (by rw [hrneg]; omega), ite_eq_left rfl]
  have hdr_ne : sRes Q (-(P % Q)) (P % Q).natDegree ≠ 0 := by
    have h := sRes_q_eq Q (-(P % Q)) hRn (by rw [hrneg]; exact hrq)
    rw [hrneg] at h; rw [h]
    exact mul_ne_zero (eps_cast_ne _)
      (pow_ne_zero _ (by rw [Polynomial.leadingCoeff_neg]; exact neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr hR)))
  have hsrP : sRes P Q (P % Q).natDegree
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
        Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) * sRes Q (-(P % Q)) (P % Q).natDegree :=
    proposition_4_37_part1 P Q (P % Q).natDegree hQ (le_refl _) hrq hqp
  have hsrP_ne : sRes P Q (P % Q).natDegree ≠ 0 := by
    rw [hsrP]; exact mul_ne_zero (mul_ne_zero (eps_cast_ne _) (pow_ne_zero _ hbq)) hdr_ne
  -- bridges
  have hpq := PmV_partialSeq_bridge P Q hqp hsq_ne
    (fun j hj hjp => sRes_eq_zero_of_gap P Q hj hjp)
  have hqrP := PmV_partialSeq_bridge P Q hrq hsrP_ne
    (fun j hj hjq => (proposition_4_37_part2 P Q j hQ hj hjq hqp).1)
  have hqrQR := PmV_partialSeq_bridge Q (-(P % Q)) hrq hdr_ne
    (fun j hj hjq => (proposition_4_37_part2 P Q j hQ hj hjq hqp).2)
  -- scaling: the bottom parts are proportional
  have hscale : PmV (partialSeq P Q (P % Q).natDegree)
      = PmV (partialSeq Q (-(P % Q)) (P % Q).natDegree) := by
    have hmap : partialSeq P Q (P % Q).natDegree
        = (partialSeq Q (-(P % Q)) (P % Q).natDegree).map
          (fun x => ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
            Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) * x) := by
      unfold partialSeq
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      exact proposition_4_37_part1 P Q ((P % Q).natDegree - j) hQ (by omega) hrq hqp
    rw [hmap, PmV_smul (mul_ne_zero (eps_cast_ne _) (pow_ne_zero _ hbq))]
  -- assemble
  rw [hpq, hqrP, hscale, hqrQR]
  -- the `q → r` terms agree (identity B) and the `p → q` term is sign(a_p b_q) (identity A)
  have hBeq : (if Odd (Q.natDegree - (P % Q).natDegree) then
        ε (Q.natDegree - (P % Q).natDegree) *
          (SignType.sign (sRes P Q Q.natDegree * sRes P Q (P % Q).natDegree) : ℤ) else 0)
      = (if Odd (Q.natDegree - (P % Q).natDegree) then
        ε (Q.natDegree - (P % Q).natDegree) *
          (SignType.sign (sRes Q (-(P % Q)) Q.natDegree * sRes Q (-(P % Q)) (P % Q).natDegree) : ℤ)
        else 0) := by
    by_cases hodd : Odd (Q.natDegree - (P % Q).natDegree)
    · rw [ite_eq_left hodd, ite_eq_left hodd]
      congr 1
      -- both signs equal sign(b_q · d_r)
      have hPside : (SignType.sign (sRes P Q Q.natDegree * sRes P Q (P % Q).natDegree) : ℤ)
          = (SignType.sign (Q.leadingCoeff * sRes Q (-(P % Q)) (P % Q).natDegree) : ℤ) := by
        rw [hsq, hsrP,
          show ((ε (P.natDegree - Q.natDegree) : ℤ) : K) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) *
              (((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
                Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) * sRes Q (-(P % Q)) (P % Q).natDegree)
            = (((ε (P.natDegree - Q.natDegree) : ℤ) : K) * ((ε (P.natDegree - Q.natDegree) : ℤ) : K)) *
              (Q.leadingCoeff ^ ((P.natDegree - Q.natDegree) + (P.natDegree - (P % Q).natDegree)) *
                sRes Q (-(P % Q)) (P % Q).natDegree) by rw [pow_add]; ring,
          ← Int.cast_mul, ε_mul_self, Int.cast_one, one_mul, sign_mul, SignType.coe_mul,
          sign_pow_odd Q.leadingCoeff hbq (by rw [Nat.odd_iff] at hodd ⊢; omega),
          ← SignType.coe_mul, ← sign_mul]
      rw [hPside, hsqQR]
    · rw [ite_eq_right hodd, ite_eq_right hodd]
  have hAeq : (if Odd (P.natDegree - Q.natDegree) then
        ε (P.natDegree - Q.natDegree) *
          (SignType.sign (sRes P Q P.natDegree * sRes P Q Q.natDegree) : ℤ) else 0)
      = (if Odd (P.natDegree - Q.natDegree) then
          (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) else 0) := by
    by_cases hodd : Odd (P.natDegree - Q.natDegree)
    · rw [ite_eq_left hodd, ite_eq_left hodd, hsp, hsq,
        show P.leadingCoeff * (((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
            Q.leadingCoeff ^ (P.natDegree - Q.natDegree))
          = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
            (P.leadingCoeff * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) by ring,
        sign_mul, SignType.coe_mul, sign_eps, ← mul_assoc, ε_mul_self, one_mul,
        sign_mul, SignType.coe_mul, sign_pow_odd Q.leadingCoeff hbq hodd,
        ← SignType.coe_mul, ← sign_mul]
    · rw [ite_eq_right hodd, ite_eq_right hodd]
  rw [hBeq, hAeq]

end Azurite.BPR.Chapter4
