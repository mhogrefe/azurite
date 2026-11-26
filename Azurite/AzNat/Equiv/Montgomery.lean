/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Montgomery
import Azurite.Montgomery.Theory
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Mul.Basic
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Parity
import Azurite.UInt64.Equiv.MulAddWithCarry
import Mathlib.Data.UInt

/-!
# Montgomery reduction on `AzNat` limbs: correctness

* `montNegInv_mul`: `n₀ * montNegInv n₀ + 1 = 0` in `UInt64` for odd `n₀`.
* `redcLimbs_spec`: the limbs `[ne, 2 ne)` of the result hold a number below the modulus whose
  product with `R = 2 ^ (64 ne)` is congruent to the input.
* `MontCtx.redc_spec` and its consequences for `mul`, `sqr`, `toMont`, `fromMont`, `one`
  (`…_spec`, values in `ZMod m`), for the context `MontCtx.make m k` of an odd `m`.
-/

namespace Azurite.AzNat

/-! ### The inverse of the lowest limb -/

open UInt64.CommRing in
private theorem newton_step (b x : UInt64) :
    1 - b * (x * (2 - b * x)) = (1 - b * x) * (1 - b * x) := by ring

open UInt64.CommRing in
/-- `n₀ * montNegInv n₀ = −1` in `UInt64`, for odd `n₀`. -/
theorem montNegInv_mul (n₀ : UInt64) (h : n₀.toNat % 2 = 1) : n₀ * montNegInv n₀ + 1 = 0 := by
  obtain ⟨d, hd⟩ : ∃ d : UInt64, n₀ = 2 * d + 1 := by
    refine ⟨n₀ / 2, ?_⟩
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div]
    have := n₀.toNat_lt
    have h2 : (2 : UInt64).toNat = 2 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h2, h1]
    omega
  have h0 : (1 - n₀ * n₀) = 4 * (0 - d * (d + 1)) := by rw [hd]; ring
  have h4 : ((4 : UInt64) ^ 32) = 0 := by decide
  have key : 1 - n₀ * (0 - montNegInv n₀) = 0 := by
    unfold montNegInv
    simp only [zero_sub, neg_neg]
    rw [newton_step, newton_step, newton_step, newton_step, newton_step, h0]
    calc _ = (4 : UInt64) ^ 32 * (0 - d * (d + 1)) ^ 32 := by ring
      _ = 0 := by rw [h4, zero_mul]
  linear_combination key

/-! ### Values of whole buffers -/

/-- The value of a whole limb array. -/
private abbrev arrVal (a : Array UInt64) : ℕ := toNatLimbsList a.toList

/-- The value of the slice `a[lo : lo + len)`. -/
private abbrev sl (a : Array UInt64) (lo len : ℕ) : ℕ :=
  toNatLimbsList ((a.toList.drop lo).take len)

private theorem arrVal_split (a : Array UInt64) (p len : ℕ) (h : p + len ≤ a.size) :
    arrVal a = toNatLimbsList (a.toList.take p) + 2 ^ (64 * p) *
      (sl a p len + 2 ^ (64 * len) * toNatLimbsList (a.toList.drop (p + len))) := by
  have e : a.toList = a.toList.take p ++
      ((a.toList.drop p).take len ++ a.toList.drop (p + len)) := by
    rw [show a.toList.drop (p + len) = (a.toList.drop p).drop len by rw [List.drop_drop],
      List.take_append_drop, List.take_append_drop]
  have l1 : (a.toList.take p).length = p := by
    rw [List.length_take, Array.length_toList]; omega
  have l2 : ((a.toList.drop p).take len).length = len := by
    rw [List.length_take, List.length_drop, Array.length_toList]; omega
  conv_lhs => rw [arrVal, e]
  rw [toNatLimbsList_append, toNatLimbsList_append, l1, l2]
  ring

/-- A change confined to the slice `[p, p + len)` changes the whole value accordingly. -/
private theorem arrVal_frame (a a' : Array UInt64) (p len c y : ℕ) (h : p + len ≤ a.size)
    (hs : a'.size = a.size) (ht : a'.toList.take p = a.toList.take p)
    (hd : a'.toList.drop (p + len) = a.toList.drop (p + len))
    (hv : sl a' p len + c * 2 ^ (64 * len) = sl a p len + y) :
    arrVal a' + c * 2 ^ (64 * (p + len)) = arrVal a + y * 2 ^ (64 * p) := by
  rw [arrVal_split a p len h, arrVal_split a' p len (by omega), ht, hd,
    show 64 * (p + len) = 64 * p + 64 * len by ring, pow_add]
  linear_combination (2 ^ (64 * p)) * hv

private theorem arrVal_mulAdd2 (N a : Array UInt64) (ne i : ℕ) (q₀ q₁ : UInt64)
    (hN : N.size = ne) (ha : i + ne ≤ a.size) :
    arrVal (mulAdd2Limbs N 0 ne i q₀ q₁ a (by omega) ha).1
        + ((mulAdd2Limbs N 0 ne i q₀ q₁ a (by omega) ha).2.1.toNat
          + (mulAdd2Limbs N 0 ne i q₀ q₁ a (by omega) ha).2.2.toNat * 2 ^ 64)
          * 2 ^ (64 * (i + ne))
      = arrVal a + arrVal N * (q₀.toNat + q₁.toNat * 2 ^ 64) * 2 ^ (64 * i) := by
  have hv := mulAdd2Limbs_toNat N 0 ne i q₀ q₁ a (by omega) ha
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList]; omega)] at hv
  refine arrVal_frame a _ i ne _ _ ha (mulAdd2Limbs_size _ _ _ _ _ _ _ _ _) ?_ ?_
    (hv.symm.trans (Nat.add_comm _ _))
  · exact mulAdd2Limbs.go_toList_take_le N 0 ne i q₀ q₁ a 0 0 0 (by omega) ha i (by omega)
  · exact mulAdd2Limbs.go_toList_drop N 0 ne i q₀ q₁ a 0 0 0 (by omega) ha

private theorem arrVal_addLimb (a : Array UInt64) (lo hi : ℕ) (b : UInt64) (hlo : lo < hi)
    (hhi : hi = a.size) :
    arrVal (addLimb a lo hi b (by omega) (by omega)).1
        + (addLimb a lo hi b (by omega) (by omega)).2.toNat * 2 ^ (64 * hi)
      = arrVal a + b.toNat * 2 ^ (64 * lo) := by
  have hv := addLimb_toNat a lo hi b (by omega) (by omega) hlo
  have e := arrVal_frame a (addLimb a lo hi b (by omega) (by omega)).1 lo (hi - lo)
    (addLimb a lo hi b (by omega) (by omega)).2.toNat b.toNat (by omega)
    (addLimb_size _ _ _ _ _ _) (addLimb_toList_take _ _ _ _ _ _) ?_ hv
  · rwa [show lo + (hi - lo) = hi by omega] at e
  · rw [List.drop_of_length_le (by rw [Array.length_toList, addLimb_size]; omega),
      List.drop_of_length_le (by rw [Array.length_toList]; omega)]

private theorem arrVal_of_dvd (a : Array UInt64) (i : ℕ) (hi : i ≤ a.size)
    (h : 2 ^ (64 * i) ∣ arrVal a) :
    arrVal a = 2 ^ (64 * i) * toNatLimbsList (a.toList.drop i) := by
  have l1 : (a.toList.take i).length = i := by
    rw [List.length_take, Array.length_toList]; omega
  have e : arrVal a = toNatLimbsList (a.toList.drop i) * 2 ^ (64 * i)
      + toNatLimbsList (a.toList.take i) := by
    conv_lhs => rw [arrVal, ← List.take_append_drop i a.toList]
    rw [toNatLimbsList_append, l1]
  have hlt := toNatLimbsList_lt_pow (a.toList.take i)
  rw [l1] at hlt
  have hd : 2 ^ (64 * i) ∣ toNatLimbsList (a.toList.take i) := by
    rw [e] at h
    exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp h
  rw [e, Nat.eq_zero_of_dvd_of_lt hd hlt, Nat.add_zero, Nat.mul_comm]

private theorem dropVal_two (a : Array UInt64) (i : ℕ) (h : i + 1 < a.size) :
    toNatLimbsList (a.toList.drop i) = a[i].toNat + a[i + 1].toNat * 2 ^ 64
      + (2 ^ 64) ^ 2 * toNatLimbsList (a.toList.drop (i + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; omega),
    List.drop_eq_getElem_cons (i := i + 1) (by rw [Array.length_toList]; omega),
    toNatLimbsList_cons, toNatLimbsList_cons, Array.getElem_toList, Array.getElem_toList]
  ring

/-! ### One step -/

private theorem redcStep_spec (N : Array UInt64) (ne : ℕ) (ninv : UInt64) (a : Array UInt64)
    (i : ℕ) (hN : N.size = ne) (ha : a.size = 2 * ne + 1) (hi : i + 2 ≤ ne)
    (hinv : N[0] * ninv + 1 = 0) (hdiv : 2 ^ (64 * i) ∣ arrVal a)
    (hb : arrVal a + 2 ^ (64 * (i + 2)) * arrVal N < 2 ^ (64 * (2 * ne + 1))) :
    ∃ q, q < 2 ^ 128 ∧
      arrVal (redcStep N ne ninv a i hN ha hi) = arrVal a + q * arrVal N * 2 ^ (64 * i) ∧
      2 ^ (64 * (i + 2)) ∣ arrVal (redcStep N ne ninv a i hN ha hi) := by
  -- the quantities of the step
  let t₀ := a[i]
  let t₁ := a[i + 1]
  let q₀ := t₀ * ninv
  let m₀ := UInt64.mulAddWithCarry N[0] q₀ t₀ 0
  let m₁ := UInt64.mulAddWithCarry N[1] q₀ t₁ m₀.1
  let q₁ := m₁.2 * ninv
  let r := mulAdd2Limbs N 0 ne i q₀ q₁ a (by omega) (by omega)
  have hr : r.1.size = a.size := mulAdd2Limbs_size _ _ _ _ _ _ _ _ _
  let s := addLimb r.1 (i + ne) (2 * ne + 1) r.2.1 (by omega) (by omega)
  have hs : s.1.size = a.size := by rw [addLimb_size, hr]
  let u := addLimb s.1 (i + ne + 1) (2 * ne + 1) r.2.2 (by omega) (by omega)
  have hstep : redcStep N ne ninv a i hN ha hi = u.1 := rfl
  have h1 : arrVal r.1 + (r.2.1.toNat + r.2.2.toNat * 2 ^ 64) * 2 ^ (64 * (i + ne))
      = arrVal a + arrVal N * (q₀.toNat + q₁.toNat * 2 ^ 64) * 2 ^ (64 * i) :=
    arrVal_mulAdd2 N a ne i q₀ q₁ hN (by omega)
  have h2 : arrVal s.1 + s.2.toNat * 2 ^ (64 * (2 * ne + 1))
      = arrVal r.1 + r.2.1.toNat * 2 ^ (64 * (i + ne)) :=
    arrVal_addLimb r.1 (i + ne) (2 * ne + 1) r.2.1 (by omega) (by omega)
  have h3 : arrVal u.1 + u.2.toNat * 2 ^ (64 * (2 * ne + 1))
      = arrVal s.1 + r.2.2.toNat * 2 ^ (64 * (i + ne + 1)) :=
    arrVal_addLimb s.1 (i + ne + 1) (2 * ne + 1) r.2.2 (by omega) (by omega)
  rw [hstep]
  set q := q₀.toNat + q₁.toNat * 2 ^ 64 with hq
  have hqlt : q < 2 ^ 128 := by
    have := q₀.toNat_lt
    have := q₁.toNat_lt
    omega
  have key : arrVal u.1 + (s.2.toNat + u.2.toNat) * 2 ^ (64 * (2 * ne + 1))
      = arrVal a + q * arrVal N * 2 ^ (64 * i) := by
    rw [show 64 * (i + ne + 1) = 64 * (i + ne) + 64 by ring, pow_add] at h3
    linear_combination h1 + h2 + h3
  have hlt : arrVal a + q * arrVal N * 2 ^ (64 * i) < 2 ^ (64 * (2 * ne + 1)) := by
    refine lt_of_le_of_lt ?_ hb
    rw [show 64 * (i + 2) = 128 + 64 * i by ring, pow_add]
    have : q * arrVal N * 2 ^ (64 * i) ≤ 2 ^ 128 * arrVal N * 2 ^ (64 * i) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hqlt.le)
    have e : 2 ^ 128 * 2 ^ (64 * i) * arrVal N = 2 ^ 128 * arrVal N * 2 ^ (64 * i) := by ring
    omega
  have hk : s.2.toNat + u.2.toNat = 0 := by
    by_contra hne
    have : 2 ^ (64 * (2 * ne + 1)) ≤ (s.2.toNat + u.2.toNat) * 2 ^ (64 * (2 * ne + 1)) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  rw [hk, Nat.zero_mul, Nat.add_zero] at key
  refine ⟨q, hqlt, key, ?_⟩
  -- divisibility
  have hD := arrVal_of_dvd a i (by omega) hdiv
  have hD2 := dropVal_two a i (by omega)
  have hN2 := dropVal_two N 0 (by omega)
  rw [List.drop_zero] at hN2
  have hinv' : 2 ^ 64 ∣ N[0].toNat * ninv.toNat + 1 := by
    have h0 := congrArg UInt64.toNat hinv
    rw [UInt64.toNat_add, UInt64.toNat_mul] at h0
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h00 : (0 : UInt64).toNat = 0 := rfl
    rw [h1, h00] at h0
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hm0 := UInt64.mulAddWithCarry_eq N[0] q₀ t₀ 0
  have hm1 := UInt64.mulAddWithCarry_eq N[1] q₀ t₁ m₀.1
  rw [show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at hm0
  have hdvd := Azurite.Montgomery.dvd_two_digit_step (β := 2 ^ 64) (t₀ := t₀.toNat)
    (t₁ := t₁.toNat) (n₀ := N[0].toNat) (n₁ := N[1].toNat) (n' := ninv.toNat)
    (h₀ := m₀.1.toNat) (l₀ := m₀.2.toNat) (h₁ := m₁.1.toNat) (u₁ := m₁.2.toNat)
    (q₀ := q₀.toNat) (q₁ := q₁.toNat) (V' := toNatLimbsList (a.toList.drop (i + 2)))
    (N' := toNatLimbsList (N.toList.drop (0 + 2))) hinv' (UInt64.toNat_mul _ _)
    hm0 m₀.2.toNat_lt hm1 (UInt64.toNat_mul _ _)
  rw [key, hD, hD2]
  have hNv : arrVal N = N[0].toNat + N[1].toNat * 2 ^ 64
      + (2 ^ 64) ^ 2 * toNatLimbsList (N.toList.drop (0 + 2)) := hN2
  rw [hNv, show 64 * (i + 2) = 64 * i + 64 * 2 by ring, pow_add, pow_mul 2 64 2]
  obtain ⟨w, hw⟩ := hdvd
  exact ⟨w, by rw [hq]; linear_combination (2 ^ (64 * i)) * hw⟩

/-! ### The loop -/

private theorem redcLoop_spec (N : Array UInt64) (ne : ℕ) (ninv : UInt64) (T : ℕ)
    (hN : N.size = ne) (he : Even ne) (h2 : 2 ≤ ne) (hinv : N[0]'(by omega) * ninv + 1 = 0)
    (hT : T < arrVal N * 2 ^ (64 * ne)) (a : Array UInt64) (i : ℕ)
    (ha : a.size = 2 * ne + 1) (hie : Even i) (hile : i ≤ ne)
    (hval : ∃ Q, Q < 2 ^ (64 * i) ∧ arrVal a = T + Q * arrVal N)
    (hdiv : 2 ^ (64 * i) ∣ arrVal a) :
    ∃ Q, Q ≤ 2 ^ (64 * ne) ∧ arrVal (redcLoop N ne ninv a i hN ha) = T + Q * arrVal N ∧
      2 ^ (64 * ne) ∣ arrVal (redcLoop N ne ninv a i hN ha) := by
  induction h : ne - i using Nat.strong_induction_on generalizing a i with
  | _ k ih =>
    obtain ⟨Q, hQ, hQv⟩ := hval
    rw [redcLoop]
    by_cases hi : i + 2 ≤ ne
    · simp only [hi, ↓reduceDIte]
      have hNlt : arrVal N < 2 ^ (64 * ne) := by
        have := toNatLimbsList_lt_pow N.toList
        rwa [Array.length_toList, hN] at this
      have hpi : 2 ^ (64 * i) ≤ 2 ^ (64 * ne) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpi2 : 2 ^ (64 * (i + 2)) ≤ 2 ^ (64 * ne) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hb : arrVal a + 2 ^ (64 * (i + 2)) * arrVal N < 2 ^ (64 * (2 * ne + 1)) := by
        have e1 : Q * arrVal N ≤ 2 ^ (64 * ne) * arrVal N :=
          Nat.mul_le_mul_right _ (hQ.le.trans hpi)
        have e2 : 2 ^ (64 * (i + 2)) * arrVal N ≤ 2 ^ (64 * ne) * arrVal N :=
          Nat.mul_le_mul_right _ hpi2
        have e3 : 2 ^ (64 * ne) * arrVal N ≤ 2 ^ (64 * ne) * 2 ^ (64 * ne) :=
          Nat.mul_le_mul_left _ hNlt.le
        have e4 : arrVal N * 2 ^ (64 * ne) = 2 ^ (64 * ne) * arrVal N := Nat.mul_comm _ _
        have e5 : 2 ^ (64 * (2 * ne + 1)) = 2 ^ (64 * ne) * 2 ^ (64 * ne) * 2 ^ 64 := by
          rw [← pow_add, ← pow_add]; congr 1; ring
        have e6 : 0 < 2 ^ (64 * ne) * 2 ^ (64 * ne) := by positivity
        rw [hQv, e5]
        omega
      obtain ⟨q, hq, hsv, hsd⟩ := redcStep_spec N ne ninv a i hN ha hi hinv hdiv hb
      refine ih (ne - (i + 2)) (by omega) _ (i + 2) _ ?_ (by omega) ⟨Q + q * 2 ^ (64 * i), ?_, ?_⟩
        hsd rfl
      · obtain ⟨j, hj⟩ := hie
        exact ⟨j + 1, by omega⟩
      · rw [show 64 * (i + 2) = 128 + 64 * i by ring, pow_add]
        have : (q + 1) * 2 ^ (64 * i) ≤ 2 ^ 128 * 2 ^ (64 * i) :=
          Nat.mul_le_mul_right _ hq
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · rw [hsv, hQv]; ring
    · simp only [hi, ↓reduceDIte]
      have hin : i = ne := by
        obtain ⟨j, hj⟩ := hie
        obtain ⟨l, hl⟩ := he
        omega
      subst hin
      exact ⟨Q, hQ.le, hQv, hdiv⟩

/-! ### The reduction -/

/-- **Correctness of `redcLimbs`.**  For an even `ne ≥ 2`, a modulus `N` of `ne` limbs with
`N[0] * ninv = −1`, and a buffer holding `T < N R` (`R = 2 ^ (64 ne)`): the limbs `[ne, 2 ne)`
of the result hold a number `r < N` with `r R ≡ T (mod N)`. -/
theorem redcLimbs_spec (N : Array UInt64) (ne : ℕ) (ninv : UInt64) (a : Array UInt64)
    (hN : N.size = ne) (ha : a.size = 2 * ne + 1) (he : Even ne) (h2 : 2 ≤ ne)
    (hinv : N[0]'(by omega) * ninv + 1 = 0)
    (hT : toNatLimbsList a.toList < toNatLimbsList N.toList * 2 ^ (64 * ne)) :
    toNatLimbsList (((redcLimbs N ne ninv a hN ha).toList.drop ne).take ne)
        < toNatLimbsList N.toList ∧
      toNatLimbsList (((redcLimbs N ne ninv a hN ha).toList.drop ne).take ne) * 2 ^ (64 * ne)
        ≡ toNatLimbsList a.toList [MOD toNatLimbsList N.toList] := by
  obtain ⟨Q, hQ, hval, hdvd⟩ := redcLoop_spec N ne ninv (arrVal a) hN he h2 hinv hT a 0 ha
    ⟨0, by omega⟩ (by omega) ⟨0, by positivity, by simp⟩ (by simp)
  have hNlt : arrVal N < 2 ^ (64 * ne) := by
    have := toNatLimbsList_lt_pow N.toList
    rwa [Array.length_toList, hN] at this
  have hNs : sl N 0 ne = arrVal N := by
    show toNatLimbsList ((N.toList.drop 0).take ne) = _
    rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList]; omega)]
  unfold redcLimbs
  simp only
  set b := redcLoop N ne ninv a 0 hN ha with hbdef
  have hb : b.size = 2 * ne + 1 := by rw [hbdef, redcLoop_size]; exact ha
  have hX := arrVal_of_dvd b ne (by omega) hdvd
  set X := toNatLimbsList (b.toList.drop ne) with hXdef
  have hx : X * 2 ^ (64 * ne) = arrVal a + Q * arrVal N := by
    rw [← hval, hX, Nat.mul_comm]
  have hX2 : X < 2 * arrVal N := Azurite.Montgomery.quotient_lt_two_mul hT hQ hx
  have hsplit : X = sl b ne ne + (b[2 * ne]'(by omega)).toNat * 2 ^ (64 * ne) := by
    have h := toNatLimbsList_drop_take_succ b ne ne (by omega)
    rw [List.take_of_length_le (by rw [List.length_drop, Array.length_toList]; omega)] at h
    simp only [show ne + ne = 2 * ne by omega] at h
    exact h
  have htop : (b[2 * ne]'(by omega)).toNat ≤ 1 := by
    by_contra hc
    have : 2 * 2 ^ (64 * ne) ≤ (b[2 * ne]'(by omega)).toNat * 2 ^ (64 * ne) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hcmp := compareLimbs_eq_compare_slice b N ne 0 ne (by omega) (by omega)
  rw [show toNatLimbsList ((N.toList.drop 0).take ne) = arrVal N from hNs] at hcmp
  split
  · rename_i hcond
    have hge : arrVal N ≤ X := by
      rcases hcond with h | h
      · have : (b[2 * ne]'(by omega)).toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp h0)
        have : 2 ^ (64 * ne) ≤ (b[2 * ne]'(by omega)).toNat * 2 ^ (64 * ne) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · rw [hcmp] at h
        by_contra hlt
        exact h (Nat.compare_eq_lt.mpr (by simp only [arrVal, sl] at *; omega))
    have hsub := subSameLengthLimbs_toNat b N ne 0 ne (by omega) (by omega)
    rw [show toNatLimbsList ((N.toList.drop 0).take ne) = arrVal N from hNs] at hsub
    generalize subSameLengthLimbs b N ne 0 ne (by omega) (by omega) = res at hsub ⊢
    obtain ⟨a', c⟩ := res
    simp only at hsub ⊢
    have hlt' : sl a' ne ne < 2 ^ (64 * ne) := by
      refine lt_of_lt_of_le (toNatLimbsList_lt_pow _) (Nat.pow_le_pow_right (by norm_num) ?_)
      exact Nat.mul_le_mul_left _ (List.length_take_le _ _)
    have hres : sl a' ne ne = X - arrVal N := by
      have h01 : (b[2 * ne]'(by omega)).toNat = 0 ∨ (b[2 * ne]'(by omega)).toNat = 1 := by omega
      simp only [arrVal, sl] at *
      cases c <;> rcases h01 with h0 | h0 <;> rw [h0] at hsplit <;>
        simp only [Bool.toNat_false, Bool.toNat_true] at hsub <;> omega
    show sl a' ne ne < _ ∧ sl a' ne ne * _ ≡ _ [MOD _]
    rw [hres]
    exact ⟨by simp only [arrVal, sl] at *; omega, Azurite.Montgomery.quotient_sub_modEq hx hge⟩
  · rename_i hcond
    push Not at hcond
    obtain ⟨h0, hc⟩ := hcond
    rw [hcmp] at hc
    have hlt := Nat.compare_eq_lt.mp hc
    have hXe : X = sl b ne ne := by rw [hsplit, h0]; simp
    show sl b ne ne < _ ∧ sl b ne ne * _ ≡ _ [MOD _]
    rw [← hXe]
    exact ⟨by simp only [arrVal, sl] at *; omega, Azurite.Montgomery.quotient_modEq hx⟩

/-! ### The context of an odd modulus -/

/-- The limb count of `MontCtx.make m k` is even. -/
theorem MontCtx.even_ne_make (m : AzNat) (k : ℕ) : Even (MontCtx.make m k).ne := by
  show Even (max 2 (m.limbs.size + k + (m.limbs.size + k) % 2))
  refine ⟨max 2 (m.limbs.size + k + (m.limbs.size + k) % 2) / 2, ?_⟩
  omega

/-- The padded limbs of `MontCtx.make m k` are those of `m`. -/
theorem MontCtx.limbs_make_toNat (m : AzNat) (k : ℕ) :
    toNatLimbsList (MontCtx.make m k).limbs.toList = m.toNat := by
  show toNatLimbsList (m.limbs ++ Array.replicate _ 0).toList = _
  rw [Array.toList_append, Array.toList_replicate, toNatLimbsList_append_zeros]
  rfl

/-- The modulus of `MontCtx.make m k` is `m`. -/
@[simp] theorem MontCtx.m_make (m : AzNat) (k : ℕ) : (MontCtx.make m k).m = m := rfl

/-- `m < R`. -/
theorem MontCtx.toNat_lt_pow_make (m : AzNat) (k : ℕ) :
    m.toNat < 2 ^ (64 * (MontCtx.make m k).ne) := by
  have h := toNatLimbsList_lt_pow (MontCtx.make m k).limbs.toList
  rwa [Array.length_toList, (MontCtx.make m k).size_limbs, MontCtx.limbs_make_toNat] at h

/-- The lowest limb and `ninv` of `MontCtx.make m k`, for odd `m`. -/
theorem MontCtx.ninv_make (m : AzNat) (k : ℕ) (hm : Odd m.toNat) :
    (MontCtx.make m k).limbs[0]'(by
        have := (MontCtx.make m k).two_le; have := (MontCtx.make m k).size_limbs; omega)
      * (MontCtx.make m k).ninv + 1 = 0 := by
  have hs : 0 < (MontCtx.make m k).limbs.toList.length := by
    have := (MontCtx.make m k).two_le
    have := (MontCtx.make m k).size_limbs
    rw [Array.length_toList]; omega
  have h := toNatLimbsList_mod_2_64 (MontCtx.make m k).limbs.toList
  simp only [hs, ↓reduceDIte] at h
  rw [MontCtx.limbs_make_toNat] at h
  refine montNegInv_mul _ ?_
  have h2 : m.toNat % 2 = 1 := Nat.odd_iff.mp hm
  have e : ((MontCtx.make m k).limbs[0]'(by
      have := (MontCtx.make m k).two_le; have := (MontCtx.make m k).size_limbs; omega)).toNat
      = m.toNat % 2 ^ 64 := by
    rw [h]; rfl
  rw [e]
  omega

/-- `R mod m` and `R² mod m`. -/
theorem MontCtx.one_make_toNat (m : AzNat) (k : ℕ) :
    (MontCtx.make m k).one.toNat = 2 ^ (64 * (MontCtx.make m k).ne) % m.toNat := by
  show (((1 : AzNat) <<< (64 * (MontCtx.make m k).ne)) % m).toNat = _
  rw [toNat_mod, toNat_hShiftLeft, toNat_one, Nat.shiftLeft_eq, Nat.one_mul]

theorem MontCtx.r2_make_toNat (m : AzNat) (k : ℕ) :
    (MontCtx.make m k).r2.toNat = 2 ^ (128 * (MontCtx.make m k).ne) % m.toNat := by
  show (((1 : AzNat) <<< (128 * (MontCtx.make m k).ne)) % m).toNat = _
  rw [toNat_mod, toNat_hShiftLeft, toNat_one, Nat.shiftLeft_eq, Nat.one_mul]

/-- **Correctness of `MontCtx.redc`** for an odd modulus: for `t < m R`, the result is below `m`
and its product with `R = 2 ^ (64 ne)` is congruent to `t`. -/
theorem MontCtx.redc_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (t : AzNat)
    (ht : t.toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne)) :
    ((MontCtx.make m k).redc t).toNat < m.toNat ∧
      ((MontCtx.make m k).redc t).toNat * 2 ^ (64 * (MontCtx.make m k).ne)
        ≡ t.toNat [MOD m.toNat] := by
  have hmlt := MontCtx.toNat_lt_pow_make m k
  have hsz : t.limbs.size ≤ 2 * (MontCtx.make m k).ne + 1 := by
    by_contra hc
    have h1 := toNat_pos_of_size_pos t (by omega)
    have h2 : 2 ^ (64 * (MontCtx.make m k).ne) * 2 ^ (64 * (MontCtx.make m k).ne)
        ≤ 2 ^ (64 * (t.limbs.size - 1)) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : m.toNat * 2 ^ (64 * (MontCtx.make m k).ne)
        ≤ 2 ^ (64 * (MontCtx.make m k).ne) * 2 ^ (64 * (MontCtx.make m k).ne) :=
      Nat.mul_le_mul_right _ hmlt.le
    omega
  unfold MontCtx.redc
  simp only [hsz, ↓reduceDIte]
  rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop,
    show 2 * (MontCtx.make m k).ne - (MontCtx.make m k).ne = (MontCtx.make m k).ne by omega]
  have hpad : toNatLimbsList (t.limbs ++ Array.replicate
      (2 * (MontCtx.make m k).ne + 1 - t.limbs.size) 0).toList = t.toNat := by
    rw [Array.toList_append, Array.toList_replicate, toNatLimbsList_append_zeros]
    rfl
  have h := redcLimbs_spec (MontCtx.make m k).limbs (MontCtx.make m k).ne (MontCtx.make m k).ninv
    (t.limbs ++ Array.replicate (2 * (MontCtx.make m k).ne + 1 - t.limbs.size) 0)
    (MontCtx.make m k).size_limbs (by simp only [Array.size_append, Array.size_replicate]; omega)
    (MontCtx.even_ne_make m k) (MontCtx.make m k).two_le (MontCtx.ninv_make m k hm)
    (by rw [hpad, MontCtx.limbs_make_toNat]; exact ht)
  rw [hpad, MontCtx.limbs_make_toNat] at h
  exact h

/-! ### In `ZMod m` -/

/-- `R` is invertible modulo an odd `m`. -/
theorem MontCtx.pow_mul_inv (m : AzNat) (k : ℕ) (hm : Odd m.toNat) :
    ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)
      * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm))

/-- `redc t = t R⁻¹` in `ZMod m`. -/
theorem MontCtx.redc_cast (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (t : AzNat)
    (ht : t.toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne)) :
    (((MontCtx.make m k).redc t).toNat : ZMod m.toNat)
      = (t.toNat : ZMod m.toNat) * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)⁻¹ :=
  Azurite.Montgomery.natCast_eq_mul_inv
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)) (MontCtx.redc_spec m k hm t ht).2

/-- A product of two residues is below `m R`. -/
theorem MontCtx.mul_lt (m : AzNat) (k : ℕ) {a b : ℕ} (ha : a < m.toNat) (hb : b < m.toNat) :
    a * b < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne) :=
  Nat.mul_lt_mul'' ha (hb.trans (MontCtx.toNat_lt_pow_make m k))

/-- `mul a b = a b R⁻¹` in `ZMod m`, and it is reduced. -/
theorem MontCtx.mul_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (a b : AzNat)
    (ha : a.toNat < m.toNat)
    (hb : b.toNat < m.toNat) :
    ((MontCtx.make m k).mul a b).toNat < m.toNat ∧
      (((MontCtx.make m k).mul a b).toNat : ZMod m.toNat) = (a.toNat : ZMod m.toNat) * b.toNat
        * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)⁻¹ := by
  have ht : (a * b).toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne) := by
    rw [toNat_mul]; exact MontCtx.mul_lt m k ha hb
  refine ⟨(MontCtx.redc_spec m k hm _ ht).1, ?_⟩
  show (((MontCtx.make m k).redc (a * b)).toNat : ZMod m.toNat) = _
  rw [MontCtx.redc_cast m k hm _ ht, toNat_mul, Nat.cast_mul]

/-- `sqr a = a² R⁻¹` in `ZMod m`, and it is reduced. -/
theorem MontCtx.sqr_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (a : AzNat)
    (ha : a.toNat < m.toNat) :
    ((MontCtx.make m k).sqr a).toNat < m.toNat ∧
      (((MontCtx.make m k).sqr a).toNat : ZMod m.toNat) = (a.toNat : ZMod m.toNat) * a.toNat
        * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)⁻¹ := by
  have ht : (square a).toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne) := by
    rw [toNat_square, pow_two]; exact MontCtx.mul_lt m k ha ha
  refine ⟨(MontCtx.redc_spec m k hm _ ht).1, ?_⟩
  show (((MontCtx.make m k).redc (square a)).toNat : ZMod m.toNat) = _
  rw [MontCtx.redc_cast m k hm _ ht, toNat_square, pow_two, Nat.cast_mul]

/-- `toMont a = a R` in `ZMod m`, and it is reduced. -/
theorem MontCtx.toMont_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (a : AzNat)
    (ha : a.toNat < m.toNat) :
    ((MontCtx.make m k).toMont a).toNat < m.toNat ∧
      (((MontCtx.make m k).toMont a).toNat : ZMod m.toNat)
        = (a.toNat : ZMod m.toNat) * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat) := by
  have hr : (MontCtx.make m k).r2.toNat < m.toNat := by
    rw [MontCtx.r2_make_toNat]; exact Nat.mod_lt _ (by omega)
  have ht : (a * (MontCtx.make m k).r2).toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne) := by
    rw [toNat_mul]; exact MontCtx.mul_lt m k ha hr
  refine ⟨(MontCtx.redc_spec m k hm _ ht).1, ?_⟩
  show (((MontCtx.make m k).redc (a * (MontCtx.make m k).r2)).toNat : ZMod m.toNat) = _
  rw [MontCtx.redc_cast m k hm _ ht, toNat_mul, Nat.cast_mul, MontCtx.r2_make_toNat,
    ZMod.natCast_mod, show 128 * (MontCtx.make m k).ne
      = 64 * (MontCtx.make m k).ne + 64 * (MontCtx.make m k).ne by ring, pow_add, Nat.cast_mul,
    mul_assoc, mul_assoc, MontCtx.pow_mul_inv m k hm, mul_one]

/-- `fromMont a = a R⁻¹` in `ZMod m`, and it is reduced. -/
theorem MontCtx.fromMont_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) (a : AzNat)
    (ha : a.toNat < m.toNat) :
    ((MontCtx.make m k).fromMont a).toNat < m.toNat ∧
      (((MontCtx.make m k).fromMont a).toNat : ZMod m.toNat)
        = (a.toNat : ZMod m.toNat) * ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat)⁻¹ := by
  have ht : a.toNat < m.toNat * 2 ^ (64 * (MontCtx.make m k).ne) :=
    lt_of_lt_of_le ha (Nat.le_mul_of_pos_right _ (by positivity))
  exact ⟨(MontCtx.redc_spec m k hm _ ht).1, MontCtx.redc_cast m k hm _ ht⟩

/-- `one = R` in `ZMod m`, and it is reduced (for `m ≠ 0`). -/
theorem MontCtx.one_spec (m : AzNat) (k : ℕ) (hm : Odd m.toNat) :
    (MontCtx.make m k).one.toNat < m.toNat ∧
      ((MontCtx.make m k).one.toNat : ZMod m.toNat)
        = ((2 ^ (64 * (MontCtx.make m k).ne) : ℕ) : ZMod m.toNat) := by
  rw [MontCtx.one_make_toNat]
  exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro h; rw [h] at hm; simp at hm)),
    ZMod.natCast_mod _ _⟩

end Azurite.AzNat
