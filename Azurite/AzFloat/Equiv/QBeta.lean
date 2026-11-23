/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QBeta
import Azurite.AzFloat.Equiv.LnQGamma
import Azurite.AzFloat.Equiv.BetaFloatRat

/-!
# Equivalence: the `q`-beta function

`Spec.qBeta` and the specifications of the six functions of `AzFloat/QBeta.lean`:
**`qBetaPrecRoundFuel_zivSpec`**, **`qBetaFloatFloatRatPrecRoundFuel_zivSpec`**,
**`qBetaFloatRatRatPrecRoundFuel_zivSpec`**, **`qBetaRatFloatFloatPrecRoundFuel_zivSpec`**,
**`qBetaRatFloatRatPrecRoundFuel_zivSpec`**, **`qBetaRatPrecRoundFuel_zivSpec`** — sound at
every fuel, complete in the limit of the fuel wherever the value is no rounding boundary, and
correct at every fuel on the class `QBetaD`: a base that is no positive real, arguments that
are not real, and the poles and zeros (`a`, `b` or `a + b` a non-positive integer).  At the
base `1` the function is `B` with its own specification.

The six are instances of `qBeta_zivSpec_sides`, from the function `qBetaOf` on a base and
arguments given by their data: `qBetaOf_eq_or_loop`, `qBetaOf_main`, `qBetaOf_complete`,
`qBetaOf_special`, and `qBetaOf_exact` (**correct at every fuel at positive integers whose
value is formed**).  The bracket is the exponential of the sum of three enclosures of
`ln |Γ_q|` (`qBetaLnEnclOf_spec`, `qBetaLnEnclOf_conv`), through the generic `lnCoreExp`
(`lnCoreExp_spec`, `lnCoreExp_coreConv`): no new width proof.
-/

namespace Azurite.AzFloat

open Filter Topology Finset DLMF

/-- `B_q(a, b) = Γ_q(a) Γ_q(b) / Γ_q(a + b)` for reals. -/
noncomputable def qBetaReal (q a b : ℝ) : ℝ :=
  qGammaReal q a * qGammaReal q b / qGammaReal q (a + b)

namespace Spec

open Classical in
/-- `B_q` for a real base `q > 0`, `q ≠ 1`, on the extended reals.  Undefined at `−∞` and when
an argument is a negative integer; `B_q(+∞, b) = 0` for `q > 1` and `b > 0`, undefined for
`q < 1` (the limit is not `0` there); `+∞` when an argument is `0`; `0` when `a + b` is a
non-positive integer; otherwise `Γ_q(a) Γ_q(b) / Γ_q(a + b)`. -/
noncomputable def qBetaAt (qv : ℝ) (a b : EReal) : Option EReal :=
  if a = ⊥ ∨ b = ⊥ then none
  else if a = ⊤ then (if 1 < qv ∧ 0 < b then some 0 else none)
  else if b = ⊤ then (if 1 < qv ∧ 0 < a then some 0 else none)
  else if (a.toReal < 0 ∧ ∃ k : ℤ, a.toReal = k) ∨ (b.toReal < 0 ∧ ∃ k : ℤ, b.toReal = k)
  then none
  else if a.toReal = 0 ∨ b.toReal = 0 then some ⊤
  else if a.toReal + b.toReal ≤ 0 ∧ ∃ k : ℤ, a.toReal + b.toReal = k then some 0
  else some ((qBetaReal qv a.toReal b.toReal : ℝ) : EReal)

/-- **`B_q(a, b)` on the extended reals**: undefined for a base `q ≤ 0` or `q = +∞`,
`B(a, b)` at `q = 1`. -/
noncomputable def qBeta (q a b : EReal) : Option EReal :=
  qBaseLift (fun x : EReal × EReal => beta x.1 x.2) (fun qv x => qBetaAt qv x.1 x.2) q (a, b)

theorem qBeta_none {q : EReal} (hq : q ≤ 0 ∨ q = ⊤) (a b : EReal) : qBeta q a b = none :=
  qBaseLift_none hq _

theorem qBeta_one (a b : EReal) : qBeta 1 a b = beta a b := qBaseLift_one _

theorem qBeta_coe {qv : ℝ} (hq0 : 0 < qv) (hq1 : qv ≠ 1) (a b : EReal) :
    qBeta (qv : EReal) a b = qBetaAt qv a b := qBaseLift_coe hq0 hq1 _

theorem qBetaAt_bot_left (qv : ℝ) (b : EReal) : qBetaAt qv ⊥ b = none := by simp [qBetaAt]

theorem qBetaAt_bot_right (qv : ℝ) (a : EReal) : qBetaAt qv a ⊥ = none := by simp [qBetaAt]

theorem qBetaAt_top_coe (qv yv : ℝ) :
    qBetaAt qv ⊤ (yv : EReal) = if 1 < qv ∧ 0 < yv then some 0 else none := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_left rfl]
  simp only [EReal.coe_pos]

theorem qBetaAt_coe_top (qv xv : ℝ) :
    qBetaAt qv (xv : EReal) ⊤ = if 1 < qv ∧ 0 < xv then some 0 else none := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _), ite_eq_left rfl]
  simp only [EReal.coe_pos]

theorem qBetaAt_top_top (qv : ℝ) : qBetaAt qv ⊤ ⊤ = if 1 < qv then some 0 else none := by
  simp [qBetaAt]

theorem qBetaAt_coe_of_pole (qv : ℝ) {xv yv : ℝ}
    (h : (xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)) :
    qBetaAt qv (xv : EReal) (yv : EReal) = none := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_left h]

theorem qBetaAt_coe_of_zero (qv : ℝ) {xv yv : ℝ}
    (hnp : ¬ ((xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)))
    (h0 : xv = 0 ∨ yv = 0) : qBetaAt qv (xv : EReal) (yv : EReal) = some ⊤ := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_right hnp,
    ite_eq_left h0]

theorem qBetaAt_coe_of_sum (qv : ℝ) {xv yv : ℝ}
    (hnp : ¬ ((xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)))
    (h0 : ¬ (xv = 0 ∨ yv = 0)) (hs : xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k) :
    qBetaAt qv (xv : EReal) (yv : EReal) = some 0 := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_right hnp,
    ite_eq_right h0, ite_eq_left hs]

theorem qBetaAt_coe (qv : ℝ) {xv yv : ℝ}
    (hnp : ¬ ((xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)))
    (h0 : ¬ (xv = 0 ∨ yv = 0)) (hs : ¬ (xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k)) :
    qBetaAt qv (xv : EReal) (yv : EReal) = some ((qBetaReal qv xv yv : ℝ) : EReal) := by
  unfold qBetaAt
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_right hnp,
    ite_eq_right h0, ite_eq_right hs]

/-- A real value of `B_q` at arguments that are not both real is `0`. -/
theorem qBetaAt_eq_zero_of_nonreal (qv : ℝ) {x y : EReal}
    (h : ¬ ∃ av bv : ℝ, x = (av : EReal) ∧ y = (bv : EReal)) {v : ℝ}
    (hv : qBetaAt qv x y = some (v : EReal)) : v = 0 := by
  have hzero : ∀ {c : Prop} [Decidable c],
      (if c then some (0 : EReal) else none) = some (v : EReal) → v = 0 := by
    intro c _ hc
    split_ifs at hc
    rw [Option.some.injEq] at hc
    exact_mod_cast hc.symm
  induction x using EReal.rec with
  | bot =>
    rw [qBetaAt_bot_left] at hv
    exact absurd hv (by simp)
  | top =>
    induction y using EReal.rec with
    | bot =>
      rw [qBetaAt_bot_right] at hv
      exact absurd hv (by simp)
    | top =>
      rw [qBetaAt_top_top] at hv
      exact hzero hv
    | coe bv =>
      rw [qBetaAt_top_coe] at hv
      exact hzero hv
  | coe av =>
    induction y using EReal.rec with
    | bot =>
      rw [qBetaAt_bot_right] at hv
      exact absurd hv (by simp)
    | top =>
      rw [qBetaAt_coe_top] at hv
      exact hzero hv
    | coe bv => exact absurd ⟨av, bv, rfl, rfl⟩ h

end Spec

/-! ### The exponential of an enclosure of a logarithm -/

/-- **`lnCoreExp` encloses**: from an enclosure of `ln |v|` with the sign of `v`, the sign and
a positive enclosure of `|v|`. -/
theorem lnCoreExp_spec {l : ℕ → Option (Bool × Encl)} {v : ℝ} {w : ℕ} (hw : 64 ≤ w)
    (hl : ∀ neg L, l w = some (neg, L) → 0 < (if neg then (-1 : ℝ) else 1) * v ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * v)))
    {neg : Bool} {b : Encl} (h : lnCoreExp l w = some (neg, b)) :
    IsEnclPos b ((if neg then (-1 : ℝ) else 1) * v) := by
  unfold lnCoreExp at h
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg', Lg⟩ := c
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp hr
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  obtain ⟨hpos, hL⟩ := hl _ _ hc
  have := gammaExpEncl_spec hL hw hg
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rwa [Real.exp_log hpos] at this

/-- **`lnCoreExp` converges** when the enclosure of the logarithm does. -/
theorem lnCoreExp_coreConv {l : ℕ → Option (Bool × Encl)} {v : ℝ}
    (hl : ∀ w neg L, l w = some (neg, L) → 0 < (if neg then (-1 : ℝ) else 1) * v)
    (hconv : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      l w = some (neg, L) ∧ AEncl L (Real.log |v|) (ε w)) :
    CoreConv (lnCoreExp l) v := by
  obtain ⟨E, hE, hev⟩ := hconv
  obtain ⟨ht, hevE⟩ := gammaExpEncl_eventually false (Real.log |v|) hE
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hevE
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, hevE] with w h1 h2
  obtain ⟨neg, L, hc, hLA⟩ := h1
  have hpos := hl w neg L hc
  have habs := sign_mul_eq_abs hpos
  have hB0 : 0 < |v| := habs ▸ hpos
  obtain ⟨b, hb, hb1, hb2⟩ := h2 L hLA
  rw [Real.exp_log hB0] at hb1 hb2
  refine ⟨neg, b, ?_, ?_, ?_⟩
  · unfold lnCoreExp
    rw [hc]
    simp [hb]
  · rw [habs]; exact hb1
  · rw [habs]; exact hb2

/-! ### The enclosure of `ln |B_q|` -/

/-- **The sign and the enclosure of the logarithm of a quotient `ga gb / gc`**, from those of
its three factors. -/
theorem qBetaLnEnclOf_spec {A B C : QGammaIn} {ga gb gc : ℝ} {w : ℕ}
    (hA : ∀ neg L, qGammaLnEnclOf A w = some (neg, L) →
      0 < (if neg then (-1 : ℝ) else 1) * ga ∧
        IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * ga)))
    (hB : ∀ neg L, qGammaLnEnclOf B w = some (neg, L) →
      0 < (if neg then (-1 : ℝ) else 1) * gb ∧
        IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * gb)))
    (hC : ∀ neg L, qGammaLnEnclOf C w = some (neg, L) →
      0 < (if neg then (-1 : ℝ) else 1) * gc ∧
        IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * gc)))
    {neg : Bool} {L : Encl} (h : qBetaLnEnclOf A B C w = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * (ga * gb / gc) ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * (ga * gb / gc))) := by
  unfold qBetaLnEnclOf at h
  obtain ⟨ra, hra, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rb, hrb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rc, hrc, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨na, La⟩ := ra
  obtain ⟨nb, Lb⟩ := rb
  obtain ⟨nc, Lc⟩ := rc
  rw [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨pa, ea⟩ := hA na La hra
  obtain ⟨pb, eb⟩ := hB nb Lb hrb
  obtain ⟨pc, ec⟩ := hC nc Lc hrc
  have : NeZero (w + 64) := ⟨by omega⟩
  have hs : (if nc then (-1 : ℝ) else 1) * (if nc then (-1 : ℝ) else 1) = 1 := by
    cases nc <;> simp
  have hgc : gc ≠ 0 := by
    rintro rfl
    rw [mul_zero] at pc
    exact lt_irrefl _ pc
  have hinv : gc⁻¹ * gc = 1 := inv_mul_cancel₀ hgc
  have e : (if ((na != nb) != nc) = true then (-1 : ℝ) else 1) * (ga * gb / gc)
      = (if na then (-1 : ℝ) else 1) * ga * ((if nb then (-1 : ℝ) else 1) * gb) /
        ((if nc then (-1 : ℝ) else 1) * gc) := by
    rw [sign_xor, sign_xor, eq_div_iff pc.ne', div_eq_mul_inv]
    linear_combination
      ((if na then (-1 : ℝ) else 1) * (if nb then (-1 : ℝ) else 1) * ga * gb *
        ((if nc then (-1 : ℝ) else 1) * (if nc then (-1 : ℝ) else 1))) * hinv +
      ((if na then (-1 : ℝ) else 1) * (if nb then (-1 : ℝ) else 1) * ga * gb) * hs
  rw [e]
  refine ⟨div_pos (mul_pos pa pb) pc, ?_⟩
  rw [Real.log_div (mul_pos pa pb).ne' pc.ne', Real.log_mul pa.ne' pb.ne']
  exact (ea.add eb).sub ec

/-- **The enclosure of the logarithm of a quotient converges** when those of its three
factors do. -/
theorem qBetaLnEnclOf_conv {A B C : QGammaIn} {la lb lc : ℝ}
    (hA : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qGammaLnEnclOf A w = some (neg, L) ∧ AEncl L la (ε w))
    (hB : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qGammaLnEnclOf B w = some (neg, L) ∧ AEncl L lb (ε w))
    (hC : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qGammaLnEnclOf C w = some (neg, L) ∧ AEncl L lc (ε w)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qBetaLnEnclOf A B C w = some (neg, L) ∧ AEncl L (la + lb - lc) (ε w) := by
  obtain ⟨εa, ha, hevA⟩ := hA
  obtain ⟨εb, hb, hevB⟩ := hB
  obtain ⟨εc, hc, hevC⟩ := hC
  have hu : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 64)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 64)
  have h1 : Tendsto (fun w => εa w + εb w +
      4 * (|la + lb| + (εa w + εb w)) * (1 / 2 : ℝ) ^ (w + 64)) atTop (𝓝 0) := by
    have := (ha.add hb).add ((((ha.add hb).const_add |la + lb|).const_mul 4).mul hu)
    simpa using this
  have h2 : Tendsto (fun w => (εa w + εb w +
        4 * (|la + lb| + (εa w + εb w)) * (1 / 2 : ℝ) ^ (w + 64)) + εc w +
      4 * (|la + lb - lc| + ((εa w + εb w +
        4 * (|la + lb| + (εa w + εb w)) * (1 / 2 : ℝ) ^ (w + 64)) + εc w)) *
        (1 / 2 : ℝ) ^ (w + 64)) atTop (𝓝 0) := by
    have := (h1.add hc).add ((((h1.add hc).const_add |la + lb - lc|).const_mul 4).mul hu)
    simpa using this
  refine ⟨_, h2, ?_⟩
  filter_upwards [hevA, hevB, hevC] with w ⟨na, La, hLa, wa⟩ ⟨nb, Lb, hLb, wb⟩
    ⟨nc, Lc, hLc, wc⟩
  have : NeZero (w + 64) := ⟨by omega⟩
  refine ⟨(na != nb) != nc, Encl.sub (w + 64) (Encl.add (w + 64) La Lb) Lc, ?_, ?_⟩
  · unfold qBetaLnEnclOf
    rw [hLa, hLb, hLc]
    rfl
  · have s1 := (wa.add (w := w + 64) wb (B := |la + lb| + (εa w + εb w))
      (le_of_eq (by ring)))
    exact (s1.sub (w := w + 64) wc
      (B := |la + lb - lc| + ((εa w + εb w +
        4 * (|la + lb| + (εa w + εb w)) * (1 / 2 : ℝ) ^ (w + 64)) + εc w))
      (le_of_eq (by ring))).mono (le_of_eq (by ring))

/-! ### The classes of the arguments -/

variable {Q : QBase} {S Sa Sb Ss : QArg} {qv xv av bv : ℝ}

theorem QArgSpec.isPole_iff (hS : QArgSpec S xv) :
    S.kind.isPole = true ↔ (xv < 0 ∧ ∃ k : ℤ, xv = k) := by
  have hk := hS.kind
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    have h0 : xv = 0 := hk
    exact ⟨fun h => absurd h (by simp [QArgKind.isPole]),
      fun ⟨hlt, _⟩ => absurd hlt (by rw [h0]; exact lt_irrefl 0)⟩
  | pole =>
    rw [hkind] at hk
    obtain ⟨m, hm⟩ := hk
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact ⟨fun _ => ⟨by rw [hm]; linarith, -((m : ℤ) + 1), by rw [hm]; push_cast; ring⟩,
      fun _ => rfl⟩
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨-, hxn⟩ := hk
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ⟨fun h => absurd h (by simp [QArgKind.isPole]),
      fun ⟨hlt, _⟩ => absurd hlt (by rw [hxn]; exact not_lt.mpr hn0)⟩
  | general =>
    rw [hkind] at hk
    exact ⟨fun h => absurd h (by simp [QArgKind.isPole]),
      fun ⟨hlt, hint⟩ => absurd ⟨hlt.le, hint⟩ (not_pole_of_ne_neg_nat hk)⟩

theorem QArgSpec.isZero_iff (hS : QArgSpec S xv) : S.kind.isZero = true ↔ xv = 0 := by
  have hk := hS.kind
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    exact ⟨fun _ => hk, fun _ => rfl⟩
  | pole =>
    rw [hkind] at hk
    obtain ⟨m, hm⟩ := hk
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact ⟨fun h => absurd h (by simp [QArgKind.isZero]), fun h0 => by
      rw [hm] at h0
      linarith⟩
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨hn1, hxn⟩ := hk
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    exact ⟨fun h => absurd h (by simp [QArgKind.isZero]), fun h0 => by
      rw [hxn] at h0
      linarith⟩
  | general =>
    rw [hkind] at hk
    exact ⟨fun h => absurd h (by simp [QArgKind.isZero]), fun h0 =>
      absurd (by rw [h0]; simp) (hk 0)⟩

/-- A non-positive integer is a `−m`. -/
theorem nonpos_int_iff_neg_nat {s : ℝ} : (s ≤ 0 ∧ ∃ k : ℤ, s = k) ↔ ∃ m : ℕ, s = -m := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact not_pole_of_ne_neg_nat hc h
  · rintro ⟨m, rfl⟩
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact ⟨by linarith, -(m : ℤ), by push_cast; rfl⟩

theorem QArgSpec.neg_nat_iff (hS : QArgSpec S xv) :
    (S.kind.isZero || S.kind.isPole) = true ↔ ∃ m : ℕ, xv = -m := by
  rw [Bool.or_eq_true, hS.isZero_iff, hS.isPole_iff, ← nonpos_int_iff_neg_nat]
  constructor
  · rintro (h0 | ⟨hlt, hint⟩)
    · exact ⟨h0.le, 0, by rw [h0]; simp⟩
    · exact ⟨hlt.le, hint⟩
  · rintro ⟨hle, hint⟩
    rcases hle.eq_or_lt with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr ⟨hlt, hint⟩

/-- **What the argument of the sum says of `a + b`**: the enclosures, and the classes `zero`
and `pole` exactly at the non-positive integers. -/
structure QSumSpec (S : QArg) (sv : ℝ) : Prop where
  X : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl (S.X V) sv (C * (1 / 2 : ℝ) ^ V)
  absX : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl0 (S.absX V) |sv| (C * (1 / 2 : ℝ) ^ V)
  kind : (S.kind.isZero || S.kind.isPole) = true ↔ ∃ m : ℕ, sv = -m

theorem QArgSpec.sumSpec (hS : QArgSpec S xv) : QSumSpec S xv :=
  ⟨hS.X, hS.absX, hS.neg_nat_iff⟩

/-- The input of the bracket of `Γ_q` at the sum. -/
theorem qGammaArg_of_sum (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hS : QSumSpec S xv) :
    QGammaArg (qGammaInOf Q S) (if Q.inv then qv⁻¹ else qv) xv :=
  ⟨(qGammaArg_of hQ hSa).p_pos, (qGammaArg_of hQ hSa).p_lt, hQ.P, hS.X, hS.absX⟩

/-- The enclosure of the bracket of `Γ_q` in terms of `Γ_q(x)`, from the input. -/
theorem qGammaLnEnclOf_real_spec' (hQ : QBaseSpec Q qv)
    (hA : QGammaArg (qGammaInOf Q S) (if Q.inv then qv⁻¹ else qv) xv) {w : ℕ} {neg : Bool}
    {L : Encl} (hc : qGammaLnEnclOf (qGammaInOf Q S) w = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * qGammaReal qv xv ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * qGammaReal qv xv)) := by
  have := qGammaLnEnclOf_spec hA hc
  rwa [qGammaVal_of hQ] at this

theorem qGammaLnEnclOf_real_conv (hQ : QBaseSpec Q qv)
    (hA : QGammaArg (qGammaInOf Q S) (if Q.inv then qv⁻¹ else qv) xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qGammaLnEnclOf (qGammaInOf Q S) w = some (neg, L) ∧
        AEncl L (Real.log |qGammaReal qv xv|) (ε w) := by
  have := qGammaLnEnclOf_conv hA hnz
  rwa [qGammaVal_of hQ] at this

/-- `Γ_q(x) ≠ 0` off the poles. -/
theorem qGammaReal_ne_zero_of (hQ : QBaseSpec Q qv)
    (hA : QGammaArg (qGammaInOf Q S) (if Q.inv then qv⁻¹ else qv) xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) : qGammaReal qv xv ≠ 0 := by
  obtain ⟨ε, -, hev⟩ := qGammaLnEnclOf_real_conv hQ hA hnz
  obtain ⟨w, neg, L, hc, -⟩ := hev.exists
  have hpos := (qGammaLnEnclOf_real_spec' hQ hA hc).1
  intro h0
  rw [h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### `B_q` on a base and arguments -/

theorem qBetaExact?_eq_some {ka kb : QArgKind} {p : ℕ} {r : AzRat}
    (h : qBetaExact? Q ka kb p = some r) :
    ∃ m n ra rb rc, ka = .posInt m ∧ kb = .posInt n ∧ qGammaExact? Q m p = some ra ∧
      qGammaExact? Q n p = some rb ∧ qGammaExact? Q (m + n) p = some rc ∧
      r = ra * rb / rc := by
  unfold qBetaExact? at h
  split at h
  · next m n =>
    obtain ⟨ra, hra, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, hrb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rc, hrc, heq⟩ := Option.map_eq_some_iff.mp h
    exact ⟨m, n, ra, rb, rc, rfl, rfl, hra, hrb, hrc, heq.symm⟩
  · exact absurd h (by simp)

/-- The exact value is `B_q(m, n)`. -/
theorem qBetaExact?_spec (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    {p : ℕ} {r : AzRat} (h : qBetaExact? Q Sa.kind Sb.kind p = some r) :
    ((AzRat.toRat r : ℚ) : ℝ) = qBetaReal qv av bv := by
  obtain ⟨m, n, ra, rb, rc, hka, hkb, hra, hrb, hrc, rfl⟩ := qBetaExact?_eq_some h
  have hA := hSa.kind
  rw [hka] at hA
  obtain ⟨hm1, ham⟩ := hA
  have hB := hSb.kind
  rw [hkb] at hB
  obtain ⟨hn1, hbn⟩ := hB
  have e1 := qGammaExact?_spec hQ hm1 hra
  have e2 := qGammaExact?_spec hQ hn1 hrb
  have e3 := qGammaExact?_spec hQ (by omega : 1 ≤ m + n) hrc
  rw [AzRat.toRat_div, AzRat.toRat_mul]
  push_cast
  rw [e1, e2, e3, ham, hbn, qBetaReal, Nat.cast_add]

/-- An exact value formed at precision `0` is formed at every precision. -/
theorem qBetaExact?_isSome_mono {ka kb : QArgKind}
    (h : (qBetaExact? Q ka kb 0).isSome = true) (p : ℕ) :
    (qBetaExact? Q ka kb p).isSome = true := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨m, n, ra, rb, rc, rfl, rfl, hra, hrb, hrc, -⟩ := qBetaExact?_eq_some hr
  obtain ⟨ra', hra'⟩ := Option.isSome_iff_exists.mp
    (qGammaExact?_isSome_mono (by rw [hra]; rfl) p)
  obtain ⟨rb', hrb'⟩ := Option.isSome_iff_exists.mp
    (qGammaExact?_isSome_mono (by rw [hrb]; rfl) p)
  obtain ⟨rc', hrc'⟩ := Option.isSome_iff_exists.mp
    (qGammaExact?_isSome_mono (by rw [hrc]; rfl) p)
  simp [qBetaExact?, hra', hrb', hrc']

/-- The value of `B_q` off the poles and the zeros. -/
theorem qBetaAt_general (qv : ℝ) {av bv : ℝ} (hnza : ∀ m : ℕ, av ≠ -m)
    (hnzb : ∀ m : ℕ, bv ≠ -m) (hnzs : ∀ m : ℕ, av + bv ≠ -m) :
    Spec.qBetaAt qv (av : EReal) (bv : EReal) = some ((qBetaReal qv av bv : ℝ) : EReal) := by
  have hpa := not_pole_of_ne_neg_nat hnza
  have hpb := not_pole_of_ne_neg_nat hnzb
  refine Spec.qBetaAt_coe qv ?_ ?_ (not_pole_of_ne_neg_nat hnzs)
  · rintro (⟨h, hi⟩ | ⟨h, hi⟩)
    · exact hpa ⟨h.le, hi⟩
    · exact hpb ⟨h.le, hi⟩
  · rintro (h | h)
    · exact hnza 0 (by rw [h]; simp)
    · exact hnzb 0 (by rw [h]; simp)

/-- **`B_q` on a base and arguments is correctly rounded, or it is the loop** off the poles
and the zeros. -/
theorem qBetaOf_eq_or_loop (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaOf Q Sa Sb Ss fuel p mode
        = roundVal p mode (Spec.qBetaAt qv (av : EReal) (bv : EReal)) ∨
      ((∀ m : ℕ, av ≠ -m) ∧ (∀ m : ℕ, bv ≠ -m) ∧ (∀ m : ℕ, av + bv ≠ -m) ∧
        qBetaExact? Q Sa.kind Sb.kind p = none ∧
        qBetaOf Q Sa Sb Ss fuel p mode
          = zivLoop (qBetaApproxOf Q Sa Sb Ss) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold qBetaOf
  by_cases hpole : (Sa.kind.isPole || Sb.kind.isPole) = true
  · left
    rw [ite_eq_left hpole]
    rw [Bool.or_eq_true, hSa.isPole_iff, hSb.isPole_iff] at hpole
    rw [Spec.qBetaAt_coe_of_pole qv hpole, roundVal_none]
  · rw [ite_eq_right hpole]
    have hnp : ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) := by
      rw [Bool.or_eq_true, hSa.isPole_iff, hSb.isPole_iff] at hpole
      exact hpole
    by_cases hzero : (Sa.kind.isZero || Sb.kind.isZero) = true
    · left
      rw [ite_eq_left hzero]
      rw [Bool.or_eq_true, hSa.isZero_iff, hSb.isZero_iff] at hzero
      rw [Spec.qBetaAt_coe_of_zero qv hnp hzero, roundVal_top]
    · rw [ite_eq_right hzero, ite_eq_right hp]
      have hz : ¬ (av = 0 ∨ bv = 0) := by
        rw [Bool.or_eq_true, hSa.isZero_iff, hSb.isZero_iff] at hzero
        exact hzero
      by_cases hsum : (Ss.kind.isZero || Ss.kind.isPole) = true
      · left
        rw [ite_eq_left hsum, Spec.qBetaAt_coe_of_sum qv hnp hz
          (nonpos_int_iff_neg_nat.mpr (hSs.kind.mp hsum)), roundVal_zero]
      · rw [ite_eq_right hsum]
        have hnza : ∀ m : ℕ, av ≠ -m :=
          ne_neg_nat_of_not_pole (fun h => hz (Or.inl h)) (fun h => hnp (Or.inl h))
        have hnzb : ∀ m : ℕ, bv ≠ -m :=
          ne_neg_nat_of_not_pole (fun h => hz (Or.inr h)) (fun h => hnp (Or.inr h))
        have hnzs : ∀ m : ℕ, av + bv ≠ -m := fun m h => hsum (hSs.kind.mpr ⟨m, h⟩)
        cases hex : qBetaExact? Q Sa.kind Sb.kind p with
        | none => exact Or.inr ⟨hnza, hnzb, hnzs, rfl, rfl⟩
        | some r =>
          left
          dsimp only
          rw [ofAzRatRound_eq_roundVal, qBetaAt_general qv hnza hnzb hnzs,
            qBetaExact?_spec hQ hSa hSb hex]

/-- The bracket of `B_q(a, b)` is valid, or rejected. -/
theorem qBetaApprox_valid_or_none (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) {w : ℕ} (hw : 64 ≤ w) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (qBetaApproxOf Q Sa Sb Ss w).1 lv ∧
        Rounds (qBetaApproxOf Q Sa Sb Ss w).2 hv ∧
        lv ≤ qBetaReal qv av bv ∧ qBetaReal qv av bv ≤ hv ∧
        (lv = qBetaReal qv av bv → hv = qBetaReal qv av bv)) ∨
      roundingPossible (qBetaApproxOf Q Sa Sb Ss w).1 (qBetaApproxOf Q Sa Sb Ss w).2 p mode
        = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => lnCoreExp_spec hw (fun _ _ hl =>
    qBetaLnEnclOf_spec
      (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of hQ hSa) h)
      (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of hQ hSb) h)
      (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of_sum hQ hSa hSs) h) hl) hc)
    w p mode

/-- **Correctly rounded or `NaN`, at every fuel.** -/
theorem qBetaOf_main (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaOf Q Sa Sb Ss fuel p mode
        = roundVal p mode (Spec.qBetaAt qv (av : EReal) (bv : EReal)) ∨
      qBetaOf Q Sa Sb Ss fuel p mode = (nan, .eq) := by
  rcases qBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨hnza, hnzb, hnzs, -, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (qBetaOf Q Sa Sb Ss fuel p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      rw [h] at hz ⊢
      rw [qBetaAt_general qv hnza hnzb hnzs]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => qBetaApprox_valid_or_none hQ hSa hSb hSs hw p mode) _ _
        (le_max_left _ _) hz

/-- **Correctly rounded for every large enough fuel**, wherever the value is no rounding
boundary. -/
theorem qBetaOf_complete (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → qBetaOf Q Sa Sb Ss fuel p mode
      = roundVal p mode (Spec.qBetaAt qv (av : EReal) (bv : EReal)) := by
  by_cases hg : (∀ m : ℕ, av ≠ -m) ∧ (∀ m : ℕ, bv ≠ -m) ∧ ∀ m : ℕ, av + bv ≠ -m
  · obtain ⟨hnza, hnzb, hnzs⟩ := hg
    have hB' := hB _ (qBetaAt_general qv hnza hnzb hnzs)
    have hAa := qGammaArg_of hQ hSa
    have hAb := qGammaArg_of hQ hSb
    have hAs := qGammaArg_of_sum hQ hSa hSs
    have ga0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAa hnza)
    have gb0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAb hnzb)
    have gs0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAs hnzs)
    have hlog : Real.log |qGammaReal qv av| + Real.log |qGammaReal qv bv|
        - Real.log |qGammaReal qv (av + bv)| = Real.log |qBetaReal qv av bv| := by
      unfold qBetaReal
      rw [abs_div, abs_mul, Real.log_div (mul_ne_zero ga0 gb0) gs0, Real.log_mul ga0 gb0]
    have hc := qBetaLnEnclOf_conv (qGammaLnEnclOf_real_conv hQ hAa hnza)
      (qGammaLnEnclOf_real_conv hQ hAb hnzb) (qGammaLnEnclOf_real_conv hQ hAs hnzs)
    rw [hlog] at hc
    have hconv : CoreConv (lnCoreExp (qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb)
        (qGammaInOf Q Ss))) (qBetaReal qv av bv) :=
      lnCoreExp_coreConv (fun w _ _ hl => (qBetaLnEnclOf_spec
        (fun _ _ h => qGammaLnEnclOf_real_spec' hQ hAa h)
        (fun _ _ h => qGammaLnEnclOf_real_spec' hQ hAb h)
        (fun _ _ h => qGammaLnEnclOf_real_spec' hQ hAs h) hl).1) hc
    obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (qBetaApproxOf Q Sa Sb Ss)
      (gammaApproxOf_bracketConv hconv) (ne_zero_of_not_mem_floatSet hB') hB'
      (max 64 (p + 32)) (by omega)
      (fun w hw =>
        (qBetaApprox_valid_or_none hQ hSa hSb hSs (le_trans (le_max_left _ _) hw) p
          mode).imp_left fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
    refine ⟨F, fun fuel hfuel => ?_⟩
    rcases qBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨-, -, -, -, h⟩
    · exact h
    · rw [h, qBetaAt_general qv hnza hnzb hnzs]
      exact hF fuel hfuel
  · refine ⟨0, fun fuel _ => ?_⟩
    rcases qBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨h1, h2, h3, -, -⟩
    · exact h
    · exact absurd ⟨h1, h2, h3⟩ hg

/-- **At the poles and the zeros the result is correctly rounded at every fuel.** -/
theorem qBetaOf_special (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv))
    (hsp : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ ∃ m : ℕ, av + bv = -m) (fuel p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    qBetaOf Q Sa Sb Ss fuel p mode
      = roundVal p mode (Spec.qBetaAt qv (av : EReal) (bv : EReal)) := by
  rcases qBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨ha, hb, hs, -, -⟩
  · exact h
  · rcases hsp with ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩
    · exact absurd h (ha m)
    · exact absurd h (hb m)
    · exact absurd h (hs m)

/-- **At positive integers whose value is formed the result is correctly rounded at every
fuel**, in every base. -/
theorem qBetaOf_exact (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (hE : (qBetaExact? Q Sa.kind Sb.kind 0).isSome = true)
    (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaOf Q Sa Sb Ss fuel p mode
      = roundVal p mode (Spec.qBetaAt qv (av : EReal) (bv : EReal)) := by
  rcases qBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨-, -, -, hn, -⟩
  · exact h
  · have := qBetaExact?_isSome_mono hE p
    rw [hn] at this
    exact absurd this (by simp)

/-- At the poles and the zeros the real values are `0`. -/
theorem qBetaAt_special_dyadic (qv : ℝ) {av bv : ℝ}
    (hsp : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ ∃ m : ℕ, av + bv = -m) {v : ℝ}
    (hv : Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal)) : IsDyadic v := by
  by_cases hnp : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
  · rw [Spec.qBetaAt_coe_of_pole qv hnp] at hv
    exact absurd hv (by simp)
  · by_cases hz : av = 0 ∨ bv = 0
    · rw [Spec.qBetaAt_coe_of_zero qv hnp hz] at hv
      exact absurd hv (by simp)
    · by_cases hs : av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k
      · rw [Spec.qBetaAt_coe_of_sum qv hnp hz hs, Option.some.injEq] at hv
        have h0 : v = 0 := by exact_mod_cast hv.symm
        rw [h0]
        exact isDyadic_zero
      · exfalso
        rcases hsp with ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩
        · exact ne_neg_nat_of_not_pole (fun h0 => hz (Or.inl h0))
            (fun hc => hnp (Or.inl hc)) m h
        · exact ne_neg_nat_of_not_pole (fun h0 => hz (Or.inr h0))
            (fun hc => hnp (Or.inr hc)) m h
        · exact hs (nonpos_int_iff_neg_nat.mpr ⟨m, h⟩)

/-! ### The specification, generically -/

/-- **The class where `B_q` is exact, with dyadic values**: a base that is no positive real;
or a base `q > 0`, `q ≠ 1`, with arguments that are not both real, or with `a`, `b` or `a + b`
a non-positive integer. -/
def QBetaD {α : Type*} (qe xe ye : α → Option EReal) (a : α) : Prop :=
  (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
    ((∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1) ∧
      ∀ av bv : ℝ, xe a = some (av : EReal) → ye a = some (bv : EReal) →
        (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ ∃ m : ℕ, av + bv = -m)

theorem bind_bind_const_none {β γ δ : Type*} (o : Option β) (o' : Option γ) :
    (o.bind fun _ => o'.bind fun _ => (none : Option δ)) = none := by
  cases o <;> cases o' <;> rfl

open Classical in
/-- **The specification of a function that is `B_q`** on a base and two arguments with values
`qe`, `xe`, `ye` in the extended reals: `NaN` on a base that is no positive real, the function
`fΓ` (a function that is `B`) at the base `1`, the special values at arguments that are not
both real, and `qBetaOf` elsewhere. -/
theorem qBeta_zivSpec_sides {α : Type*} {qe xe ye : α → Option EReal}
    {f fΓ : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (Q : α → QBase)
    (Sa Sb Ss : α → QArg)
    (hbase : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 → QBaseSpec (Q a) qv)
    (harg : ∀ a (av bv : ℝ), xe a = some (av : EReal) → ye a = some (bv : EReal) →
      QArgSpec (Sa a) av ∧ QArgSpec (Sb a) bv ∧ QSumSpec (Ss a) (av + bv))
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode
          = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.beta x y) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, ((xe a).bind fun x => (ye a).bind fun y => Spec.beta x y) = some (v : EReal) →
        ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → fΓ fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.beta x y))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      f fuel a p mode = qBetaOf (Q a) (Sa a) (Sb a) (Ss a) fuel p mode)
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 →
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) →
      f fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.qBetaAt qv x y)) :
    ZivSpec
      (fun a => (qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y => Spec.qBeta q x y)
      f {a | QBetaD qe xe ye a} ∅ := by
  have hval_bad : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y => Spec.qBeta q x y)
        = none := by
    intro a hb
    cases hq : qe a with
    | none => rfl
    | some e =>
      rw [Option.bind_some]
      have hn : e ≤ 0 ∨ e = ⊤ := by
        induction e using EReal.rec with
        | bot => exact Or.inl bot_le
        | top => exact Or.inr rfl
        | coe r => exact Or.inl (by exact_mod_cast hb r hq)
      simp only [Spec.qBeta_none hn]
      exact bind_bind_const_none _ _
  have hval_one : ∀ a, qe a = some ((1 : ℝ) : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y => Spec.qBeta q x y)
        = (xe a).bind fun x => (ye a).bind fun y => Spec.beta x y := by
    intro a hq
    rw [hq, Option.bind_some]
    simp only [EReal.coe_one, Spec.qBeta_one]
  have hval_pos : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y => Spec.qBeta q x y)
        = (xe a).bind fun x => (ye a).bind fun y => Spec.qBetaAt qv x y := by
    intro a qv hq h0 h1
    rw [hq, Option.bind_some]
    simp only [Spec.qBeta_coe h0 h1]
  have hval_real : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y => Spec.qBeta q x y)
        = Spec.qBetaAt qv (av : EReal) (bv : EReal) := by
    intro a qv av bv hq h0 h1 hx hy
    rw [hval_pos a qv hq h0 h1, hx, hy, Option.bind_some, Option.bind_some]
  have hnr : ∀ a (qv : ℝ),
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) → ∀ v : ℝ,
      ((xe a).bind fun x => (ye a).bind fun y => Spec.qBetaAt qv x y) = some (v : EReal) →
      v = 0 := by
    intro a qv hR v hv
    cases hxe : xe a with
    | none =>
      rw [hxe] at hv
      exact absurd hv (by simp)
    | some x =>
      cases hye : ye a with
      | none =>
        rw [hxe, hye] at hv
        exact absurd hv (by simp)
      | some y =>
        rw [hxe, hye, Option.bind_some, Option.bind_some] at hv
        exact Spec.qBetaAt_eq_zero_of_nonreal qv
          (fun ⟨av, bv, h1, h2⟩ => hR ⟨av, bv, by rw [hxe, h1], by rw [hye, h2]⟩) hv
  have hcases : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
      qe a = some ((1 : ℝ) : EReal) ∨
      ∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1 ∧
        ((∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) ∨
          ¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) := by
    intro a
    by_cases hb : ∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0
    · exact Or.inl hb
    · push Not at hb
      obtain ⟨qv, hq, h0⟩ := hb
      by_cases h1 : qv = 1
      · exact Or.inr (Or.inl (h1 ▸ hq))
      · exact Or.inr (Or.inr ⟨qv, hq, h0, h1, Classical.em _⟩)
  refine ⟨fun fuel a p _ mode => ?_, fun a p _ mode hB => ?_, fun a ha v hv => ?_,
    fun a ha => absurd ha (Set.notMem_empty _), fun a ha fuel p _ mode => ?_⟩
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨av, bv, hx, hy⟩ | hx⟩
    · left
      rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · rw [hf_one fuel a p mode h1, hval_one a h1]
      exact hΓs fuel a p mode
    · rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy, hval_real a qv av bv hq h0 h1 hx hy]
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      exact qBetaOf_main (hbase a qv hq h0 h1) hSa hSb hSs fuel p mode
    · left
      rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨av, bv, hx, hy⟩ | hx⟩
    · exact ⟨0, fun fuel _ => by rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]⟩
    · rw [hval_one a h1] at hB ⊢
      obtain ⟨F, hF⟩ := hΓc a p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf_one fuel a p mode h1]; exact hF fuel hfuel⟩
    · rw [hval_real a qv av bv hq h0 h1 hx hy] at hB ⊢
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      obtain ⟨F, hF⟩ := qBetaOf_complete (hbase a qv hq h0 h1) hSa hSb hSs p mode hB
      exact ⟨F, fun fuel hfuel => by
        rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => by
        rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]⟩
  · rcases ha with hb | ⟨⟨qv, hq, h0, h1⟩, hsp⟩
    · rw [hval_bad a hb] at hv
      exact absurd hv (by simp)
    · by_cases hR : ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)
      · obtain ⟨av, bv, hx, hy⟩ := hR
        rw [hval_real a qv av bv hq h0 h1 hx hy] at hv
        exact qBetaAt_special_dyadic qv (hsp av bv hx hy) hv
      · rw [hval_pos a qv hq h0 h1] at hv
        rw [hnr a qv hR v hv]
        exact isDyadic_zero
  · rcases ha with (hb | ⟨⟨qv, hq, h0, h1⟩, hsp⟩) | hN
    · rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · by_cases hR : ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)
      · obtain ⟨av, bv, hx, hy⟩ := hR
        rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy,
          hval_real a qv av bv hq h0 h1 hx hy]
        obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
        exact qBetaOf_special (hbase a qv hq h0 h1) hSa hSb hSs (hsp av bv hx hy) fuel p mode
      · rw [hf_nonreal fuel a p mode qv hq h0 h1 hR, hval_pos a qv hq h0 h1]
    · exact absurd hN (Set.notMem_empty _)

/-! ### The arguments -/

theorem toVal_neg_coe {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) :
    (-a).toVal = some ((-av : ℝ) : EReal) := by
  rw [toVal_neg, ha, Option.map_some, EReal.coe_neg]

/-- The sum of two floats as an argument. -/
theorem qArgSumFloat_spec {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) : QSumSpec (qArgSumFloat a b) (av + bv) where
  X := ⟨0 + 0 + 4 * (|av + bv| + |(0 : ℝ)| + |(0 : ℝ)|), fun V hV => by
    have : NeZero V := ⟨by omega⟩
    exact (AEncl.exact_level ha V).add_level (AEncl.exact_level hb V)⟩
  absX := by
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 0 + 0 + 4 * (|av + bv| + |(0 : ℝ)| + |(0 : ℝ)|) := ⟨_, rfl⟩
    refine ⟨C, fun V hV => ?_⟩
    have : NeZero V := ⟨by omega⟩
    have hs : AEncl (Encl.add V (Encl.exact a) (Encl.exact b)) (av + bv)
        (C * (1 / 2 : ℝ) ^ V) := by
      rw [hC]
      exact (AEncl.exact_level ha V).add_level (AEncl.exact_level hb V)
    show AEncl0 (if le (-a) b = true then _ else _) _ _
    by_cases hle : le (-a) b = true
    · rw [ite_eq_left hle]
      have h0 : 0 ≤ av + bv := by
        have := (le_eq_true_iff (toVal_neg_coe ha) hb).mp hle
        linarith
      rw [abs_of_nonneg h0]
      exact hs.clamp0 h0
    · rw [ite_eq_right hle]
      have h0 : av + bv < 0 := by
        have := mt (le_eq_true_iff (toVal_neg_coe ha) hb).mpr hle
        linarith
      rw [abs_of_neg h0]
      exact hs.neg.clamp0 (by linarith)
  kind := by
    show ((if sumIsNonposInt a b = true then QArgKind.zero else QArgKind.general).isZero ||
      (if sumIsNonposInt a b = true then QArgKind.zero else QArgKind.general).isPole) = true
        ↔ _
    rw [← nonpos_int_iff_neg_nat, ← sumIsNonposInt_iff ha hb]
    by_cases h : sumIsNonposInt a b = true
    · rw [ite_eq_left h]
      simp [QArgKind.isZero, h]
    · rw [ite_eq_right h]
      simp [QArgKind.isZero, QArgKind.isPole, h]

theorem qBetaFloatArgs_eq_of (Q : QBase) (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ)
    (mode : RoundingMode) :
    qBetaFloatArgs Q fuel a b p mode
      = qBetaOf Q (qArgFloat a) (qArgFloat b) (qArgSumFloat a b) fuel p mode := by
  cases a with
  | nan => simp at ha
  | infinity s => cases s <;> simp at ha
  | zero =>
    cases b with
    | nan => simp at hb
    | infinity s => cases s <;> simp at hb
    | zero => rfl
    | finite s e pr m hv => rfl
  | finite s e pr m hv =>
    cases b with
    | nan => simp at hb
    | infinity s => cases s <;> simp at hb
    | zero => rfl
    | finite s e pr m hv => rfl

theorem qBetaInfinite_eq (hQ : QBaseSpec Q qv) {y : AzFloat} {yv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaInfinite Q.inv y
      = roundVal p mode (if 1 < qv ∧ 0 < yv then some (0 : EReal) else none) := by
  unfold qBetaInfinite
  by_cases h : 1 < qv ∧ 0 < yv
  · rw [ite_eq_left h, ite_eq_left (by
      rw [Bool.and_eq_true]
      exact ⟨hQ.inv.mpr h.1, (lt_eq_true_iff toVal_zero' hy).mpr h.2⟩), roundVal_zero]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (by
      rw [Bool.and_eq_true] at hc
      exact ⟨hQ.inv.mp hc.1, (lt_eq_true_iff toVal_zero' hy).mp hc.2⟩)), roundVal_none]

/-- `B_q` at two floats that are not both real. -/
theorem qBetaFloatArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a b : AzFloat)
    (h : ¬ ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    qBetaFloatArgs Q fuel a b p mode
      = roundVal p mode (a.toVal.bind fun x => b.toVal.bind fun y => Spec.qBetaAt qv x y) := by
  have htt : lt zero (infinity true) = true := by decide
  have htf : lt zero (infinity false) = false := by decide
  rcases exists_real_or_not a with ⟨av, ha⟩ | rfl | rfl | rfl
  · rw [ha, Option.bind_some]
    rcases exists_real_or_not b with ⟨bv, hb⟩ | rfl | rfl | rfl
    · exact absurd ⟨av, bv, ha, hb⟩ h
    · have e : qBetaFloatArgs Q fuel a nan p mode = (nan, .eq) := by
        cases a <;> rfl
      rw [e]
      rfl
    · have e : qBetaFloatArgs Q fuel a (infinity true) p mode = qBetaInfinite Q.inv a := by
        cases a with
        | nan => simp at ha
        | infinity s => cases s <;> simp at ha
        | zero => rfl
        | finite s e pr m hv => rfl
      rw [e, qBetaInfinite_eq hQ ha p mode]
      show _ = roundVal p mode (Spec.qBetaAt qv (av : EReal) ⊤)
      rw [Spec.qBetaAt_coe_top]
    · have e : qBetaFloatArgs Q fuel a (infinity false) p mode = (nan, .eq) := by
        cases a with
        | nan => rfl
        | infinity s => cases s <;> simp at ha
        | zero => rfl
        | finite s e pr m hv => rfl
      rw [e]
      show _ = roundVal p mode (Spec.qBetaAt qv (av : EReal) ⊥)
      rw [Spec.qBetaAt_bot_right, roundVal_none]
  · cases b <;> rfl
  · rcases exists_real_or_not b with ⟨bv, hb⟩ | rfl | rfl | rfl
    · have e : qBetaFloatArgs Q fuel (infinity true) b p mode = qBetaInfinite Q.inv b := by
        cases b with
        | nan => simp at hb
        | infinity s => rfl
        | zero => rfl
        | finite s e pr m hv => rfl
      rw [e, qBetaInfinite_eq hQ hb p mode, hb]
      show _ = roundVal p mode (Spec.qBetaAt qv ⊤ (bv : EReal))
      rw [Spec.qBetaAt_top_coe]
    · rfl
    · show qBetaInfinite Q.inv (infinity true) = roundVal p mode (Spec.qBetaAt qv ⊤ ⊤)
      unfold qBetaInfinite
      rw [Spec.qBetaAt_top_top, htt, Bool.and_true]
      by_cases h1 : 1 < qv
      · rw [ite_eq_left h1, ite_eq_left (hQ.inv.mpr h1), roundVal_zero]
      · rw [ite_eq_right h1, ite_eq_right (mt hQ.inv.mp h1), roundVal_none]
    · show qBetaInfinite Q.inv (infinity false) = roundVal p mode (Spec.qBetaAt qv ⊤ ⊥)
      unfold qBetaInfinite
      rw [Spec.qBetaAt_bot_right, htf, Bool.and_false]
      rfl
  · have hv : ((infinity false).toVal.bind fun x => b.toVal.bind fun y =>
        Spec.qBetaAt qv x y) = none := by
      show (b.toVal.bind fun y => Spec.qBetaAt qv ⊥ y) = none
      simp only [Spec.qBetaAt_bot_left]
      exact bind_const_none _
    rw [hv, roundVal_none]
    cases b <;> rfl

theorem qBetaMixedArgs_eq_of (Q : QBase) (fuel : ℕ) {a : AzFloat} {r : AzRat}
    (hr : a.toAzRat? = some r) (b : AzRat) (p : ℕ) (mode : RoundingMode) :
    qBetaMixedArgs Q fuel a b p mode
      = qBetaOf Q (qArgRat r) (qArgRat b) (qArgRat (r + b)) fuel p mode := by
  unfold qBetaMixedArgs
  rw [hr]
  rfl

/-- `B_q` at a float that is not real and a rational. -/
theorem qBetaMixedArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a : AzFloat) (b : AzRat)
    (h : ∀ av : ℝ, a.toVal ≠ some (av : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaMixedArgs Q fuel a b p mode = roundVal p mode
      (a.toVal.bind fun x => Spec.qBetaAt qv x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) := by
  rcases exists_real_or_not a with ⟨av, ha⟩ | rfl | rfl | rfl
  · exact absurd ha (h av)
  · rfl
  · show (if (Q.inv && ratIsPos b) = true then (zero, Ordering.eq) else (nan, .eq))
      = roundVal p mode (Spec.qBetaAt qv ⊤ (((AzRat.toRat b : ℚ) : ℝ) : EReal))
    rw [Spec.qBetaAt_top_coe]
    by_cases hc : 1 < qv ∧ 0 < ((AzRat.toRat b : ℚ) : ℝ)
    · rw [ite_eq_left hc, ite_eq_left (by
        rw [Bool.and_eq_true]
        exact ⟨hQ.inv.mpr hc.1, (ratIsPos_iff b).mpr hc.2⟩), roundVal_zero]
    · rw [ite_eq_right hc, ite_eq_right (fun hd => hc (by
        rw [Bool.and_eq_true] at hd
        exact ⟨hQ.inv.mp hd.1, (ratIsPos_iff b).mp hd.2⟩)), roundVal_none]
  · show (nan, Ordering.eq)
      = roundVal p mode (Spec.qBetaAt qv ⊥ (((AzRat.toRat b : ℚ) : ℝ) : EReal))
    rw [Spec.qBetaAt_bot_left, roundVal_none]

/-- The arguments of the mixed function: the float as a rational. -/
theorem qBetaMixed_arg {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (b : AzRat) :
    QArgSpec (qArgRat (a.toAzRat?.getD 0)) av ∧
      QArgSpec (qArgRat b) ((AzRat.toRat b : ℚ) : ℝ) ∧
      QSumSpec (qArgRat (a.toAzRat?.getD 0 + b)) (av + ((AzRat.toRat b : ℚ) : ℝ)) := by
  obtain ⟨r, hr, hrv⟩ := exists_toAzRat? ha
  rw [hr, Option.getD_some]
  refine ⟨by rw [← hrv]; exact qArgRat_spec r, qArgRat_spec b, ?_⟩
  have hs := (qArgRat_spec (r + b)).sumSpec
  rw [AzRat.toRat_add] at hs
  push_cast at hs
  rw [hrv] at hs
  exact hs

theorem qBetaRat_arg (a b : AzRat) :
    QArgSpec (qArgRat a) ((AzRat.toRat a : ℚ) : ℝ) ∧
      QArgSpec (qArgRat b) ((AzRat.toRat b : ℚ) : ℝ) ∧
      QSumSpec (qArgRat (a + b)) (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) := by
  refine ⟨qArgRat_spec a, qArgRat_spec b, ?_⟩
  have hs := (qArgRat_spec (a + b)).sumSpec
  rw [AzRat.toRat_add] at hs
  push_cast at hs
  exact hs

/-! ### The bases -/

theorem floatBaseSel_bad {β : Type*} {q : AzFloat}
    (hb : ∀ qv : ℝ, q.toVal = some (qv : EReal) → qv ≤ 0) (x y z : β) :
    (if (q.isFinite && lt zero q) = true then
      (if (le q one && le one q) = true then x else y) else z) = z := by
  rw [qFloatBase_bad hb]
  rfl

theorem floatBaseSel_one {β : Type*} {q : AzFloat} (hq : q.toVal = some ((1 : ℝ) : EReal))
    (x y z : β) :
    (if (q.isFinite && lt zero q) = true then
      (if (le q one && le one q) = true then x else y) else z) = x := by
  rw [qFloatBase_pos hq one_pos, (qFloatBase_one_iff hq).mpr rfl]
  rfl

theorem floatBaseSel_real {β : Type*} {q : AzFloat} {qv : ℝ} (hq : q.toVal = some (qv : EReal))
    (h0 : 0 < qv) (h1 : qv ≠ 1) (x y z : β) :
    (if (q.isFinite && lt zero q) = true then
      (if (le q one && le one q) = true then x else y) else z) = y := by
  have hne : (le q one && le one q) = false := by
    rw [← Bool.not_eq_true]
    exact mt (qFloatBase_one_iff hq).mp h1
  rw [qFloatBase_pos hq h0, hne]
  rfl

theorem ratBaseSel_bad {β : Type*} {q : AzRat} (hb : ((AzRat.toRat q : ℚ) : ℝ) ≤ 0)
    (x y z : β) :
    (if q.sign = true ∧ q.num ≠ 0 then (if q.num = q.den then x else y) else z) = z := by
  rw [ite_eq_right (fun hc => by linarith [(qRatBase_pos_iff q).mp hc])]

theorem ratBaseSel_one {β : Type*} {q : AzRat} (h1 : ((AzRat.toRat q : ℚ) : ℝ) = 1)
    (x y z : β) :
    (if q.sign = true ∧ q.num ≠ 0 then (if q.num = q.den then x else y) else z) = x := by
  have hpos := (qRatBase_pos_iff q).mpr (by rw [h1]; exact one_pos)
  rw [ite_eq_left hpos, ite_eq_left ((qRatBase_one_iff q hpos.1).mpr h1)]

theorem ratBaseSel_real {β : Type*} {q : AzRat} (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) (x y z : β) :
    (if q.sign = true ∧ q.num ≠ 0 then (if q.num = q.den then x else y) else z) = y := by
  have hpos := (qRatBase_pos_iff q).mpr h0
  have hne : ¬ q.num = q.den := fun hc => h1 ((qRatBase_one_iff q hpos.1).mp hc)
  rw [ite_eq_left hpos, ite_eq_right hne]

theorem coe_eq_of_some_eq {x y : ℝ} (h : some (x : EReal) = some (y : EReal)) : x = y := by
  rwa [Option.some.injEq, EReal.coe_eq_coe_iff] at h

/-! ### The six specifications -/

/-- **The specification of `B_q(a, b)` for floats** (`ZivSpec`): sound at every fuel; complete
in the limit of the fuel wherever the value is no rounding boundary; and correct at every fuel
on the class `QBetaD` (a base that is no positive real, arguments that are not both real, and
`a`, `b` or `a + b` a non-positive integer). -/
theorem qBetaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y =>
          Spec.qBeta q x y)
      (fun fuel a p mode => qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzFloat × AzFloat × AzFloat => a.1.toVal)
        (fun a => a.2.1.toVal)
        (fun a => a.2.2.toVal) a} ∅ :=
  qBeta_zivSpec_sides (α := AzFloat × AzFloat × AzFloat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => betaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaFloatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact qBetaFloatArgs_eq_of _ fuel hx hy p mode)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaFloatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact qBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode)

/-- **The specification of `B_q(a, b)` for a float `q`, a float `a` and a rational `b`.** -/
theorem qBetaFloatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzRat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x =>
          Spec.qBeta q x (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzFloat × AzFloat × AzRat => a.1.toVal)
        (fun a => a.2.1.toVal)
        (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal)) a} ∅ :=
  qBeta_zivSpec_sides (α := AzFloat × AzFloat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => betaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaMixedArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      obtain ⟨r, hr, -⟩ := exists_toAzRat? hx
      rw [qBetaMixedArgs_eq_of _ fuel hr, hr]
      rfl)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaMixedArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact qBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2 (fun av h => hx ⟨av, _, h, rfl⟩) p mode)

/-- **The specification of `B_q(a, b)` for a float `q` and rationals `a`, `b`.** -/
theorem qBetaFloatRatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat × AzRat =>
        a.1.toVal.bind fun q =>
          Spec.qBeta q (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal)
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzFloat × AzRat × AzRat => a.1.toVal)
        (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
        (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal)) a} ∅ :=
  qBeta_zivSpec_sides (α := AzFloat × AzRat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => betaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaRatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      rfl)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show qBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaRatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-- **The specification of `B_q(a, b)` for a rational `q` and floats `a`, `b`.** -/
theorem qBetaRatFloatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzFloat =>
        a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y =>
          Spec.qBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x y)
      (fun fuel a p mode => qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzRat × AzFloat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
        (fun a => a.2.1.toVal)
        (fun a => a.2.2.toVal) a} ∅ :=
  qBeta_zivSpec_sides (α := AzRat × AzFloat × AzFloat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => betaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaFloatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact qBetaFloatArgs_eq_of _ fuel hx hy p mode)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      show qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaFloatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact qBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode)

/-- **The specification of `B_q(a, b)` for a rational `q`, a float `a` and a rational `b`.** -/
theorem qBetaRatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzRat =>
        a.2.1.toVal.bind fun x =>
          Spec.qBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzRat × AzFloat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
        (fun a => a.2.1.toVal)
        (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal)) a} ∅ :=
  qBeta_zivSpec_sides (α := AzRat × AzFloat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => betaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaMixedArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      obtain ⟨r, hr, -⟩ := exists_toAzRat? hx
      rw [qBetaMixedArgs_eq_of _ fuel hr, hr]
      rfl)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      show qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaMixedArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact qBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2 (fun av h => hx ⟨av, _, h, rfl⟩) p mode)

/-- **The specification of `B_q(a, b)` for rationals `q`, `a`, `b`.** -/
theorem qBetaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat × AzRat =>
        Spec.qBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal)
          (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBetaD (fun a : AzRat × AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
        (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
        (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal)) a} ∅ :=
  qBeta_zivSpec_sides (α := AzRat × AzRat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => betaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => betaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => betaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaRatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      rfl)
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      show qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      rw [show qBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = qBetaRatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-! ### At the default fuel -/

/-- **`B_q(a, b)` for floats is correctly rounded, or the fuel ran out.** -/
theorem qBetaPrecRound_eq_or (q a b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.qBeta qe x y) ∨
      qBetaPrecRound q a b p mode = (nan, .eq) :=
  qBetaPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem qBetaFloatFloatRatPrecRound_eq_or (q a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qBetaFloatFloatRatPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x =>
          Spec.qBeta qe x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      qBetaFloatFloatRatPrecRound q a b p mode = (nan, .eq) :=
  qBetaFloatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem qBetaFloatRatRatPrecRound_eq_or (q : AzFloat) (a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qBetaFloatRatRatPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe => Spec.qBeta qe (((AzRat.toRat a : ℚ) : ℝ) : EReal)
          (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      qBetaFloatRatRatPrecRound q a b p mode = (nan, .eq) :=
  qBetaFloatRatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem qBetaRatFloatFloatPrecRound_eq_or (q : AzRat) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qBetaRatFloatFloatPrecRound q a b p mode = roundVal p mode
        (a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.qBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x y) ∨
      qBetaRatFloatFloatPrecRound q a b p mode = (nan, .eq) :=
  qBetaRatFloatFloatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem qBetaRatFloatRatPrecRound_eq_or (q : AzRat) (a : AzFloat) (b : AzRat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    qBetaRatFloatRatPrecRound q a b p mode = roundVal p mode
        (a.toVal.bind fun x => Spec.qBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x
          (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      qBetaRatFloatRatPrecRound q a b p mode = (nan, .eq) :=
  qBetaRatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem qBetaRatPrecRound_eq_or (q a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qBetaRatPrecRound q a b p mode = roundVal p mode
        (Spec.qBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) (((AzRat.toRat a : ℚ) : ℝ) : EReal)
          (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      qBetaRatPrecRound q a b p mode = (nan, .eq) :=
  qBetaRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

end Azurite.AzFloat
