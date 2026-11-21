/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PolygammaWidth

/-!
# Enclosures of level-dependent numbers with geometrically small widths

The enclosure calculus `AEncl`/`LEncl` (`Equiv/EnclWidth.lean`) keeps explicit widths; for a
bracket whose intermediate values grow with the Ziv level `w` (a shifted argument `x + N(w)`,
a product of `N(w)` factors) the bookkeeping is the whole proof.  Here it is done once:

* `GS f`: **geometrically small** — `|f w| ≤ P(w) ρ^w` eventually, `P` polynomially bounded
  (`PB`), `ρ < 1`.  Closed under sums, products with a `PB` sequence, and tending to `0`
  (`GS.tendsto`); `GS.geom` (`r^(e w)` with `w ≤ c · e w`), `GS.half_pow`.
* `AW a v`: the enclosures `a w` of the polynomially bounded numbers `v w` have geometrically
  small widths; `LW a v`: the same for relative widths; `TW a v`: widths that only tend to
  `0`.
* The operations at a working precision `V w ≥ w + 64`: `AW.add`, `AW.sub`, `AW.half`,
  `AW.mulPosClamp`, `LW.mul`, `LW.div`, `LW.ln`, the conversions `LW.toAW`, `AW.toLW`,
  `AW.toTW`, and `TW.add`, `TW.sub`.
-/

namespace Azurite.AzFloat

open Filter Topology

/-! ### Geometrically small sequences -/

/-- `|f w| ≤ P(w) ρ^w` eventually, with `P` polynomially bounded and `ρ < 1`. -/
def GS (f : ℕ → ℝ) : Prop :=
  ∃ (P : ℕ → ℝ) (ρ : ℝ), PB P ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ᶠ w in atTop, |f w| ≤ P w * ρ ^ w

theorem PB.abs {f : ℕ → ℝ} (hf : PB f) : PB fun w => |f w| :=
  hf.of_abs_le fun w => by rw [abs_abs]

theorem PB.neg {f : ℕ → ℝ} (hf : PB f) : PB fun w => -f w :=
  hf.of_abs_le fun w => by rw [abs_neg]

theorem PB.sub {f g : ℕ → ℝ} (hf : PB f) (hg : PB g) : PB fun w => f w - g w := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem GS.of_le {f g : ℕ → ℝ} (hf : GS f) (h : ∀ᶠ w in atTop, |g w| ≤ |f w|) : GS g := by
  obtain ⟨P, ρ, hP, h0, h1, hev⟩ := hf
  exact ⟨P, ρ, hP, h0, h1, by filter_upwards [hev, h] with w a b using b.trans a⟩

theorem GS.zero : GS fun _ => 0 :=
  ⟨fun _ => 0, 0, PB.const 0, le_rfl, by norm_num, Eventually.of_forall fun w => by simp⟩

theorem GS.add {f g : ℕ → ℝ} (hf : GS f) (hg : GS g) : GS fun w => f w + g w := by
  obtain ⟨P, ρ, hP, h0, h1, hev⟩ := hf
  obtain ⟨Q, σ, hQ, k0, k1, kev⟩ := hg
  refine ⟨fun w => |P w| + |Q w|, max ρ σ, hP.abs.add hQ.abs, le_max_of_le_left h0,
    max_lt h1 k1, ?_⟩
  filter_upwards [hev, kev] with w a b
  have hm0 : 0 ≤ max ρ σ := le_max_of_le_left h0
  have e1 : P w * ρ ^ w ≤ |P w| * max ρ σ ^ w :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h0 w)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (le_max_left _ _) w) (abs_nonneg _))
  have e2 : Q w * σ ^ w ≤ |Q w| * max ρ σ ^ w :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg k0 w)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ k0 (le_max_right _ _) w) (abs_nonneg _))
  calc |f w + g w| ≤ |f w| + |g w| := abs_add_le _ _
    _ ≤ |P w| * max ρ σ ^ w + |Q w| * max ρ σ ^ w := by linarith
    _ = _ := by ring

theorem GS.mul_pb {f g : ℕ → ℝ} (hf : GS f) (hg : PB g) : GS fun w => f w * g w := by
  obtain ⟨P, ρ, hP, h0, h1, hev⟩ := hf
  refine ⟨fun w => |P w| * |g w|, ρ, hP.abs.mul hg.abs, h0, h1, ?_⟩
  filter_upwards [hev] with w a
  rw [abs_mul]
  calc |f w| * |g w| ≤ P w * ρ ^ w * |g w| := mul_le_mul_of_nonneg_right a (abs_nonneg _)
    _ ≤ |P w| * ρ ^ w * |g w| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h0 w)) (abs_nonneg _)
    _ = _ := by ring

theorem GS.pb_mul {f g : ℕ → ℝ} (hg : PB g) (hf : GS f) : GS fun w => g w * f w := by
  simpa [mul_comm] using hf.mul_pb hg

theorem GS.const_mul {f : ℕ → ℝ} (hf : GS f) (c : ℝ) : GS fun w => c * f w :=
  GS.pb_mul (PB.const c) hf

/-- A polynomially bounded sequence times `ρ^w`, `ρ < 1`, tends to `0`. -/
theorem PB.tendsto_mul_pow {P : ℕ → ℝ} (hP : PB P) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Tendsto (fun w : ℕ => P w * ρ ^ w) atTop (𝓝 0) := by
  obtain ⟨C, k, hC⟩ := hP
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    simpa using this
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (by rwa [abs_of_nonneg h0] : |ρ| < 1)).const_mul (C * 2 ^ k)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with w hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpow : ((w : ℝ) + 1) ^ k ≤ 2 ^ k * (w : ℝ) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 w)]
  calc |P w| * ρ ^ w ≤ C * ((w : ℝ) + 1) ^ k * ρ ^ w :=
        mul_le_mul_of_nonneg_right (hC w) (pow_nonneg h0 w)
    _ ≤ C * (2 ^ k * (w : ℝ) ^ k) * ρ ^ w :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) (pow_nonneg h0 w)
    _ = C * 2 ^ k * ((w : ℝ) ^ k * ρ ^ w) := by ring

theorem GS.tendsto {f : ℕ → ℝ} (hf : GS f) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨P, ρ, hP, h0, h1, hev⟩ := hf
  refine squeeze_zero_norm' ?_ (hP.tendsto_mul_pow h0 h1)
  filter_upwards [hev] with w a
  rwa [Real.norm_eq_abs]

theorem GS.eventually_le {f : ℕ → ℝ} (hf : GS f) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ w in atTop, |f w| ≤ c := by
  have h := hf.tendsto.abs
  rw [abs_zero] at h
  exact h.eventually (ge_mem_nhds hc)

/-- `r^(e w)` is geometrically small when `w ≤ c · e w`. -/
theorem GS.geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {c : ℕ} (hc : 1 ≤ c) {e : ℕ → ℕ}
    (he : ∀ᶠ w in atTop, w ≤ c * e w) : GS fun w => r ^ e w := by
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  refine ⟨fun _ => 1, r ^ (1 / (c : ℝ)), PB.const 1, Real.rpow_nonneg hr0 _,
    Real.rpow_lt_one hr0 hr1 (by positivity), ?_⟩
  have hρc : (r ^ (1 / (c : ℝ))) ^ c = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, one_div, inv_mul_cancel₀ hcpos.ne',
      Real.rpow_one]
  filter_upwards [he] with w hw
  rw [one_mul, abs_of_nonneg (pow_nonneg hr0 _)]
  calc r ^ e w = (r ^ (1 / (c : ℝ))) ^ (c * e w) := by rw [pow_mul, hρc]
    _ ≤ (r ^ (1 / (c : ℝ))) ^ w :=
        pow_le_pow_of_le_one (Real.rpow_nonneg hr0 _)
          (Real.rpow_lt_one hr0 hr1 (by positivity)).le hw

theorem GS.half_pow {V : ℕ → ℕ} (hV : ∀ w, w + 64 ≤ V w) : GS fun w => (1 / 2 : ℝ) ^ V w :=
  GS.geom (by norm_num) (by norm_num) le_rfl
    (Eventually.of_forall fun w => by have := hV w; omega)

/-! ### Enclosures with small widths -/

/-- The enclosures `a w` of the polynomially bounded `v w` have geometrically small widths. -/
def AW (a : ℕ → Encl) (v : ℕ → ℝ) : Prop :=
  PB v ∧ ∃ ε : ℕ → ℝ, GS ε ∧ ∀ᶠ w in atTop, AEncl (a w) (v w) (ε w)

/-- The enclosures `a w` of `v w > 0` have geometrically small relative widths. -/
def LW (a : ℕ → Encl) (v : ℕ → ℝ) : Prop :=
  ∃ lam : ℕ → ℝ, GS lam ∧ ∀ᶠ w in atTop, 0 ≤ lam w ∧ LEncl (a w) (v w) (lam w)

/-- The enclosures `a w` of the polynomially bounded `v w` have widths tending to `0`. -/
def TW (a : ℕ → Encl) (v : ℕ → ℝ) : Prop :=
  PB v ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, AEncl (a w) (v w) (ε w)

theorem AEncl.width_nonneg {a : Encl} {x ε : ℝ} (h : AEncl a x ε) : 0 ≤ ε := by
  obtain ⟨l, u, -, -, h1, h2, h3⟩ := h
  linarith

variable {a b : ℕ → Encl} {x y : ℕ → ℝ} {V : ℕ → ℕ}

theorem AW.toTW (h : AW a x) : TW a x := by
  obtain ⟨hx, ε, g, e⟩ := h
  exact ⟨hx, ε, g.tendsto, e⟩

theorem AW.exact {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) :
    AW (fun _ => Encl.exact t) fun _ => tv :=
  ⟨PB.const tv, fun _ => 0, GS.zero, Eventually.of_forall fun _ =>
    ⟨tv, tv, ht, ht, le_rfl, le_rfl, by simp⟩⟩

theorem AW.nat {n : ℕ → ℕ} (hn : PB fun w => (n w : ℝ)) :
    AW (fun w => Encl.nat (n w)) fun w => (n w : ℝ) :=
  ⟨hn, fun _ => 0, GS.zero, Eventually.of_forall fun w => AEncl.natEncl (n w)⟩

/-- The width of a rounded sum. -/
theorem gs_sum_width {ε₁ ε₂ B : ℕ → ℝ} (g1 : GS ε₁) (g2 : GS ε₂) (hB : PB B)
    (hV : ∀ w, w + 64 ≤ V w) :
    GS fun w => ε₁ w + ε₂ w + 4 * (B w + 2) * (1 / 2 : ℝ) ^ V w :=
  (g1.add g2).add (GS.pb_mul ((hB.add (PB.const 2)).const_mul 4) (GS.half_pow hV))

theorem AW.add (hV : ∀ w, w + 64 ≤ V w) (ha : AW a x) (hb : AW b y) :
    AW (fun w => Encl.add (V w) (a w) (b w)) fun w => x w + y w := by
  obtain ⟨hx, ε₁, g1, e1⟩ := ha
  obtain ⟨hy, ε₂, g2, e2⟩ := hb
  refine ⟨hx.add hy, _, gs_sum_width g1 g2 (hx.add hy).abs hV, ?_⟩
  filter_upwards [e1, e2, g1.eventually_le one_pos, g2.eventually_le one_pos] with w h1 h2 h3 h4
  have : NeZero (V w) := ⟨by have := hV w; omega⟩
  exact h1.add h2 (by linarith [le_abs_self (ε₁ w), le_abs_self (ε₂ w)])

theorem AW.sub (hV : ∀ w, w + 64 ≤ V w) (ha : AW a x) (hb : AW b y) :
    AW (fun w => Encl.sub (V w) (a w) (b w)) fun w => x w - y w := by
  obtain ⟨hx, ε₁, g1, e1⟩ := ha
  obtain ⟨hy, ε₂, g2, e2⟩ := hb
  refine ⟨hx.sub hy, _, gs_sum_width g1 g2 (hx.sub hy).abs hV, ?_⟩
  filter_upwards [e1, e2, g1.eventually_le one_pos, g2.eventually_le one_pos] with w h1 h2 h3 h4
  have : NeZero (V w) := ⟨by have := hV w; omega⟩
  exact h1.sub h2 (by linarith [le_abs_self (ε₁ w), le_abs_self (ε₂ w)])

theorem AW.half (ha : AW a x) : AW (fun w => Encl.half (a w)) fun w => x w / 2 := by
  obtain ⟨hx, ε, g, e⟩ := ha
  refine ⟨hx.div_const 2, fun w => ε w / 2, ?_, ?_⟩
  · simpa [div_eq_inv_mul] using g.const_mul (1 / 2)
  · filter_upwards [e] with w h using h.half

/-- A product with a nonnegative factor, its lower end clamped at `0`. -/
theorem AW.mulPosClamp (hV : ∀ w, w + 64 ≤ V w) (ha : AW a x) (hb : AW b y)
    (h0 : ∀ᶠ w in atTop, 0 ≤ y w) :
    AW (fun w => Encl.mulPos (V w) (a w) (clampNonneg (b w).1, (b w).2))
      fun w => x w * y w := by
  obtain ⟨hx, ε₁, g1, e1⟩ := ha
  obtain ⟨hy, ε₂, g2, e2⟩ := hb
  refine ⟨hx.mul hy, fun w => ε₁ w * (|y w| + 1) + (|x w| + 1) * ε₂ w
    + 4 * (|x w| + 1) * (|y w| + 1) * (1 / 2 : ℝ) ^ V w, ?_, ?_⟩
  · exact ((g1.mul_pb (hy.abs.add (PB.const 1))).add
      (GS.pb_mul (hx.abs.add (PB.const 1)) g2)).add
      (GS.pb_mul (((hx.abs.add (PB.const 1)).const_mul 4).mul (hy.abs.add (PB.const 1)))
        (GS.half_pow hV))
  · filter_upwards [e1, e2, g1.eventually_le one_pos, g2.eventually_le one_pos, h0] with
      w h1 h2 h3 h4 h5
    have : NeZero (V w) := ⟨by have := hV w; omega⟩
    exact AEncl.mulPos h1 (h2.clamp0 h5)
      (by linarith [le_abs_self (ε₁ w)])
      (by linarith [le_abs_self (ε₂ w), le_abs_self (y w)])

theorem LW.exact {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (h0 : 0 < tv) :
    LW (fun _ => Encl.exact t) fun _ => tv :=
  ⟨fun _ => 0, GS.zero, Eventually.of_forall fun _ => ⟨le_rfl, LEncl.exact ht h0⟩⟩

theorem LW.nat {n : ℕ → ℕ} (hn : ∀ w, 0 < n w) :
    LW (fun w => Encl.nat (n w)) fun w => (n w : ℝ) :=
  ⟨fun _ => 0, GS.zero, Eventually.of_forall fun w => ⟨le_rfl, LEncl.nat (hn w)⟩⟩

theorem LW.pi (hV : ∀ w, w + 64 ≤ V w) : LW (fun w => Encl.pi (V w)) fun _ => Real.pi :=
  ⟨fun w => 3 * (1 / 2 : ℝ) ^ V w, (GS.half_pow hV).const_mul 3, Eventually.of_forall fun w =>
    ⟨by positivity, LEncl.pi (by have := hV w; omega)⟩⟩

theorem LW.mul (hV : ∀ w, w + 64 ≤ V w) (ha : LW a x) (hb : LW b y) :
    LW (fun w => Encl.mul (V w) (a w) (b w)) fun w => x w * y w := by
  obtain ⟨l₁, g1, e1⟩ := ha
  obtain ⟨l₂, g2, e2⟩ := hb
  refine ⟨fun w => l₁ w + l₂ w + 6 * (1 / 2 : ℝ) ^ V w,
    (g1.add g2).add ((GS.half_pow hV).const_mul 6), ?_⟩
  filter_upwards [e1, e2] with w h1 h2
  have : NeZero (V w) := ⟨by have := hV w; omega⟩
  exact ⟨by have := h1.1; have := h2.1; positivity,
    LEncl.mul (half_pow_le_eighth (by have := hV w; omega)) h1.2 h2.2⟩

theorem LW.div (hV : ∀ w, w + 64 ≤ V w) (ha : LW a x) (hb : LW b y) :
    LW (fun w => Encl.div (V w) (a w) (b w)) fun w => x w / y w := by
  obtain ⟨l₁, g1, e1⟩ := ha
  obtain ⟨l₂, g2, e2⟩ := hb
  refine ⟨fun w => l₁ w + l₂ w + 6 * (1 / 2 : ℝ) ^ V w,
    (g1.add g2).add ((GS.half_pow hV).const_mul 6), ?_⟩
  filter_upwards [e1, e2] with w h1 h2
  have : NeZero (V w) := ⟨by have := hV w; omega⟩
  exact ⟨by have := h1.1; have := h2.1; positivity,
    LEncl.div (half_pow_le_eighth (by have := hV w; omega)) h1.2 h2.2⟩

theorem LW.toAW (h : LW a x) (hx : PB x) : AW a x := by
  obtain ⟨lam, g, e⟩ := h
  refine ⟨hx, fun w => 2 * x w * lam w, GS.pb_mul (hx.const_mul 2) g, ?_⟩
  filter_upwards [e, g.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w h1 h2
  exact (h1.2.toA h1.1 ((le_abs_self _).trans h2)).toA

theorem AW.toLW (h : AW a x) (h1 : ∀ᶠ w in atTop, 1 ≤ x w) : LW a x := by
  obtain ⟨-, ε, g, e⟩ := h
  refine ⟨fun w => 2 * ε w / x w, ?_, ?_⟩
  · refine (g.const_mul 2).of_le ?_
    filter_upwards [h1] with w hw
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < x w)]
    exact div_le_self (abs_nonneg _) hw
  · filter_upwards [e, h1, g.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w he hw hs
    have hε0 := he.width_nonneg
    have hε : ε w ≤ 1 / 2 := (le_abs_self _).trans hs
    exact ⟨by positivity, LEncl.ofA he (by linarith) (by linarith)⟩

/-- The logarithm of a relatively narrow enclosure. -/
theorem LW.ln (hV : ∀ w, w + 64 ≤ V w) (hVpb : PB fun w => (V w : ℝ)) (h : LW a x)
    {G : ℕ → ℝ} (hG : PB G) (hlog : ∀ w, |Real.log (x w)| ≤ G w) :
    AW (fun w => lnOfEncl (a w) (V w)) fun w => Real.log (x w) := by
  obtain ⟨lam, g, e⟩ := h
  refine ⟨hG.of_abs_le fun w => (hlog w).trans (le_abs_self _),
    fun w => lnW (G w) (V w) + 5 * lam w, ?_, ?_⟩
  · refine GS.add ?_ (g.const_mul 5)
    unfold lnW
    exact GS.pb_mul ((((hVpb.add (hG.const_mul 2)).add (PB.const 10)).pow 5).const_mul _)
      (GS.half_pow hV)
  · filter_upwards [e, g.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w h1 h2
    exact h1.2.lnOfEncl h1.1 ((le_abs_self _).trans h2) (hlog w) (by have := hV w; omega)

theorem TW.add (hV : ∀ w, w + 64 ≤ V w) (ha : TW a x) (hb : TW b y) :
    TW (fun w => Encl.add (V w) (a w) (b w)) fun w => x w + y w := by
  obtain ⟨hx, ε₁, g1, e1⟩ := ha
  obtain ⟨hy, ε₂, g2, e2⟩ := hb
  refine ⟨hx.add hy, fun w => ε₁ w + ε₂ w + 4 * (|x w + y w| + 2) * (1 / 2 : ℝ) ^ V w, ?_, ?_⟩
  · have := (g1.add g2).add (GS.pb_mul ((((hx.add hy).abs.add (PB.const 2)).const_mul 4))
      (GS.half_pow hV)).tendsto
    simpa using this
  · filter_upwards [e1, e2, g1.eventually (ge_mem_nhds one_pos),
      g2.eventually (ge_mem_nhds one_pos)] with w h1 h2 h3 h4
    have : NeZero (V w) := ⟨by have := hV w; omega⟩
    exact h1.add h2 (by linarith)

theorem TW.sub (hV : ∀ w, w + 64 ≤ V w) (ha : TW a x) (hb : TW b y) :
    TW (fun w => Encl.sub (V w) (a w) (b w)) fun w => x w - y w := by
  obtain ⟨hx, ε₁, g1, e1⟩ := ha
  obtain ⟨hy, ε₂, g2, e2⟩ := hb
  refine ⟨hx.sub hy, fun w => ε₁ w + ε₂ w + 4 * (|x w - y w| + 2) * (1 / 2 : ℝ) ^ V w, ?_, ?_⟩
  · have := (g1.add g2).add (GS.pb_mul ((((hx.sub hy).abs.add (PB.const 2)).const_mul 4))
      (GS.half_pow hV)).tendsto
    simpa using this
  · filter_upwards [e1, e2, g1.eventually (ge_mem_nhds one_pos),
      g2.eventually (ge_mem_nhds one_pos)] with w h1 h2 h3 h4
    have : NeZero (V w) := ⟨by have := hV w; omega⟩
    exact h1.sub h2 (by linarith)

end Azurite.AzFloat
