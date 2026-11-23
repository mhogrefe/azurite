/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.BarnesGBracket
import Azurite.AzFloat.Equiv.EnclGeom

/-!
# The bracket of the Barnes `G`-function converges

`barnesGCoreOf_coreConv`: at an argument `x` (`BarnesArg`) that is no zero of `G`, the core
answers at every large level with a positive enclosure of `± G(x)` whose width tends to `0`.
The widths are kept by the calculus of `Equiv/EnclGeom.lean` (`AW`, `LW`, `TW`); the three
pieces with their own arguments are the products (`barnesProdLo_lencl`), Stirling's series
(`barnesStirling_aw`, from `lnGammaStirlingEncl_width'`) and the alternating sum
(`barnesSum_aw`, from `altSumLoop_width`).
-/

namespace Azurite.AzFloat

open Finset Filter Topology DLMF
open scoped Nat

/-! ### The products -/

/-- The distance of a real number off the zeros of `G` to them. -/
theorem exists_pos_le_abs_add {xv : ℝ} (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ j : ℕ, d ≤ |xv + j| := by
  by_cases hint : ∃ z : ℤ, xv = z
  · obtain ⟨z, rfl⟩ := hint
    refine ⟨1, one_pos, le_rfl, fun j => ?_⟩
    have hne : z + (j : ℤ) ≠ 0 := fun h => hnz j (by
      have : (z : ℝ) + j = 0 := by exact_mod_cast h
      linarith)
    have : (1 : ℤ) ≤ |z + (j : ℤ)| := Int.one_le_abs hne
    exact_mod_cast this
  · have hpos : 0 < |xv - round xv| := abs_pos.mpr fun h => hint ⟨round xv, by linarith⟩
    refine ⟨min 1 |xv - round xv|, lt_min one_pos hpos, min_le_left _ _, fun j => ?_⟩
    have := round_le xv (-(j : ℤ))
    push_cast at this
    rw [sub_neg_eq_add] at this
    exact (min_le_right _ _).trans this

/-- `|ln t| ≤ t + 1/t`. -/
theorem abs_log_le_add_inv {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 1 / t := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht)
  rw [one_div, Real.log_inv] at h2
  have h3 : 0 < 1 / t := one_div_pos.mpr ht
  rw [abs_le]
  constructor <;> linarith [one_div t]

/-- The size of the logarithm of the product. -/
theorem abs_log_barnesProd_le {xv d : ℝ} (hd0 : 0 < d) (hd : ∀ j : ℕ, d ≤ |xv + j|) (N : ℕ) :
    |Real.log (∏ j ∈ range N, |xv + j| ^ (j + 1))|
      ≤ (N : ℝ) ^ 2 * (|xv| + N + 1 / d) := by
  have hpos : ∀ j : ℕ, 0 < |xv + j| := fun j => lt_of_lt_of_le hd0 (hd j)
  rw [Real.log_prod (fun j _ => (pow_pos (hpos j) _).ne')]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB0 : 0 ≤ |xv| + N + 1 / d := by positivity
  calc ∑ j ∈ range N, |Real.log (|xv + j| ^ (j + 1))|
      ≤ ∑ _j ∈ range N, (N : ℝ) * (|xv| + N + 1 / d) := by
        refine sum_le_sum fun j hj => ?_
        have hjN : j + 1 ≤ N := mem_range.mp hj
        have hjN' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hjN
        rw [Real.log_pow, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have h1 := abs_log_le_add_inv (hpos j)
        have h2 : |xv + j| ≤ |xv| + N := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
          have : (j : ℝ) ≤ N := by exact_mod_cast (by omega : j ≤ N)
          linarith
        have h3 : 1 / |xv + j| ≤ 1 / d := one_div_le_one_div_of_le hd0 (hd j)
        exact mul_le_mul hjN' (by linarith) (abs_nonneg _) hN0
    _ = (N : ℝ) ^ 2 * (|xv| + N + 1 / d) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-! ### The levels -/

/-- The shift at level `w`. -/
def bgN (A : BarnesIn) (w : ℕ) : ℕ := A.shift (glaisherArg w)

/-- The working precision at level `w`. -/
def bgV (A : BarnesIn) (w : ℕ) : ℕ :=
  w + 3 * max A.eb ((bgN A w + glaisherArg w + 3).log2 + 1) + 64

theorem bgV_ge (A : BarnesIn) (w : ℕ) : w + 64 ≤ bgV A w := by
  unfold bgV
  omega

theorem pb_glaisherTerms : PB fun w : ℕ => ((glaisherTerms w : ℕ) : ℝ) := by
  refine (PB.natCast.add (PB.const 3)).of_abs_le fun w => ?_
  have h : glaisherTerms w ≤ w + 3 := by unfold glaisherTerms; omega
  have h' : ((glaisherTerms w : ℕ) : ℝ) ≤ (w : ℝ) + 3 := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

theorem pb_bgN {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    PB fun w : ℕ => ((bgN A w : ℕ) : ℝ) := by
  obtain ⟨C, hC⟩ := hA.shift_le
  refine (pb_glaisherArg.add (PB.const |C|)).of_abs_le fun w => ?_
  have h := hC (glaisherArg w)
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h.trans (by linarith [le_abs_self C])

theorem pb_bgV {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    PB fun w : ℕ => ((bgV A w : ℕ) : ℝ) := by
  refine ((PB.natCast.add (((PB.const (A.eb : ℝ)).add
    (((pb_bgN hA).add pb_glaisherArg).add (PB.const 4))).const_mul 3)).add
    (PB.const 64)).of_abs_le fun w => ?_
  have h1 := log2_le_self (bgN A w + glaisherArg w + 3)
  have h : bgV A w ≤ w + 3 * (A.eb + (bgN A w + glaisherArg w + 4)) + 64 := by
    unfold bgV
    have := max_le_add_of_nonneg (Nat.zero_le A.eb)
      (Nat.zero_le ((bgN A w + glaisherArg w + 3).log2 + 1))
    omega
  have h' : ((bgV A w : ℕ) : ℝ) ≤ (w : ℝ) + 3 * ((A.eb : ℝ)
      + ((bgN A w : ℝ) + glaisherArg w + 4)) + 64 := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

/-- The argument at level `w`: an enclosure of geometrically small width. -/
theorem bgX_aw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    AW (fun w => A.X (bgV A w)) fun _ => xv :=
  ⟨PB.const xv, fun w => (1 / 2 : ℝ) ^ bgV A w, GS.half_pow (bgV_ge A),
    Eventually.of_forall fun w => hA.encl _ (by have := bgV_ge A w; omega)⟩

/-- The shifted argument at level `w` is beyond `8 j + 1`. -/
theorem bgY_gt {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) (w : ℕ) :
    8 * (glaisherTerms w : ℝ) + 1 < xv + bgN A w := by
  have := hA.shift_gt (glaisherArg w)
  unfold bgN
  have e : ((glaisherArg w : ℕ) : ℝ) = 8 * (glaisherTerms w : ℝ) := by
    unfold glaisherArg
    push_cast
    ring
  rw [e] at this
  exact this

theorem glaisherTerms_ge (w : ℕ) : 3 ≤ glaisherTerms w := by
  unfold glaisherTerms
  omega

theorem bgY_aw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    AW (fun w => Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))
      fun w => xv + bgN A w :=
  AW.add (bgV_ge A) (bgX_aw hA) (AW.nat (pb_bgN hA))

theorem bgY_lw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    LW (fun w => Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))
      fun w => xv + bgN A w :=
  (bgY_aw hA).toLW (Eventually.of_forall fun w => by
    have := bgY_gt hA w
    have h3 : (3 : ℝ) ≤ glaisherTerms w := by exact_mod_cast glaisherTerms_ge w
    linarith)

/-! ### Stirling's series -/

/-- `max` of two geometrically small sequences. -/
theorem GS.max {f g : ℕ → ℝ} (hf : GS f) (hg : GS g) : GS fun w => max (f w) (g w) := by
  obtain ⟨P, ρ, hP, h0, h1, hev⟩ := hf
  obtain ⟨Q, σ, hQ, k0, k1, kev⟩ := hg
  refine ⟨fun w => |P w| + |Q w|, Max.max ρ σ, hP.abs.add hQ.abs, le_max_of_le_left h0,
    max_lt h1 k1, ?_⟩
  filter_upwards [hev, kev] with w a b
  have e1 : P w * ρ ^ w ≤ |P w| * Max.max ρ σ ^ w :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h0 w)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (le_max_left _ _) w) (abs_nonneg _))
  have e2 : Q w * σ ^ w ≤ |Q w| * Max.max ρ σ ^ w :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg k0 w)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ k0 (le_max_right _ _) w) (abs_nonneg _))
  have : |Max.max (f w) (g w)| ≤ |f w| + |g w| := by
    rcases max_cases (f w) (g w) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      linarith [abs_nonneg (f w), abs_nonneg (g w)]
  calc |Max.max (f w) (g w)| ≤ |f w| + |g w| := this
    _ ≤ |P w| * Max.max ρ σ ^ w + |Q w| * Max.max ρ σ ^ w := by linarith
    _ = _ := by ring

/-- The size of `ln Γ(Y) − ½ ln (2π)`. -/
theorem abs_logGamma_sub_le {Y : ℝ} (hY : 1 ≤ Y) :
    |Real.log (Real.Gamma Y) - 1 / 2 * Real.log (2 * Real.pi)| ≤ Y ^ 2 + Y + 1 := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨h1, h2⟩ := DLMF.stirlingMu_bounds hY0
  unfold DLMF.stirlingMu at h1 h2
  have hl0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hl1 : Real.log Y ≤ Y - 1 := Real.log_le_sub_one_of_pos hY0
  have h3 : 1 / (12 * Y) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have h4 : (Y - 1 / 2) * Real.log Y ≤ (Y - 1 / 2) * (Y - 1) :=
    mul_le_mul_of_nonneg_left hl1 (by linarith)
  have h5 : 0 ≤ (Y - 1 / 2) * Real.log Y := mul_nonneg (by linarith) hl0
  rw [abs_le]
  constructor <;> nlinarith

/-- **Stirling's series at the shifted argument**, level by level. -/
theorem barnesStirling_aw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    AW (fun w => lnGammaStirlingEncl (bgV A w) (glaisherTerms w + 1)
        (Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))
        (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)))
      fun w => Real.log (Real.Gamma (xv + bgN A w)) - 1 / 2 * Real.log (2 * Real.pi) := by
  obtain ⟨lam, g, e⟩ := bgY_lw hA
  have hY1 : ∀ w, 1 ≤ xv + bgN A w := fun w => by
    have := bgY_gt hA w
    have h3 : (3 : ℝ) ≤ glaisherTerms w := by exact_mod_cast glaisherTerms_ge w
    linarith
  have pbY : PB fun w : ℕ => xv + bgN A w := (PB.const xv).add (pb_bgN hA)
  have pbB : PB fun w : ℕ => xv + bgN A w + 2 := pbY.add (PB.const 2)
  have pbM : PB fun w : ℕ => ((glaisherTerms w + 1 : ℕ) : ℝ) := by
    simpa using pb_glaisherTerms.add (PB.const 1)
  have gu : GS fun w => (1 / 2 : ℝ) ^ bgV A w := GS.half_pow (bgV_ge A)
  have g1 : GS fun w => (xv + bgN A w + 2) * lam w := GS.pb_mul pbB g
  have g2 : GS fun w => (xv + bgN A w + 2) ^ 2 * (1 / 2 : ℝ) ^ bgV A w :=
    GS.pb_mul (pbB.pow 2) gu
  have gl12 : GS fun w => lam w + 12 * (1 / 2 : ℝ) ^ bgV A w := g.add (gu.const_mul 12)
  have g3 : GS fun w => 2 * ((glaisherTerms w + 1 : ℕ) : ℝ)
      * (lam w + 12 * (1 / 2 : ℝ) ^ bgV A w) := GS.pb_mul (pbM.const_mul 2) gl12
  have glnW : GS fun w => lnW (xv + bgN A w + 2) (bgV A w) + 5 * lam w := by
    refine GS.add ?_ (g.const_mul 5)
    unfold lnW
    exact GS.pb_mul (((((pb_bgV hA).add (pbB.const_mul 2)).add (PB.const 10)).pow 5).const_mul _)
      gu
  have gtol : GS fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16) :=
    GS.geom (by norm_num) (by norm_num) le_rfl (Eventually.of_forall fun w => by omega)
  have g910 : GS fun w : ℕ => 2 * (9 / 10 : ℝ) ^ (2 * (glaisherTerms w + 1) - 1) :=
    (GS.geom (by norm_num) (by norm_num) (c := 6) (by norm_num)
      (Eventually.of_forall fun w => by unfold glaisherTerms; omega)).const_mul 2
  have gμ : GS fun w => ((glaisherTerms w + 1 : ℕ) : ℝ)
        * (2 * (2 * ((glaisherTerms w + 1 : ℕ) : ℝ) * (lam w + 12 * (1 / 2 : ℝ) ^ bgV A w))
          + 4 * (xv + bgN A w + 2) * (1 / 2 : ℝ) ^ bgV A w)
      + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * (glaisherTerms w + 1) - 1))
      + 2 * (xv + bgN A w + 2) * (1 / 2 : ℝ) ^ bgV A w :=
    ((GS.pb_mul pbM ((g3.const_mul 2).add (GS.pb_mul (pbB.const_mul 4) gu))).add
      (gtol.max g910)).add (GS.pb_mul (pbB.const_mul 2) gu)
  refine ⟨(((pbY.pow 2).add pbY).add (PB.const 1)).of_abs_le fun w => ?_, _,
    (((GS.pb_mul ((pbB.pow 2).const_mul 3) g).add (GS.pb_mul pbB glnW)).add gμ).add
      (GS.pb_mul ((pbB.pow 2).const_mul 42) gu), ?_⟩
  · have h := abs_logGamma_sub_le (hY1 w)
    rw [abs_of_nonneg (by have := hY1 w; positivity : (0 : ℝ) ≤ (xv + bgN A w) ^ 2
      + (xv + bgN A w) + 1)]
    exact h
  · filter_upwards [e, g1.eventually_le (by norm_num : (0 : ℝ) < 1 / 8),
      g2.eventually_le (by norm_num : (0 : ℝ) < 1 / 16),
      g3.eventually_le (by norm_num : (0 : ℝ) < 1 / 2), glnW.eventually_le one_pos,
      gμ.eventually_le one_pos] with w he h1 h2 h3 h4 h5
    have hY := bgY_gt hA w
    have hj3 : (3 : ℝ) ≤ glaisherTerms w := by exact_mod_cast glaisherTerms_ge w
    have h64 : 64 ≤ bgV A w := by have := bgV_ge A w; omega
    exact lnGammaStirlingEncl_width' h64 (M := glaisherTerms w + 1) (by omega) he.2 he.1
      (hY1 w) (by push_cast; linarith) (toVal_lnGammaTol w) (B := xv + bgN A w + 2) le_rfl
      (by push_cast; linarith) ((le_abs_self _).trans h1) ((le_abs_self _).trans h2)
      ((le_abs_self _).trans h3) ((le_abs_self _).trans h4) ((le_abs_self _).trans h5)

/-! ### The alternating sum -/

/-- **A term on enclosures** at a real argument: `l2 + 24 u` more of relative width. -/
theorem glaisherTermEncl_lencl' {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M k : ℕ}
    (hk : 1 ≤ k) (hkM : k ≤ M) {y : ℝ} (hy : 0 < y) {y2 p : Encl} {lam l2 : ℝ}
    (hy2 : LEncl y2 (y ^ 2) l2) (hp : LEncl p (1 / y ^ (2 * (k + 1))) lam) :
    LEncl (glaisherTermEncl V (AzNat.tangentNumbers (M + 1)) y2 k p) (barnesTau y k)
      (lam + l2 + 24 * (1 / 2 : ℝ) ^ V) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := psiTermEncl_width hu (M := M + 1) (k := k + 1) (by omega) (by omega) hp
  have h2 := (h1.mul hu hy2).div hu (LEncl.nat (n := 2 * k * (2 * k + 1)) (by positivity))
  unfold glaisherTermEncl
  have hval : psiCoeffT (k + 1) / y ^ (2 * (k + 1)) * y ^ 2
      / ((2 * k * (2 * k + 1) : ℕ) : ℝ) = barnesTau y k := by
    unfold barnesTau
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    push_cast
    field_simp
  rw [hval] at h2
  exact h2.mono (le_of_eq (by ring))

/-- The shifted argument less one, its square and the reciprocal of the square, at level
`w`. -/
def bgy (A : BarnesIn) (w : ℕ) : Encl :=
  Encl.sub (bgV A w) (Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w))) (Encl.exact one)

def bgy2 (A : BarnesIn) (w : ℕ) : Encl := Encl.mul (bgV A w) (bgy A w) (bgy A w)

def bgInv2 (A : BarnesIn) (w : ℕ) : Encl := Encl.div (bgV A w) (Encl.exact one) (bgy2 A w)

theorem bgy_gt {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) (w : ℕ) :
    8 * (glaisherTerms w : ℝ) < xv + bgN A w - 1 := by
  have := bgY_gt hA w
  linarith

theorem bgy_aw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    AW (bgy A) fun w => xv + bgN A w - 1 :=
  AW.sub (bgV_ge A) (bgY_aw hA) (AW.exact toVal_one')

theorem bgy_lw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    LW (bgy A) fun w => xv + bgN A w - 1 :=
  (bgy_aw hA).toLW (Eventually.of_forall fun w => by
    have := bgy_gt hA w
    have h3 : (3 : ℝ) ≤ glaisherTerms w := by exact_mod_cast glaisherTerms_ge w
    linarith)

/-- **The alternating sum at the shifted argument**, level by level. -/
theorem barnesSum_aw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv) :
    AW (fun w => altSumLoop (bgV A w)
        (glaisherTermEncl (bgV A w) (AzNat.tangentNumbers (glaisherTerms w + 1)) (bgy2 A w))
        (bgInv2 A w) (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)) (glaisherTerms w - 1) 1
        (Encl.mul (bgV A w) (bgInv2 A w) (bgInv2 A w)) (Encl.exact zero))
      fun w => -(glaisherR ((xv + bgN A w - 1 : ℝ) : ℂ)).re - glaisherC := by
  have hV := bgV_ge A
  have hy2l := LW.mul hV (bgy_lw hA) (bgy_lw hA)
  have hinvl := LW.div hV (LW.exact toVal_one' one_pos) hy2l
  have hp1l := LW.mul hV hinvl hinvl
  obtain ⟨l2, gl2, el2⟩ := hy2l
  obtain ⟨li, gli, eli⟩ := hinvl
  obtain ⟨lp, glp, elp⟩ := hp1l
  have gu : GS fun w => (1 / 2 : ℝ) ^ bgV A w := GS.half_pow hV
  have pbJ : PB fun w : ℕ => ((glaisherTerms w : ℕ) : ℝ) := pb_glaisherTerms
  have pbJ1 : PB fun w : ℕ => ((glaisherTerms w - 1 : ℕ) : ℝ) :=
    pbJ.of_abs_le fun w => by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.sub_le _ _
  have hy0 : ∀ w, 0 < xv + bgN A w - 1 := fun w => by
    have := bgy_gt hA w
    have h3 : (3 : ℝ) ≤ glaisherTerms w := by exact_mod_cast glaisherTerms_ge w
    linarith
  -- the terms are at most `16`
  have hτ16 : ∀ w k, 1 ≤ k → k ≤ glaisherTerms w → barnesTau (xv + bgN A w - 1) k ≤ 16 :=
    fun w k hk hkj => by
      have hy := bgy_gt hA w
      have hkj' : (k : ℝ) ≤ glaisherTerms w := by exact_mod_cast hkj
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h1 := barnesTau_le (y := xv + bgN A w - 1) hk (by push_cast; linarith)
      have h2 := succ_sq_mul_quarter_pow_le k hk
      linarith
  -- the relative width along the loop
  have gLam : GS fun w => lp w + ((glaisherTerms w - 1 : ℕ) : ℝ)
      * (li w + 6 * (1 / 2 : ℝ) ^ bgV A w) + (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w) :=
    (glp.add (GS.pb_mul pbJ1 (gli.add (gu.const_mul 6)))).add (gl2.add (gu.const_mul 24))
  have gBu : GS fun w => 4 * (33 * ((glaisherTerms w : ℕ) : ℝ) + 33)
      * (1 / 2 : ℝ) ^ bgV A w :=
    GS.pb_mul (((pbJ.const_mul 33).add (PB.const 33)).const_mul 4) gu
  have gtol : GS fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16) :=
    GS.geom (by norm_num) (by norm_num) le_rfl (Eventually.of_forall fun w => by omega)
  have gτ : GS fun w => 2 * barnesTau (xv + bgN A w - 1) (glaisherTerms w) := by
    have g4 : GS fun w : ℕ => (1 / 4 : ℝ) ^ glaisherTerms w :=
      GS.geom (by norm_num) (by norm_num) (c := 12) (by norm_num)
        (Eventually.of_forall fun w => by unfold glaisherTerms; omega)
    refine (GS.pb_mul (((pbJ.add (PB.const 1)).pow 2).const_mul 32) g4).of_le
      (Eventually.of_forall fun w => ?_)
    have hj1 : 1 ≤ glaisherTerms w := by have := glaisherTerms_ge w; omega
    have hy := bgy_gt hA w
    have hj1r : (1 : ℝ) ≤ glaisherTerms w := by exact_mod_cast hj1
    have h1 := barnesTau_le (y := xv + bgN A w - 1) hj1 (by push_cast; linarith)
    have h0 := (barnesTau_pos (hy0 w) hj1).le
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    linarith
  refine ⟨(PB.const 16).of_abs_le fun w => ?_, fun w => 0 + ((glaisherTerms w - 1 : ℕ) : ℝ)
      * (2 * 16 * (lp w + ((glaisherTerms w - 1 : ℕ) : ℝ)
          * (li w + 6 * (1 / 2 : ℝ) ^ bgV A w) + (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w))
        + 4 * (33 * ((glaisherTerms w : ℕ) : ℝ) + 33) * (1 / 2 : ℝ) ^ bgV A w)
      + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * barnesTau (xv + bgN A w - 1) (glaisherTerms w))
      + 2 * (33 * ((glaisherTerms w : ℕ) : ℝ) + 33) * (1 / 2 : ℝ) ^ bgV A w, ?_, ?_⟩
  · obtain ⟨r, h1, -, h3⟩ := barnesMu_alt (hy0 w) (k := 1) le_rfl
    have h4 : altPartial (barnesTau (xv + bgN A w - 1)) 1 = 0 := by simp [altPartial]
    rw [h4, zero_add] at h1
    have := hτ16 w 1 le_rfl (by have := glaisherTerms_ge w; omega)
    rw [h1, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
    linarith
  · have e0 : (fun _ : ℕ => (0 : ℝ)) = fun _ => 0 := rfl
    exact (((GS.zero.add (GS.pb_mul pbJ1 ((gLam.const_mul (2 * 16)).add gBu))).add
      (gtol.max gτ)).add (GS.pb_mul (((pbJ.const_mul 33).add (PB.const 33)).const_mul 2) gu))
  · filter_upwards [el2, eli, elp, gLam.eventually_le (by norm_num : (0 : ℝ) < 1 / 2),
      gBu.eventually_le one_pos] with w h2 hi hp hL hB
    have hj3 := glaisherTerms_ge w
    have h64 : 64 ≤ bgV A w := by have := hV w; omega
    have : NeZero (bgV A w) := ⟨by omega⟩
    have hu8 : (1 / 2 : ℝ) ^ bgV A w ≤ 1 / 8 := half_pow_le_eighth (by omega)
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ bgV A w := by positivity
    have hy := hy0 w
    have hL' := (le_abs_self _).trans hL
    have hy2' : LEncl (bgy2 A w) ((xv + bgN A w - 1) ^ 2) (l2 w) := by
      rw [sq]; exact h2.2
    have hinv' : LEncl (bgInv2 A w) (1 / (xv + bgN A w - 1) ^ 2) (li w) := by
      rw [sq]; exact hi.2
    have hc0 : 0 ≤ (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w) / (1 / 2 : ℝ) ^ bgV A w :=
      div_nonneg (by have := h2.1; positivity) hu0.le
    have hcu : (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w) / (1 / 2 : ℝ) ^ bgV A w
        * (1 / 2 : ℝ) ^ bgV A w = l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w :=
      div_mul_cancel₀ _ hu0.ne'
    have hjr : (0 : ℝ) ≤ ((glaisherTerms w : ℕ) : ℝ) := Nat.cast_nonneg _
    have := altSumLoop_width (V := bgV A w) (M := glaisherTerms w)
      (t := barnesTau (xv + bgN A w - 1)) (q := fun k => 1 / (xv + bgN A w - 1) ^ (2 * (k + 1)))
      (term := glaisherTermEncl (bgV A w) (AzNat.tangentNumbers (glaisherTerms w + 1))
        (bgy2 A w))
      (T := 16) (B := 33 * ((glaisherTerms w : ℕ) : ℝ) + 33)
      (Lam := lp w + ((glaisherTerms w - 1 : ℕ) : ℝ)
        * (li w + 6 * (1 / 2 : ℝ) ^ bgV A w) + (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w))
      (c := (l2 w + 24 * (1 / 2 : ℝ) ^ bgV A w) / (1 / 2 : ℝ) ^ bgV A w)
      (μ := -(glaisherR ((xv + bgN A w - 1 : ℝ) : ℂ)).re - glaisherC)
      hu8 hinv'
      (fun k => by
        show 1 / (xv + bgN A w - 1) ^ (2 * (k + 1 + 1))
          = 1 / (xv + bgN A w - 1) ^ (2 * (k + 1)) * (1 / (xv + bgN A w - 1) ^ 2)
        rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by ring, pow_add]
        field_simp)
      (toVal_lnGammaTol w) hL' (by norm_num) hc0
      (fun k hk _ => barnesTau_pos hy hk) (fun k hk hkM => hτ16 w k hk hkM)
      (fun k p lam hk hkM hpk => by
        rw [hcu, ← add_assoc]
        exact glaisherTermEncl_lencl' hu8 hk hkM hy hy2' hpk)
      (fun k hk _ => barnesMu_alt hy hk)
      ((le_abs_self _).trans hB)
      (by nlinarith)
      (glaisherTerms w - 1) 1 (Encl.mul (bgV A w) (bgInv2 A w) (bgInv2 A w)) (Encl.exact zero)
      (lp w) 0 le_rfl (by omega)
      (by
        show LEncl _ (1 / (xv + bgN A w - 1) ^ (2 * (1 + 1))) (lp w)
        refine (congrArg (fun v => LEncl _ v (lp w)) ?_).mp hp.2
        field_simp)
      hp.1 (by rw [hcu])
      (by
        have h4 : altPartial (barnesTau (xv + bgN A w - 1)) 1 = 0 := by simp [altPartial]
        rw [h4]
        exact ⟨0, 0, toVal_zero', toVal_zero', le_rfl, le_rfl, by simp⟩)
      (by simp)
    exact this

/-! ### The enclosure of `ln |G(x)|` at level `w` -/

/-- The enclosure of the product at level `w` (`1` when `barnesProdLo` gives nothing). -/
def bgW (A : BarnesIn) (w : ℕ) : Encl :=
  match barnesProdLo (bgV A w) (A.frac (bgV A w)) (bgN A w) one one false with
  | some (_, wlo) => (wlo, glaisherUpper (bgV A w) wlo (16 * bgN A w * bgN A w))
  | none => Encl.exact one

/-- The products are small against the precision. -/
theorem bgN_sq_le (A : BarnesIn) (w : ℕ) :
    16 * ((bgN A w : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ bgV A w ≤ 1 / 2 :=
  sq_mul_half_pow_le (L := (bgN A w + glaisherArg w + 3).log2 + 1)
    ((Nat.lt_log2_self (n := bgN A w + glaisherArg w + 3)).trans_le' (by omega)) (by
      unfold bgV
      have := le_max_right A.eb ((bgN A w + glaisherArg w + 3).log2 + 1)
      omega)

/-- The enclosure of `ln |G(x)|` at level `w`, on the product `bgW`. -/
def bgL (A : BarnesIn) (w : ℕ) : Encl :=
  Encl.add (bgV A w)
    (Encl.sub (bgV A w)
      (Encl.sub (bgV A w)
        (Encl.sub (bgV A w)
          (Encl.add (bgV A w) (Encl.half (Encl.half (bgy2 A w)))
            (Encl.mulPos (bgV A w) (Encl.sub (bgV A w) (A.X (bgV A w)) (Encl.exact one))
              (clampNonneg (Encl.add (bgV A w)
                  (lnGammaStirlingEncl (bgV A w) (glaisherTerms w + 1)
                    (Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))
                    (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)))
                  (Encl.half (lnOfEncl (Encl.mul (bgV A w) (Encl.nat 2) (Encl.pi (bgV A w)))
                    (bgV A w)))).1,
                (Encl.add (bgV A w)
                  (lnGammaStirlingEncl (bgV A w) (glaisherTerms w + 1)
                    (Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))
                    (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)))
                  (Encl.half (lnOfEncl (Encl.mul (bgV A w) (Encl.nat 2) (Encl.pi (bgV A w)))
                    (bgV A w)))).2)))
          (Encl.mulPos (bgV A w)
            (Encl.add (bgV A w)
              (Encl.half (Encl.mul (bgV A w) (bgy A w)
                (Encl.add (bgV A w) (A.X (bgV A w)) (Encl.nat (bgN A w)))))
              (Encl.div (bgV A w) (Encl.exact one) (Encl.nat 12)))
            (clampNonneg (lnOfEncl (bgy A w) (bgV A w)).1, (lnOfEncl (bgy A w) (bgV A w)).2)))
        (glaisherKinkelinLnEnclWith w (AzNat.tangentNumbers (glaisherTerms w + 1))))
      (altSumLoop (bgV A w)
        (glaisherTermEncl (bgV A w) (AzNat.tangentNumbers (glaisherTerms w + 1)) (bgy2 A w))
        (bgInv2 A w) (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)) (glaisherTerms w - 1) 1
        (Encl.mul (bgV A w) (bgInv2 A w) (bgInv2 A w)) (Encl.exact zero)))
    (lnOfEncl (bgW A w) (bgV A w))

/-- `barnesGLnEncl` is `bgL` when the product answers. -/
theorem barnesGLnEncl_eq_bgL {A : BarnesIn} {w : ℕ} {neg : Bool} {wlo : AzFloat}
    (hprod : barnesProdLo (bgV A w) (A.frac (bgV A w)) (bgN A w) one one false
      = some (neg, wlo)) :
    barnesGLnEnclOf A w = some (neg, bgL A w) := by
  have hW : bgW A w = (wlo, glaisherUpper (bgV A w) wlo (16 * bgN A w * bgN A w)) := by
    unfold bgW
    rw [hprod]
  unfold barnesGLnEnclOf
  dsimp only
  split
  · next heq => exact absurd (hprod.symm.trans heq) (by simp)
  · next neg' W' heq =>
    have h := hprod.symm.trans heq
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Option.some.injEq, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    unfold bgL
    rw [hW]
    rfl

/-- **The enclosure of `ln |G(x)|` has a width that tends to `0`.** -/
theorem bgL_tw {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) : ∃ v : ℕ → ℝ, TW (bgL A) v := by
  have hV := bgV_ge A
  have pbV := pb_bgV hA
  have pbY : PB fun w : ℕ => xv + bgN A w := (PB.const xv).add (pb_bgN hA)
  have pby : PB fun w : ℕ => xv + bgN A w - 1 := pbY.sub (PB.const 1)
  have hYgt := bgY_gt hA
  have hj3 : ∀ w, (3 : ℝ) ≤ glaisherTerms w := fun w => by exact_mod_cast glaisherTerms_ge w
  have Xa := bgX_aw hA
  have yl := bgy_lw hA
  have Yl := bgY_lw hA
  -- `y²/4`
  have y2A : AW (bgy2 A) fun w => (xv + bgN A w - 1) * (xv + bgN A w - 1) :=
    (LW.mul hV yl yl).toAW (pby.mul pby)
  have q4 := y2A.half.half
  -- `(x − 1) ln Γ(Y)`
  have ln2pi := (LW.ln hV pbV (LW.mul hV (LW.nat (n := fun _ => 2) (fun _ => by norm_num))
    (LW.pi hV)) (G := fun _ => 3) (PB.const 3) (fun _ => by
      simpa using abs_log_two_pi_le)).half
  have lnGam := AW.add hV (barnesStirling_aw hA) ln2pi
  have t2 := AW.mulPosClamp hV (AW.sub hV Xa (AW.exact toVal_one')) lnGam
    (Eventually.of_forall fun w => by
      have e : Real.log (Real.Gamma (xv + bgN A w)) - 1 / 2 * Real.log (2 * Real.pi)
          + Real.log (((2 : ℕ) : ℝ) * Real.pi) / 2 = Real.log (Real.Gamma (xv + bgN A w)) := by
        push_cast
        ring
      rw [e]
      exact Real.log_nonneg (one_le_gamma_of_two_le (by
        have := hYgt w
        have := hj3 w
        linarith)))
  -- `(y (y + 1) / 2 + 1/12) ln y`
  have cA := AW.add hV ((LW.mul hV yl Yl).toAW (pby.mul pbY)).half
    ((LW.div hV (LW.exact toVal_one' one_pos) (LW.nat (n := fun _ => 12)
      (fun _ => by norm_num))).toAW (PB.const _))
  have hy1 : ∀ w, 1 ≤ xv + bgN A w - 1 := fun w => by
    have := hYgt w
    have := hj3 w
    linarith
  have lny := LW.ln hV pbV yl (G := fun w => xv + bgN A w - 1) pby (fun w => by
    have h1 := hy1 w
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < xv + bgN A w - 1)
    linarith)
  have t3 := AW.mulPosClamp hV cA lny
    (Eventually.of_forall fun w => Real.log_nonneg (hy1 w))
  -- `ln A`
  have lnA : TW (fun w => glaisherKinkelinLnEnclWith w
      (AzNat.tangentNumbers (glaisherTerms w + 1))) fun _ => glaisherC :=
    ⟨PB.const _, glaisherDelta, tendsto_glaisherDelta,
      (eventually_ge_atTop 64).mono fun w hw => glaisherKinkelinLnEncl_aencl hw⟩
  -- the product
  obtain ⟨d, hd0, -, hd⟩ := exists_pos_le_abs_add hnz
  have gu : GS fun w => (1 / 2 : ℝ) ^ bgV A w := GS.half_pow hV
  have Wl : LW (bgW A) fun w => ∏ j ∈ range (bgN A w), |xv + j| ^ (j + 1) := by
    refine ⟨fun w => (32 * ((bgN A w : ℕ) : ℝ) ^ 2 + 4) * (1 / 2 : ℝ) ^ bgV A w,
      GS.pb_mul ((((pb_bgN hA).pow 2).const_mul 32).add (PB.const 4)) gu,
      Eventually.of_forall fun w => ?_⟩
    have h64 : 64 ≤ bgV A w := by have := hV w; omega
    have : NeZero (bgV A w) := ⟨by omega⟩
    obtain ⟨neg', wlo, h1, h2, -⟩ := barnesProdLo_lencl (half_pow_le_eighth (by omega))
      (hA.frac _ (half_pow_le_eighth (by omega))) hnz (bgN A w) (bgN_sq_le A w)
    have hW : bgW A w = (wlo, glaisherUpper (bgV A w) wlo (16 * bgN A w * bgN A w)) := by
      unfold bgW
      rw [h1]
    rw [hW]
    exact ⟨by positivity, h2⟩
  have lnP := LW.ln hV pbV Wl
    (G := fun w => ((bgN A w : ℕ) : ℝ) ^ 2 * (|xv| + (bgN A w : ℕ) + 1 / d))
    (((pb_bgN hA).pow 2).mul (((PB.const |xv|).add (pb_bgN hA)).add (PB.const (1 / d))))
    (fun w => abs_log_barnesProd_le hd0 hd (bgN A w))
  exact ⟨_, TW.add hV (TW.sub hV (TW.sub hV ((AW.sub hV (AW.add hV q4 t2) t3).toTW) lnA)
    (barnesSum_aw hA).toTW) lnP.toTW⟩

/-- **The core of `G(x)` converges** off the zeros of `G`. -/
theorem barnesGCoreOf_coreConv {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) : CoreConv (barnesGCoreOf A) (barnesGR xv) := by
  obtain ⟨v, -, E, hE, hev⟩ := bgL_tw hA hnz
  obtain ⟨ht, hevE⟩ := gammaExpEncl_eventually false (Real.log |barnesGR xv|) hE
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hevE
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, hevE, eventually_ge_atTop 64] with w h1 h2 h3
  have h64 : 64 ≤ bgV A w := by have := bgV_ge A w; omega
  have : NeZero (bgV A w) := ⟨by omega⟩
  obtain ⟨neg, wlo, hprod, -⟩ := barnesProdLo_lencl (half_pow_le_eighth (by omega))
    (hA.frac _ (half_pow_le_eighth (by omega))) hnz (bgN A w) (bgN_sq_le A w)
  have hc := barnesGLnEncl_eq_bgL hprod
  obtain ⟨hpos, hL⟩ := barnesGLnEnclOf_spec hA hnz h3 hc
  have habs := sign_mul_eq_abs hpos
  rw [habs] at hL
  have hB0 : 0 < |barnesGR xv| := habs ▸ hpos
  obtain ⟨b, hb, hb1, hb2⟩ := h2 (bgL A w) (h1.of_isEncl hL)
  rw [Real.exp_log hB0] at hb1 hb2
  refine ⟨neg, b, ?_, ?_, ?_⟩
  · unfold barnesGCoreOf
    rw [hc]
    simp [hb]
  · rw [habs]; exact hb1
  · rw [habs]; exact hb2

/-- The core of `G(x)` converges at a float off the zeros of `G`. -/
theorem barnesGCore_coreConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hnz : ∀ m : ℕ, xv ≠ -m) : CoreConv (barnesGCore x) (barnesGR xv) :=
  barnesGCoreOf_coreConv (barnesArg_float hx) hnz

end Azurite.AzFloat
