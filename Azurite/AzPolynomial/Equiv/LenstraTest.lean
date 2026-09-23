/-
  Soundness of the finite field primality certificate checker
  (`Azurite.AzPolynomial.lenstraTest`), both verdicts:

  * `lenstraTest_eq_some_true`  — a `some true` verdict proves
    `n.toNat` PRIME, by discharging `CP.prime_of_lenstra_conditions`:
    the run itself has verified conditions (1), (2), (3) of
    Theorem 4.3.3 and emptied the divisor search.
  * `lenstraTest_eq_some_false` — a `some false` verdict proves
    `n.toNat` COMPOSITE: either a `gcdOrFactor`/`irreducibleOrFactor`
    call exhibited a factor, the divisor search found one, or a
    condition failed that `cond1_of_prime`/`cond3_of_prime`
    guarantees for primes (given the step-1 promise that `f` is
    irreducible when `n` is prime).

  The transports run at the RESIDUE-CLASS level in
  `AdjoinRoot (toZModPoly f)`, so no primality is needed for them:
  `mk_toZModPoly_powModByMonic'` (the class-level power bridge, over
  any modulus — by induction through `AzPolyMod`'s proven monoid
  power) and `symCoeffs_class` (the computed coefficient list of
  `(T − g)(T − g^n)⋯` represents, class by class, the coefficients
  of the abstract product over `AdjoinRoot`).  Canonical-form
  uniqueness (`toZModPoly_eq_of_mk_eq`: reduced representatives of
  equal classes are equal) upgrades class facts to the checker's
  syntactic checks where the composite verdicts need it.
-/
import Azurite.AzPolynomial.LenstraTest
import Azurite.AzPolynomial.Equiv.IrreducibleOrFactor
import Azurite.CrandallPomerance.Chapter4.Algorithm_4_3_4
import Azurite.AzNat.Equiv.IsPrime
import Azurite.AzNat.Equiv.Pow

namespace Azurite.AzPolynomial

open Polynomial

variable {m : AzNat} [NeZero m.toNat]

/-! ### Class-level transport plumbing (no primality) -/

section ClassBridge

variable {f : AzPolynomial (AzZMod m)}

/-- Reduction mod `f` preserves the transported residue class. -/
theorem mk_toZModPoly_modByMonic (hm : 1 < m.toNat) (hf : f.Monic)
    (p : AzPolynomial (AzZMod m)) :
    AdjoinRoot.mk (toZModPoly f) (toZModPoly (modByMonic p f))
      = AdjoinRoot.mk (toZModPoly f) (toZModPoly p) := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have : Nontrivial (AzZMod m) := nontrivial_of_ne 1 0 (NeZero.ne 1)
  rw [AdjoinRoot.mk_eq_mk]
  have h := toPoly_f_dvd_sub_modByMonic ((Monic_toPoly f).mpr hf)
    ((Monic_toPoly f).mpr hf).ne_zero p
  have h2 := map_dvd (mapRingHom (AzZMod.toZModRingHom (m := m))) h
  simp only [coe_mapRingHom, Polynomial.map_sub] at h2
  unfold toZModPoly
  exact dvd_sub_comm.mp h2

/-- **The class-level power bridge, primality-free**: over any modulus
`m > 1`, `powModByMonic` raises the transported residue class to the
power. -/
theorem mk_toZModPoly_powModByMonic' (hm : 1 < m.toNat) (hf : f.Monic)
    (a : AzPolynomial (AzZMod m)) (q : AzNat) :
    AdjoinRoot.mk (toZModPoly f) (toZModPoly (powModByMonic a q f))
      = AdjoinRoot.mk (toZModPoly f) (toZModPoly a) ^ q.toNat := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have : Nontrivial (AzZMod m) := nontrivial_of_ne 1 0 (NeZero.ne 1)
  have : Fact ((AzPolynomial.toPoly f).Monic) := ⟨(Monic_toPoly f).mpr hf⟩
  have hpow : AzPolyMod.ofPoly (f := f) a ^ q
      = AzPolyMod.ofPoly (f := f) a ^ q.toNat :=
    AzPolyMod.powAzNat_eq_pow _ q
  have hbase : AdjoinRoot.mk (toZModPoly f)
      (toZModPoly (AzPolyMod.ofPoly (f := f) a).val)
      = AdjoinRoot.mk (toZModPoly f) (toZModPoly a) :=
    mk_toZModPoly_modByMonic hm hf a
  show AdjoinRoot.mk (toZModPoly f)
      (toZModPoly ((AzPolyMod.ofPoly (f := f) a ^ q).val)) = _
  rw [hpow, ← hbase]
  generalize q.toNat = k
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    show AdjoinRoot.mk _ (toZModPoly (modByMonic 1 f)) = 1
    rw [mk_toZModPoly_modByMonic hm hf, toZModPoly_one, map_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    show AdjoinRoot.mk _ (toZModPoly (modByMonic
      ((AzPolyMod.ofPoly (f := f) a ^ k).val
        * (AzPolyMod.ofPoly (f := f) a).val) f)) = _
    rw [mk_toZModPoly_modByMonic hm hf, toZModPoly_mul, map_mul]

/-- Reduced representatives of equal residue classes are equal.  (The
divisor is MONIC, so no domain hypothesis is needed — the degree of
`fZ · c` is `deg fZ + deg c` even over `ZMod` of a composite.) -/
theorem toZModPoly_eq_of_mk_eq (hf : f.Monic)
    {p : AzPolynomial (AzZMod m)} {w : Polynomial (ZMod m.toNat)}
    (hp : (toZModPoly p).degree < (toZModPoly f).degree)
    (hw : w.degree < (toZModPoly f).degree)
    (hmk : AdjoinRoot.mk (toZModPoly f) (toZModPoly p)
      = AdjoinRoot.mk (toZModPoly f) w) :
    toZModPoly p = w := by
  obtain ⟨c, hc⟩ : toZModPoly f ∣ toZModPoly p - w :=
    AdjoinRoot.mk_eq_mk.mp hmk
  have hdeg : (toZModPoly p - w).degree < (toZModPoly f).degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hw)
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero] at hc
    exact sub_eq_zero.mp hc
  · exfalso
    have hfZm : (toZModPoly f).Monic := Monic_toZModPoly.mpr hf
    rw [mul_comm] at hc
    have hmul : (c * toZModPoly f).degree
        = c.degree + (toZModPoly f).degree := hfZm.degree_mul
    rw [← hc] at hmul
    have hle : (toZModPoly f).degree ≤ (toZModPoly p - w).degree := by
      rw [hmul]
      exact le_add_of_nonneg_left (Polynomial.zero_le_degree_iff.mpr hc0)
    exact absurd hdeg (not_lt.mpr hle)

/-- Degrees transport: a size-reduced `Az`-polynomial has transported
degree below the (monic) modulus. -/
theorem degree_toZModPoly_lt (hm : 1 < m.toNat) (hf : f.Monic)
    {p : AzPolynomial (AzZMod m)}
    (hsize : p.coeffs.size < f.coeffs.size) :
    (toZModPoly p).degree < (toZModPoly f).degree := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have : Nontrivial (AzZMod m) := nontrivial_of_ne 1 0 (NeZero.ne 1)
  have hfm := (Monic_toPoly f).mpr hf
  have h1 : (AzPolynomial.toPoly p).degree
      < (AzPolynomial.toPoly f).degree :=
    degree_toPoly_lt_of_size_lt hsize hfm.ne_zero
  calc (toZModPoly p).degree ≤ (AzPolynomial.toPoly p).degree := by
        unfold toZModPoly
        exact Polynomial.degree_map_le
    _ < (AzPolynomial.toPoly f).degree := h1
    _ = (toZModPoly f).degree := (hfm.degree_map _).symm

/-- `powModByMonic` outputs are size-reduced (for a monic modulus). -/
theorem powModByMonic_size (hm : 1 < m.toNat) (hf : f.Monic)
    (a : AzPolynomial (AzZMod m)) (q : AzNat) :
    (powModByMonic a q f).coeffs.size < f.coeffs.size := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have : Nontrivial (AzZMod m) := nontrivial_of_ne 1 0 (NeZero.ne 1)
  have hf0 : 0 < f.coeffs.size := by
    rcases Nat.eq_zero_or_pos f.coeffs.size with h0 | h
    · exfalso
      apply ((Monic_toPoly f).mpr hf).ne_zero
      rw [show f = 0 from AzPolynomial.ext (Array.size_eq_zero_iff.mp h0),
        toPoly_zero]
    · exact h
  rcases (AzPolyMod.ofPoly (f := f) a ^ q).isReduced with h | h
  · exact h
  · omega

end ClassBridge

/-! ### The step-3 coefficient fold: abstract mirror and transport -/

section SymCoeffs

variable {f : AzPolynomial (AzZMod m)}

/-- Abstract mirror of `mulLinAux` over any commutative ring. -/
private def mulLinAbsAux {S : Type _} [CommRing S] (a prev : S) :
    List S → List S
  | [] => [prev]
  | c :: cs => (prev - a * c) :: mulLinAbsAux a c cs

/-- Abstract mirror of `mulLin`. -/
private def mulLinAbs {S : Type _} [CommRing S] (a : S) :
    List S → List S
  | [] => []
  | c :: cs => (-(a * c)) :: mulLinAbsAux a c cs

private theorem toPoly_mulLinAbsAux {S : Type _} [CommRing S] (a : S) :
    ∀ (prev : S) (cs : List S),
      (mulLinAbsAux a prev cs).toPoly
        = Polynomial.C prev + (Polynomial.X - Polynomial.C a) * cs.toPoly
  | prev, [] => by
    show Polynomial.C prev + Polynomial.X * List.toPoly [] = _
    rw [show List.toPoly ([] : List S) = 0 from rfl]
    ring
  | prev, c :: cs => by
    show Polynomial.C (prev - a * c) + Polynomial.X
        * (mulLinAbsAux a c cs).toPoly = _
    rw [toPoly_mulLinAbsAux a c cs,
      show (c :: cs).toPoly = Polynomial.C c + Polynomial.X * cs.toPoly
        from rfl, Polynomial.C_sub, Polynomial.C_mul]
    ring

private theorem toPoly_mulLinAbs {S : Type _} [CommRing S] (a : S)
    (cs : List S) :
    (mulLinAbs a cs).toPoly
      = (Polynomial.X - Polynomial.C a) * cs.toPoly := by
  cases cs with
  | nil =>
    show List.toPoly [] = _
    rw [show List.toPoly ([] : List S) = 0 from rfl]
    ring
  | cons c cs =>
    show Polynomial.C (-(a * c)) + Polynomial.X
        * (mulLinAbsAux a c cs).toPoly = _
    rw [toPoly_mulLinAbsAux a c cs,
      show (c :: cs).toPoly = Polynomial.C c + Polynomial.X * cs.toPoly
        from rfl, Polynomial.C_neg, Polynomial.C_mul]
    ring

private theorem map_mulLinAux (hm : 1 < m.toNat) (hf : f.Monic)
    (a : AzPolynomial (AzZMod m)) :
    ∀ (prev : AzPolynomial (AzZMod m))
      (cs : List (AzPolynomial (AzZMod m))),
      (mulLinAux f a prev cs).map
          (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
        = mulLinAbsAux (AdjoinRoot.mk (toZModPoly f) (toZModPoly a))
            (AdjoinRoot.mk (toZModPoly f) (toZModPoly prev))
            (cs.map fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
  | prev, [] => rfl
  | prev, c :: cs => by
    show AdjoinRoot.mk _ (toZModPoly (modByMonic (prev - a * c) f))
        :: (mulLinAux f a c cs).map _ = _
    rw [map_mulLinAux hm hf a c cs, mk_toZModPoly_modByMonic hm hf,
      toZModPoly_sub, toZModPoly_mul, map_sub, map_mul]
    rfl

private theorem map_mulLin (hm : 1 < m.toNat) (hf : f.Monic)
    (a : AzPolynomial (AzZMod m))
    (cs : List (AzPolynomial (AzZMod m))) :
    (mulLin f a cs).map
        (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
      = mulLinAbs (AdjoinRoot.mk (toZModPoly f) (toZModPoly a))
          (cs.map fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c)) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    show AdjoinRoot.mk _ (toZModPoly (modByMonic (-(a * c)) f))
        :: (mulLinAux f a c cs).map _ = _
    rw [map_mulLinAux hm hf a c cs, mk_toZModPoly_modByMonic hm hf,
      show (-(a * c) : AzPolynomial (AzZMod m)) = 0 - a * c by ring,
      toZModPoly_sub, toZModPoly_mul]
    have h0 : toZModPoly (0 : AzPolynomial (AzZMod m)) = 0 := by
      unfold toZModPoly
      rw [toPoly_zero, Polynomial.map_zero]
    rw [h0, map_sub, map_zero, map_mul, zero_sub]
    rfl

/-- The transported conjugate list: entry `j` is the class
`(mk g)^(m^j)`. -/
private theorem conjugates_classes (hm : 1 < m.toNat) (hf : f.Monic) :
    ∀ (I : ℕ) (g₀ : AzPolynomial (AzZMod m)) (b : AdjoinRoot (toZModPoly f)),
      AdjoinRoot.mk (toZModPoly f) (toZModPoly g₀) = b →
      (conjugates f m g₀ I).map
          (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
        = (List.range I).map (fun j => b ^ m.toNat ^ j)
  | 0, g₀, b, hb => rfl
  | I + 1, g₀, b, hb => by
    show AdjoinRoot.mk _ (toZModPoly g₀)
        :: (conjugates f m (powModByMonic g₀ m f) I).map _ = _
    rw [conjugates_classes hm hf I (powModByMonic g₀ m f) (b ^ m.toNat)
        (by rw [mk_toZModPoly_powModByMonic' hm hf, hb]),
      hb, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rw [pow_zero, pow_one]
    · refine List.map_congr_left fun j _ => ?_
      show (b ^ m.toNat) ^ m.toNat ^ j = b ^ m.toNat ^ (j + 1)
      rw [← pow_mul, ← pow_succ']

/-- **The step-3 fold bridge**: the transported computed coefficient
list is the coefficient list of the abstract product
`∏ (T − (mk g)^(m^j))` over `AdjoinRoot (toZModPoly f)`. -/
private theorem symCoeffs_toPoly (hm : 1 < m.toNat) (hf : f.Monic)
    (g : AzPolynomial (AzZMod m)) (I : ℕ) :
    ((symCoeffs f g I).map
        (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).toPoly
      = ((List.range I).map (fun j =>
          Polynomial.X - Polynomial.C
            (AdjoinRoot.mk (toZModPoly f) (toZModPoly g)
              ^ m.toNat ^ j))).prod := by
  have hone : ((1 : AzPolynomial (AzZMod m)) :: ([] : List _)).map
      (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
      = [1] := by
    rw [List.map_cons, toZModPoly_one, map_one]
    rfl
  -- generalized fold invariant
  have hfold : ∀ (es cs : List (AzPolynomial (AzZMod m))),
      ((es.foldl (fun cs a => mulLin f a cs) cs).map
          (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).toPoly
        = (((es.map (fun c =>
              AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).map
            (fun b => Polynomial.X - Polynomial.C b)).prod)
          * (cs.map (fun c =>
              AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).toPoly := by
    intro es
    induction es with
    | nil =>
      intro cs
      show ((cs.map _).toPoly) = List.prod [] * _
      rw [List.prod_nil, one_mul]
    | cons e es ih =>
      intro cs
      show ((es.foldl _ (mulLin f e cs)).map _).toPoly = _
      rw [ih (mulLin f e cs), map_mulLin hm hf, toPoly_mulLinAbs,
        List.map_cons, List.map_cons, List.prod_cons]
      ring
  have h := hfold (conjugates f m (modByMonic g f) I) [1]
  rw [symCoeffs]
  rw [h]
  have h1 : (([1] : List (AzPolynomial (AzZMod m))).map
      (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).toPoly
      = 1 := by
    rw [show ([1] : List (AzPolynomial (AzZMod m))).map
        (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))
        = [1] from hone]
    show Polynomial.C 1 + Polynomial.X * List.toPoly [] = 1
    rw [show List.toPoly ([] : List (AdjoinRoot (toZModPoly f))) = 0
      from rfl]
    rw [Polynomial.C_1]
    ring
  rw [h1, mul_one,
    conjugates_classes hm hf I (modByMonic g f)
      (AdjoinRoot.mk (toZModPoly f) (toZModPoly g))
      (mk_toZModPoly_modByMonic hm hf g),
    List.map_map]
  rfl

/-- Hom application through `List.getCoeff`. -/
private theorem getCoeff_map_mk (l : List (AzPolynomial (AzZMod m)))
    (t : ℕ) :
    (l.map (fun c => AdjoinRoot.mk (toZModPoly f) (toZModPoly c))).getCoeff t
      = AdjoinRoot.mk (toZModPoly f) (toZModPoly (l.getCoeff t)) := by
  show ((l.map _)[t]?.getD 0) = _
  rw [List.getElem?_map]
  cases hl : l[t]? with
  | none =>
    show (0 : AdjoinRoot (toZModPoly f)) = _
    have h0 : toZModPoly (0 : AzPolynomial (AzZMod m)) = 0 := by
      unfold toZModPoly
      rw [toPoly_zero, Polynomial.map_zero]
    show (0 : AdjoinRoot (toZModPoly f))
        = AdjoinRoot.mk _ (toZModPoly ((l[t]?).getD 0))
    rw [hl]
    show (0 : AdjoinRoot (toZModPoly f)) = AdjoinRoot.mk _ (toZModPoly 0)
    rw [h0, map_zero]
  | some c =>
    show AdjoinRoot.mk _ (toZModPoly c)
        = AdjoinRoot.mk _ (toZModPoly ((l[t]?).getD 0))
    rw [hl]
    rfl

/-- **The per-coefficient class formula**: the class of the `t`-th
computed step-3 coefficient is the `t`-th coefficient of the abstract
product. -/
theorem symCoeffs_class (hm : 1 < m.toNat) (hf : f.Monic)
    (g : AzPolynomial (AzZMod m)) (I t : ℕ) :
    AdjoinRoot.mk (toZModPoly f) (toZModPoly ((symCoeffs f g I).getCoeff t))
      = (((List.range I).map (fun j =>
          Polynomial.X - Polynomial.C
            (AdjoinRoot.mk (toZModPoly f) (toZModPoly g)
              ^ m.toNat ^ j))).prod).coeff t := by
  rw [← symCoeffs_toPoly hm hf, _root_.coeff_toPoly, getCoeff_map_mk]

/-- Every entry of the step-3 coefficient list is size-reduced. -/
private theorem symCoeffs_size (hm : 1 < m.toNat) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (g : AzPolynomial (AzZMod m)) (I : ℕ) :
    ∀ c ∈ symCoeffs f g I, c.coeffs.size < f.coeffs.size := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have : Nontrivial (AzZMod m) := nontrivial_of_ne 1 0 (NeZero.ne 1)
  have hf0 : 0 < f.coeffs.size := by
    rcases Nat.eq_zero_or_pos f.coeffs.size with h0 | h
    · exfalso
      apply ((Monic_toPoly f).mpr hf).ne_zero
      rw [show f = 0 from AzPolynomial.ext (Array.size_eq_zero_iff.mp h0),
        toPoly_zero]
    · exact h
  have hf2 : 2 ≤ f.coeffs.size := by
    have : f.natDegree = f.coeffs.size - 1 := rfl
    omega
  have honesize : (1 : AzPolynomial (AzZMod m)).coeffs.size = 1 := by
    show (AzPolynomial.one).coeffs.size = 1
    unfold AzPolynomial.one
    rw [dite_eq_right (one_ne_zero (α := AzZMod m))]
    rfl
  have haux : ∀ (a : AzPolynomial (AzZMod m))
      (prev : AzPolynomial (AzZMod m)) cs,
      prev.coeffs.size < f.coeffs.size →
      (∀ c ∈ cs, c.coeffs.size < f.coeffs.size) →
      ∀ c' ∈ mulLinAux f a prev cs, c'.coeffs.size < f.coeffs.size := by
    intro a prev cs
    induction cs generalizing prev with
    | nil =>
      intro hprev _ c' hc'
      rw [mulLinAux, List.mem_singleton] at hc'
      subst hc'
      exact hprev
    | cons c cs ih =>
      intro hprev hcs c' hc'
      rw [mulLinAux] at hc'
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact modByMonic_coeffs_size_lt _ _ hf0
      · exact ih c (hcs c List.mem_cons_self)
          (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) c' hmem
  have hlin : ∀ (a : AzPolynomial (AzZMod m)) cs,
      (∀ c ∈ cs, c.coeffs.size < f.coeffs.size) →
      ∀ c' ∈ mulLin f a cs, c'.coeffs.size < f.coeffs.size := by
    intro a cs hcs c' hc'
    cases cs with
    | nil =>
      rw [mulLin] at hc'
      exact absurd hc' (List.not_mem_nil)
    | cons c cs =>
      rw [mulLin] at hc'
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact modByMonic_coeffs_size_lt _ _ hf0
      · exact haux a c cs (hcs c List.mem_cons_self)
          (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) c' hmem
  have hfold : ∀ (es cs : List (AzPolynomial (AzZMod m))),
      (∀ c ∈ cs, c.coeffs.size < f.coeffs.size) →
      ∀ c' ∈ es.foldl (fun cs a => mulLin f a cs) cs,
        c'.coeffs.size < f.coeffs.size := by
    intro es
    induction es with
    | nil => intro cs hcs c' hc'; exact hcs c' hc'
    | cons e es ih =>
      intro cs hcs c' hc'
      exact ih (mulLin f e cs) (hlin e cs hcs) c' hc'
  intro c hc
  refine hfold _ [1] ?_ c hc
  intro c' hc'
  rw [List.mem_singleton] at hc'
  subst hc'
  omega

end SymCoeffs

/-! ### Step-2 loop and certificate bridges -/

section Loops

variable {f g : AzPolynomial (AzZMod m)}

private theorem primitiveLoop_factor (hm : 1 < m.toNat) {N d : AzNat} :
    ∀ qs : List AzNat, primitiveLoop f g N qs = .inl d →
      d.toNat ∣ m.toNat ∧ 1 < d.toNat ∧ d.toNat < m.toNat := by
  intro qs
  induction qs with
  | nil =>
    intro h
    exact absurd h (by simp [primitiveLoop])
  | cons q qs ih =>
    intro h
    rw [primitiveLoop] at h
    cases hgo : gcdOrFactor m (powModByMonic g (N / q) f - 1) f with
    | inl d' =>
      rw [hgo] at h
      dsimp only at h
      obtain rfl : d' = d := by simpa using h
      exact gcdOrFactor_factor hm hgo
    | inr w =>
      rw [hgo] at h
      dsimp only at h
      by_cases hw : w = 1
      · rw [ite_eq_left hw] at h
        exact ih h
      · rw [ite_eq_right hw] at h
        exact absurd h (by simp)

private theorem primitiveLoop_pass {N : AzNat} :
    ∀ qs : List AzNat, primitiveLoop f g N qs = .inr true →
      ∀ q ∈ qs, ∃ w, gcdOrFactor m (powModByMonic g (N / q) f - 1) f
        = .inr w ∧ w = 1 := by
  intro qs
  induction qs with
  | nil =>
    intro _ q hq
    exact absurd hq List.not_mem_nil
  | cons q₀ qs ih =>
    intro h q hq
    rw [primitiveLoop] at h
    cases hgo : gcdOrFactor m (powModByMonic g (N / q₀) f - 1) f with
    | inl d =>
      rw [hgo] at h
      dsimp only at h
      exact absurd h (by simp)
    | inr w =>
      rw [hgo] at h
      dsimp only at h
      by_cases hw : w = 1
      · rw [ite_eq_left hw] at h
        rcases List.mem_cons.mp hq with rfl | hmem
        · exact ⟨w, hgo, hw⟩
        · exact ih h q hmem
      · rw [ite_eq_right hw] at h
        exact absurd h (by simp)

end Loops

private theorem foldl_mul_toNat :
    ∀ (qs : List AzNat) (acc : AzNat),
      (qs.foldl (· * ·) acc).toNat
        = qs.foldl (fun a q => a * q.toNat) acc.toNat
  | [], _ => rfl
  | q :: qs, acc => by
    show (qs.foldl (· * ·) (acc * q)).toNat = _
    rw [foldl_mul_toNat qs (acc * q), AzNat.toNat_mul]
    rfl

private theorem prime_dvd_foldl {p : ℕ} (hp : p.Prime) :
    ∀ qs : List AzNat, (∀ q ∈ qs, Nat.Prime q.toNat) → ∀ acc : ℕ,
      p ∣ qs.foldl (fun a q => a * q.toNat) acc →
      p ∣ acc ∨ ∃ q ∈ qs, p = q.toNat
  | [], _, _, h => Or.inl h
  | q₀ :: qs, hqs, acc, h => by
    rcases prime_dvd_foldl hp qs
        (fun q hq => hqs q (List.mem_cons_of_mem _ hq))
        (acc * q₀.toNat) h with hd | ⟨q, hq, hpq⟩
    · rcases hp.dvd_mul.mp hd with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨q₀, List.mem_cons_self,
          (Nat.prime_dvd_prime_iff_eq hp (hqs q₀ List.mem_cons_self)).mp h1⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hpq⟩

private theorem divisorSearch_eq_false {n F : AzNat} {I : ℕ}
    (h : divisorSearch n F I = false) :
    ∀ j : ℕ, 0 < j → j < I →
      ¬(n.toNat ^ j % F.toNat ∣ n.toNat ∧ 1 < n.toNat ^ j % F.toNat
        ∧ n.toNat ^ j % F.toNat < n.toNat) := by
  intro j hj0 hjI hcon
  obtain ⟨hdvd, h1, h2⟩ := hcon
  rw [divisorSearch, List.any_eq_false] at h
  have hj := h j (List.mem_range.mpr hjI)
  rw [decide_eq_true_eq] at hj
  refine hj ⟨hj0, ?_, ?_, ?_⟩
  · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat, AzNat.toNat_mod,
      AzNat.toNat_pow]
    exact h1
  · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_mod, AzNat.toNat_pow]
    exact h2
  · apply AzNat.toNat_injective
    rw [AzNat.toNat_mod, AzNat.toNat_mod, AzNat.toNat_pow, AzNat.toNat_zero]
    exact Nat.mod_eq_zero_of_dvd hdvd

private theorem divisorSearch_eq_true {n F : AzNat} {I : ℕ}
    (h : divisorSearch n F I = true) : ¬Nat.Prime n.toNat := by
  rw [divisorSearch, List.any_eq_true] at h
  obtain ⟨j, _, hj⟩ := h
  rw [decide_eq_true_eq] at hj
  obtain ⟨hj0, h1, h2, h3⟩ := hj
  intro hp
  have hdvd : (n.pow j % F).toNat ∣ n.toNat := by
    have h0 : (n % (n.pow j % F)).toNat = 0 := by
      rw [h3]
      rfl
    rw [AzNat.toNat_mod] at h0
    exact Nat.dvd_of_mod_eq_zero h0
  have h1' : 1 < (n.pow j % F).toNat := by
    have := (AzNat.lt_iff_toNat_lt _ _).mp h1
    rwa [AzNat.toNat_ofNat] at this
  have h2' : (n.pow j % F).toNat < n.toNat :=
    (AzNat.lt_iff_toNat_lt _ _).mp h2
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

/-! ### Shared step-3 class algebra -/

section Assembly

variable {f g : AzPolynomial (AzZMod m)}

private theorem esymm_class_transport (g : AzPolynomial (AzZMod m))
    (I k : ℕ) :
    AdjoinRoot.mk (toZModPoly f)
      (((Multiset.range I).map fun j => toZModPoly g ^ m.toNat ^ j).esymm k)
      = ((Multiset.range I).map fun j =>
          AdjoinRoot.mk (toZModPoly f) (toZModPoly g) ^ m.toNat ^ j).esymm
            k := by
  rw [← CP.esymm_map (AdjoinRoot.mk (toZModPoly f)), Multiset.map_map]
  congr 1

private theorem prod_multiset_eq_list (b : AdjoinRoot (toZModPoly f))
    (I : ℕ) :
    (((Multiset.range I).map fun j => b ^ m.toNat ^ j).map
        fun a => Polynomial.X - Polynomial.C a).prod
      = ((List.range I).map fun j =>
          Polynomial.X - Polynomial.C (b ^ m.toNat ^ j)).prod := by
  rw [show (Multiset.range I) = ((List.range I : List ℕ) : Multiset ℕ)
      from rfl,
    Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  rfl

private theorem mk_C_pow_mul (k : ℕ) (c : ZMod m.toNat) :
    AdjoinRoot.mk (toZModPoly f) (Polynomial.C ((-1) ^ k * c))
      = (-1) ^ k * AdjoinRoot.mk (toZModPoly f) (Polynomial.C c) := by
  rw [Polynomial.C_mul, map_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_1, map_pow, map_neg, map_one]

private theorem natDegree_prod_le (b : AdjoinRoot (toZModPoly f)) (I : ℕ) :
    (((List.range I).map fun j =>
        Polynomial.X - Polynomial.C (b ^ m.toNat ^ j)).prod).natDegree
      ≤ I := by
  refine le_trans (Polynomial.natDegree_list_prod_le _) ?_
  rw [List.map_map]
  refine le_trans (List.sum_le_length_nsmul _ 1 ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact Polynomial.natDegree_X_sub_C_le _
  · rw [List.length_map, List.length_range, smul_eq_mul, mul_one]

theorem natDegree_toZModPoly_eq (p : AzPolynomial (AzZMod m)) :
    (toZModPoly p).natDegree = p.natDegree := by
  unfold toZModPoly
  rw [Polynomial.natDegree_map_eq_of_injective
      (fun a b hab => AzZMod.toZMod_injective (by simpa using hab)),
    AzPolynomial.natDegree_toPoly]

end Assembly

/-! ### The positive direction (for completeness) -/

section Positive

variable {f g : AzPolynomial (AzZMod m)}

/-- Condition (1) forces the Fermat check to pass: the computed power
is the canonical representative of the class `1`. -/
private theorem powModByMonic_eq_one (hm : 1 < m.toNat) (hf : f.Monic)
    (hfdeg : 0 < f.natDegree) {e : AzNat}
    (h1 : toZModPoly f ∣ toZModPoly g ^ e.toNat - 1) :
    powModByMonic g e f = 1 := by
  have : Fact (1 < m.toNat) := ⟨hm⟩
  have hclass := mk_toZModPoly_powModByMonic' hm hf g e
  have hone : AdjoinRoot.mk (toZModPoly f) (toZModPoly g) ^ e.toNat
      = AdjoinRoot.mk (toZModPoly f) 1 := by
    rw [map_one, ← sub_eq_zero, ← map_one (AdjoinRoot.mk (toZModPoly f)),
      ← map_pow, ← map_sub, AdjoinRoot.mk_eq_zero]
    exact h1
  have hdegfZ : 0 < (toZModPoly f).degree := by
    refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
    rw [natDegree_toZModPoly_eq]
    omega
  apply toZModPoly_injective
  rw [toZModPoly_one]
  refine toZModPoly_eq_of_mk_eq hf ?_ ?_ ?_
  · exact degree_toZModPoly_lt hm hf (powModByMonic_size hm hf g e)
  · rw [Polynomial.degree_one]
    exact hdegfZ
  · rw [hclass, hone, map_one]

/-- Condition (2) forces every primitivity gcd to be `1`. -/
private theorem primitiveLoop_eq_inr_true (hp : Nat.Prime m.toNat)
    (hf : f.Monic) {N : AzNat} :
    ∀ qs : List AzNat,
      (∀ q ∈ qs, IsCoprime (toZModPoly g ^ (N / q).toNat - 1)
        (toZModPoly f)) →
      primitiveLoop f g N qs = .inr true := by
  intro qs
  induction qs with
  | nil => intro _; rfl
  | cons q qs ih =>
    intro hall
    rw [primitiveLoop]
    cases hgo : gcdOrFactor m (powModByMonic g (N / q) f - 1) f with
    | inl d => exact absurd hgo (gcdOrFactor_ne_inl_of_prime hp _ _ _)
    | inr w =>
      dsimp only
      have hw : w = 1 := by
        rw [gcd_eq_one_iff hf hgo, toZModPoly_sub, toZModPoly_one]
        refine (isCoprime_congr ?_).mpr (hall q List.mem_cons_self)
        simp only [map_sub, map_pow, map_one]
        rw [mk_toZModPoly_powModByMonic' hp.one_lt hf]
      rw [ite_eq_left hw]
      exact ih fun q' hq' => hall q' (List.mem_cons_of_mem _ hq')

/-- Condition (3) — automatic for a prime modulus and irreducible
transported `f` — forces every step-3 coefficient to be constant. -/
private theorem symCoeffs_all_const (hp : Nat.Prime m.toNat) {I : ℕ}
    (hI : 0 < I) (hfm : f.Monic) (hfdeg : f.natDegree = I)
    (hirr : Irreducible (toZModPoly f)) (g : AzPolynomial (AzZMod m)) :
    (symCoeffs f g I).all (fun c => c.natDegree == 0) = true := by
  have := Fact.mk hp
  have hn1' : 1 < m.toNat := hp.one_lt
  have hdegZ : (toZModPoly f).natDegree = f.natDegree :=
    natDegree_toZModPoly_eq f
  rw [List.all_eq_true]
  intro e hmem
  have hgoal : e.natDegree = 0 := by
    obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.mp hmem
    have hget : (symCoeffs f g I).getCoeff t = e := by
      show (((symCoeffs f g I)[t]?).getD 0) = e
      rw [List.getElem?_eq_getElem ht, hte]
      rfl
    have hclass := symCoeffs_class hn1' hfm g I t
    rw [hget] at hclass
    have hdegfZ : 0 < (toZModPoly f).degree := by
      refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
      omega
    have hconstcls : ∃ c : ZMod m.toNat,
        AdjoinRoot.mk (toZModPoly f) (toZModPoly e)
          = AdjoinRoot.mk (toZModPoly f) (Polynomial.C c) := by
      rcases Nat.lt_or_ge I t with htI | htI
      · refine ⟨0, ?_⟩
        rw [hclass, Polynomial.C_0, map_zero,
          Polynomial.coeff_eq_zero_of_natDegree_lt]
        exact lt_of_le_of_lt (natDegree_prod_le _ I) htI
      · have hvieta := Multiset.prod_X_sub_C_coeff
          ((Multiset.range I).map fun j =>
            AdjoinRoot.mk (toZModPoly f) (toZModPoly g) ^ m.toNat ^ j)
          (k := t)
          (by rw [Multiset.card_map, Multiset.card_range]; exact htI)
        rw [Multiset.card_map, Multiset.card_range] at hvieta
        rcases Nat.eq_zero_or_pos (I - t) with h0 | hpos
        · refine ⟨1, ?_⟩
          have hesymm0 : ((Multiset.range I).map fun j =>
              AdjoinRoot.mk (toZModPoly f) (toZModPoly g)
                ^ m.toNat ^ j).esymm 0 = 1 := by
            simp [Multiset.esymm, Multiset.powersetCard_zero_left]
          rw [hclass, ← prod_multiset_eq_list, hvieta, h0, hesymm0,
            pow_zero, one_mul, Polynomial.C_1, map_one]
        · obtain ⟨c, hc⟩ := CP.cond3_of_prime hI hirr
            (by rw [hdegZ, hfdeg]) (toZModPoly g) (I - t)
            hpos (by omega)
          refine ⟨(-1) ^ (I - t) * c, ?_⟩
          have hcc : AdjoinRoot.mk (toZModPoly f)
              (((Multiset.range I).map fun j =>
                toZModPoly g ^ m.toNat ^ j).esymm (I - t))
              = AdjoinRoot.mk (toZModPoly f) (Polynomial.C c) := by
            rw [← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
            exact hc
          rw [hclass, ← prod_multiset_eq_list, hvieta,
            ← esymm_class_transport, hcc, mk_C_pow_mul]
    obtain ⟨c, hc⟩ := hconstcls
    have hesize : e.coeffs.size < f.coeffs.size :=
      symCoeffs_size hn1' hfm (by omega) g I e hmem
    have heq := toZModPoly_eq_of_mk_eq hfm
      (degree_toZModPoly_lt hn1' hfm hesize)
      (lt_of_le_of_lt Polynomial.degree_C_le hdegfZ) hc
    have hnd := natDegree_toZModPoly_eq e
    rw [heq, Polynomial.natDegree_C] at hnd
    omega
  simpa using hgoal

end Positive

/-- No proper divisor of a prime can turn up in the divisor search. -/
private theorem divisorSearch_eq_false_of_prime {n F : AzNat} {I : ℕ}
    (hp : Nat.Prime n.toNat) : divisorSearch n F I = false := by
  cases hdv : divisorSearch n F I
  · rfl
  · exact absurd hp (divisorSearch_eq_true hdv)

/-! ### The verdict theorems -/

section Verdicts

variable {n : AzNat} [NeZero n.toNat] {I : ℕ} {F : AzNat}
  {qs : List AzNat} {f g : AzPolynomial (AzZMod n)}

/-- **A `some true` verdict proves `n` prime.** -/
theorem lenstraTest_eq_some_true
    (h : lenstraTest n I F qs f g = some true) : Nat.Prime n.toNat := by
  rw [lenstraTest] at h
  by_cases hval : (AzNat.ofNat 1 < n ∧ 0 < I ∧ f.Monic ∧ f.natDegree = I
      ∧ g ≠ 0 ∧ g.natDegree < I ∧ (qs.all AzNat.isPrime : Bool) = true
      ∧ qs.foldl (· * ·) (AzNat.ofNat 1) = F
      ∧ (n.pow I - 1) % F = 0 ∧ n ≤ F * F)
  case neg =>
    rw [ite_eq_left hval] at h
    exact absurd h (by simp)
  rw [ite_eq_right (not_not_intro hval)] at h
  obtain ⟨hn1, hI0, hfm, hfdeg, hg0, hgdeg, hqsp, hqsF, hFdvd, hnF2⟩ := hval
  have hn1' : 1 < n.toNat := by
    have := (AzNat.lt_iff_toNat_lt _ _).mp hn1
    rwa [AzNat.toNat_ofNat] at this
  cases hio : irreducibleOrFactor n f with
  | inl d =>
    rw [hio] at h
    exact absurd h (by simp)
  | inr b =>
    rw [hio] at h
    cases b with
    | false => exact absurd h (by simp)
    | true =>
      dsimp only at h
      by_cases hG : powModByMonic g (n.pow I - 1) f = 1
      case neg =>
        rw [ite_eq_left hG] at h
        exact absurd h (by simp)
      rw [ite_eq_right (not_not_intro hG)] at h
      cases hloop : primitiveLoop f g (n.pow I - 1) qs with
      | inl d =>
        rw [hloop] at h
        exact absurd h (by simp)
      | inr b' =>
        rw [hloop] at h
        cases b' with
        | false => exact absurd h (by simp)
        | true =>
          dsimp only at h
          by_cases h1 : ((symCoeffs f g I).all
              (fun c => c.natDegree == 0) : Bool) = true
          case neg =>
            rw [ite_eq_left h1] at h
            exact absurd h (by simp)
          rw [ite_eq_right (not_not_intro h1)] at h
          by_cases hdv : (divisorSearch n F I : Bool) = true
          case pos =>
            rw [ite_eq_left hdv] at h
            exact absurd h (by simp)
          rw [ite_eq_right hdv] at h
          have hdiv : divisorSearch n F I = false := by
            cases hd : divisorSearch n F I
            · rfl
            · exact absurd hd hdv
          -- assemble `prime_of_lenstra_conditions`
          have hNexp : (n.pow I - 1).toNat = n.toNat ^ I - 1 := by
            rw [AzNat.toNat_sub, AzNat.toNat_pow, AzNat.toNat_one]
          have hfZm : (toZModPoly f).Monic := Monic_toZModPoly.mpr hfm
          have hdegZ : (toZModPoly f).natDegree = f.natDegree :=
            natDegree_toZModPoly_eq f
          have hF0' : n.toNat ≤ F.toNat ^ 2 := by
            have := (AzNat.le_iff_toNat_le _ _).mp hnF2
            rwa [AzNat.toNat_mul, ← sq] at this
          have hFpos : 0 < F.toNat := by
            rcases Nat.eq_zero_or_pos F.toNat with h0 | hpos
            · rw [h0] at hF0'
              simp at hF0'
              omega
            · exact hpos
          have hFdvd' : F.toNat ∣ n.toNat ^ I - 1 := by
            have hc := congrArg AzNat.toNat hFdvd
            rw [AzNat.toNat_mod, hNexp, AzNat.toNat_zero] at hc
            exact Nat.dvd_of_mod_eq_zero hc
          -- condition (1)
          have hpowG := mk_toZModPoly_powModByMonic' hn1' hfm g
            (n.pow I - 1)
          rw [hG, hNexp, toZModPoly_one, map_one] at hpowG
          have hcond1 : toZModPoly f
              ∣ toZModPoly g ^ (n.toNat ^ I - 1) - 1 := by
            rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one,
              ← hpowG, sub_self]
          -- condition (2)
          have hqsp' : ∀ q ∈ qs, Nat.Prime q.toNat := by
            intro q hq
            exact (AzNat.isPrime_eq_true_iff q).mp
              (List.all_eq_true.mp hqsp q hq)
          have hFprod : F.toNat
              = qs.foldl (fun a q => a * q.toNat) 1 := by
            rw [← hqsF, foldl_mul_toNat, AzNat.toNat_ofNat]
          have hcond2 : ∀ q' : ℕ, q'.Prime → q' ∣ F.toNat →
              IsCoprime (toZModPoly g ^ ((n.toNat ^ I - 1) / q') - 1)
                (toZModPoly f) := by
            intro q' hq' hq'F
            rw [hFprod] at hq'F
            rcases prime_dvd_foldl hq' qs hqsp' 1 hq'F with hd | ⟨q, hqmem, rfl⟩
            · have h2 := Nat.le_of_dvd one_pos hd
              have h3 := hq'.two_le
              omega
            · obtain ⟨w, hgo, hw⟩ := primitiveLoop_pass qs hloop q hqmem
              have hcop := (gcd_eq_one_iff hfm hgo).mp hw
              rw [toZModPoly_sub, toZModPoly_one] at hcop
              have hclass := mk_toZModPoly_powModByMonic' hn1' hfm g
                ((n.pow I - 1) / q)
              rw [AzNat.toNat_div, hNexp] at hclass
              refine (isCoprime_congr ?_).mp hcop
              simp only [map_sub, map_pow, map_one]
              rw [hclass]
          -- condition (3)
          have hcond3 : ∀ k : ℕ, 1 ≤ k → k ≤ I → ∃ c : ZMod n.toNat,
              toZModPoly f ∣ ((Multiset.range I).map fun j =>
                toZModPoly g ^ n.toNat ^ j).esymm k - Polynomial.C c := by
            intro k hk1 hkI
            have hconst : ((symCoeffs f g I).getCoeff (I - k)).natDegree
                = 0 := by
              show (((symCoeffs f g I)[I - k]?).getD 0).natDegree = 0
              cases hmem : (symCoeffs f g I)[I - k]? with
              | none => rfl
              | some c =>
                have hcmem : c ∈ symCoeffs f g I :=
                  List.mem_of_getElem? hmem
                have hb := List.all_eq_true.mp h1 c hcmem
                simpa using hb
            have hdeg0 : (toZModPoly
                ((symCoeffs f g I).getCoeff (I - k))).natDegree = 0 := by
              rw [natDegree_toZModPoly_eq]
              exact hconst
            obtain ⟨c₀, hc₀⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
            refine ⟨(-1) ^ k * c₀, ?_⟩
            rw [← AdjoinRoot.mk_eq_zero, map_sub, sub_eq_zero]
            have hvieta := Multiset.prod_X_sub_C_coeff
              ((Multiset.range I).map fun j =>
                AdjoinRoot.mk (toZModPoly f) (toZModPoly g) ^ n.toNat ^ j)
              (k := I - k)
              (by rw [Multiset.card_map, Multiset.card_range]; omega)
            rw [Multiset.card_map, Multiset.card_range,
              show I - (I - k) = k by omega] at hvieta
            calc
              AdjoinRoot.mk (toZModPoly f)
                  (((Multiset.range I).map fun j =>
                    toZModPoly g ^ n.toNat ^ j).esymm k)
                = ((Multiset.range I).map fun j =>
                    AdjoinRoot.mk (toZModPoly f) (toZModPoly g)
                      ^ n.toNat ^ j).esymm k := esymm_class_transport g I k
              _ = (-1) ^ k * ((((Multiset.range I).map fun j =>
                    AdjoinRoot.mk (toZModPoly f) (toZModPoly g)
                      ^ n.toNat ^ j).map fun a =>
                    Polynomial.X - Polynomial.C a).prod.coeff (I - k)) := by
                  rw [hvieta, ← mul_assoc, ← pow_add,
                    Even.neg_one_pow ⟨k, rfl⟩, one_mul]
              _ = (-1) ^ k * AdjoinRoot.mk (toZModPoly f)
                    (toZModPoly ((symCoeffs f g I).getCoeff (I - k))) := by
                  rw [prod_multiset_eq_list,
                    ← symCoeffs_class hn1' hfm g I (I - k)]
              _ = (-1) ^ k * AdjoinRoot.mk (toZModPoly f)
                    (Polynomial.C c₀) := by rw [← hc₀]
              _ = AdjoinRoot.mk (toZModPoly f)
                    (Polynomial.C ((-1) ^ k * c₀)) :=
                  (mk_C_pow_mul k c₀).symm
          -- condition (4)
          have hcond4 := divisorSearch_eq_false hdiv
          exact CP.prime_of_lenstra_conditions hn1' hI0 hFpos hFdvd' hF0'
            hfZm (by omega) hcond1 hcond2 hcond3 hcond4

/-- **A `some false` verdict proves `n` composite.** -/
theorem lenstraTest_eq_some_false
    (h : lenstraTest n I F qs f g = some false) : ¬Nat.Prime n.toNat := by
  rw [lenstraTest] at h
  by_cases hval : (AzNat.ofNat 1 < n ∧ 0 < I ∧ f.Monic ∧ f.natDegree = I
      ∧ g ≠ 0 ∧ g.natDegree < I ∧ (qs.all AzNat.isPrime : Bool) = true
      ∧ qs.foldl (· * ·) (AzNat.ofNat 1) = F
      ∧ (n.pow I - 1) % F = 0 ∧ n ≤ F * F)
  case neg =>
    rw [ite_eq_left hval] at h
    exact absurd h (by simp)
  rw [ite_eq_right (not_not_intro hval)] at h
  obtain ⟨hn1, hI0, hfm, hfdeg, hg0, hgdeg, hqsp, hqsF, hFdvd, hnF2⟩ := hval
  have hn1' : 1 < n.toNat := by
    have := (AzNat.lt_iff_toNat_lt _ _).mp hn1
    rwa [AzNat.toNat_ofNat] at this
  have hNexp : (n.pow I - 1).toNat = n.toNat ^ I - 1 := by
    rw [AzNat.toNat_sub, AzNat.toNat_pow, AzNat.toNat_one]
  have hfZm : (toZModPoly f).Monic := Monic_toZModPoly.mpr hfm
  have hdegZ : (toZModPoly f).natDegree = f.natDegree :=
    natDegree_toZModPoly_eq f
  cases hio : irreducibleOrFactor n f with
  | inl d =>
    obtain ⟨hdvd, hd1, hdn⟩ := irreducibleOrFactor_factor hn1' hio
    intro hp
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h' | h' <;> omega
  | inr b =>
    rw [hio] at h
    cases b with
    | false => exact absurd h (by simp)
    | true =>
      dsimp only at h
      have hirr : Nat.Prime n.toNat → Irreducible (toZModPoly f) := by
        intro hp
        exact (irreducibleOrFactor_eq_inr_true_iff hp hfm (by omega)).mp hio
      have hfnotdvd : ¬toZModPoly f ∣ toZModPoly g := by
        have : Fact (1 < n.toNat) := ⟨hn1'⟩
        have : Nontrivial (AzZMod n) := nontrivial_of_ne 1 0 (NeZero.ne 1)
        intro hdvd
        have hgZ0 : toZModPoly g ≠ 0 := by
          intro h0
          apply hg0
          apply toZModPoly_injective
          rw [h0]
          unfold toZModPoly
          rw [toPoly_zero, Polynomial.map_zero]
        -- monic-degree argument, valid over any `ZMod`
        obtain ⟨c, hc⟩ := hdvd
        have hc0 : c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hc
          exact hgZ0 hc
        have hgsize : g.coeffs.size < f.coeffs.size := by
          have hg0' : g.coeffs.size ≠ 0 := by
            intro h0
            exact hg0 (AzPolynomial.ext (Array.size_eq_zero_iff.mp h0))
          have hf0' : f.coeffs.size ≠ 0 := by
            intro h0
            apply ((Monic_toPoly f).mpr hfm).ne_zero
            rw [show f = 0 from AzPolynomial.ext
              (Array.size_eq_zero_iff.mp h0), toPoly_zero]
          have h1 : g.natDegree = g.coeffs.size - 1 := rfl
          have h2 : f.natDegree = f.coeffs.size - 1 := rfl
          omega
        have hlt := degree_toZModPoly_lt hn1' hfm hgsize
        have hge : (toZModPoly f).degree ≤ (toZModPoly g).degree := by
          rw [hc, mul_comm, hfZm.degree_mul]
          exact le_add_of_nonneg_left (Polynomial.zero_le_degree_iff.mpr hc0)
        exact absurd hlt (not_lt.mpr hge)
      by_cases hG : powModByMonic g (n.pow I - 1) f = 1
      case neg =>
        rw [ite_eq_left hG] at h
        intro hp
        have : Fact (Nat.Prime n.toNat) := ⟨hp⟩
        have hcond1 := CP.cond1_of_prime (hirr hp)
          (by rw [hdegZ, hfdeg]) hfnotdvd
        exact hG (powModByMonic_eq_one hn1' hfm (by omega)
          (by rw [hNexp]; exact hcond1))
      rw [ite_eq_right (not_not_intro hG)] at h
      cases hloop : primitiveLoop f g (n.pow I - 1) qs with
      | inl d =>
        obtain ⟨hdvd, hd1, hdn⟩ := primitiveLoop_factor hn1' qs hloop
        intro hp
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h' | h' <;> omega
      | inr b' =>
        rw [hloop] at h
        cases b' with
        | false => exact absurd h (by simp)
        | true =>
          dsimp only at h
          by_cases h1 : ((symCoeffs f g I).all
              (fun c => c.natDegree == 0) : Bool) = true
          case pos =>
            rw [ite_eq_right (not_not_intro h1)] at h
            by_cases hdv : (divisorSearch n F I : Bool) = true
            case pos => exact divisorSearch_eq_true hdv
            rw [ite_eq_right hdv] at h
            exact absurd h (by simp)
          -- a step-3 coefficient is nonconstant: composite by
          -- the contrapositive of `cond3_of_prime`
          rw [ite_eq_left h1] at h
          intro hp
          exact h1 (symCoeffs_all_const hp hI0 hfm hfdeg (hirr hp) g)

/-- **The positive direction, for completeness**: valid certificate
data plus an irreducible transported `f` and conditions (1), (2) for
the witness `g` force the `some true` verdict. -/
theorem lenstraTest_eq_some_true_of (hp : Nat.Prime n.toNat)
    (hI : 0 < I) (hfm : f.Monic) (hfdeg : f.natDegree = I)
    (hg0 : g ≠ 0) (hgdeg : g.natDegree < I)
    (hqsp : (qs.all AzNat.isPrime : Bool) = true)
    (hqsF : qs.foldl (· * ·) (AzNat.ofNat 1) = F)
    (hFdvd : (n.pow I - 1) % F = 0)
    (hnF2 : n ≤ F * F)
    (hirr : Irreducible (toZModPoly f))
    (h1 : toZModPoly f ∣ toZModPoly g ^ (n.toNat ^ I - 1) - 1)
    (h2 : ∀ q ∈ qs, IsCoprime
      (toZModPoly g ^ ((n.toNat ^ I - 1) / q.toNat) - 1)
      (toZModPoly f)) :
    lenstraTest n I F qs f g = some true := by
  have hn1 : AzNat.ofNat 1 < n := by
    rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat]
    exact hp.one_lt
  have hNexp : (n.pow I - 1).toNat = n.toNat ^ I - 1 := by
    rw [AzNat.toNat_sub, AzNat.toNat_pow, AzNat.toNat_one]
  rw [lenstraTest,
    ite_eq_right (not_not_intro
      ⟨hn1, hI, hfm, hfdeg, hg0, hgdeg, hqsp, hqsF, hFdvd, hnF2⟩),
    (irreducibleOrFactor_eq_inr_true_iff hp hfm (by omega)).mpr hirr]
  dsimp only
  have hG : powModByMonic g (n.pow I - 1) f = 1 :=
    powModByMonic_eq_one hp.one_lt hfm (by omega)
      (by rw [hNexp]; exact h1)
  rw [ite_eq_right (not_not_intro hG),
    primitiveLoop_eq_inr_true hp hfm qs (fun q hq => by
      rw [AzNat.toNat_div, hNexp]
      exact h2 q hq)]
  dsimp only
  rw [ite_eq_right (not_not_intro
      (symCoeffs_all_const hp hI hfm hfdeg hirr g)),
    ite_eq_right (show ¬((divisorSearch n F I : Bool) = true) from by
      rw [divisorSearch_eq_false_of_prime hp]
      simp)]

end Verdicts

end Azurite.AzPolynomial
