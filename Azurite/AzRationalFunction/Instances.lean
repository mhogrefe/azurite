import Azurite.AzRationalFunction.Equiv.Arithmetic
import Azurite.AzRat.Instances

/-!
# Algebraic instances for `AzRationalFunction`

`AzRationalFunction` is a field: this file assembles the `Field` instance on
top of the computational operations defined earlier, plus the bundled ring
equivalence `ringEquivRatFunc` with `ℚ(x)`. Every law is transported from
`RatFunc ℚ` through the injection `toRatFunc` and the `toRatFunc_*`
commutation theorems — no new computation is introduced, and all data
fields are the existing verified operations.

The casts are computable and factor through the `O(1)` constant embedding
`ofAzRat` and the (limb-level) `AzRat` casts; `n • r` and `z • r` are one
cast plus one multiplication.
-/

namespace Azurite.AzRationalFunction

open Azurite.AzRat (toRat)

instance : NatCast AzRationalFunction := ⟨fun n => ofAzRat n⟩

@[simp] theorem toRatFunc_natCast (n : ℕ) :
    toRatFunc (n : AzRationalFunction) = (n : RatFunc ℚ) := by
  show toRatFunc (ofAzRat ((n : ℕ) : AzRat)) = _
  rw [toRatFunc_ofAzRat, Azurite.AzRat.toRat_natCast, map_natCast]

instance : IntCast AzRationalFunction := ⟨fun z => ofAzRat z⟩

@[simp] theorem toRatFunc_intCast (z : ℤ) :
    toRatFunc (z : AzRationalFunction) = (z : RatFunc ℚ) := by
  show toRatFunc (ofAzRat ((z : ℤ) : AzRat)) = _
  rw [toRatFunc_ofAzRat, Azurite.AzRat.toRat_intCast, map_intCast]

instance : RatCast AzRationalFunction := ⟨fun q => ofAzRat q⟩

@[simp] theorem toRatFunc_ratCast (q : ℚ) :
    toRatFunc (q : AzRationalFunction) = (q : RatFunc ℚ) := by
  show toRatFunc (ofAzRat ((q : ℚ) : AzRat)) = _
  rw [toRatFunc_ofAzRat, Azurite.AzRat.toRat_ratCast]
  simp

instance : NNRatCast AzRationalFunction := ⟨fun q => ofAzRat q⟩

@[simp] theorem toRatFunc_nnratCast (q : ℚ≥0) :
    toRatFunc (q : AzRationalFunction) = (q : RatFunc ℚ) := by
  show toRatFunc (ofAzRat ((q : ℚ≥0) : AzRat)) = _
  rw [toRatFunc_ofAzRat, Azurite.AzRat.toRat_nnratCast]
  simp

instance : Nontrivial AzRationalFunction := ⟨0, 1, fun h => by
  have h1 : (0 : RatFunc ℚ) = 1 := by rw [← toRatFunc_zero, ← toRatFunc_one, h]
  exact absurd h1 zero_ne_one⟩

/-- **`AzRationalFunction` is a field.** Every law is transported from
`RatFunc ℚ` through `toRatFunc_injective`; the data fields are the existing
computable operations (`n • r`/`z • r`/`q • r` are one cast plus one
multiplication; `r ^ n`/`r ^ z` run the componentwise gcd-free
`AzRationalFunction.pow`/`zpow`). -/
instance : Field AzRationalFunction where
  add_assoc a b c := toRatFunc_injective (by simp only [toRatFunc_add]; ring)
  zero_add a := toRatFunc_injective (by
    simp only [toRatFunc_add, toRatFunc_zero]; ring)
  add_zero a := toRatFunc_injective (by
    simp only [toRatFunc_add, toRatFunc_zero]; ring)
  add_comm a b := toRatFunc_injective (by simp only [toRatFunc_add]; ring)
  mul_assoc a b c := toRatFunc_injective (by simp only [toRatFunc_mul]; ring)
  one_mul a := toRatFunc_injective (by
    simp only [toRatFunc_mul, toRatFunc_one]; ring)
  mul_one a := toRatFunc_injective (by
    simp only [toRatFunc_mul, toRatFunc_one]; ring)
  left_distrib a b c := toRatFunc_injective (by
    simp only [toRatFunc_add, toRatFunc_mul]; ring)
  right_distrib a b c := toRatFunc_injective (by
    simp only [toRatFunc_add, toRatFunc_mul]; ring)
  zero_mul a := toRatFunc_injective (by
    simp only [toRatFunc_mul, toRatFunc_zero]; ring)
  mul_zero a := toRatFunc_injective (by
    simp only [toRatFunc_mul, toRatFunc_zero]; ring)
  mul_comm a b := toRatFunc_injective (by simp only [toRatFunc_mul]; ring)
  neg_add_cancel a := toRatFunc_injective (by
    simp only [toRatFunc_add, toRatFunc_neg, toRatFunc_zero]; ring)
  sub_eq_add_neg _ _ := rfl
  div_eq_mul_inv _ _ := rfl
  -- `n • r` / `z • r` are one cast plus one multiplication (the default
  -- `nsmulRec`/`zsmulRec` would be `n` additions); the casts are `O(1)`
  -- through `ofAzRat`.
  nsmul n r := (n : AzRationalFunction) * r
  nsmul_zero r := toRatFunc_injective (by
    show toRatFunc (((0 : ℕ) : AzRationalFunction) * r) = toRatFunc 0
    simp only [toRatFunc_mul, toRatFunc_natCast, toRatFunc_zero]
    push_cast
    ring)
  nsmul_succ n r := toRatFunc_injective (by
    show toRatFunc (((n + 1 : ℕ) : AzRationalFunction) * r)
      = toRatFunc (((n : ℕ) : AzRationalFunction) * r + r)
    simp only [toRatFunc_mul, toRatFunc_add, toRatFunc_natCast]
    push_cast
    ring)
  zsmul z r := (z : AzRationalFunction) * r
  zsmul_zero' r := toRatFunc_injective (by
    show toRatFunc (((0 : ℤ) : AzRationalFunction) * r) = toRatFunc 0
    simp only [toRatFunc_mul, toRatFunc_intCast, toRatFunc_zero]
    push_cast
    ring)
  zsmul_succ' n r := toRatFunc_injective (by
    show toRatFunc ((((n + 1 : ℕ) : ℤ) : AzRationalFunction) * r)
      = toRatFunc ((((n : ℕ) : ℤ) : AzRationalFunction) * r + r)
    simp only [toRatFunc_mul, toRatFunc_add, toRatFunc_intCast]
    push_cast
    ring)
  zsmul_neg' n r := toRatFunc_injective (by
    show toRatFunc (((Int.negSucc n) : AzRationalFunction) * r)
      = toRatFunc (-((((n + 1 : ℕ) : ℤ) : AzRationalFunction) * r))
    simp only [toRatFunc_mul, toRatFunc_neg, toRatFunc_intCast]
    push_cast [Int.negSucc_eq]
    ring)
  -- `r ^ n` / `r ^ z` run the componentwise `pow`/`zpow` (no gcd; the
  -- parts and the factor use sliding-window powers), so they are
  -- `O(log n)` multiplications rather than the default `O(n)`.
  npow n r := pow r n
  npow_zero r := toRatFunc_injective (by
    show toRatFunc (pow r 0) = toRatFunc 1
    rw [toRatFunc_pow, pow_zero, toRatFunc_one])
  npow_succ n r := toRatFunc_injective (by
    show toRatFunc (pow r (n + 1)) = toRatFunc (pow r n * r)
    rw [toRatFunc_mul, toRatFunc_pow, toRatFunc_pow, pow_succ])
  zpow z r := zpow r z
  zpow_zero' r := toRatFunc_injective (by
    show toRatFunc (zpow r 0) = toRatFunc 1
    rw [toRatFunc_zpow, zpow_zero, toRatFunc_one])
  zpow_succ' n r := toRatFunc_injective (by
    show toRatFunc (zpow r ((n.succ : ℕ) : ℤ)) = toRatFunc (zpow r ((n : ℕ) : ℤ) * r)
    rw [toRatFunc_mul, toRatFunc_zpow, toRatFunc_zpow, zpow_natCast, zpow_natCast,
      pow_succ])
  zpow_neg' n r := toRatFunc_injective (by
    show toRatFunc (zpow r (Int.negSucc n)) = toRatFunc ((zpow r ((n.succ : ℕ) : ℤ))⁻¹)
    rw [toRatFunc_inv, toRatFunc_zpow, toRatFunc_zpow, zpow_negSucc, zpow_natCast])
  natCast_zero := toRatFunc_injective (by
    rw [toRatFunc_natCast, toRatFunc_zero, Nat.cast_zero])
  natCast_succ n := toRatFunc_injective (by
    rw [toRatFunc_natCast, toRatFunc_add, toRatFunc_natCast, toRatFunc_one,
      Nat.cast_succ])
  intCast_ofNat n := toRatFunc_injective (by
    rw [toRatFunc_intCast, toRatFunc_natCast, Int.cast_natCast])
  intCast_negSucc n := toRatFunc_injective (by
    rw [toRatFunc_intCast, toRatFunc_neg, toRatFunc_natCast, Int.cast_negSucc])
  mul_inv_cancel a ha := toRatFunc_injective (by
    rw [toRatFunc_mul, toRatFunc_inv, toRatFunc_one]
    exact mul_inv_cancel₀ fun h =>
      ha (toRatFunc_injective (h.trans toRatFunc_zero.symm)))
  inv_zero := toRatFunc_injective (by
    rw [toRatFunc_inv, toRatFunc_zero, inv_zero])
  nnqsmul q a := (q : AzRationalFunction) * a
  qsmul q a := (q : AzRationalFunction) * a
  nnratCast_def q := toRatFunc_injective (by
    simp only [toRatFunc_nnratCast, toRatFunc_div, toRatFunc_natCast]
    exact NNRat.cast_def q)
  ratCast_def q := toRatFunc_injective (by
    simp only [toRatFunc_ratCast, toRatFunc_div, toRatFunc_intCast,
      toRatFunc_natCast]
    rw [Rat.cast_def])

/-- **The bundled ring equivalence with `ℚ(x)`**: `equivRatFunc`, together
with the `toRatFunc_add`/`toRatFunc_mul` commutation theorems. -/
noncomputable def ringEquivRatFunc : AzRationalFunction ≃+* RatFunc ℚ :=
  { equivRatFunc with
    map_add' := toRatFunc_add
    map_mul' := toRatFunc_mul }

end Azurite.AzRationalFunction

namespace Azurite

-- Sanity checks: numeric literals, field operations, smul, and pow all
-- compute (string-anchored via `AzRationalFunction.toString`).

private def rr (s : String) : AzRationalFunction :=
  (AzRationalFunction.parse s).get!

#guard toString ((rr "1/x" + rr "1/(x+1)") * (rr "x^2+x")) == "2*x+1"
#guard toString ((rr "(x+1)/(x-1)") ^ 2) == "(x^2+2*x+1)/(x^2-2*x+1)"
#guard toString ((2 : ℕ) • rr "x/2") == "x"
#guard toString (((-1 : ℤ) : AzRationalFunction) * rr "x") == "-x"
#guard toString (((3 / 4 : ℚ) : AzRationalFunction)) == "3/4"
#guard (rr "x/2") ^ (3 : ℕ) == rr "x^3/8"
#guard (rr "x/2") ^ (-2 : ℤ) == rr "4/x^2"

end Azurite
