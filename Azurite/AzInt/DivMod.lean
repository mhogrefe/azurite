import Azurite.AzInt.Add
import Azurite.AzInt.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Parse
import Azurite.AzInt.ToString
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Sub

namespace Azurite

/-- Euclidean divmod for `AzInt`. Returns `(q, r)` with `q * b + r = a` and
    `0 ≤ r < |b|` when `b ≠ 0`. Matches Lean's `Int.ediv`/`Int.emod`, which
    are the operations underlying `(/)` and `(%)` on `Int` in current Lean.

    When `b = 0`: returns `(0, a)` (Lean's convention for all four variants). -/
def AzInt.edivMod (a b : AzInt) : AzInt × AzInt :=
  let qr := a.abs.divMod b.abs
  let q' := qr.1
  let r' := qr.2
  if a.sign then
    (AzInt.mkNorm (a.sign == b.sign) q', r'.toAzInt)
  else if hr0 : r' = 0 then
    (AzInt.mkNorm (a.sign == b.sign) q', AzInt.mkNorm a.sign r')
  else if hBzero : b.abs = 0 then
    (AzInt.mkNorm (a.sign == b.sign) q', AzInt.mkNonzero a.sign r' hr0)
  else
    have h_q_abs_ne : (q'.addUInt64 1) ≠ 0 := by
      intro h
      have h0 : (q'.addUInt64 1).toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_addUInt64, show ((1 : UInt64).toNat = 1) from rfl] at h0
      omega
    have hbnz : b.abs.toNat ≠ 0 := by
      intro he
      apply hBzero
      apply AzNat.toNat_injective
      rw [he, AzNat.toNat_zero]
    have hrlt : r'.toNat < b.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).2 hbnz
    have h_r_abs_ne : (b.abs - r') ≠ 0 := by
      intro h
      have h0 : (b.abs - r').toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_sub] at h0
      omega
    (AzInt.mkNonzero (!b.sign) (q'.addUInt64 1) h_q_abs_ne,
     AzInt.mkNonzero true (b.abs - r') h_r_abs_ne)

/-- Euclidean division on `AzInt`: `q` such that `q * b + r = a`, `0 ≤ r < |b|`.
    Specialised: mirrors `edivMod`'s branch structure but skips the
    remainder-side AzInt construction (notably the `b.abs - r'`
    subtraction in branch 4).  Equal to `(a.edivMod b).1` (see
    `Equiv/DivMod.lean`). -/
def AzInt.ediv (a b : AzInt) : AzInt :=
  let qr := a.abs.divMod b.abs
  let q' := qr.1
  let r' := qr.2
  if a.sign then
    AzInt.mkNorm (a.sign == b.sign) q'
  else if hr0 : r' = 0 then
    AzInt.mkNorm (a.sign == b.sign) q'
  else if hBzero : b.abs = 0 then
    AzInt.mkNorm (a.sign == b.sign) q'
  else
    have h_q_abs_ne : (q'.addUInt64 1) ≠ 0 := by
      intro h
      have h0 : (q'.addUInt64 1).toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_addUInt64, show ((1 : UInt64).toNat = 1) from rfl] at h0
      omega
    have hbnz : b.abs.toNat ≠ 0 := by
      intro he
      apply hBzero
      apply AzNat.toNat_injective
      rw [he, AzNat.toNat_zero]
    have hrlt : r'.toNat < b.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).2 hbnz
    have h_r_abs_ne : (b.abs - r') ≠ 0 := by
      intro h
      have h0 : (b.abs - r').toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_sub] at h0
      omega
    AzInt.mkNonzero (!b.sign) (q'.addUInt64 1) h_q_abs_ne

/-- Euclidean modulus on `AzInt`: always non-negative when `b ≠ 0`.
    Specialised: mirrors `edivMod`'s branch structure but skips the
    quotient-side AzInt construction (notably the `q'.addUInt64 1`
    increment and `mkNonzero (!b.sign) ...` wrap in branch 4).  Equal to
    `(a.edivMod b).2` (see `Equiv/DivMod.lean`). -/
def AzInt.emod (a b : AzInt) : AzInt :=
  let qr := a.abs.divMod b.abs
  let q' := qr.1
  let r' := qr.2
  if a.sign then
    r'.toAzInt
  else if hr0 : r' = 0 then
    AzInt.mkNorm a.sign r'
  else if hBzero : b.abs = 0 then
    AzInt.mkNonzero a.sign r' hr0
  else
    have h_q_abs_ne : (q'.addUInt64 1) ≠ 0 := by
      intro h
      have h0 : (q'.addUInt64 1).toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_addUInt64, show ((1 : UInt64).toNat = 1) from rfl] at h0
      omega
    have hbnz : b.abs.toNat ≠ 0 := by
      intro he
      apply hBzero
      apply AzNat.toNat_injective
      rw [he, AzNat.toNat_zero]
    have hrlt : r'.toNat < b.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).2 hbnz
    have h_r_abs_ne : (b.abs - r') ≠ 0 := by
      intro h
      have h0 : (b.abs - r').toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_sub] at h0
      omega
    AzInt.mkNonzero true (b.abs - r') h_r_abs_ne

/-- `(div, mod)` as a single computation. Equal to `edivMod` because Lean's
    `Int.div`/`Int.mod` are Euclidean. -/
def AzInt.divMod : AzInt → AzInt → AzInt × AzInt := AzInt.edivMod

/-- `AzInt` division — Euclidean, matching Lean's `Int.div`. -/
def AzInt.div (a b : AzInt) : AzInt := a.ediv b

/-- `AzInt` modulus — Euclidean, matching Lean's `Int.mod`. -/
def AzInt.mod (a b : AzInt) : AzInt := a.emod b

instance : Div AzInt := ⟨AzInt.div⟩
instance : Mod AzInt := ⟨AzInt.mod⟩

/-- Floor divmod for `AzInt`. Returns `(q, r)` with `q = ⌊a/b⌋` (rounding toward
    `-∞`) and `q * b + r = a`. The remainder has the sign of `b` when nonzero,
    or is zero. Matches Lean's `Int.fdiv`/`Int.fmod`.

    When `b = 0`: returns `(0, a)`. -/
def AzInt.fdivMod (a b : AzInt) : AzInt × AzInt :=
  let qr := a.abs.divMod b.abs
  let q' := qr.1
  let r' := qr.2
  if a.sign == b.sign then
    (q'.toAzInt, AzInt.mkNorm a.sign r')
  else if hr0 : r' = 0 then
    (AzInt.mkNorm false q', AzInt.mkNorm a.sign r')
  else if hBzero : b.abs = 0 then
    (AzInt.mkNorm false q', AzInt.mkNonzero a.sign r' hr0)
  else
    have h_q_abs_ne : (q'.addUInt64 1) ≠ 0 := by
      intro h
      have h0 : (q'.addUInt64 1).toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_addUInt64, show ((1 : UInt64).toNat = 1) from rfl] at h0
      omega
    have hbnz : b.abs.toNat ≠ 0 := by
      intro he
      apply hBzero
      apply AzNat.toNat_injective
      rw [he, AzNat.toNat_zero]
    have hrlt : r'.toNat < b.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).2 hbnz
    have h_r_abs_ne : (b.abs - r') ≠ 0 := by
      intro h
      have h0 : (b.abs - r').toNat = 0 := by rw [h]; rfl
      rw [AzNat.toNat_sub] at h0
      omega
    (AzInt.mkNonzero false (q'.addUInt64 1) h_q_abs_ne,
     AzInt.mkNonzero b.sign (b.abs - r') h_r_abs_ne)

/-- Floor division on `AzInt`: rounds the true quotient `a/b` toward `-∞`. -/
def AzInt.fdiv (a b : AzInt) : AzInt := (a.fdivMod b).1

/-- Floor modulus on `AzInt`: remainder has the sign of `b` (or is zero). -/
def AzInt.fmod (a b : AzInt) : AzInt := (a.fdivMod b).2

section Examples

private def parse (s : String) : AzInt := (AzInt.parse s).get!

-- Euclidean (div / mod): always 0 ≤ r < |b|.
#guard Azurite.AzInt.toString ((parse "7").div (parse "2")) == "3"
#guard Azurite.AzInt.toString ((parse "7").mod (parse "2")) == "1"
#guard Azurite.AzInt.toString ((parse "-7").div (parse "2")) == "-4"
#guard Azurite.AzInt.toString ((parse "-7").mod (parse "2")) == "1"
#guard Azurite.AzInt.toString ((parse "7").div (parse "-2")) == "-3"
#guard Azurite.AzInt.toString ((parse "7").mod (parse "-2")) == "1"
#guard Azurite.AzInt.toString ((parse "-7").div (parse "-2")) == "4"
#guard Azurite.AzInt.toString ((parse "-7").mod (parse "-2")) == "1"
#guard Azurite.AzInt.toString ((parse "8").div (parse "2")) == "4"
#guard Azurite.AzInt.toString ((parse "8").mod (parse "2")) == "0"

-- Floor (fdiv / fmod): r has the sign of b.
#guard Azurite.AzInt.toString ((parse "7").fdiv (parse "2")) == "3"
#guard Azurite.AzInt.toString ((parse "7").fmod (parse "2")) == "1"
#guard Azurite.AzInt.toString ((parse "-7").fdiv (parse "2")) == "-4"
#guard Azurite.AzInt.toString ((parse "-7").fmod (parse "2")) == "1"
#guard Azurite.AzInt.toString ((parse "7").fdiv (parse "-2")) == "-4"
#guard Azurite.AzInt.toString ((parse "7").fmod (parse "-2")) == "-1"
#guard Azurite.AzInt.toString ((parse "-7").fdiv (parse "-2")) == "3"
#guard Azurite.AzInt.toString ((parse "-7").fmod (parse "-2")) == "-1"

-- Division by zero: q = 0, r = a (Lean's convention).
#guard Azurite.AzInt.toString ((parse "7").div (parse "0")) == "0"
#guard Azurite.AzInt.toString ((parse "7").mod (parse "0")) == "7"
#guard Azurite.AzInt.toString ((parse "-7").div (parse "0")) == "0"
#guard Azurite.AzInt.toString ((parse "-7").mod (parse "0")) == "-7"
#guard Azurite.AzInt.toString ((parse "-7").fdiv (parse "0")) == "0"
#guard Azurite.AzInt.toString ((parse "-7").fmod (parse "0")) == "-7"

-- divMod returns (div, mod).
#guard (let (q, r) := (parse "-7").divMod (parse "2")
        (Azurite.AzInt.toString q, Azurite.AzInt.toString r)) == ("-4", "1")

end Examples

end Azurite
