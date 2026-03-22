/-
  Variable types for multivariate polynomials.
-/
import Mathlib.Order.Fin.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.ToString
import Azurite.AzPolynomial.StringLemmas

namespace Azurite

open AzPolynomial in
private theorem charOfNat_toNat_small (n : ℕ) (h : n < 55296) :
    (Char.ofNat n).toNat = n := by
  have : n.isValidChar = true := by simp [Nat.isValidChar]; omega
  simp only [Char.ofNat, this, ↓reduceDIte]
  simp [Char.ofNatAux, Char.toNat, UInt32.toNat]

/-- A typeclass for multivariate polynomial variable types with `n` variables.
    Requires a linear ordering and a bijection to `Fin n`. -/
class Var (α : Type _) (n : ℕ) [LinearOrder α] where
  /-- Convert a variable to its index in `Fin n`. -/
  toFin : α → Fin n
  /-- Convert an index in `Fin n` to a variable. -/
  ofFin : Fin n → α
  /-- `ofFin` is a left inverse of `toFin`. -/
  ofFin_toFin : ∀ v : α, ofFin (toFin v) = v
  /-- `toFin` is a left inverse of `ofFin`. -/
  toFin_ofFin : ∀ i : Fin n, toFin (ofFin i) = i

namespace Var

variable {α : Type _} {n : ℕ} [LinearOrder α] [inst : Var α n]

theorem toFin_injective : Function.Injective (inst.toFin) := by
  intro a b h
  have := congr_arg inst.ofFin h
  simp [inst.ofFin_toFin] at this
  exact this

theorem ofFin_injective : Function.Injective (inst.ofFin) := by
  intro a b h
  have := congr_arg inst.toFin h
  simp [inst.toFin_ofFin] at this
  exact this

/-- The bijection between a variable type and `Fin n`. -/
def equiv : α ≃ Fin n where
  toFun := inst.toFin
  invFun := inst.ofFin
  left_inv := inst.ofFin_toFin
  right_inv := inst.toFin_ofFin

end Var

/-- A character used in polynomial syntax: ASCII digits, `+`, `-`, `*`, `^`. -/
def isPolySyntaxChar (c : Char) : Prop :=
  (c.toNat ≥ '0'.toNat ∧ c.toNat ≤ '9'.toNat) ∨ c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '^'

/-- Extension of `Var` for variable types that can be serialized/deserialized
    as character sequences that do not collide with polynomial syntax. -/
class ParseableVar (α : Type _) (n : ℕ) [LinearOrder α] extends Var α n where
  toChars : α → List Char
  parseChars : List Char → Option α
  parse_toChars : ∀ v : α, parseChars (toChars v) = some v
  toChars_nonempty : ∀ v : α, toChars v ≠ []
  toChars_no_syntax : ∀ v : α, ∀ c ∈ toChars v, ¬ isPolySyntaxChar c

/-- Convert a natural number to a list of Unicode subscript digit characters (₀₁₂...). -/
def natToSubscriptChars (n : ℕ) : List Char :=
  (AzPolynomial.natToChars n).map (fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat))

/-- Parse a list of Unicode subscript digit characters to a natural number. -/
def parseSubscriptChars (cs : List Char) : Option ℕ :=
  AzPolynomial.parseNatChars (cs.map (fun c => Char.ofNat (c.toNat - '₀'.toNat + '0'.toNat)))

private theorem subscript_unsubscript_digit (c : Char)
    (hge : 48 ≤ c.toNat) (hle : c.toNat ≤ 57) :
    Char.ofNat ((Char.ofNat (c.toNat - 48 + 8320)).toNat - 8320 + 48) = c := by
  rw [charOfNat_toNat_small (c.toNat - 48 + 8320) (by omega)]
  have : c.toNat - 48 + 8320 - 8320 + 48 = c.toNat := by omega
  rw [this]; exact Char.ofNat_toNat c

private theorem subscript_map_cancel (l : List Char)
    (h : ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    l.map (fun c => Char.ofNat ((Char.ofNat (c.toNat - 48 + 8320)).toNat - 8320 + 48)) = l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨subscript_unsubscript_digit hd (h hd (.head _)).1 (h hd (.head _)).2,
           ih (fun c hc => h c (.tail _ hc))⟩

open AzPolynomial in
theorem parseSubscriptChars_natToSubscriptChars (n : ℕ) :
    parseSubscriptChars (natToSubscriptChars n) = some n := by
  unfold parseSubscriptChars natToSubscriptChars
  simp only [List.map_map, Function.comp_def,
    show ('0' : Char).toNat = 48 from by decide,
    show ('₀' : Char).toNat = 8320 from by decide]
  rw [subscript_map_cancel _ (fun c hc => by
    have := mem_natToChars_only_digits n c hc
    constructor <;> [exact (by decide : ('0' : Char).toNat = 48) ▸ this.1;
                     exact (by decide : ('9' : Char).toNat = 57) ▸ this.2])]
  exact parseNatChars_natToChars n

/-- Convert a natural number to a string of Unicode subscript digits. -/
private def natToSubscript (n : ℕ) : String := String.ofList (natToSubscriptChars n)

open AzPolynomial in
theorem mem_natToSubscriptChars_range (n : ℕ) (c : Char) (h : c ∈ natToSubscriptChars n) :
    c.toNat ≥ 8320 ∧ c.toNat ≤ 8329 := by
  simp only [natToSubscriptChars, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  have ⟨hge, hle⟩ := mem_natToChars_only_digits n d hd
  simp only [show ('0' : Char).toNat = 48 from by decide,
             show ('9' : Char).toNat = 57 from by decide,
             show ('₀' : Char).toNat = 8320 from by decide] at hge hle ⊢
  constructor <;> (rw [charOfNat_toNat_small (d.toNat - 48 + 8320) (by omega)]; omega)

private theorem lowercase_not_syntax (c : Char) (hge : c.toNat ≥ 97) (hle : c.toNat ≤ 122) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

private theorem subscript_not_syntax (c : Char) (hge : c.toNat ≥ 8320) (hle : c.toNat ≤ 8329) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

/-- A variable indexed by `Fin n`, displayed as `x₀`, `x₁`, etc. -/
@[ext]
structure IndexedVar (n : ℕ) where
  val : Fin n
  deriving DecidableEq

namespace IndexedVar

/-- Shorthand constructor: `X 5` creates an `IndexedVar` with index 5. -/
abbrev X {n : ℕ} (i : Fin n) : IndexedVar n := ⟨i⟩

instance {n : ℕ} : LinearOrder (IndexedVar n) :=
  LinearOrder.lift' (fun v => v.val) (fun _ _ h => IndexedVar.ext h)

instance {n : ℕ} : Ord (IndexedVar n) where
  compare a b := compare a.val b.val

instance {n : ℕ} : ToString (IndexedVar n) where
  toString v := s!"x{natToSubscript v.val}"

instance {n : ℕ} : Repr (IndexedVar n) where
  reprPrec v _ := s!"X{natToSubscript v.val}"

def toChars {n : ℕ} (v : IndexedVar n) : List Char :=
  ['x'] ++ natToSubscriptChars v.val

def parse {n : ℕ} (cs : List Char) : Option (IndexedVar n) :=
  match cs with
  | 'x' :: rest => do
    let k ← parseSubscriptChars rest
    if h : k < n then some ⟨⟨k, h⟩⟩ else none
  | _ => none

theorem parse_toChars {n : ℕ} (v : IndexedVar n) :
    IndexedVar.parse (IndexedVar.toChars v) = some v := by
  simp only [toChars, parse, List.cons_append, List.nil_append]
  rw [parseSubscriptChars_natToSubscriptChars]
  simp [v.val.isLt]

/-- Embed `IndexedVar n` into `IndexedVar m` when `n ≤ m`. -/
def embed {n m : ℕ} (h : n ≤ m) (v : IndexedVar n) : IndexedVar m :=
  ⟨Fin.castLE h v.val⟩

theorem embed_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (embed h) := by
  intro a b hab
  simp only [embed, IndexedVar.mk.injEq] at hab
  exact IndexedVar.ext (Fin.castLE_injective h hab)

theorem embed_mono {n m : ℕ} (h : n ≤ m) : Monotone (embed h) := by
  intro a b hab
  exact hab

instance {n : ℕ} : Var (IndexedVar n) n where
  toFin v := v.val
  ofFin i := ⟨i⟩
  ofFin_toFin _ := rfl
  toFin_ofFin _ := rfl

instance {n : ℕ} : ParseableVar (IndexedVar n) n where
  toChars v := ['x'] ++ natToSubscriptChars v.val
  parseChars cs := match cs with
    | 'x' :: rest => do
      let k ← parseSubscriptChars rest
      if h : k < n then some ⟨⟨k, h⟩⟩ else none
    | _ => none
  parse_toChars v := by
    simp only [List.cons_append, List.nil_append]
    rw [parseSubscriptChars_natToSubscriptChars]
    simp [v.val.isLt]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact lowercase_not_syntax 'x' (by decide) (by decide)
    · have ⟨hge, hle⟩ := mem_natToSubscriptChars_range v.val c hc
      exact subscript_not_syntax c hge hle

end IndexedVar

/-- A variable named by a lowercase letter: `'a'`, `'b'`, `'c'`, ..., `'z'`.
    `n` is the number of variables in scope (at most 26).
    Stores the raw character, so construction is natural: `⟨'a', by omega⟩`. -/
structure AbcVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'a'.toNat ∧ ch.toNat ≤ 'z'.toNat ∧ ch.toNat - 'a'.toNat < n
  deriving DecidableEq

namespace AbcVar

/-- The zero-based index of this variable (0 for 'a', 1 for 'b', etc.). -/
def index {n : ℕ} (v : AbcVar n) : Fin n :=
  ⟨v.ch.toNat - 'a'.toNat, v.is_valid.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : AbcVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  congr 1; rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega

instance {n : ℕ} : LinearOrder (AbcVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (AbcVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (AbcVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (AbcVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : AbcVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (AbcVar n) :=
  if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧ c.toNat - 'a'.toNat < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : AbcVar n) :
    AbcVar.parse v.ch = some v := by
  simp only [parse, dif_pos v.is_valid]

/-- Embed `AbcVar n` into `AbcVar m` when `n ≤ m`. -/
def embed {n m : ℕ} (h : n ≤ m) (v : AbcVar n) : AbcVar m :=
  ⟨v.ch, ⟨v.is_valid.1, v.is_valid.2.1, Nat.lt_of_lt_of_le v.is_valid.2.2 h⟩⟩

theorem embed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (embed h : AbcVar n → AbcVar m) := by
  intro ⟨a, _⟩ ⟨b, _⟩ hab; simp [embed] at hab; congr

theorem embed_mono {n m : ℕ} (h : n ≤ m) :
    Monotone (embed h : AbcVar n → AbcVar m) := by
  intro a b hab; exact hab

/-- Construct an `AbcVar` from a `Fin n` index (0 → 'a', 1 → 'b', etc.). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : AbcVar n :=
  ⟨Char.ofNat ('a'.toNat + i.val), by
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide]
    rw [charOfNat_toNat_small (97 + i.val) (by omega)]
    omega⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : AbcVar n) :
    AbcVar.ofIndex hn (AbcVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1
  simp only [show ('a' : Char).toNat = 97 from by decide] at hge ⊢
  rw [show 97 + (v.ch.toNat - 97) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    AbcVar.index (AbcVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('a' : Char).toNat = 97 from by decide]
  rw [charOfNat_toNat_small (97 + i.val) (by omega)]
  omega

instance {n : ℕ} [Fact (n ≤ 26)] : Var (AbcVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParseableVar (AbcVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧ c.toNat - 'a'.toNat < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dif_pos v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide] at hge hle
    exact lowercase_not_syntax v.ch hge hle

end AbcVar

/-- Maps an abc-index (0 = 'a', ..., 25 = 'z') to an xyz-rank:
    x(0), y(1), z(2), w(3), v(4), ..., a(25).
    This generalizes the convention where the 4th spatial axis is 'w'. -/
private def xyzRank (abcIdx : ℕ) : ℕ :=
  if abcIdx ≥ 23 then abcIdx - 23 else 25 - abcIdx

/-- Inverse of `xyzRank`: maps an xyz-rank back to an abc-index. -/
private def xyzUnrank (rank : ℕ) : ℕ :=
  if rank < 3 then rank + 23 else 25 - rank

private theorem xyzRank_xyzUnrank (r : ℕ) (h : r < 26) :
    xyzRank (xyzUnrank r) = r := by
  simp [xyzRank, xyzUnrank]; split <;> split <;> omega

private theorem xyzUnrank_xyzRank (i : ℕ) (h : i ≤ 25) :
    xyzUnrank (xyzRank i) = i := by
  simp [xyzRank, xyzUnrank]; split <;> split <;> omega

/-- A variable with ordering x, y, z, w, v, u, ..., a.
    Stores the raw character with a validity proof.
    Construction: `⟨'x', by omega⟩`, `⟨'y', by omega⟩`, etc. -/
structure XyzVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'a'.toNat ∧ ch.toNat ≤ 'z'.toNat ∧
    xyzRank (ch.toNat - 'a'.toNat) < n
  deriving DecidableEq

namespace XyzVar

/-- The zero-based xyz-rank of this variable (0 for 'x', 1 for 'y', 2 for 'z', 3 for 'w', ...). -/
def index {n : ℕ} (v : XyzVar n) : Fin n :=
  ⟨xyzRank (v.ch.toNat - 'a'.toNat), v.is_valid.2.2⟩

private theorem xyzRank_injective :
    ∀ a b : ℕ, a ≤ 25 → b ≤ 25 → xyzRank a = xyzRank b → a = b := by
  intro a b ha hb h; simp [xyzRank] at h; split at h <;> split at h <;> omega

private theorem index_injective {n : ℕ} : Function.Injective (index : XyzVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  simp only [show 'a'.toNat = 97 from by decide,
             show 'z'.toNat = 122 from by decide] at ha hb h ⊢
  have hab := xyzRank_injective _ _ (by omega) (by omega) h
  congr 1; rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega

instance {n : ℕ} : LinearOrder (XyzVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (XyzVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (XyzVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (XyzVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : XyzVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (XyzVar n) :=
  if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧
      xyzRank (c.toNat - 'a'.toNat) < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : XyzVar n) :
    XyzVar.parse v.ch = some v := by
  simp only [parse, dif_pos v.is_valid]

/-- Embed `XyzVar n` into `XyzVar m` when `n ≤ m`. -/
def embed {n m : ℕ} (h : n ≤ m) (v : XyzVar n) : XyzVar m :=
  ⟨v.ch, ⟨v.is_valid.1, v.is_valid.2.1, Nat.lt_of_lt_of_le v.is_valid.2.2 h⟩⟩

theorem embed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (embed h : XyzVar n → XyzVar m) := by
  intro ⟨a, _⟩ ⟨b, _⟩ hab; simp [embed] at hab; congr

theorem embed_mono {n m : ℕ} (h : n ≤ m) :
    Monotone (embed h : XyzVar n → XyzVar m) := by
  intro a b hab; exact hab

/-- Construct an `XyzVar` from a `Fin n` rank (0 → 'x', 1 → 'y', 2 → 'z', 3 → 'w', ...). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : XyzVar n :=
  ⟨Char.ofNat ('a'.toNat + xyzUnrank i.val), by
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide]
    have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
    rw [charOfNat_toNat_small (97 + xyzUnrank i.val) (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [show 97 + xyzUnrank i.val - 97 = xyzUnrank i.val from by omega]
    rw [xyzRank_xyzUnrank i.val (by omega)]
    exact i.isLt⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : XyzVar n) :
    XyzVar.ofIndex hn (XyzVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1; have hle := v.is_valid.2.1
  simp only [show ('a' : Char).toNat = 97 from by decide,
             show ('z' : Char).toNat = 122 from by decide] at hge hle ⊢
  rw [xyzUnrank_xyzRank (v.ch.toNat - 97) (by omega)]
  rw [show 97 + (v.ch.toNat - 97) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    XyzVar.index (XyzVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('a' : Char).toNat = 97 from by decide]
  have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
  rw [charOfNat_toNat_small (97 + xyzUnrank i.val) (by omega)]
  rw [show 97 + xyzUnrank i.val - 97 = xyzUnrank i.val from by omega]
  rw [xyzRank_xyzUnrank i.val (by omega)]

instance {n : ℕ} [Fact (n ≤ 26)] : Var (XyzVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParseableVar (XyzVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧
        xyzRank (c.toNat - 'a'.toNat) < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dif_pos v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide] at hge hle
    exact lowercase_not_syntax v.ch hge hle

end XyzVar

end Azurite
