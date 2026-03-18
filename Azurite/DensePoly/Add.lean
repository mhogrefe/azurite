import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

/-- Typeclass for semirings where `a + b = 0` implies `a = 0` and `b = 0`.
    When this holds, polynomial addition never needs normalization. -/
class NoAddCancellation (R : Type _) [Add R] [Zero R] where
  add_eq_zero : ∀ a b : R, a + b = 0 → a = 0 ∧ b = 0

instance : NoAddCancellation ℕ where
  add_eq_zero := fun _ _ => Nat.eq_zero_of_add_eq_zero

variable {R : Type _} [Semiring R] [DecidableEq R]

-- The sum array for addition
private abbrev addArray (p q : DensePoly R) :=
  Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
    p.coeff i.val + q.coeff i.val)

-- Helper lemmas
omit [DecidableEq R] in
private lemma coeff_eq_zero_of_size_le (p : DensePoly R) (n : ℕ) (h : p.coeffs.size ≤ n) :
    p.coeff n = 0 := by
  simp [coeff, Array.getElem?_eq_none h]

omit [Semiring R] [DecidableEq R] in
private lemma back_ofFn {n : ℕ} (hn : 0 < n) (f : Fin n → R) :
    (Array.ofFn f).back? = some (f ⟨n - 1, by omega⟩) := by
  unfold Array.back?; simp [show n - 1 < n from by omega]

omit [DecidableEq R] in
private lemma coeff_at_leading (p : DensePoly R) (m : ℕ) (hm : m = p.coeffs.size)
    (hp : 0 < p.coeffs.size) :
    p.coeff (m - 1) = p.coeffs[p.coeffs.size - 1]'(by omega) := by
  simp [coeff, hm, show p.coeffs.size - 1 < p.coeffs.size from by omega]

omit [DecidableEq R] in
private lemma back_eq_some_zero_of_leading (p : DensePoly R) (hp : 0 < p.coeffs.size)
    (h : p.coeffs[p.coeffs.size - 1]'(by omega) = 0) : p.coeffs.back? = some 0 := by
  unfold Array.back?; simp [show p.coeffs.size - 1 < p.coeffs.size from by omega, h]

omit [DecidableEq R] in
private lemma add_back_ne_zero_of_ne_size (p q : DensePoly R)
    (hps : 0 < p.coeffs.size) (hqs : 0 < q.coeffs.size)
    (hne : p.coeffs.size ≠ q.coeffs.size) :
    (addArray p q).back? ≠ some 0 := by
  rw [back_ofFn (by omega : 0 < max p.coeffs.size q.coeffs.size)]
  intro h; simp only [Option.some.injEq] at h
  by_cases hpq : p.coeffs.size > q.coeffs.size
  · rw [coeff_eq_zero_of_size_le q _ (by omega), add_zero,
        coeff_at_leading p _ (by omega) hps] at h
    exact p.last_ne_zero (back_eq_some_zero_of_leading p hps h)
  · rw [coeff_eq_zero_of_size_le p _ (by omega), zero_add,
        coeff_at_leading q _ (by omega) hqs] at h
    exact q.last_ne_zero (back_eq_some_zero_of_leading q hqs h)

omit [DecidableEq R] in
private lemma add_back_ne_zero_no_cancel [NoAddCancellation R]
    (p q : DensePoly R) (hps : 0 < p.coeffs.size) (hqs : 0 < q.coeffs.size) :
    (addArray p q).back? ≠ some 0 := by
  rw [back_ofFn (by omega : 0 < max p.coeffs.size q.coeffs.size)]
  intro h; simp only [Option.some.injEq] at h
  have ⟨ha, hb⟩ := NoAddCancellation.add_eq_zero _ _ h
  by_cases hpq : p.coeffs.size ≥ q.coeffs.size
  · rw [coeff_at_leading p _ (by omega) hps] at ha
    exact p.last_ne_zero (back_eq_some_zero_of_leading p hps ha)
  · rw [coeff_at_leading q _ (by omega) hqs] at hb
    exact q.last_ne_zero (back_eq_some_zero_of_leading q hqs hb)

/-- Adds two DensePolynomials. Short-circuits when either is zero,
    and skips normalization when sizes differ. -/
def add (p q : DensePoly R) : DensePoly R :=
  if hps : p.coeffs.size = 0 then q
  else if hqs : q.coeffs.size = 0 then p
  else if _ : p.coeffs.size = q.coeffs.size then
    normalize (addArray p q)
  else ⟨addArray p q, add_back_ne_zero_of_ne_size p q (by omega) (by omega) ‹_›⟩

instance (priority := default) : Add (DensePoly R) := ⟨add⟩

/-- Specialized add for semirings with no additive cancellation (e.g., ℕ).
    Never calls `normalize`; provably equal as polynomials to `add`. -/
def addNoCancel [NoAddCancellation R] (p q : DensePoly R) : DensePoly R :=
  if hps : p.coeffs.size = 0 then q
  else if hqs : q.coeffs.size = 0 then p
  else ⟨addArray p q, add_back_ne_zero_no_cancel p q (by omega) (by omega)⟩

instance (priority := high) [NoAddCancellation R] : Add (DensePoly R) := ⟨addNoCancel⟩

-- Testing ℤ (uses add via default instance, normalizes same-size cancellation)
#guard (parseDensePoly (R := ℤ) "x^2+1").get! + (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+x+3").get!
#guard (parseDensePoly (R := ℤ) "x^2+x").get! + (parseDensePoly (R := ℤ) "-x^2+1").get! == (parseDensePoly (R := ℤ) "x+1").get!
#guard (parseDensePoly (R := ℤ) "x^2").get! + (parseDensePoly (R := ℤ) "-x^2").get! == (0 : DensePoly ℤ)
#guard (0 : DensePoly ℤ) + (parseDensePoly (R := ℤ) "x").get! == (parseDensePoly (R := ℤ) "x").get!

-- Testing ℕ (uses addNoCancel via high-priority instance, never normalizes)
#guard (parseDensePoly (R := ℕ) "x^2+1").get! + (parseDensePoly (R := ℕ) "x+2").get! == (parseDensePoly (R := ℕ) "x^2+x+3").get!
#guard (0 : DensePoly ℕ) + (parseDensePoly (R := ℕ) "x^2+1").get! == (parseDensePoly (R := ℕ) "x^2+1").get!
#guard (parseDensePoly (R := ℕ) "3").get! + (parseDensePoly (R := ℕ) "5").get! == (parseDensePoly (R := ℕ) "8").get!

end Azurite.DensePoly

