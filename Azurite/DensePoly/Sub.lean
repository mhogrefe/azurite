import Azurite.DensePoly.Basic
import Azurite.DensePoly.Neg
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

variable {R : Type _} [Ring R] [DecidableEq R]

-- The difference array for subtraction
private abbrev subArray (p q : DensePoly R) :=
  Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
    p.coeff i.val - q.coeff i.val)

-- Helper lemmas (same pattern as add)
omit [DecidableEq R] in
private lemma sub_coeff_eq_zero_of_size_le (p : DensePoly R) (n : ℕ) (h : p.coeffs.size ≤ n) :
    p.coeff n = 0 := by
  simp [coeff, Array.getElem?_eq_none h]

omit [Ring R] [DecidableEq R] in
private lemma sub_back_ofFn {n : ℕ} (hn : 0 < n) (f : Fin n → R) :
    (Array.ofFn f).back? = some (f ⟨n - 1, by omega⟩) := by
  unfold Array.back?; simp [show n - 1 < n from by omega]

omit [DecidableEq R] in
private lemma sub_coeff_at_leading (p : DensePoly R) (m : ℕ) (hm : m = p.coeffs.size)
    (hp : 0 < p.coeffs.size) :
    p.coeff (m - 1) = p.coeffs[p.coeffs.size - 1]'(by omega) := by
  simp [coeff, hm, show p.coeffs.size - 1 < p.coeffs.size from by omega]

omit [DecidableEq R] in
private lemma sub_back_eq_some_zero_of_leading (p : DensePoly R) (hp : 0 < p.coeffs.size)
    (h : p.coeffs[p.coeffs.size - 1]'(by omega) = 0) : p.coeffs.back? = some 0 := by
  unfold Array.back?; simp [show p.coeffs.size - 1 < p.coeffs.size from by omega, h]

omit [DecidableEq R] in
private lemma sub_back_ne_zero_of_ne_size (p q : DensePoly R)
    (hps : 0 < p.coeffs.size) (hqs : 0 < q.coeffs.size)
    (hne : p.coeffs.size ≠ q.coeffs.size) :
    (subArray p q).back? ≠ some 0 := by
  rw [sub_back_ofFn (by omega : 0 < max p.coeffs.size q.coeffs.size)]
  intro h; simp only [Option.some.injEq] at h
  by_cases hpq : p.coeffs.size > q.coeffs.size
  · rw [sub_coeff_eq_zero_of_size_le q _ (by omega), sub_zero,
        sub_coeff_at_leading p _ (by omega) hps] at h
    exact p.last_ne_zero (sub_back_eq_some_zero_of_leading p hps h)
  · rw [sub_coeff_eq_zero_of_size_le p _ (by omega), zero_sub] at h
    have : q.coeff (max p.coeffs.size q.coeffs.size - 1) = q.coeffs[q.coeffs.size - 1]'(by omega) :=
      sub_coeff_at_leading q _ (by omega) hqs
    rw [this] at h
    have hq0 : q.coeffs[q.coeffs.size - 1]'(by omega) = 0 := neg_eq_zero.mp h
    exact q.last_ne_zero (sub_back_eq_some_zero_of_leading q hqs hq0)

/-- Subtracts two DensePolynomials in a single traversal. Short-circuits when
    either is zero, and skips normalization when sizes differ. -/
def sub (p q : DensePoly R) : DensePoly R :=
  if hps : p.coeffs.size = 0 then -q
  else if hqs : q.coeffs.size = 0 then p
  else if _ : p.coeffs.size = q.coeffs.size then
    normalize (subArray p q)
  else ⟨subArray p q, sub_back_ne_zero_of_ne_size p q (by omega) (by omega) ‹_›⟩

instance : Sub (DensePoly R) := ⟨sub⟩

-- Testing the implementation using Integer polynomials
#guard (parseDensePoly (R := ℤ) "x^2+1").get! - (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2-x-1").get!
#guard (parseDensePoly (R := ℤ) "x^2+x").get! - (parseDensePoly (R := ℤ) "x^2+1").get! == (parseDensePoly (R := ℤ) "x-1").get!
#guard (parseDensePoly (R := ℤ) "x^2").get! - (parseDensePoly (R := ℤ) "x^2").get! == (0 : DensePoly ℤ)
#guard (0 : DensePoly ℤ) - (parseDensePoly (R := ℤ) "x").get! == (parseDensePoly (R := ℤ) "-x").get!

end Azurite.DensePoly
