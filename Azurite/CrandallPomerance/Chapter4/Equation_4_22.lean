/-
  Crandall–Pomerance, equation (4.22): given (4.21) — `p^w ∣ M` for
  `M = r^(p−1) − 1` — there are integers `a_p, b_p` with

    `M / (p^w u_p) = a_p / b_p`,   `b_p ≡ 1 (mod p)`,      (4.22)

  stated integrally: `M · b = p^w · u · a` with `b ≡ 1 (mod p)`.
  This is the exponent identity behind the character chain of the
  proof of Theorem 4.4.6,

    `χ(r) = χ(r)^b ≡ G^(M b) = G^(p^w u a) ≡ χ(l)^a (mod r)`:

  raising to the `b`-th power is harmless (`χ` has order `p` and
  `b ≡ 1`), and the identity converts the Lemma-4.4.2 exponent `M`
  into the step-3/4 exponent `p^w u`.

  Proof: write `M = p^w m`; cancel `g = gcd(m, u)` to `m = g m'`,
  `u = g u'` with `m u' = u m'`; then `p ∤ u'` and Bézout
  (`exists_mul_modEq`) supplies `t` with `u' t ≡ 1 (mod p)`, so
  `a = m' t`, `b = u' t` work.
-/
import Azurite.CrandallPomerance.Chapter4.Equation_4_21

namespace Azurite

namespace CP

/-- **Equation (4.22)**: from `p^w ∣ M` (equation (4.21)), integers
`a`, `b` with `M b = p^w u a` and `b ≡ 1 (mod p)`. -/
theorem eq_4_22 {p w u M : ℕ} (hp : p.Prime) (hu : ¬p ∣ u)
    (hM : p ^ w ∣ M) :
    ∃ a b : ℕ, M * b = p ^ w * u * a ∧ b ≡ 1 [MOD p] := by
  obtain ⟨m, rfl⟩ := hM
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left m u
  obtain ⟨u', hu'⟩ := Nat.gcd_dvd_right m u
  have hpu' : ¬p ∣ u' := fun hd => hu (hu' ▸ hd.mul_left (Nat.gcd m u))
  obtain ⟨t, ht⟩ := exists_mul_modEq p u' 1 hp.pos (by
    rw [Nat.Coprime.gcd_eq_one
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu'))])
  refine ⟨m' * t, u' * t, ?_, ht⟩
  have hkey : m * u' = u * m' := by
    conv_lhs => rw [hm']
    conv_rhs => rw [hu']
    ring
  calc p ^ w * m * (u' * t) = m * u' * t * p ^ w := by ring
    _ = u * m' * t * p ^ w := by rw [hkey]
    _ = p ^ w * u * (m' * t) := by ring

end CP

end Azurite
