/-
  **Soundness of the Lucas–Pratt certificate checker**: a passing check
  PROVES `Nat.Prime` (`checkPrattLink_sound`, `checkPrattChain_sound`),
  by Mathlib's `lucas_primality` — the checked conditions say exactly
  that the witness has full order `p − 1` in `F_p^×`.

  On top sits the PROOF-CARRYING GENERATOR `findProvenPrime`: it re-checks
  the certificate found by `findPrattPrime` under a dependent `if` and
  returns `{n : AzNat // Nat.Prime n.toNat}` — a runtime-generated prime
  carrying a genuine primality proof, ready to instantiate
  `Fact (Nat.Prime q.toNat)` for the modular-factorization pipelines.
-/
import Azurite.AzNat.Pratt
import Azurite.AzNat.Equiv.IsPrime
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzZMod.Instances
import Mathlib.NumberTheory.LucasPrimality

namespace Azurite

namespace AzNat

/-- `certProduct` computes the product of the prime powers. -/
theorem toNat_certProduct : ∀ l : List (AzNat × ℕ),
    (certProduct l).toNat = (l.map (fun qe => qe.1.toNat ^ qe.2)).prod := by
  intro l
  induction l with
  | nil => rfl
  | cons qe rest ih =>
    obtain ⟨q, e⟩ := qe
    rw [certProduct, toNat_mul, toNat_pow, List.map_cons, List.prod_cons, ih]

/-- **Soundness of one link**: if every previously certified value is
prime and the link checks, then `p` is prime (Lucas). -/
theorem checkPrattLink_sound {certified : List AzNat} {p a : AzNat}
    {factors : List (AzNat × ℕ)}
    (hcert : ∀ c ∈ certified, Nat.Prime c.toNat)
    (h : checkPrattLink certified p a factors = true) :
    Nat.Prime p.toNat := by
  rw [checkPrattLink] at h
  by_cases h1 : 1 < p.toNat
  case neg => rw [dite_eq_right h1] at h; exact Bool.noConfusion h
  rw [dite_eq_left h1] at h
  have : NeZero p.toNat := ⟨by omega⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨hprod, hfac⟩, hferm, hord⟩ := h
  -- the `p − 1` facts
  have hM1 : (p - 1).toNat = p.toNat - 1 := by rw [toNat_sub, toNat_one]
  have hprod' : (factors.map (fun qe => qe.1.toNat ^ qe.2)).prod
      = p.toNat - 1 := by
    rw [← toNat_certProduct, hprod, hM1]
  -- the witness in `ZMod`
  refine lucas_primality p.toNat ((a.toNat : ZMod p.toNat)) ?_ ?_
  · -- Fermat
    have := congrArg AzZMod.toZMod hferm
    rwa [AzZMod.toZMod_powAzNat, AzZMod.toZMod_ofAzNat, AzZMod.toZMod_one,
      hM1] at this
  · -- full order
    intro q hq hqdvd
    -- `q` is one of the listed factor bases
    rw [← hprod'] at hqdvd
    have hqdvd' := (Prime.dvd_prod_iff hq.prime).mp hqdvd
    obtain ⟨x, hxmem, hqx⟩ := hqdvd'
    obtain ⟨qe, hqe, rfl⟩ := List.mem_map.mp hxmem
    have hqbase : q ∣ qe.1.toNat := hq.dvd_of_dvd_pow hqx
    have hbaseprime : Nat.Prime qe.1.toNat := by
      rcases hfac qe hqe with hmem | hsmall
      · exact hcert _ hmem
      · exact (isPrime_eq_true_iff _).mp hsmall
    have hqeq : q = qe.1.toNat :=
      (Nat.prime_dvd_prime_iff_eq hq hbaseprime).mp hqbase
    -- transport the checked non-identity
    intro hone
    apply hord qe hqe
    apply AzZMod.toZMod_injective
    rw [AzZMod.toZMod_powAzNat, AzZMod.toZMod_ofAzNat, AzZMod.toZMod_one,
      toNat_div, hM1, ← hqeq]
    exact hone

/-- **Soundness of a chain**: every link's `p` is prime. -/
theorem checkPrattChain_sound :
    ∀ (links : List PrattLink) (certified : List AzNat),
      (∀ c ∈ certified, Nat.Prime c.toNat) →
      checkPrattChain certified links = true →
      ∀ l ∈ links, Nat.Prime (l.1).toNat := by
  intro links
  induction links with
  | nil => intro certified _ _ l hl; exact absurd hl (List.not_mem_nil)
  | cons link rest ih =>
    intro certified hcert h l hl
    obtain ⟨p, a, factors⟩ := link
    rw [checkPrattChain, Bool.and_eq_true] at h
    have hp : Nat.Prime p.toNat := checkPrattLink_sound hcert h.1
    rcases List.mem_cons.mp hl with rfl | hl
    · exact hp
    · refine ih (p :: certified) ?_ h.2 l hl
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hp
      · exact hcert c hc

/-- **The proof-carrying prime generator**: search for a Proth-shaped
prime and return it TOGETHER with its primality proof (the certificate
found by the search is re-checked under a dependent `if`, and soundness
converts the check into `Nat.Prime`).  Ready to instantiate
`Fact (Nat.Prime q.toNat)` for the modular-factorization pipelines. -/
def findProvenPrime (m : ℕ) (seed : UInt64) (attempts k₀ : ℕ) :
    Option {n : AzNat // Nat.Prime n.toNat} :=
  match findPrattPrime m seed attempts k₀ with
  | none => none
  | some (p, a, factors) =>
    if h : checkPrattLink [] p a factors = true then
      some ⟨p, checkPrattLink_sound (by simp) h⟩
    else none

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

-- proven primes, generated at runtime: the value carries `Nat.Prime`
#guard ((findProvenPrime 16 0 64 3).map (fun s => s.val.toNat))
  == some 2424833                       -- 37·2^16 + 1
#guard ((findProvenPrime 61 0 64 3).map (fun s => s.val.toNat))
  == some 122209679488325779457         -- 53·2^61 + 1
-- a 128-bit proven prime (k = 1171; the search scans ~600 candidates)
#guard (findProvenPrime 128 0 1024 3).isSome

end Tests
