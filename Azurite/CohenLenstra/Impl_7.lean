/-
  **Implementation paper, §7: examples and running times — recorded
  as test vectors.**

  *Multiprecision.*  Two fixed-length integer kinds: a "multiple"
  (somewhat more bits than `n`) and a "double" (twice as many);
  `+`/`−` stay within a kind, `multiple × multiple → double`,
  `(multiple | double) mod multiple → multiple`, all by the classical
  algorithms [4].  Pascal (≤ 104 digits): 8/16 words of 47 bits;
  Fortran: 16/32 words.  Table 1 (CDC 170/750, ms): add 0.014/0.019,
  mul 0.07/0.21, double-mod-multiple 0.20/0.47 for 8/16 words — the
  16-word multiplication is only `3×` the 8-word one (overhead).
  Our rail: `AzNat` limbs of 64 bits with variable length; the
  "double" is just the product's length.

  *Table 2* (Fortran, 20 random primes per digit size, seconds;
  mean/sd/max/min): totals `50 / 98 / 156 / 246 / 360 / 496` s for
  `100 / 120 / 140 / 160 / 180 / 200` digits; the Jacobi-sum stage
  dominates (`37 → 438` s), then the final trial division
  (`2.3 → 41` s; `t = 55440` divisions, fixed-precision routines not
  skipping leading zeros), then the Lucas–Lehmer stage (`2.2 → 6.7` s);
  trial division to `10⁶` is a flat `8` s (fixed precision).  Our
  benchmark targets are these ratios, not the absolute times.

  *The 247-digit example* `prime247_2_892 ∣ 2^892 + 1` (Cunningham
  table [3]), beyond the Fortran capacity `N` but "lucky": `B = 10⁶`
  gives `l⁻ = {7, 223, 2017, 4001, 162553}`, `l⁺ = {3, 19, 367}`; no
  compositeness test (already probable prime, `m = 0`); flags
  `flag₃ = F, flag₄ = T, flag₅ = F, flag₇ = T, flag₈ = T, flag₉ = F,
  flag₁₁ = F, flag₁₆ = T`; Lucas–Lehmer 14.7 s; the remaining
  `q`-primes (all but `2, 3, 7, 19`) *just* suffice for
  `s₁s₂ > n^(1/2)` with `t = 55440`; all `λ_p` true already in (g);
  Jacobi-sum stage 807 s; 55440 final trial divisions 56 s; total
  under 15 minutes.  Table 3 (`p^k, q, (i1)-time, h`):
  `(3,13,2.1,1), (4,13,1.0,1), (2,23,1.0,0), (11,23,26.3,8),
  (5,41,5.4,3), (8,41,1.0,4), (7,1009,1.1,5), (9,1009,9.9,0),
  (16,1009,1.2,11)` — the `h`-values depend on the generator choice
  in the tables, so they are regression data only for an
  implementation using the same generators.

  Every checkable claim about the 247-digit number is verified below
  against our definitions (`smoothPart`, `s1`, `s2`, `bigEnough`):
  divisibility, `l∓`, the flags, the `q`-prime set, and the
  "just sufficient" `s₁s₂ > n^(1/2)` — which fails as soon as the
  largest `q`-prime is dropped.

  *The 180-digit example* `prime180_table2` (from the Table 2 sample):
  Table 4 total times `378 / 591 / 197` s on CDC 170/750 (16×47-bit
  words) / CDC 205 / Cray 1 (32×24-bit words); the Cray's 64-long
  vectors match the "doubles".
-/
import Azurite.CohenLenstra.Impl_6_1

namespace Azurite

namespace CL

/-- The 247-digit prime factor of `2^892 + 1` proved prime in §7. -/
def prime247_2_892 : ℕ :=
  3876504335317997501469391035319109708663589625180623029822890926723711514115245155566479256098717968310496836053912513303910310541847025911281558587559700056356937703949226241396723616837470247248135048208451745439902122005282381436679587515252273

/-- The 180-digit prime of Table 4 (one of the Table 2 sample). -/
def prime180_table2 : ℕ :=
  339549724935349607481986319204055049743924044985997021775725614091378200404186185545246430931525038059779334403309483454226092284418382591337309620364938100840903721641622176153759

/-- The `B`-smooth part of `N` by trial division (test-vector helper). -/
def smoothPart (B N : ℕ) : ℕ := Id.run do
  let mut m := N
  let mut s := 1
  for d in [2:B+1] do
    while m % d == 0 do
      m := m / d
      s := s * d
  return s

/-- The odd primes `≤ B` dividing `N`, in increasing order. -/
def oddPrimeDivs (B N : ℕ) : List ℕ := Id.run do
  let mut m := N
  let mut l := []
  for d in [2:B+1] do
    if m % d == 0 then
      if d != 2 then l := l ++ [d]
      while m % d == 0 do m := m / d
  return l

/-- The distinct primes of `s₂` for the 247-digit example. -/
def s2primes247 : List ℕ :=
  [5, 11, 13, 17, 23, 29, 31, 37, 41, 43, 61, 67, 71, 73, 89, 113, 127, 181, 199,
   211, 241, 281, 331, 337, 397, 421, 463, 617, 631, 661, 881, 991, 1009, 1321,
   2311, 2521, 3697, 4621, 9241, 18481, 55441]

-- sizes
#guard Nat.log 10 prime247_2_892 + 1 = 247
#guard Nat.log 10 prime180_table2 + 1 = 180
-- a factor of `2^892 + 1`
#guard (2 ^ 892 + 1) % prime247_2_892 = 0
-- (2.1) with `B = 10⁶`: `l⁻`, `l⁺`
#guard oddPrimeDivs 1000000 (prime247_2_892 - 1) = [7, 223, 2017, 4001, 162553]
#guard oddPrimeDivs 1000000 (prime247_2_892 + 1) = [3, 19, 367]
-- (1.3)(d): the flags `n ≡ 1 (mod p^k)` for `p^k ∣ 55440`
#guard (prime247_2_892 % 3 = 1) = false
#guard (prime247_2_892 % 4 = 1) = true
#guard (prime247_2_892 % 5 = 1) = false
#guard (prime247_2_892 % 7 = 1) = true
#guard (prime247_2_892 % 8 = 1) = true
#guard (prime247_2_892 % 9 = 1) = false
#guard (prime247_2_892 % 11 = 1) = false
#guard (prime247_2_892 % 16 = 1) = true
-- the `q`-primes of `e(55440)` are the 45 primes `q` with `q − 1 ∣ 55440`;
-- all but `2, 3, 7, 19` (handled by the Lucas–Lehmer stage) form `s̄₂`
#guard s2primes247.length = 41
#guard (((Nat.divisors 55440).filter fun d => (d + 1).Prime).image (· + 1)).sort (· ≤ ·)
  = ([2, 3, 7, 19] ++ s2primes247).mergeSort
-- (5.2): with `F` the `10⁶`-smooth part of `n² − 1` and `t = 55440`,
-- `s₁ s₂ > n^(1/2)` — and not without the largest `q`-prime
#guard bigEnough prime247_2_892
  (s1 55440 (smoothPart 1000000 (prime247_2_892 - 1)
    * smoothPart 1000000 (prime247_2_892 + 1)))
  (s2 55440 prime247_2_892 s2primes247.prod) = true
#guard bigEnough prime247_2_892
  (s1 55440 (smoothPart 1000000 (prime247_2_892 - 1)
    * smoothPart 1000000 (prime247_2_892 + 1)))
  (s2 55440 prime247_2_892 (s2primes247.erase 55441).prod) = false

end CL

end Azurite
