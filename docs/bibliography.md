# Bibliography

The textbooks, papers and software that Azurite formalizes, implements or builds on.
Each entry says where in the library it is used. Abbreviations in parentheses are the
ones used in docstrings and in `docs/module_map.md`.

## Provenance of the code

Azurite is released under the Apache License 2.0, and its code is written from the
published descriptions cited below, not derived from existing implementations. In
particular, no code is derived from GMP or from other copyleft-licensed libraries, and
the only material taken from Malachite is the author's own original Malachite code
(the `RationalSequence` and exhaustive-generation designs); the parts of Malachite that
are themselves derived from GMP or FLINT are not used. Algorithms such as Karatsuba and
Toom–Cook multiplication, divide-and-conquer division, division by invariant integers
and binary GCD are implemented from the papers and textbooks listed here. References
to GMP in the library are to Lean's built-in `Nat`, whose runtime is GMP-backed and
which serves as the benchmark baseline.

## Texts formalized

The `BasuPollackRoy/`, `GathenGerhard/`, `CrandallPomerance/` and `CohenLenstra/`
directories follow these sources statement by statement.

- **(BPR)** Saugata Basu, Richard Pollack, Marie-Françoise Roy. *Algorithms in Real
  Algebraic Geometry*, 2nd ed. Algorithms and Computation in Mathematics 10.
  Springer, 2006. — `Azurite/BasuPollackRoy/` (Chapters 1–4, 8, 10), the signed
  subresultant, Cauchy index and Tarski query algorithms in `AzPolynomial/`, the
  determinant, rank, signature and characteristic-polynomial algorithms in `AzMatrix/`,
  and `AzFormula/`.
- **(GG)** Joachim von zur Gathen, Jürgen Gerhard. *Modern Computer Algebra*, 3rd ed.
  Cambridge University Press, 2013. — `Azurite/GathenGerhard/Chapter14/` and the
  finite-field factorization rail in `AzPolynomial/` (distinct-degree factorization,
  equal-degree splitting, Ben-Or's irreducibility test).
- **(C&P)** Richard Crandall, Carl Pomerance. *Prime Numbers: A Computational
  Perspective*, 2nd ed. Springer, 2005. — `Azurite/CrandallPomerance/` (Chapter 2:
  Chinese remaindering and Garner's algorithm; Chapter 4: primality proving), the
  `n − 1`, `n + 1` and finite-field tests in `AzNat/` and `AzPolynomial/`, and the Gauss
  sum test.
- **(CL)** Henri Cohen, Hendrik W. Lenstra, Jr. Primality testing and Jacobi sums.
  *Mathematics of Computation* 42 (1984), no. 165, 297–330. — `Azurite/CohenLenstra/`
  (the `Theorem_*`, `Proposition_*`, `Lemma_*`, `Method_*` files), `Azurite/APRCL/`.
- **(CLI)** Henri Cohen, Arjen K. Lenstra. Implementation of a new primality test.
  *Mathematics of Computation* 48 (1987), no. 177, 103–121, with supplement S1–S4. —
  `Azurite/CohenLenstra/Impl_*.lean`, `Azurite/APRCL/` (the certificate checker and the
  (5.5) selection).
- Leonard M. Adleman, Carl Pomerance, Robert S. Rumely. On distinguishing prime
  numbers from composite numbers. *Annals of Mathematics* (2) 117 (1983), no. 1,
  173–206. — the origin of the APR-CL test; not formalized directly.

## Algorithm sources

- **(MCA)** Richard P. Brent, Paul Zimmermann. *Modern Computer Arithmetic*.
  Cambridge Monographs on Applied and Computational Mathematics 18. Cambridge
  University Press, 2010. — `AzNat/`: binary GCD (Algorithm 1.18), Toom–Cook
  multiplication (§1.3), divide-and-conquer division, integer roots (§1.5).
- Niels Möller, Torbjörn Granlund. Improved division by invariant integers. *IEEE
  Transactions on Computers* 60 (2011), no. 2, 165–175. — `UInt64/Reciprocal.lean`,
  `UInt64/Div2By1.lean`, `UInt64/Div3By2.lean`, `AzNat/Div/Schoolbook.lean`
  (Algorithms 2, 4, 5, 6, 7 and the reciprocal table).
- **(GCL)** Keith O. Geddes, Stephen R. Czapor, George Labahn. *Algorithms for
  Computer Algebra*. Kluwer Academic Publishers, 1992. — `AzPolynomial/`: squarefree
  factorization (Algorithm 8.2), polynomial GCD and content (Chapter 7).
- **(TAOCP)** Donald E. Knuth. *The Art of Computer Programming, Volume 2:
  Seminumerical Algorithms*, 3rd ed. Addison-Wesley, 1997. — pseudo-remainder
  (Algorithm R in `AzPolynomial/PRem.lean`), the rational addition pattern in
  `AzRationalFunction/`, the two-correction division step.
- Anatolii Karatsuba, Yuri Ofman. Multiplication of many-digital numbers by
  automatic computers. *Doklady Akademii Nauk SSSR* 145 (1962), 293–294; English
  translation in *Soviet Physics Doklady* 7 (1963), 595–596. — `AzNat/Mul/`,
  `AzPolynomial/` Karatsuba multiplication.
- Andrei L. Toom. The complexity of a scheme of functional elements realizing the
  multiplication of integers. *Soviet Mathematics Doklady* 3 (1963), 714–716; and
  Stephen A. Cook. *On the Minimum Computation Time of Functions*. PhD thesis, Harvard
  University, 1966. — `AzNat/Mul/ToomCook3.lean`.
- Christoph Burnikel, Joachim Ziegler. Fast recursive division. Research Report
  MPI-I-98-1-022, Max-Planck-Institut für Informatik, Saarbrücken, 1998. — the
  divide-and-conquer division in `AzNat/Div/`.
- Josef Stein. Computational problems associated with Racah algebra. *Journal of
  Computational Physics* 1 (1967), 397–405. — the binary GCD in `AzNat/Gcd.lean` and
  `AzInt/` (extended form).
- Harvey L. Garner. The residue number system. *IRE Transactions on Electronic
  Computers* EC-8 (1959), 140–147. — `CrandallPomerance/Chapter2/Algorithm_2_1_7.lean`.
- David Y. Y. Yun. On square-free decomposition algorithms. *Proceedings of SYMSAC
  '76*, ACM, 1976, 26–35. — `AzPolynomial/SquarefreeFactorization.lean`,
  `AzMvPolynomial/` multivariate Yun.
- David G. Cantor, Hans Zassenhaus. A new algorithm for factoring polynomials over
  finite fields. *Mathematics of Computation* 36 (1981), no. 154, 587–592. —
  `AzPolynomial/EqualDegreeSplitting.lean` (GG Algorithm 14.8).
- Michael Ben-Or. Probabilistic algorithms in finite fields. *Proceedings of the 22nd
  IEEE Symposium on Foundations of Computer Science*, 1981, 394–398. —
  `AzPolynomial/IrreducibleOrFactor.lean`, `GathenGerhard/Chapter14/Theorem_14_2.lean`.
- Elwyn R. Berlekamp. Factoring polynomials over finite fields. *Bell System Technical
  Journal* 46 (1967), 1853–1859. — root finding in `CohenLenstra/Method_10_2.lean`.
- Erwin H. Bareiss. Sylvester's identity and multistep integer-preserving Gaussian
  elimination. *Mathematics of Computation* 22 (1968), 565–578. — `AzMatrix/` Bareiss
  determinant and rank (BPR Algorithm 8.16).
- Jacob T. Schwartz. Fast probabilistic algorithms for verification of polynomial
  identities. *Journal of the ACM* 27 (1980), no. 4, 701–717; and Richard Zippel.
  Probabilistic algorithms for sparse polynomials. *EUROSAM '79*, Lecture Notes in
  Computer Science 72, Springer, 1979, 216–226. — randomized identity checks in the
  multivariate GCD.

## Primality

- Vaughan R. Pratt. Every prime has a succinct certificate. *SIAM Journal on
  Computing* 4 (1975), no. 3, 214–220. — `AzNat/Pratt.lean` (Lucas–Pratt certificates).
- Gary L. Miller. Riemann's hypothesis and tests for primality. *Journal of Computer
  and System Sciences* 13 (1976), no. 3, 300–317; and Michael O. Rabin. Probabilistic
  algorithm for testing primality. *Journal of Number Theory* 12 (1980), no. 1,
  128–138. — `AzNat/MillerRabin.lean`.
- Jon Sorenson, Jonathan Webster. Strong pseudoprimes to twelve prime bases.
  *Mathematics of Computation* 86 (2017), no. 304, 985–1003. — the source of the
  pseudoprime 3317044064679887385961981 used as a guard in `AzNat/IsPrime.lean` and in
  `Examples.lean`.
- François Arnault. Constructing Carmichael numbers which are strong pseudoprimes to
  several bases. *Journal of Symbolic Computation* 20 (1995), no. 2, 151–161. — the
  construction behind `scripts/arnault_pseudoprime.py` and the large composites that
  Miller–Rabin accepts in `Examples.lean` and `Examples/Main.lean`.
- Robert Solovay, Volker Strassen. A fast Monte-Carlo test for primality. *SIAM
  Journal on Computing* 6 (1977), no. 1, 84–85. — Euler liars, in the completeness
  discussion of the Lucas–Lehmer stage (`docs/aprcl_implementation_plan.md`).
- Henry C. Pocklington. The determination of the prime or composite nature of large
  numbers by Fermat's theorem. *Proceedings of the Cambridge Philosophical Society* 18
  (1914–1916), 29–30. — `CrandallPomerance/Chapter4/` (Theorem 4.1.3) and the order
  climbs in `CohenLenstra/`.
- John Brillhart, Derrick H. Lehmer, John L. Selfridge. New primality criteria and
  factorizations of 2^m ± 1. *Mathematics of Computation* 29 (1975), no. 130, 620–647.
  — the BLS tests, C&P Theorems 4.1.5 and 4.2.10.
- Michael A. Morrison. A note on primality testing using Lucas sequences.
  *Mathematics of Computation* 29 (1975), no. 129, 181–182. — the `n + 1` test, C&P
  Theorem 4.2.3.
- Sergei Konyagin, Carl Pomerance. On primes recognizable in deterministic polynomial
  time. In *The Mathematics of Paul Erdős I*, Algorithms and Combinatorics 13,
  Springer, 1997, 176–198. — C&P Theorem 4.1.6 and Algorithm 4.1.7
  (`AzNat/NMinusOneTest.lean`).
- Hendrik W. Lenstra, Jr. Divisors in residue classes. *Mathematics of Computation* 42
  (1984), no. 165, 331–340. — C&P Theorems 4.2.11 and 4.2.12, `lenstraDivisors`.
- Hendrik W. Lenstra, Jr. Galois theory and primality testing. In *Orders and their
  Applications* (Oberwolfach, 1984), Lecture Notes in Mathematics 1142, Springer, 1985,
  169–189. — the finite-field primality test of C&P §4.3 (`AzPolynomial/LenstraTest.lean`).
- Édouard Lucas. Théorie des fonctions numériques simplement périodiques. *American
  Journal of Mathematics* 1 (1878), 184–240 and 289–321; and Derrick H. Lehmer. An
  extended theory of Lucas' functions. *Annals of Mathematics* (2) 31 (1930), 419–448.
  — Lucas sequences and the Lucas–Lehmer test, C&P §4.2.
- François Proth. Théorèmes sur les nombres premiers. *Comptes Rendus de l'Académie des
  Sciences* 87 (1878), 926. — the Proth-form prime generator `findProvenPrime`.
- Théophile Pépin. Sur la formule 2^{2^n} + 1. *Comptes Rendus de l'Académie des
  Sciences* 85 (1877), 329–331. — C&P Theorem 4.1.2.

Classical results used through BPR — Descartes' rule of signs, Sturm's theorem,
Thom's lemma, the Tarski–Seidenberg theorem, Hadamard's inequality, Puiseux series,
Hilbert's Nullstellensatz, Bézout's theorem — are cited from BPR rather than from
their original sources.

## Software

- Leonardo de Moura, Sebastian Ullrich. The Lean 4 theorem prover and programming
  language. *Automated Deduction – CADE 28*, Lecture Notes in Computer Science 12699,
  Springer, 2021, 625–635. <https://lean-lang.org>
- The mathlib Community. The Lean mathematical library. *Proceedings of the 9th ACM
  SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM,
  2020, 367–381. <https://github.com/leanprover-community/mathlib4> — every
  correctness proof in the `Equiv/` directories is an equivalence with a Mathlib object.
- Mikhail Hogrefe. *Malachite*, arbitrary-precision arithmetic in Rust.
  <https://github.com/mhogrefe/malachite> — the source of the `RationalSequence` port
  (`FoerSequence/`), the exhaustive generators (`ExhaustiveGenerator/`), and the
  reference implementation used by `benchmark-charts/`.
- Torbjörn Granlund and the GMP development team. *GNU Multiple Precision Arithmetic
  Library*. <https://gmplib.org> — the backend of Lean's built-in `Nat`, against which
  `AzNat` is benchmarked.
- Patrick Massot. *leanblueprint* and *checkdecls*.
  <https://github.com/PatrickMassot/leanblueprint>,
  <https://github.com/PatrickMassot/checkdecls> — the blueprint toolchain.
- *doc-gen4*. <https://github.com/leanprover/doc-gen4> — API documentation.
- *plotters*. <https://github.com/plotters-rs/plotters> — the chart renderer in
  `benchmark-charts/`.
- OEIS Foundation Inc. *The On-Line Encyclopedia of Integer Sequences*, sequence
  A007814 (the ruler sequence). <https://oeis.org/A007814> — `ExhaustiveGenerator/`.
