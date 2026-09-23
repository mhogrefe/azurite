# Copyright © 2026 Mikhail Hogrefe
#
# This file is part of Azurite.
#
# Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
# License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.

"""Arnault's construction: a Carmichael number N = p1*p2*p3 with p2 = k2(p1-1)+1, p3 = k3(p1-1)+1,
all p_i = 3 mod 4, and every base a in B a quadratic non-residue mod each p_i.  Then a^((N-1)/2)
= -1 mod N for all a in B, so N is a strong pseudoprime to every base in B.

Reference: F. Arnault, Constructing Carmichael numbers which are strong pseudoprimes to several
bases, J. Symbolic Comput. 20 (1995), 151-161.  Used to produce the composites in Examples.lean
and Examples/Main.lean that Miller-Rabin with Azurite's twelve fixed bases accepts and the APR-CL
test refutes.

Usage: scripts/arnault_pseudoprime.py [digits_of_p1] [seed]"""
import random, sys
from math import gcd

B = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
k2, k3 = 313, 353          # both = 1 mod 4, coprime
digits = int(sys.argv[1]) if len(sys.argv) > 1 else 18
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
random.seed(seed)

def legendre(a, p):
    return pow(a % p, (p - 1) // 2, p)  # 1, p-1 (= -1), or 0

def is_probable_prime(n, rounds=24):
    if n < 2: return False
    for q in SMALL:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for _ in range(rounds):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

SMALL = [q for q in range(2, 2000) if all(q % r for r in range(2, int(q ** 0.5) + 1))]

def crt(residues):  # list of (r, m) with pairwise coprime m
    R, M = 0, 1
    for r, m in residues:
        t = ((r - R) * pow(M, -1, m)) % m
        R, M = R + M * t, M * m
    return R % M, M

# Conditions on p1 modulo each odd base a (mod 4a, but the "mod 4" part is handled by mod 8):
# (a / p1) = (a / p2) = (a / p3) = -1, using that Legendre(a, p) for odd a depends on p mod 4a.
def allowed_mod(a):
    m = 4 * a
    out = []
    for r in range(m):
        if gcd(r, m) != 1 or r % 4 != 3: continue
        ok = True
        for k in (1, k2, k3):
            pr = (k * (r - 1) + 1) % m
            if gcd(pr, m) != 1: ok = False; break   # symbol would be 0: no prime in this class
            # Legendre symbol via a representative prime in the class pr (mod 4a).
            p = pr
            while not is_probable_prime(p): p += m
            if legendre(a, p) != p - 1: ok = False; break
        if ok: out.append(r % a)   # the mod-a part; the mod-4 part is r ≡ 3 mod 4 (fixed below)
    return out

# mod 8: p1 ≡ 3 (mod 8) makes (2/p) = -1 for p1, and for p2, p3 since k2, k3 ≡ 1 mod 4.
assert k2 % 4 == 1 and k3 % 4 == 1
conds = [(3, 8)]
for a in B[1:]:
    S = allowed_mod(a)
    assert S, a
    conds.append((random.choice(S), a))
# Carmichael conditions mod k2 and k3: p1 * p3 ≡ 1 (mod k2), p1 * p2 ≡ 1 (mod k3), p1 ≢ 1 mod k2, k3.
def carm(k, kother):
    return [c for c in range(k) if c != 1 and (c * (kother * (c - 1) + 1)) % k == 1]
C2, C3 = carm(k2, k3), carm(k3, k2)
assert C2 and C3
conds.append((random.choice(C2), k2))
conds.append((random.choice(C3), k3))
r0, M = crt(conds)

lo = 10 ** (digits - 1)
t = random.randrange((lo - r0) // M + 1, (10 * lo - r0) // M)   # p1 anywhere in [lo, 10 lo)
tested = 0
while True:
    p1 = r0 + t * M; t += 1; tested += 1
    p2, p3 = k2 * (p1 - 1) + 1, k3 * (p1 - 1) + 1
    if any(p % q == 0 for p in (p1, p2, p3) for q in SMALL if p != q): continue
    if is_probable_prime(p1) and is_probable_prime(p2) and is_probable_prime(p3):
        N = p1 * p2 * p3
        # sanity: strong pseudoprime to every base in B, and Korselt's criterion
        assert all((N - 1) % (p - 1) == 0 for p in (p1, p2, p3))
        m = (N - 1) // 2
        assert (N - 1) % 4 == 2 and all(pow(a, m, N) == N - 1 for a in B)
        print(f"# tested {tested} candidates")
        print(f"p1 = {p1}\np2 = {p2}\np3 = {p3}\nN = {N}\ndigits(N) = {len(str(N))}")
        break
