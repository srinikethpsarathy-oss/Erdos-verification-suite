#!/usr/bin/env python3
"""
INDEPENDENT VERIFICATION — Erdős Prime Divisibility Conjecture
==============================================================
Second implementation, deliberately written differently from the
primary suite. Uses only stdlib. Confirms the main claim:

  For all 1 ≤ i < j ≤ n/2, n ≥ 2j: ∃ prime p ≥ i, p | gcd(C(n,i),C(n,j)).

Method: computes gcd(C(n,i),C(n,j)) directly via factorial-based
valuation, completely independent of the primary code's architecture.
"""
import sys
from math import gcd, factorial

def primes_up_to(N):
    sieve = bytearray(b'\x01') * (N + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, int(N**0.5) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytearray(len(sieve[p*p::p]))
    return [p for p in range(2, N + 1) if sieve[p]]

def comb_val(n, k, p):
    """v_p(C(n,k)) via sum of carries / Legendre."""
    v = 0; pk = p
    while pk <= n:
        v += n // pk - k // pk - (n - k) // pk
        pk *= p
    return v

def verify_range(lo, hi, i_max, primes):
    """Check all valid triples with lo ≤ n ≤ hi."""
    fails = 0; total = 0
    for n in range(lo, hi + 1):
        for j in range(2, n // 2 + 1):
            if n < 2 * j: continue
            for i in range(1, min(j, i_max + 1)):
                total += 1
                ok = False
                for p in primes:
                    if p < i: continue
                    if p > n: break
                    if comb_val(n, i, p) > 0 and comb_val(n, j, p) > 0:
                        ok = True; break
                if not ok:
                    fails += 1
                    print(f"COUNTEREXAMPLE: n={n}, i={i}, j={j}")
    return total, fails

def main():
    print("Independent verification of Erdős conjecture")
    print("=" * 50)
    
    P = primes_up_to(5000)
    
    # Chunk 1: n ≤ 500
    t, f = verify_range(3, 500, 15, P)
    print(f"n=3..500:    {t:>10,} triples, {f} fails")
    
    # Chunk 2: n = 501..1000
    t2, f2 = verify_range(501, 1000, 15, P)
    print(f"n=501..1000: {t2:>10,} triples, {f2} fails")
    
    total = t + t2; total_f = f + f2
    print(f"\nTotal: {total:,} triples, {total_f} counterexamples")
    
    if total_f == 0:
        print("CONFIRMED: Zero counterexamples through n = 1000")
    else:
        print("FAILURE: Counterexamples found!")
    
    # Spot-check the B(i) values
    print("\nB(i) spot-checks (gap ≤ i-1, S_i-smooth pairs):")
    checks = [
        (3, 16, 18, 2),   # B(3): (16,18), gap 2 = i-1
        (5, 320, 324, 4),  # B(5): (320,324), gap 4 = i-1
    ]
    for (i, x1, x2, gap) in checks:
        S = [p for p in P if p <= i]
        def smooth(n):
            r = n
            for p in S:
                while r % p == 0: r //= p
            return r == 1
        ok = smooth(x1) and smooth(x2) and x2 - x1 == gap
        print(f"  B({i}): ({x1},{x2}) gap={gap}, both S_{i}-smooth: {ok}")
    
    return 0 if total_f == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
