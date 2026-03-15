#!/usr/bin/env python3
"""
ERDŐS PRIME DIVISIBILITY CONJECTURE — Verification Suite (Revision 6)
=====================================================================
Run: python3 erdos_verification_suite.py
Zero dependencies beyond stdlib. Prints PASS/FAIL per claim.

Claims:
  1. Zero counterexamples (n ≤ 4400, i ≤ 23)
  2. Exactly 8 FO triples (paper's §5.2 definition)
  3. All 8 FO triples have prime i and p = i witnesses
  4. Appendix B: 10 "hard" triples classification
  5. Brun–Titchmarsh: 2i/ln(i) < i-1 for i ≥ 10
  6. i = 1 algebraic proof: ∃ p|n with p|C(n,j)
  7. Tame-Prime Lemma (⇐): p ∈ (j-i,j], p>i → p|C(j,i)
  8. Tame Valuation: v_q(C(j,i))=1 for tame q
  9. Bridge Lemma correctness
"""
import sys, time, math

def sieve_primes(limit):
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

PRIMES = sieve_primes(5000)
PRIME_SET = set(PRIMES)

def vp(n, p):
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def vp_binom(n, k, p):
    val = 0; pp = p
    while pp <= n:
        val += n // pp - k // pp - (n - k) // pp
        pp *= p
    return val

def is_smooth(n, bound):
    rem = n
    for p in PRIMES:
        if p > bound: break
        while rem % p == 0: rem //= p
    return rem == 1

def largest_prime_factor(n):
    lpf = 1; rem = n
    for p in PRIMES:
        if p * p > rem: break
        while rem % p == 0: lpf = max(lpf, p); rem //= p
    if rem > 1: lpf = rem
    return lpf

def find_witness(n, i, j):
    for p in PRIMES:
        if p < i: continue
        if p > n: break
        if vp_binom(n, i, p) >= 1 and vp_binom(n, j, p) >= 1:
            return p
    return None

def is_fo(n, i, j):
    """Paper §5.2: P is j-smooth AND no prime > i witnesses."""
    for k in range(i):
        if not is_smooth(n - k, j):
            return False
    for p in PRIMES:
        if p <= i: continue
        if p > n: break
        if vp_binom(n, i, p) >= 1 and vp_binom(n, j, p) >= 1:
            return False
    return True

# ═══════════ CLAIMS 1-3: Main verification ═══════════

def verify_claims_1_2_3(n_max=4400, i_max=23):
    print("=" * 60)
    print(f"CLAIMS 1-3: n ≤ {n_max}, i ≤ {i_max}")
    print("=" * 60)
    total = 0; cex = 0; fo_list = []; t0 = time.time()
    for n in range(3, n_max + 1):
        for j in range(2, n // 2 + 1):
            if n < 2 * j: continue
            for i in range(1, min(j, i_max + 1)):
                total += 1
                w = find_witness(n, i, j)
                if w is None:
                    cex += 1
                    print(f"  COUNTEREXAMPLE: ({n},{i},{j})")
                # FO check only for j-smooth (skip Case A quickly)
                if any(largest_prime_factor(n-k) > j for k in range(i)):
                    continue
                if is_fo(n, i, j):
                    fo_list.append((n, i, j, w))
        if n % 500 == 0:
            print(f"  n={n}: {total:,} triples, {time.time()-t0:.0f}s",
                  file=sys.stderr)
    
    elapsed = time.time() - t0
    print(f"  Triples: {total:,}, Counterexamples: {cex}")
    print(f"  FO triples: {len(fo_list)}")
    for t in sorted(fo_list):
        failing = []
        n,i,j,w = t
        for r in PRIMES:
            if r <= i or r > j: continue
            if any((n-k)%r==0 for k in range(i)):
                if not(vp_binom(n,i,r)>=1 and vp_binom(n,j,r)>=1):
                    failing.append(r)
        print(f"    ({n},{i},{j}): witness={w}, failing={failing}")
    print(f"  Time: {elapsed:.0f}s")
    
    ok1 = cex == 0
    ok2 = len(fo_list) == 8
    ok3 = all(t[1] in PRIME_SET and t[3] == t[1] for t in fo_list)
    
    print(f"  Claim 1 (zero counterexamples): {'PASS' if ok1 else 'FAIL'}")
    print(f"  Claim 2 (8 FO triples): {'PASS' if ok2 else 'FAIL'}")
    print(f"  Claim 3 (all FO: i prime, p=i): {'PASS' if ok3 else 'FAIL'}")
    return ok1, ok2, ok3

# ═══════════ CLAIM 4: Appendix B ═══════════

def verify_claim_4():
    print("\n" + "=" * 60)
    print("CLAIM 4: 10 hard triples")
    print("=" * 60)
    triples = [(10,3,5),(16,3,7),(16,3,8),(22,3,11),(26,3,13),
               (27,3,13),(28,3,13),(27,4,13),(28,4,13),(28,5,13)]
    from math import comb
    fo_c = 0; untame_c = 0; notlonely_c = 0
    for (n,i,j) in triples:
        w = find_witness(n,i,j)
        f = is_fo(n,i,j)
        # Check untame escape: prime r > i, r|P, r ∤ C(j,i)
        has_untame = False
        for r in PRIMES:
            if r <= i or r > j: continue
            if any((n-k)%r==0 for k in range(i)):
                if comb(j,i) % r != 0:
                    has_untame = True; break
        # Check not-lonely
        has_notlonely = False
        if not f and not has_untame:
            for r in PRIMES:
                if r <= i or r > j: continue
                hit_i = any((n-k)%r==0 for k in range(i))
                hit_ji = any((n-k)%r==0 for k in range(i,j))
                if hit_i and hit_ji:
                    has_notlonely = True; break
        if f: fo_c += 1; lbl = "FO"
        elif has_untame: untame_c += 1; lbl = "Untame"
        elif has_notlonely: notlonely_c += 1; lbl = "Not-lonely"
        else: lbl = "other"
        print(f"  ({n:>2},{i},{j:>2}): w={w}, {lbl}")
    ok = fo_c == 1 and untame_c == 7 and notlonely_c == 2
    print(f"  FO:{fo_c} Untame:{untame_c} Not-lonely:{notlonely_c}")
    print(f"  Claim 4: {'PASS' if ok else 'FAIL'}")
    return ok

# ═══════════ CLAIM 5: Brun-Titchmarsh ═══════════

def verify_claim_5():
    print("\n" + "=" * 60)
    print("CLAIM 5: 2i/ln(i) < i-1 for i >= 10")
    print("=" * 60)
    ok = all(2*i/math.log(i) < i-1 for i in range(10, 10001))
    print(f"  i=10..10000: {'all hold' if ok else 'FAILURE'}")
    print(f"  Claim 5: {'PASS' if ok else 'FAIL'}")
    return ok

# ═══════════ CLAIM 6: i=1 algebraic ═══════════

def verify_claim_6():
    print("\n" + "=" * 60)
    print("CLAIM 6: i=1, some p|n witnesses")
    print("=" * 60)
    fails = 0
    for n in range(4, 2001):
        for j in range(2, n//2+1):
            if n < 2*j: continue
            found = False
            for p in PRIMES:
                if p > n: break
                if n % p != 0: continue
                if vp_binom(n, j, p) >= 1:
                    found = True; break
            if not found: fails += 1
    ok = fails == 0
    print(f"  Failures: {fails}")
    print(f"  Claim 6: {'PASS' if ok else 'FAIL'}")
    return ok

# ═══════════ CLAIMS 7-9: Lemma checks ═══════════

def verify_claim_7():
    print("\n" + "=" * 60)
    print("CLAIM 7: Tame-Prime (backward): p ∈ (j-i,j], p>i → p|C(j,i)")
    print("=" * 60)
    from math import comb
    f = sum(1 for j in range(2,200) for i in range(1,j)
            for p in PRIMES if j-i < p <= j and p > i and comb(j,i)%p != 0)
    ok = f == 0
    print(f"  Failures: {f}")
    print(f"  Claim 7: {'PASS' if ok else 'FAIL'}")
    return ok

def verify_claim_8():
    print("\n" + "=" * 60)
    print("CLAIM 8: Tame Valuation: v_q(C(j,i))=1")
    print("=" * 60)
    f = sum(1 for j in range(2,200) for i in range(1,j)
            for q in PRIMES if j-i < q <= j and q > i and vp_binom(j,i,q) != 1)
    ok = f == 0
    print(f"  Failures: {f}")
    print(f"  Claim 8: {'PASS' if ok else 'FAIL'}")
    return ok

def verify_claim_9():
    print("\n" + "=" * 60)
    print("CLAIM 9: Bridge Lemma")
    print("=" * 60)
    fails = 0; total = 0
    for n in range(4, 300):
        for j in range(2, n//2+1):
            if n < 2*j: continue
            for i in range(1, min(j, 10)):
                for k in range(i):
                    for p in PRIMES:
                        if p < i or p > j: continue
                        v = vp(n-k, p)
                        if v < 2 or p**v <= j: continue
                        total += 1
                        if not(vp_binom(n,i,p)>=1 and vp_binom(n,j,p)>=1):
                            fails += 1
    ok = fails == 0
    print(f"  Tested: {total}, Failures: {fails}")
    print(f"  Claim 9: {'PASS' if ok else 'FAIL'}")
    return ok

# ═══════════ MAIN ═══════════

def main():
    print("+" + "=" * 58 + "+")
    print("|  ERDOS CONJECTURE — VERIFICATION SUITE (Rev 6)         |")
    print("+" + "=" * 58 + "+\n")
    R = {}; t0 = time.time()
    
    # Fast claims first
    R[5] = verify_claim_5()
    R[6] = verify_claim_6()
    R[7] = verify_claim_7()
    R[8] = verify_claim_8()
    R[9] = verify_claim_9()
    R[4] = verify_claim_4()
    
    # Slow claim
    r1, r2, r3 = verify_claims_1_2_3()
    R[1] = r1; R[2] = r2; R[3] = r3
    
    print("\n" + "=" * 60)
    print("FINAL REPORT")
    print("=" * 60)
    all_pass = True
    for c in sorted(R):
        s = "PASS" if R[c] else "FAIL"
        if not R[c]: all_pass = False
        print(f"  Claim {c}: {s}")
    print(f"\n  Total: {time.time()-t0:.0f}s")
    if all_pass:
        print("\n  +== ALL CLAIMS VERIFIED ==+")
    else:
        print("\n  +== SOME CLAIMS FAILED ==+")
    return 0 if all_pass else 1

if __name__ == "__main__":
    sys.exit(main())
