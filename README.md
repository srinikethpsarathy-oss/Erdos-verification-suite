# Erdős Prime Divisibility Conjecture — Verification Suite

Computational verification code for the paper:

**"An effective proof of the Erdős prime divisibility conjecture for binomial coefficients"**
*Sriniketh Parthasarathy, 2026*
Submitted to the Journal of Experimental Mathematics (JXM).

## The Conjecture

For every triple of integers satisfying 1 ≤ i < j ≤ n/2 and n ≥ 2j, there exists a prime p ≥ i such that p divides gcd(C(n,i), C(n,j)).

## What's Here

| File | Purpose |
|------|---------|
| `erdos_verification_suite.py` | Primary verification — 9 claims including brute-force over 110M triples (n ≤ 4400, i ≤ 23), FO triple classification, and lemma checks |
| `erdos_independent_check.py` | Independent second implementation with a deliberately different architecture, cross-validates through n = 1000 |

## Running

Python 3.10+, no external dependencies.

```bash
# Full suite (takes several hours for the main sweep)
python3 erdos_verification_suite.py

# Independent check (faster, covers n ≤ 1000)
python3 erdos_independent_check.py
```

## Results

- **110,109,924 triples** checked, **zero counterexamples**
- **8 fully obstructed triples** found — all have i prime, all witnessed by p = i:

| (n, i, j) | Failing primes > i | Witness |
|---|---|---|
| (10, 3, 5) | {5} | p = 3 |
| (16, 2, 6) | {3, 5} | p = 2 |
| (28, 3, 14) | {7, 13} | p = 3 |
| (28, 5, 14) | {7, 13} | p = 5 |
| (244, 3, 122) | {11, 61} | p = 3 |
| (512, 2, 147) | {7, 73} | p = 2 |
| (2048, 2, 713) | {23, 89} | p = 2 |
| (2188, 3, 1094) | {547, 1093} | p = 3 |

## License

MIT
