# Cycles with Exactly Two Amplifications in GCD-Augmented Fibonacci Recurrences: Reproduction Code and Data

This repository holds the reproduction code and data for the paper

> M. Hawarey, *Cycles with Exactly Two Amplifications in GCD-Augmented Fibonacci Recurrences* (2026). This line will be updated once the paper is published.

The recurrence is C(n) = C(n−1) + C(n−2) + gcd(C(n−1), C(n−2)). Its gcd dynamics is governed by the cofactor map
R(α, β) = (β/g, (α+β+1)/g) with g = gcd(β, α+1). The paper shows that R has cycles with exactly two amplifications
(steps with g > 1) per period, gives twenty-five explicit cycles at ten periods, the smallest of period 188, and proves
their structure. Twelve of them, at the periods 556, 604 and 652, were found during the revision of the paper (rows
14–25 of Table 1).

## Usage

```
pip install cypari2              # PARI/GP bindings, used for factoring and primality proofs
python reproduce.py --quick      # about 10 seconds: a reduced run of every part
python reproduce.py              # full run: about 30 minutes, plus about 1 hour for 'range'
python reproduce.py cycles       # selected parts only
python reproduce.py factorizations further   # checks based on the archived factorizations (version 1.1.0)
```

Requirements: Python 3.10 or later, and `cypari2` for the parts `census`, `extended` and `factorizations` and for the
primality and factor columns of `cycles`. All arithmetic is exact. The script was run with Python 3.13 and PARI/GP
2.17.2. Primality is always proved with PARI's `isprime` in its default setting (a Baillie-Pomerance-Selfridge-Wagstaff
test, then a proof by the p - 1 test or by APR-CL).

Measured run times of the full run, on one core of a virtual machine with two Intel Xeon cores at 2.1 GHz and 7 GB of
memory: `covering` under 1 second, `census` about 3 minutes, `seeds` about 1 minute, `extended` about 23 minutes
(mostly the 90-second limits at the periods that are not completed), `range` about 58 minutes, `factorizations`
about 3 seconds, `further` under 1 second.

## Parts and results

| Part | Result in the paper | Full run prints |
|---|---|---|
| `cycles` | Theorem 7, Table 1, Table A1, Corollary 12 | the 25 cycles of Table 1, each verified from its triple (q, s, h) by direct iteration of R; h and L_q/h in full with their prime factors; writes `table1_full.csv` |
| `covering` | Theorem 9 | 31,080 residue classes mod 240; survivors s ∈ {1, 2, 5, 6}, q ≡ 4, 20 (mod 24) |
| `census` | Theorem 11 (q ≤ 360), Figure 1, Section 6 | 6,249,456 patterns, 97 local survivors, 6 cycles; tallies of the local conditions; writes `figure1_data.csv` |
| `extended` | Theorem 11 (360 < q ≤ 716), proof | with PARI alone and 90 seconds per period: rows 7–13 of Table 1; 16 of the 30 admissible periods completed |
| `t2family` | Proposition 14 | the t = 2 family never carries a cycle |
| `range` | Theorem 15 | 1,634,583,763 congruences; 26 candidates with G > L_q, none a cycle |
| `boundary` | Section 6 | the three single-amplification cycles |
| `seeds` | Section 6 | 24,463 coprime seeds in [1, 200]² reach exactly five cycles |
| `factorizations` | Theorem 11, Appendix A | checks `lucas_factorizations.csv`: every product equals L_q and every listed prime is proved prime |
| `further` | Theorem 11 (360 < q ≤ 716) | restricted search at the 30 admissible periods in (360, 716] with the primes listed in the file; finds rows 7–25 of Table 1 (periods 364, 532, 556, 604, 652 and 692) |

## Data files (unchanged since version 1.1.0)

- `lucas_factorizations.csv`: the factorizations of L_q used in the paper, for every even q ≤ 360 and for the 30
  periods q ≡ 4, 20 (mod 24) in (360, 716]. Columns: `q`, `status` (`complete` or `partial`), `digits_of_Lq`,
  `prime_factors` (separated by spaces, with `^` for exponents) and `composite_cofactors` (empty when complete). The
  factorizations were computed for the paper with PARI/GP 2.17.2 (`factor`) and, for the periods above 360 that PARI
  does not finish within 90 seconds, with GMP-ECM 7.0.5 and longer PARI runs. Every listed prime was proved prime with PARI's `isprime`.
- `table1_full.csv`: all known cycles in full (Table A1 of the paper): q, s, h, L_q/h and the prime
  factors of both multipliers.

The part `extended` factors the primitive part of each Lucas number L_q with a time limit per period (option
`--tlim=SECONDS`, default 90). On a faster machine, or with a larger limit, more periods may be completed; the cycles
found for the periods listed in the paper do not change, and any further cycles found are among rows 14–25 of Table 1.

## Versions

- 1.0.0: first release, with the paper as submitted.
- 1.1.0: parts `factorizations` and `further`; data files; twelve further cycles; multipliers printed in full.
- 1.1.1: labels only. Version 1.1.0 called rows 14–25 of Table 1 and the search above period 360 "Proposition 17", a
  draft label; in the paper they are part of Theorems 7 and 11. No computation, number or data file differs from 1.1.0.

## Citation

Please cite the paper and this software; see `CITATION.cff`.

## License

MIT (see `LICENSE`).
