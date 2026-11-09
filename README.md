# Cycles with Exactly Two Amplifications in GCD-Augmented Fibonacci Recurrences: Reproduction Code

This repository holds the reproduction code for the paper

> M. Hawarey, *Cycles with Exactly Two Amplifications in GCD-Augmented Fibonacci Recurrences* (2026).

The recurrence is C(n) = C(n−1) + C(n−2) + gcd(C(n−1), C(n−2)). Its gcd dynamics is governed by the cofactor map
R(α, β) = (β/g, (α+β+1)/g) with g = gcd(β, α+1). The paper shows that R has cycles with exactly two amplifications
(steps with g > 1) per period, gives thirteen explicit cycles, the smallest of period 188, and proves their structure.

## Usage

```
pip install cypari2              # PARI/GP bindings, used for factoring and primality proofs
python reproduce.py --quick      # about 10 seconds: a reduced run of every part
python reproduce.py              # full run: about 25 minutes, plus about 1 hour for 'range'
python reproduce.py cycles       # selected parts only
```

Requirements: Python 3.10 or later, and `cypari2` for the parts `census` and `extended` and for the primality column
of `cycles`. All arithmetic is exact. The script was run with Python 3.13 and PARI/GP 2.17.2.

## Parts and results

| Part | Result in the paper | Full run prints |
|---|---|---|
| `cycles` | Theorem 7, Table 1, Corollary 12 | the 13 cycles, each verified from its triple (q, s, h) by direct iteration of R |
| `covering` | Theorem 9 | 31,080 residue classes mod 240; survivors s ∈ {1, 2, 5, 6}, q ≡ 4, 20 (mod 24) |
| `census` | Theorem 11 (q ≤ 360), Figure 1 | 6,249,456 patterns, 97 local survivors, 6 cycles; writes `figure1_data.csv` |
| `extended` | Theorem 11 (360 < q ≤ 716) | 7 further cycles; the list is complete for 16 of the 30 admissible periods |
| `t2family` | Proposition 14 | the t = 2 family never carries a cycle |
| `range` | Theorem 15 | 1,634,583,763 congruences; 26 candidates with G > L_q, none a cycle |
| `boundary` | Section 6 | the three single-amplification cycles |
| `seeds` | Section 6 | 24,463 coprime seeds in [1, 200]² reach exactly five cycles |

The part `extended` factors the primitive part of each Lucas number L_q with a time limit per period (option
`--tlim=SECONDS`, default 90). On a faster machine, or with a larger limit, more periods may be completed; the cycles
found for the periods listed in the paper do not change.

## Citation

Please cite the paper and this software; see `CITATION.cff`.

## License

MIT (see `LICENSE`).
