#!/usr/bin/env python3
"""reproduce.py: reproduces the computations of
  M. Hawarey, "Cycles with Exactly Two Amplifications in GCD-Augmented Fibonacci Recurrences" (2026).

Recurrence C(n) = C(n-1) + C(n-2) + gcd(C(n-1), C(n-2)); cofactor map R(a, b) = (b/g, (a+b+1)/g), g = gcd(b, a+1).
A state (a, b) has the golden coordinate Y = (2a - b + 1) + (b - a) phi in Z[phi]; the content of x + y phi is gcd(x, y).
A pattern (q1, q2; g1, g2) carries a cycle with exactly two amplifications iff the conditions of Lemma 3 hold.

Parts (labels follow the paper; each part prints the numbers quoted there):
  cycles     Theorem 7, Table 1, Corollary 12(d): every cycle from its triple (q, s, h) alone, by direct iteration
             of R from sigma* = (F_{2q+1}, F_{2q+2}) + (h-1)(F_{q+s+1}, F_{q+s+2}) - h (F_{q+1}, F_{q+2})
  covering   Theorem 9: the 31,080 residue classes mod 240 that survive the local conditions mod 2, 3, 5, 7
  census     Theorem 11 (q <= 360) and Figure 1: every pattern with G = L_q, its first failing condition, the local
             survivors mod 2, 3, 5, 7, and a re-check by direct iteration; writes figure1_data.csv
  extended   Theorem 11 (360 < q <= 716): restricted search (Theorem 9, Proposition 8); per-q factoring time limit
  t2family   Proposition 14: the t = 2 family (m <= 100) never carries a cycle
  range      Theorem 15: all integral candidates with G > L_q allowed by Lemma 13(c), q <= 36
  boundary   Section 6, boundary recovery: the single-amplification cycles (q, g) = (1, 2), (2, 3), (4, 7), q <= 20
  seeds      Section 6: iteration of R from all coprime seeds in [1, 200]^2
  factorizations  Theorem 11, Appendix A: checks the archived file lucas_factorizations.csv (every listed prime is
             proved prime, every product is L_q) and prints its summary
  further    Theorem 11 (360 < q <= 716): restricted search (Corollary 12) at all 30 admissible periods, with long
             multipliers built from the primitive primes listed in lucas_factorizations.csv; no factoring is needed

Version 1.1.0 adds the parts 'factorizations' and 'further' and rows 14-25 of Table 1 (list CYC_NEW),
prints the long multipliers in full with their prime factors (part 'cycles', Table A1), and prints the tallies of the
local conditions (part 'census'). The parts of version 1.0.0 and their results are unchanged.
Version 1.1.1 changes labels only: rows 14-25 of Table 1 and the search above period 360 carried the draft label
'Proposition 17' in version 1.1.0; in the paper they are part of Theorems 7 and 11. No computation, number or data
file differs from version 1.1.0.
Data files: lucas_factorizations.csv, table1_full.csv.

Usage:  python reproduce.py --quick          about 10 s: census q <= 120, extended q <= 411, range q <= 20, seeds <= 60
        python reproduce.py                  full: about 30 min plus about 1 hour for 'range'
        python reproduce.py cycles covering  selected parts;  --tlim=SECONDS sets the factoring limit (default 90)
Requirements: Python >= 3.10; cypari2 (pip install cypari2) for 'census', 'extended', 'factorizations' and the
primality and factor columns of 'cycles'. Primality is always proved with PARI's isprime (flag 0: BPSW test, then a
proof by the p - 1 test or APR-CL). All arithmetic is exact. License: MIT."""
import sys, os, csv, time, multiprocessing as mp
from math import gcd, isqrt, prod
from itertools import product
from collections import Counter

F, L = [0, 1], [2, 1]
def fib(n):
    while len(F) <= n + 2: F.append(F[-1] + F[-2]); L.append(L[-1] + L[-2])
    return F[n]
def luc(n): fib(n); return L[n]
def mul(x, y, m=None):                                    # (a + b phi)(c + d phi), phi^2 = phi + 1
    a, b = x; c, d = y; r = (a*c + b*d, a*d + b*c + b*d)
    return (r[0] % m, r[1] % m) if m else r
def phipow(n, m=None):
    if m is None: return (fib(n - 1), fib(n)) if n >= 1 else (1, 0)
    res, base = (1 % m, 0), (0, 1 % m)
    while n:
        if n & 1: res = mul(res, base, m)
        base = mul(base, base, m); n >>= 1
    return res
def content(w): return gcd(w[0], w[1])
def state_of(Y): a, b = Y; return (a + b - 1, a + 2*b - 1)
def R(s): a, b = s; g = gcd(b, a + 1); return (b // g, (a + b + 1) // g), g
def pisano(r):
    a, b, k = 0, 1, 0
    while True:
        a, b, k = b, (a + b) % r, k + 1
        if (a, b) == (0, 1): return k
PI = {r: pisano(r) for r in (2, 3, 5, 7)}                 # 3, 8, 20, 16
SMALLP = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
SMALL = prod(SMALLP)

def XY(q1, q2, g1, g2):
    """Lemma 2: golden coordinates (X, Y) after the first / second amplification, or None if not integral."""
    q = q1 + q2; G = g1 * g2; d = (G - fib(q - 1), -fib(q)); N = d[0]**2 + d[0]*d[1] - d[1]**2
    conj = (d[0] + d[1], -d[1]); out = []
    for num in (((g1 - 1)*g2 + (g2 - 1)*fib(q1 - 1), (g2 - 1)*fib(q1)), (g1*(g2 - 1) + (g1 - 1)*fib(q2 - 1), (g1 - 1)*fib(q2))):
        w = mul(num, conj)
        if w[0] % N or w[1] % N: return None
        out.append((w[0] // N, w[1] // N))
    return tuple(out)
def first_content(X, Y, q1, q2):
    """Lemma 3(iii): None if all contents are 1, else (side, i, content) of the first content > 1."""
    for side, W, n in (("Y", Y, q1), ("X", X, q2)):
        w = W
        for i in range(n):
            c = content((w[0] - 1, w[1]))
            if c > 1: return side, i, c
            w = mul(w, (0, 1))
    return None
def first_failure(q1, q2, g1, g2):
    """None if the pattern carries a cycle with exactly two amplifications (Lemma 3), else the failing condition."""
    s = XY(q1, q2, g1, g2)
    if s is None: return "not integral"
    X, Y = s; st = state_of(Y)
    if st[0] < 1 or st[1] < 1: return "not positive"
    f = first_content(X, Y, q1, q2)
    if f: return f"{f[0]}, i = {f[1]}"
    return "repeat of a shorter cycle" if X == Y else None
def direct(Y, q1, q2, g1, g2):
    """Direct iteration of R: True iff the state of Y lies on a cycle of least period q with exactly the two
    amplifications at steps q1 - 1 and q - 1, with multipliers g1 and g2."""
    s0 = state_of(Y)
    if s0[0] < 1 or s0[1] < 1 or gcd(*s0) != 1: return False
    s, q, amps = s0, q1 + q2, []
    for j in range(q):
        s, m = R(s)
        if m > 1: amps.append((j, m))
        if s == s0 and j < q - 1: return False
    return s == s0 and amps == [(q1 - 1, g1), (q - 1, g2)]
_loc = {}
def local_ok(r, q, q1, q2, g1, g2):
    """Lemma 4 mod r for G = L_q (Lemma 6): phi^i Y != 1 for i < min(q1, pi(r)), phi^i X != 1 for i < min(q2, pi(r))."""
    P = PI[r]; key = (r, q % P, q1 % P, q2 % P, min(q1, P), min(q2, P), g1 % r, g2 % r)
    if key not in _loc:
        Lq = (2*phipow(q % P, r)[0] + phipow(q % P, r)[1]) % r
        def W(g, k):
            u, v = mul(((Lq - g) % r, 0), phipow(q % P, r), r), mul(((g - 1) % r, 0), phipow((q + k) % P, r), r)
            return ((u[0] + v[0]) % r, (u[1] + v[1]) % r)
        ok = True
        for w, n in ((W(g1, q2), min(q1, P)), (W(g2, q1), min(q2, P))):
            for _ in range(n):
                if w == (1 % r, 0): ok = False; break
                w = mul(w, (0, 1), r)
        _loc[key] = ok
    return _loc[key]
_P = []
def pari():
    if not _P:
        import cypari2; p = cypari2.Pari(); p.allocatemem(2 * 10**9, silent=True); _P.append(p)
    return _P[0]

HERE = os.path.dirname(os.path.abspath(__file__))
def read_factorizations():
    """lucas_factorizations.csv -> {q: (status, [(p, e), ...], [composite cofactors])}."""
    out = {}
    with open(os.path.join(HERE, "lucas_factorizations.csv")) as fi:
        for row in csv.DictReader(fi):
            pe = [(int(t.split("^")[0]), int(t.split("^")[1]) if "^" in t else 1) for t in row["prime_factors"].split()]
            out[int(row["q"])] = (row["status"], pe, [int(c) for c in row["composite_cofactors"].split()])
    return out
def fmt_factors(n, primes, comp=()):
    """n as a product of the given primes; a factor left over must be the product of the composite cofactors 'comp'
    of L_q that are not yet factored, and is printed in square brackets."""
    parts = []
    for p in sorted(primes):
        e = 0
        while n % p == 0: n //= p; e += 1
        if e: parts.append(str(p) if e == 1 else f"{p}^{e}")
    assert n == 1 or n == prod(comp)
    return " * ".join(parts + ([f"[{n}]"] if n > 1 else []))

CYC = [(188, 2, 18049), (236, 5, 39299585040574991646429560062415143), (236, 6, 2871307447985313921708888731089),
       (244, 5, 25553609562771866971783), (244, 6, 52471477541626010209), (268, 2, 27394199849089),
       (364, 5, 1607900243355223), (364, 5, 112739025441223), (364, 5, 2167970958120041964878941094897400376601026388806528443943),
       (532, 5, 1963935786170995308172874586609385961733047712487738064669834056498633369360565230903),
       (692, 2, 25734139343360815502009252332479063945286304136739969), (692, 6, 365418564450128053103699216003150641416769),
       (692, 6, 1627640193104185047895754236771619530198929553121521288865608772205585604958397908108746641186763652209)]
CYC_NEW = [(556, 1, 202636238996806404322047320340239815186169623),
           (604, 2, 1146134421052077514508781114144769),
           (652, 1, 6862459992387646640985182801732832691615891330831600249544889505596968405523597280183),
           (652, 1, 728370715811779241086035320509543720676852318364909874541933887807304317633538100629222769604183),
           (652, 2, 152218087412280529),
           (652, 2, 4682215972495649106931635525559578959733529165345139935180000639204609),
           (652, 2, 496963042881861649021823347258779166653551663461618759325372304819352370253856609),
           (652, 2, 11400762099581095348048392294330704463142437505909226373535266477471982500660997249),
           (652, 2, 9987854582061901661632075252066156397151472306402969825472725248541480129645758571969),
           (652, 6, 496963042881861649021823347258779166653551663461618759325372304819352370253856609),
           (652, 6, 9987854582061901661632075252066156397151472306402969825472725248541480129645758571969),
           (652, 6, 17075645976599186234679196392353322131092635154535015786655910096246976487766358311405972398498459187676528709280887649)]     # rows 14-25 of Table 1, found in the revision
def verify_cycle(q, s, h):
    """Direct iteration of R from sigma*(q, s, h): least period q, multipliers h at step q - s - 1 and L_q/h at step
    q - 1, no other amplification; the content test of Lemma 3 must agree. Returns sigma*."""
    g = luc(q) // h; assert luc(q) % h == 0
    sig = anchor(q, s, h); st, amps, minb = sig, [], sig[1]
    for j in range(q):
        st, m = R(st)
        if m > 1: amps.append((j, m))
        assert j == q - 1 or st != sig
        minb = min(minb, st[1])
    assert st == sig and amps == [(q - s - 1, h), (q - 1, g)] and first_failure(s, q - s, g, h) is None
    assert minb == sig[1] > fib(2*q + 2)
    return sig
def anchor(q, s, h):
    return (fib(2*q+1) + (h-1)*fib(q+s+1) - h*fib(q+1), fib(2*q+2) + (h-1)*fib(q+s+2) - h*fib(q+2))
def part_cycles():
    try: P = pari(); isprime = lambda n: bool(P.isprime(n))
    except ImportError: isprime = lambda n: "?"
    assert luc(188) == 7 * 18049 * 100769 * 153037630649666194962091443041
    print("Table 1, rows 1-13 (q | s | h | h prime | digits of L_q/h | digits of beta*):")
    for q, s, h in CYC:
        g = luc(q) // h; sig = verify_cycle(q, s, h)
        print(f"  {q} | {s} | {h if len(str(h)) <= 40 else f'({len(str(h))} digits)'} | {isprime(h)} | {len(str(g))} | {len(str(sig[1]))}")
    print("  period-188 anchor state (Theorem 7):", anchor(*CYC[0]))
    for row, (q, s, h) in enumerate(CYC_NEW, len(CYC) + 1):
        sig = verify_cycle(q, s, h)
        print(f"Table 1, row {row} (Theorem 7): cycle (q, s, h) = ({q}, {s}, {h}) verified (least period {q}, exactly two "
              f"amplifications, multipliers h and L_q/h); h prime: {isprime(h)}; digits of L_q/h: {len(str(luc(q) // h))}; "
              f"digits of beta*: {len(str(sig[1]))}")
    try: FA = read_factorizations()
    except OSError: FA = {}
    print("Table A1 (row | q | s | h | L_q/h | prime factors of h | prime factors of L_q/h; a factor in square brackets "
          "is a composite cofactor of L_q that is not yet factored):")
    rows = []
    for i, (q, s, h) in enumerate(CYC + CYC_NEW, 1):
        g = luc(q) // h
        primes = [p for p, _ in FA[q][1]] if q in FA else [int(p) for p in pari().factor(luc(q))[0]]
        assert all(isprime(p) is not False for p in primes)
        fh, fg = fmt_factors(h, primes), fmt_factors(g, primes, FA[q][2] if q in FA else ())
        rows.append((i, q, s, h, g, fh, fg, fh.count("*") + 1)); print(f"  {i} | {q} | {s} | {h} | {g} | {fh} | {fg}")
    with open("table1_full.csv", "w") as fo:
        fo.write("row,q,s,h,Lq_over_h,prime_factors_of_h,prime_factors_of_Lq_over_h\n")
        fo.writelines(f"{i},{q},{s},{h},{g},{fh},{fg}\n" for i, q, s, h, g, fh, fg, _ in rows)
    print(f"  number of prime factors of h, rows 1-{len(rows)}: {[r[7] for r in rows]}; table1_full.csv written")
    print(f"cycles: {len(CYC)} verified (least period q, exactly two amplifications, multipliers h and L_q/h); "
          f"every state has beta > F_(2q+2) >= F_378 = {fib(378):.3e} (Corollary 12)")

def part_covering():
    M = 240
    def surv(q1, q2): return all(any(local_ok(r, q1 + q2, q1, q2, g1, g2) for g1, g2 in product(range(r), repeat=2)
                                     if (g1*g2 - luc(q1 + q2)) % r == 0) for r in PI)
    left, n = {}, 0
    for s in range(1, 20):
        for c in range(M):
            if (s + c) % 2: continue
            n += 1
            if surv(s, c + M): left.setdefault(s, set()).add((s + c) % M)
    both = 0
    for c1 in range(M):
        for c2 in range(M):
            if (c1 + c2) % 2: continue
            n += 1; both += surv(c1 + M, c2 + M)
    print(f"Theorem 9: {n:,} classes mod 240; surviving short lengths s and classes of q mod 24: "
          f"{ {s: sorted({x % 24 for x in v}) for s, v in left.items()} }; both lengths >= 20: {both} classes survive")

def part_census(QC):
    P = pari(); tot, kinds, loc, gen, rechk, rows, t0 = 0, Counter(), 0, [], 0, [], time.time()
    locp, lpf, allp = Counter(), Counter(), set()
    for q in range(2, QC + 1, 2):
        Lq = luc(q); f = P.factor(Lq); ps = [int(p) for p in f[0]]; es = [int(e) for e in f[1]]
        assert prod(p**e for p, e in zip(ps, es)) == Lq and all(bool(P.isprime(p)) for p in ps)
        allp.update(ps); divs = [1]
        for p, e in zip(ps, es): divs = [d * p**k for d in divs for k in range(e + 1)]
        divs.sort(); n = sym = lq = gq = 0
        for g1 in divs:
            g2 = Lq // g1
            if g1 < 2 or g2 < 2: continue
            for q1 in range(1, q):
                q2 = q - q1
                if (q1, g1) > (q2, g2): continue
                n += 1; sym += (q1, g1) == (q2, g2); tot += 1
                X, Y = XY(q1, q2, g1, g2)
                fl = next((r for r in PI if not local_ok(r, q, q1, q2, g1, g2)), 0); lq += fl == 0; locp[fl] += 1
                fc = first_content(X, Y, q1, q2)
                if fc is None:
                    assert X != Y and direct(Y, q1, q2, g1, g2); gen.append((q, min(q1, q2))); gq += 1; rechk += 1
                    continue
                side, i, c = fc
                lpf[next((p for p in SMALLP if c % p == 0), 99)] += 1
                kinds["start not coprime" if (side, i) == ("Y", 0) else "larger multiplier" if (side, i) == ("X", 0)
                      else "early segment 1" if side == "Y" else "early segment 2"] += 1
                if gcd(c, SMALL) == 1 or n % 2000 == 0:
                    assert not direct(Y, q1, q2, g1, g2); rechk += 1
        assert 2 * n == (len(divs) - 2) * (q - 1) + sym          # pattern count = divisor count identity
        loc += lq; rows.append((q, n, lq, gq))
    with open("figure1_data.csv", "w") as fo:
        fo.write("q,patterns,local_survivors_mod_2357,cycles\n"); fo.writelines(f"{a},{b},{c},{d}\n" for a, b, c, d in rows)
    print(f"Theorem 11: G = L_q, even q <= {QC}: {tot:,} patterns; first failing condition {dict(kinds)}; "
          f"{loc} local survivors mod 2, 3, 5, 7 at q = {[r[0] for r in rows if r[2]]}; {len(gen)} cycles (q, s): {gen}; "
          f"{rechk:,} patterns re-checked by direct iteration; figure1_data.csv written  [{time.time() - t0:.0f} s]")
    print(f"  least prime among 2, 3, 5, 7 whose local condition fails: { {r: locp[r] for r in PI} }; none: {locp[0]}")
    print(f"  least prime factor of the first failing content: { {p: lpf[p] for p in (2, 3, 5, 7)} }; "
          f"11 to 47: {sum(lpf[p] for p in SMALLP[4:])}; above 47: {lpf[99]}")
    print(f"  factorizations: {QC // 2} Lucas numbers, {len(allp)} distinct primes, each proved prime (PARI isprime); "
          f"the largest has {len(str(max(allp)))} digits")

def _factor(n, conn):
    import cypari2; p = cypari2.Pari(); p.allocatemem(10**9, silent=True); f = p.factor(n)
    conn.send([(int(a), int(b)) for a, b in zip(f[0], f[1])])
def factor_tl(n, tl):
    a, b = mp.Pipe(False); pr = mp.Process(target=_factor, args=(n, b)); pr.start(); pr.join(tl)
    if pr.is_alive(): pr.terminate(); return None
    return a.recv()
def order_is_4q(r, q):
    if phipow(4*q, r) != (1, 0): return False
    n, ps, p = 4*q, set(), 2
    while p * p <= n:
        while n % p == 0: ps.add(p); n //= p
        p += 1
    if n > 1: ps.add(n)
    return all(phipow(4*q // p, r) != (1, 0) for p in ps)
def part_extended(QMAX, TLIM):
    P = pari(); done, found, t0 = [], [], time.time()
    for q in range(362, QMAX + 1):
        if q % 24 not in (4, 20): continue
        m, Lq = q // 4, luc(q); cof, known = Lq, []
        for d in range(1, m):                                     # primes of L_4d, d | m, d < m (not primitive)
            if m % d == 0:
                for p in P.factor(luc(4*d))[0]:
                    while cof % int(p) == 0: cof //= int(p); known.append(int(p))
        f = factor_tl(cof, TLIM) if cof > 1 else []
        primes = sorted(set(known) | {p for p, _ in (f or [])})
        complete = f is not None and prod(known) * prod(p**e for p, e in f) == Lq and all(bool(P.isprime(p)) for p in primes)
        prim = [p for p in primes if p != 2 and order_is_4q(p, q)]  # primitive prime divisors of F_2q (Proposition 8)
        hs = [1]
        for p in prim:
            e, t = 0, Lq
            while t % p == 0: t //= p; e += 1
            hs = [h * p**k for h in hs for k in range(e + 1)]
        for h in (h for h in hs if h >= 3):
            for s in (1, 2, 5, 6):
                if first_failure(s, q - s, Lq // h, h) is None:
                    sig = anchor(q, s, h); st, amps = sig, []
                    for j in range(q):
                        st, mm = R(st)
                        if mm > 1: amps.append((j, mm))
                    assert st == sig and amps == [(q - s - 1, h), (q - 1, Lq // h)]
                    found.append((q, s, h))
        if complete: done.append(q)
    print(f"Theorem 11: 360 < q <= {QMAX}, q = 4, 20 mod 24: list complete for q = {done} ({len(done)} periods; "
          f"factoring limit {TLIM} s); cycles (q, s, h): {found}  [{time.time() - t0:.0f} s]")

def part_factorizations():
    P = pari(); FA = read_factorizations(); t0 = time.time(); allp, part = set(), []
    for q, (status, pe, comp) in sorted(FA.items()):
        assert prod(p**e for p, e in pe) * prod(comp) == luc(q), q
        assert all(bool(P.isprime(p)) for p, _ in pe), q
        assert all(c > 1 and not bool(P.ispseudoprime(c)) for c in comp) and (status == "complete") == (not comp), q
        allp.update(p for p, _ in pe)
        if comp: part.append((q, [len(str(c)) for c in comp]))
    ev = [q for q in FA if q <= 360]; ad = [q for q in FA if q > 360]
    assert ev == list(range(2, 361, 2)) and ad == [q for q in range(362, 717) if q % 24 in (4, 20)]
    print(f"Theorem 11, Appendix A: lucas_factorizations.csv holds L_q for the {len(ev)} even q <= 360 and the {len(ad)} "
          f"periods q = 4, 20 mod 24 in (360, 716]; {len(FA) - len(part)} factorizations are complete; {len(allp)} distinct "
          f"primes, each proved prime (PARI isprime), the largest with {len(str(max(allp)))} digits; every product equals "
          f"L_q. Not fully factored (q, digits of the composite cofactors): {part}  [{time.time() - t0:.0f} s]")

def part_further():
    FA = read_factorizations(); t0, comp_q, part, found, nc, npp, npc = time.time(), [], [], [], 0, 0, 0
    for q, (status, pe, comp) in sorted(FA.items()):
        if q <= 360: continue
        Lq = luc(q); prim = [p for p, _ in pe if p != 2 and order_is_4q(p, q)]; hs = [1]
        for p in prim:
            e, t = 0, Lq
            while t % p == 0: t //= p; e += 1
            hs = [h * p**k for h in hs for k in range(e + 1)]
        n = 0
        for h in (h for h in hs if h >= 3):
            for s in (1, 2, 5, 6):
                n += 1
                if first_failure(s, q - s, Lq // h, h) is None: verify_cycle(q, s, h); found.append((q, s, h))
        if status == "complete": comp_q.append(q); nc += n
        else: part.append((q, len(prim), n, [len(str(c)) for c in comp])); npp += len(prim); npc += n
    assert sorted(found) == sorted(c for c in CYC + CYC_NEW if c[0] > 360)
    print(f"Theorem 11 (360 < q <= 716): admissible periods: {len(comp_q)} fully factored, q = {comp_q}, with {nc} candidates "
          f"(h, s); {len(part)} not fully factored, as (q, known primitive primes, candidates, digits of composite cofactors): "
          f"{part}, in total {npp} primes and {npc} candidates; cycles found (q, s, h): {found}; these are rows "
          f"7-25 of Table 1: True  [{time.time() - t0:.0f} s]")

def part_t2family():
    for m in range(2, 101, 2):
        n = luc(m); assert luc(3*m) + 2 == (n - 1)**2 * (n + 2)
        assert XY(m, 2*m, n - 1, (n - 1)*(n + 2)) is not None and first_failure(m, 2*m, n - 1, (n - 1)*(n + 2)) is not None
    print("Proposition 14: the t = 2 family (even m <= 100, q = 3m) is integral and never carries a cycle")

def tmax(q, q1):                                                  # Lemma 13(c)
    q2 = q - q1; Fq, Lq, P = fib(q), luc(q), fib(q1) * fib(q2)
    u = (P + isqrt(P*P + 4*P*(Lq + Fq + 1))) // 2 + 2
    while u > 0 and u*u >= (Lq + Fq + 1 + u) * P: u -= 1
    return Fq + 1 + max(u, 0)
def part_range(QB):
    t0, cands, iters = time.time(), [], 0
    for q in range(3, QB + 1):
        Fq, Lq, eps = fib(q), luc(q), (-1)**q
        for q1 in range(1, q // 2 + 1):
            q2 = q - q1; Fq2, Fqq2 = fib(q2), fib(q + q2)
            for t in range(1, tmax(q, q1) + 1):                  # Lemma 13(a): a linear congruence in g1
                iters += 1
                G = Lq + t; D = G*t + eps; K = Fqq2 + t*Fq2; c1 = (K - Fq) % D; c0 = (K - Fq*G) % D; gm = gcd(c1, D)
                if c0 % gm: continue
                Dp = D // gm; g0 = (c0 // gm) * pow(c1 // gm, -1, Dp) % Dp if Dp > 1 else 0
                g1 = g0 if g0 >= 2 else g0 + Dp * ((2 - g0 + Dp - 1) // Dp)
                while g1 <= G // 2:
                    if G % g1 == 0 and XY(q1, q2, g1, G // g1) is not None:
                        assert first_failure(q1, q2, g1, G // g1) is not None, ("CYCLE WITH G > L_q", q, q1, g1)
                        cands.append((q, q1, g1, G // g1, t))
                    g1 += Dp
    def fam(q, q1, g1, g2, t):
        if 2*q1 == q and g1 == g2: return "symmetric"
        if t == 2 and q % 6 == 0:
            m = q // 3; n = luc(m)
            if {(q1, g1), (q - q1, g2)} == {(m, n - 1), (2*m, (n - 1)*(n + 2))}: return "t = 2 family"
        return "sporadic"
    kinds = Counter(fam(*c) for c in cands)
    print(f"Theorem 15: 3 <= q <= {QB}: {iters:,} congruences; {len(cands)} integral candidates with G > L_q {dict(kinds)}; "
          f"sporadic (q1, q2; g1, g2): {[(c[1], c[0] - c[1], c[2], c[3]) for c in cands if fam(*c) == 'sporadic']}; "
          f"none carries a cycle  [{time.time() - t0:.0f} s]")

def part_boundary():
    found = []
    for q in range(1, 21):
        for g in range(2, 2*luc(q) + 3):
            D = g*g - luc(q)*g + (-1)**q
            if D <= 0: continue
            d = (g - fib(q - 1), -fib(q)); w = mul((g - 1, 0), (d[0] + d[1], -d[1]))
            if w[0] % D or w[1] % D: continue
            X = (w[0] // D, w[1] // D); assert g == (luc(q) if q % 2 == 0 else luc(q) + 1)
            okc = all(content(((lambda u: (u[0] - 1, u[1]))(mul(phipow(i), X)))) == 1 for i in range(q))
            if okc and content(((lambda u: (u[0] - 1, u[1]))(mul(phipow(q), X)))) == g: found.append((q, g, state_of(X)))
    print("Section 6, boundary recovery (q <= 20): single-amplification cycles (q, g, state):", found)

def part_seeds(BOX=200, CAP=3000):
    cyc, n = {}, 0
    for a in range(1, BOX + 1):
        for b in range(1, BOX + 1):
            if gcd(a, b) != 1: continue
            n += 1; s, seen = (a, b), set()
            for _ in range(CAP):
                if s in seen: break
                seen.add(s); s, _g = R(s)
            else: continue
            start, mem, amps = s, [], 0
            while True:
                mem.append(s); s, g = R(s); amps += g > 1
                if s == start: break
            cyc.setdefault(min(mem), (len(mem), amps))
    print(f"Section 6: {n:,} coprime seeds in [1, {BOX}]^2 reach {len(cyc)} cycles (period, amplifications):",
          sorted(cyc.values()))

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]; quick = "--quick" in sys.argv
    tl = next((int(a.split("=")[1]) for a in sys.argv if a.startswith("--tlim=")), 90)
    run = {"cycles": part_cycles, "covering": part_covering, "census": lambda: part_census(120 if quick else 360),
           "extended": lambda: part_extended(411 if quick else 716, tl), "t2family": part_t2family,
           "range": lambda: part_range(20 if quick else 36), "boundary": part_boundary,
           "seeds": lambda: part_seeds(60 if quick else 200), "factorizations": part_factorizations,
           "further": part_further}
    for p in args or list(run):
        run[p]()
