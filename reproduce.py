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

Usage:  python reproduce.py --quick          about 10 s: census q <= 120, extended q <= 411, range q <= 20, seeds <= 60
        python reproduce.py                  full: about 25 min plus about 1 hour for 'range'
        python reproduce.py cycles covering  selected parts;  --tlim=SECONDS sets the factoring limit (default 90)
Requirements: Python >= 3.10; cypari2 (pip install cypari2) for 'census', 'extended' and the primality column of
'cycles'. All arithmetic is exact. License: MIT."""
import sys, time, multiprocessing as mp
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
SMALL = prod((2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47))

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

CYC = [(188, 2, 18049), (236, 5, 39299585040574991646429560062415143), (236, 6, 2871307447985313921708888731089),
       (244, 5, 25553609562771866971783), (244, 6, 52471477541626010209), (268, 2, 27394199849089),
       (364, 5, 1607900243355223), (364, 5, 112739025441223), (364, 5, 2167970958120041964878941094897400376601026388806528443943),
       (532, 5, 1963935786170995308172874586609385961733047712487738064669834056498633369360565230903),
       (692, 2, 25734139343360815502009252332479063945286304136739969), (692, 6, 365418564450128053103699216003150641416769),
       (692, 6, 1627640193104185047895754236771619530198929553121521288865608772205585604958397908108746641186763652209)]
def anchor(q, s, h):
    return (fib(2*q+1) + (h-1)*fib(q+s+1) - h*fib(q+1), fib(2*q+2) + (h-1)*fib(q+s+2) - h*fib(q+2))
def part_cycles():
    try: P = pari(); isprime = lambda n: bool(P.isprime(n))
    except ImportError: isprime = lambda n: "?"
    assert luc(188) == 7 * 18049 * 100769 * 153037630649666194962091443041
    print("Table 1 (q | s | h | h prime | digits of L_q/h | digits of beta*):")
    for q, s, h in CYC:
        g = luc(q) // h; assert luc(q) % h == 0
        sig = anchor(q, s, h); st, amps, minb = sig, [], sig[1]
        for j in range(q):
            st, m = R(st)
            if m > 1: amps.append((j, m))
            assert j == q - 1 or st != sig
            minb = min(minb, st[1])
        assert st == sig and amps == [(q - s - 1, h), (q - 1, g)] and first_failure(s, q - s, g, h) is None
        assert minb == sig[1] > fib(2*q + 2)
        print(f"  {q} | {s} | {h if len(str(h)) <= 40 else f'({len(str(h))} digits)'} | {isprime(h)} | {len(str(g))} | {len(str(sig[1]))}")
    print("  period-188 anchor state (Theorem 7):", anchor(*CYC[0]))
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
    for q in range(2, QC + 1, 2):
        Lq = luc(q); f = P.factor(Lq); ps = [int(p) for p in f[0]]; es = [int(e) for e in f[1]]
        assert prod(p**e for p, e in zip(ps, es)) == Lq and all(bool(P.isprime(p)) for p in ps)
        divs = [1]
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
                lq += all(local_ok(r, q, q1, q2, g1, g2) for r in PI)
                fc = first_content(X, Y, q1, q2)
                if fc is None:
                    assert X != Y and direct(Y, q1, q2, g1, g2); gen.append((q, min(q1, q2))); gq += 1; rechk += 1
                    continue
                side, i, c = fc
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
           "seeds": lambda: part_seeds(60 if quick else 200)}
    for p in args or list(run):
        run[p]()
