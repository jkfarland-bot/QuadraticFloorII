# Numerical check of the Lean statements of QuadraticFloorII, exactly as formalized.
# Floor sums and Kronecker symbols are exact; Bernoulli numbers of characters of order dividing 4 are
# computed exactly in Q(i) (Fractions); other characters use floating point with tolerance 1e-7.
import cmath
from fractions import Fraction as Fr
from math import gcd
from sympy import primerange, primitive_root, jacobi_symbol, factorint, totient, legendre_symbol

fails = {}
def F(name): fails[name] = fails.get(name, 0) + 1
def close(a, b): return abs(a - b) < 1e-7

def floorSum(A, B, C, p):
    return sum((-1) ** (((A * n * n + B * n + C) // p) % 2) for n in range(p))
def negOnePow(C): return -1 if C % 2 else 1
def eta(p, x):
    return 0 if x % 2 == 0 else (int(jacobi_symbol((-8 * p) % x, x)) if x > 1 else 1)
def chi4(x): return 0 if x % 2 == 0 else (1 if x % 4 == 1 else -1)
def bern(q, f): return sum(x * f(x) for x in range(1, q + 1)) / q
def leg(a, l): return int(legendre_symbol(a % l, l)) if a % l else 0

def chars(A):
    """All Dirichlet characters mod odd A as (values dict on units, order), float complex."""
    fac = factorint(A)
    comps = []
    for q, e in fac.items():
        m = q ** e; g = primitive_root(m); ph = int(totient(m))
        ind = {pow(g, k, m): k for k in range(ph)}
        comps.append((m, ph, ind))
    res = [[]]
    for (m, ph, ind) in comps:
        res = [r + [(m, ph, ind, k)] for r in res for k in range(ph)]
    out = []
    for r in res:
        def ch(x, r=r):
            if gcd(x, A) != 1: return 0
            v = 1
            for (m, ph, ind, k) in r: v *= cmath.exp(2j * cmath.pi * k * ind[x % m] / ph)
            return v
        out.append((tuple(c[3] for c in r), ch))
    return out

def vartheta(p, A, ch):
    odd = abs(ch(A - 1) + 1) < 1e-9 if A > 1 else False
    return lambda x: eta(p, x) * (chi4(x) if odd else chi4(x) ** 2) * ch(x % A if A > 1 else 0)

def adm_lift(A, b):
    B = b if b % 2 else b + A
    return B, (B * B - 1) // (4 * A)

# Euler factor for eta, all l > 0
for p in primerange(3, 30):
    for l in range(1, 16):
        lhs = bern(8 * l * p, lambda x: eta(p, x) * (0 if x % l == 0 else 1))
        rhs = (1 - eta(p, l)) * bern(8 * p, lambda x: eta(p, x))
        if Fr(lhs).limit_denominator(10**9) != Fr(rhs).limit_denominator(10**9) and abs(lhs - rhs) > 1e-9: F('euler_factor_eta')

# A = 3 and A = 5 in class-number shape
for p in primerange(5, 200):
    S1 = floorSum(1, 1, 0, p); S3 = floorSum(3, 1, 0, p)
    B24 = Fr(sum(x * eta(p, x) * chi4(x) * leg(x, 3) for x in range(1, 24 * p + 1)), 24 * p)
    B8 = Fr(sum(x * eta(p, x) for x in range(1, 8 * p + 1)), 8 * p)
    if S3 != 1 - B24 / 2 - Fr(1, 2) * (1 - leg(p, 3)) * B8: F('floorSum_three_class')
    if p % 3 == 1 and -B24 != 2 * (S3 - 1): F('class_twentyfour')
    if p % 3 == 2 and -B24 != 2 * (S3 - S1): F('class_twentyfour')
    if p != 5:
        B40 = Fr(sum(x * eta(p, x) * leg(x, 5) for x in range(1, 40 * p + 1)), 40 * p)
        if -B40 != 2 * (floorSum(5, 1, 0, p) + floorSum(5, 3, 0, p) - 2) - (1 + leg(p, 5)) * (S1 - 1):
            F('class_forty')
    # half range
    h = sum(negOnePow((n * (n + 1)) // p) for n in range(1, (p - 1) // 2 + 1))
    if 2 * h != S1 - 2 + leg(-2, p): F('half_range_triangular')

# fibre sums, reality, quarter range
for A in [1, 3, 5, 7, 9, 15, 21]:
    CH = chars(A) if A > 1 else [((), lambda x: 1)]
    for p in primerange(3, 24):
        if A % p == 0: continue
        q = 8 * A * p
        Bs = {}
        for key, ch in CH:
            th = vartheta(p, A, ch)
            Bs[key] = bern(q, th)
            if not close(Bs[key], -sum(th(x) for x in range(1, 2 * A * p + 1))): F('quarter_range')
        units = [b for b in range(A) if gcd(b, A) == 1] if A > 1 else [0]
        for k0, ch0 in CH:
            lhs = 0
            for b in units:
                B, C = adm_lift(A, b if A > 1 else 1)
                lhs += ch0(b) ** 2 * (floorSum(A, B, C, p) - negOnePow(C)) if A > 1 else (floorSum(1, 1, 0, p) - 1)
            fib = [k for k, ch in CH if all(close(ch(x) ** 2, ch0(x) ** 2) for x in units)]
            rhs = -sum(Bs[k] for k in fib)
            if not close(lhs, rhs): F('fibre_sum')
            if all(close(ch0(x) ** 4, 1) for x in units) and abs(complex(rhs).imag) > 1e-7: F('fibre_sum_real')

# conductor 8lp, exact, both quartic characters; parity also at p = l
I4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
for l in [5, 13, 17, 29, 37, 41]:
    g = primitive_root(l); ind = {pow(g, k, l): k for k in range(l - 1)}
    Q = sorted({b * b % l for b in range(1, l)})
    rep = {}
    for s in Q:
        B = next(B for B in range(1, 4 * l, 2) if B * B % l == s and B % l)
        rep[s] = (B, (B * B - 1) // (4 * l))
    for sgn in (1, 3):
        xi = lambda x: (0, 0) if x % l == 0 else I4[(sgn * ind[x % l]) % 4]
        delta = 1 if l % 8 == 5 else 0
        for p in primerange(3, 70):
            q = 8 * l * p
            def th(x):
                e = eta(p, x) * (chi4(x) if delta else chi4(x) ** 2)
                z = xi(x); return (e * z[0], e * z[1])
            re = Fr(sum(x * th(x)[0] for x in range(1, q + 1)), q)
            im = Fr(sum(x * th(x)[1] for x in range(1, q + 1)), q)
            qre = -sum(th(x)[0] for x in range(1, 2 * l * p + 1)); qim = -sum(th(x)[1] for x in range(1, 2 * l * p + 1))
            if (re, im) != (qre, qim) or qre % 2 or qim % 2: F('conductor_even')
            if l == 5 and sgn == 1:
                # Theta p with xi(2) = i: here g = 2 is the least primitive root mod 5
                if (re, im) != (qre, qim) or qre % 2 or qim % 2: F('quartic_trace_even')
            if p == l: continue
            S = {s: floorSum(l, *rep[s], p) - negOnePow(rep[s][1]) for s in Q}
            if re != -sum(leg(rep[s][0], l) * S[s] for s in Q): F('conductor_trace')
            B8l = Fr(sum(x * eta(p, x) * leg(x, l) for x in range(1, q + 1)), q)
            if -B8l != 2 * sum(S.values()) - (1 - leg(2 * p, l)) * (floorSum(1, 1, 0, p) - 1):
                F('conductor_quadratic')
            if l == 13:
                d = (floorSum(13, 1, 0, p) + floorSum(13, 3, 0, p) - floorSum(13, 5, 0, p) - floorSum(13, 7, 0, p)
                     + floorSum(13, 9, 1, p) - floorSum(13, 11, 2, p) + 2)
                if re != -d: F('conductor_thirteen')
print("failures:", fails or "none")
