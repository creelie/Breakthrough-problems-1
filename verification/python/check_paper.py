"""Recomputes the numbers stated in the paper and checks that the paper states them as recomputed.

Each check names a string that must occur verbatim in preprint/main.tex and recomputes the value it
states, in exact integer arithmetic or with mpmath at 60 digits:

  * Table 1, parsed from main.tex, against the classes of regular tournaments in DATA_DIR
    (the output of regtour.c): every row, decimal and labelled count, each class exactly once;
  * Wormald's table (R_3, ..., R_13, R_9', and his decimals for R_21, R_41, R_81, R_101) and his
    7-vertex example, recomputed from Theorem 1.1;
  * the closed form (1.3) for R_d against exact determinants det(d^2 I -+ S^2), 3 <= d <= 41, and
    against the characteristic polynomial of S for d <= 21;
  * cosh 1/cos 1, the coefficients of d^-2, d^-1, d^-3 and d^-5 in the expansion of rho_R(R_d);
  * the bounds of Theorem 1.5: the limit of U_d, the interval for limit points, the 0.051% gap,
    rho_R > e, the claims about d <= 9;
  * the circulant remark (Wormald's seven 9-vertex sets D) and the footnote's factorizations.

    usage: python3 -I check_paper.py PAPER_TEX DATA_DIR

Prints one line per check and "N checks, K failures"; exits with status 1 if K > 0.
"""
import math
import os
import re
import sys
from fractions import Fraction as Fr
from math import isqrt

import mpmath as mp

mp.mp.dps = 60
TEX = ""
checks = fails = 0


def check(name, cond, info="", lit=None):
    """Record one check; if lit is given it must occur verbatim in the paper."""
    global checks, fails
    if lit is not None and lit not in TEX:
        cond, info = False, f"string not found in main.tex: {lit!r}"
    checks += 1
    fails += not cond
    print(f"{'ok  ' if cond else 'FAIL'} {name}{': ' + info if info else ''}", flush=True)


# ------------------------------------------------------------------ exact linear algebra
def bareiss(M):
    """Determinant of an integer matrix (fraction-free elimination)."""
    M = [row[:] for row in M]
    n, sign, prev = len(M), 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            p = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
            if p is None:
                return 0
            M[k], M[p] = M[p], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def skew(A):
    d = len(A)
    return [[A[i][j] - A[j][i] for j in range(d)] for i in range(d)]


def matmul(X, Y):
    n = len(X)
    return [[sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def rho_exact(A):
    """rho_T = sqrt(d/H) = det(dI - S)/det(dI - iS) by Theorem 1.1, from det(d^2 I -+ S^2)."""
    d = len(A)
    S = skew(A)
    S2 = matmul(S, S)
    minus = bareiss([[d * d * (i == j) - S2[i][j] for j in range(d)] for i in range(d)])
    plus = bareiss([[d * d * (i == j) + S2[i][j] for j in range(d)] for i in range(d)])
    a, b = isqrt(minus), isqrt(plus)
    assert a * a == minus and b * b == plus and a > 0 and b > 0
    return Fr(a, b)


def rho_from_poly(d, c):
    """rho_T from the characteristic polynomial det(tI - S) = sum c[k] t^(d-k)."""
    num = sum(ck * d ** (d - k) for k, ck in enumerate(c))
    re_, im_ = 0, 0  # Horner at t = i d
    for ck in c:
        re_, im_ = -im_ * d + ck, re_ * d
    assert re_ == 0
    den = im_ if d % 4 == 1 else -im_  # divide p(id) by i^d
    return Fr(num, den)


def cyclic(d):
    m = (d - 1) // 2
    return [[1 if 1 <= (j - i) % d <= m else 0 for j in range(d)] for i in range(d)]


def circ(d, D):
    return [[1 if (j - i) % d in D else 0 for j in range(d)] for i in range(d)]


def re_pow_d_plus_i(d):
    re_, im_ = 1, 0
    for _ in range(d):
        re_, im_ = re_ * d - im_, re_ + im_ * d
    return re_


def closed_form(d):
    """The first expression in (1.3)."""
    return Fr(((d + 1) ** d + (d - 1) ** d) // 2, re_pow_d_plus_i(d))


def is_prime(n):
    return n > 1 and all(n % p for p in range(2, isqrt(n) + 1))


def rnd(x, places):
    q = mp.mpf(10) ** places
    return mp.nint(mp.mpf(x) * q) / q


def trunc(x, places):
    q = mp.mpf(10) ** places
    return mp.floor(mp.mpf(x) * q) / q


def mpq(x):
    return mp.mpf(x.numerator) / x.denominator


# ------------------------------------------------------------------ data
def classes(path):
    out = []
    with open(path) as f:
        head = f.readline().split()
        total = int(head[1])
        for line in f:
            t = line.split()
            i, j = t.index("count"), t.index("mat")
            poly = [int(x) for x in t[1:i]]
            A = [[int(ch) for ch in row] for row in t[j + 1:]]
            out.append((poly, int(t[i + 1]), A))
    return total, out


def table_rows():
    """Rows of Table 1 as (d, fraction, decimal string, labelled count, remark)."""
    body = TEX[TEX.index(r"\label{tab:small}"):]
    body = body[body.index(r"\midrule"):body.index(r"\bottomrule")]
    rows, d = [], None
    for line in body.splitlines():
        cells = [c.strip() for c in line.rstrip("\\ ").split("&")]
        if len(cells) != 5:
            continue
        if cells[0]:
            d = int(cells[0])
        frac = Fr(cells[1])
        rows.append((d, frac, cells[2], int(cells[3]), cells[4]))
    return rows


def main():
    global TEX
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    with open(sys.argv[1]) as f:
        TEX = f.read()
    data = sys.argv[2]
    c = mp.cosh(1) / mp.cos(1)

    # ---- Table 1 and the claims about d <= 9
    rows = table_rows()
    allrho = {}
    for d in (3, 5, 7, 9):
        total, cl = classes(os.path.join(data, f"classes{d}.txt"))
        check(f"d={d}: labelled counts add up to the total", sum(k for _, k, _ in cl) == total,
              f"{total} tournaments, {len(cl)} spectra")
        comp = []
        for poly, cnt, A in cl:
            r1, r2 = rho_from_poly(d, poly), rho_exact(A)
            check(f"d={d} class {poly}: rho from char poly = rho from det(d^2I -+ S^2)", r1 == r2, str(r1))
            comp.append((r1, cnt, A))
        allrho[d] = comp
        if d == 3:
            continue
        mine = sorted(((r, k) for r, k, _ in comp), key=lambda t: -t[0])
        theirs = [(f, k) for dd, f, _, k, _ in rows if dd == d]
        check(f"Table 1, d={d}: rows = classes, in decreasing order", mine == theirs,
              f"{len(theirs)} rows")
        for dd, f, s, k, rem in rows:
            if dd == d:
                check(f"Table 1, d={d}, {f}: decimal", f"{float(f):.6f}" == s, s)
    check("totals 4, 132, 46144 labelled tournaments for d = 5, 7, 9",
          [classes(os.path.join(data, f"classes{d}.txt"))[0] for d in (5, 7, 9)] == [4, 132, 46144])

    # R_d is the maximum for d <= 9 and U_d is within 1e-4 of it
    for d in (3, 5, 7, 9):
        best = max(r for r, _, _ in allrho[d])
        check(f"d={d}: R_d has the largest rho_T", best == rho_exact(cyclic(d)), str(best))
        check(f"d={d}: U_d - rho_T(R_d) < 1e-4", 0 <= U(d) - mpq(best) < mp.mpf("1e-4"),
              mp.nstr(U(d) - mpq(best), 5))
    # lower bound with equality exactly for doubly regular classes
    for d in (3, 5, 7, 9):
        m = (d - 1) // 2
        low = Fr(d + 1, d - 1) ** m
        for r, _, A in allrho[d]:
            S = skew(A)
            dr = matmul(S, [list(x) for x in zip(*S)]) == [[d * (i == j) - 1 for j in range(d)]
                                                           for i in range(d)]
            check(f"d={d}, rho={r}: rho >= ((d+1)/(d-1))^m, equality iff doubly regular",
                  r >= low and ((r == low) == dr))
    check("Paley 7 row is doubly regular: 64/27 = (8/6)^3",
          Fr(64, 27) == Fr(8, 6) ** 3, lit="64/27 & 2.370370 & 12 & doubly regular (Paley)")

    # ---- Wormald's table, exact
    w = {3: Fr(2), 5: Fr(44, 19), 7: Fr(3032, 1231), 9: Fr(437584, 171769),
         11: Fr(108859552, 41833969), 13: Fr(41637757888, 15769379963)}
    for d, v in w.items():
        check(f"Wormald's table: rho_T(R_{d}) = {v}", closed_form(d) == v == rho_exact(cyclic(d)))
    r9p = [[1 if ((j // 3 - i // 3) % 3 == 1 or (i // 3 == j // 3 and (j - i) % 3 == 1)) else 0
            for j in range(9)] for i in range(9)]
    check("Wormald's table: rho_T(R_9') = 5488/2197 (R_9' = R_3 blown up by R_3)",
          rho_exact(r9p) == Fr(5488, 2197), lit=r"5488/2197 & 2.497952 & 64 & $R_9'$ (blow-up of $R_3$)")
    rt4 = {3: "2.0000", 5: "2.3158", 7: "2.4630", 9: "2.5475", 11: "2.6022", 13: "2.6404"}
    rr4 = {3: "2.7912", 5: "2.8285", 7: "2.8413", 9: "2.8469", 11: "2.8498", 13: "2.8515"}
    for d in rt4:
        x = closed_form(d)
        check(f"Wormald's decimals for R_{d}",
              f"{float(x):.4f}" == rt4[d] and f"{float(math.exp(1 / d) * x):.4f}" == rr4[d])
    check("Wormald's decimals for R_9'", f"{float(Fr(5488, 2197)):.4f}" == "2.4980"
          and f"{float(math.exp(1 / 9) * Fr(5488, 2197)):.4f}" == "2.7915")
    big = {21: ("2.7215188", "2.8542501"), 41: ("2.7867038", "2.8555079"),
           81: ("2.820801899", "2.855842468"), 101: ("2.827747088", "2.855883644")}
    for d, (t, r) in big.items():
        x = mpq(closed_form(d))
        y = mp.exp(mp.mpf(1) / d) * x
        pt, pr = len(t) - 2, len(r) - 2
        check(f"decimals for R_{d}, truncated (Wormald's, R_81 corrected)",
              trunc(x, pt) == mp.mpf(t) and trunc(y, pr) == mp.mpf(r), f"{mp.nstr(x, 12)}, {mp.nstr(y, 12)}")
    y81 = mp.exp(mp.mpf(1) / 81) * mpq(closed_form(81))
    check("Wormald's rho_R(R_81) = 2.855842467 is off in the last digit, as the paper says",
          trunc(y81, 9) == mp.mpf("2.855842468"), mp.nstr(y81, 15),
          lit=r"his $\rho_\cR(R_{81})=2.855842467\ldots$ should read $2.855842468\ldots$")
    y101 = mp.exp(mp.mpf(1) / 101) * mpq(closed_form(101))
    check("rho_R(R_101) = 2.855883...", trunc(y101, 6) == mp.mpf("2.855883"),
          lit=r"$\rho_\cR(R_{101})=2.855883\ldots$")
    check("h(n) > 2.85588 g(n) follows from R_101", y101 > mp.mpf("2.85588"), lit="h(n)>2.85588\\,g(n)")
    check("rho_T(R_13) as stated", closed_form(13) == Fr(41637757888, 15769379963),
          lit=r"\rho_\cT(R_{13})=41637757888/15769379963")
    check("rho_T(R_3) = 2 and rho_T(R_5) = 44/19", closed_form(3) == 2 and closed_form(5) == Fr(44, 19),
          lit=r"$\rho_\cT(R_3)=2$ and $\rho_\cT(R_5)=44/19$")

    # Wormald's 7-vertex example: triples abc, a'b'c', arcs aa', bb', cc', ad, bd, cd
    a, b, cc, a2, b2, c2, dd = range(7)
    arcs = [(a, b), (b, cc), (cc, a), (a2, b2), (b2, c2), (c2, a2), (a, a2), (b, b2), (cc, c2),
            (a, dd), (b, dd), (cc, dd), (dd, a2), (dd, b2), (dd, c2), (b2, a), (c2, a), (a2, b), (c2, b),
            (a2, cc), (b2, cc)]
    W7 = [[0] * 7 for _ in range(7)]
    for i, j in arcs:
        W7[i][j] = 1
    reg = all(sum(W7[i]) == 3 and W7[i][j] + W7[j][i] == 1 for i in range(7) for j in range(7) if i != j)
    r = rho_exact(W7)
    match = [k for rr, k, _ in allrho[7] if rr == r]
    check("Wormald's 7-vertex example: regular, rho_T = 3088/1287, the 84-tournament row",
          reg and r == Fr(3088, 1287) and match == [84], lit="3088/1287 & 2.399378 & 84 & Wormald's example")

    # footnote
    check("footnote: 41833969 = 43*307*3169 (primes), the denominator for d = 11",
          43 * 307 * 3169 == 41833969 == closed_form(11).denominator and all(map(is_prime, (43, 307, 3169))),
          lit=r"$41833969=43\cdot307\cdot3169$")
    check("footnote: 53*297535471 (primes) is the denominator for d = 13",
          53 * 297535471 == closed_form(13).denominator and is_prime(53) and is_prime(297535471),
          lit=r"$53\cdot297535471$")

    # ---- closed form for R_d
    for d in range(3, 42, 2):
        check(f"closed form (1.3) = det ratio for R_{d}", closed_form(d) == rho_exact(cyclic(d)))
    for d in range(3, 22, 2):
        S = skew(cyclic(d))
        ok = all(bareiss([[x * (i == j) - S[i][j] for j in range(d)] for i in range(d)]) * 2
                 == (x + 1) ** d + (x - 1) ** d for x in range(-d, d + 2))
        check(f"det(xI - S) = ((x+1)^d + (x-1)^d)/2 for R_{d} at 2d+2 points", ok)
    for d in range(3, 200, 2):
        x = closed_form(d)
        e2 = (mp.mpf(d * d - 1) / (d * d + 1)) ** (mp.mpf(d) / 2) * mp.cosh(d * mp.atanh(mp.mpf(1) / d)) \
            / mp.cos(d * mp.atan(mp.mpf(1) / d))
        if not mp.almosteq(mpq(x), e2, mp.mpf("1e-50")):
            check(f"second expression in (1.3) at d={d}", False)
            break
    else:
        check("second expression in (1.3) equals the first for odd d < 200", True)

    # ---- constants and the expansion
    check("cosh1/cos1 = 2.85595789256511371...", trunc(c, 17) == mp.mpf("2.85595789256511371"),
          mp.nstr(c, 25), lit="2.85595789256511371")
    check("abstract: 2.8559578925...", trunc(c, 10) == mp.mpf("2.8559578925"), lit="2.8559578925\\ldots")
    check("2.855958 is cosh1/cos1 to six places", rnd(c, 6) == mp.mpf("2.855958"), lit="constant $2.855958$")
    check("Wormald's estimate 2.8559579 is cosh1/cos1 to seven places", rnd(c, 7) == mp.mpf("2.8559579"),
          lit="as $2.8559579$")

    def G(x):  # rho_R(R_d) at x = 1/d, from the second expression in (1.3)
        x = mp.mpf(x)
        return mp.exp(x + mp.log((1 - x * x) / (1 + x * x)) / (2 * x)
                      + mp.log(mp.cosh(mp.atanh(x) / x)) - mp.log(mp.cos(mp.atan(x) / x)))

    check("G(1/d) = rho_R(R_d) at d = 11, 101",
          all(mp.almosteq(G(mp.mpf(1) / d), mp.exp(mp.mpf(1) / d) * mpq(closed_form(d)), mp.mpf("1e-45"))
              for d in (11, 101)))
    h = mp.mpf("1e-4")
    odd = (G(h) - G(-h)) / 2
    even = (G(h) + G(-h)) / 2
    c2 = -c * (mp.tan(1) - mp.tanh(1)) / 3
    check("coefficient of d^-2 is -c(tan1 - tanh1)/3", abs((even - c) / h ** 2 - c2) < mp.mpf("1e-6"),
          f"{mp.nstr((even - c) / h ** 2, 12)} vs {mp.nstr(c2, 12)}",
          lit=r"\Bigl(1-\dfrac{\tan1-\tanh1}{3d^2}+O(d^{-4})\Bigr)")
    check("coefficients of d^-1 and d^-3 vanish, that of d^-5 is -c/3",
          abs(odd / h ** 5 + c / 3) < mp.mpf("1e-6"), f"{mp.nstr(odd / h ** 5, 12)} vs {mp.nstr(-c / 3, 12)}",
          lit=r"that of $d^{-5}$ equals $-\cosh1/(3\cos1)$")

    # ---- Theorem 1.5
    limU = (mp.pi ** 2 + 4) * (3 * mp.pi ** 2 - 8) / ((mp.pi ** 2 - 4) * (mp.pi ** 2 + 8))
    check("lim U_d = 2.8574011776...", trunc(limU, 10) == mp.mpf("2.8574011776"), mp.nstr(limU, 15),
          lit="=2.8574011776\\ldots")
    for d in (10 ** 4 + 1, 10 ** 5 + 1, 10 ** 6 + 1):
        check(f"e^(1/d) U_d near the limit at d = {d}", abs(mp.exp(mp.mpf(1) / d) * U(d) - limU) < mp.mpf(30) / d,
              mp.nstr(mp.exp(mp.mpf(1) / d) * U(d) - limU, 5))
    check("limit points lie in [2.8559578, 2.8574012]", mp.mpf("2.8559578") <= c and limU <= mp.mpf("2.8574012"),
          lit=r"$[2.8559578,\,2.8574012]$")
    gap = (limU - c) / c * 100
    check("gap (lim U - c)/c is below 0.051%", gap < mp.mpf("0.051"), mp.nstr(gap, 6) + "%",
          lit=r"within $0.051\%$")
    ok = True
    for d in range(3, 2002, 2):
        m = (d - 1) // 2
        lowR = mp.exp(mp.mpf(1) / d) * (mp.mpf(d + 1) / (d - 1)) ** m
        ok = ok and lowR > mp.e
        if d < 400:
            ok = ok and U(d) >= mpq(closed_form(d))
    check("e^(1/d)((d+1)/(d-1))^m > e (d < 2002) and U_d >= rho_T(R_d) (d < 400)", ok)
    check("(5/4)^4 = 2.4414...", trunc(mp.mpf(5) ** 4 / 4 ** 4, 4) == mp.mpf("2.4414"), lit="(5/4)^4=2.4414\\ldots")

    # ---- circulant remark
    Ds = {(1, 3, 4, 5): 1.4582, (1, 2, 4, 5): 1.6811, (1, 2, 3, 5): 2.4557, (2, 3, 4, 5): 1.5618,
          (1, 3, 5, 6): 1.5529, (1, 4, 5, 6): 1.9325, (2, 3, 5, 6): 1.8117}
    tours = [D for D in Ds if all((9 - r) not in D for r in D)]
    check("of Wormald's seven sets D only {1,2,3,5} gives a tournament", tours == [(1, 2, 3, 5)])
    rc = rho_exact(circ(9, {1, 2, 3, 5}))
    check("circulant {1,2,3,5}: rho_T = 451696/183937 = 2.4557..., the 576-tournament row",
          rc == Fr(451696, 183937) and trunc(mpq(rc), 4) == mp.mpf("2.4557")
          and [k for r, k, _ in allrho[9] if r == rc] == [576],
          lit=r"451696/183937 & 2.455710 & 576 & circulant $\{1,2,3,5\}$")
    check("1.4582 e^(1/9) is about 1.63", round(1.4582 * math.exp(1 / 9), 2) == 1.63,
          lit=r"1.4582\,e^{1/9}g(n)\approx1.63\,g(n)")

    print(f"{checks} checks, {fails} failures")
    sys.exit(1 if fails else 0)


def U(d):
    """U_d of Theorem 1.5, at 60 digits."""
    C = mp.mpf(d) * (d - 1) / 2
    s = mp.cot(mp.pi / (2 * d)) ** 2
    q = int(mp.floor(C / s))
    r = C - q * s
    phi = lambda x: (d * d + x) / (d * d - x)
    return phi(s) ** q * phi(r)


if __name__ == "__main__":
    main()
