"""Independent checks for conjecture 00000009614 (Python 3 standard library only).

A = [4] (full 4-shift), B = [[3,1],[1,3]].

1. Both matrices are nonnegative and entrywise positive (primitive, so the edge
   shifts are mixing SFTs).  Characteristic polynomials x - 4 and x^2 - 6x + 8 =
   (x - 4)(x - 2); spectral radius (Perron eigenvalue) 4 for both, with positive
   eigenvectors (1) and (1,1).  Path counts: sum of entries of A^k is 4^k, of B^k
   is 2*4^k (equal entropy log 4).
2. Eventual-range model (Lind-Marcus 7.5): Delta_M = {x in R_M : x M^k in Z^n for
   some k}, R_M the eventual range.  R_A = Q, Delta_A = Z[1/4]: rank 1 (explicit
   integer relation for random pairs).  B is invertible over Q (det 8), so R_B = Q^2
   and Z^2 is contained in Delta_B: rank 2.  Exact rational arithmetic.
3. Direct-limit model (as in Lean): brute force that (a+1)e1+(b+1)e2 and
   (c+1)e1+(d+1)e2 are never identified at any depth t <= 12 unless (a,b)=(c,d),
   and that every pair (u,k),(w,l) in lim(Z,4) satisfies the explicit relation.
4. Shift-equivalence invariants (second, independent obstruction for the
   dimension-triple reading): nonzero spectra {4} vs {4,2}, and the traces
   tr(A^k) = 4^k vs tr(B^k) = 4^k + 2^k differ for every k >= 1.
"""

import random
from fractions import Fraction

A = [[4]]
B = [[3, 1], [1, 3]]


def matmul(X, Y):
    return [[sum(X[i][l] * Y[l][j] for l in range(len(Y))) for j in range(len(Y[0]))]
            for i in range(len(X))]


def matpow(X, k):
    n = len(X)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for _ in range(k):
        R = matmul(R, X)
    return R


def rowmul(v, M):
    return [sum(v[i] * M[i][j] for i in range(len(v))) for j in range(len(M[0]))]


def det(M):
    M = [[Fraction(x) for x in row] for row in M]
    n, d = len(M), Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [M[r][j] - f * M[c][j] for j in range(n)]
    return d


def charpoly(M):
    """Coefficients c_0..c_n of det(xI - M), by interpolation at n+1 points."""
    n = len(M)
    xs = list(range(n + 1))
    ys = [det([[(x if i == j else 0) - M[i][j] for j in range(n)] for i in range(n)]) for x in xs]
    # Lagrange interpolation to monomial coefficients
    coeffs = [Fraction(0)] * (n + 1)
    for i, xi in enumerate(xs):
        basis = [Fraction(1)]
        denom = Fraction(1)
        for j, xj in enumerate(xs):
            if j == i:
                continue
            basis = [Fraction(0)] + basis
            for t in range(len(basis) - 1):
                basis[t] -= xj * basis[t + 1]
            denom *= (xi - xj)
        for t in range(n + 1):
            coeffs[t] += ys[i] * basis[t] / denom
    return [int(c) for c in coeffs]


def check(cond, msg):
    if not cond:
        raise SystemExit("FAILED: " + msg)
    print("ok:", msg)


# ---- 1. primitivity, Perron eigenvalue, entropy ---------------------------------
check(all(x > 0 for row in A for x in row) and all(x > 0 for row in B for x in row),
      "A and B are entrywise positive, hence primitive (mixing edge shifts)")
pa, pb = charpoly(A), charpoly(B)
check(pa == [-4, 1], "charpoly(A) = x - 4")
check(pb == [8, -6, 1], "charpoly(B) = x^2 - 6x + 8 = (x-4)(x-2)")
roots_b = [r for r in range(-10, 11) if sum(c * r ** i for i, c in enumerate(pb)) == 0]
check(sorted(roots_b) == [2, 4], "eigenvalues of B are 2 and 4 (both rational)")
check(max(roots_b) == 4, "Perron eigenvalue lambda_B = 4 = lambda_A")
check(rowmul([1], A) == [4] and rowmul([1, 1], B) == [4, 4],
      "positive eigenvectors: (1) A = 4 (1), (1,1) B = 4 (1,1)")
check(rowmul([1, -1], B) == [2, -2], "(1,-1) B = 2 (1,-1)")
for k in range(0, 25):
    assert sum(map(sum, matpow(A, k))) == 4 ** k
    assert sum(map(sum, matpow(B, k))) == 2 * 4 ** k
check(True, "path counts 4^k and 2*4^k for k < 25 (entropy log 4 for both)")
# power iteration as an independent numeric confirmation of the spectral radius
v = [1.0, 0.3]
for _ in range(60):
    w = rowmul(v, B)
    s = max(abs(x) for x in w)
    v = [x / s for x in w]
check(abs(s - 4.0) < 1e-9, "power iteration on B converges to 4.0")

# ---- 2. eventual-range model --------------------------------------------------
check(det(B) == 8, "det B = 8 != 0, so R_B = Q^2 and Delta_B contains Z^2")
# e1, e2 lie in Delta_B (k = 0) and are Q-linearly independent
check(det([[1, 0], [0, 1]]) != 0, "e1, e2 in Delta_B are linearly independent: rank Delta_B = 2")


def in_delta_A(x, kmax=40):
    return any((x * 4 ** k).denominator == 1 for k in range(kmax))


random.seed(9614)
for _ in range(2000):
    m, k = random.randint(-10 ** 6, 10 ** 6), random.randint(0, 12)
    m2, k2 = random.randint(-10 ** 6, 10 ** 6), random.randint(0, 12)
    p, q = Fraction(m, 4 ** k), Fraction(m2, 4 ** k2)
    assert in_delta_A(p) and in_delta_A(q)
    a, b = m2 * 4 ** k, -m * 4 ** k2          # explicit relation a p + b q = 0
    if (a, b) == (0, 0):                      # p = q = 0
        a, b = 1, 0
    assert (a, b) != (0, 0) and a * p + b * q == 0
check(True, "2000 random pairs in Delta_A = Z[1/4] satisfy a nontrivial integer relation (rank 1)")
check(not in_delta_A(Fraction(1, 3)) and in_delta_A(Fraction(5, 64)), "Delta_A = Z[1/4] membership sanity")

# ---- 3. direct-limit model ----------------------------------------------------


def pw(M, t, v):
    for _ in range(t):
        v = rowmul(v, M)
    return v


def related(M, v, k, w, l, tmax=12):
    return any(pw(M, l + t, v) == pw(M, k + t, w) for t in range(tmax + 1))


bad = 0
for a in range(6):
    for b in range(6):
        for c in range(6):
            for d in range(6):
                if related(B, [a + 1, b + 1], 0, [c + 1, d + 1], 0) != ((a, b) == (c, d)):
                    bad += 1
check(bad == 0, "in lim(Z^2, B): (a+1)e1+(b+1)e2 ~ (c+1)e1+(d+1)e2 only if equal (a,b,c,d < 6, t <= 12)")


def rep_add(M, p, q):
    """(u, k) + (w, l) = (u M^l + w M^k, k + l) on representatives."""
    (u, k), (w, l) = p, q
    return ([x + y for x, y in zip(pw(M, l, u), pw(M, k, w))], k + l)


def rep_smul(c, p):
    return ([c * x for x in p[0]], p[1])


for _ in range(500):
    u, k = random.randint(-50, 50), random.randint(0, 5)
    w, l = random.randint(-50, 50), random.randint(0, 5)
    U, W = u * 4 ** l, w * 4 ** k            # numerators at the common level k + l
    alpha, beta = (W, -U) if U != 0 else (1, 0)
    z = rep_add(A, rep_smul(alpha, ([u], k)), rep_smul(beta, ([w], l)))
    assert (alpha, beta) != (0, 0) and related(A, z[0], z[1], [0], 0)
check(True, "in lim(Z, 4): every sampled pair of classes satisfies a nontrivial relation")

# ---- 4. shift-equivalence invariants ------------------------------------------
check([4] != sorted(r for r in roots_b if r != 0), "nonzero spectra {4} and {2,4} differ")
for k in range(1, 30):
    ta = sum(matpow(A, k)[i][i] for i in range(1))
    tb = sum(matpow(B, k)[i][i] for i in range(2))
    assert ta == 4 ** k and tb == 4 ** k + 2 ** k and ta != tb
check(True, "tr(A^k) = 4^k != 4^k + 2^k = tr(B^k) for 1 <= k < 30")

print("ALL CHECKS PASSED")
