"""Generate AME7/Data.lean: cut certificates for the odd-q, AME(7,4) and AME(7,8) graph states.

Coordinates are natural numbers c = k * i + a (party i < 7, digit a < k). A cut is a 7-bit mask of
three parties. For each cut the certificate is (mask, d, L): L lists, row by row, an integer matrix
R indexed by (coordinates outside the cut) x (coordinates inside), both in increasing order, with

    sum over j outside of  T[i][j] * R[j][l]  =  d * [i = l]     for i, l inside the cut,

exactly over the integers (odd q, d = det of a 3 x 3 minor, R from its adjugate) or modulo 2
(GF(2^k), d = 1, R from the inverse of a 3k x 3k block).

Odd q: T = Gamma, the complement of the 7-cycle. GF(2^k), k = 2, 3: the circulant matrix with first
row g over GF(2^k), in the basis 1, alpha, ..., alpha^(k-1), blocks Tr(gamma alpha^a alpha^b).
"""
import itertools, sys

GAMMA = [[1 if (i - j) % 7 not in (0, 1, 6) else 0 for j in range(7)] for i in range(7)]

def det3(M):
    a, b, c = M
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))

def adj3(M):
    C = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            minor = [[M[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
            C[i][j] = (-1) ** (i + j) * (minor[0][0] * minor[1][1] - minor[0][1] * minor[1][0])
    return [[C[j][i] for j in range(3)] for i in range(3)]  # adjugate = transpose of cofactors

def gfmul(a, b, m, poly):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & (1 << m):
            a ^= poly
    return r

def trace(a, m, poly):
    t, x = 0, a
    for _ in range(m):
        t ^= x
        x = gfmul(x, x, m, poly)
    return t

def binary_table(m, poly, g):
    gam = [[g[(j - i) % 7] for j in range(7)] for i in range(7)]
    return [[trace(gfmul(gam[i][j], gfmul(1 << a, 1 << b, m, poly), m, poly), m, poly)
             for j in range(7) for b in range(m)] for i in range(7) for a in range(m)]

def inv2(M):
    n = len(M)
    A = [M[i][:] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c]), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[r][c]:
                A[r] = [x ^ y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]

def cut_coords(S, k):
    inside = [k * i + a for i in range(7) for a in range(k) if i in S]
    outside = [k * i + a for i in range(7) for a in range(k) if i not in S]
    return inside, outside

def check(T, inside, outside, d, R, mod):
    for x, i in enumerate(inside):
        for y, l in enumerate(inside):
            s = sum(T[i][j] * R[u][y] for u, j in enumerate(outside))
            t = d if x == y else 0
            if (s - t) % mod if mod else s - t:
                sys.exit("certificate check failed")

def odd_cert(S):
    inside, outside = cut_coords(S, 1)
    for Rp in itertools.combinations(outside, 3):
        M = [[GAMMA[s][r] for r in Rp] for s in inside]
        d = det3(M)
        if abs(d) in (1, 2):
            A = adj3(M)
            R = [[A[Rp.index(j)][y] if j in Rp else 0 for y in range(3)] for j in outside]
            check(GAMMA, inside, outside, d, R, 0)
            return d, R
    sys.exit("no unit minor for %s" % (S,))

def bin_cert(S, k, T):
    inside, outside = cut_coords(S, k)
    for cols in itertools.combinations(outside, 3 * k):
        M = [[T[i][j] for j in cols] for i in inside]
        N = inv2(M)
        if N is not None:
            R = [[N[cols.index(j)][y] if j in cols else 0 for y in range(3 * k)] for j in outside]
            check(T, inside, outside, 1, R, 2)
            return 1, R
    sys.exit("no invertible block for %s" % (S,))

def mask(S):
    return sum(1 << i for i in S)

def lean_rows(T):
    return "[" + ",\n    ".join("[" + ", ".join(map(str, r)) + "]" for r in T) + "]"

def wrap(nums, indent):
    """Comma-separated numbers, wrapped so that no line exceeds 100 characters."""
    lines, cur = [], ""
    for x in nums:
        piece = str(x) + ", "
        if len(indent) + len(cur) + len(piece) > 99:
            lines.append(cur.rstrip())
            cur = ""
        cur += piece
    lines.append(cur.rstrip().rstrip(","))
    return ("\n" + indent).join(lines)

def lean_certs(name, certs, doc):
    items = ["(%d, %d, [\n    %s])" % (mk, d, wrap([x for row in R for x in row], "    "))
             for mk, d, R in certs]
    return "%s\ndef %s : List (ℕ × ℤ × List ℤ) := [\n  %s]\n" % (doc, name, ",\n  ".join(items))

def main(path):
    cuts = sorted(itertools.combinations(range(7), 3), key=mask)
    odd = [(mask(S),) + odd_cert(S) for S in cuts]
    out = ["""/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Data.Int.Basic

/-!
# Certificate data (generated by `scripts/gen_data.py`; do not edit)

Coordinates are natural numbers `c = k i + a` (party `i < 7`, digit `a < k`), and a cut is a
mask of three of the seven parties. A certificate `(mask, d, L)` lists, row by row, a matrix `R`
indexed by the coordinates outside the cut times those inside (both in increasing order) with
`∑_{j outside} T i j · R j l = d · [i = l]` for `i, l` inside: exactly over the integers for odd
`q` (where `d` is the determinant of a `3 × 3` minor and `R` comes from its adjugate), and modulo
`2` for `GF(4)` and `GF(8)` (where `d = 1`).

* `oddCerts`: `T` is `Γ`, the complement of the 7-cycle (`k = 1`).
* `table4Rows`, `certs4`: the binary form of the circulant graph matrix over `GF(4)` with first row
  `0, 1, 1, ω, ω, 1, 1` (`k = 2`).
* `table8Rows`, `certs8`: the same over `GF(8)` with first row `0, 0, 1, α, α, 1, 0`,
  `α³ = α + 1` (`k = 3`).

Both tables use the basis `1, α, …` of `GF(2^k)` over `GF(2)`, with blocks `Tr(γ αᵃ αᵇ)`.
-/

namespace AME7
"""]
    out.append(lean_certs("oddCerts", odd, "/-- The odd-`q` certificates, one per cut, by mask. -/"))
    for k, poly, g, name in [(2, 0b111, [0, 1, 1, 2, 2, 1, 1], "4"), (3, 0b1011, [0, 0, 1, 2, 2, 1, 0], "8")]:
        T = binary_table(k, poly, g)
        assert all(T[r][c] == T[c][r] for r in range(7 * k) for c in range(7 * k))
        certs = [(mask(S),) + bin_cert(S, k, T) for S in cuts]
        out.append("/-- The binary form of the circulant graph matrix over `GF(%s)`, by rows. -/" % name)
        out.append("def table%sRows : List (List ℕ) :=\n  %s\n" % (name, lean_rows(T)))
        out.append(lean_certs("certs" + name, certs, "/-- The `GF(%s)` certificates, one per cut, by mask. -/" % name))
    out.append("end AME7\n")
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(out))
    print("odd dets:", sorted({d for _, d, _ in odd}), "| 35 cuts x 3 families checked | written", path)

if __name__ == "__main__":
    main(sys.argv[1])
