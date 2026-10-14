# Generates proto/block_data.bend: one rigid cyclic block (a random
# Henneberg-II Laman framework: edge splits, so no triangle-by-triangle
# construction), with
#   - x̃: a float64 Newton solution (Bend refines it to working precision),
#   - Yᵀ: the transpose of an F32-quality inverse of J(x̃) (float32 Gauss-Jordan,
#     emulated exactly: each op computed in double and rounded to float32),
# and prints the condition number and ‖I − Y·J‖∞ as Python sees them.
# usage: gen_block.py n flatten P seed
import math, random, struct, sys
n = int(sys.argv[1]); flat = float(sys.argv[2]); P = int(sys.argv[3]); seed = int(sys.argv[4])
random.seed(seed)

def f32(x): return struct.unpack("f", struct.pack("f", x))[0]

# graph
edges = [(0, 1), (1, 2), (0, 2)]
for v in range(3, n):
    i = random.randrange(len(edges)); a, b = edges.pop(i)
    c = random.choice([w for w in range(v) if w not in (a, b)])
    edges += [(v, a), (v, b), (v, c)]
assert len(edges) == 2 * n - 3

# positions (nm) in a 200 mm box, y scaled by `flat`; pin P0 at 0, P1 on the x-axis
pts = [(random.uniform(0, 2e8), random.uniform(0, 2e8) * flat) for _ in range(n)]
ox, oy = pts[0]; ang = math.atan2(pts[1][1] - oy, pts[1][0] - ox)
c_, s_ = math.cos(-ang), math.sin(-ang)
pts = [((x - ox) * c_ - (y - oy) * s_, (x - ox) * s_ + (y - oy) * c_) for x, y in pts]
pts[0] = (0.0, 0.0); pts[1] = (pts[1][0], 0.0)
dims = [round(math.dist(pts[u], pts[v])) for u, v in edges]

m = 2 * n - 3
def idx(point, axis):                  # unknown index, or m for a pinned coordinate
    if point == 0: return m
    if point == 1: return 0 if axis == 0 else m
    return 2 * point - 3 + axis
def coords(x, point):
    return (0.0 if idx(point, 0) == m else x[idx(point, 0)], 0.0 if idx(point, 1) == m else x[idx(point, 1)])

def F(x):
    out = []
    for (u, v), d in zip(edges, dims):
        (ux, uy), (vx, vy) = coords(x, u), coords(x, v)
        out.append((ux - vx) ** 2 + (uy - vy) ** 2 - d * d)
    return out
def Jac(x):
    J = [[0.0] * m for _ in range(m)]
    for e, (u, v) in enumerate(edges):
        (ux, uy), (vx, vy) = coords(x, u), coords(x, v)
        for (p, sgn) in ((u, 1), (v, -1)):
            for axis, dd in ((0, ux - vx), (1, uy - vy)):
                i = idx(p, axis)
                if i != m: J[e][i] += sgn * 2 * dd
    return J
def inverse(A, rnd=lambda t: t):
    k = len(A); M = [[rnd(v) for v in row] + [1.0 if i == j else 0.0 for j in range(k)] for i, row in enumerate(A)]
    for c in range(k):
        p = max(range(c, k), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        piv = M[c][c]; M[c] = [rnd(v / piv) for v in M[c]]
        for r in range(k):
            if r != c and M[r][c] != 0.0:
                f = M[r][c]; rowc = M[c]
                M[r] = [rnd(a - rnd(f * b)) for a, b in zip(M[r], rowc)]
    return [row[k:] for row in M]
def matvec(A, v): return [sum(a * b for a, b in zip(row, v)) for row in A]
def ninf(A): return max(sum(abs(a) for a in row) for row in A)

x = [0.0] * m
for p in range(1, n):
    for axis in (0, 1):
        i = idx(p, axis)
        if i != m: x[i] = pts[p][axis] + random.uniform(-2e5, 2e5) * flat   # a sloppy drawing, ±0.2 mm × flat
for it in range(30):
    Ji = inverse(Jac(x)); dx = matvec(Ji, F(x)); x = [a - b for a, b in zip(x, dx)]
    if max(abs(t) for t in dx) < 1e-6: break
J = Jac(x); Ji = inverse(J); kappa = ninf(J) * ninf(Ji)
Y32 = inverse(J, f32)
YJ = [[sum(Y32[i][e] * J[e][j] for e in range(m)) for j in range(m)] for i in range(m)]
q0 = max(sum(abs((1.0 if i == j else 0.0) - YJ[i][j]) for j in range(m)) for i in range(m))
print(f"n={n} m={m} flat={flat}: kappa_inf={kappa:.3g}  F32 q0=‖I−YJ‖={q0:.3g}  newton_iters={it+1}")

from fractions import Fraction
def dy(v): return round(Fraction(v) * 2 ** P)
def w(name, text): open(f"proto/block.{name}", "w").write(text)
w("meta", f"{m} {P}")
w("edges", "\n".join(f"{idx(u,0)} {idx(u,1)} {idx(v,0)} {idx(v,1)} {d}" for (u, v), d in zip(edges, dims)))
w("x0", " ".join(str(dy(t)) for t in x))
w("yt", "\n".join(" ".join(str(dy(Y32[i][e])) for i in range(m)) for e in range(m)))
cols = [[] for _ in range(m)]
for e, (u, v) in enumerate(edges):
    for (p_, sgn) in ((u, 1), (v, -1)):
        for axis in (0, 1):
            i = idx(p_, axis)
            if i != m: cols[i] += [e, 1 if sgn > 0 else 0, axis]
w("jcols", "\n".join(" ".join(map(str, c)) for c in cols))
