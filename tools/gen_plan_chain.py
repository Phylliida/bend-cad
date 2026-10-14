#!/usr/bin/env python3
"""Write proto/plan_chain.txt: a depth-N circle chain as a sketch and a plan
for the verified plan checker (lib/plan.bend), read by
proto/plan_chain_run.bend.

    tools/gen_plan_chain.py [well|flat] [P] [N]

The geometry is the sk-P1 spike's (proto/gen_chain_run.py: same strips,
same seed): points P_0 .. P_{N+1} in nm, P_0 = (0, 0) and P_1 = (L1, 0)
pinned (radius 0), and P_k for k >= 2 at integer distances r_k from
P_{k-2} and s_k from P_{k-1}, as two driving Distance constraints. Block
k - 2 has unknowns P_k and parameters P_{k-2}, P_{k-1}. Centers are the
solution rounded to 2^-P nm; Y is the inverse slope matrix at the center
with 32 significant bits; q = 1/2.

Radii come from an emulation of the checker's conditions (DESIGN §8.3)
in exact rationals, with the slope spread Δ taken twice as wide as the
checker's ball arithmetic gives it and 1% added, then rounded up to 8
significant bits. The emulation only picks numbers: the Bend checker
decides.

File format, one record per line, numbers as binary strings (a dyadic is
"mantissa:exponent", meaning mantissa * 2^-exponent; "-" for negative):
    N P
    the box centers (2(N + 2) dyadics)
    the box radii
    the distances r_2 s_2 r_3 s_3 ... (positive binary integers)
    per block: yc(2) yr(2) q Y(2 x 2, by rows) pc(4) pr(4)
"""
import math, random, sys
from fractions import Fraction as Fr
import mpmath

name = sys.argv[1] if len(sys.argv) > 1 else 'well'
P = int(sys.argv[2]) if len(sys.argv) > 2 else 96
N = int(sys.argv[3]) if len(sys.argv) > 3 else 30
# sabotage (to see the checker refuse): "halve:j" halves block j's radius
# after the radii are chosen; "shift:j" moves block j's center by 2^-(P/2)
mode = sys.argv[4] if len(sys.argv) > 4 else 'ok'
L = 50_000_000
random.seed(7)

# proto/gen_chain_run.py's strips (same random draws, in the same order)
def chain(eta, jitter):
    raw = []
    for k in range(N + 2):
        m, odd = divmod(k, 2)
        x = m * L + (L / 2 if odd else 0.0)
        y = eta * L if odd else 0.0
        if k >= 2:
            x += random.uniform(-jitter, jitter); y += random.uniform(-jitter, jitter)
        raw.append((x, y))
    phi = math.atan2(raw[1][1], raw[1][0]); c, s_ = math.cos(-phi), math.sin(-phi)
    pts = [(x * c - y * s_, x * s_ + y * c) for (x, y) in raw]
    L1 = round(math.hypot(*raw[1]))
    pts[0], pts[1] = (0.0, 0.0), (float(L1), 0.0)
    steps = []
    for k in range(2, N + 2):
        a, b, p = pts[k - 2], pts[k - 1], pts[k]
        r = round(math.dist(a, p)); s = round(math.dist(b, p))
        cross = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
        steps.append((r, s, cross > 0))
    return L1, steps

chains = {"well": chain(math.sqrt(3) / 2, 300_000), "flat": chain(0.08, 30_000)}
L1, steps = chains[name]

# the exact solution, to P + 64 bits
mpmath.mp.prec = P + 64
sol = [(mpmath.mpf(0), mpmath.mpf(0)), (mpmath.mpf(L1), mpmath.mpf(0))]
for (r, s, left) in steps:
    a, b = sol[-2], sol[-1]
    dx, dy = b[0] - a[0], b[1] - a[1]; D = dx * dx + dy * dy
    k = (D + r * r - s * s) / (2 * D); h = mpmath.sqrt(r * r - k * k * D) / mpmath.sqrt(D)
    sg = 1 if left else -1
    sol.append((a[0] + k * dx - sg * h * dy, a[1] + k * dy + sg * h * dx))

def rnd(x, e):
    return Fr(int(mpmath.nint(x * mpmath.mpf(2) ** e)), 2 ** e)

# round up to 8 significant bits
def up8(x):
    if x == 0:
        return Fr(1, 2 ** (P + 8))
    e = 8 - math.floor(math.log2(x))
    return Fr(math.ceil(x * Fr(2) ** e)) / Fr(2) ** e

def sig32(x):
    if x == 0:
        return Fr(0)
    e = 32 - math.floor(math.log2(abs(x)))
    return Fr(round(x * Fr(2) ** e)) / Fr(2) ** e

gc = [Fr(0), Fr(0), Fr(L1), Fr(0)]
gr = [Fr(0)] * 4
blocks = []
q = Fr(1, 2)
for j, (r, s, left) in enumerate(steps):
    k = j + 2
    y = (rnd(sol[k][0], P), rnd(sol[k][1], P))
    a, b = (gc[2 * k - 4], gc[2 * k - 3]), (gc[2 * k - 2], gc[2 * k - 1])
    ra, rb = (gr[2 * k - 4], gr[2 * k - 3]), (gr[2 * k - 2], gr[2 * k - 1])
    u = (y[0] - a[0], y[1] - a[1]); v = (y[0] - b[0], y[1] - b[1])
    f = [u[0] ** 2 + u[1] ** 2 - r * r, v[0] ** 2 + v[1] ** 2 - s * s]
    J = [[2 * u[0], 2 * u[1]], [2 * v[0], 2 * v[1]]]
    det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
    Y = [[sig32(J[1][1] / det), sig32(-J[0][1] / det)], [sig32(-J[1][0] / det), sig32(J[0][0] / det)]]
    aY = [[abs(x) for x in row] for row in Y]
    Yf = [abs(Y[i][0] * f[0] + Y[i][1] * f[1]) for i in range(2)]
    IYJ = [[abs((1 if i == l else 0) - (Y[i][0] * J[0][l] + Y[i][1] * J[1][l])) for l in range(2)] for i in range(2)]

    def conds(R):
        # slope spreads: row 1 is |y - a|^2, row 2 |y - b|^2; per coordinate c
        # the spread is 2 (R + rho_c) (doubled here for safety)
        dy = [[4 * (R + ra[c]) for c in range(2)], [4 * (R + rb[c]) for c in range(2)]]
        G = [[IYJ[i][l] + aY[i][0] * dy[0][l] + aY[i][1] * dy[1][l] for l in range(2)] for i in range(2)]
        # parameter part: row 1 against a (|J| = |2u|), row 2 against b
        za = [abs(J[0][c]) + dy[0][c] for c in range(2)]
        zb = [abs(J[1][c]) + dy[1][c] for c in range(2)]
        zp = [aY[i][0] * (za[0] * ra[0] + za[1] * ra[1]) + aY[i][1] * (zb[0] * rb[0] + zb[1] * rb[1]) for i in range(2)]
        Gr = [G[i][0] * R + G[i][1] * R for i in range(2)]
        ok1 = all(Gr[i] <= q * R for i in range(2))
        ok2 = all(Yf[i] + zp[i] + Gr[i] <= R for i in range(2))
        need = max(Yf[i] + zp[i] for i in range(2))
        return ok1 and ok2, need

    _, need = conds(Fr(0))
    R = up8(need * Fr(102, 100))
    while not conds(R)[0]:
        R = up8(R * Fr(102, 100))
        if R > L:
            sys.exit('%s P=%d N=%d: no radius contracts at block %d (P too small)' % (name, P, N, j))
    if mode == 'halve:%d' % j:
        R = R / 2
    if mode == 'shift:%d' % j:
        y = (y[0] + Fr(1, 2 ** (P // 2)), y[1])
    gc += [y[0], y[1]]
    gr += [R, R]
    blocks.append((list(y), [R, R], q, Y, [a[0], a[1], b[0], b[1]], [ra[0], ra[1], rb[0], rb[1]]))

def zbin(m):
    if m == 0:
        return '0'
    return ('-' if m < 0 else '') + bin(abs(m))[2:]

def dy(x):
    # x is dyadic: m / 2^e
    d = x.denominator
    assert d & (d - 1) == 0, x
    return zbin(x.numerator) + ':' + str(d.bit_length() - 1)

out = ['%d %d' % (N, P), ' '.join(map(dy, gc)), ' '.join(map(dy, gr)),
       ' '.join(bin(x)[2:] for (r, s, _) in steps for x in (r, s))]
for (yc, yr, qq, Y, pc, pr) in blocks:
    out.append(' '.join(map(dy, yc + yr + [qq] + Y[0] + Y[1] + pc + pr)))
open('proto/plan_chain.txt', 'w').write('\n'.join(out) + '\n')
last = gr[-1]
print('%s P=%d N=%d: last radius 2^%.1f nm' % (name, P, N, math.log2(last)))
