#!/usr/bin/env python3
"""Exact null spaces of one block's Jacobian, named by constraint.

Usage: python3 tools/diag/nullspace.py owners.json block_owners.txt block_jac.txt

- owners.json: from tools/diag/owners.mjs (request position -> GUI constraint)
- block_owners.txt: proto/probe_block stage 5 output ("owners ...", "vars ...")
- block_jac.txt: proto/probe_block stage 4 output ("jac", then "row m:e ...")

Prints the rank, each left null vector (a dependency among the block's
equations: a self-stress), and each right null vector (a free direction:
a flex), computed exactly with fractions.
"""
import json, sys
from fractions import Fraction as Fr

def dy(t):
    m, e = t.split(':'); neg = m.startswith('-'); m = m.lstrip('-')
    v = Fr(int(m, 2) if m else 0, 2 ** int(e)); return -v if neg else v

def nullspace(A):
    A = [r[:] for r in A]; rows, cols = len(A), len(A[0]); piv = []; r = 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; inv = 1 / A[r][c]; A[r] = [x * inv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
    basis = []
    for fcol in (c for c in range(cols) if c not in piv):
        v = [Fr(0)] * cols; v[fcol] = Fr(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fcol]
        basis.append(v)
    return len(piv), basis

own = json.load(open(sys.argv[1]))
lines = open(sys.argv[2]).read().split('\n')
rows_own = [int(t) for t in lines[0].split()[1:]]
cols_var = [int(t) for t in lines[1].split()[1:]]
J = [[dy(t) for t in l.split()[1:]] for l in open(sys.argv[3]).read().split('\n') if l.startswith('row')]
rank, right = nullspace(J)
_, left = nullspace([list(c) for c in zip(*J)])
print('J is %d x %d, rank %d' % (len(J), len(J[0]), rank))
for v in left:
    print('dependent equations (left null vector):')
    for i, x in enumerate(v):
        if x != 0: print('   %+.4f  eq %2d  %s' % (float(x), i, own[rows_own[i]]))
for v in right:
    print('free direction (right null vector):')
    for i, x in enumerate(v):
        if x != 0: print('   %+.4f  var %d' % (float(x), cols_var[i]))
