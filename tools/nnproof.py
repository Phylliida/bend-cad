# Nonnegativity proofs for drafts: for an expression built from +, *,
# the numbers 0 and 1, and atoms (or listed subterms such as "1 - u")
# whose proofs of 0 <= . are given, emit the FO.nonneg_add / mul_nonneg
# term proving 0 <= expr, with @FT[set | ...] subterms for expand.py.
# Usage (from a generator script):
#   import sys; sys.path.insert(0, "tools"); import nnproof
#   nnproof.nn("((s*G)*(1 - u))*(1 + G)", "set", {"s": "hs", "G": "hg", "(1 - u)": "h1u"})
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zexpr

def unparse(a):
    k = a[0]
    if k == 'var': return a[1]
    if k == 'num': return str(a[1])
    if k == 'neg': return '-(' + unparse(a[1]) + ')'
    return '(' + unparse(a[1]) + ' ' + k + ' ' + unparse(a[2]) + ')'

def nn(expr, setname, table):
    def go(a):
        u = unparse(a)
        if u in table: return table[u]
        k = a[0]
        if k == 'num' and a[1] == 1: return "NP.one_nn(~F)"
        if k == 'num' and a[1] == 0: return "FO.le_refl(~F, @0)"
        if k == 'var': raise Exception("no nonneg proof for atom " + u)
        if k in ('+', '*'):
            f = "FO.nonneg_add" if k == '+' else "FO.mul_nonneg"
            return "%s(~F, @FT[%s | %s], @FT[%s | %s], %s, %s)" % (f, setname, unparse(a[1]), setname, unparse(a[2]), go(a[1]), go(a[2]))
        raise Exception("cannot prove nonneg: " + u)
    return go(zexpr.parse(expr))
