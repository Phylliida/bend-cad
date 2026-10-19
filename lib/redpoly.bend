# bend-cad: the normal forms of lib/zring.bend are reduced (PLAN-sk13a S1).
# A polynomial is reduced (red) when its terms ascend strictly by monomial
# (NR.mcmp, lexicographic), no coefficient is zero, and every monomial is
# sorted (each variable at most the ones after it). R.norm's output is
# reduced for every expression (norm_red). Proofs only; the normalizer is
# unchanged.

import Base
import ./natring.bend as NR
import ./zring.bend as R
import ./karith.bend as KA
import ../spec/num.bend as S
import ../spec/ring.bend as E

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Comparisons
# -----------

def islt(o: Cmp) -> Bool:
  match o:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def ncmp_refl(x: Nat) -> {EQ{} == Nat.cmp(x, x) : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      ncmp_refl(y)

def ncmp_gt(x: Nat, y: Nat, e: {GT{} == Nat.cmp(x, y) : Cmp}) -> {LT{} == Nat.cmp(y, x) : Cmp}:
  match x y:
    case 0n 0n:
      %e : NR.CmpD(_, Unit, {LT{} == Nat.cmp(0n, 0n) : Cmp}, Unit)
      Unit{}
    case 0n 1n+q:
      %e : NR.CmpD(_, {LT{} == Nat.cmp(1n+q, 0n) : Cmp}, Unit, Unit)
      Unit{}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ncmp_gt(p, q, e)

def ncmp_trans(x: Nat, y: Nat, z: Nat, e1: {LT{} == Nat.cmp(x, y) : Cmp}, e2: {LT{} == Nat.cmp(y, z) : Cmp}) -> {LT{} == Nat.cmp(x, z) : Cmp}:
  match x y z:
    case 0n 0n 0n:
      %e1 : NR.CmpD(_, Unit, {LT{} == Nat.cmp(0n, 0n) : Cmp}, Unit)
      Unit{}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == Nat.cmp(0n, 0n) : Cmp})
      Unit{}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == Nat.cmp(1n+p, 0n) : Cmp})
      Unit{}
    case 1n+p 0n 1n+r:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == Nat.cmp(1n+p, 1n+r) : Cmp})
      Unit{}
    case 1n+p 1n+q 0n:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == Nat.cmp(1n+p, 0n) : Cmp})
      Unit{}
    case 1n+p 1n+q 1n+r:
      ncmp_trans(p, q, r, e1, e2)

# Monomial order: reflexive, flips, transitive
# --------------------------------------------

def mcmp_refl(m: List<&2, Nat>) -> {EQ{} == NR.mcmp(m, m) : Cmp}:
  match m:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      %ncmp_refl(x) : {EQ{} == NR.mcmp.dec(_, NR.mcmp(xs, xs)) : Cmp}
      mcmp_refl(xs)

def mcmp_gt.dec(o: Cmp, +x: Nat, +y: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>,
  eo: {o == Nat.cmp(x, y) : Cmp}, e: {GT{} == NR.mcmp.dec(o, NR.mcmp(xs, ys)) : Cmp},
  rec: {GT{} == NR.mcmp(xs, ys) : Cmp} -> {LT{} == NR.mcmp(ys, xs) : Cmp})
  -> {LT{} == NR.mcmp.dec(Nat.cmp(y, x), NR.mcmp(ys, xs)) : Cmp}:
  match o:
    case LT{}:
      %e : NR.CmpD(_, {LT{} == NR.mcmp.dec(Nat.cmp(y, x), NR.mcmp(ys, xs)) : Cmp}, Unit, Unit)
      Unit{}
    case EQ{}:
      %Equal.sym(Nat, x, y, NR.nat_cmp_eq(x, y, eo)) : {LT{} == NR.mcmp.dec(Nat.cmp(y, _), NR.mcmp(ys, xs)) : Cmp}
      %ncmp_refl(y) : {LT{} == NR.mcmp.dec(_, NR.mcmp(ys, xs)) : Cmp}
      rec(e)
    case GT{}:
      %ncmp_gt(x, y, eo) : {LT{} == NR.mcmp.dec(_, NR.mcmp(ys, xs)) : Cmp}
      {==}

def mcmp_gt(m: List<&2, Nat>, n: List<&2, Nat>, e: {GT{} == NR.mcmp(m, n) : Cmp}) -> {LT{} == NR.mcmp(n, m) : Cmp}:
  match m n:
    case Nil{} Nil{}:
      %e : NR.CmpD(_, Unit, {LT{} == NR.mcmp(Nil{}, Nil{}) : Cmp}, Unit)
      Unit{}
    case Nil{} Con{y, ys}:
      %e : NR.CmpD(_, {LT{} == NR.mcmp(Con{y, ys}, Nil{}) : Cmp}, Unit, Unit)
      Unit{}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      mcmp_gt.dec(Nat.cmp(x, y), x, y, xs, ys, {==}, e, ee => mcmp_gt(xs, ys, ee))

def mlt_trans.dec(o1: Cmp, o2: Cmp, +x: Nat, +y: Nat, +z: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, +zs: List<&2, Nat>,
  eo1: {o1 == Nat.cmp(x, y) : Cmp}, eo2: {o2 == Nat.cmp(y, z) : Cmp},
  e1: {LT{} == NR.mcmp.dec(o1, NR.mcmp(xs, ys)) : Cmp}, e2: {LT{} == NR.mcmp.dec(o2, NR.mcmp(ys, zs)) : Cmp},
  rec: {LT{} == NR.mcmp(xs, ys) : Cmp} -> {LT{} == NR.mcmp(ys, zs) : Cmp} -> {LT{} == NR.mcmp(xs, zs) : Cmp})
  -> {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp}:
  match o1 o2:
    case LT{} LT{}:
      %ncmp_trans(x, y, z, eo1, eo2) : {LT{} == NR.mcmp.dec(_, NR.mcmp(xs, zs)) : Cmp}
      {==}
    case LT{} EQ{}:
      %NR.nat_cmp_eq(y, z, eo2) : {LT{} == NR.mcmp.dec(Nat.cmp(x, _), NR.mcmp(xs, zs)) : Cmp}
      %eo1 : {LT{} == NR.mcmp.dec(_, NR.mcmp(xs, zs)) : Cmp}
      {==}
    case LT{} GT{}:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp})
      Unit{}
    case EQ{} LT{}:
      %Equal.sym(Nat, x, y, NR.nat_cmp_eq(x, y, eo1)) : {LT{} == NR.mcmp.dec(Nat.cmp(_, z), NR.mcmp(xs, zs)) : Cmp}
      %eo2 : {LT{} == NR.mcmp.dec(_, NR.mcmp(xs, zs)) : Cmp}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Nat, x, y, NR.nat_cmp_eq(x, y, eo1)) : {LT{} == NR.mcmp.dec(Nat.cmp(_, z), NR.mcmp(xs, zs)) : Cmp}
      %eo2 : {LT{} == NR.mcmp.dec(_, NR.mcmp(xs, zs)) : Cmp}
      rec(e1, e2)
    case EQ{} GT{}:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp})
      Unit{}
    case GT{} LT{}:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp})
      Unit{}
    case GT{} EQ{}:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp})
      Unit{}
    case GT{} GT{}:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp.dec(Nat.cmp(x, z), NR.mcmp(xs, zs)) : Cmp})
      Unit{}

def mlt_trans(a: List<&2, Nat>, b: List<&2, Nat>, c: List<&2, Nat>, e1: {LT{} == NR.mcmp(a, b) : Cmp}, e2: {LT{} == NR.mcmp(b, c) : Cmp}) -> {LT{} == NR.mcmp(a, c) : Cmp}:
  match a b c:
    case Nil{} Nil{} Nil{}:
      %e1 : NR.CmpD(_, Unit, {LT{} == NR.mcmp(Nil{}, Nil{}) : Cmp}, Unit)
      Unit{}
    case Nil{} Nil{} Con{z, zs}:
      {==}
    case Nil{} Con{y, ys} Nil{}:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp(Nil{}, Nil{}) : Cmp})
      Unit{}
    case Nil{} Con{y, ys} Con{z, zs}:
      {==}
    case Con{x, xs} Nil{} Nil{}:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp(Con{x, xs}, Nil{}) : Cmp})
      Unit{}
    case Con{x, xs} Nil{} Con{z, zs}:
      %e1 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp(Con{x, xs}, Con{z, zs}) : Cmp})
      Unit{}
    case Con{x, xs} Con{y, ys} Nil{}:
      %e2 : NR.CmpD(_, Unit, Unit, {LT{} == NR.mcmp(Con{x, xs}, Nil{}) : Cmp})
      Unit{}
    case Con{+x, +xs} Con{+y, +ys} Con{+z, +zs}:
      mlt_trans.dec(Nat.cmp(x, y), Nat.cmp(y, z), x, y, z, xs, ys, zs, {==}, {==}, e1, e2, ea => eb => mlt_trans(xs, ys, zs, ea, eb))

# Sorted monomials
# ----------------

# every variable of m is at least x
def mge(+x: Nat, m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{y, ys}:
      KA.band(KA.natle(x, y), mge(x, ys))

def msort(m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{+y, +ys}:
      KA.band(mge(y, ys), msort(ys))

def mge_trans(+x: Nat, +y: Nat, m: List<&2, Nat>, +h1: {KA.natle(x, y) == True{} : Bool}, +h2: {mge(y, m) == True{} : Bool}) -> {mge(x, m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+z, +zs}:
      KA.band_i(KA.natle(x, z), mge(x, zs), KA.natle_trans(x, y, z, h1, KA.band_l(KA.natle(y, z), mge(y, zs), h2)), mge_trans(x, y, zs, h1, KA.band_r(KA.natle(y, z), mge(y, zs), h2)))

def isle_true(x: Nat, y: Nat, e: {True{} == Nat.is_le(x, y) : Bool}) -> {KA.natle(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({KA.natle(1n+p, 0n) == True{} : Bool}, KA.tf(e))
    case 1n+p 1n+q:
      isle_true(p, q, e)

def isle_false(x: Nat, y: Nat, e: {False{} == Nat.is_le(x, y) : Bool}) -> {KA.natle(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      absurd({KA.natle(0n, 0n) == True{} : Bool}, KA.ft(e))
    case 0n 1n+q:
      absurd({KA.natle(1n+q, 0n) == True{} : Bool}, KA.ft(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      isle_false(p, q, e)

def mge_minsert.dec(b: Bool, +h: Nat, +x: Nat, +y: Nat, +t: List<&2, Nat>,
  hx: {KA.natle(h, x) == True{} : Bool}, hy: {KA.natle(h, y) == True{} : Bool}, ht: {mge(h, t) == True{} : Bool},
  rec: {mge(h, NR.minsert(x, t)) == True{} : Bool})
  -> {mge(h, NR.minsert.dec(b, x, y, t, NR.minsert(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      KA.band_i(KA.natle(h, x), mge(h, Con{y, t}), hx, KA.band_i(KA.natle(h, y), mge(h, t), hy, ht))
    case False{}:
      KA.band_i(KA.natle(h, y), mge(h, NR.minsert(x, t)), hy, rec)

def mge_minsert(+h: Nat, +x: Nat, m: List<&2, Nat>, +hx: {KA.natle(h, x) == True{} : Bool}, +hm: {mge(h, m) == True{} : Bool}) -> {mge(h, NR.minsert(x, m)) == True{} : Bool}:
  match m:
    case Nil{}:
      KA.band_i(KA.natle(h, x), True{}, hx, {==})
    case Con{+y, +t}:
      mge_minsert.dec(Nat.is_le(x, y), h, x, y, t, hx, KA.band_l(KA.natle(h, y), mge(h, t), hm), KA.band_r(KA.natle(h, y), mge(h, t), hm),
        mge_minsert(h, x, t, hx, KA.band_r(KA.natle(h, y), mge(h, t), hm)))

def minsert_sort.dec(b: Bool, +x: Nat, +y: Nat, +t: List<&2, Nat>, eb: {b == Nat.is_le(x, y) : Bool},
  +hs: {msort(Con{y, t}) == True{} : Bool}, rec: {msort(NR.minsert(x, t)) == True{} : Bool})
  -> {msort(NR.minsert.dec(b, x, y, t, NR.minsert(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      +hxy = isle_true(x, y, eb)
      KA.band_i(mge(x, Con{y, t}), msort(Con{y, t}), KA.band_i(KA.natle(x, y), mge(x, t), hxy, mge_trans(x, y, t, hxy, KA.band_l(mge(y, t), msort(t), hs))), hs)
    case False{}:
      KA.band_i(mge(y, NR.minsert(x, t)), msort(NR.minsert(x, t)), mge_minsert(y, x, t, isle_false(x, y, eb), KA.band_l(mge(y, t), msort(t), hs)), rec)

def minsert_sort(+x: Nat, m: List<&2, Nat>, +h: {msort(m) == True{} : Bool}) -> {msort(NR.minsert(x, m)) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      minsert_sort.dec(Nat.is_le(x, y), x, y, t, {==}, h, minsert_sort(x, t, KA.band_r(mge(y, t), msort(t), h)))

def mmul_sort(m1: List<&2, Nat>, +m2: List<&2, Nat>, +h: {msort(m2) == True{} : Bool}) -> {msort(NR.mmul(m1, m2)) == True{} : Bool}:
  match m1:
    case Nil{}:
      h
    case Con{+v, +vs}:
      minsert_sort(v, NR.mmul(vs, m2), mmul_sort(vs, m2, h))

# Reduced polynomials
# -------------------

def nz(c: S.Z) -> Bool:
  match c:
    case S.Z0{}:
      False{}
    case S.Zpos{p}:
      True{}
    case S.Zneg{p}:
      True{}

# m is below every monomial of p
def mlts(+m: List<&2, Nat>, p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{d, n}, rest}:
      KA.band(islt(NR.mcmp(m, n)), mlts(m, rest))

def red(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))))

def red_c(+c: S.Z, +m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, h: {red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}) -> {nz(c) == True{} : Bool}:
  KA.band_l(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))), h)

def red_m(+c: S.Z, +m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, h: {red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}) -> {msort(m) == True{} : Bool}:
  KA.band_l(msort(m), KA.band(mlts(m, rest), red(rest)), KA.band_r(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))), h))

def red_l(+c: S.Z, +m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, h: {red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}) -> {mlts(m, rest) == True{} : Bool}:
  KA.band_l(mlts(m, rest), red(rest), KA.band_r(msort(m), KA.band(mlts(m, rest), red(rest)), KA.band_r(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))), h)))

def red_r(+c: S.Z, +m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, h: {red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}) -> {red(rest) == True{} : Bool}:
  KA.band_r(mlts(m, rest), red(rest), KA.band_r(msort(m), KA.band(mlts(m, rest), red(rest)), KA.band_r(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))), h)))

def red_mk(+c: S.Z, +m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, hc: {nz(c) == True{} : Bool}, hm: {msort(m) == True{} : Bool}, hl: {mlts(m, rest) == True{} : Bool}, hr: {red(rest) == True{} : Bool}) -> {red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}:
  KA.band_i(nz(c), KA.band(msort(m), KA.band(mlts(m, rest), red(rest))), hc, KA.band_i(msort(m), KA.band(mlts(m, rest), red(rest)), hm, KA.band_i(mlts(m, rest), red(rest), hl, hr)))

def lt_of(+o: Cmp, e: {LT{} == o : Cmp}) -> {islt(o) == True{} : Bool}:
  %e : {islt(_) == True{} : Bool}
  {==}

def of_lt(o: Cmp, h: {islt(o) == True{} : Bool}) -> {LT{} == o : Cmp}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      absurd({LT{} == EQ{} : Cmp}, KA.ft(h))
    case GT{}:
      absurd({LT{} == GT{} : Cmp}, KA.ft(h))

def mlts_trans(+k: List<&2, Nat>, +m: List<&2, Nat>, p: List<&2, R.ZTerm>, +hk: {LT{} == NR.mcmp(k, m) : Cmp}, +hp: {mlts(m, p) == True{} : Bool}) -> {mlts(k, p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{d, +n}, +rest}:
      KA.band_i(islt(NR.mcmp(k, n)), mlts(k, rest),
        lt_of(NR.mcmp(k, n), mlt_trans(k, m, n, hk, of_lt(NR.mcmp(m, n), KA.band_l(islt(NR.mcmp(m, n)), mlts(m, rest), hp)))),
        mlts_trans(k, m, rest, hk, KA.band_r(islt(NR.mcmp(m, n)), mlts(m, rest), hp)))

def pcoef_lts(+k: List<&2, Nat>, s: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>, hn: {islt(NR.mcmp(k, n)) == True{} : Bool}, hr: {mlts(k, rest) == True{} : Bool}) -> {mlts(k, R.pcoef(s, n, rest)) == True{} : Bool}:
  match s:
    case S.Z0{}:
      hr
    case S.Zpos{p}:
      KA.band_i(islt(NR.mcmp(k, n)), mlts(k, rest), hn, hr)
    case S.Zneg{p}:
      KA.band_i(islt(NR.mcmp(k, n)), mlts(k, rest), hn, hr)

def pcoef_red(s: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>, hn: {msort(n) == True{} : Bool}, hl: {mlts(n, rest) == True{} : Bool}, hr: {red(rest) == True{} : Bool}) -> {red(R.pcoef(s, n, rest)) == True{} : Bool}:
  match s:
    case S.Z0{}:
      hr
    case S.Zpos{p}:
      red_mk(S.Zpos{p}, n, rest, {==}, hn, hl, hr)
    case S.Zneg{p}:
      red_mk(S.Zneg{p}, n, rest, {==}, hn, hl, hr)

def pins_lts.dec(o: Cmp, +k: List<&2, Nat>, +c: S.Z, +m: List<&2, Nat>, +d: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>,
  hk: {LT{} == NR.mcmp(k, m) : Cmp}, hn: {islt(NR.mcmp(k, n)) == True{} : Bool}, hr: {mlts(k, rest) == True{} : Bool},
  rec: {mlts(k, R.pins(c, m, rest)) == True{} : Bool})
  -> {mlts(k, R.pins.dec(o, c, m, d, n, rest, R.pins(c, m, rest))) == True{} : Bool}:
  match o:
    case LT{}:
      KA.band_i(islt(NR.mcmp(k, m)), mlts(k, Con{R.ZTerm{d, n}, rest}), lt_of(NR.mcmp(k, m), hk), KA.band_i(islt(NR.mcmp(k, n)), mlts(k, rest), hn, hr))
    case EQ{}:
      pcoef_lts(k, S.Z.add(c, d), n, rest, hn, hr)
    case GT{}:
      KA.band_i(islt(NR.mcmp(k, n)), mlts(k, R.pins(c, m, rest)), hn, rec)

def pins_lts(+k: List<&2, Nat>, +c: S.Z, +m: List<&2, Nat>, p: List<&2, R.ZTerm>, +hk: {LT{} == NR.mcmp(k, m) : Cmp}, +hp: {mlts(k, p) == True{} : Bool}) -> {mlts(k, R.pins(c, m, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      KA.band_i(islt(NR.mcmp(k, m)), True{}, lt_of(NR.mcmp(k, m), hk), {==})
    case Con{R.ZTerm{+d, +n}, +rest}:
      pins_lts.dec(NR.mcmp(m, n), k, c, m, d, n, rest, hk, KA.band_l(islt(NR.mcmp(k, n)), mlts(k, rest), hp), KA.band_r(islt(NR.mcmp(k, n)), mlts(k, rest), hp),
        pins_lts(k, c, m, rest, hk, KA.band_r(islt(NR.mcmp(k, n)), mlts(k, rest), hp)))

def pins_red.dec(o: Cmp, +c: S.Z, +m: List<&2, Nat>, +d: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>,
  +eo: {o == NR.mcmp(m, n) : Cmp}, hc: {nz(c) == True{} : Bool}, hm: {msort(m) == True{} : Bool},
  +hp: {red(Con{R.ZTerm{d, n}, rest}) == True{} : Bool}, rec: {red(R.pins(c, m, rest)) == True{} : Bool})
  -> {red(R.pins.dec(o, c, m, d, n, rest, R.pins(c, m, rest))) == True{} : Bool}:
  match o:
    case LT{}:
      red_mk(c, m, Con{R.ZTerm{d, n}, rest}, hc, hm,
        KA.band_i(islt(NR.mcmp(m, n)), mlts(m, rest), lt_of(NR.mcmp(m, n), eo), mlts_trans(m, n, rest, eo, red_l(d, n, rest, hp))), hp)
    case EQ{}:
      pcoef_red(S.Z.add(c, d), n, rest, red_m(d, n, rest, hp), red_l(d, n, rest, hp), red_r(d, n, rest, hp))
    case GT{}:
      red_mk(d, n, R.pins(c, m, rest), red_c(d, n, rest, hp), red_m(d, n, rest, hp), pins_lts(n, c, m, rest, mcmp_gt(m, n, eo), red_l(d, n, rest, hp)), rec)

def pins_red(+c: S.Z, +m: List<&2, Nat>, p: List<&2, R.ZTerm>, +hc: {nz(c) == True{} : Bool}, +hm: {msort(m) == True{} : Bool}, +hp: {red(p) == True{} : Bool}) -> {red(R.pins(c, m, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      red_mk(c, m, Nil{}, hc, hm, {==}, {==})
    case Con{R.ZTerm{+d, +n}, +rest}:
      pins_red.dec(NR.mcmp(m, n), c, m, d, n, rest, {==}, hc, hm, hp, pins_red(c, m, rest, hc, hm, red_r(d, n, rest, hp)))

def pinsert_red(c: S.Z, +m: List<&2, Nat>, +p: List<&2, R.ZTerm>, hm: {msort(m) == True{} : Bool}, hp: {red(p) == True{} : Bool}) -> {red(R.pinsert(c, m, p)) == True{} : Bool}:
  match c:
    case S.Z0{}:
      hp
    case S.Zpos{q}:
      pins_red(S.Zpos{q}, m, p, {==}, hm, hp)
    case S.Zneg{q}:
      pins_red(S.Zneg{q}, m, p, {==}, hm, hp)

def padd_red(p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, +hp: {red(p) == True{} : Bool}, +hq: {red(q) == True{} : Bool}) -> {red(R.padd(p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      hq
    case Con{R.ZTerm{+c, +m}, +rest}:
      pinsert_red(c, m, R.padd(rest, q), red_m(c, m, rest, hp), padd_red(rest, q, red_r(c, m, rest, hp), hq))

def pscale_red(+c: S.Z, +m: List<&2, Nat>, q: List<&2, R.ZTerm>, +hq: {red(q) == True{} : Bool}) -> {red(R.pscale(c, m, q)) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+d, +n}, +rest}:
      pinsert_red(S.Z.mul(c, d), NR.mmul(m, n), R.pscale(c, m, rest), mmul_sort(m, n, red_m(d, n, rest, hq)), pscale_red(c, m, rest, red_r(d, n, rest, hq)))

def pmul_red(p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, +hq: {red(q) == True{} : Bool}) -> {red(R.pmul(p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      padd_red(R.pscale(c, m, q), R.pmul(rest, q), pscale_red(c, m, q, hq), pmul_red(rest, q, hq))

def neg_nz(c: S.Z, h: {nz(c) == True{} : Bool}) -> {nz(S.Z.neg(c)) == True{} : Bool}:
  match c:
    case S.Z0{}:
      absurd({nz(S.Z.neg(S.Z0{})) == True{} : Bool}, KA.ft(h))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def lts_neg(+k: List<&2, Nat>, p: List<&2, R.ZTerm>, +h: {mlts(k, p) == True{} : Bool}) -> {mlts(k, R.pneg(p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +n}, +rest}:
      KA.band_i(islt(NR.mcmp(k, n)), mlts(k, R.pneg(rest)), KA.band_l(islt(NR.mcmp(k, n)), mlts(k, rest), h), lts_neg(k, rest, KA.band_r(islt(NR.mcmp(k, n)), mlts(k, rest), h)))

def pneg_red(p: List<&2, R.ZTerm>, +hp: {red(p) == True{} : Bool}) -> {red(R.pneg(p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      red_mk(S.Z.neg(c), m, R.pneg(rest), neg_nz(c, red_c(c, m, rest, hp)), red_m(c, m, rest, hp), lts_neg(m, rest, red_l(c, m, rest, hp)), pneg_red(rest, red_r(c, m, rest, hp)))

def pconst_red(c: S.Z) -> {red(R.pconst(c)) == True{} : Bool}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

# every normal form is reduced
def norm_red(e: E.ZExpr) -> {red(R.norm(e)) == True{} : Bool}:
  match e:
    case E.ZVar{i}:
      {==}
    case E.ZCst{c}:
      pconst_red(c)
    case E.ZAdd{+a, +b}:
      padd_red(R.norm(a), R.norm(b), norm_red(a), norm_red(b))
    case E.ZSub{+a, +b}:
      padd_red(R.norm(a), R.pneg(R.norm(b)), norm_red(a), pneg_red(R.norm(b), norm_red(b)))
    case E.ZMul{+a, +b}:
      pmul_red(R.norm(a), R.norm(b), norm_red(b))
    case E.ZNeg{+a}:
      pneg_red(R.norm(a), norm_red(a))
