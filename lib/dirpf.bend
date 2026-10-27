# bend-cad: the direction calculus is sound (PLAN-sk13b B1). In every
# ordered field, wherever a derivation's facts hold (each where its own nd
# is nonzero) and the segments of its nd have nonzero length, what it
# proves holds: K(e) means e evaluates to 0, par(a, x) that cross(z_a, x)
# does. One lemma per rule; each is a polynomial identity with the
# hypotheses as certificate terms (lib/ford.bend), checked by the
# normalizer (lib/fring.bend), and a cancellation of a nonzero squared
# length where the rule names a segment. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/geom.bend as G
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./identpf.bend as IP
import ./meaning.bend as MN

# What a judgment, a statement and a fact mean
# --------------------------------------------

def ev(~F: O.OField, +env: List<&2, O.C(F)>, e: E.QExpr) -> O.C(F):
  O.eval(~F, env, e)

# cross(u, x) evaluated
def evc(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE) -> O.C(F):
  O.eval(~F, env, SK.VE.cross(u, x))

# a reusable either (Base's Or is affine)
def DOr(-A: Data, -B: Data) -> Data:
  Either<&2, &2, A, B>

def Holds(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, j: DR.Jd) -> Data:
  match j:
    case DR.JK{+e}:
      {ev(~F, env, e) == O.zero(F) : O.C(F)}
    case DR.JP{+a, +x}:
      {evc(~F, env, DR.zdir(es, a), x) == O.zero(F) : O.C(F)}

def StatHolds(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, DR.DStat>) -> Data:
  match m:
    case Some{DR.DStat{+a, +x, l}}:
      {evc(~F, env, DR.zseg(es, a), x) == O.zero(F) : O.C(F)}
    case None{}:
      Unit

# some segment of nd has squared length 0
def Short(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>) -> Data:
  match nd:
    case Nil{}:
      {False{} == True{} : Bool}
    case Con{+s, t}:
      DOr({ev(~F, env, SK.VE.norm2(DR.zseg(es, s))) == O.zero(F) : O.C(F)}, Short(~F, env, es, t))

# a fact holds where its own nd is nonzero: some nd segment has squared
# length 0, or its equation and its direction statement hold (a reusable
# form of "nd nonzero implies the fact")
def FactHolds(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, f: DR.Fact) -> Data:
  match f:
    case DR.Fact{+e, +nd, +ds}:
      DOr(Short(~F, env, es, nd), SK.Both({ev(~F, env, e) == O.zero(F) : O.C(F)}, StatHolds(~F, env, es, ds)))

def AllFacts(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, fs: List<&2, DR.Fact>) -> Data:
  match fs:
    case Nil{}:
      Unit
    case Con{+f, t}:
      SK.Both(FactHolds(~F, env, es, f), AllFacts(~F, env, es, t))

def MHolds(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, DR.Fact>) -> Data:
  match m:
    case Some{+f}:
      FactHolds(~F, env, es, f)
    case None{}:
      Unit

def fact_at_ok(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, fs: List<&2, DR.Fact>, i: Nat, h: AllFacts(~F, env, es, fs)) -> MHolds(~F, env, es, DR.fact_at(fs, i)):
  match fs i:
    case Nil{} i:
      Unit{}
    case Con{f, t} 0n:
      (hf, ht) = h
      hf
    case Con{f, t} 1n+j:
      (hf, ht) = h
      fact_at_ok(~F, env, es, t, j, ht)

# Field helpers
# -------------

def same_ev(~F: O.OField, +env: List<&2, O.C(F)>, +e1: E.QExpr, +e2: E.QExpr, h: DR.Same(e1, e2)) -> {ev(~F, env, e1) == ev(~F, env, e2) : O.C(F)}:
  IP.ident_all(~F, e1, e2, h, env)

# cross(u, x) = cross(u, y) when x and y evaluate alike
def cross_cong(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, +y: SK.VE, ex: {ev(~F, env, SK.VE.x(x)) == ev(~F, env, SK.VE.x(y)) : O.C(F)}, ey: {ev(~F, env, SK.VE.y(x)) == ev(~F, env, SK.VE.y(y)) : O.C(F)}) -> {evc(~F, env, u, x) == evc(~F, env, u, y) : O.C(F)}:
  %ex : {evc(~F, env, u, x) == O.sub(~F, O.mul(F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(y))), O.mul(F, ev(~F, env, SK.VE.y(u)), _)) : O.C(F)}
  %ey : {evc(~F, env, u, x) == O.sub(~F, O.mul(F, ev(~F, env, SK.VE.x(u)), _), O.mul(F, ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x)))) : O.C(F)}
  {==}

def samev_cross(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, +y: SK.VE, h: DR.SameV(x, y)) -> {evc(~F, env, u, x) == evc(~F, env, u, y) : O.C(F)}:
  (hx, hy) = h
  cross_cong(~F, env, u, x, y, same_ev(~F, env, SK.VE.x(x), SK.VE.x(y), hx), same_ev(~F, env, SK.VE.y(x), SK.VE.y(y), hy))

# Nonzero lengths
# ---------------

def longs_cat.go(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, hs: DR.Long(~F, env, es, s), r: SK.Both(DR.Longs(~F, env, es, t), DR.Longs(~F, env, es, b))) -> SK.Both(DR.Longs(~F, env, es, Con{s, t}), DR.Longs(~F, env, es, b)):
  (rt, rb) = r
  ((hs, rt), rb)

def longs_cat(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, a: List<&2, Nat>, +b: List<&2, Nat>, h: DR.Longs(~F, env, es, DR.ncat(a, b))) -> SK.Both(DR.Longs(~F, env, es, a), DR.Longs(~F, env, es, b)):
  match a:
    case Nil{}:
      (Unit{}, h)
    case Con{+s, +t}:
      (hs, ht) = h
      longs_cat.go(~F, env, es, s, t, b, hs, longs_cat(~F, env, es, t, b, ht))

# distinct points give a direction of positive squared length
# a segment of nonzero length: |z_s|^2 is not 0
def long_nz(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat, h: DR.Long(~F, env, es, s)) -> {MN.n2(~F, ev(~F, env, SK.VE.x(DR.zseg(es, s))), ev(~F, env, SK.VE.y(DR.zseg(es, s)))) == O.zero(F) : O.C(F)} -> Empty:
  FO.ne_of_gt(~F, MN.n2(~F, ev(~F, env, SK.VE.x(DR.zseg(es, s))), ev(~F, env, SK.VE.y(DR.zseg(es, s)))), O.zero(F), h)

# Reading judgments
# -----------------

def kval(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, j: DR.Jd, k: DR.IsK(j), h: Holds(~F, env, es, j)) -> {ev(~F, env, DR.Jd.e(j)) == O.zero(F) : O.C(F)}:
  match j:
    case DR.JK{e}:
      h
    case DR.JP{a, x}:
      FO.absurd({ev(~F, env, DR.zeroe()) == O.zero(F) : O.C(F)}, k)

def pval(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, j: DR.Jd, k: DR.IsP(j), h: Holds(~F, env, es, j)) -> {evc(~F, env, DR.zdir(es, DR.Jd.a(j)), DR.Jd.x(j)) == O.zero(F) : O.C(F)}:
  match j:
    case DR.JK{e}:
      FO.absurd({evc(~F, env, DR.zdir(es, DR.NFrame{}), DR.zerov()) == O.zero(F) : O.C(F)}, k)
    case DR.JP{a, x}:
      h

# The rules, one lemma each
# -------------------------
# u and x stand for complex forms; U1, U2 and X1, X2 for their parts'
# values. Labels enter through O.ofq.

# sub(a, b) = 0 from a = b
def sub0(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {a == b : O.C(F)}) -> {O.sub(~F, a, b) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), a, b, h) : {O.sub(~F, _, b) == O.zero(F) : O.C(F)}
  FR.fring_eq(~F, [b], E.ZSub{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Z0{}}, {==})

def ofq_one0(~F: O.OField) -> {O.sub(~F, O.ofq(~F, DR.qo()), O.one(F)) == O.zero(F) : O.C(F)}:
  sub0(~F, O.ofq(~F, DR.qo()), O.one(F), QE.ofq_one(~F))

# conj's sine plus the sine: ofq(-s) + ofq(s) = 0
def negs0(~F: O.OField, +s: S.Q) -> {O.add(F, O.ofq(~F, S.Q.neg(s)), O.ofq(~F, s)) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(s)), O.neg(F, O.ofq(~F, s)), QE.ofq_neg(~F, s)) : {O.add(F, _, O.ofq(~F, s)) == O.zero(F) : O.C(F)}
  FR.fring_eq(~F, [O.ofq(~F, s)], E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}, {==})

# K-lin
def r_klin(~F: O.OField, +env: List<&2, O.C(F)>, +l1: S.Q, +e1: E.QExpr, +l2: S.Q, +e2: E.QExpr, h1: {ev(~F, env, e1) == O.zero(F) : O.C(F)}, h2: {ev(~F, env, e2) == O.zero(F) : O.C(F)}) -> {ev(~F, env, E.QAdd{E.QMul{DR.cst(l1), e1}, E.QMul{DR.cst(l2), e2}}) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, ev(~F, env, E.QAdd{E.QMul{DR.cst(l1), e1}, E.QMul{DR.cst(l2), e2}}), O.ofq(~F, l1), ev(~F, env, e1), O.ofq(~F, l2), ev(~F, env, e2), {==}, h1, h2)

# frame-back: cross((1, 0), x) = 0 gives Im x = 0
def r_back(~F: O.OField, +env: List<&2, O.C(F)>, +x: SK.VE, h: {evc(~F, env, DR.zdir(Nil{}, DR.NFrame{}), x) == O.zero(F) : O.C(F)}) -> {ev(~F, env, SK.VE.y(x)) == O.zero(F) : O.C(F)}:
  FO.cert3(~F, ev(~F, env, SK.VE.y(x)), O.one(F), evc(~F, env, DR.zdir(Nil{}, DR.NFrame{}), x), O.neg(F, ev(~F, env, SK.VE.y(x))), O.sub(~F, O.ofq(~F, DR.qo()), O.one(F)), ev(~F, env, SK.VE.x(x)), O.ofq(~F, DR.qz()),
    FR.fring_eq(~F, [O.ofq(~F, DR.qo()), O.ofq(~F, DR.qz()), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x))], E.ZVar{3n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZNeg{E.ZVar{3n}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, {==}), h, ofq_one0(~F), QE.ofq_zero(~F))

# frame: Im x = 0 gives cross((1, 0), x) = 0
def r_frame(~F: O.OField, +env: List<&2, O.C(F)>, +x: SK.VE, h: {ev(~F, env, SK.VE.y(x)) == O.zero(F) : O.C(F)}) -> {evc(~F, env, DR.zdir(Nil{}, DR.NFrame{}), x) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, evc(~F, env, DR.zdir(Nil{}, DR.NFrame{}), x), O.ofq(~F, DR.qo()), ev(~F, env, SK.VE.y(x)), O.neg(F, ev(~F, env, SK.VE.x(x))), O.ofq(~F, DR.qz()),
    FR.fring_eq(~F, [O.ofq(~F, DR.qo()), O.ofq(~F, DR.qz()), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{1n}}}, {==}), h, QE.ofq_zero(~F))

# self: cross(u, u) = 0
def r_self(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE) -> {evc(~F, env, u, u) == O.zero(F) : O.C(F)}:
  FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})

# par-lin: cross(u, m1 x1 + m2 x2) = m1 cross(u, x1) + m2 cross(u, x2)
def r_plin(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, h1: {evc(~F, env, u, x1) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, u, x2) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, DR.vlin(m1, x1, m2, x2)) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, evc(~F, env, u, DR.vlin(m1, x1, m2, x2)), O.ofq(~F, m1), evc(~F, env, u, x1), O.ofq(~F, m2), evc(~F, env, u, x2),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x1)), ev(~F, env, SK.VE.y(x1)), ev(~F, env, SK.VE.x(x2)), ev(~F, env, SK.VE.y(x2)), O.ofq(~F, m1), O.ofq(~F, m2)], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{3n}}, E.ZMul{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{7n}, E.ZVar{4n}}}}}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{7n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{4n}}}}}, {==}), h1, h2)

# known: cross(u, x + l) = cross(u, x) + u1 l2 - u2 l1
def r_known(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, +er: E.QExpr, +ei: E.QExpr, h: {evc(~F, env, u, x) == O.zero(F) : O.C(F)}, hr: {ev(~F, env, er) == O.zero(F) : O.C(F)}, hi: {ev(~F, env, ei) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, SK.VE.add(x, SK.VE{er, ei})) == O.zero(F) : O.C(F)}:
  FO.cert3(~F, evc(~F, env, u, SK.VE.add(x, SK.VE{er, ei})), O.one(F), evc(~F, env, u, x), ev(~F, env, SK.VE.x(u)), ev(~F, env, ei), O.neg(F, ev(~F, env, SK.VE.y(u))), ev(~F, env, er),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x)), ev(~F, env, er), ev(~F, env, ei)], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{3n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZVar{2n}, E.ZVar{4n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{4n}}}, {==}), h, hi, hr)

# void: u = 0 gives cross(u, x) = 0
def r_void(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, hr: {ev(~F, env, SK.VE.x(u)) == O.zero(F) : O.C(F)}, hi: {ev(~F, env, SK.VE.y(u)) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, x) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, evc(~F, env, u, x), ev(~F, env, SK.VE.y(x)), ev(~F, env, SK.VE.x(u)), O.neg(F, ev(~F, env, SK.VE.x(x))), ev(~F, env, SK.VE.y(u)),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZVar{0n}}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{1n}}}, {==}), hr, hi)

# complex line: cross(u, x) = 0 and cross(u, i x) = 0, |u|^2 not 0, give
# x = 0: |u|^2 x1 = u1 cross(u, i x) - u2 cross(u, x), and likewise x2
def r_line_re(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, nz: {MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))) == O.zero(F) : O.C(F)} -> Empty, h1: {evc(~F, env, u, x) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, u, DR.imul(x)) == O.zero(F) : O.C(F)}) -> {ev(~F, env, SK.VE.x(x)) == O.zero(F) : O.C(F)}:
  FO.cert3(~F, ev(~F, env, SK.VE.x(x)), O.neg(F, ev(~F, env, SK.VE.x(x))), O.sub(~F, O.mul(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))))), O.one(F)),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.x(u))), evc(~F, env, u, DR.imul(x)),
    O.neg(F, O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.y(u)))), evc(~F, env, u, x),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x)), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))))], E.ZVar{2n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZNeg{E.ZVar{3n}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}),
    FO.inv_rel(~F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))), nz), h2, h1)

def r_line_im(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, nz: {MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))) == O.zero(F) : O.C(F)} -> Empty, h1: {evc(~F, env, u, x) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, u, DR.imul(x)) == O.zero(F) : O.C(F)}) -> {ev(~F, env, SK.VE.y(x)) == O.zero(F) : O.C(F)}:
  FO.cert3(~F, ev(~F, env, SK.VE.y(x)), O.neg(F, ev(~F, env, SK.VE.y(x))), O.sub(~F, O.mul(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))))), O.one(F)),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.y(u))), evc(~F, env, u, DR.imul(x)),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.x(u))), evc(~F, env, u, x),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x)), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))))], E.ZVar{3n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZNeg{E.ZVar{3n}}}}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}),
    FO.inv_rel(~F, MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))), nz), h2, h1)

# turn: cross(u, conj(g) b) = 0 gives cross(b, g u) = 0, since
# cross(b, g u) = -cross(u, conj(g) b) + (t + s) dot(u, b) with t = -s
def r_turn.go(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +b: SK.VE, +c: S.Q, +s: S.Q, h: {evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, b)) == O.zero(F) : O.C(F)}) -> {evc(~F, env, b, DR.gmul(DR.Lab{c, s}, u)) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, evc(~F, env, b, DR.gmul(DR.Lab{c, s}, u)), O.neg(F, O.one(F)), evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, b)), O.add(F, O.mul(F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.x(b))), O.mul(F, ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.y(b)))), O.add(F, O.ofq(~F, S.Q.neg(s)), O.ofq(~F, s)),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b)), O.ofq(~F, c), O.ofq(~F, s), O.ofq(~F, S.Q.neg(s))], E.ZSub{E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{0n}}, E.ZMul{E.ZVar{5n}, E.ZVar{1n}}}}}, E.ZAdd{E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZVar{6n}, E.ZVar{3n}}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{6n}, E.ZVar{5n}}}}, {==}), h, negs0(~F, s))

def r_turn(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +b: SK.VE, g: DR.Lab, h: {evc(~F, env, u, DR.gmul(DR.Lab.conj(g), b)) == O.zero(F) : O.C(F)}) -> {evc(~F, env, b, DR.gmul(g, u)) == O.zero(F) : O.C(F)}:
  match g:
    case DR.Lab{+c, +s}:
      r_turn.go(~F, env, u, b, c, s, h)

# through: cross(u, conj(g) b) = 0 and cross(b, x) = 0, |b|^2 not 0, give
# cross(u, conj(g) x) = 0. With y = cross(u, conj(g) x) and n = |b|^2:
# n y = dot(g u, b) cross(b, x) + dot(b, x) cross(u, conj(g) b)
#       - (t + s) cross(u, b) cross(b, x), t = -s (the path lemma)
def r_through.go(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +b: SK.VE, +x: SK.VE, +c: S.Q, +s: S.Q, nz: {MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))) == O.zero(F) : O.C(F)} -> Empty, h1: {evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, b)) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, b, x) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, x)) == O.zero(F) : O.C(F)}:
  FO.cert4(~F, evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, x)),
    O.neg(F, evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, x))), O.sub(~F, O.mul(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))))), O.one(F)),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b)))), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, c), ev(~F, env, SK.VE.x(u))), O.mul(F, O.ofq(~F, s), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.x(b))), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, s), ev(~F, env, SK.VE.x(u))), O.mul(F, O.ofq(~F, c), ev(~F, env, SK.VE.y(u)))), ev(~F, env, SK.VE.y(b))))), evc(~F, env, b, x),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b)))), O.add(F, O.mul(F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.x(x))), O.mul(F, ev(~F, env, SK.VE.y(b)), ev(~F, env, SK.VE.y(x))))), evc(~F, env, u, DR.gmul(DR.Lab{c, S.Q.neg(s)}, b)),
    O.mul(F, O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b)))), O.neg(F, O.mul(F, O.sub(~F, O.mul(F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(b))), O.mul(F, ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(b)))), evc(~F, env, b, x)))), O.add(F, O.ofq(~F, S.Q.neg(s)), O.ofq(~F, s)),
    FR.fring_eq(~F, [ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u)), ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b)), ev(~F, env, SK.VE.x(x)), ev(~F, env, SK.VE.y(x)), O.ofq(~F, c), O.ofq(~F, s), O.ofq(~F, S.Q.neg(s)), O.inv(F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{8n}, E.ZVar{4n}}, E.ZMul{E.ZVar{6n}, E.ZVar{5n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{4n}}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{8n}, E.ZVar{4n}}, E.ZMul{E.ZVar{6n}, E.ZVar{5n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{4n}}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{3n}}}, E.ZVar{9n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{9n}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{0n}}, E.ZMul{E.ZVar{7n}, E.ZVar{1n}}}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{7n}, E.ZVar{0n}}, E.ZMul{E.ZVar{6n}, E.ZVar{1n}}}, E.ZVar{3n}}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}}}, E.ZMul{E.ZMul{E.ZVar{9n}, E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{8n}, E.ZVar{2n}}, E.ZMul{E.ZVar{6n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{8n}, E.ZVar{3n}}}}}}}, E.ZMul{E.ZMul{E.ZVar{9n}, E.ZNeg{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}}}}, E.ZAdd{E.ZVar{8n}, E.ZVar{7n}}}}, {==}),
    FO.inv_rel(~F, MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))), nz), h2, h1, negs0(~F, s))

def r_through(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +b: SK.VE, +x: SK.VE, g: DR.Lab, nz: {MN.n2(~F, ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))) == O.zero(F) : O.C(F)} -> Empty, h1: {evc(~F, env, u, DR.gmul(DR.Lab.conj(g), b)) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, b, x) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, DR.gmul(DR.Lab.conj(g), x)) == O.zero(F) : O.C(F)}:
  match g:
    case DR.Lab{+c, +s}:
      r_through.go(~F, env, u, b, x, c, s, nz, h1, h2)

# Transports and readers for the cases
# ------------------------------------

# projections of a pair (a computed pair cannot be destructured in place)
def fst(-A: Data, -B: Data, p: SK.Both(A, B)) -> A:
  (a, b) = p
  a

def snd(-A: Data, -B: Data, p: SK.Both(A, B)) -> B:
  (a, b) = p
  b


# a parallel judgment moved along a node equality
def node_tr(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: DR.Node, +b: DR.Node, +x: SK.VE, e: {a == b : DR.Node}, h: {evc(~F, env, DR.zdir(es, a), x) == O.zero(F) : O.C(F)}) -> {evc(~F, env, DR.zdir(es, b), x) == O.zero(F) : O.C(F)}:
  %e : {evc(~F, env, DR.zdir(es, _), x) == O.zero(F) : O.C(F)}
  h

# a parallel judgment moved along x's sameness to y
def same_tr(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, +y: SK.VE, s: DR.SameV(x, y), h: {evc(~F, env, u, x) == O.zero(F) : O.C(F)}) -> {evc(~F, env, u, y) == O.zero(F) : O.C(F)}:
  Equal.trans(O.C(F), evc(~F, env, u, y), evc(~F, env, u, x), O.zero(F), Equal.sym(O.C(F), evc(~F, env, u, x), evc(~F, env, u, y), samev_cross(~F, env, u, x, y, s)), h)

# a K judgment moved along sameness
def k_tr(~F: O.OField, +env: List<&2, O.C(F)>, +e: E.QExpr, +f: E.QExpr, s: DR.Same(e, f), h: {ev(~F, env, e) == O.zero(F) : O.C(F)}) -> {ev(~F, env, f) == O.zero(F) : O.C(F)}:
  Equal.trans(O.C(F), ev(~F, env, f), ev(~F, env, e), O.zero(F), Equal.sym(O.C(F), ev(~F, env, e), ev(~F, env, f), same_ev(~F, env, e, f, s)), h)

# the frame's squared length, 1, is not 0
def frame_nz(~F: O.OField, h: {MN.n2(~F, O.ofq(~F, DR.qo()), O.ofq(~F, DR.qz())) == O.zero(F) : O.C(F)}) -> Empty:
  FO.ne_of_gt(~F, O.one(F), O.zero(F), O.zero_lt_one(F),
    FO.cert3(~F, O.one(F), O.one(F), MN.n2(~F, O.ofq(~F, DR.qo()), O.ofq(~F, DR.qz())), O.neg(F, O.add(F, O.ofq(~F, DR.qo()), O.one(F))), O.sub(~F, O.ofq(~F, DR.qo()), O.one(F)), O.neg(F, O.ofq(~F, DR.qz())), O.ofq(~F, DR.qz()),
      FR.fring_eq(~F, [O.ofq(~F, DR.qo()), O.ofq(~F, DR.qz())], E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{1n}}}, {==}), h, ofq_one0(~F), QE.ofq_zero(~F)))

# a node a complex line is applied at has a nonzero squared length: the
# frame always, a segment when nd says so
def node_nz(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, a: DR.Node, h: DR.Longs(~F, env, es, DR.Node.segs(a))) -> {MN.n2(~F, ev(~F, env, SK.VE.x(DR.zdir(es, a))), ev(~F, env, SK.VE.y(DR.zdir(es, a)))) == O.zero(F) : O.C(F)} -> Empty:
  match a:
    case DR.NFrame{}:
      frame_nz(~F)
    case DR.NSeg{+s}:
      (hs, hn) = h
      long_nz(~F, env, es, s, hs)

def s_lt0(~F: O.OField, +v: O.C(F), h: O.lt(F, O.zero(F), v), z: {v == O.zero(F) : O.C(F)}) -> O.lt(F, O.zero(F), O.zero(F)):
  %z : O.lt(F, O.zero(F), _)
  h

# a positive squared length is not 0
def long_short(~F: O.OField, +v: O.C(F), h: O.lt(F, O.zero(F), v), z: {v == O.zero(F) : O.C(F)}) -> Empty:
  O.lt_irrefl(F)(O.zero(F))(s_lt0(~F, v, h, z))

def bool_ne.pick(b: Bool) -> Data:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def bool_ne(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_ne.pick(_)
  Unit{}

# nd's segments all long, and one short: impossible (ih: the same for t)
def short_long.go(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat, +t: List<&2, Nat>, sh: DOr({ev(~F, env, SK.VE.norm2(DR.zseg(es, s))) == O.zero(F) : O.C(F)}, Short(~F, env, es, t)), hs: DR.Long(~F, env, es, s), ih: Short(~F, env, es, t) -> Empty) -> Empty:
  match sh:
    case Inl{z}:
      long_short(~F, ev(~F, env, SK.VE.norm2(DR.zseg(es, s))), hs, z)
    case Inr{st}:
      ih(st)

def short_long(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>, sh: Short(~F, env, es, nd), hl: DR.Longs(~F, env, es, nd)) -> Empty:
  match nd:
    case Nil{}:
      bool_ne(sh)
    case Con{+s, +t}:
      (hs, ht) = hl
      short_long.go(~F, env, es, s, t, sh, hs, st => short_long(~F, env, es, t, st, ht))

# a fact read where its nd is long: its equation and its statement
def fact_ok(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>, h: FactHolds(~F, env, es, DR.Fact{e, nd, ds}), +hl: DR.Longs(~F, env, es, nd)) -> SK.Both({ev(~F, env, e) == O.zero(F) : O.C(F)}, StatHolds(~F, env, es, ds)):
  match h:
    case Inl{sh}:
      FO.absurd(SK.Both({ev(~F, env, e) == O.zero(F) : O.C(F)}, StatHolds(~F, env, es, ds)), short_long(~F, env, es, nd, sh, hl))
    case Inr{b}:
      b

def s_prem(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, DR.Fact>, h: MHolds(~F, env, es, m), hl: DR.Longs(~F, env, es, DR.fact.nd(m))) -> {ev(~F, env, DR.fact.e(m)) == O.zero(F) : O.C(F)}:
  match m:
    case Some{DR.Fact{+e, +nd, +ds}}:
      fst({ev(~F, env, e) == O.zero(F) : O.C(F)}, StatHolds(~F, env, es, ds), fact_ok(~F, env, es, e, nd, ds, h, hl))
    case None{}:
      QE.ofq_zero(~F)

def s_stat(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +e: E.QExpr, +nd: List<&2, Nat>, ds: Maybe<&2, DR.DStat>, h: StatHolds(~F, env, es, ds)) -> Holds(~F, env, es, DR.fact.pj(Some{DR.Fact{e, nd, ds}})):
  match ds:
    case Some{DR.DStat{a, x, l}}:
      h
    case None{}:
      QE.ofq_zero(~F)

def s_pprem(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, DR.Fact>, h: MHolds(~F, env, es, m), hl: DR.Longs(~F, env, es, DR.fact.nd(m))) -> Holds(~F, env, es, DR.fact.pj(m)):
  match m:
    case Some{DR.Fact{+e, +nd, +ds}}:
      s_stat(~F, env, es, e, nd, ds, snd({ev(~F, env, e) == O.zero(F) : O.C(F)}, StatHolds(~F, env, es, ds), fact_ok(~F, env, es, e, nd, ds, h, hl)))
    case None{}:
      QE.ofq_zero(~F)

def s_line(~F: O.OField, +env: List<&2, O.C(F)>, +u: SK.VE, +x: SK.VE, re: Bool, nz: {MN.n2(~F, ev(~F, env, SK.VE.x(u)), ev(~F, env, SK.VE.y(u))) == O.zero(F) : O.C(F)} -> Empty, h1: {evc(~F, env, u, x) == O.zero(F) : O.C(F)}, h2: {evc(~F, env, u, DR.imul(x)) == O.zero(F) : O.C(F)}) -> {ev(~F, env, DR.dline.e(re, x)) == O.zero(F) : O.C(F)}:
  match re:
    case True{}:
      r_line_re(~F, env, u, x, nz, h1, h2)
    case False{}:
      r_line_im(~F, env, u, x, nz, h1, h2)

# Soundness
# ---------
# Where the facts hold and the derivation's nd segments have nonzero
# length, its conclusion holds.

def lsplit1(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: List<&2, Nat>, +b: List<&2, Nat>, h: DR.Longs(~F, env, es, DR.ncat(a, b))) -> DR.Longs(~F, env, es, a):
  fst(DR.Longs(~F, env, es, a), DR.Longs(~F, env, es, b), longs_cat(~F, env, es, a, b, h))

def lsplit2(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: List<&2, Nat>, +b: List<&2, Nat>, h: DR.Longs(~F, env, es, DR.ncat(a, b))) -> DR.Longs(~F, env, es, b):
  snd(DR.Longs(~F, env, es, a), DR.Longs(~F, env, es, b), longs_cat(~F, env, es, a, b, h))

def sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +hf: AllFacts(~F, env, es, fs), d: DR.Der, hv: DR.Valid(es, fs, ctx, d), +hl: DR.Longs(~F, env, es, DR.nd(es, fs, d))) -> Holds(~F, env, es, DR.concl(es, fs, d)):
  match d:
    case DR.DPrem{+i}:
      s_prem(~F, env, es, DR.fact_at(fs, i), fact_at_ok(~F, env, es, fs, i, hf), hl)
    case DR.DKLin{+l1, +d1, +l2, +d2}:
      (v1, r) = hv
      (v2, ks) = r
      (k1, k2) = ks
      r_klin(~F, env, l1, DR.Jd.e(DR.concl(es, fs, d1)), l2, DR.Jd.e(DR.concl(es, fs, d2)),
        kval(~F, env, es, DR.concl(es, fs, d1), k1, sound(~F, env, es, fs, ctx, hf, d1, v1, lsplit1(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), hl))),
        kval(~F, env, es, DR.concl(es, fs, d2), k2, sound(~F, env, es, fs, ctx, hf, d2, v2, lsplit2(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), hl))))
    case DR.DBack{+d}:
      (v, r) = hv
      (p, e) = r
      r_back(~F, env, DR.Jd.x(DR.concl(es, fs, d)),
        node_tr(~F, env, es, DR.Jd.a(DR.concl(es, fs, d)), DR.NFrame{}, DR.Jd.x(DR.concl(es, fs, d)), e,
          pval(~F, env, es, DR.concl(es, fs, d), p, sound(~F, env, es, fs, ctx, hf, d, v, hl))))
    case DR.DLine{+d1, +d2, +re}:
      (v1, r) = hv
      (v2, r2) = r
      (p1, r3) = r2
      (p2, r4) = r3
      (e, r5) = r4
      (o, sm) = r5
      s_line(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), DR.Jd.x(DR.concl(es, fs, d1)), re,
        node_nz(~F, env, es, DR.Jd.a(DR.concl(es, fs, d1)), lsplit1(~F, env, es, DR.Node.segs(DR.Jd.a(DR.concl(es, fs, d1))), DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2)), hl)),
        pval(~F, env, es, DR.concl(es, fs, d1), p1, sound(~F, env, es, fs, ctx, hf, d1, v1, lsplit1(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), lsplit2(~F, env, es, DR.Node.segs(DR.Jd.a(DR.concl(es, fs, d1))), DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2)), hl)))),
        same_tr(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), DR.Jd.x(DR.concl(es, fs, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs, d1))), sm,
          node_tr(~F, env, es, DR.Jd.a(DR.concl(es, fs, d2)), DR.Jd.a(DR.concl(es, fs, d1)), DR.Jd.x(DR.concl(es, fs, d2)), Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, d1)), DR.Jd.a(DR.concl(es, fs, d2)), e),
            pval(~F, env, es, DR.concl(es, fs, d2), p2, sound(~F, env, es, fs, ctx, hf, d2, v2, lsplit2(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), lsplit2(~F, env, es, DR.Node.segs(DR.Jd.a(DR.concl(es, fs, d1))), DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2)), hl)))))))
    case DR.DPPrem{+i}:
      s_pprem(~F, env, es, DR.fact_at(fs, i), fact_at_ok(~F, env, es, fs, i, hf), hl)
    case DR.DSelf{+a}:
      r_self(~F, env, DR.zdir(es, a))
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r) = hv
      (v2, r2) = r
      (p1, r3) = r2
      (p2, e) = r3
      r_plin(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), m1, DR.Jd.x(DR.concl(es, fs, d1)), m2, DR.Jd.x(DR.concl(es, fs, d2)),
        pval(~F, env, es, DR.concl(es, fs, d1), p1, sound(~F, env, es, fs, ctx, hf, d1, v1, lsplit1(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), hl))),
        node_tr(~F, env, es, DR.Jd.a(DR.concl(es, fs, d2)), DR.Jd.a(DR.concl(es, fs, d1)), DR.Jd.x(DR.concl(es, fs, d2)), Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, d1)), DR.Jd.a(DR.concl(es, fs, d2)), e),
          pval(~F, env, es, DR.concl(es, fs, d2), p2, sound(~F, env, es, fs, ctx, hf, d2, v2, lsplit2(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), hl)))))
    case DR.DKnown{+d, +dr, +di}:
      (v, r) = hv
      (vr, r2) = r
      (vi, r3) = r2
      (p, r4) = r3
      (kr, ki) = r4
      r_known(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d))), DR.Jd.x(DR.concl(es, fs, d)), DR.Jd.e(DR.concl(es, fs, dr)), DR.Jd.e(DR.concl(es, fs, di)),
        pval(~F, env, es, DR.concl(es, fs, d), p, sound(~F, env, es, fs, ctx, hf, d, v, lsplit1(~F, env, es, DR.nd(es, fs, d), DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di)), hl))),
        kval(~F, env, es, DR.concl(es, fs, dr), kr, sound(~F, env, es, fs, ctx, hf, dr, vr, lsplit1(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), lsplit2(~F, env, es, DR.nd(es, fs, d), DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di)), hl)))),
        kval(~F, env, es, DR.concl(es, fs, di), ki, sound(~F, env, es, fs, ctx, hf, di, vi, lsplit2(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), lsplit2(~F, env, es, DR.nd(es, fs, d), DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di)), hl)))))
    case DR.DTurn{+d, +g, +b}:
      (v, r) = hv
      (p, sm) = r
      r_turn(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d))), DR.zseg(es, b), g,
        same_tr(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d))), DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(DR.Lab.conj(g), DR.zseg(es, b)), sm,
          pval(~F, env, es, DR.concl(es, fs, d), p, sound(~F, env, es, fs, ctx, hf, d, v, hl))))
    case DR.DThrough{+d1, +d2, +g, +b}:
      (v1, r) = hv
      (v2, r2) = r
      (p1, r3) = r2
      (p2, r4) = r3
      (sm, r5) = r4
      (e, o) = r5
      r_through(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), DR.zseg(es, b), DR.Jd.x(DR.concl(es, fs, d2)), g, long_nz(~F, env, es, b, fst(DR.Long(~F, env, es, b), DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2))), hl)),
        same_tr(~F, env, DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), DR.Jd.x(DR.concl(es, fs, d1)), DR.gmul(DR.Lab.conj(g), DR.zseg(es, b)), sm,
          pval(~F, env, es, DR.concl(es, fs, d1), p1, sound(~F, env, es, fs, ctx, hf, d1, v1, lsplit1(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), snd(DR.Long(~F, env, es, b), DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2))), hl))))),
        node_tr(~F, env, es, DR.Jd.a(DR.concl(es, fs, d2)), DR.NSeg{b}, DR.Jd.x(DR.concl(es, fs, d2)), e,
          pval(~F, env, es, DR.concl(es, fs, d2), p2, sound(~F, env, es, fs, ctx, hf, d2, v2, lsplit2(~F, env, es, DR.nd(es, fs, d1), DR.nd(es, fs, d2), snd(DR.Long(~F, env, es, b), DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, d1), DR.nd(es, fs, d2))), hl))))))
    case DR.DFrame{+d, +x}:
      (v, r) = hv
      (k, sm) = r
      r_frame(~F, env, x, k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, d)), SK.VE.y(x), sm, kval(~F, env, es, DR.concl(es, fs, d), k, sound(~F, env, es, fs, ctx, hf, d, v, hl))))
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r) = hv
      (vi, r2) = r
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      r_void(~F, env, DR.zdir(es, a), x,
        k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zdir(es, a)), sr, kval(~F, env, es, DR.concl(es, fs, dr), kr, sound(~F, env, es, fs, ctx, hf, dr, vr, lsplit1(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), hl)))),
        k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zdir(es, a)), si, kval(~F, env, es, DR.concl(es, fs, di), ki, sound(~F, env, es, fs, ctx, hf, di, vi, lsplit2(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), hl)))))

# Direction statements are right
# ------------------------------
# Where a constraint's equation vanishes, so does the cross product its
# direction statement (spec/dir.bend: dstat) names.

def stat_perp(~F: O.OField, +env: List<&2, O.C(F)>, +a: SK.VE, +b: SK.VE, h: {ev(~F, env, SK.VE.dot(a, b)) == O.zero(F) : O.C(F)}) -> {evc(~F, env, a, DR.imul(b)) == O.zero(F) : O.C(F)}:
  FO.cert1(~F, evc(~F, env, a, DR.imul(b)), O.one(F), ev(~F, env, SK.VE.dot(a, b)), FR.fring_eq(~F, [ev(~F, env, SK.VE.x(a)), ev(~F, env, SK.VE.y(a)), ev(~F, env, SK.VE.x(b)), ev(~F, env, SK.VE.y(b))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZNeg{E.ZVar{3n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, {==}), h)

# an Angle's equation cross(rot(c, s) a', w) = 0, with a' = sign a, gives
# cross(a, conj(c + is) w) = 0: the two differ by sign and (t + s) dot(a, w)
def stat_angle.go(~F: O.OField, +env: List<&2, O.C(F)>, +a1: O.C(F), +a2: O.C(F), +w1: O.C(F), +w2: O.C(F), +qc: S.Q, +qs: S.Q, +sg: O.C(F), hs: {O.mul(F, sg, sg) == O.one(F) : O.C(F)}, h: {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)) == O.zero(F) : O.C(F)}) -> {O.sub(~F, O.mul(F, a1, O.add(F, O.mul(F, O.ofq(~F, S.Q.neg(qs)), w1), O.mul(F, O.ofq(~F, qc), w2))), O.mul(F, a2, O.sub(~F, O.mul(F, O.ofq(~F, qc), w1), O.mul(F, O.ofq(~F, S.Q.neg(qs)), w2)))) == O.zero(F) : O.C(F)}:
  FO.cert3(~F, O.sub(~F, O.mul(F, a1, O.add(F, O.mul(F, O.ofq(~F, S.Q.neg(qs)), w1), O.mul(F, O.ofq(~F, qc), w2))), O.mul(F, a2, O.sub(~F, O.mul(F, O.ofq(~F, qc), w1), O.mul(F, O.ofq(~F, S.Q.neg(qs)), w2)))),
    sg, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)),
    O.mul(F, O.mul(F, sg, sg), O.add(F, O.mul(F, a1, w1), O.mul(F, a2, w2))), O.add(F, O.ofq(~F, S.Q.neg(qs)), O.ofq(~F, qs)),
    O.neg(F, O.sub(~F, O.mul(F, a1, O.add(F, O.mul(F, O.ofq(~F, S.Q.neg(qs)), w1), O.mul(F, O.ofq(~F, qc), w2))), O.mul(F, a2, O.sub(~F, O.mul(F, O.ofq(~F, qc), w1), O.mul(F, O.ofq(~F, S.Q.neg(qs)), w2))))), O.sub(~F, O.mul(F, sg, sg), O.one(F)),
    FR.fring_eq(~F, [a1, a2, w1, w2, O.ofq(~F, qc), O.ofq(~F, qs), O.ofq(~F, S.Q.neg(qs)), sg], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZVar{6n}, E.ZVar{3n}}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{7n}, E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{7n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{7n}, E.ZVar{1n}}}}, E.ZVar{3n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{7n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{7n}, E.ZVar{1n}}}}, E.ZVar{2n}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{7n}, E.ZVar{7n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZAdd{E.ZVar{6n}, E.ZVar{5n}}}}, E.ZMul{E.ZNeg{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZVar{6n}, E.ZVar{3n}}}}}}, E.ZSub{E.ZMul{E.ZVar{7n}, E.ZVar{7n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}),
    h, negs0(~F, qs), sub0(~F, O.mul(F, sg, sg), O.one(F), hs))

# 1, or -1 for a reversed segment
def rsign(~F: O.OField, rev: Bool) -> O.C(F):
  match rev:
    case False{}:
      O.one(F)
    case True{}:
      O.neg(F, O.one(F))

def rsign_sq(~F: O.OField, rev: Bool) -> {O.mul(F, rsign(~F, rev), rsign(~F, rev)) == O.one(F) : O.C(F)}:
  match rev:
    case False{}:
      FR.fring_eq(~F, [], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}, {==})
    case True{}:
      FR.fring_eq(~F, [], E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}, {==})

# the same with the Angle's own direction d = sg a (sg = 1, or -1 when it
# takes the segment reversed)
def stat_angle.tr(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +d1: O.C(F), +d2: O.C(F), +w1: O.C(F), +w2: O.C(F), +qc: S.Q, +qs: S.Q, +sg: O.C(F), hd1: {d1 == O.mul(F, sg, a1) : O.C(F)}, hd2: {d2 == O.mul(F, sg, a2) : O.C(F)}, h: {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), d1), O.mul(F, O.ofq(~F, qs), d2)), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), d1), O.mul(F, O.ofq(~F, qc), d2)), w1)) == O.zero(F) : O.C(F)}) -> {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)) == O.zero(F) : O.C(F)}:
  %hd1 : {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), _), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), _), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)) == O.zero(F) : O.C(F)}
  %hd2 : {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), d1), O.mul(F, O.ofq(~F, qs), _)), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), d1), O.mul(F, O.ofq(~F, qc), _)), w1)) == O.zero(F) : O.C(F)}
  h

# a segment taken forwards or reversed: its direction is sg times its own
def rev_x(~F: O.OField, +env: List<&2, O.C(F)>, sg: SK.Seg, rev: Bool) -> {ev(~F, env, SK.VE.x(SK.Seg.dir(SK.Seg.rev_if(sg, rev)))) == O.mul(F, rsign(~F, rev), ev(~F, env, SK.VE.x(SK.Seg.dir(sg)))) : O.C(F)}:
  match sg rev:
    case SK.Seg{SK.Pt{px, py}, SK.Pt{qx, qy}} False{}:
      FR.fring_eq(~F, [O.lookup(~F, env, px), O.lookup(~F, env, qx)], E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, {==})
    case SK.Seg{SK.Pt{px, py}, SK.Pt{qx, qy}} True{}:
      FR.fring_eq(~F, [O.lookup(~F, env, px), O.lookup(~F, env, qx)], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, {==})

def rev_y(~F: O.OField, +env: List<&2, O.C(F)>, sg: SK.Seg, rev: Bool) -> {ev(~F, env, SK.VE.y(SK.Seg.dir(SK.Seg.rev_if(sg, rev)))) == O.mul(F, rsign(~F, rev), ev(~F, env, SK.VE.y(SK.Seg.dir(sg)))) : O.C(F)}:
  match sg rev:
    case SK.Seg{SK.Pt{px, py}, SK.Pt{qx, qy}} False{}:
      FR.fring_eq(~F, [O.lookup(~F, env, py), O.lookup(~F, env, qy)], E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, {==})
    case SK.Seg{SK.Pt{px, py}, SK.Pt{qx, qy}} True{}:
      FR.fring_eq(~F, [O.lookup(~F, env, py), O.lookup(~F, env, qy)], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, {==})

def stat_angle.s(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +qc: S.Q, s: E.QExpr, h: {ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}) -> StatHolds(~F, env, es, DR.dstat.angle(es, a, ra, b, rb, E.QCst{qc}, s)):
  match s:
    case E.QCst{+qs}:
      stat_angle.go(~F, env, ev(~F, env, SK.VE.x(DR.zseg(es, a))), ev(~F, env, SK.VE.y(DR.zseg(es, a))), ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))), ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))), qc, qs, rsign(~F, ra), rsign_sq(~F, ra),
        stat_angle.tr(~F, ev(~F, env, SK.VE.x(DR.zseg(es, a))), ev(~F, env, SK.VE.y(DR.zseg(es, a))), ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra)))), ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))), ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))), ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))), qc, qs, rsign(~F, ra),
          rev_x(~F, env, SK.seg(es, a), ra), rev_y(~F, env, SK.seg(es, a), ra), h))
    case E.QVar{i}:
      Unit{}
    case E.QAdd{x, y}:
      Unit{}
    case E.QSub{x, y}:
      Unit{}
    case E.QMul{x, y}:
      Unit{}
    case E.QNeg{x}:
      Unit{}

def stat_angle.cs(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, c: E.QExpr, +s: E.QExpr, h: {ev(~F, env, SK.VE.cross(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}) -> StatHolds(~F, env, es, DR.dstat.angle(es, a, ra, b, rb, c, s)):
  match c:
    case E.QCst{+qc}:
      stat_angle.s(~F, env, es, a, ra, b, rb, qc, s, h)
    case E.QVar{i}:
      Unit{}
    case E.QAdd{x, y}:
      Unit{}
    case E.QSub{x, y}:
      Unit{}
    case E.QMul{x, y}:
      Unit{}
    case E.QNeg{x}:
      Unit{}

# where a constraint's equations vanish, its direction statement holds
def dstat_ok(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, h: SK.Zeros(~F, env, SK.Constraint.eqs(es, k))) -> StatHolds(~F, env, es, DR.dstat(es, k)):
  match k:
    case SK.Parallel{a, b}:
      (he, ht) = h
      he
    case SK.Perpendicular{+a, +b}:
      (he, ht) = h
      stat_perp(~F, env, DR.zseg(es, a), DR.zseg(es, b), he)
    case SK.Angle{+a, +ra, +b, +rb, c, s}:
      (he, ht) = h
      stat_angle.cs(~F, env, es, a, ra, b, rb, c, s, he)
    case SK.OnLine{p, a}:
      (he, ht) = h
      he
    case SK.Coincident{a, b}:
      Unit{}
    case SK.Horizontal{a, b}:
      Unit{}
    case SK.Vertical{a, b}:
      Unit{}
    case SK.Concentric{a, b}:
      Unit{}
    case SK.EqualRadius{a, b}:
      Unit{}
    case SK.Fix{v, q}:
      Unit{}
    case SK.Distance{p, q, d}:
      Unit{}
    case SK.HDistance{p, q, d}:
      Unit{}
    case SK.VDistance{p, q, d}:
      Unit{}
    case SK.Radius{c, d}:
      Unit{}
    case SK.Diameter{c, d}:
      Unit{}
    case SK.LineDistance{p, a, rev, d, l}:
      Unit{}
    case SK.EqualLength{a, b}:
      Unit{}
    case SK.OnCircle{p, c}:
      Unit{}
    case SK.Midpoint{m, a}:
      Unit{}
    case SK.Symmetric{p, q, a}:
      Unit{}
