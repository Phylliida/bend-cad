# bend-cad: the closure's forms are combinations of base forms (PLAN-sk13b
# B3, termination). DC.bases lists every fact's equation and statement
# parts and every node's direction parts. VS(x, B) says both parts of the
# form x are constant combinations of B. Spans are closed under the
# shapes the closure builds: sums, constant multiples, rotations, i
# (vs_*). The facts' equations and statement forms are in DC.bases'
# span (fe_in, fs_in). A monomial outside the bases' normal forms
# (DC.kmons) has coefficient 0 in everything in their span (span_cz):
# that bounds K's pivots. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./natring.bend as NR
import ./karith.bend as KA
import ./qnorm.bend as QN
import ./identpf.bend as ID
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./coefpf.bend as CF
import ./spanpf.bend as SN
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./listpf.bend as LP2

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Spans
# -----

def in_tr.at(+p: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, +L: E.QExpr, +s: VD.SameD(e2, e1), +q: VD.SameD(e1, L)) -> S.Q.eq(E.qeval(p, e2), E.qeval(p, L)):
  LQ.q_trans(E.qeval(p, e2), E.qeval(p, e1), E.qeval(p, L), ID.ident_ok(e2, e1, s)(p), ID.ident_ok(e1, L, q)(p))

def in_tr.mk(+e1: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +ls: List<&2, S.Q>, +q: {QN.qzero(E.QSub{e1, SV.lin(ls, B)}) == True{} : Bool}, +s: VD.SameD(e2, e1)) -> SN.InSpan(e2, B):
  (ls, ID.qzero_ident(e2, SV.lin(ls, B), p => in_tr.at(p, e1, e2, SV.lin(ls, B), s, q)))

# the span holds whatever is the same as one of its members
def in_tr(+e1: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +h: SN.InSpan(e1, B), +s: VD.SameD(e2, e1)) -> SN.InSpan(e2, B):
  in_tr.mk(e1, e2, B, SN.in_ls(e1, B, h), SN.in_qz(e1, B, h), s)

def in_id(+e1: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +h: SN.InSpan(e1, B), i: SV.Ident(e2, e1)) -> SN.InSpan(e2, B):
  in_tr(e1, e2, B, h, ID.qzero_ident(e2, e1, i))

def in_hd.at(+p: List<&2, S.Q>, +b: E.QExpr, rest: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, b), E.qeval(p, SV.lin(Con{DR.qo(), Nil{}}, Con{b, rest}))):
  QR.qring_eq([E.qeval(p, b)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==})

# the first generator is in the span
def in_hd(+b: E.QExpr, +rest: List<&2, E.QExpr>) -> SN.InSpan(b, Con{b, rest}):
  (Con{DR.qo(), Nil{}}, ID.qzero_ident(b, SV.lin(Con{DR.qo(), Nil{}}, Con{b, rest}), p => in_hd.at(p, b, rest)))

def in_tl.at(+p: List<&2, S.Q>, +e: E.QExpr, +b: E.QExpr, +L: E.QExpr, +q: VD.SameD(e, L)) -> S.Q.eq(E.qeval(p, e), E.qeval(p, E.QAdd{E.QMul{E.QCst{DR.qz()}, b}, L})):
  LQ.q_trans(E.qeval(p, e), E.qeval(p, L), E.qeval(p, E.QAdd{E.QMul{E.QCst{DR.qz()}, b}, L}), ID.ident_ok(e, L, q)(p),
    QR.qring_eq([E.qeval(p, L), E.qeval(p, b)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QVar{0n}}, {==}))

def in_tl.mk(+e: E.QExpr, +b: E.QExpr, +rest: List<&2, E.QExpr>, +ls: List<&2, S.Q>, +q: {QN.qzero(E.QSub{e, SV.lin(ls, rest)}) == True{} : Bool}) -> SN.InSpan(e, Con{b, rest}):
  (Con{DR.qz(), ls}, ID.qzero_ident(e, SV.lin(Con{DR.qz(), ls}, Con{b, rest}), p => in_tl.at(p, e, b, SV.lin(ls, rest), q)))

# a span grows at the front
def in_tl(+e: E.QExpr, +b: E.QExpr, +rest: List<&2, E.QExpr>, +h: SN.InSpan(e, rest)) -> SN.InSpan(e, Con{b, rest}):
  in_tl.mk(e, b, rest, SN.in_ls(e, rest, h), SN.in_qz(e, rest, h))

def in_catr(A: List<&2, E.QExpr>, +C: List<&2, E.QExpr>, +e: E.QExpr, +h: SN.InSpan(e, C)) -> SN.InSpan(e, DC.qcat(A, C)):
  match A:
    case Nil{}:
      h
    case Con{+a, +t}:
      in_tl(e, a, DC.qcat(t, C), in_catr(t, C, e, h))

def in_scale(+l: S.Q, +e: E.QExpr, +B: List<&2, E.QExpr>, +h: SN.InSpan(e, B)) -> SN.InSpan(E.QMul{E.QCst{l}, e}, B):
  in_id(E.QAdd{E.QMul{E.QCst{l}, e}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QMul{E.QCst{l}, e}, B, SN.in_comb(l, e, E.QCst{S.Q{S.Z0{}, S.XH{}}}, B, h, SN.in_zero(B)),
    p => QR.qring_eq([l, E.qeval(p, e)], E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==}))

def add.id(+p: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr) -> S.Q.eq(E.qeval(p, E.QAdd{a, b}), E.qeval(p, E.QAdd{E.QMul{E.QCst{DR.qo()}, a}, b})):
  QR.qring_eq([E.qeval(p, a), E.qeval(p, b)], E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QVar{1n}}, {==})

def in_add(+a: E.QExpr, +b: E.QExpr, +B: List<&2, E.QExpr>, +ha: SN.InSpan(a, B), +hb: SN.InSpan(b, B)) -> SN.InSpan(E.QAdd{a, b}, B):
  in_id(E.QAdd{E.QMul{E.QCst{DR.qo()}, a}, b}, E.QAdd{a, b}, B, SN.in_comb(DR.qo(), a, b, B, ha, hb),
    p => add.id(p, a, b))

def qm1() -> S.Q:
  S.Q{S.Zneg{S.XH{}}, S.XH{}}

def sub.id(+p: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr) -> S.Q.eq(E.qeval(p, E.QSub{a, b}), E.qeval(p, E.QAdd{E.QMul{E.QCst{qm1()}, b}, a})):
  QR.qring_eq([E.qeval(p, a), E.qeval(p, b)], E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QMul{E.QCst{qm1()}, E.QVar{1n}}, E.QVar{0n}}, {==})

def in_sub(+a: E.QExpr, +b: E.QExpr, +B: List<&2, E.QExpr>, +ha: SN.InSpan(a, B), +hb: SN.InSpan(b, B)) -> SN.InSpan(E.QSub{a, b}, B):
  in_id(E.QAdd{E.QMul{E.QCst{qm1()}, b}, a}, E.QSub{a, b}, B, SN.in_comb(qm1(), b, a, B, hb, ha),
    p => sub.id(p, a, b))

def in_neg(+a: E.QExpr, +B: List<&2, E.QExpr>, +h: SN.InSpan(a, B)) -> SN.InSpan(E.QNeg{a}, B):
  in_id(E.QAdd{E.QMul{E.QCst{qm1()}, a}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QNeg{a}, B, SN.in_comb(qm1(), a, E.QCst{S.Q{S.Z0{}, S.XH{}}}, B, h, SN.in_zero(B)),
    p => QR.qring_eq([E.qeval(p, a)], E.QNeg{E.QVar{0n}}, E.QAdd{E.QMul{E.QCst{qm1()}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==}))

# Forms
# -----

# both parts of x are in the span of B
def VS(+x: SK.VE, +B: List<&2, E.QExpr>) -> Data:
  SK.Both(SN.InSpan(SK.VE.x(x), B), SN.InSpan(SK.VE.y(x), B))

def vs.x(+x: SK.VE, +B: List<&2, E.QExpr>, h: VS(x, B)) -> SN.InSpan(SK.VE.x(x), B):
  (a, b) = h
  a

def vs.y(+x: SK.VE, +B: List<&2, E.QExpr>, h: VS(x, B)) -> SN.InSpan(SK.VE.y(x), B):
  (a, b) = h
  b

def svx(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameD(SK.VE.x(u), SK.VE.x(v)):
  (a, b) = h
  a

def svy(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameD(SK.VE.y(u), SK.VE.y(v)):
  (a, b) = h
  b

def vs_tr(+x1: SK.VE, +x2: SK.VE, +B: List<&2, E.QExpr>, +h: VS(x1, B), +s: VD.SameVD(x2, x1)) -> VS(x2, B):
  (in_tr(SK.VE.x(x1), SK.VE.x(x2), B, vs.x(x1, B, h), svx(x2, x1, s)), in_tr(SK.VE.y(x1), SK.VE.y(x2), B, vs.y(x1, B, h), svy(x2, x1, s)))

def vs_zero(+B: List<&2, E.QExpr>) -> VS(DR.zerov(), B):
  (SN.in_zero(B), SN.in_zero(B))

def vs_vlin(+m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, +B: List<&2, E.QExpr>, +h1: VS(x1, B), +h2: VS(x2, B)) -> VS(DR.vlin(m1, x1, m2, x2), B):
  (in_add(E.QMul{E.QCst{m1}, SK.VE.x(x1)}, E.QMul{E.QCst{m2}, SK.VE.x(x2)}, B, in_scale(m1, SK.VE.x(x1), B, vs.x(x1, B, h1)), in_scale(m2, SK.VE.x(x2), B, vs.x(x2, B, h2))),
   in_add(E.QMul{E.QCst{m1}, SK.VE.y(x1)}, E.QMul{E.QCst{m2}, SK.VE.y(x2)}, B, in_scale(m1, SK.VE.y(x1), B, vs.y(x1, B, h1)), in_scale(m2, SK.VE.y(x2), B, vs.y(x2, B, h2))))

def vs_rot(+c: S.Q, +s: S.Q, +x: SK.VE, +B: List<&2, E.QExpr>, +hx: SN.InSpan(SK.VE.x(x), B), +hy: SN.InSpan(SK.VE.y(x), B)) -> VS(SK.VE.rot(E.QCst{c}, E.QCst{s}, x), B):
  (in_sub(E.QMul{E.QCst{c}, SK.VE.x(x)}, E.QMul{E.QCst{s}, SK.VE.y(x)}, B, in_scale(c, SK.VE.x(x), B, hx), in_scale(s, SK.VE.y(x), B, hy)),
   in_add(E.QMul{E.QCst{s}, SK.VE.x(x)}, E.QMul{E.QCst{c}, SK.VE.y(x)}, B, in_scale(s, SK.VE.x(x), B, hx), in_scale(c, SK.VE.y(x), B, hy)))

def vs_gmul(g: DR.Lab, +x: SK.VE, +B: List<&2, E.QExpr>, +h: VS(x, B)) -> VS(DR.gmul(g, x), B):
  match g:
    case DR.Lab{+c, +s}:
      vs_rot(c, s, x, B, vs.x(x, B, h), vs.y(x, B, h))

def vs_imul(+x: SK.VE, +B: List<&2, E.QExpr>, +h: VS(x, B)) -> VS(DR.imul(x), B):
  (in_neg(SK.VE.y(x), B, vs.y(x, B, h)), vs.x(x, B, h))

def vs_add(+a: SK.VE, +b: SK.VE, +B: List<&2, E.QExpr>, +ha: VS(a, B), +hb: VS(b, B)) -> VS(SK.VE.add(a, b), B):
  (in_add(SK.VE.x(a), SK.VE.x(b), B, vs.x(a, B, ha), vs.x(b, B, hb)), in_add(SK.VE.y(a), SK.VE.y(b), B, vs.y(a, B, ha), vs.y(b, B, hb)))

# The facts
# ---------

def in_bstat(ds: Maybe<&2, DR.DStat>, +R0: List<&2, E.QExpr>, +D: List<&2, E.QExpr>, +e: E.QExpr, +h: SN.InSpan(e, DC.qcat(R0, D))) -> SN.InSpan(e, DC.qcat(DC.bstat(ds, R0), D)):
  match ds:
    case None{}:
      h
    case Some{DR.DStat{a, +x, l}}:
      in_tl(e, SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(R0, D)}, in_tl(e, SK.VE.y(x), DC.qcat(R0, D), h))

def fe_in.hd(f: DR.Fact, +t: List<&2, DR.Fact>, +D: List<&2, E.QExpr>) -> SN.InSpan(DR.fact.e(Some{f}), DC.qcat(DC.fbases(Con{f, t}), D)):
  match f:
    case DR.Fact{+e, nd, +ds}:
      in_hd(e, DC.qcat(DC.bstat(ds, DC.fbases(t)), D))

def fe_in.tl(f: DR.Fact, +t: List<&2, DR.Fact>, +D: List<&2, E.QExpr>, +x: E.QExpr, +h: SN.InSpan(x, DC.qcat(DC.fbases(t), D))) -> SN.InSpan(x, DC.qcat(DC.fbases(Con{f, t}), D)):
  match f:
    case DR.Fact{+e, nd, +ds}:
      in_tl(x, e, DC.qcat(DC.bstat(ds, DC.fbases(t)), D), in_bstat(ds, DC.fbases(t), D, x, h))

# a fact's equation is in the bases' span
def fe_in(fs: List<&2, DR.Fact>, i: Nat, +D: List<&2, E.QExpr>) -> SN.InSpan(DR.fact.e(DR.fact_at(fs, i)), DC.qcat(DC.fbases(fs), D)):
  match fs i:
    case Nil{} i:
      SN.in_zero(D)
    case Con{+f, +t} 0n:
      fe_in.hd(f, t, D)
    case Con{+f, +t} 1n++j:
      fe_in.tl(f, t, D, DR.fact.e(DR.fact_at(t, j)), fe_in(t, j, D))

def vs_tl(+x: SK.VE, +b: E.QExpr, +rest: List<&2, E.QExpr>, +h: VS(x, rest)) -> VS(x, Con{b, rest}):
  (in_tl(SK.VE.x(x), b, rest, vs.x(x, rest, h)), in_tl(SK.VE.y(x), b, rest, vs.y(x, rest, h)))

def fs_in.st(ds: Maybe<&2, DR.DStat>, +e: E.QExpr, +nd: List<&2, Nat>, +t: List<&2, DR.Fact>, +D: List<&2, E.QExpr>)
  -> VS(DR.Jd.x(DR.fact.pj(Some{DR.Fact{e, nd, ds}})), DC.qcat(DC.fbases(Con{DR.Fact{e, nd, ds}, t}), D)):
  match ds:
    case None{}:
      vs_zero(Con{e, DC.qcat(DC.fbases(t), D)})
    case Some{DR.DStat{+a, +x, +l}}:
      (in_tl(SK.VE.x(x), e, Con{SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(DC.fbases(t), D)}}, in_hd(SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(DC.fbases(t), D)})),
       in_tl(SK.VE.y(x), e, Con{SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(DC.fbases(t), D)}}, in_tl(SK.VE.y(x), SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(DC.fbases(t), D)}, in_hd(SK.VE.y(x), DC.qcat(DC.fbases(t), D)))))

def fs_in.hd(f: DR.Fact, +t: List<&2, DR.Fact>, +D: List<&2, E.QExpr>) -> VS(DR.Jd.x(DR.fact.pj(Some{f})), DC.qcat(DC.fbases(Con{f, t}), D)):
  match f:
    case DR.Fact{+e, +nd, +ds}:
      fs_in.st(ds, e, nd, t, D)

def fs_in.tl(+f: DR.Fact, +t: List<&2, DR.Fact>, +D: List<&2, E.QExpr>, +x: SK.VE, +h: VS(x, DC.qcat(DC.fbases(t), D))) -> VS(x, DC.qcat(DC.fbases(Con{f, t}), D)):
  (fe_in.tl(f, t, D, SK.VE.x(x), vs.x(x, DC.qcat(DC.fbases(t), D), h)), fe_in.tl(f, t, D, SK.VE.y(x), vs.y(x, DC.qcat(DC.fbases(t), D), h)))

# a fact's statement form is in the bases' span
def fs_in(fs: List<&2, DR.Fact>, i: Nat, +D: List<&2, E.QExpr>) -> VS(DR.Jd.x(DR.fact.pj(DR.fact_at(fs, i))), DC.qcat(DC.fbases(fs), D)):
  match fs i:
    case Nil{} i:
      vs_zero(D)
    case Con{+f, +t} 0n:
      fs_in.hd(f, t, D)
    case Con{+f, +t} 1n++j:
      fs_in.tl(f, t, D, DR.Jd.x(DR.fact.pj(DR.fact_at(t, j))), fs_in(t, j, D))

# Coefficients outside the bases' monomials
# -----------------------------------------

# m is among ms (by the comparison coefficients use)
def mmem(+m: List<&2, Nat>, ms: List<&2, List<&2, Nat>>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{n, t}:
      SV.bor(EL.iseq(NR.mcmp(m, n)), mmem(m, t))

def cz_out.go(b: Bool, +m: List<&2, Nat>, +c: S.Z, +n: List<&2, Nat>, +t: List<&2, R.ZTerm>, +rest: List<&2, List<&2, Nat>>, eb: {b == EL.iseq(NR.mcmp(m, n)) : Bool},
  h: {SV.bor(b, mmem(m, DC.tmons(t, rest))) == False{} : Bool}, ih: {mmem(m, DC.tmons(t, rest)) == False{} : Bool} -> {EL.cz(m, t) == S.Z0{} : S.Z})
  -> {EL.cz(m, Con{R.ZTerm{c, n}, t}) == S.Z0{} : S.Z}:
  match b:
    case True{}:
      absurd({EL.cz(m, Con{R.ZTerm{c, n}, t}) == S.Z0{} : S.Z}, KA.tf(h))
    case False{}:
      %eb : {S.Z.add(EL.ifz(_, c), EL.cz(m, t)) == S.Z0{} : S.Z}
      ih(h)

# a monomial not among p's has coefficient 0 in p
def cz_out(+m: List<&2, Nat>, p: List<&2, R.ZTerm>, +rest: List<&2, List<&2, Nat>>, h: {mmem(m, DC.tmons(p, rest)) == False{} : Bool}) -> {EL.cz(m, p) == S.Z0{} : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +t}:
      cz_out.go(EL.iseq(NR.mcmp(m, n)), m, c, n, t, rest, {==}, h, x => cz_out(m, t, rest, x))

def bor_rf(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, KA.tf(h))
    case False{}:
      h

def mmem_rest(+m: List<&2, Nat>, p: List<&2, R.ZTerm>, +rest: List<&2, List<&2, Nat>>, h: {mmem(m, DC.tmons(p, rest)) == False{} : Bool}) -> {mmem(m, rest) == False{} : Bool}:
  match p:
    case Nil{}:
      h
    case Con{R.ZTerm{+c, +n}, +t}:
      mmem_rest(m, t, rest, bor_rf(EL.iseq(NR.mcmp(m, n)), mmem(m, DC.tmons(t, rest)), h))

# every base has coefficient 0 at m
def czs0(B: List<&2, E.QExpr>, +m: List<&2, Nat>) -> Bool:
  match B:
    case Nil{}:
      True{}
    case Con{b, t}:
      SV.band(EP.iszero(EL.cz(m, EP.NE(b))), czs0(t, m))

def czs_out(B: List<&2, E.QExpr>, +m: List<&2, Nat>, +h: {mmem(m, DC.kmons(B)) == False{} : Bool}) -> {czs0(B, m) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(Bool, EP.iszero(EL.cz(m, EP.NE(b))), True{}, EP.iszero_of(EL.cz(m, EP.NE(b)), cz_out(m, EP.NE(b), DC.kmons(t), h))) : {SV.band(_, czs0(t, m)) == True{} : Bool}
      czs_out(t, m, mmem_rest(m, EP.NE(b), DC.kmons(t), h))

def qlin_z(ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +m: List<&2, Nat>, h: {czs0(B, m) == True{} : Bool}) -> {S.Q.num(CF.qlin(ls, B, m)) == S.Z0{} : S.Z}:
  match ls B:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bt}:
      {==}
    case Con{l, lt} Nil{}:
      {==}
    case Con{+l, +lt} Con{+b, +bt}:
      +h2 = h
      +e0 = EP.zero_of(EL.cz(m, EP.NE(b)), LP2.band_l(EP.iszero(EL.cz(m, EP.NE(b))), czs0(bt, m), h2))
      %Equal.sym(S.Z, EL.cz(m, EP.NE(b)), S.Z0{}, e0) : {S.Z.add(S.Z.mul(S.Z.mul(S.Q.num(l), _), S.Zpos{S.Q.den(CF.qlin(lt, bt, m))}), S.Z.mul(S.Q.num(CF.qlin(lt, bt, m)), S.Zpos{S.Pos.mul(S.Q.den(l), QN.den(b))})) == S.Z0{} : S.Z}
      %ZL.mul_zero(S.Q.num(l)) : {S.Z.add(S.Z.mul(_, S.Zpos{S.Q.den(CF.qlin(lt, bt, m))}), S.Z.mul(S.Q.num(CF.qlin(lt, bt, m)), S.Zpos{S.Pos.mul(S.Q.den(l), QN.den(b))})) == S.Z0{} : S.Z}
      %Equal.sym(S.Z, S.Q.num(CF.qlin(lt, bt, m)), S.Z0{}, qlin_z(lt, bt, m, LP2.band_r(EP.iszero(EL.cz(m, EP.NE(b))), czs0(bt, m), h2))) : {S.Z.add(S.Z0{}, S.Z.mul(_, S.Zpos{S.Pos.mul(S.Q.den(l), QN.den(b))})) == S.Z0{} : S.Z}
      {==}

# a combination of the bases has coefficient 0 at m
def lin_cz(+ls: List<&2, S.Q>, +B: List<&2, E.QExpr>, +m: List<&2, Nat>, h: {czs0(B, m) == True{} : Bool}) -> {EL.cz(m, EP.NE(SV.lin(ls, B))) == S.Z0{} : S.Z}:
  CF.num0(CF.qlin(ls, B, m), CF.coef(SV.lin(ls, B), m), CF.coef_lin(ls, B, m), qlin_z(ls, B, m, h))

def mulpos_zero(z: S.Z, +p: S.Pos, h: {S.Z.mul(z, S.Zpos{p}) == S.Z0{} : S.Z}) -> {z == S.Z0{} : S.Z}:
  match z:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      absurd({S.Zpos{q} == S.Z0{} : S.Z}, KA.ft(Equal.cong(S.Z, Bool, x => EP.iszero(x), S.Z.mul(S.Zpos{q}, S.Zpos{p}), S.Z0{}, h)))
    case S.Zneg{q}:
      absurd({S.Zneg{q} == S.Z0{} : S.Z}, KA.ft(Equal.cong(S.Z, Bool, x => EP.iszero(x), S.Z.mul(S.Zneg{q}, S.Zpos{p}), S.Z0{}, h)))

def span_cz.go(+x: E.QExpr, +L: E.QExpr, +m: List<&2, Nat>, hL: {EL.cz(m, EP.NE(L)) == S.Z0{} : S.Z}, q: {QN.qzero(E.QSub{x, L}) == True{} : Bool}) -> {EL.cz(m, EP.NE(x)) == S.Z0{} : S.Z}:
  mulpos_zero(EL.cz(m, EP.NE(x)), QN.den(L),
    Equal.trans(S.Z, S.Z.mul(EL.cz(m, EP.NE(x)), S.Zpos{QN.den(L)}), S.Z.add(S.Z.mul(EL.cz(m, EP.NE(x)), S.Zpos{QN.den(L)}), S.Z0{}), S.Z0{},
      ZL.add_zero(S.Z.mul(EL.cz(m, EP.NE(x)), S.Zpos{QN.den(L)})),
      (%hL : {S.Z.sub(S.Z.mul(EL.cz(m, EP.NE(x)), S.Zpos{QN.den(L)}), S.Z.mul(_, S.Zpos{QN.den(x)})) == S.Z0{} : S.Z}
       CF.coef_zero(x, L, m, QN.nil_of(R.norm(QN.clr(E.QSub{x, L})), q)))))

# everything in the bases' span has coefficient 0 at a monomial where every
# base does
def span_cz(+x: E.QExpr, +B: List<&2, E.QExpr>, +m: List<&2, Nat>, +h: SN.InSpan(x, B), hz: {czs0(B, m) == True{} : Bool}) -> {EL.cz(m, EP.NE(x)) == S.Z0{} : S.Z}:
  span_cz.go(x, SV.lin(SN.in_ls(x, B, h), B), m, lin_cz(SN.in_ls(x, B, h), B, m, hz), SN.in_qz(x, B, h))
