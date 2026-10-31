# bend-cad: K, proven (PLAN-sk13b B2). The invariant: the rows are sk-13a's
# echelon form of the generators (EP.rinv, one row per generator), and
# every generator's derivation is valid and proves a K judgment. Adding a
# generator keeps it (sk-13a's new_rinv). A zero residual gives a valid
# derivation proving e (the K-add chain concludes lin of the generators,
# up to the 0 terms it skips, which sk-13a's derivable shows is e); a
# nonzero one shows no constant combination of the generators is e
# (sk-13a's indep). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./indpf.bend as IN
import ./cwpf.bend as CW
import ./q.bend as LQ
import ./qring.bend as QR
import ./kspace.bend as KS

# every generator's derivation is valid and proves a K judgment
def AllK(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, ds: List<&2, DR.Der>) -> Type:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, t}:
      DR.Valid(es, fs, ctx, d) & (DR.IsK(DR.concl(es, fs, d)) & AllK(es, fs, ctx, t))

def KInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS) -> Type:
  match k:
    case KS.KS{+rows, +ds}:
      {EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool} & ({EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat} & AllK(es, fs, ctx, ds))

def ks0_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>) -> KInv(es, fs, ctx, KS.ks0()):
  ({==}, ({==}, Unit{}))

# Adding a generator
# ------------------

def kexprs_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, ds: List<&2, DR.Der>, +d: DR.Der) -> {KS.kexprs(es, fs, KS.dsnoc(ds, d)) == EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, E.QExpr>, KS.kexprs(es, fs, KS.dsnoc(t, d)), EP.qsnoc(KS.kexprs(es, fs, t), DR.Jd.e(DR.concl(es, fs, d))), kexprs_snoc(es, fs, t, d)) : {Con{DR.Jd.e(DR.concl(es, fs, h)), _} == Con{DR.Jd.e(DR.concl(es, fs, h)), EP.qsnoc(KS.kexprs(es, fs, t), DR.Jd.e(DR.concl(es, fs, d)))} : List<&2, E.QExpr>}
      {==}

def allk_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, ds: List<&2, DR.Der>, +d: DR.Der, h: AllK(es, fs, ctx, ds), hd: DR.Valid(es, fs, ctx, d) & DR.IsK(DR.concl(es, fs, d))) -> AllK(es, fs, ctx, KS.dsnoc(ds, d)):
  match ds:
    case Nil{}:
      (v, k) = hd
      (v, (k, Unit{}))
    case Con{+h0, +t}:
      (v0, r) = h
      (k0, rt) = r
      (v0, (k0, allk_snoc(es, fs, ctx, t, d, rt, hd)))

def ks_add.rinv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der,
  hr: {EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) == False{} : Bool})
  -> {EP.rinv(KS.kexprs(es, fs, KS.dsnoc(ds, d)), EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), 0n) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, KS.kexprs(es, fs, KS.dsnoc(ds, d)), EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), kexprs_snoc(es, fs, ds, d)) : {EP.rinv(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), 0n) == True{} : Bool}
  EP.new_rinv(KS.kexprs(es, fs, ds), rows, DR.Jd.e(DR.concl(es, fs, d)), hr, hl, hne)

def ks_add.len(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +x: EL.Row,
  hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat})
  -> {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(KS.kexprs(es, fs, KS.dsnoc(ds, d))) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, KS.kexprs(es, fs, KS.dsnoc(ds, d)), EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), kexprs_snoc(es, fs, ds, d)) : {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(_) : Nat}
  %Equal.sym(Nat, SV.neqs(EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d)))), 1n+SV.neqs(KS.kexprs(es, fs, ds)), CW.neqs_qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d)))) : {EL.rlen(EL.rsnoc(rows, x)) == _ : Nat}
  %Equal.sym(Nat, EL.rlen(EL.rsnoc(rows, x)), 1n+EL.rlen(rows), CW.rlen_rsnoc(rows, x)) : {_ == 1n+SV.neqs(KS.kexprs(es, fs, ds)) : Nat}
  %Equal.sym(Nat, EL.rlen(rows), SV.neqs(KS.kexprs(es, fs, ds)), hl) : {1n+_ == 1n+SV.neqs(KS.kexprs(es, fs, ds)) : Nat}
  {==}

def ks_add.new(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der,
  +hr: {EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat}, ha: AllK(es, fs, ctx, ds), hd: DR.Valid(es, fs, ctx, d) & DR.IsK(DR.concl(es, fs, d)),
  +hne: {EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) == False{} : Bool})
  -> KInv(es, fs, ctx, KS.KS{EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), KS.dsnoc(ds, d)}):
  (ks_add.rinv(es, fs, rows, ds, d, hr, hl, hne), (ks_add.len(es, fs, rows, ds, d, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d)))), hl), allk_snoc(es, fs, ctx, ds, d, ha, hd)))

def ks_add.pick(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, b: Bool,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) : Bool},
  +hr: {EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat}, ha: AllK(es, fs, ctx, ds), hd: DR.Valid(es, fs, ctx, d) & DR.IsK(DR.concl(es, fs, d)))
  -> KInv(es, fs, ctx, KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d)):
  match b:
    case True{}:
      (hr, (hl, ha))
    case False{}:
      ks_add.new(es, fs, ctx, rows, ds, d, hr, hl, ha, hd, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb))

# adding a generator keeps the invariant
def ks_add_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +d: DR.Der, h: KInv(es, fs, ctx, k), hd: DR.Valid(es, fs, ctx, d) & DR.IsK(DR.concl(es, fs, d))) -> KInv(es, fs, ctx, KS.ks.add(es, fs, k, d)):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r) = h
      (hl, ha) = r
      ks_add.pick(es, fs, ctx, rows, ds, d, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), {==}, hr, hl, ha, hd)

# The K-add chain
# ---------------

# A multiplier that is 0 adds nothing (the chain skips it, KS.kc.pick)
def absurd(-A: Type, x: Empty) -> A:
  match x:

def bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def tf(h: {True{} == False{} : Bool}) -> Empty:
  %h : bt(_)
  Unit{}

def qnz_z.n(n: S.Z, +d: S.Pos, h: {DR.znz(n) == False{} : Bool}) -> S.Q.eq(S.Q{n, d}, DR.qz()):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd(S.Q.eq(S.Q{S.Zpos{p}, d}, DR.qz()), tf(h))
    case S.Zneg{p}:
      absurd(S.Q.eq(S.Q{S.Zneg{p}, d}, DR.qz()), tf(h))

def qnz_z(q: S.Q, h: {DR.qnz(q) == False{} : Bool}) -> S.Q.eq(q, DR.qz()):
  match q:
    case S.Q{n, d}:
      qnz_z.n(n, d, h)

# l X + Y = Y when l is 0
def zl(+l: S.Q, +X: S.Q, +Y: S.Q, h: {DR.qnz(l) == False{} : Bool}) -> S.Q.eq(S.Q.add(S.Q.mul(l, X), Y), Y):
  LQ.q_trans(S.Q.add(S.Q.mul(l, X), Y), S.Q.add(S.Q.mul(DR.qz(), X), Y), Y,
    LQ.q_add_cong_l(S.Q.mul(l, X), S.Q.mul(DR.qz(), X), Y, LQ.q_mul_cong_l(l, DR.qz(), X, qnz_z(l, h))),
    QR.qring_eq([X, Y], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QVar{1n}}, E.QVar{1n}, {==}))

def same_trans.at(+x: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, h1: DR.Same(a, b), h2: DR.Same(b, c)) -> S.Q.eq(E.qeval(x, a), E.qeval(x, c)):
  LQ.q_trans(E.qeval(x, a), E.qeval(x, b), E.qeval(x, c), h1(x), h2(x))

def same_trans(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, h1: DR.Same(a, b), h2: DR.Same(b, c)) -> DR.Same(a, c):
  x => same_trans.at(x, a, b, c, h1, h2)

def kchain_e.t(+x: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +l: S.Q, +d: DR.Der, +rest: DR.Der, +L: E.QExpr, ih: DR.Same(DR.Jd.e(DR.concl(es, fs, rest)), L))
  -> S.Q.eq(S.Q.add(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, DR.Jd.e(DR.concl(es, fs, rest)))), S.Q.add(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, L))):
  LQ.q_add_cong_r(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, DR.Jd.e(DR.concl(es, fs, rest))), E.qeval(x, L), ih(x))

def kchain_e.f(+x: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +l: S.Q, +d: DR.Der, +rest: DR.Der, +L: E.QExpr, +hl: {DR.qnz(l) == False{} : Bool}, ih: DR.Same(DR.Jd.e(DR.concl(es, fs, rest)), L))
  -> S.Q.eq(E.qeval(x, DR.Jd.e(DR.concl(es, fs, rest))), S.Q.add(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, L))):
  LQ.q_trans(E.qeval(x, DR.Jd.e(DR.concl(es, fs, rest))), E.qeval(x, L), S.Q.add(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, L)), ih(x),
    LQ.q_sym(S.Q.add(S.Q.mul(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(x, L)), E.qeval(x, L), zl(l, E.qeval(x, DR.Jd.e(DR.concl(es, fs, d))), E.qeval(x, L), hl)))

def kchain_e.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +l: S.Q, +d: DR.Der, +rest: DR.Der, +L: E.QExpr, eb: {b == DR.qnz(l) : Bool}, ih: DR.Same(DR.Jd.e(DR.concl(es, fs, rest)), L))
  -> DR.Same(DR.Jd.e(DR.concl(es, fs, KS.kc.pick(b, l, d, rest))), E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, fs, d))}, L}):
  match b:
    case True{}:
      x => kchain_e.t(x, es, fs, l, d, rest, L, ih)
    case False{}:
      +hl = Equal.sym(Bool, False{}, DR.qnz(l), eb)
      x => kchain_e.f(x, es, fs, l, d, rest, L, hl, ih)

# the chain proves lin of the generators (up to its 0 terms)
def kchain_e(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, ls: List<&2, S.Q>, ds: List<&2, DR.Der>) -> DR.Same(DR.Jd.e(DR.concl(es, fs, KS.kchain(ls, ds))), SV.lin(ls, KS.kexprs(es, fs, ds))):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      kchain_e.pick(DR.qnz(l), es, fs, l, d, KS.kchain(lt, dt), SV.lin(lt, KS.kexprs(es, fs, dt)), {==}, kchain_e(es, fs, lt, dt))
    case Nil{} ds:
      x => LQ.q_refl(DR.qz())
    case Con{l, lt} Nil{}:
      x => LQ.q_refl(DR.qz())

def kchain_ok.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +l: S.Q, +d: DR.Der, +rest: DR.Der, v: DR.Valid(es, fs, ctx, d), k: DR.IsK(DR.concl(es, fs, d)), ih: DR.Valid(es, fs, ctx, rest) & DR.IsK(DR.concl(es, fs, rest))) -> DR.Valid(es, fs, ctx, DR.DKAdd{l, d, rest}) & DR.IsK(DR.concl(es, fs, DR.DKAdd{l, d, rest})):
  (v2, k2) = ih
  ((v, (v2, (k, k2))), Unit{})

def kchain_ok.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +l: S.Q, +d: DR.Der, +rest: DR.Der, v: DR.Valid(es, fs, ctx, d), k: DR.IsK(DR.concl(es, fs, d)), ih: DR.Valid(es, fs, ctx, rest) & DR.IsK(DR.concl(es, fs, rest)))
  -> DR.Valid(es, fs, ctx, KS.kc.pick(b, l, d, rest)) & DR.IsK(DR.concl(es, fs, KS.kc.pick(b, l, d, rest))):
  match b:
    case True{}:
      kchain_ok.go(es, fs, ctx, l, d, rest, v, k, ih)
    case False{}:
      ih

def kchain_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, ls: List<&2, S.Q>, ds: List<&2, DR.Der>, h: AllK(es, fs, ctx, ds)) -> DR.Valid(es, fs, ctx, KS.kchain(ls, ds)) & DR.IsK(DR.concl(es, fs, KS.kchain(ls, ds))):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (v, r) = h
      (k, rt) = r
      kchain_ok.pick(DR.qnz(l), es, fs, ctx, l, d, KS.kchain(lt, dt), v, k, kchain_ok(es, fs, ctx, lt, dt, rt))
    case Nil{} ds:
      (Unit{}, Unit{})
    case Con{l, lt} Nil{}:
      (Unit{}, Unit{})

# Membership
# ----------

def ident_same.at(+x: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: SV.Ident(e1, e2)) -> S.Q.eq(E.qeval(x, e2), E.qeval(x, e1)):
  LQ.q_sym(E.qeval(x, e1), E.qeval(x, e2), h(x))

def ident_same(+e1: E.QExpr, +e2: E.QExpr, h: SV.Ident(e1, e2)) -> DR.Same(e2, e1):
  x => ident_same.at(x, e1, e2, h)

# e in K: K's chain for e is valid, proves a K judgment, and proves e
def ks_der_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +e: E.QExpr, h: KInv(es, fs, ctx, k), hz: {KS.ks.inb(k, e) == True{} : Bool})
  -> (DR.Valid(es, fs, ctx, KS.ks.der(es, fs, k, e)) & DR.IsK(DR.concl(es, fs, KS.ks.der(es, fs, k, e)))) & DR.Same(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, e))), e):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r) = h
      (hl, ha) = r
      (kchain_ok(es, fs, ctx, DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), ds, ha),
       same_trans(DR.Jd.e(DR.concl(es, fs, KS.kchain(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), ds))),
         SV.lin(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), KS.kexprs(es, fs, ds)), e,
         kchain_e(es, fs, DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), ds),
         ident_same(e, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), KS.kexprs(es, fs, ds)),
           DV.derivable(KS.kexprs(es, fs, ds), rows, e, hr, hz))))

# e not in K: no constant combination of K's generators is e
def ks_out(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +e: E.QExpr, h: KInv(es, fs, ctx, k), hz: {KS.ks.inb(k, e) == False{} : Bool})
  -> @ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, KS.kexprs(es, fs, KS.ks.ds(k)))) -> Empty:
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r) = h
      (hl, ha) = r
      IN.indep(KS.kexprs(es, fs, ds), rows, e, hr, hl, hz)
