# bend-cad: a hull, proven (PLAN-sk13b B3). The invariant: the rows are
# sk-13a's echelon form of the encoded generators, and every generator's
# derivation is valid, proves a parallel judgment at the root, and proves
# a form whose parts are below t. Adding keeps it. A zero residual gives a
# valid par-lin chain proving par(r, y): its conclusion is clin of the
# generators (pchain_x), lin over the encoded generators is clin's
# encoding (enc_lin), and the tag separates (lib/seppf.bend). A nonzero
# residual means no combination. Proofs only.

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
import ./seppf.bend as SP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS

# both parts of a form are below t
def VBelow(+x: SK.VE, +t: Nat) -> Data:
  SK.Both({SP.vbelow(SK.VE.x(x), t) == True{} : Bool}, {SP.vbelow(SK.VE.y(x), t) == True{} : Bool})

# every generator's derivation is valid, proves a parallel judgment at r,
# and its form is below t
def AllP(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>) -> Type:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, tl}:
      DR.Valid(es, fs, ctx, d) & (DR.IsP(DR.concl(es, fs, d)) & ({DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node} & (VBelow(DR.Jd.x(DR.concl(es, fs, d)), t) & AllP(es, fs, ctx, r, t, tl))))

def HInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS) -> Type:
  match h:
    case HS.HS{+rows, +ds}:
      {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool} & ({EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat} & AllP(es, fs, ctx, r, t, ds))

def hs0_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat) -> HInv(es, fs, ctx, r, t, HS.hs0()):
  ({==}, ({==}, Unit{}))

# Adding a generator
# ------------------

def encs_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, ds: List<&2, DR.Der>, +d: DR.Der) -> {HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t) == EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(tl, d)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, tl), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), encs_snoc(es, fs, t, tl, d)) : {Con{HS.enc(DR.Jd.x(DR.concl(es, fs, h)), t), _} == Con{HS.enc(DR.Jd.x(DR.concl(es, fs, h)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, tl), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))} : List<&2, E.QExpr>}
      {==}

# what a generator brings: valid, parallel at r, below t
def PGen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der) -> Type:
  DR.Valid(es, fs, ctx, d) & (DR.IsP(DR.concl(es, fs, d)) & ({DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node} & VBelow(DR.Jd.x(DR.concl(es, fs, d)), t)))

def allp_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>, +d: DR.Der, h: AllP(es, fs, ctx, r, t, ds), hd: PGen(es, fs, ctx, r, t, d)) -> AllP(es, fs, ctx, r, t, KS.dsnoc(ds, d)):
  match ds:
    case Nil{}:
      (v, r1) = hd
      (p, r2) = r1
      (n, b) = r2
      (v, (p, (n, (b, Unit{}))))
    case Con{+h0, +tl}:
      (v0, r1) = h
      (p0, r2) = r1
      (n0, r3) = r2
      (b0, rt) = r3
      (v0, (p0, (n0, (b0, allp_snoc(es, fs, ctx, r, t, tl, d, rt, hd)))))

def hs_add.rinv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der,
  hr: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) == False{} : Bool})
  -> {EP.rinv(HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t), EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), 0n) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), encs_snoc(es, fs, t, ds, d)) : {EP.rinv(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), 0n) == True{} : Bool}
  EP.new_rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), hr, hl, hne)

def hs_add.len(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +x: EL.Row,
  hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat})
  -> {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t)) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), encs_snoc(es, fs, t, ds, d)) : {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(_) : Nat}
  %Equal.sym(Nat, SV.neqs(EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))), 1n+SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), CW.neqs_qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))) : {EL.rlen(EL.rsnoc(rows, x)) == _ : Nat}
  %Equal.sym(Nat, EL.rlen(EL.rsnoc(rows, x)), 1n+EL.rlen(rows), CW.rlen_rsnoc(rows, x)) : {_ == 1n+SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}
  %Equal.sym(Nat, EL.rlen(rows), SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), hl) : {1n+_ == 1n+SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}
  {==}

def hs_add.pick(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, b: Bool,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) : Bool},
  +hr: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, ha: AllP(es, fs, ctx, r, t, ds), hd: PGen(es, fs, ctx, r, t, d))
  -> HInv(es, fs, ctx, r, t, HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d)):
  match b:
    case True{}:
      (hr, (hl, ha))
    case False{}:
      (hs_add.rinv(es, fs, t, rows, ds, d, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb)),
       (hs_add.len(es, fs, t, rows, ds, d, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))), hl), allp_snoc(es, fs, ctx, r, t, ds, d, ha, hd)))

# adding a generator keeps the invariant
def hs_add_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +d: DR.Der, hi: HInv(es, fs, ctx, r, t, h), hd: PGen(es, fs, ctx, r, t, d)) -> HInv(es, fs, ctx, r, t, HS.hs.add(es, fs, t, h, d)):
  match h:
    case HS.HS{+rows, +ds}:
      (hr, rr) = hi
      (hl, ha) = rr
      hs_add.pick(es, fs, ctx, r, t, rows, ds, d, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), {==}, hr, hl, ha, hd)

# The par-lin chain
# -----------------

def AllBelow(xs: List<&2, SK.VE>, +t: Nat) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, tl}:
      SK.Both(VBelow(x, t), AllBelow(tl, t))

def pchain_x(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, ls: List<&2, S.Q>, ds: List<&2, DR.Der>) -> {DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))) == HS.clin(es, r, ls, HS.hxs(es, fs, ds)) : SK.VE}:
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      %Equal.sym(SK.VE, DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lt, dt))), HS.clin(es, r, lt, HS.hxs(es, fs, dt)), pchain_x(es, fs, r, lt, dt)) : {DR.vlin(l, DR.Jd.x(DR.concl(es, fs, d)), DR.qo(), _) == HS.clin(es, r, Con{l, lt}, HS.hxs(es, fs, Con{d, dt})) : SK.VE}
      {==}
    case Nil{} ds:
      {==}
    case Con{l, lt} Nil{}:
      {==}

def pchain_ok.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +l: S.Q, +d: DR.Der, +rest: DR.Der, +dt: List<&2, DR.Der>,
  v: DR.Valid(es, fs, ctx, d), p: DR.IsP(DR.concl(es, fs, d)), +n: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, b: VBelow(DR.Jd.x(DR.concl(es, fs, d)), t),
  ih: ((DR.Valid(es, fs, ctx, rest) & DR.IsP(DR.concl(es, fs, rest))) & {DR.Jd.a(DR.concl(es, fs, rest)) == r : DR.Node}) & AllBelow(HS.hxs(es, fs, dt), t))
  -> ((DR.Valid(es, fs, ctx, DR.DPLin{l, d, DR.qo(), rest}) & DR.IsP(DR.concl(es, fs, DR.DPLin{l, d, DR.qo(), rest}))) & {DR.Jd.a(DR.concl(es, fs, DR.DPLin{l, d, DR.qo(), rest})) == r : DR.Node}) & AllBelow(HS.hxs(es, fs, Con{d, dt}), t):
  (vn, ab) = ih
  (vp, nr) = vn
  (vr, pr) = vp
  ((((v, (vr, (p, (pr, Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, d)), r, DR.Jd.a(DR.concl(es, fs, rest)), n, Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, rest)), r, nr)))))), Unit{}), n), (b, ab))

def allp_below(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>, h: AllP(es, fs, ctx, r, t, ds)) -> AllBelow(HS.hxs(es, fs, ds), t):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (v, r1) = h
      (p, r2) = r1
      (n, r3) = r2
      (b, rt) = r3
      (b, allp_below(es, fs, ctx, r, t, tl, rt))

def pchain_ok.base(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>, h: AllP(es, fs, ctx, r, t, ds))
  -> ((DR.Valid(es, fs, ctx, HS.pchain(r, Nil{}, ds)) & DR.IsP(DR.concl(es, fs, HS.pchain(r, Nil{}, ds)))) & {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, Nil{}, ds))) == r : DR.Node}) & AllBelow(HS.hxs(es, fs, ds), t):
  ((((Unit{}, (Unit{}, (Unit{}, (Unit{}, {==})))), Unit{}), {==}), allp_below(es, fs, ctx, r, t, ds, h))

# the chain over the generators is valid, parallel at r, and the
# generators' forms are below t
def pchain_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ls: List<&2, S.Q>, ds: List<&2, DR.Der>, h: AllP(es, fs, ctx, r, t, ds))
  -> ((DR.Valid(es, fs, ctx, HS.pchain(r, ls, ds)) & DR.IsP(DR.concl(es, fs, HS.pchain(r, ls, ds)))) & {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, ls, ds))) == r : DR.Node}) & AllBelow(HS.hxs(es, fs, ds), t):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (v, r1) = h
      (p, r2) = r1
      (n, r3) = r2
      (b, rt) = r3
      pchain_ok.go(es, fs, ctx, r, t, l, d, HS.pchain(r, lt, dt), dt, v, p, n, b, pchain_ok(es, fs, ctx, r, t, lt, dt, rt))
    case Nil{} ds:
      pchain_ok.base(es, fs, ctx, r, t, ds, h)
    case Con{l, lt} Nil{}:
      ((((Unit{}, (Unit{}, (Unit{}, (Unit{}, {==})))), Unit{}), {==}), Unit{})


# lin over the encoded forms is the encoding of clin
# --------------------------------------------------

def enc_lin.step(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +l: S.Q, +x: SK.VE, +lt: List<&2, S.Q>, +xt: List<&2, SK.VE>,
  ih: SV.Ident(SV.lin(lt, HS.encs(xt, t)), HS.enc(HS.clin(es, r, lt, xt), t)))
  -> S.Q.eq(E.qeval(p, SV.lin(Con{l, lt}, HS.encs(Con{x, xt}, t))), E.qeval(p, HS.enc(HS.clin(es, r, Con{l, lt}, Con{x, xt}), t))):
  LQ.q_trans(E.qeval(p, SV.lin(Con{l, lt}, HS.encs(Con{x, xt}, t))),
    S.Q.add(S.Q.mul(l, E.qeval(p, HS.enc(x, t))), E.qeval(p, HS.enc(HS.clin(es, r, lt, xt), t))),
    E.qeval(p, HS.enc(HS.clin(es, r, Con{l, lt}, Con{x, xt}), t)),
    LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, HS.enc(x, t))), E.qeval(p, SV.lin(lt, HS.encs(xt, t))), E.qeval(p, HS.enc(HS.clin(es, r, lt, xt), t)), ih(p)),
    QR.qring_eq([l, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.y(x)), E.qlookup(p, t), E.qeval(p, SK.VE.x(HS.clin(es, r, lt, xt))), E.qeval(p, SK.VE.y(HS.clin(es, r, lt, xt)))],
      E.QAdd{E.QMul{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QMul{E.QVar{3n}, E.QVar{2n}}}}, E.QAdd{E.QVar{4n}, E.QMul{E.QVar{3n}, E.QVar{5n}}}},
      E.QAdd{E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{4n}}}, E.QMul{E.QVar{3n}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{5n}}}}},
      {==}))

def enc_lin.base(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat)
  -> S.Q.eq(SP.q0(), E.qeval(p, HS.enc(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), t))):
  QR.qring_eq([E.qeval(p, SK.VE.x(DR.zdir(es, r))), E.qeval(p, SK.VE.y(DR.zdir(es, r))), E.qlookup(p, t)],
    E.QCst{SP.q0()},
    E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QMul{E.QVar{2n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}}},
    {==})

def enc_lin(+es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, ls: List<&2, S.Q>, xs: List<&2, SK.VE>) -> SV.Ident(SV.lin(ls, HS.encs(xs, t)), HS.enc(HS.clin(es, r, ls, xs), t)):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      p => enc_lin.step(p, es, r, t, l, x, lt, xt, enc_lin(es, r, t, lt, xt))
    case Nil{} xs:
      p => enc_lin.base(p, es, r, t)
    case Con{l, lt} Nil{}:
      p => enc_lin.base(p, es, r, t)

# clin's parts are below t when its forms and r's direction are
# -------------------------------------------------------------

def band_tt(a: Bool, b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {SV.band(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {SV.band(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {SV.band(True{}, _) == True{} : Bool}
  {==}

def vlin_below.go(+m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, +t: Nat, a1: {SP.vbelow(SK.VE.x(x1), t) == True{} : Bool}, b1: {SP.vbelow(SK.VE.y(x1), t) == True{} : Bool}, h2: VBelow(x2, t)) -> VBelow(DR.vlin(m1, x1, m2, x2), t):
  (a2, b2) = h2
  (band_tt(SP.vbelow(SK.VE.x(x1), t), SP.vbelow(SK.VE.x(x2), t), a1, a2), band_tt(SP.vbelow(SK.VE.y(x1), t), SP.vbelow(SK.VE.y(x2), t), b1, b2))

def vlin_below(+m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, +t: Nat, h1: VBelow(x1, t), h2: VBelow(x2, t)) -> VBelow(DR.vlin(m1, x1, m2, x2), t):
  (a1, b1) = h1
  vlin_below.go(m1, x1, m2, x2, t, a1, b1, h2)

def clin_below(+es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, ls: List<&2, S.Q>, xs: List<&2, SK.VE>, h: AllBelow(xs, t), +hr: VBelow(DR.zdir(es, r), t)) -> VBelow(HS.clin(es, r, ls, xs), t):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      (hx, ht) = h
      vlin_below(l, x, DR.qo(), HS.clin(es, r, lt, xt), t, hx, clin_below(es, r, t, lt, xt, ht, hr))
    case Nil{} xs:
      vlin_below(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), t, hr, hr)
    case Con{l, lt} Nil{}:
      vlin_below(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), t, hr, hr)

# Membership
# ----------

def ident_trans.at(+p: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, h1: SV.Ident(a, b), h2: SV.Ident(b, c)) -> S.Q.eq(E.qeval(p, a), E.qeval(p, c)):
  LQ.q_trans(E.qeval(p, a), E.qeval(p, b), E.qeval(p, c), h1(p), h2(p))

def ident_trans(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, h1: SV.Ident(a, b), h2: SV.Ident(b, c)) -> SV.Ident(a, c):
  p => ident_trans.at(p, a, b, c, h1, h2)

def samev_of(+y: SK.VE, +z: SK.VE, h: SV.Ident(SK.VE.x(y), SK.VE.x(z)) & SV.Ident(SK.VE.y(y), SK.VE.y(z))) -> DR.SameV(z, y):
  (h1, h2) = h
  (KP.ident_same(SK.VE.x(y), SK.VE.x(z), h1), KP.ident_same(SK.VE.y(y), SK.VE.y(z), h2))

def hs_der.sep(+es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +y: SK.VE, +z: SK.VE, +y1: {SP.vbelow(SK.VE.x(y), t) == True{} : Bool}, +y2: {SP.vbelow(SK.VE.y(y), t) == True{} : Bool}, hc: VBelow(z, t),
  h: SV.Ident(HS.enc(y, t), HS.enc(z, t))) -> DR.SameV(z, y):
  (c1, c2) = hc
  samev_of(y, z, SP.sep(SK.VE.x(y), SK.VE.y(y), SK.VE.x(z), SK.VE.y(z), t, y1, y2, c1, c2, h))

# y in the hull: the chain for y is valid, parallel at r, and proves y
def hs_der.sep0(+es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +y: SK.VE, +z: SK.VE, hy: VBelow(y, t), hc: VBelow(z, t),
  h: SV.Ident(HS.enc(y, t), HS.enc(z, t))) -> DR.SameV(z, y):
  (y1, y2) = hy
  hs_der.sep(es, r, t, y, z, y1, y2, hc, h)

def hs_der.same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +ds: List<&2, DR.Der>, +y: SK.VE, +ls: List<&2, S.Q>,
  hid: SV.Ident(HS.enc(y, t), SV.lin(ls, HS.encs(HS.hxs(es, fs, ds), t))), hy: VBelow(y, t), hc: VBelow(HS.clin(es, r, ls, HS.hxs(es, fs, ds)), t))
  -> DR.SameV(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), y):
  %Equal.sym(SK.VE, DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), HS.clin(es, r, ls, HS.hxs(es, fs, ds)), pchain_x(es, fs, r, ls, ds)) : DR.SameV(_, y)
  hs_der.sep0(es, r, t, y, HS.clin(es, r, ls, HS.hxs(es, fs, ds)), hy, hc,
    ident_trans(HS.enc(y, t), SV.lin(ls, HS.encs(HS.hxs(es, fs, ds), t)), HS.enc(HS.clin(es, r, ls, HS.hxs(es, fs, ds)), t), hid, enc_lin(es, r, t, ls, HS.hxs(es, fs, ds))))

def hs_der.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE, +ls: List<&2, S.Q>,
  hid: SV.Ident(HS.enc(y, t), SV.lin(ls, HS.encs(HS.hxs(es, fs, ds), t))), +hy: VBelow(y, t), +hr: VBelow(DR.zdir(es, r), t),
  pc: ((DR.Valid(es, fs, ctx, HS.pchain(r, ls, ds)) & DR.IsP(DR.concl(es, fs, HS.pchain(r, ls, ds)))) & {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, ls, ds))) == r : DR.Node}) & AllBelow(HS.hxs(es, fs, ds), t))
  -> ((DR.Valid(es, fs, ctx, HS.pchain(r, ls, ds)) & DR.IsP(DR.concl(es, fs, HS.pchain(r, ls, ds)))) & {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, ls, ds))) == r : DR.Node}) & DR.SameV(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), y):
  (vn, ab) = pc
  (vn, hs_der.same(es, fs, r, t, ds, y, ls, hid, hy, clin_below(es, r, t, ls, HS.hxs(es, fs, ds), ab, hr)))

def hs_der_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +y: SK.VE, hi: HInv(es, fs, ctx, r, t, h), hz: {HS.hs.inb(h, y, t) == True{} : Bool}, +hy: VBelow(y, t), +hr: VBelow(DR.zdir(es, r), t))
  -> ((DR.Valid(es, fs, ctx, HS.hs.der(es, fs, t, r, h, y)) & DR.IsP(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y)))) & {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))) == r : DR.Node}) & DR.SameV(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y):
  match h:
    case HS.HS{+rows, +ds}:
      (hrv, rr) = hi
      (hl, ha) = rr
      hs_der.go(es, fs, ctx, r, t, rows, ds, y, DV.dropls(DV.rescb(EL.resid(rows, HS.enc(y, t))), DV.resbt(EL.resid(rows, HS.enc(y, t))), HS.enc(y, t), HS.encs(HS.hxs(es, fs, ds), t)),
        DV.derivable(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(y, t), hrv, hz), hy, hr,
        pchain_ok(es, fs, ctx, r, t, DV.dropls(DV.rescb(EL.resid(rows, HS.enc(y, t))), DV.resbt(EL.resid(rows, HS.enc(y, t))), HS.enc(y, t), HS.encs(HS.hxs(es, fs, ds), t)), ds, ha))

# y not in the hull: no combination of the encoded generators is y's
# encoding
def hs_out(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +y: SK.VE, hi: HInv(es, fs, ctx, r, t, h), hz: {HS.hs.inb(h, y, t) == False{} : Bool})
  -> @ls: List<&2, S.Q> -> SV.Ident(HS.enc(y, t), SV.lin(ls, HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t))) -> Empty:
  match h:
    case HS.HS{+rows, +ds}:
      (hrv, rr) = hi
      (hl, ha) = rr
      IN.indep(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(y, t), hrv, hl, hz)
