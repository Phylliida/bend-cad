# bend-cad: a reusable form of validity, for the closure's proofs
# (PLAN-sk13b B3). spec/dir.bend's Valid is a Type: its identities are
# functions (Same), its Open a negation, and Bend lets each be used once.
# The closure shares one derivation among many (a member's, in every
# generator through it), so its invariants hold VD instead: the same
# conditions as Data, identities in the normalizer's form
# {qzero(e1 - e2) == True} (lib/identpf.bend), Open as the closure's own
# test (lib/dcopenpf.bend). VD gives Valid (valid_of). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./qnorm.bend as QN
import ./identpf.bend as ID
import ./labpf.bend as LP
import ./dclose.bend as DC
import ./dcopenpf.bend as OP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Data forms
# ----------

def isk(j: DR.Jd) -> Bool:
  match j:
    case DR.JK{e}:
      True{}
    case DR.JP{a, x}:
      False{}

def isp(j: DR.Jd) -> Bool:
  match j:
    case DR.JK{e}:
      False{}
    case DR.JP{a, x}:
      True{}

def hasf(m: Maybe<&2, DR.Fact>) -> Bool:
  match m:
    case Some{f}:
      True{}
    case None{}:
      False{}

def hass.ds(ds: Maybe<&2, DR.DStat>) -> Bool:
  match ds:
    case Some{DR.DStat{a, x, l}}:
      DR.qnz(l)
    case None{}:
      False{}

def hass(m: Maybe<&2, DR.Fact>) -> Bool:
  match m:
    case Some{DR.Fact{e, nd, ds}}:
      hass.ds(ds)
    case None{}:
      False{}

def SameD(+e1: E.QExpr, +e2: E.QExpr) -> Data:
  {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}

def SameVD(+u: SK.VE, +v: SK.VE) -> Data:
  SK.Both(SameD(SK.VE.x(u), SK.VE.x(v)), SameD(SK.VE.y(u), SK.VE.y(v)))

def OpenD(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +n: DR.Node) -> Data:
  {DC.isopen(es, OP.cspan(ctx), n) == True{} : Bool}

def Isk(+j: DR.Jd) -> Data:
  {isk(j) == True{} : Bool}

def Isp(+j: DR.Jd) -> Data:
  {isp(j) == True{} : Bool}

# d follows the rules, as Data
def VD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, d: DR.Der) -> Data:
  match d:
    case DR.DZero{}:
      Unit
    case DR.DPrem{+i}:
      {hasf(DR.fact_at(fs, i)) == True{} : Bool}
    case DR.DKAdd{+l, +d1, +d2}:
      SK.Both(VD(es, fs, ctx, d1), SK.Both(VD(es, fs, ctx, d2), SK.Both(Isk(DR.concl(es, fs, d1)), Isk(DR.concl(es, fs, d2)))))
    case DR.DBack{+d}:
      SK.Both(VD(es, fs, ctx, d), SK.Both(Isp(DR.concl(es, fs, d)), {DR.Jd.a(DR.concl(es, fs, d)) == DR.NFrame{} : DR.Node}))
    case DR.DLine{+d1, +d2, +re}:
      SK.Both(VD(es, fs, ctx, d1), SK.Both(VD(es, fs, ctx, d2), SK.Both(Isp(DR.concl(es, fs, d1)), SK.Both(Isp(DR.concl(es, fs, d2)), SK.Both({DR.Jd.a(DR.concl(es, fs, d1)) == DR.Jd.a(DR.concl(es, fs, d2)) : DR.Node}, SK.Both(OpenD(es, ctx, DR.Jd.a(DR.concl(es, fs, d1))), SameVD(DR.Jd.x(DR.concl(es, fs, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs, d1))))))))))
    case DR.DPPrem{+i}:
      {hass(DR.fact_at(fs, i)) == True{} : Bool}
    case DR.DSelf{+a}:
      Unit
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      SK.Both(VD(es, fs, ctx, d1), SK.Both(VD(es, fs, ctx, d2), SK.Both(Isp(DR.concl(es, fs, d1)), SK.Both(Isp(DR.concl(es, fs, d2)), {DR.Jd.a(DR.concl(es, fs, d1)) == DR.Jd.a(DR.concl(es, fs, d2)) : DR.Node}))))
    case DR.DKnown{+d, +dr, +di}:
      SK.Both(VD(es, fs, ctx, d), SK.Both(VD(es, fs, ctx, dr), SK.Both(VD(es, fs, ctx, di), SK.Both(Isp(DR.concl(es, fs, d)), SK.Both(Isk(DR.concl(es, fs, dr)), Isk(DR.concl(es, fs, di)))))))
    case DR.DTurn{+d, +g, +b}:
      SK.Both(VD(es, fs, ctx, d), SK.Both(Isp(DR.concl(es, fs, d)), SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))))
    case DR.DThrough{+d1, +d2, +g, +b}:
      SK.Both(VD(es, fs, ctx, d1), SK.Both(VD(es, fs, ctx, d2), SK.Both(Isp(DR.concl(es, fs, d1)), SK.Both(Isp(DR.concl(es, fs, d2)), SK.Both(SameVD(DR.Jd.x(DR.concl(es, fs, d1)), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), SK.Both({DR.Jd.a(DR.concl(es, fs, d2)) == b : DR.Node}, OpenD(es, ctx, b)))))))
    case DR.DFrame{+d, +x}:
      SK.Both(VD(es, fs, ctx, d), SK.Both(Isk(DR.concl(es, fs, d)), SameD(DR.Jd.e(DR.concl(es, fs, d)), SK.VE.y(x))))
    case DR.DVoid{+dr, +di, +a, +x}:
      SK.Both(VD(es, fs, ctx, dr), SK.Both(VD(es, fs, ctx, di), SK.Both(Isk(DR.concl(es, fs, dr)), SK.Both(Isk(DR.concl(es, fs, di)), SK.Both(SameD(DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zdir(es, a))), SameD(DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zdir(es, a))))))))

# Back to the Type forms
# ----------------------

def isk_of(j: DR.Jd, h: {isk(j) == True{} : Bool}) -> DR.IsK(j):
  match j:
    case DR.JK{e}:
      Unit{}
    case DR.JP{a, x}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h))

def isp_of(j: DR.Jd, h: {isp(j) == True{} : Bool}) -> DR.IsP(j):
  match j:
    case DR.JK{e}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h))
    case DR.JP{a, x}:
      Unit{}

def hasf_of(m: Maybe<&2, DR.Fact>, h: {hasf(m) == True{} : Bool}) -> DR.HasFact(m):
  match m:
    case Some{f}:
      Unit{}
    case None{}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h))

def hass_of.ds(ds: Maybe<&2, DR.DStat>, +e: E.QExpr, +nd: List<&2, Nat>, h: {hass.ds(ds) == True{} : Bool}) -> DR.HasStat(Some{DR.Fact{e, nd, ds}}):
  match ds:
    case Some{DR.DStat{a, x, l}}:
      h
    case None{}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h))

def hass_of(m: Maybe<&2, DR.Fact>, h: {hass(m) == True{} : Bool}) -> DR.HasStat(m):
  match m:
    case Some{DR.Fact{+e, +nd, ds}}:
      hass_of.ds(ds, e, nd, h)
    case None{}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h))

def same_of(+e1: E.QExpr, +e2: E.QExpr, +h: SameD(e1, e2)) -> DR.Same(e1, e2):
  ID.ident_ok(e1, e2, h)

def samev_of(+u: SK.VE, +v: SK.VE, h: SameVD(u, v)) -> DR.SameV(u, v):
  (h1, h2) = h
  (same_of(SK.VE.x(u), SK.VE.x(v), h1), same_of(SK.VE.y(u), SK.VE.y(v), h2))

# and from them, the Data forms
def samed_of(+e1: E.QExpr, +e2: E.QExpr, h: DR.Same(e1, e2)) -> SameD(e1, e2):
  ID.qzero_ident(e1, e2, h)

def samevd_of(+u: SK.VE, +v: SK.VE, h: DR.SameV(u, v)) -> SameVD(u, v):
  (h1, h2) = h
  (samed_of(SK.VE.x(u), SK.VE.x(v), h1), samed_of(SK.VE.y(u), SK.VE.y(v), h2))

# VD gives Valid
# --------------

def valid_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, d: DR.Der, h: VD(es, fs, ctx, d)) -> DR.Valid(es, fs, ctx, d):
  match d:
    case DR.DZero{}:
      Unit{}
    case DR.DPrem{+i}:
      hasf_of(DR.fact_at(fs, i), h)
    case DR.DKAdd{+l, +d1, +d2}:
      (v1, r1) = h
      (v2, r2) = r1
      (k1, k2) = r2
      (valid_of(es, fs, ctx, d1, v1), (valid_of(es, fs, ctx, d2, v2), (isk_of(DR.concl(es, fs, d1), k1), isk_of(DR.concl(es, fs, d2), k2))))
    case DR.DBack{+d}:
      (v, r1) = h
      (p, ea) = r1
      (valid_of(es, fs, ctx, d, v), (isp_of(DR.concl(es, fs, d), p), ea))
    case DR.DLine{+d1, +d2, +re}:
      (v1, r1) = h
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (ea, r5) = r4
      (ho, hs) = r5
      (valid_of(es, fs, ctx, d1, v1), (valid_of(es, fs, ctx, d2, v2), (isp_of(DR.concl(es, fs, d1), p1), (isp_of(DR.concl(es, fs, d2), p2), (ea,
        (OP.open_of(es, ctx, DR.Jd.a(DR.concl(es, fs, d1)), ho), samev_of(DR.Jd.x(DR.concl(es, fs, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs, d1))), hs)))))))
    case DR.DPPrem{+i}:
      hass_of(DR.fact_at(fs, i), h)
    case DR.DSelf{+a}:
      Unit{}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r1) = h
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, ea) = r3
      (valid_of(es, fs, ctx, d1, v1), (valid_of(es, fs, ctx, d2, v2), (isp_of(DR.concl(es, fs, d1), p1), (isp_of(DR.concl(es, fs, d2), p2), ea))))
    case DR.DKnown{+d, +dr, +di}:
      (v, r1) = h
      (vr, r2) = r1
      (vi, r3) = r2
      (p, r4) = r3
      (kr, ki) = r4
      (valid_of(es, fs, ctx, d, v), (valid_of(es, fs, ctx, dr, vr), (valid_of(es, fs, ctx, di, vi), (isp_of(DR.concl(es, fs, d), p), (isk_of(DR.concl(es, fs, dr), kr), isk_of(DR.concl(es, fs, di), ki))))))
    case DR.DTurn{+d, +g, +b}:
      (v, r1) = h
      (p, hs) = r1
      (valid_of(es, fs, ctx, d, v), (isp_of(DR.concl(es, fs, d), p), samev_of(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), hs)))
    case DR.DThrough{+d1, +d2, +g, +b}:
      (v1, r1) = h
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (hs, r5) = r4
      (ea, ho) = r5
      (valid_of(es, fs, ctx, d1, v1), (valid_of(es, fs, ctx, d2, v2), (isp_of(DR.concl(es, fs, d1), p1), (isp_of(DR.concl(es, fs, d2), p2),
        (samev_of(DR.Jd.x(DR.concl(es, fs, d1)), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), hs), (ea, OP.open_of(es, ctx, b, ho)))))))
    case DR.DFrame{+d, +x}:
      (v, r1) = h
      (k, hs) = r1
      (valid_of(es, fs, ctx, d, v), (isk_of(DR.concl(es, fs, d), k), same_of(DR.Jd.e(DR.concl(es, fs, d)), SK.VE.y(x), hs)))
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r1) = h
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      (valid_of(es, fs, ctx, dr, vr), (valid_of(es, fs, ctx, di, vi), (isk_of(DR.concl(es, fs, dr), kr), (isk_of(DR.concl(es, fs, di), ki),
        (same_of(DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zdir(es, a)), sr), same_of(DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zdir(es, a)), si))))))
