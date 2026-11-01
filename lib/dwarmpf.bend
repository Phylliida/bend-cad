# bend-cad: a closure run started from an earlier state (PLAN-sk13b B4.8,
# the incremental closure). A state kept for facts P is a state for any
# facts fs that agree with P at its positions (lib/dmemopf.bend: Pre):
# - a valid derivation cites only facts it has (vd_db), so it stays valid
#   over fs and concludes the same (vd_pre, by concl_pre); so the state's
#   invariant carries (skinv_pre: K's generators, records, links).
# Proofs only.

import Base
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./seppf.bend as SP
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspacepf.bend as HP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcgenpf.bend as GN
import ./dcroundpf.bend as RD
import ./dmemopf.bend as MP

def absurd(-A: Type, x: Empty) -> A:
  match x:

def ft(h: {False{} == True{} : Bool}) -> Empty:
  KA.tf(Equal.sym(Bool, False{}, True{}, h))

# What a valid derivation cites
# -----------------------------

def hasf_lt(fs: List<&2, DR.Fact>, i: Nat, h: {VD.hasf(DR.fact_at(fs, i)) == True{} : Bool}) -> {SV.lt(i, MP.flen(fs)) == True{} : Bool}:
  match fs i:
    case Nil{} 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, ft(h))
    case Nil{} 1n+j:
      absurd({SV.lt(1n+j, 0n) == True{} : Bool}, ft(h))
    case Con{+f, +t} 0n:
      {==}
    case Con{+f, +t} 1n+j:
      hasf_lt(t, j, h)

def hass_lt(fs: List<&2, DR.Fact>, i: Nat, h: {VD.hass(DR.fact_at(fs, i)) == True{} : Bool}) -> {SV.lt(i, MP.flen(fs)) == True{} : Bool}:
  match fs i:
    case Nil{} 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, ft(h))
    case Nil{} 1n+j:
      absurd({SV.lt(1n+j, 0n) == True{} : Bool}, ft(h))
    case Con{+f, +t} 0n:
      {==}
    case Con{+f, +t} 1n+j:
      hass_lt(t, j, h)

# a valid derivation cites only positions of fs
def vd_db(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, d: DR.Der, v: VD.VD(es, fs, ctx, d)) -> MP.DB(d, MP.flen(fs)):
  match d:
    case DR.DZero{}:
      Unit{}
    case DR.DPrem{+i}:
      hasf_lt(fs, i, v)
    case DR.DKAdd{+l, +d1, +d2}:
      (v1, r1) = v
      (v2, r2) = r1
      (vd_db(es, fs, ctx, d1, v1), vd_db(es, fs, ctx, d2, v2))
    case DR.DBack{+d0}:
      (v0, r1) = v
      vd_db(es, fs, ctx, d0, v0)
    case DR.DLine{+d1, +d2, +re}:
      (v1, r1) = v
      (v2, r2) = r1
      (vd_db(es, fs, ctx, d1, v1), vd_db(es, fs, ctx, d2, v2))
    case DR.DPPrem{+i}:
      hass_lt(fs, i, v)
    case DR.DSelf{+a}:
      Unit{}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r1) = v
      (v2, r2) = r1
      (vd_db(es, fs, ctx, d1, v1), vd_db(es, fs, ctx, d2, v2))
    case DR.DKnown{+d0, +dr, +di}:
      (v0, r1) = v
      (vr, r2) = r1
      (vi, r3) = r2
      (vd_db(es, fs, ctx, d0, v0), (vd_db(es, fs, ctx, dr, vr), vd_db(es, fs, ctx, di, vi)))
    case DR.DTurn{+d0, +g, +nb}:
      (v0, r1) = v
      vd_db(es, fs, ctx, d0, v0)
    case DR.DThrough{+d1, +d2, +g, +nb}:
      (v1, r1) = v
      (v2, r2) = r1
      (vd_db(es, fs, ctx, d1, v1), vd_db(es, fs, ctx, d2, v2))
    case DR.DFrame{+d0, +x}:
      (v0, r1) = v
      vd_db(es, fs, ctx, d0, v0)
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r1) = v
      (vi, r2) = r1
      (vd_db(es, fs, ctx, dr, vr), vd_db(es, fs, ctx, di, vi))

# so it concludes the same over facts that agree
def cpre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +d: DR.Der, +h: MP.Pre(fs1, fs2), +v: VD.VD(es, fs1, ctx, d)) -> {DR.concl(es, fs1, d) == DR.concl(es, fs2, d) : DR.Jd}:
  MP.concl_pre(es, fs1, fs2, d, h, vd_db(es, fs1, ctx, d, v))

def hasf_pre(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat, +h: MP.Pre(fs1, fs2), hv: {VD.hasf(DR.fact_at(fs1, i)) == True{} : Bool}) -> {VD.hasf(DR.fact_at(fs2, i)) == True{} : Bool}:
  match fs1 fs2 i:
    case Nil{} Nil{} 0n:
      absurd({VD.hasf(DR.fact_at(Nil{}, 0n)) == True{} : Bool}, ft(hv))
    case Nil{} Nil{} 1n+j:
      absurd({VD.hasf(DR.fact_at(Nil{}, 1n+j)) == True{} : Bool}, ft(hv))
    case Nil{} Con{+g, +t2} 0n:
      absurd({VD.hasf(DR.fact_at(Con{g, t2}, 0n)) == True{} : Bool}, ft(hv))
    case Nil{} Con{+g, +t2} 1n+j:
      absurd({VD.hasf(DR.fact_at(Con{g, t2}, 1n+j)) == True{} : Bool}, ft(hv))
    case Con{+f, +t1} Nil{} 0n:
      absurd({VD.hasf(DR.fact_at(Nil{}, 0n)) == True{} : Bool}, h)
    case Con{+f, +t1} Nil{} 1n+j:
      absurd({VD.hasf(DR.fact_at(Nil{}, 1n+j)) == True{} : Bool}, h)
    case Con{+f, +t1} Con{+g, +t2} 0n:
      {==}
    case Con{+f, +t1} Con{+g, +t2} 1n+j:
      (a, ht) = h
      hasf_pre(t1, t2, j, ht, hv)

def hass_ag(f: DR.Fact, g: DR.Fact, h: MP.FAg(f, g)) -> {VD.hass(Some{f}) == VD.hass(Some{g}) : Bool}:
  match f g:
    case DR.Fact{+e1, +n1, +d1} DR.Fact{+e2, +n2, +d2}:
      %MP.fag.ds(DR.Fact{e1, n1, d1}, DR.Fact{e2, n2, d2}, h) : {VD.hass(Some{DR.Fact{e1, n1, d1}}) == VD.hass(Some{DR.Fact{e2, n2, _}}) : Bool}
      {==}

def hass_pre(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat, +h: MP.Pre(fs1, fs2), hv: {VD.hass(DR.fact_at(fs1, i)) == True{} : Bool}) -> {VD.hass(DR.fact_at(fs2, i)) == True{} : Bool}:
  match fs1 fs2 i:
    case Nil{} Nil{} 0n:
      absurd({VD.hass(DR.fact_at(Nil{}, 0n)) == True{} : Bool}, ft(hv))
    case Nil{} Nil{} 1n+j:
      absurd({VD.hass(DR.fact_at(Nil{}, 1n+j)) == True{} : Bool}, ft(hv))
    case Nil{} Con{+g, +t2} 0n:
      absurd({VD.hass(DR.fact_at(Con{g, t2}, 0n)) == True{} : Bool}, ft(hv))
    case Nil{} Con{+g, +t2} 1n+j:
      absurd({VD.hass(DR.fact_at(Con{g, t2}, 1n+j)) == True{} : Bool}, ft(hv))
    case Con{+f, +t1} Nil{} 0n:
      absurd({VD.hass(DR.fact_at(Nil{}, 0n)) == True{} : Bool}, h)
    case Con{+f, +t1} Nil{} 1n+j:
      absurd({VD.hass(DR.fact_at(Nil{}, 1n+j)) == True{} : Bool}, h)
    case Con{+f, +t1} Con{+g, +t2} 0n:
      (a, ht) = h
      Equal.trans(Bool, VD.hass(Some{g}), VD.hass(Some{f}), True{}, Equal.sym(Bool, VD.hass(Some{f}), VD.hass(Some{g}), hass_ag(f, g, a)), hv)
    case Con{+f, +t1} Con{+g, +t2} 1n+j:
      (a, ht) = h
      hass_pre(t1, t2, j, ht, hv)

# One judgment for another, equal one
# -----------------------------------

def tr.isk(+j: DR.Jd, +j2: DR.Jd, +e: {j == j2 : DR.Jd}, h: VD.Isk(j)) -> VD.Isk(j2):
  %e : VD.Isk(_)
  h

def tr.isp(+j: DR.Jd, +j2: DR.Jd, +e: {j == j2 : DR.Jd}, h: VD.Isp(j)) -> VD.Isp(j2):
  %e : VD.Isp(_)
  h

def tr.a(+j: DR.Jd, +j2: DR.Jd, +n: DR.Node, +e: {j == j2 : DR.Jd}, h: {DR.Jd.a(j) == n : DR.Node}) -> {DR.Jd.a(j2) == n : DR.Node}:
  %e : {DR.Jd.a(_) == n : DR.Node}
  h

def tr.a2(+j1: DR.Jd, +j1b: DR.Jd, +j2: DR.Jd, +j2b: DR.Jd, +e1: {j1 == j1b : DR.Jd}, +e2: {j2 == j2b : DR.Jd}, h: {DR.Jd.a(j1) == DR.Jd.a(j2) : DR.Node}) -> {DR.Jd.a(j1b) == DR.Jd.a(j2b) : DR.Node}:
  %e1 : {DR.Jd.a(_) == DR.Jd.a(j2b) : DR.Node}
  %e2 : {DR.Jd.a(j1) == DR.Jd.a(_) : DR.Node}
  h

def tr.open(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +j: DR.Jd, +j2: DR.Jd, +e: {j == j2 : DR.Jd}, h: VD.OpenD(es, ctx, DR.Jd.a(j))) -> VD.OpenD(es, ctx, DR.Jd.a(j2)):
  %e : VD.OpenD(es, ctx, DR.Jd.a(_))
  h

def tr.sv(+j: DR.Jd, +j2: DR.Jd, +y: SK.VE, +e: {j == j2 : DR.Jd}, h: VD.SameVD(DR.Jd.x(j), y)) -> VD.SameVD(DR.Jd.x(j2), y):
  %e : VD.SameVD(DR.Jd.x(_), y)
  h

def tr.svim(+j1: DR.Jd, +j1b: DR.Jd, +j2: DR.Jd, +j2b: DR.Jd, +e1: {j1 == j1b : DR.Jd}, +e2: {j2 == j2b : DR.Jd}, h: VD.SameVD(DR.Jd.x(j2), DR.imul(DR.Jd.x(j1)))) -> VD.SameVD(DR.Jd.x(j2b), DR.imul(DR.Jd.x(j1b))):
  %e1 : VD.SameVD(DR.Jd.x(j2b), DR.imul(DR.Jd.x(_)))
  %e2 : VD.SameVD(DR.Jd.x(_), DR.imul(DR.Jd.x(j1)))
  h

def tr.sd(+j: DR.Jd, +j2: DR.Jd, +y: E.QExpr, +e: {j == j2 : DR.Jd}, h: VD.SameD(DR.Jd.e(j), y)) -> VD.SameD(DR.Jd.e(j2), y):
  %e : VD.SameD(DR.Jd.e(_), y)
  h

def tr.vb(+j: DR.Jd, +j2: DR.Jd, +t: Nat, +e: {j == j2 : DR.Jd}, h: HP.VBelow(DR.Jd.x(j), t)) -> HP.VBelow(DR.Jd.x(j2), t):
  %e : HP.VBelow(DR.Jd.x(_), t)
  h

def tr.vbe(+j: DR.Jd, +j2: DR.Jd, +t: Nat, +e: {j == j2 : DR.Jd}, h: {SP.vbelow(DR.Jd.e(j), t) == True{} : Bool}) -> {SP.vbelow(DR.Jd.e(j2), t) == True{} : Bool}:
  %e : {SP.vbelow(DR.Jd.e(_), t) == True{} : Bool}
  h

# a valid derivation over facts P is valid over facts that agree with P
def vd_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, d: DR.Der, +h: MP.Pre(fs1, fs2), v: VD.VD(es, fs1, ctx, d)) -> VD.VD(es, fs2, ctx, d):
  match d:
    case DR.DZero{}:
      Unit{}
    case DR.DPrem{+i}:
      hasf_pre(fs1, fs2, i, h, v)
    case DR.DKAdd{+l, +d1, +d2}:
      (+v1, r1) = v
      (+v2, r2) = r1
      (k1, k2) = r2
      (vd_pre(es, fs1, fs2, ctx, d1, h, v1), (vd_pre(es, fs1, fs2, ctx, d2, h, v2), (tr.isk(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), cpre(es, fs1, fs2, ctx, d1, h, v1), k1), tr.isk(DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d2, h, v2), k2))))
    case DR.DBack{+d0}:
      (+v0, r1) = v
      (ip, ea) = r1
      (vd_pre(es, fs1, fs2, ctx, d0, h, v0), (tr.isp(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), cpre(es, fs1, fs2, ctx, d0, h, v0), ip), tr.a(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), DR.NFrame{}, cpre(es, fs1, fs2, ctx, d0, h, v0), ea)))
    case DR.DLine{+d1, +d2, +re}:
      (+v1, r1) = v
      (+v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (ea, r5) = r4
      (op, sv) = r5
      (vd_pre(es, fs1, fs2, ctx, d1, h, v1), (vd_pre(es, fs1, fs2, ctx, d2, h, v2), (tr.isp(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), cpre(es, fs1, fs2, ctx, d1, h, v1), p1), (tr.isp(DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d2, h, v2), p2), (tr.a2(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d1, h, v1), cpre(es, fs1, fs2, ctx, d2, h, v2), ea), (tr.open(es, ctx, DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), cpre(es, fs1, fs2, ctx, d1, h, v1), op), tr.svim(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d1, h, v1), cpre(es, fs1, fs2, ctx, d2, h, v2), sv)))))))
    case DR.DPPrem{+i}:
      hass_pre(fs1, fs2, i, h, v)
    case DR.DSelf{+a}:
      Unit{}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (+v1, r1) = v
      (+v2, r2) = r1
      (p1, r3) = r2
      (p2, ea) = r3
      (vd_pre(es, fs1, fs2, ctx, d1, h, v1), (vd_pre(es, fs1, fs2, ctx, d2, h, v2), (tr.isp(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), cpre(es, fs1, fs2, ctx, d1, h, v1), p1), (tr.isp(DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d2, h, v2), p2), tr.a2(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d1, h, v1), cpre(es, fs1, fs2, ctx, d2, h, v2), ea)))))
    case DR.DKnown{+d0, +dr, +di}:
      (+v0, r1) = v
      (+vr, r2) = r1
      (+vi, r3) = r2
      (p0, r4) = r3
      (kr, ki) = r4
      (vd_pre(es, fs1, fs2, ctx, d0, h, v0), (vd_pre(es, fs1, fs2, ctx, dr, h, vr), (vd_pre(es, fs1, fs2, ctx, di, h, vi), (tr.isp(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), cpre(es, fs1, fs2, ctx, d0, h, v0), p0), (tr.isk(DR.concl(es, fs1, dr), DR.concl(es, fs2, dr), cpre(es, fs1, fs2, ctx, dr, h, vr), kr), tr.isk(DR.concl(es, fs1, di), DR.concl(es, fs2, di), cpre(es, fs1, fs2, ctx, di, h, vi), ki))))))
    case DR.DTurn{+d0, +g, +nb}:
      (+v0, r1) = v
      (p0, sv) = r1
      (vd_pre(es, fs1, fs2, ctx, d0, h, v0), (tr.isp(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), cpre(es, fs1, fs2, ctx, d0, h, v0), p0), tr.sv(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), DR.gmul(DR.Lab.conj(g), DR.zdir(es, nb)), cpre(es, fs1, fs2, ctx, d0, h, v0), sv)))
    case DR.DThrough{+d1, +d2, +g, +nb}:
      (+v1, r1) = v
      (+v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (sv, r5) = r4
      (ea, op) = r5
      (vd_pre(es, fs1, fs2, ctx, d1, h, v1), (vd_pre(es, fs1, fs2, ctx, d2, h, v2), (tr.isp(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), cpre(es, fs1, fs2, ctx, d1, h, v1), p1), (tr.isp(DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), cpre(es, fs1, fs2, ctx, d2, h, v2), p2), (tr.sv(DR.concl(es, fs1, d1), DR.concl(es, fs2, d1), DR.gmul(DR.Lab.conj(g), DR.zdir(es, nb)), cpre(es, fs1, fs2, ctx, d1, h, v1), sv), (tr.a(DR.concl(es, fs1, d2), DR.concl(es, fs2, d2), nb, cpre(es, fs1, fs2, ctx, d2, h, v2), ea), op))))))
    case DR.DFrame{+d0, +x}:
      (+v0, r1) = v
      (k0, sd) = r1
      (vd_pre(es, fs1, fs2, ctx, d0, h, v0), (tr.isk(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), cpre(es, fs1, fs2, ctx, d0, h, v0), k0), tr.sd(DR.concl(es, fs1, d0), DR.concl(es, fs2, d0), SK.VE.y(x), cpre(es, fs1, fs2, ctx, d0, h, v0), sd)))
    case DR.DVoid{+dr, +di, +a, +x}:
      (+vr, r1) = v
      (+vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      (vd_pre(es, fs1, fs2, ctx, dr, h, vr), (vd_pre(es, fs1, fs2, ctx, di, h, vi), (tr.isk(DR.concl(es, fs1, dr), DR.concl(es, fs2, dr), cpre(es, fs1, fs2, ctx, dr, h, vr), kr), (tr.isk(DR.concl(es, fs1, di), DR.concl(es, fs2, di), cpre(es, fs1, fs2, ctx, di, h, vi), ki), (tr.sd(DR.concl(es, fs1, dr), DR.concl(es, fs2, dr), SK.VE.x(DR.zdir(es, a)), cpre(es, fs1, fs2, ctx, dr, h, vr), sr), tr.sd(DR.concl(es, fs1, di), DR.concl(es, fs2, di), SK.VE.y(DR.zdir(es, a)), cpre(es, fs1, fs2, ctx, di, h, vi), si))))))

# The state's invariant
# ---------------------

def kgen_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +d: DR.Der, +h: MP.Pre(fs1, fs2), kg: IV.KGen(es, fs1, ctx, t, d)) -> IV.KGen(es, fs2, ctx, t, d):
  (+v, r1) = kg
  (ik, vb) = r1
  (vd_pre(es, fs1, fs2, ctx, d, h, v), (tr.isk(DR.concl(es, fs1, d), DR.concl(es, fs2, d), cpre(es, fs1, fs2, ctx, d, h, v), ik), tr.vbe(DR.concl(es, fs1, d), DR.concl(es, fs2, d), t, cpre(es, fs1, fs2, ctx, d, h, v), vb)))

def allkd_pre(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: MP.Pre(fs1, fs2), ha: IV.AllKD(es, fs1, ctx, t, ds)) -> IV.AllKD(es, fs2, ctx, t, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (kg, rt) = ha
      (kgen_pre(es, fs1, fs2, ctx, t, d, h, kg), allkd_pre(tl, es, fs1, fs2, ctx, t, h, rt))

def kgen_c(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +d: DR.Der, +h: MP.Pre(fs1, fs2), kg: IV.KGen(es, fs1, ctx, t, d)) -> {DR.concl(es, fs1, d) == DR.concl(es, fs2, d) : DR.Jd}:
  (v, r1) = kg
  cpre(es, fs1, fs2, ctx, d, h, v)

# K's generators conclude the same
def kexprs_pre(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: MP.Pre(fs1, fs2), ha: IV.AllKD(es, fs1, ctx, t, ds))
  -> {KS.kexprs(es, fs1, ds) == KS.kexprs(es, fs2, ds) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      (kg, rt) = ha
      %kgen_c(es, fs1, fs2, ctx, t, d, h, kg) : {Con{DR.Jd.e(DR.concl(es, fs1, d)), KS.kexprs(es, fs1, tl)} == Con{DR.Jd.e(_), KS.kexprs(es, fs2, tl)} : List<&2, E.QExpr>}
      %kexprs_pre(tl, es, fs1, fs2, ctx, t, h, rt) : {Con{DR.Jd.e(DR.concl(es, fs1, d)), KS.kexprs(es, fs1, tl)} == Con{DR.Jd.e(DR.concl(es, fs1, d)), _} : List<&2, E.QExpr>}
      {==}

def kinvd.c(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +h: MP.Pre(fs1, fs2),
  hr: {EP.rinv(KS.kexprs(es, fs1, ds), rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs1, ds)) : Nat}, +ha: IV.AllKD(es, fs1, ctx, t, ds)) -> IV.KInvD(es, fs2, ctx, t, KS.KS{rows, ds}):
  ((%kexprs_pre(ds, es, fs1, fs2, ctx, t, h, ha) : {EP.rinv(_, rows, 0n) == True{} : Bool}
     hr),
   ((%kexprs_pre(ds, es, fs1, fs2, ctx, t, h, ha) : {EL.rlen(rows) == SV.neqs(_) : Nat}
      hl),
    allkd_pre(ds, es, fs1, fs2, ctx, t, h, ha)))

def kinvd_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, +h: MP.Pre(fs1, fs2), hk: IV.KInvD(es, fs1, ctx, t, k)) -> IV.KInvD(es, fs2, ctx, t, k):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = hk
      (hl, ha) = r1
      kinvd.c(es, fs1, fs2, ctx, t, rows, ds, h, hr, hl, ha)

def mokd_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, m: DC.Mem, +h: MP.Pre(fs1, fs2), mk: GN.MOkD(es, fs1, ctx, t, m)) -> GN.MOkD(es, fs2, ctx, t, m):
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      (+v, r1) = mk
      (ip, r2) = r1
      (ea, r3) = r2
      (sv, r4) = r3
      (oa, r5) = r4
      (orr, vb) = r5
      (vd_pre(es, fs1, fs2, ctx, d, h, v), (tr.isp(DR.concl(es, fs1, d), DR.concl(es, fs2, d), cpre(es, fs1, fs2, ctx, d, h, v), ip), (tr.a(DR.concl(es, fs1, d), DR.concl(es, fs2, d), r, cpre(es, fs1, fs2, ctx, d, h, v), ea),
        (tr.sv(DR.concl(es, fs1, d), DR.concl(es, fs2, d), DR.gmul(w, DR.zdir(es, a)), cpre(es, fs1, fs2, ctx, d, h, v), sv), (oa, (orr, tr.vb(DR.concl(es, fs1, d), DR.concl(es, fs2, d), t, cpre(es, fs1, fs2, ctx, d, h, v), vb)))))))

def msok_pre(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: MP.Pre(fs1, fs2), hm: GN.MsOk(es, fs1, ctx, t, ms)) -> GN.MsOk(es, fs2, ctx, t, ms):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m, +tl}:
      (h1, rt) = hm
      (mokd_pre(es, fs1, fs2, ctx, t, m, h, h1), msok_pre(tl, es, fs1, fs2, ctx, t, h, rt))

def lokd_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, l: DC.Link, +h: MP.Pre(fs1, fs2), lk: GN.LOkD(es, fs1, ctx, t, l)) -> GN.LOkD(es, fs2, ctx, t, l):
  match l:
    case DC.Link{+c, +b, +w, +d}:
      (+v, r1) = lk
      (ip, r2) = r1
      (ea, r3) = r2
      (sv, vb) = r3
      (vd_pre(es, fs1, fs2, ctx, d, h, v), (tr.isp(DR.concl(es, fs1, d), DR.concl(es, fs2, d), cpre(es, fs1, fs2, ctx, d, h, v), ip), (tr.a(DR.concl(es, fs1, d), DR.concl(es, fs2, d), DR.NSeg{c}, cpre(es, fs1, fs2, ctx, d, h, v), ea),
        (tr.sv(DR.concl(es, fs1, d), DR.concl(es, fs2, d), DR.gmul(w, DR.zdir(es, b)), cpre(es, fs1, fs2, ctx, d, h, v), sv), tr.vb(DR.concl(es, fs1, d), DR.concl(es, fs2, d), t, cpre(es, fs1, fs2, ctx, d, h, v), vb)))))

def lsok_pre(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: MP.Pre(fs1, fs2), hl: GN.LsOk(es, fs1, ctx, t, ls)) -> GN.LsOk(es, fs2, ctx, t, ls):
  match ls:
    case Nil{}:
      Unit{}
    case Con{+l, +tl}:
      (h1, rt) = hl
      (lokd_pre(es, fs1, fs2, ctx, t, l, h, h1), lsok_pre(tl, es, fs1, fs2, ctx, t, h, rt))

# a state kept for facts P is one for facts that agree with P
def skinv_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +h: MP.Pre(fs1, fs2), hs: RD.SkInv(es, fs1, ctx, t, s)) -> RD.SkInv(es, fs2, ctx, t, s):
  (hk, r1) = hs
  (hm, r2) = r1
  (hl, r3) = r2
  (hmn, hln) = r3
  (kinvd_pre(es, fs1, fs2, ctx, t, DC.Sk.k(s), h, hk), (msok_pre(DC.Sk.ms(s), es, fs1, fs2, ctx, t, h, hm), (lsok_pre(DC.Sk.ls(s), es, fs1, fs2, ctx, t, h, hl), (hmn, hln))))
