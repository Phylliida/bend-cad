# bend-cad: a closure run started from an earlier state (PLAN-sk13b B4.8,
# the incremental closure). A state kept for facts P is a state for any
# facts fs that agree with P at its positions (lib/dmemopf.bend: Pre):
# - a valid derivation cites only facts it has (vd_db), so it stays valid
#   over fs and concludes the same (vd_pre, by concl_pre); so the state's
#   invariant carries (skinv_pre: K's generators, records, links);
# - P's bases are in the span of fs's (allin_fb, in_trans), so K stays in
#   the bases' span (kspan_pre);
# - the warm start (wstart) gives K the facts from position |P| on, as
#   sk0 gives it all: every fact is then in K (kfw), and the run's
#   invariants hold (wstart_t);
# - DC.wfuel bounds the measure of every state (mu_w), so the run from a
#   warm start stops, and gives Ex (warm_ex); frun.fo returns the cache
#   too, right for a fixpoint (frun_fo).
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./seppf.bend as SP
import ./qnorm.bend as QN
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
import ./listpf.bend as LI
import ./spanpf.bend as SN
import ./dcbasepf.bend as BS
import ./dckslpf.bend as KL
import ./dcgspanpf.bend as GS
import ./dcshapepf.bend as SH
import ./ownpf.bend as OW
import ./nat.bend as LN
import ./dcsetpf.bend as ST
import ./dctermpf.bend as TRM
import ./dcopenpf.bend as OP
import ./dcreprpf.bend as RR
import ./dcslotpf.bend as SL
import ./dcfixpf.bend as FX
import ./dfastpf.bend as FP
import ./dcexpf.bend as CX

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

# The bases' span
# ---------------

# a combination of B, each of B in the span of B2, is in the span of B2
def in_lin(ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +B2: List<&2, E.QExpr>, hall: KL.AllIn(B, B2)) -> SN.InSpan(SV.lin(ls, B), B2):
  match ls B:
    case Con{+l, +lt} Con{+b, +bt}:
      (hb, ht) = hall
      SN.in_comb(l, b, SV.lin(lt, bt), B2, hb, in_lin(lt, bt, B2, ht))
    case Con{+l, +lt} Nil{}:
      SN.in_zero(B2)
    case Nil{} Con{+b, +bt}:
      SN.in_zero(B2)
    case Nil{} Nil{}:
      SN.in_zero(B2)

def in_trans.c(+e: E.QExpr, +B: List<&2, E.QExpr>, +B2: List<&2, E.QExpr>, +ls: List<&2, S.Q>, +q: {QN.qzero(E.QSub{e, SV.lin(ls, B)}) == True{} : Bool}, +hall: KL.AllIn(B, B2)) -> SN.InSpan(e, B2):
  BS.in_tr(SV.lin(ls, B), e, B2, in_lin(ls, B, B2, hall), q)

def in_trans(+e: E.QExpr, +B: List<&2, E.QExpr>, +B2: List<&2, E.QExpr>, h: SN.InSpan(e, B), +hall: KL.AllIn(B, B2)) -> SN.InSpan(e, B2):
  (ls, q) = h
  in_trans.c(e, B, B2, ls, q, hall)

def allin_trans(xs: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +B2: List<&2, E.QExpr>, +hall: KL.AllIn(B, B2), h: KL.AllIn(xs, B)) -> KL.AllIn(xs, B2):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (hx, ht) = h
      (in_trans(x, B, B2, hx, hall), allin_trans(t, B, B2, hall, ht))

def allin_tl(xs: List<&2, E.QExpr>, +b: E.QExpr, +B: List<&2, E.QExpr>, h: KL.AllIn(xs, B)) -> KL.AllIn(xs, Con{b, B}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (hx, ht) = h
      (BS.in_tl(x, b, B, hx), allin_tl(t, b, B, ht))

def allin_cons(+b: E.QExpr, +xs: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, h: KL.AllIn(xs, B)) -> KL.AllIn(Con{b, xs}, Con{b, B}):
  (BS.in_hd(b, B), allin_tl(xs, b, B, h))

def allin_refl(B: List<&2, E.QExpr>) -> KL.AllIn(B, B):
  match B:
    case Nil{}:
      Unit{}
    case Con{+b, +t}:
      allin_cons(b, t, t, allin_refl(t))

def allin_catr(+A: List<&2, E.QExpr>, xs: List<&2, E.QExpr>, +C: List<&2, E.QExpr>, h: KL.AllIn(xs, C)) -> KL.AllIn(xs, DC.qcat(A, C)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (hx, ht) = h
      (BS.in_catr(A, C, x, hx), allin_catr(A, t, C, ht))

def allin_bstat(ds: Maybe<&2, DR.DStat>, +X: List<&2, E.QExpr>, +Y: List<&2, E.QExpr>, +D: List<&2, E.QExpr>, h: KL.AllIn(DC.qcat(X, D), DC.qcat(Y, D)))
  -> KL.AllIn(DC.qcat(DC.bstat(ds, X), D), DC.qcat(DC.bstat(ds, Y), D)):
  match ds:
    case None{}:
      h
    case Some{DR.DStat{+a, +x, +l}}:
      allin_cons(SK.VE.x(x), Con{SK.VE.y(x), DC.qcat(X, D)}, Con{SK.VE.y(x), DC.qcat(Y, D)}, allin_cons(SK.VE.y(x), DC.qcat(X, D), DC.qcat(Y, D), h))

def allin_fb.c(f: DR.Fact, g: DR.Fact, +pt: List<&2, DR.Fact>, +ft: List<&2, DR.Fact>, +D: List<&2, E.QExpr>, a: MP.FAg(f, g), ih: KL.AllIn(DC.qcat(DC.fbases(pt), D), DC.qcat(DC.fbases(ft), D)))
  -> KL.AllIn(DC.qcat(DC.fbases(Con{f, pt}), D), DC.qcat(DC.fbases(Con{g, ft}), D)):
  match f g:
    case DR.Fact{+e1, +n1, +d1} DR.Fact{+e2, +n2, +d2}:
      (he, hd) = a
      %he : KL.AllIn(Con{e1, DC.qcat(DC.bstat(d1, DC.fbases(pt)), D)}, Con{_, DC.qcat(DC.bstat(d2, DC.fbases(ft)), D)})
      %hd : KL.AllIn(Con{e1, DC.qcat(DC.bstat(d1, DC.fbases(pt)), D)}, Con{e1, DC.qcat(DC.bstat(_, DC.fbases(ft)), D)})
      allin_cons(e1, DC.qcat(DC.bstat(d1, DC.fbases(pt)), D), DC.qcat(DC.bstat(d1, DC.fbases(ft)), D), allin_bstat(d1, DC.fbases(pt), DC.fbases(ft), D, ih))

# P's bases lie in the span of fs's
def allin_fb(P: List<&2, DR.Fact>, F: List<&2, DR.Fact>, +D: List<&2, E.QExpr>, h: MP.Pre(P, F)) -> KL.AllIn(DC.qcat(DC.fbases(P), D), DC.qcat(DC.fbases(F), D)):
  match P F:
    case Nil{} Nil{}:
      allin_refl(D)
    case Nil{} Con{+g, +ft}:
      allin_catr(DC.fbases(Con{g, ft}), D, D, allin_refl(D))
    case Con{+f, +pt} Nil{}:
      absurd(KL.AllIn(DC.qcat(DC.fbases(Con{f, pt}), D), DC.qcat(DC.fbases(Nil{}), D)), h)
    case Con{+f, +pt} Con{+g, +ft}:
      (a, ht) = h
      allin_fb.c(f, g, pt, ft, D, a, allin_fb(pt, ft, D, ht))

# K stays in the bases' span
def kspan_pre(+es: List<&2, SK.Ent>, +P: List<&2, DR.Fact>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +h: MP.Pre(P, fs), +ha: IV.AllKD(es, P, ctx, t, KS.ks.ds(k)), hs: GS.KSpan(es, P, k))
  -> GS.KSpan(es, fs, k):
  %kexprs_pre(KS.ks.ds(k), es, P, fs, ctx, t, h, ha) : KL.AllIn(_, DC.bases(es, fs))
  allin_trans(KS.kexprs(es, P, KS.ks.ds(k)), DC.bases(es, P), DC.bases(es, fs), allin_fb(P, fs, DC.dbases(es, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}), h), hs)

# Every fact in K
# ---------------

def fd_eq(+fs: List<&2, DR.Fact>, +i: Nat, +n: Nat, +ein: {i == n : Nat}) -> {DC.fdrop(n, fs) == DC.fdrop(i, fs) : List<&2, DR.Fact>}:
  %ein : {DC.fdrop(_, fs) == DC.fdrop(i, fs) : List<&2, DR.Fact>}
  {==}

# no facts of P left: the rest of fs is what K was given
def kfw.nil(+F: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +n: Nat, +k: KS.KS, +hr: SH.KR(es, fs, k), +ed: {GN.fdrop(i, fs) == F : List<&2, DR.Fact>}, +en: {Nat.add(i, 0n) == n : Nat})
  -> SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), F):
  %Equal.trans(List<&2, DR.Fact>, DC.fdrop(n, fs), DC.fdrop(i, fs), F, fd_eq(fs, i, n, Equal.trans(Nat, i, Nat.add(i, 0n), n, LN.add_zero(i), en)), ed) : SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), _)
  SH.kinit_kf(DC.fdrop(n, fs), es, fs, n, k, hr, {==})

def kfw.c(g: DR.Fact, +e1: E.QExpr, +ft: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +n: Nat, +k: KS.KS, +hr: SH.KR(es, fs, k),
  he: {e1 == DR.fact.e(Some{g}) : E.QExpr}, hin: {KS.ks.inb(k, e1) == True{} : Bool}, ih: SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), ft)) -> SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), Con{g, ft}):
  match g:
    case DR.Fact{+e2, +n2, +d2}:
      (SH.kinit_mono(DC.fdrop(n, fs), es, fs, n, k, e2, hr, (%he : ST.Inb(KS.ks.rows(k), _)
         hin)), ih)

# the facts F (fs from position i), agreeing with P whose facts are in K,
# are in K given the facts from position n = i + |P|
def kfw(P: List<&2, DR.Fact>, F: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +n: Nat, +k: KS.KS, +hr: SH.KR(es, fs, k), h: MP.Pre(P, F), kf: SH.KF(k, P),
  +ed: {GN.fdrop(i, fs) == F : List<&2, DR.Fact>}, +en: {Nat.add(i, MP.flen(P)) == n : Nat}) -> SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), F):
  match P F:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+g, +ft}:
      kfw.nil(Con{g, ft}, es, fs, i, n, k, hr, ed, en)
    case Con{DR.Fact{+e1, +n1, +d1}, +pt} Nil{}:
      absurd(SH.KF(DC.kinit(es, fs, DC.fdrop(n, fs), n, k), Nil{}), h)
    case Con{DR.Fact{+e1, +n1, +d1}, +pt} Con{+g, +ft}:
      (a, ht) = h
      (hin, kt) = kf
      kfw.c(g, e1, ft, es, fs, n, k, hr, MP.fag_e(DR.Fact{e1, n1, d1}, g, a), hin,
        kfw(pt, ft, es, fs, 1n+i, n, k, hr, ht, kt, GN.fdrop_tl(i, fs, g, ft, ed), LN.succ_add(i, MP.flen(pt), n, en)))

# The start
# ---------

def fb_tl(f: DR.Fact, +tl: List<&2, DR.Fact>, +t: Nat, h: {DC.fb(Con{f, tl}, t) == True{} : Bool}) -> {DC.fb(tl, t) == True{} : Bool}:
  match f:
    case DR.Fact{+e, +nd, +ds}:
      LI.band_r(DC.fb.ds(ds, t), DC.fb(tl, t), LI.band_r(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), h))

def fb_drop(i: Nat, fs: List<&2, DR.Fact>, +t: Nat, h: {DC.fb(fs, t) == True{} : Bool}) -> {DC.fb(DC.fdrop(i, fs), t) == True{} : Bool}:
  match i fs:
    case 0n Nil{}:
      h
    case 0n Con{+f, +tl}:
      h
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{+f, +tl}:
      fb_drop(j, tl, t, fb_tl(f, tl, t, h))

def kinvd_allkd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, h: IV.KInvD(es, fs, ctx, t, k)) -> IV.AllKD(es, fs, ctx, t, KS.ks.ds(k)):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = h
      (hl, ha) = r1
      ha

def ws.sk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +n: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>, +hb: {DC.fb(fs, t) == True{} : Bool},
  h: RD.SkInv(es, fs, ctx, t, DC.Sk{k, ms, ls})) -> RD.SkInv(es, fs, ctx, t, DC.Sk{DC.kinit(es, fs, DC.fdrop(n, fs), n, k), ms, ls}):
  (hk, r1) = h
  (RD.kinit_ok(DC.fdrop(n, fs), es, fs, ctx, t, n, k, {==}, fb_drop(n, fs, t, hb), hk), r1)

def ws.sh(+es: List<&2, SK.Ent>, +P: List<&2, DR.Fact>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +n: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>,
  +h: MP.Pre(P, fs), +en: {MP.flen(P) == n : Nat}, +hr: SH.KR(es, fs, k), hs: SH.ShInv(es, P, cs, ids, DC.Sk{k, ms, ls})) -> SH.ShInv(es, fs, cs, ids, DC.Sk{DC.kinit(es, fs, DC.fdrop(n, fs), n, k), ms, ls}):
  (hm, r1) = hs
  (kf, pl) = r1
  (hm, (kfw(P, fs, es, fs, 0n, n, k, hr, h, kf, {==}, en), pl))

def ws.c(+es: List<&2, SK.Ent>, +P: List<&2, DR.Fact>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +n: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>,
  +h: MP.Pre(P, fs), +en: {MP.flen(P) == n : Nat}, +hb: {DC.fb(fs, t) == True{} : Bool}, +hsk: RD.SkInv(es, P, ctx, t, DC.Sk{k, ms, ls}), hsh: SH.ShInv(es, P, OP.cspan(ctx), ids, DC.Sk{k, ms, ls}), hk: GS.KSpan(es, P, k))
  -> TRM.TInv(es, fs, ctx, t, ids, DC.Sk{DC.kinit(es, fs, DC.fdrop(n, fs), n, k), ms, ls}):
  ((ws.sk(es, fs, ctx, t, n, k, ms, ls, hb, skinv_pre(es, P, fs, ctx, t, DC.Sk{k, ms, ls}, h, hsk)),
    ws.sh(es, P, fs, OP.cspan(ctx), ids, n, k, ms, ls, h, en, ST.kri(es, fs, ctx, t, k, RR.sk.k(es, fs, ctx, t, DC.Sk{k, ms, ls}, skinv_pre(es, P, fs, ctx, t, DC.Sk{k, ms, ls}, h, hsk))), hsh)),
   GS.kinit_span(DC.fdrop(n, fs), es, fs, n, k, kspan_pre(es, P, fs, ctx, t, k, h, kinvd_allkd(es, P, ctx, t, k, RR.sk.k(es, P, ctx, t, DC.Sk{k, ms, ls}, hsk)), hk)))

# a state with the run's invariants for facts P, given the facts of fs past
# P (fs agreeing with P), has them for fs
def wstart_t(+es: List<&2, SK.Ent>, +P: List<&2, DR.Fact>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +n: Nat, s: DC.Sk,
  +h: MP.Pre(P, fs), +en: {MP.flen(P) == n : Nat}, +hb: {DC.fb(fs, t) == True{} : Bool}, hi: TRM.TInv(es, P, ctx, t, ids, s)) -> TRM.TInv(es, fs, ctx, t, ids, DC.wstart(es, fs, n, s)):
  match s:
    case DC.Sk{+k, +ms, +ls}:
      (h1, hk) = hi
      (hsk, hsh) = h1
      ws.c(es, P, fs, ctx, t, ids, n, k, ms, ls, h, en, hb, hsk, hsh, hk)

# The fuel
# --------

def rc1_le(m: DC.Mem) -> {KA.natle(SL.rc1(m), 1n) == True{} : Bool}:
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      TRM.rb_le(DC.node_eq(a, r))

def rc_le(ms: List<&2, DC.Mem>) -> {KA.natle(SL.rcount(ms), DC.mcount(ms)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      KA.natle_add2(SL.rc1(m), SL.rcount(t), 1n, DC.mcount(t), rc1_le(m), rc_le(t))

def slots_le.t(+w0: DR.Lab, t: List<&2, DR.Lab>) -> {KA.natle(DC.slots(Con{w0, t}), 2n) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+w1, +t2}:
      {==}

def slots_le(ws: List<&2, DR.Lab>) -> {KA.natle(DC.slots(ws), 2n) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w0, +t}:
      slots_le.t(w0, t)

def lsc_le(+ls: List<&2, DC.Link>, +c: Nat, bs: List<&2, DR.Node>) -> {KA.natle(DC.lslack.c(ls, c, bs), DC.lslack.c(Nil{}, c, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      KA.natle_add2(DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t), 2n, DC.lslack.c(Nil{}, c, t), slots_le(DC.lstored(ls, c, b)), lsc_le(ls, c, t))

# links only take slots away
def ls_le(ids: List<&2, Nat>, +bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>) -> {KA.natle(DC.lslack(ids, bs, ls), DC.lslack(ids, bs, Nil{})) == True{} : Bool}:
  match ids:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      KA.natle_add2(DC.lslack.c(ls, c, bs), DC.lslack(t, bs, ls), DC.lslack.c(Nil{}, c, bs), DC.lslack(t, bs, Nil{}), lsc_le(ls, c, bs), ls_le(t, bs, ls))

# wfuel is past the measure of every state
def mu_w(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +s: DC.Sk) -> {KA.natle(1n+TRM.mu(DC.kmons(DC.bases(es, fs)), DC.segids(es), s), DC.wfuel(es, fs, s)) == True{} : Bool}:
  KA.natle_add2(KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.Sk.k(s)))), Nat.add(SL.rcount(DC.Sk.ms(s)), DC.lslack(DC.segids(es), TRM.bs(DC.segids(es)), DC.Sk.ls(s))),
    DC.mlen(DC.kmons(DC.bases(es, fs))), Nat.add(DC.mcount(DC.Sk.ms(s)), DC.lslack(DC.segids(es), TRM.bs(DC.segids(es)), Nil{})),
    KL.kslack_bound(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.Sk.k(s)))),
    KA.natle_add2(SL.rcount(DC.Sk.ms(s)), DC.lslack(DC.segids(es), TRM.bs(DC.segids(es)), DC.Sk.ls(s)), DC.mcount(DC.Sk.ms(s)), DC.lslack(DC.segids(es), TRM.bs(DC.segids(es)), Nil{}),
      rc_le(DC.Sk.ms(s)), ls_le(DC.segids(es), TRM.bs(DC.segids(es)), DC.Sk.ls(s))))

# The warm run
# ------------

# the fast run with its cache is the run, and the cache is right for it
def frun_fo(fuel: Nat, fo: DC.FO, +o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, h: FP.FRel(es, fs, t, fo, o))
  -> FP.FRel(es, fs, t, DC.frun.fo(fuel, fo, es, fs, t, cs, DC.oids(ids, es, cs), ids), DC.run(fuel, o, es, fs, t, cs, ids)):
  match fuel fo:
    case 0n DC.FO{+o2, +C}:
      h
    case 1n+f DC.FO{DC.OStep{+s}, +C}:
      (+eo, hc) = h
      %eo : FP.FRel(es, fs, t, DC.frun.fo(f, DC.fround(es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), es, fs, t, cs, DC.oids(ids, es, cs), ids), DC.run(1n+f, _, es, fs, t, cs, ids))
      frun_fo(f, DC.fround(es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), DC.round(es, fs, t, cs, ids, s), es, fs, t, cs, ids,
        FP.fround_ok(es, fs, t, cs, ids, s, C, (%Equal.sym(DC.Out, DC.OStep{s}, o, eo) : FP.CacheOk(es, fs, t, C, _)
          hc)))
    case 1n+f DC.FO{DC.OFix{+s}, +C}:
      (+eo, hc) = h
      %eo : FP.FRel(es, fs, t, DC.FO{DC.OFix{s}, C}, DC.run(1n+f, _, es, fs, t, cs, ids))
      ({==}, (%Equal.sym(DC.Out, DC.OFix{s}, o, eo) : FP.CacheOk(es, fs, t, C, _)
        hc))
    case 1n+f DC.FO{DC.OOne{+d}, +C}:
      (eo, hc) = h
      %eo : FP.FRel(es, fs, t, DC.FO{DC.OOne{d}, C}, DC.run(1n+f, _, es, fs, t, cs, ids))
      ({==}, Unit{})
    case 1n+f DC.FO{DC.OVoid{+sg, +dr, +di}, +C}:
      (eo, hc) = h
      %eo : FP.FRel(es, fs, t, DC.FO{DC.OVoid{sg, dr, di}, C}, DC.run(1n+f, _, es, fs, t, cs, ids))
      ({==}, Unit{})

def ti.sk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, h: TRM.TInv(es, fs, ctx, t, ids, s)) -> RD.SkInv(es, fs, ctx, t, s):
  (h1, hk) = h
  (a, b) = h1
  a

def ti.sh(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, h: TRM.TInv(es, fs, ctx, t, ids, s)) -> SH.ShInv(es, fs, OP.cspan(ctx), ids, s):
  (h1, hk) = h
  (a, b) = h1
  b

def wex.c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +hsk: RD.SkInv(es, fs, ctx, t, s), +hsh: SH.ShInv(es, fs, OP.cspan(ctx), DC.segids(es), s),
  +hi: TRM.TInv(es, fs, ctx, t, DC.segids(es), s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> CX.Ex(es, fs, ctx, t, DC.run(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, t, OP.cspan(ctx), DC.segids(es))):
  CX.ex_of(DC.run(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, t, OP.cspan(ctx), DC.segids(es)), es, fs, ctx, t,
    RD.run_ok(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, ctx, t, DC.segids(es), hsk, hz, hb),
    FX.run_fix(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, ctx, t, DC.segids(es), (hsk, hsh), hz, hb),
    TRM.run_t(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, ctx, t, DC.segids(es), (hi, mu_w(es, fs, s)), hz, hb), hz, hb)

# a run from any state with the run's invariants, with DC.wfuel, gives Ex
def warm_ex(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +hi: TRM.TInv(es, fs, ctx, t, DC.segids(es), s),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> CX.Ex(es, fs, ctx, t, DC.run(DC.wfuel(es, fs, s), DC.OStep{s}, es, fs, t, OP.cspan(ctx), DC.segids(es))):
  wex.c(es, fs, ctx, t, s, ti.sk(es, fs, ctx, t, DC.segids(es), s, hi), ti.sh(es, fs, ctx, t, DC.segids(es), s, hi), hi, hz, hb)

# the run's invariants, at a step or a fixpoint (a fixpoint is carried on)
def RunI(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      TRM.TInv(es, fs, ctx, t, ids, s)
    case DC.OFix{+s}:
      TRM.TInv(es, fs, ctx, t, ids, s)
    case DC.OOne{d}:
      Unit
    case DC.OVoid{g, dr, di}:
      Unit

def runi_of(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  h1: FX.FixOut(es, fs, ctx, t, ids, o), h2: TRM.Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, o)) -> RunI(es, fs, ctx, t, ids, o):
  match o:
    case DC.OStep{+s2}:
      (a, b) = h1
      (lt, hk) = h2
      ((a, b), hk)
    case DC.OFix{+s2}:
      (a, r1) = h1
      (b, fx) = r1
      ((a, b), h2)
    case DC.OOne{+d}:
      Unit{}
    case DC.OVoid{+g, +dr, +di}:
      Unit{}

def run_inv(fuel: Nat, o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +h: RunI(es, fs, ctx, t, ids, o),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> RunI(es, fs, ctx, t, ids, DC.run(fuel, o, es, fs, t, OP.cspan(ctx), ids)):
  match fuel o:
    case 0n o:
      h
    case 1n+f DC.OStep{+s}:
      run_inv(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids,
        runi_of(DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, s,
          FX.fix_of(DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, RD.round_ok(es, fs, ctx, t, ids, s, ti.sk(es, fs, ctx, t, ids, s, h), hz, hb),
            FX.round_sh(es, fs, ctx, t, ids, s, FX.skinv_k(es, fs, ctx, t, s, ti.sk(es, fs, ctx, t, ids, s, h)), ti.sh(es, fs, ctx, t, ids, s, h))),
          TRM.round_t(es, fs, ctx, t, ids, s, h)), hz, hb)
    case 1n+f DC.OFix{+s}:
      h
    case 1n+f DC.OOne{+d}:
      h
    case 1n+f DC.OVoid{+sg, +dr, +di}:
      h
