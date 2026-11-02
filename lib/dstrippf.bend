# bend-cad: a derivation over facts that differ only in their nd (PLAN-sk13b
# B6, for honest_unique). Proofs only.
#
# A derivation reads its premises' equations and direction statements,
# never their nd. So over two lists of facts that are the same once every
# nd is erased (fstrip), a derivation proves the same judgment (ctr) and is
# valid in one exactly when in the other (vtr). Two honest classifications
# may record different reasons for the same drop, which changes only the
# nd of its fact; this is why the later drops still agree. Mirrors
# lib/dmappf.bend's cmap and vmap, with the identity renumbering.
#
# Generated from tools/drafts/dstrippf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR


# Erasing nd
# ----------

def fsx(f: DR.Fact) -> DR.Fact:
  match f:
    case DR.Fact{e, nd, ds}:
      DR.Fact{e, Nil{}, ds}

def fstrip(fs: List<&2, DR.Fact>) -> List<&2, DR.Fact>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      Con{fsx(f), fstrip(t)}

def mstrip(m: Maybe<&2, DR.Fact>) -> Maybe<&2, DR.Fact>:
  match m:
    case Some{f}:
      Some{fsx(f)}
    case None{}:
      None{}

def fat_s(fs: List<&2, DR.Fact>, i: Nat) -> {DR.fact_at(fstrip(fs), i) == mstrip(DR.fact_at(fs, i)) : Maybe<&2, DR.Fact>}:
  match fs i:
    case Nil{} i:
      {==}
    case Con{f, t} 0n:
      {==}
    case Con{f, t} 1n+j:
      fat_s(t, j)

def fe_f(f: DR.Fact) -> {DR.fact.e(Some{fsx(f)}) == DR.fact.e(Some{f}) : E.QExpr}:
  match f:
    case DR.Fact{e, nd, ds}:
      {==}

def fe_s(m: Maybe<&2, DR.Fact>) -> {DR.fact.e(mstrip(m)) == DR.fact.e(m) : E.QExpr}:
  match m:
    case Some{f}:
      fe_f(f)
    case None{}:
      {==}

def fp_d(+e: E.QExpr, +nd: List<&2, Nat>, ds: Maybe<&2, DR.DStat>) -> {DR.fact.pj(Some{DR.Fact{e, Nil{}, ds}}) == DR.fact.pj(Some{DR.Fact{e, nd, ds}}) : DR.Jd}:
  match ds:
    case Some{DR.DStat{a, x, l}}:
      {==}
    case None{}:
      {==}

def fp_f(f: DR.Fact) -> {DR.fact.pj(Some{fsx(f)}) == DR.fact.pj(Some{f}) : DR.Jd}:
  match f:
    case DR.Fact{+e, +nd, ds}:
      fp_d(e, nd, ds)

def fp_s(m: Maybe<&2, DR.Fact>) -> {DR.fact.pj(mstrip(m)) == DR.fact.pj(m) : DR.Jd}:
  match m:
    case Some{f}:
      fp_f(f)
    case None{}:
      {==}

def hf_s(m: Maybe<&2, DR.Fact>, h: DR.HasFact(m)) -> DR.HasFact(mstrip(m)):
  match m:
    case Some{f}:
      Unit{}
    case None{}:
      h

def hf_u(m: Maybe<&2, DR.Fact>, h: DR.HasFact(mstrip(m))) -> DR.HasFact(m):
  match m:
    case Some{f}:
      Unit{}
    case None{}:
      h

def hs_d(+e: E.QExpr, +nd: List<&2, Nat>, ds: Maybe<&2, DR.DStat>, h: DR.HasStat(Some{DR.Fact{e, nd, ds}})) -> DR.HasStat(Some{DR.Fact{e, Nil{}, ds}}):
  match ds:
    case Some{DR.DStat{a, x, l}}:
      h
    case None{}:
      h

def hs_f(f: DR.Fact, h: DR.HasStat(Some{f})) -> DR.HasStat(Some{fsx(f)}):
  match f:
    case DR.Fact{+e, +nd, ds}:
      hs_d(e, nd, ds, h)

def hs_s(m: Maybe<&2, DR.Fact>, h: DR.HasStat(m)) -> DR.HasStat(mstrip(m)):
  match m:
    case Some{f}:
      hs_f(f, h)
    case None{}:
      h

def hs_du(+e: E.QExpr, +nd: List<&2, Nat>, ds: Maybe<&2, DR.DStat>, h: DR.HasStat(Some{DR.Fact{e, Nil{}, ds}})) -> DR.HasStat(Some{DR.Fact{e, nd, ds}}):
  match ds:
    case Some{DR.DStat{a, x, l}}:
      h
    case None{}:
      h

def hs_fu(f: DR.Fact, h: DR.HasStat(Some{fsx(f)})) -> DR.HasStat(Some{f}):
  match f:
    case DR.Fact{+e, +nd, ds}:
      hs_du(e, nd, ds, h)

def hs_u(m: Maybe<&2, DR.Fact>, h: DR.HasStat(mstrip(m))) -> DR.HasStat(m):
  match m:
    case Some{f}:
      hs_fu(f, h)
    case None{}:
      h

# Reading two lists that differ only in nd
# ----------------------------------------

def ms_at(+fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, +i: Nat) -> {mstrip(DR.fact_at(fs1, i)) == mstrip(DR.fact_at(fs2, i)) : Maybe<&2, DR.Fact>}:
  Equal.trans(Maybe<&2, DR.Fact>, mstrip(DR.fact_at(fs1, i)), DR.fact_at(fstrip(fs1), i), mstrip(DR.fact_at(fs2, i)), Equal.sym(Maybe<&2, DR.Fact>, DR.fact_at(fstrip(fs1), i), mstrip(DR.fact_at(fs1, i)), fat_s(fs1, i)),
    Equal.trans(Maybe<&2, DR.Fact>, DR.fact_at(fstrip(fs1), i), DR.fact_at(fstrip(fs2), i), mstrip(DR.fact_at(fs2, i)), Equal.cong(List<&2, DR.Fact>, Maybe<&2, DR.Fact>, x => DR.fact_at(x, i), fstrip(fs1), fstrip(fs2), hw), fat_s(fs2, i)))

def fe_at(+fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, +i: Nat) -> {DR.fact.e(DR.fact_at(fs1, i)) == DR.fact.e(DR.fact_at(fs2, i)) : E.QExpr}:
  Equal.trans(E.QExpr, DR.fact.e(DR.fact_at(fs1, i)), DR.fact.e(mstrip(DR.fact_at(fs1, i))), DR.fact.e(DR.fact_at(fs2, i)), Equal.sym(E.QExpr, DR.fact.e(mstrip(DR.fact_at(fs1, i))), DR.fact.e(DR.fact_at(fs1, i)), fe_s(DR.fact_at(fs1, i))),
    Equal.trans(E.QExpr, DR.fact.e(mstrip(DR.fact_at(fs1, i))), DR.fact.e(mstrip(DR.fact_at(fs2, i))), DR.fact.e(DR.fact_at(fs2, i)), Equal.cong(Maybe<&2, DR.Fact>, E.QExpr, x => DR.fact.e(x), mstrip(DR.fact_at(fs1, i)), mstrip(DR.fact_at(fs2, i)), ms_at(fs1, fs2, hw, i)), fe_s(DR.fact_at(fs2, i))))

def fp_at(+fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, +i: Nat) -> {DR.fact.pj(DR.fact_at(fs1, i)) == DR.fact.pj(DR.fact_at(fs2, i)) : DR.Jd}:
  Equal.trans(DR.Jd, DR.fact.pj(DR.fact_at(fs1, i)), DR.fact.pj(mstrip(DR.fact_at(fs1, i))), DR.fact.pj(DR.fact_at(fs2, i)), Equal.sym(DR.Jd, DR.fact.pj(mstrip(DR.fact_at(fs1, i))), DR.fact.pj(DR.fact_at(fs1, i)), fp_s(DR.fact_at(fs1, i))),
    Equal.trans(DR.Jd, DR.fact.pj(mstrip(DR.fact_at(fs1, i))), DR.fact.pj(mstrip(DR.fact_at(fs2, i))), DR.fact.pj(DR.fact_at(fs2, i)), Equal.cong(Maybe<&2, DR.Fact>, DR.Jd, x => DR.fact.pj(x), mstrip(DR.fact_at(fs1, i)), mstrip(DR.fact_at(fs2, i)), ms_at(fs1, fs2, hw, i)), fp_s(DR.fact_at(fs2, i))))

def hf_tr(+m1: Maybe<&2, DR.Fact>, +m2: Maybe<&2, DR.Fact>, +e: {mstrip(m1) == mstrip(m2) : Maybe<&2, DR.Fact>}, h: DR.HasFact(m1)) -> DR.HasFact(m2):
  hf_u(m2, (%e : DR.HasFact(_)
    hf_s(m1, h)))

def hs_tr(+m1: Maybe<&2, DR.Fact>, +m2: Maybe<&2, DR.Fact>, +e: {mstrip(m1) == mstrip(m2) : Maybe<&2, DR.Fact>}, h: DR.HasStat(m1)) -> DR.HasStat(m2):
  hs_u(m2, (%e : DR.HasStat(_)
    hs_s(m1, h)))

# Conclusions
# -----------

# the same judgment
def ctr(d: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}) -> {DR.concl(es, fs1, d) == DR.concl(es, fs2, d) : DR.Jd}:
  match d:
    case DR.DZero{}:
      {==}
    case DR.DPrem{+i}:
      %fe_at(fs1, fs2, hw, i) : {DR.JK{DR.fact.e(DR.fact_at(fs1, i))} == DR.JK{_} : DR.Jd}
      {==}
    case DR.DKAdd{+l, +d1, +d2}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, fs1, d1))}, DR.Jd.e(DR.concl(es, fs1, d2))}} == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(_)}, DR.Jd.e(DR.concl(es, fs2, d2))}} : DR.Jd}
      %ctr(d2, es, fs1, fs2, hw) : {DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, fs1, d1))}, DR.Jd.e(DR.concl(es, fs1, d2))}} == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, fs1, d1))}, DR.Jd.e(_)}} : DR.Jd}
      {==}
    case DR.DBack{+d1}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JK{SK.VE.y(DR.Jd.x(DR.concl(es, fs1, d1)))} == DR.JK{SK.VE.y(DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DLine{+d1, +d2, +re}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JK{DR.dline.e(re, DR.Jd.x(DR.concl(es, fs1, d1)))} == DR.JK{DR.dline.e(re, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DPPrem{+i}:
      fp_at(fs1, fs2, hw, i)
    case DR.DSelf{+a}:
      {==}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.vlin(m1, DR.Jd.x(DR.concl(es, fs1, d1)), m2, DR.Jd.x(DR.concl(es, fs1, d2)))} == DR.JP{DR.Jd.a(_), DR.vlin(m1, DR.Jd.x(_), m2, DR.Jd.x(DR.concl(es, fs2, d2)))} : DR.Jd}
      %ctr(d2, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.vlin(m1, DR.Jd.x(DR.concl(es, fs1, d1)), m2, DR.Jd.x(DR.concl(es, fs1, d2)))} == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.vlin(m1, DR.Jd.x(DR.concl(es, fs1, d1)), m2, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DKnown{+d1, +dr, +di}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d1)), SK.VE{DR.Jd.e(DR.concl(es, fs1, dr)), DR.Jd.e(DR.concl(es, fs1, di))})} == DR.JP{DR.Jd.a(_), SK.VE.add(DR.Jd.x(_), SK.VE{DR.Jd.e(DR.concl(es, fs2, dr)), DR.Jd.e(DR.concl(es, fs2, di))})} : DR.Jd}
      %ctr(dr, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d1)), SK.VE{DR.Jd.e(DR.concl(es, fs1, dr)), DR.Jd.e(DR.concl(es, fs1, di))})} == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d1)), SK.VE{DR.Jd.e(_), DR.Jd.e(DR.concl(es, fs2, di))})} : DR.Jd}
      %ctr(di, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d1)), SK.VE{DR.Jd.e(DR.concl(es, fs1, dr)), DR.Jd.e(DR.concl(es, fs1, di))})} == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d1)), SK.VE{DR.Jd.e(DR.concl(es, fs1, dr)), DR.Jd.e(_)})} : DR.Jd}
      {==}
    case DR.DTurn{+d1, +g, +b}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JP{b, DR.gmul(g, DR.zdir(es, DR.Jd.a(DR.concl(es, fs1, d1))))} == DR.JP{b, DR.gmul(g, DR.zdir(es, DR.Jd.a(_)))} : DR.Jd}
      {==}
    case DR.DThrough{+d1, +d2, +g, +b}:
      %ctr(d1, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, fs1, d2)))} == DR.JP{DR.Jd.a(_), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, fs2, d2)))} : DR.Jd}
      %ctr(d2, es, fs1, fs2, hw) : {DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, fs1, d2)))} == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.gmul(DR.Lab.conj(g), DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DFrame{+d1, +x}:
      {==}
    case DR.DVoid{+dr, +di, +a, +x}:
      {==}

# Validity
# --------

def ik(+d: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, h: DR.IsK(DR.concl(es, fs1, d))) -> DR.IsK(DR.concl(es, fs2, d)):
  (%ctr(d, es, fs1, fs2, hw) : DR.IsK(_) h)

def ip(+d: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, h: DR.IsP(DR.concl(es, fs1, d))) -> DR.IsP(DR.concl(es, fs2, d)):
  (%ctr(d, es, fs1, fs2, hw) : DR.IsP(_) h)

def aeq(+d1: DR.Der, +d2: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, h: {DR.Jd.a(DR.concl(es, fs1, d1)) == DR.Jd.a(DR.concl(es, fs1, d2)) : DR.Node}) -> {DR.Jd.a(DR.concl(es, fs2, d1)) == DR.Jd.a(DR.concl(es, fs2, d2)) : DR.Node}:
  %ctr(d1, es, fs1, fs2, hw) : {DR.Jd.a(_) == DR.Jd.a(DR.concl(es, fs2, d2)) : DR.Node}
  %ctr(d2, es, fs1, fs2, hw) : {DR.Jd.a(DR.concl(es, fs1, d1)) == DR.Jd.a(_) : DR.Node}
  h

def svline(+d1: DR.Der, +d2: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, h: DR.SameV(DR.Jd.x(DR.concl(es, fs1, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs1, d1))))) -> DR.SameV(DR.Jd.x(DR.concl(es, fs2, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs2, d1)))):
  %ctr(d1, es, fs1, fs2, hw) : DR.SameV(DR.Jd.x(DR.concl(es, fs2, d2)), DR.imul(DR.Jd.x(_)))
  %ctr(d2, es, fs1, fs2, hw) : DR.SameV(DR.Jd.x(_), DR.imul(DR.Jd.x(DR.concl(es, fs1, d1))))
  h

# a valid derivation stays valid over facts that differ only in nd
def vtr(d: DR.Der, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, hv: DR.Valid(es, fs1, ctx, d)) -> DR.Valid(es, fs2, ctx, d):
  match d:
    case DR.DZero{}:
      hv
    case DR.DPrem{+i}:
      hf_tr(DR.fact_at(fs1, i), DR.fact_at(fs2, i), ms_at(fs1, fs2, hw, i), hv)
    case DR.DKAdd{+l, +d1, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (k1, k2) = r2
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (vtr(d2, es, ctx, fs1, fs2, hw, v2), (ik(d1, es, fs1, fs2, hw, k1), ik(d2, es, fs1, fs2, hw, k2))))
    case DR.DBack{+d1}:
      (v1, r1) = hv
      (p1, e1) = r1
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (ip(d1, es, fs1, fs2, hw, p1), (%ctr(d1, es, fs1, fs2, hw) : {DR.Jd.a(_) == DR.NFrame{} : DR.Node} e1)))
    case DR.DLine{+d1, +d2, +re}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (ea, r5) = r4
      (op, sv) = r5
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (vtr(d2, es, ctx, fs1, fs2, hw, v2), (ip(d1, es, fs1, fs2, hw, p1), (ip(d2, es, fs1, fs2, hw, p2),
        (aeq(d1, d2, es, fs1, fs2, hw, ea),
         ((%ctr(d1, es, fs1, fs2, hw) : DR.Open(es, ctx, DR.Jd.a(_)) op),
          svline(d1, d2, es, fs1, fs2, hw, sv)))))))
    case DR.DPPrem{+i}:
      hs_tr(DR.fact_at(fs1, i), DR.fact_at(fs2, i), ms_at(fs1, fs2, hw, i), hv)
    case DR.DSelf{+a}:
      hv
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, ea) = r3
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (vtr(d2, es, ctx, fs1, fs2, hw, v2), (ip(d1, es, fs1, fs2, hw, p1), (ip(d2, es, fs1, fs2, hw, p2),
        aeq(d1, d2, es, fs1, fs2, hw, ea)))))
    case DR.DKnown{+d1, +dr, +di}:
      (v1, r1) = hv
      (vr, r2) = r1
      (vi, r3) = r2
      (p1, r4) = r3
      (kr, ki) = r4
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (vtr(dr, es, ctx, fs1, fs2, hw, vr), (vtr(di, es, ctx, fs1, fs2, hw, vi), (ip(d1, es, fs1, fs2, hw, p1), (ik(dr, es, fs1, fs2, hw, kr), ik(di, es, fs1, fs2, hw, ki))))))
    case DR.DTurn{+d1, +g, +b}:
      (v1, r1) = hv
      (p1, sv) = r1
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (ip(d1, es, fs1, fs2, hw, p1), (%ctr(d1, es, fs1, fs2, hw) : DR.SameV(DR.Jd.x(_), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))) sv)))
    case DR.DThrough{+d1, +d2, +g, +b}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (sv, r5) = r4
      (eb, op) = r5
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (vtr(d2, es, ctx, fs1, fs2, hw, v2), (ip(d1, es, fs1, fs2, hw, p1), (ip(d2, es, fs1, fs2, hw, p2),
        ((%ctr(d1, es, fs1, fs2, hw) : DR.SameV(DR.Jd.x(_), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))) sv),
         ((%ctr(d2, es, fs1, fs2, hw) : {DR.Jd.a(_) == b : DR.Node} eb), op))))))
    case DR.DFrame{+d1, +x}:
      (v1, r1) = hv
      (k1, sm) = r1
      (vtr(d1, es, ctx, fs1, fs2, hw, v1), (ik(d1, es, fs1, fs2, hw, k1), (%ctr(d1, es, fs1, fs2, hw) : DR.Same(DR.Jd.e(_), SK.VE.y(x)) sm)))
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r1) = hv
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      (vtr(dr, es, ctx, fs1, fs2, hw, vr), (vtr(di, es, ctx, fs1, fs2, hw, vi), (ik(dr, es, fs1, fs2, hw, kr), (ik(di, es, fs1, fs2, hw, ki),
        ((%ctr(dr, es, fs1, fs2, hw) : DR.Same(DR.Jd.e(_), SK.VE.x(DR.zdir(es, a))) sr), (%ctr(di, es, fs1, fs2, hw) : DR.Same(DR.Jd.e(_), SK.VE.y(DR.zdir(es, a))) si))))))

# what a derivation proves, over the other list
def pr_tr(+d: DR.Der, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +hw: {fstrip(fs1) == fstrip(fs2) : List<&2, DR.Fact>}, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, hp: SV.Proves(es, m, e, DR.concl(es, fs1, d))) -> SV.Proves(es, m, e, DR.concl(es, fs2, d)):
  (%ctr(d, es, fs1, fs2, hw) : SV.Proves(es, m, e, _)
    hp)
