# bend-cad: moving a derivation to more facts (PLAN-sk13b B4.1). Premises
# are named by their position in the list of facts, so a derivation over
# the facts of some constraints is renumbered (dmap) to read the same
# facts in the list of more constraints, given the shorter list as a
# sublist of the longer (SubF). Its conclusion and nd stay the same, and it
# stays valid; so does a refutation, a Motzkin refutation's side
# multipliers padded with 0s for the sides added (spad). So c has with
# more constraints every direction refutation it has with fewer
# (nodir_mono): the deletion filter's monotonicity. Proofs only.
#
# Generated from tools/drafts/dmappf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./lexpf.bend as LX
import ./karith.bend as KA
import ./listpf.bend as LI
import ./q.bend as LQ
import ./qring.bend as QR
import ./conflictpf.bend as CP


def absurd(-A: Type, x: Empty) -> A:
  match x:

# Facts as a sublist
# ------------------

# xs is ys with some entries left out, in order
def SubF(xs: List<&2, DR.Fact>, ys: List<&2, DR.Fact>) -> Data:
  match xs ys:
    case Nil{} ys:
      Unit
    case Con{x, xt} Nil{}:
      Empty
    case Con{+x, +xt} Con{y, yt}:
      Either<&2, &2, M.Both({x == y : DR.Fact}, SubF(xt, yt)), SubF(Con{x, xt}, yt)>

def flen(xs: List<&2, DR.Fact>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+flen(t)

# where entry i of xs is in ys (past ys's end when xs has no entry i)
def ix(ys: List<&2, DR.Fact>, xs: List<&2, DR.Fact>, w: SubF(xs, ys), i: Nat) -> Nat:
  match ys xs:
    case Nil{} Nil{}:
      i
    case Nil{} Con{x, xt}:
      absurd(Nat, w)
    case Con{+y, +yt} Nil{}:
      Nat.add(flen(Con{y, yt}), i)
    case Con{y, yt} Con{+x, +xt}:
      match w:
        case Inl{p}:
          match i:
            case 0n:
              0n
            case 1n+j:
              1n+ix(yt, xt, LX.both_r({x == y : DR.Fact}, SubF(xt, yt), p), j)
        case Inr{q}:
          1n+ix(yt, Con{x, xt}, q, i)

def fat_past(ys: List<&2, DR.Fact>, +i: Nat) -> {DR.fact_at(ys, Nat.add(flen(ys), i)) == None{} : Maybe<&2, DR.Fact>}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, t}:
      fat_past(t, i)

# the entry at i of xs is the entry at ix of ys
def fat_ix(ys: List<&2, DR.Fact>, xs: List<&2, DR.Fact>, w: SubF(xs, ys), i: Nat) -> {DR.fact_at(ys, ix(ys, xs, w, i)) == DR.fact_at(xs, i) : Maybe<&2, DR.Fact>}:
  match ys xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+x, +xt}:
      absurd({DR.fact_at(Nil{}, ix(Nil{}, Con{x, xt}, w, i)) == DR.fact_at(Con{x, xt}, i) : Maybe<&2, DR.Fact>}, w)
    case Con{+y, +yt} Nil{}:
      fat_past(Con{y, yt}, i)
    case Con{+y, +yt} Con{+x, +xt}:
      match w:
        case Inl{+p}:
          match i:
            case 0n:
              %LX.both_l({x == y : DR.Fact}, SubF(xt, yt), p) : {Some{_} == Some{x} : Maybe<&2, DR.Fact>}
              {==}
            case 1n+j:
              fat_ix(yt, xt, LX.both_r({x == y : DR.Fact}, SubF(xt, yt), p), j)
        case Inr{q}:
          fat_ix(yt, Con{x, xt}, q, i)

# Renumbering
# -----------

def dmap(d: DR.Der, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> DR.Der:
  match d:
    case DR.DZero{}:
      DR.DZero{}
    case DR.DPrem{i}:
      DR.DPrem{ix(ys, xs, w, i)}
    case DR.DKAdd{l, d1, d2}:
      DR.DKAdd{l, dmap(d1, ys, xs, w), dmap(d2, ys, xs, w)}
    case DR.DBack{d1}:
      DR.DBack{dmap(d1, ys, xs, w)}
    case DR.DLine{d1, d2, re}:
      DR.DLine{dmap(d1, ys, xs, w), dmap(d2, ys, xs, w), re}
    case DR.DPPrem{i}:
      DR.DPPrem{ix(ys, xs, w, i)}
    case DR.DSelf{a}:
      DR.DSelf{a}
    case DR.DPLin{m1, d1, m2, d2}:
      DR.DPLin{m1, dmap(d1, ys, xs, w), m2, dmap(d2, ys, xs, w)}
    case DR.DKnown{d1, dr, di}:
      DR.DKnown{dmap(d1, ys, xs, w), dmap(dr, ys, xs, w), dmap(di, ys, xs, w)}
    case DR.DTurn{d1, g, b}:
      DR.DTurn{dmap(d1, ys, xs, w), g, b}
    case DR.DThrough{d1, d2, g, b}:
      DR.DThrough{dmap(d1, ys, xs, w), dmap(d2, ys, xs, w), g, b}
    case DR.DFrame{d1, x}:
      DR.DFrame{dmap(d1, ys, xs, w), x}
    case DR.DVoid{dr, di, a, x}:
      DR.DVoid{dmap(dr, ys, xs, w), dmap(di, ys, xs, w), a, x}

# the same conclusion
def cmap(d: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> {DR.concl(es, ys, dmap(d, ys, xs, w)) == DR.concl(es, xs, d) : DR.Jd}:
  match d:
    case DR.DZero{}:
      {==}
    case DR.DPrem{+i}:
      %fat_ix(ys, xs, w, i) : {DR.JK{DR.fact.e(DR.fact_at(ys, ix(ys, xs, w, i)))} == DR.JK{DR.fact.e(_)} : DR.Jd}
      {==}
    case DR.DKAdd{+l, +d1, +d2}:
      %cmap(d1, es, ys, xs, w) : {DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, ys, dmap(d1, ys, xs, w)))}, DR.Jd.e(DR.concl(es, ys, dmap(d2, ys, xs, w)))}} == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(_)}, DR.Jd.e(DR.concl(es, xs, d2))}} : DR.Jd}
      %cmap(d2, es, ys, xs, w) : {DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, ys, dmap(d1, ys, xs, w)))}, DR.Jd.e(DR.concl(es, ys, dmap(d2, ys, xs, w)))}} == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, ys, dmap(d1, ys, xs, w)))}, DR.Jd.e(_)}} : DR.Jd}
      {==}
    case DR.DBack{+d1}:
      %cmap(d1, es, ys, xs, w) : {DR.JK{SK.VE.y(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))))} == DR.JK{SK.VE.y(DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DLine{+d1, +d2, +re}:
      %cmap(d1, es, ys, xs, w) : {DR.JK{DR.dline.e(re, DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))))} == DR.JK{DR.dline.e(re, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DPPrem{+i}:
      %fat_ix(ys, xs, w, i) : {DR.fact.pj(DR.fact_at(ys, ix(ys, xs, w, i))) == DR.fact.pj(_) : DR.Jd}
      {==}
    case DR.DSelf{+a}:
      {==}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      %cmap(d1, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.vlin(m1, DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), m2, DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))))} == DR.JP{DR.Jd.a(_), DR.vlin(m1, DR.Jd.x(_), m2, DR.Jd.x(DR.concl(es, xs, d2)))} : DR.Jd}
      %cmap(d2, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.vlin(m1, DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), m2, DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))))} == DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.vlin(m1, DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), m2, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DKnown{+d1, +dr, +di}:
      %cmap(d1, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE.add(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE{DR.Jd.e(DR.concl(es, ys, dmap(dr, ys, xs, w))), DR.Jd.e(DR.concl(es, ys, dmap(di, ys, xs, w)))})} == DR.JP{DR.Jd.a(_), SK.VE.add(DR.Jd.x(_), SK.VE{DR.Jd.e(DR.concl(es, xs, dr)), DR.Jd.e(DR.concl(es, xs, di))})} : DR.Jd}
      %cmap(dr, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE.add(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE{DR.Jd.e(DR.concl(es, ys, dmap(dr, ys, xs, w))), DR.Jd.e(DR.concl(es, ys, dmap(di, ys, xs, w)))})} == DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE.add(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE{DR.Jd.e(_), DR.Jd.e(DR.concl(es, xs, di))})} : DR.Jd}
      %cmap(di, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE.add(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE{DR.Jd.e(DR.concl(es, ys, dmap(dr, ys, xs, w))), DR.Jd.e(DR.concl(es, ys, dmap(di, ys, xs, w)))})} == DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE.add(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))), SK.VE{DR.Jd.e(DR.concl(es, ys, dmap(dr, ys, xs, w))), DR.Jd.e(_)})} : DR.Jd}
      {==}
    case DR.DTurn{+d1, +g, +b}:
      %cmap(d1, es, ys, xs, w) : {DR.JP{b, DR.gmul(g, DR.zdir(es, DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))))} == DR.JP{b, DR.gmul(g, DR.zdir(es, DR.Jd.a(_)))} : DR.Jd}
      {==}
    case DR.DThrough{+d1, +d2, +g, +b}:
      %cmap(d1, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))))} == DR.JP{DR.Jd.a(_), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, xs, d2)))} : DR.Jd}
      %cmap(d2, es, ys, xs, w) : {DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))))} == DR.JP{DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))), DR.gmul(DR.Lab.conj(g), DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DFrame{+d1, +x}:
      {==}
    case DR.DVoid{+dr, +di, +a, +x}:
      {==}

# the same nd
def nmap(d: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> {DR.nd(es, ys, dmap(d, ys, xs, w)) == DR.nd(es, xs, d) : List<&2, Nat>}:
  match d:
    case DR.DZero{}:
      {==}
    case DR.DPrem{+i}:
      %fat_ix(ys, xs, w, i) : {DR.fact.nd(DR.fact_at(ys, ix(ys, xs, w, i))) == DR.fact.nd(_) : List<&2, Nat>}
      {==}
    case DR.DKAdd{+l, +d1, +d2}:
      %nmap(d1, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w))) == DR.ncat(_, DR.nd(es, xs, d2)) : List<&2, Nat>}
      %nmap(d2, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w))) == DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), _) : List<&2, Nat>}
      {==}
    case DR.DBack{+d1}:
      nmap(d1, es, ys, xs, w)
    case DR.DLine{+d1, +d2, +re}:
      %cmap(d1, es, ys, xs, w) : {DR.ncat(DR.Node.segs(DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w)))) == DR.ncat(DR.Node.segs(DR.Jd.a(_)), DR.ncat(DR.nd(es, xs, d1), DR.nd(es, xs, d2))) : List<&2, Nat>}
      %nmap(d1, es, ys, xs, w) : {DR.ncat(DR.Node.segs(DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w)))) == DR.ncat(DR.Node.segs(DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))), DR.ncat(_, DR.nd(es, xs, d2))) : List<&2, Nat>}
      %nmap(d2, es, ys, xs, w) : {DR.ncat(DR.Node.segs(DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w)))) == DR.ncat(DR.Node.segs(DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w)))), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), _)) : List<&2, Nat>}
      {==}
    case DR.DPPrem{+i}:
      %fat_ix(ys, xs, w, i) : {DR.fact.nd(DR.fact_at(ys, ix(ys, xs, w, i))) == DR.fact.nd(_) : List<&2, Nat>}
      {==}
    case DR.DSelf{+a}:
      {==}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      %nmap(d1, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w))) == DR.ncat(_, DR.nd(es, xs, d2)) : List<&2, Nat>}
      %nmap(d2, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w))) == DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), _) : List<&2, Nat>}
      {==}
    case DR.DKnown{+d1, +dr, +di}:
      %nmap(d1, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), DR.nd(es, ys, dmap(di, ys, xs, w)))) == DR.ncat(_, DR.ncat(DR.nd(es, xs, dr), DR.nd(es, xs, di))) : List<&2, Nat>}
      %nmap(dr, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), DR.nd(es, ys, dmap(di, ys, xs, w)))) == DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.ncat(_, DR.nd(es, xs, di))) : List<&2, Nat>}
      %nmap(di, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), DR.nd(es, ys, dmap(di, ys, xs, w)))) == DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), _)) : List<&2, Nat>}
      {==}
    case DR.DTurn{+d1, +g, +b}:
      nmap(d1, es, ys, xs, w)
    case DR.DThrough{+d1, +d2, +g, +b}:
      %nmap(d1, es, ys, xs, w) : {DR.ncat(DR.Node.segs(b), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w)))) == DR.ncat(DR.Node.segs(b), DR.ncat(_, DR.nd(es, xs, d2))) : List<&2, Nat>}
      %nmap(d2, es, ys, xs, w) : {DR.ncat(DR.Node.segs(b), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), DR.nd(es, ys, dmap(d2, ys, xs, w)))) == DR.ncat(DR.Node.segs(b), DR.ncat(DR.nd(es, ys, dmap(d1, ys, xs, w)), _)) : List<&2, Nat>}
      {==}
    case DR.DFrame{+d1, +x}:
      nmap(d1, es, ys, xs, w)
    case DR.DVoid{+dr, +di, +a, +x}:
      %nmap(dr, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), DR.nd(es, ys, dmap(di, ys, xs, w))) == DR.ncat(_, DR.nd(es, xs, di)) : List<&2, Nat>}
      %nmap(di, es, ys, xs, w) : {DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), DR.nd(es, ys, dmap(di, ys, xs, w))) == DR.ncat(DR.nd(es, ys, dmap(dr, ys, xs, w)), _) : List<&2, Nat>}
      {==}

# Validity
# --------

# d's conclusion read in xs, as the renumbered one read in ys
def cm.s(+d: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> {DR.concl(es, xs, d) == DR.concl(es, ys, dmap(d, ys, xs, w)) : DR.Jd}:
  Equal.sym(DR.Jd, DR.concl(es, ys, dmap(d, ys, xs, w)), DR.concl(es, xs, d), cmap(d, es, ys, xs, w))

def ik(+d: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: DR.IsK(DR.concl(es, xs, d))) -> DR.IsK(DR.concl(es, ys, dmap(d, ys, xs, w))):
  (%cm.s(d, es, ys, xs, w) : DR.IsK(_) h)

def ip(+d: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: DR.IsP(DR.concl(es, xs, d))) -> DR.IsP(DR.concl(es, ys, dmap(d, ys, xs, w))):
  (%cm.s(d, es, ys, xs, w) : DR.IsP(_) h)

def aeq(+d1: DR.Der, +d2: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: {DR.Jd.a(DR.concl(es, xs, d1)) == DR.Jd.a(DR.concl(es, xs, d2)) : DR.Node}) -> {DR.Jd.a(DR.concl(es, ys, dmap(d1, ys, xs, w))) == DR.Jd.a(DR.concl(es, ys, dmap(d2, ys, xs, w))) : DR.Node}:
  %cm.s(d1, es, ys, xs, w) : {DR.Jd.a(_) == DR.Jd.a(DR.concl(es, ys, dmap(d2, ys, xs, w))) : DR.Node}
  %cm.s(d2, es, ys, xs, w) : {DR.Jd.a(DR.concl(es, xs, d1)) == DR.Jd.a(_) : DR.Node}
  h

def svline(+d1: DR.Der, +d2: DR.Der, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: DR.SameV(DR.Jd.x(DR.concl(es, xs, d2)), DR.imul(DR.Jd.x(DR.concl(es, xs, d1))))) -> DR.SameV(DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))), DR.imul(DR.Jd.x(DR.concl(es, ys, dmap(d1, ys, xs, w))))):
  %cm.s(d1, es, ys, xs, w) : DR.SameV(DR.Jd.x(DR.concl(es, ys, dmap(d2, ys, xs, w))), DR.imul(DR.Jd.x(_)))
  %cm.s(d2, es, ys, xs, w) : DR.SameV(DR.Jd.x(_), DR.imul(DR.Jd.x(DR.concl(es, xs, d1))))
  h

# a valid derivation stays valid
def vmap(d: DR.Der, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), hv: DR.Valid(es, xs, ctx, d)) -> DR.Valid(es, ys, ctx, dmap(d, ys, xs, w)):
  match d:
    case DR.DZero{}:
      hv
    case DR.DPrem{+i}:
      (%Equal.sym(Maybe<&2, DR.Fact>, DR.fact_at(ys, ix(ys, xs, w, i)), DR.fact_at(xs, i), fat_ix(ys, xs, w, i)) : DR.HasFact(_) hv)
    case DR.DKAdd{+l, +d1, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (k1, k2) = r2
      (vmap(d1, es, ctx, ys, xs, w, v1), (vmap(d2, es, ctx, ys, xs, w, v2), (ik(d1, es, ys, xs, w, k1), ik(d2, es, ys, xs, w, k2))))
    case DR.DBack{+d1}:
      (v1, r1) = hv
      (p1, e1) = r1
      (vmap(d1, es, ctx, ys, xs, w, v1), (ip(d1, es, ys, xs, w, p1), (%cm.s(d1, es, ys, xs, w) : {DR.Jd.a(_) == DR.NFrame{} : DR.Node} e1)))
    case DR.DLine{+d1, +d2, +re}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (ea, r5) = r4
      (op, sv) = r5
      (vmap(d1, es, ctx, ys, xs, w, v1), (vmap(d2, es, ctx, ys, xs, w, v2), (ip(d1, es, ys, xs, w, p1), (ip(d2, es, ys, xs, w, p2),
        (aeq(d1, d2, es, ys, xs, w, ea),
         ((%cm.s(d1, es, ys, xs, w) : DR.Open(es, ctx, DR.Jd.a(_)) op),
          svline(d1, d2, es, ys, xs, w, sv)))))))
    case DR.DPPrem{+i}:
      (%Equal.sym(Maybe<&2, DR.Fact>, DR.fact_at(ys, ix(ys, xs, w, i)), DR.fact_at(xs, i), fat_ix(ys, xs, w, i)) : DR.HasStat(_) hv)
    case DR.DSelf{+a}:
      hv
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, ea) = r3
      (vmap(d1, es, ctx, ys, xs, w, v1), (vmap(d2, es, ctx, ys, xs, w, v2), (ip(d1, es, ys, xs, w, p1), (ip(d2, es, ys, xs, w, p2),
        aeq(d1, d2, es, ys, xs, w, ea)))))
    case DR.DKnown{+d1, +dr, +di}:
      (v1, r1) = hv
      (vr, r2) = r1
      (vi, r3) = r2
      (p1, r4) = r3
      (kr, ki) = r4
      (vmap(d1, es, ctx, ys, xs, w, v1), (vmap(dr, es, ctx, ys, xs, w, vr), (vmap(di, es, ctx, ys, xs, w, vi), (ip(d1, es, ys, xs, w, p1), (ik(dr, es, ys, xs, w, kr), ik(di, es, ys, xs, w, ki))))))
    case DR.DTurn{+d1, +g, +b}:
      (v1, r1) = hv
      (p1, sv) = r1
      (vmap(d1, es, ctx, ys, xs, w, v1), (ip(d1, es, ys, xs, w, p1), (%cm.s(d1, es, ys, xs, w) : DR.SameV(DR.Jd.x(_), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))) sv)))
    case DR.DThrough{+d1, +d2, +g, +b}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (sv, r5) = r4
      (eb, op) = r5
      (vmap(d1, es, ctx, ys, xs, w, v1), (vmap(d2, es, ctx, ys, xs, w, v2), (ip(d1, es, ys, xs, w, p1), (ip(d2, es, ys, xs, w, p2),
        ((%cm.s(d1, es, ys, xs, w) : DR.SameV(DR.Jd.x(_), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))) sv),
         ((%cm.s(d2, es, ys, xs, w) : {DR.Jd.a(_) == b : DR.Node} eb), op))))))
    case DR.DFrame{+d1, +x}:
      (v1, r1) = hv
      (k1, sm) = r1
      (vmap(d1, es, ctx, ys, xs, w, v1), (ik(d1, es, ys, xs, w, k1), (%cm.s(d1, es, ys, xs, w) : DR.Same(DR.Jd.e(_), SK.VE.y(x)) sm)))
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r1) = hv
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      (vmap(dr, es, ctx, ys, xs, w, vr), (vmap(di, es, ctx, ys, xs, w, vi), (ik(dr, es, ys, xs, w, kr), (ik(di, es, ys, xs, w, ki),
        ((%cm.s(dr, es, ys, xs, w) : DR.Same(DR.Jd.e(_), SK.VE.x(DR.zdir(es, a))) sr), (%cm.s(di, es, ys, xs, w) : DR.Same(DR.Jd.e(_), SK.VE.y(DR.zdir(es, a))) si))))))

# Lists of derivations
# --------------------

def dmaps(ds: List<&2, DR.Der>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> List<&2, DR.Der>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{dmap(d, ys, xs, w), dmaps(t, ys, xs, w)}

def dcmap(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys)) -> {DR.dconcls(es, ys, dmaps(ds, ys, xs, w)) == DR.dconcls(es, xs, ds) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %cmap(d, es, ys, xs, w) : {Con{DR.Jd.e(DR.concl(es, ys, dmap(d, ys, xs, w))), DR.dconcls(es, ys, dmaps(t, ys, xs, w))} == Con{DR.Jd.e(_), DR.dconcls(es, xs, t)} : List<&2, E.QExpr>}
      %dcmap(t, es, ys, xs, w) : {Con{DR.Jd.e(DR.concl(es, ys, dmap(d, ys, xs, w))), DR.dconcls(es, ys, dmaps(t, ys, xs, w))} == Con{DR.Jd.e(DR.concl(es, ys, dmap(d, ys, xs, w))), _} : List<&2, E.QExpr>}
      {==}

def avmap(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: DR.AllValidK(es, xs, ctx, ds)) -> DR.AllValidK(es, ys, ctx, dmaps(ds, ys, xs, w)):
  match ds:
    case Nil{}:
      h
    case Con{+d, +t}:
      (v, r) = h
      (k, rt) = r
      (vmap(d, es, ctx, ys, xs, w, v), (ik(d, es, ys, xs, w, k), avmap(t, es, ctx, ys, xs, w, rt)))

# Side multipliers, padded
# ------------------------

def qhd(ms: List<&2, S.Q>) -> S.Q:
  match ms:
    case Nil{}:
      SV.qzero()
    case Con{m, t}:
      m

def qtl(ms: List<&2, S.Q>) -> List<&2, S.Q>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      t

# ms, for the sides xs, with 0 for each side of ys left out of xs
def spad(ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, w: CP.SubS(xs, ys), +ms: List<&2, S.Q>) -> List<&2, S.Q>:
  match ys xs:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{x, xt}:
      absurd(List<&2, S.Q>, w)
    case Con{y, yt} Nil{}:
      Con{SV.qzero(), spad(yt, Nil{}, Unit{}, ms)}
    case Con{y, yt} Con{+x, +xt}:
      match w:
        case Inl{p}:
          Con{qhd(ms), spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms))}
        case Inr{q}:
          Con{SV.qzero(), spad(yt, Con{x, xt}, q, ms)}

def spad_len(ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, w: CP.SubS(xs, ys), +ms: List<&2, S.Q>) -> {SV.qlen(spad(ys, xs, w, ms)) == SV.slen(ys) : Nat}:
  match ys xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+x, +xt}:
      absurd({SV.qlen(spad(Nil{}, Con{x, xt}, w, ms)) == SV.slen(Nil{}) : Nat}, w)
    case Con{+y, +yt} Nil{}:
      %spad_len(yt, Nil{}, Unit{}, ms) : {1n+SV.qlen(spad(yt, Nil{}, Unit{}, ms)) == 1n+_ : Nat}
      {==}
    case Con{+y, +yt} Con{+x, +xt}:
      match w:
        case Inl{+p}:
          %spad_len(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms)) : {1n+SV.qlen(spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms))) == 1n+_ : Nat}
          {==}
        case Inr{q}:
          %spad_len(yt, Con{x, xt}, q, ms) : {1n+SV.qlen(spad(yt, Con{x, xt}, q, ms)) == 1n+_ : Nat}
          {==}

def nn_hd(ms: List<&2, S.Q>, h: {SV.nonneg(ms) == True{} : Bool}) -> {SV.bnot(SV.islt(S.Q.cmp(qhd(ms), SV.qzero()))) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      LI.band_l(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(t), h)

def nn_tl(ms: List<&2, S.Q>, h: {SV.nonneg(ms) == True{} : Bool}) -> {SV.nonneg(qtl(ms)) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      LI.band_r(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(t), h)

def spad_nn(ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, w: CP.SubS(xs, ys), +ms: List<&2, S.Q>, +h: {SV.nonneg(ms) == True{} : Bool}) -> {SV.nonneg(spad(ys, xs, w, ms)) == True{} : Bool}:
  match ys xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+x, +xt}:
      absurd({SV.nonneg(spad(Nil{}, Con{x, xt}, w, ms)) == True{} : Bool}, w)
    case Con{+y, +yt} Nil{}:
      spad_nn(yt, Nil{}, Unit{}, ms, h)
    case Con{+y, +yt} Con{+x, +xt}:
      match w:
        case Inl{+p}:
          LI.band_i(SV.bnot(SV.islt(S.Q.cmp(qhd(ms), SV.qzero()))), SV.nonneg(spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms))), nn_hd(ms, h),
            spad_nn(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms), nn_tl(ms, h)))
        case Inr{q}:
          spad_nn(yt, Con{x, xt}, q, ms, h)

# a 0 multiplier adds nothing to strict_pos
def spos.z(y: SK.Side, +yt: List<&2, SK.Side>, +R: List<&2, S.Q>, +b: Bool, ih: {SV.strict_pos(R, yt) == b : Bool}) -> {SV.strict_pos(Con{SV.qzero(), R}, Con{y, yt}) == b : Bool}:
  match y:
    case SK.Gt0{+e}:
      ih
    case SK.Ge0{+e}:
      ih

def spos.h(y: SK.Side, ms: List<&2, S.Q>, +yt: List<&2, SK.Side>, +xt: List<&2, SK.Side>, +R: List<&2, S.Q>, ih: {SV.strict_pos(R, yt) == SV.strict_pos(qtl(ms), xt) : Bool}) -> {SV.strict_pos(Con{qhd(ms), R}, Con{y, yt}) == SV.strict_pos(ms, Con{y, xt}) : Bool}:
  match y ms:
    case SK.Gt0{+e} Con{+m, +mt}:
      %ih : {SV.bor(SV.islt(S.Q.cmp(SV.qzero(), m)), SV.strict_pos(R, yt)) == SV.bor(SV.islt(S.Q.cmp(SV.qzero(), m)), _) : Bool}
      {==}
    case SK.Gt0{+e} Nil{}:
      ih
    case SK.Ge0{+e} Con{+m, +mt}:
      ih
    case SK.Ge0{+e} Nil{}:
      ih

def spos_nil(ms: List<&2, S.Q>) -> {False{} == SV.strict_pos(ms, Nil{}) : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, t}:
      {==}

# the padding changes no strict multiplier
def spos(ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, w: CP.SubS(xs, ys), +ms: List<&2, S.Q>) -> {SV.strict_pos(spad(ys, xs, w, ms), ys) == SV.strict_pos(ms, xs) : Bool}:
  match ys xs:
    case Nil{} Nil{}:
      spos_nil(ms)
    case Nil{} Con{+x, +xt}:
      absurd({SV.strict_pos(spad(Nil{}, Con{x, xt}, w, ms), Nil{}) == SV.strict_pos(ms, Con{x, xt}) : Bool}, w)
    case Con{+y, +yt} Nil{}:
      spos.z(y, yt, spad(yt, Nil{}, Unit{}, ms), SV.strict_pos(ms, Nil{}), spos(yt, Nil{}, Unit{}, ms))
    case Con{+y, +yt} Con{+x, +xt}:
      match w:
        case Inl{+p}:
          %Equal.sym(SK.Side, x, y, LX.both_l({x == y : SK.Side}, CP.SubS(xt, yt), p)) : {SV.strict_pos(Con{qhd(ms), spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms))}, Con{y, yt}) == SV.strict_pos(ms, Con{_, xt}) : Bool}
          spos.h(y, ms, yt, xt, spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms)), spos(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), p), qtl(ms)))
        case Inr{+q}:
          spos.z(y, yt, spad(yt, Con{x, xt}, q, ms), SV.strict_pos(ms, Con{x, xt}), spos(yt, Con{x, xt}, q, ms))

# 0 v + r = r
def zadd(+v: S.Q, +r: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(SV.qzero(), v), r), r):
  QR.qring_eq([v, r], E.QAdd{E.QMul{E.QCst{SV.qzero()}, E.QVar{0n}}, E.QVar{1n}}, E.QVar{1n}, {==})

def slin.z(+p: List<&2, S.Q>, +y: SK.Side, +yt: List<&2, SK.Side>, +R: List<&2, S.Q>, +b: S.Q, ih: S.Q.eq(E.qeval(p, SV.slin(R, yt)), b)) -> S.Q.eq(E.qeval(p, SV.slin(Con{SV.qzero(), R}, Con{y, yt})), b):
  LQ.q_trans(S.Q.add(S.Q.mul(SV.qzero(), E.qeval(p, SV.sexpr(y))), E.qeval(p, SV.slin(R, yt))), E.qeval(p, SV.slin(R, yt)), b, zadd(E.qeval(p, SV.sexpr(y)), E.qeval(p, SV.slin(R, yt))), ih)

def slin.h(+p: List<&2, S.Q>, +y: SK.Side, ms: List<&2, S.Q>, +yt: List<&2, SK.Side>, +xt: List<&2, SK.Side>, +R: List<&2, S.Q>, ih: S.Q.eq(E.qeval(p, SV.slin(R, yt)), E.qeval(p, SV.slin(qtl(ms), xt)))) -> S.Q.eq(E.qeval(p, SV.slin(Con{qhd(ms), R}, Con{y, yt})), E.qeval(p, SV.slin(ms, Con{y, xt}))):
  match ms:
    case Nil{}:
      slin.z(p, y, yt, R, SV.qzero(), ih)
    case Con{+m, +mt}:
      LQ.q_add_cong_r(S.Q.mul(m, E.qeval(p, SV.sexpr(y))), E.qeval(p, SV.slin(R, yt)), E.qeval(p, SV.slin(mt, xt)), ih)

def slin_nil(+p: List<&2, S.Q>, ms: List<&2, S.Q>) -> S.Q.eq(E.qeval(p, SV.slin(Nil{}, Nil{})), E.qeval(p, SV.slin(ms, Nil{}))):
  match ms:
    case Nil{}:
      LQ.q_refl(SV.qzero())
    case Con{m, t}:
      LQ.q_refl(SV.qzero())

# the padded multipliers give the same combination of the sides
def slin_pad(+p: List<&2, S.Q>, ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, w: CP.SubS(xs, ys), +ms: List<&2, S.Q>) -> S.Q.eq(E.qeval(p, SV.slin(spad(ys, xs, w, ms), ys)), E.qeval(p, SV.slin(ms, xs))):
  match ys xs:
    case Nil{} Nil{}:
      slin_nil(p, ms)
    case Nil{} Con{+x, +xt}:
      absurd(S.Q.eq(E.qeval(p, SV.slin(spad(Nil{}, Con{x, xt}, w, ms), Nil{})), E.qeval(p, SV.slin(ms, Con{x, xt}))), w)
    case Con{+y, +yt} Nil{}:
      slin.z(p, y, yt, spad(yt, Nil{}, Unit{}, ms), E.qeval(p, SV.slin(ms, Nil{})), slin_pad(p, yt, Nil{}, Unit{}, ms))
    case Con{+y, +yt} Con{+x, +xt}:
      match w:
        case Inl{+q}:
          %Equal.sym(SK.Side, x, y, LX.both_l({x == y : SK.Side}, CP.SubS(xt, yt), q)) : S.Q.eq(E.qeval(p, SV.slin(Con{qhd(ms), spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), q), qtl(ms))}, Con{y, yt})), E.qeval(p, SV.slin(ms, Con{_, xt})))
          slin.h(p, y, ms, yt, xt, spad(yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), q), qtl(ms)), slin_pad(p, yt, xt, LX.both_r({x == y : SK.Side}, CP.SubS(xt, yt), q), qtl(ms)))
        case Inr{+r}:
          slin.z(p, y, yt, spad(yt, Con{x, xt}, r, ms), E.qeval(p, SV.slin(ms, Con{x, xt})), slin_pad(p, yt, Con{x, xt}, r, ms))

def qlen_ok(+ys: List<&2, SK.Side>, +xs: List<&2, SK.Side>, +w: CP.SubS(xs, ys), +ms: List<&2, S.Q>) -> {SV.eq(SV.qlen(spad(ys, xs, w, ms)), SV.slen(ys)) == True{} : Bool}:
  %Equal.sym(Nat, SV.qlen(spad(ys, xs, w, ms)), SV.slen(ys), spad_len(ys, xs, w, ms)) : {SV.eq(_, SV.slen(ys)) == True{} : Bool}
  LI.eq_refl(SV.slen(ys))

# a degree-0 refutation stays one with sides added
def refok_pad(+ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +ys: List<&2, SK.Side>, +xs: List<&2, SK.Side>, +w: CP.SubS(xs, ys), +h: {SV.refok(ls, ms, k, D, xs) == True{} : Bool}) -> {SV.refok(ls, spad(ys, xs, w, ms), k, D, ys) == True{} : Bool}:
  +A = SV.eq(SV.qlen(ls), SV.neqs(D))
  +B = SV.eq(SV.qlen(ms), SV.slen(xs))
  +C = SV.nonneg(ms)
  +G = SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, xs)))
  +P = spad(ys, xs, w, ms)
  +G2 = SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(P, ys)))
  +r1 = LI.band_r(A, SV.band(B, SV.band(C, G)), h)
  +r2 = LI.band_r(B, SV.band(C, G), r1)
  LI.band_i(A, SV.band(SV.eq(SV.qlen(P), SV.slen(ys)), SV.band(SV.nonneg(P), G2)), LI.band_l(A, SV.band(B, SV.band(C, G)), h),
    LI.band_i(SV.eq(SV.qlen(P), SV.slen(ys)), SV.band(SV.nonneg(P), G2), qlen_ok(ys, xs, w, ms),
      LI.band_i(SV.nonneg(P), G2, spad_nn(ys, xs, w, ms, LI.band_l(C, G, r2)),
        (%Equal.sym(Bool, SV.strict_pos(P, ys), SV.strict_pos(ms, xs), spos(ys, xs, w, ms)) : {SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), _)) == True{} : Bool} LI.band_r(C, G, r2)))))

def r0pad.at(+p: List<&2, S.Q>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +ys: List<&2, SK.Side>, +xs: List<&2, SK.Side>, +w: CP.SubS(xs, ys), hi: SV.Ident(E.QAdd{SV.lin(ls, D), SV.slin(ms, xs)}, E.QCst{k}))
  -> S.Q.eq(E.qeval(p, E.QAdd{SV.lin(ls, D), SV.slin(spad(ys, xs, w, ms), ys)}), k):
  LQ.q_trans(S.Q.add(E.qeval(p, SV.lin(ls, D)), E.qeval(p, SV.slin(spad(ys, xs, w, ms), ys))), S.Q.add(E.qeval(p, SV.lin(ls, D)), E.qeval(p, SV.slin(ms, xs))), k,
    LQ.q_add_cong_r(E.qeval(p, SV.lin(ls, D)), E.qeval(p, SV.slin(spad(ys, xs, w, ms), ys)), E.qeval(p, SV.slin(ms, xs)), slin_pad(p, ys, xs, w, ms)), hi(p))

def r0pad.ip(+ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +ys: List<&2, SK.Side>, +xs: List<&2, SK.Side>, +w: CP.SubS(xs, ys), hi: SV.Ident(E.QAdd{SV.lin(ls, D), SV.slin(ms, xs)}, E.QCst{k}))
  -> SV.Ident(E.QAdd{SV.lin(ls, D), SV.slin(spad(ys, xs, w, ms), ys)}, E.QCst{k}):
  p => r0pad.at(p, ls, ms, k, D, ys, xs, w, hi)

def r0pad(+D: List<&2, E.QExpr>, +ys: List<&2, SK.Side>, +xs: List<&2, SK.Side>, +w: CP.SubS(xs, ys), +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, h: SV.Refutes0(D, xs, ls, ms, k)) -> SV.Refutes0(D, ys, ls, spad(ys, xs, w, ms), k):
  (ho, hi) = h
  (refok_pad(ls, ms, k, D, ys, xs, w, ho), r0pad.ip(ls, ms, k, D, ys, xs, w, hi))

# The facts of fewer constraints
# ------------------------------

def subf_cons_r(xs: List<&2, DR.Fact>, +y: DR.Fact, +ys: List<&2, DR.Fact>, h: SubF(xs, ys)) -> SubF(xs, Con{y, ys}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +xt}:
      Inr{h}

def fmono.c(b1: Bool, b2: Bool, +f: DR.Fact, +r1: List<&2, DR.Fact>, +r2: List<&2, DR.Fact>, hb: {b1 == True{} : Bool} -> {b2 == True{} : Bool}, ih: SubF(r1, r2))
  -> SubF(SV.facts.pick(b1, f, r1), SV.facts.pick(b2, f, r2)):
  match b1 b2:
    case True{} True{}:
      Inl{({==}, ih)}
    case True{} False{}:
      absurd(SubF(Con{f, r1}, r2), KA.ft(hb({==})))
    case False{} True{}:
      subf_cons_r(r1, f, r2, ih)
    case False{} False{}:
      ih

def fmono(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +wn: Bool, +k: Nat, +hsub: {SV.sub(cs1, cs2) == True{} : Bool})
  -> SubF(SV.facts.go(es, own, cs1, sk, cls, wn, k), SV.facts.go(es, own, cs2, sk, cls, wn, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      fmono.c(SV.mem(SV.nth(own, k), cs1), SV.mem(SV.nth(own, k), cs2), DR.Fact{e, SV.fnd.pick(wn, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))},
        SV.facts.go(t, own, cs1, sk, cls, wn, 1n+k), SV.facts.go(t, own, cs2, sk, cls, wn, 1n+k), a => CP.mem_sub(SV.nth(own, k), cs1, cs2, hsub, a), fmono(t, own, cs1, cs2, sk, cls, wn, 1n+k, hsub))


# the facts of c with cs1 are among those of c with cs2, cs1 among cs2
def rmono(+sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +hsub: {SV.sub(cs1, cs2) == True{} : Bool}) -> SubF(SV.rfacts(sk, Con{c, cs1}), SV.rfacts(sk, Con{c, cs2})):
  fmono(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, cs1}, Con{c, cs2}, sk, Nil{}, False{}, 0n, CP.sub_ct(c, cs1, cs2, hsub))

# Refutations, with more constraints
# ----------------------------------

def rmap(r: DR.DRef, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), +ss2: List<&2, SK.Side>, +ss1: List<&2, SK.Side>, +ws: CP.SubS(ss1, ss2)) -> DR.DRef:
  match r:
    case DR.RMotz{ds, ls, ms, k}:
      DR.RMotz{dmaps(ds, ys, xs, w), ls, spad(ss2, ss1, ws, ms), k}
    case DR.RColl{dr, di, s}:
      DR.RColl{dmap(dr, ys, xs, w), dmap(di, ys, xs, w), s}
    case DR.RAngle{dr, di, p, fst}:
      DR.RAngle{dmap(dr, ys, xs, w), dmap(di, ys, xs, w), p, fst}


def acmap(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +dr: DR.Der, +di: DR.Der, +ys: List<&2, DR.Fact>, +xs: List<&2, DR.Fact>, +w: SubF(xs, ys), h: DR.AngleColl(es, xs, dr, di, m)) -> DR.AngleColl(es, ys, dmap(dr, ys, xs, w), dmap(di, ys, xs, w), m):
  match m:
    case Some{+a}:
      (sr, si) = h
      ((%cm.s(dr, es, ys, xs, w) : DR.Same(DR.Jd.e(_), SK.VE.x(DR.zseg(es, a))) sr), (%cm.s(di, es, ys, xs, w) : DR.Same(DR.Jd.e(_), SK.VE.y(DR.zseg(es, a))) si))
    case None{}:
      h

def ramap(m: Maybe<&2, SK.Constraint>, +sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +cx: List<&2, E.QExpr>, +dr: DR.Der, +di: DR.Der, +fst: Bool, +hsub: {SV.sub(cs1, cs2) == True{} : Bool},
  h: SV.RefAngle.at(sk, c, cs1, cx, dr, di, m, fst)) -> SV.RefAngle.at(sk, c, cs2, cx, dmap(dr, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub)), dmap(di, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub)), m, fst):
  match m:
    case Some{+kc}:
      (vr, r1) = h
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, ac) = r3
      (vmap(dr, SV.ents(sk), cx, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), vr), (vmap(di, SV.ents(sk), cx, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), vi), (ik(dr, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), kr), (ik(di, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), ki),
        acmap(DR.angle_seg(kc, fst), SV.ents(sk), dr, di, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), ac)))))
    case None{}:
      h

# a refutation of c with cs1 is one with cs2
def refok_map(r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +cx: List<&2, E.QExpr>, +hsub: {SV.sub(cs1, cs2) == True{} : Bool}, h: SV.RefOk(sk, c, cs1, cx, r))
  -> SV.RefOk(sk, c, cs2, cx, rmap(r, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), SK.cats(SV.csides(sk, Con{c, cs2}), SV.esides(sk)), SK.cats(SV.csides(sk, Con{c, cs1}), SV.esides(sk)), CP.supp_mono_s(sk, c, cs1, cs2, hsub))):
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      (av, h0) = h
      (avmap(ds, SV.ents(sk), cx, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), av),
       (%Equal.sym(List<&2, E.QExpr>, DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), dmaps(ds, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub))), DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, cs1}), ds), dcmap(ds, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub))) : SV.Refutes0(_, SK.cats(SV.csides(sk, Con{c, cs2}), SV.esides(sk)), ls, spad(SK.cats(SV.csides(sk, Con{c, cs2}), SV.esides(sk)), SK.cats(SV.csides(sk, Con{c, cs1}), SV.esides(sk)), CP.supp_mono_s(sk, c, cs1, cs2, hsub), ms), k)
         r0pad(DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, cs1}), ds), SK.cats(SV.csides(sk, Con{c, cs2}), SV.esides(sk)), SK.cats(SV.csides(sk, Con{c, cs1}), SV.esides(sk)), CP.supp_mono_s(sk, c, cs1, cs2, hsub), ls, ms, k, h0)))
    case DR.RColl{+dr, +di, +s}:
      (vr, r1) = h
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, r5) = r4
      (si, op) = r5
      (vmap(dr, SV.ents(sk), cx, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), vr), (vmap(di, SV.ents(sk), cx, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), vi), (ik(dr, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), kr), (ik(di, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), ki),
        ((%cm.s(dr, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub)) : DR.Same(DR.Jd.e(_), SK.VE.x(DR.zseg(SV.ents(sk), s))) sr), ((%cm.s(di, SV.ents(sk), SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub)) : DR.Same(DR.Jd.e(_), SK.VE.y(DR.zseg(SV.ents(sk), s))) si), op))))))
    case DR.RAngle{+dr, +di, +p, +fst}:
      (hm, ra) = h
      (CP.mem_sub(p, Con{c, cs1}, Con{c, cs2}, CP.sub_ct(c, cs1, cs2, hsub), hm), ramap(SV.kind_at(sk, p), sk, c, cs1, cs2, cx, dr, di, fst, hsub, ra))

def nodir.go(+r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +cx: List<&2, E.QExpr>, +hsub: {SV.sub(cs1, cs2) == True{} : Bool}, h: SV.NoDirRef(sk, c, cs2, cx), hr: SV.RefOk(sk, c, cs1, cx, r)) -> Empty:
  h(rmap(r, SV.rfacts(sk, Con{c, cs2}), SV.rfacts(sk, Con{c, cs1}), rmono(sk, c, cs1, cs2, hsub), SK.cats(SV.csides(sk, Con{c, cs2}), SV.esides(sk)), SK.cats(SV.csides(sk, Con{c, cs1}), SV.esides(sk)), CP.supp_mono_s(sk, c, cs1, cs2, hsub)), refok_map(r, sk, c, cs1, cs2, cx, hsub, hr))

# with more constraints, no refutation means none with fewer
def nodir_mono(+sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +cx: List<&2, E.QExpr>, +hsub: {SV.sub(cs1, cs2) == True{} : Bool}, h: SV.NoDirRef(sk, c, cs2, cx)) -> SV.NoDirRef(sk, c, cs1, cx):
  r => nodir.go(r, sk, c, cs1, cs2, cx, hsub, h)
