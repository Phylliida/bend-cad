# bend-cad: what the verdict's amber checks say (lib/verdict.bend: ack;
# PLAN-sk13a S5). Proofs only.
#
# - refute_at: a degree-0 refutation that passes (refok, and its identity
#   normalizes to 0) holds at no point where its equations are 0 and its
#   side conditions hold: there l . es is 0, m . ss is >= 0 (> 0 with a
#   strict side weighted positively), and the two add up to k.
# - side_of_ref: so a passing refutation of premises and a side's
#   negation leaves the side, wherever the premises hold (the order is
#   total).
# - sides_mark: at a point where the system solved holds, the drop and
#   amber checks pass, and the side conditions of the kept constraints
#   that are not amber hold (and the entities'), every side condition of
#   the sketch less its red constraints holds. Along the order: the
#   premises of an amber constraint are the equations and side conditions
#   of the kept constraints before it (and the entities'), all known by
#   then, so each of its refutations gives one of its sides.
#
# Generated from tools/drafts/vsdpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./flaws.bend as FL
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qnorm.bend as QN
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./kbpf.bend as KB
import ./clslpf.bend as CL
import ./qsign.bend as SA
import ./conflict.bend as CO
import ./verdict.bend as VD
import ./vrdpf.bend as VR

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Side conditions over lists
# --------------------------

def sides_l(~F: O.OField, +x: M.Vec(~F), a: List<&2, SK.Side>, +b: List<&2, SK.Side>, h: SK.Sides(~F, x, SK.cats(a, b))) -> SK.Sides(~F, x, a):
  match a:
    case Nil{}:
      Unit{}
    case Con{SK.Gt0{+e}, +t}:
      (h1, h2) = h
      (h1, sides_l(~F, x, t, b, h2))
    case Con{SK.Ge0{+e}, +t}:
      (h1, h2) = h
      (h1, sides_l(~F, x, t, b, h2))

def sides_r(~F: O.OField, +x: M.Vec(~F), a: List<&2, SK.Side>, +b: List<&2, SK.Side>, h: SK.Sides(~F, x, SK.cats(a, b))) -> SK.Sides(~F, x, b):
  match a:
    case Nil{}:
      h
    case Con{SK.Gt0{+e}, +t}:
      (h1, h2) = h
      sides_r(~F, x, t, b, h2)
    case Con{SK.Ge0{+e}, +t}:
      (h1, h2) = h
      sides_r(~F, x, t, b, h2)

def sides_join(~F: O.OField, +x: M.Vec(~F), a: List<&2, SK.Side>, +b: List<&2, SK.Side>, ha: SK.Sides(~F, x, a), hb: SK.Sides(~F, x, b)) -> SK.Sides(~F, x, SK.cats(a, b)):
  match a:
    case Nil{}:
      hb
    case Con{SK.Gt0{+e}, +t}:
      (h1, h2) = ha
      (h1, sides_join(~F, x, t, b, h2, hb))
    case Con{SK.Ge0{+e}, +t}:
      (h1, h2) = ha
      (h1, sides_join(~F, x, t, b, h2, hb))

# A refutation holds nowhere
# --------------------------

def lin_zero(~F: O.OField, +x: M.Vec(~F), ls: List<&2, S.Q>, es: List<&2, E.QExpr>, hz: SK.Zeros(~F, x, es)) -> {O.eval(~F, x, SV.lin(ls, es)) == O.zero(F) : O.C(F)}:
  match ls es:
    case Con{+l, +lt} Con{+e, +et}:
      (h1, h2) = hz
      %Equal.sym(O.C(F), O.eval(~F, x, SV.lin(lt, et)), O.zero(F), lin_zero(~F, x, lt, et, h2)) : {O.add(F, O.mul(F, O.ofq(~F, l), O.eval(~F, x, e)), _) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.eval(~F, x, e), O.zero(F), h1) : {O.add(F, O.mul(F, O.ofq(~F, l), _), O.zero(F)) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, O.ofq(~F, l)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      O.add_zero(F)(O.zero(F))
    case Nil{} es:
      QE.ofq_zero(~F)
    case Con{l, lt} Nil{}:
      QE.ofq_zero(~F)

def le_zq(~F: O.OField) -> O.le(~F, O.zero(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}})):
  %Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F)) : O.le(~F, O.zero(F), _)
  FO.le_refl(~F, O.zero(F))


# with every multiplier >= 0, the sides' combination is >= 0
def slin_nn(~F: O.OField, +x: M.Vec(~F), ms: List<&2, S.Q>, ss: List<&2, SK.Side>, hs: SK.Sides(~F, x, ss), +hn: {SV.nonneg(ms) == True{} : Bool}) -> O.le(~F, O.zero(F), O.eval(~F, x, SV.slin(ms, ss))):
  match ms ss:
    case Con{+m, +mt} Con{SK.Gt0{+e}, +st}:
      (h1, h2) = hs
      +hm = L.band_l(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      +hr = L.band_r(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      FO.nonneg_add(~F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)), FO.mul_nonneg(~F, O.ofq(~F, m), O.eval(~F, x, e), SA.q_nn(~F, m, hm), FO.lt_le(~F, O.zero(F), O.eval(~F, x, e), h1)), slin_nn(~F, x, mt, st, h2, hr))
    case Con{+m, +mt} Con{SK.Ge0{+e}, +st}:
      (h1, h2) = hs
      +hm = L.band_l(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      +hr = L.band_r(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      FO.nonneg_add(~F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)), FO.mul_nonneg(~F, O.ofq(~F, m), O.eval(~F, x, e), SA.q_nn(~F, m, hm), h1), slin_nn(~F, x, mt, st, h2, hr))
    case Nil{} ss:
      le_zq(~F)
    case Con{m, mt} Nil{}:
      le_zq(~F)

def slin_pos.c(~F: O.OField, +x: M.Vec(~F), +m: S.Q, +mt: List<&2, S.Q>, +e: E.QExpr, +st: List<&2, SK.Side>, b: Bool, eb: {SV.islt(S.Q.cmp(SV.qzero(), m)) == b : Bool}, hp: {SV.bor(b, SV.strict_pos(mt, st)) == True{} : Bool},
  +h1: O.lt(F, O.zero(F), O.eval(~F, x, e)), +hm: {SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))) == True{} : Bool}, +hrest: O.le(~F, O.zero(F), O.eval(~F, x, SV.slin(mt, st))), ih: {SV.strict_pos(mt, st) == True{} : Bool} -> O.lt(F, O.zero(F), O.eval(~F, x, SV.slin(mt, st))))
  -> O.lt(F, O.zero(F), O.add(F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)))):
  match b:
    case True{}:
      FO.pos_add(~F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)), O.lt_mul(F)(O.ofq(~F, m), O.eval(~F, x, e))(SA.q_pos(~F, m, eb))(h1), hrest)
    case False{}:
      FO.pos_add_r(~F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)), FO.mul_nonneg(~F, O.ofq(~F, m), O.eval(~F, x, e), SA.q_nn(~F, m, hm), FO.lt_le(~F, O.zero(F), O.eval(~F, x, e), h1)), ih(hp))

# and > 0 when some strict side is weighted positively
def slin_pos(~F: O.OField, +x: M.Vec(~F), ms: List<&2, S.Q>, ss: List<&2, SK.Side>, +hs: SK.Sides(~F, x, ss), +hn: {SV.nonneg(ms) == True{} : Bool}, hp: {SV.strict_pos(ms, ss) == True{} : Bool}) -> O.lt(F, O.zero(F), O.eval(~F, x, SV.slin(ms, ss))):
  match ms ss:
    case Con{+m, +mt} Con{SK.Gt0{+e}, +st}:
      (+h1, +h2) = hs
      +hm = L.band_l(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      +hr = L.band_r(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      slin_pos.c(~F, x, m, mt, e, st, SV.islt(S.Q.cmp(SV.qzero(), m)), {==}, hp, h1, hm, slin_nn(~F, x, mt, st, h2, hr), hp2 => slin_pos(~F, x, mt, st, h2, hr, hp2))
    case Con{+m, +mt} Con{SK.Ge0{+e}, +st}:
      (+h1, +h2) = hs
      +hm = L.band_l(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      +hr = L.band_r(SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))), SV.nonneg(mt), hn)
      FO.pos_add_r(~F, O.mul(F, O.ofq(~F, m), O.eval(~F, x, e)), O.eval(~F, x, SV.slin(mt, st)), FO.mul_nonneg(~F, O.ofq(~F, m), O.eval(~F, x, e), SA.q_nn(~F, m, hm), h1), slin_pos(~F, x, mt, st, h2, hr, hp))
    case Nil{} ss:
      absurd(O.lt(F, O.zero(F), O.eval(~F, x, SV.slin(Nil{}, ss))), KA.ft(hp))
    case Con{m, mt} Nil{}:
      absurd(O.lt(F, O.zero(F), O.eval(~F, x, SV.slin(Con{m, mt}, Nil{}))), KA.ft(hp))

# the identity, read at x: m . ss is k there
def sv_of(~F: O.OField, +x: M.Vec(~F), +ls: List<&2, S.Q>, +es: List<&2, E.QExpr>, +ms: List<&2, S.Q>, +ss: List<&2, SK.Side>, +k: S.Q, +hq: {QN.qzero(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}) == True{} : Bool}, hz: SK.Zeros(~F, x, es))
  -> {O.eval(~F, x, SV.slin(ms, ss)) == O.ofq(~F, k) : O.C(F)}:
  +s = O.eval(~F, x, SV.slin(ms, ss))
  Equal.trans(O.C(F), s, O.add(F, O.zero(F), s), O.ofq(~F, k), Equal.sym(O.C(F), O.add(F, O.zero(F), s), s, FL.zero_add(~F, s)),
    (%lin_zero(~F, x, ls, es, hz) : {O.add(F, _, s) == O.ofq(~F, k) : O.C(F)}
      FO.eq_of_sub(~F, O.add(F, O.eval(~F, x, SV.lin(ls, es)), s), O.ofq(~F, k), QN.qzero_ok(~F, x, E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}, hq))))

def ra.c(~F: O.OField, +x: M.Vec(~F), +ms: List<&2, S.Q>, +ss: List<&2, SK.Side>, +k: S.Q, b: Bool, eb: {SV.islt(S.Q.cmp(k, SV.qzero())) == b : Bool}, +hb: {SV.bor(b, SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss))) == True{} : Bool},
  +hs: SK.Sides(~F, x, ss), +hnn: {SV.nonneg(ms) == True{} : Bool}, +hv: {O.eval(~F, x, SV.slin(ms, ss)) == O.ofq(~F, k) : O.C(F)}) -> Empty:
  match b:
    case True{}:
      O.lt_irrefl(F)(O.ofq(~F, k))(FO.lt_le_trans(~F, O.ofq(~F, k), O.zero(F), O.ofq(~F, k),
        (%QE.ofq_zero(~F) : O.lt(F, O.ofq(~F, k), _)
          QE.ofq_lt(~F, k, SV.qzero(), SA.sv_lt(S.Q.cmp(k, SV.qzero()), eb))),
        (%hv : O.le(~F, O.zero(F), _)
          slin_nn(~F, x, ms, ss, hs, hnn))))
    case False{}:
      +hz0 = L.band_l(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss), hb)
      +hsp = L.band_r(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss), hb)
      O.lt_irrefl(F)(O.zero(F))(
        (%SA.ofq_num0(~F, k, SA.iszz_eq(S.Q.num(k), hz0)) : O.lt(F, O.zero(F), _)
          (%hv : O.lt(F, O.zero(F), _)
            slin_pos(~F, x, ms, ss, hs, hnn, hsp))))

# a refutation that passes holds at no point killing its equations and
# holding its side conditions
def refute_at(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, r: SV.Ref, +hok: {VD.ref.ok(es, ss, r) == True{} : Bool}, +hz: SK.Zeros(~F, x, es), +hs: SK.Sides(~F, x, ss)) -> Empty:
  match r:
    case SV.Ref{+ls, +ms, +k}:
      +ro = SV.refok(ls, ms, k, es, ss)
      +qz = QN.qzero(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}})
      +b1 = SV.eq(SV.qlen(ls), SV.neqs(es))
      +b2 = SV.eq(SV.qlen(ms), SV.slen(ss))
      +b3 = SV.nonneg(ms)
      +b4 = SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss)))
      +h34 = L.band_r(b2, SV.band(b3, b4), L.band_r(b1, SV.band(b2, SV.band(b3, b4)), L.band_l(ro, qz, hok)))
      ra.c(~F, x, ms, ss, k, SV.islt(S.Q.cmp(k, SV.qzero())), {==}, L.band_r(b3, b4, h34), hs, L.band_l(b3, b4, h34), sv_of(~F, x, ls, es, ms, ss, k, L.band_r(ro, qz, hok), hz))

# The side a refutation leaves
# ----------------------------

def sor.gt(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +e: E.QExpr, +r: SV.Ref, +hok: {VD.ref.ok(es, SK.cats(ss, [SK.Ge0{E.QNeg{e}}]), r) == True{} : Bool}, +hz: SK.Zeros(~F, x, es), +hs: SK.Sides(~F, x, ss),
  t: Or(O.lt(F, O.zero(F), O.eval(~F, x, e)), Or({O.zero(F) == O.eval(~F, x, e) : O.C(F)}, O.lt(F, O.eval(~F, x, e), O.zero(F))))) -> O.lt(F, O.zero(F), O.eval(~F, x, e)):
  match t:
    case Inl{+l}:
      l
    case Inr{Inl{e0}}:
      absurd(O.lt(F, O.zero(F), O.eval(~F, x, e)), refute_at(~F, x, es, SK.cats(ss, [SK.Ge0{E.QNeg{e}}]), r, hok, hz,
        sides_join(~F, x, ss, [SK.Ge0{E.QNeg{e}}], hs, (Inr{(%e0 : {O.zero(F) == O.neg(F, _) : O.C(F)}
          FL.neg_zero(~F))}, Unit{}))))
    case Inr{Inr{+g}}:
      absurd(O.lt(F, O.zero(F), O.eval(~F, x, e)), refute_at(~F, x, es, SK.cats(ss, [SK.Ge0{E.QNeg{e}}]), r, hok, hz,
        sides_join(~F, x, ss, [SK.Ge0{E.QNeg{e}}], hs, (Inl{FO.neg_pos(~F, O.eval(~F, x, e), g)}, Unit{}))))

def sor.ge(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +e: E.QExpr, +r: SV.Ref, +hok: {VD.ref.ok(es, SK.cats(ss, [SK.Gt0{E.QNeg{e}}]), r) == True{} : Bool}, +hz: SK.Zeros(~F, x, es), +hs: SK.Sides(~F, x, ss),
  t: Or(O.lt(F, O.zero(F), O.eval(~F, x, e)), Or({O.zero(F) == O.eval(~F, x, e) : O.C(F)}, O.lt(F, O.eval(~F, x, e), O.zero(F))))) -> O.le(~F, O.zero(F), O.eval(~F, x, e)):
  match t:
    case Inl{+l}:
      Inl{l}
    case Inr{Inl{+e0}}:
      Inr{e0}
    case Inr{Inr{+g}}:
      absurd(O.le(~F, O.zero(F), O.eval(~F, x, e)), refute_at(~F, x, es, SK.cats(ss, [SK.Gt0{E.QNeg{e}}]), r, hok, hz,
        sides_join(~F, x, ss, [SK.Gt0{E.QNeg{e}}], hs, (FO.neg_pos(~F, O.eval(~F, x, e), g), Unit{}))))

# where the premises hold, a passing refutation of them with s's
# negation leaves s
def side_of_ref(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, s: SK.Side, +r: SV.Ref, +hok: {VD.ref.ok(es, SK.cats(ss, [SV.negate(s)]), r) == True{} : Bool}, +hz: SK.Zeros(~F, x, es), +hs: SK.Sides(~F, x, ss)) -> SK.Sides(~F, x, [s]):
  match s:
    case SK.Gt0{+e}:
      (sor.gt(~F, x, es, ss, e, r, hok, hz, hs, O.lt_total(F)(O.zero(F), O.eval(~F, x, e))), Unit{})
    case SK.Ge0{+e}:
      (sor.ge(~F, x, es, ss, e, r, hok, hz, hs, O.lt_total(F)(O.zero(F), O.eval(~F, x, e))), Unit{})

# Side lists by position
# ----------------------

def sdrop(k: Nat, xs: List<&2, SK.Side>) -> List<&2, SK.Side>:
  match k xs:
    case 0n xs:
      xs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      sdrop(j, t)

def stl(xs: List<&2, SK.Side>) -> List<&2, SK.Side>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def shd(xs: List<&2, SK.Side>) -> SK.Side:
  match xs:
    case Nil{}:
      SK.Gt0{E.QCst{SV.qzero()}}
    case Con{h, t}:
      h

def sdrop_tl(k: Nat, xs: List<&2, SK.Side>) -> {sdrop(1n+k, xs) == stl(sdrop(k, xs)) : List<&2, SK.Side>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      sdrop_tl(j, t)

def sdrop_step(+k: Nat, +xs: List<&2, SK.Side>, +s: SK.Side, +t: List<&2, SK.Side>, h: {sdrop(k, xs) == Con{s, t} : List<&2, SK.Side>}) -> {sdrop(1n+k, xs) == t : List<&2, SK.Side>}:
  Equal.trans(List<&2, SK.Side>, sdrop(1n+k, xs), stl(sdrop(k, xs)), t, sdrop_tl(k, xs), Equal.cong(List<&2, SK.Side>, List<&2, SK.Side>, y => stl(y), sdrop(k, xs), Con{s, t}, h))

def side_at_sdrop(xs: List<&2, SK.Side>, k: Nat) -> {SV.side_at(xs, k) == shd(sdrop(k, xs)) : SK.Side}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      side_at_sdrop(t, j)

def side_at_of(+xs: List<&2, SK.Side>, +k: Nat, +s: SK.Side, +t: List<&2, SK.Side>, h: {sdrop(k, xs) == Con{s, t} : List<&2, SK.Side>}) -> {SV.side_at(xs, k) == s : SK.Side}:
  Equal.trans(SK.Side, SV.side_at(xs, k), shd(sdrop(k, xs)), s, side_at_sdrop(xs, k), Equal.cong(List<&2, SK.Side>, SK.Side, y => shd(y), sdrop(k, xs), Con{s, t}, h))

# An amber constraint's sides
# ---------------------------


def rs_c(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +s: SK.Side, +t: List<&2, SK.Side>, rs: List<&2, SV.Ref>, +i: Nat, +hd: {sdrop(i, SV.csides(sk, [c])) == Con{s, t} : List<&2, SK.Side>},
  +hok: {VD.refs.ok(sk, R, c, 1n+SV.slen(t), rs, i) == True{} : Bool}, +hz: SK.Zeros(~F, x, SV.pre_eqs(sk, R, c)), +hs: SK.Sides(~F, x, SV.pre_sides(sk, R, c)),
  ih: @rt: List<&2, SV.Ref> -> {VD.refs.ok(sk, R, c, SV.slen(t), rt, 1n+i) == True{} : Bool} -> SK.Sides(~F, x, t)) -> SK.Sides(~F, x, Con{s, t}):
  match rs:
    case Nil{}:
      absurd(SK.Sides(~F, x, Con{s, t}), KA.ft(hok))
    case Con{+r, +rt}:
      +h1 = L.band_l(VD.ref.ok(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i), r), VD.refs.ok(sk, R, c, SV.slen(t), rt, 1n+i), hok)
      +h2 = L.band_r(VD.ref.ok(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i), r), VD.refs.ok(sk, R, c, SV.slen(t), rt, 1n+i), hok)
      sides_join(~F, x, [s], t,
        side_of_ref(~F, x, SV.pre_eqs(sk, R, c), SV.pre_sides(sk, R, c), s, r,
          (%side_at_of(SV.csides(sk, [c]), i, s, t, hd) : {VD.ref.ok(SV.pre_eqs(sk, R, c), SK.cats(SV.pre_sides(sk, R, c), [SV.negate(_)]), r) == True{} : Bool}
            h1), hz, hs),
        ih(rt, h2))

# c's side conditions from the i-th (ss), each refuted with the premises
# before c: they hold where the premises do
def rs_go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, ss: List<&2, SK.Side>, rs: List<&2, SV.Ref>, +i: Nat, +hd: {sdrop(i, SV.csides(sk, [c])) == ss : List<&2, SK.Side>},
  hok: {VD.refs.ok(sk, R, c, SV.slen(ss), rs, i) == True{} : Bool}, +hz: SK.Zeros(~F, x, SV.pre_eqs(sk, R, c)), +hs: SK.Sides(~F, x, SV.pre_sides(sk, R, c))) -> SK.Sides(~F, x, ss):
  match ss:
    case Nil{}:
      Unit{}
    case Con{+s, +t}:
      rs_c(~F, x, sk, R, c, s, t, rs, i, hd, hok, hz, hs, rt => h2 => rs_go(~F, x, sk, R, c, t, rt, 1n+i, sdrop_step(i, SV.csides(sk, [c]), s, t, hd), h2, hz, hs))

# an amber constraint whose refutations pass: its sides hold where its
# premises do
def am.c(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, kc: SV.Class, hia: {SV.is_amber(kc) == True{} : Bool}, hk: {VD.kamber.ok(sk, R, c, kc) == True{} : Bool}, +hz: SK.Zeros(~F, x, SV.pre_eqs(sk, R, c)), +hs: SK.Sides(~F, x, SV.pre_sides(sk, R, c)))
  -> SK.Sides(~F, x, SV.csides(sk, [c])):
  match kc:
    case SV.Kept{dd}:
      absurd(SK.Sides(~F, x, SV.csides(sk, [c])), KA.ft(hia))
    case SV.Amber{dd, +rs}:
      rs_go(~F, x, sk, R, c, SV.csides(sk, [c]), rs, 0n, {==}, hk, hz, hs)
    case SV.Over{j, s, w}:
      absurd(SK.Sides(~F, x, SV.csides(sk, [c])), KA.ft(hia))
    case SV.Conflict{s}:
      absurd(SK.Sides(~F, x, SV.csides(sk, [c])), KA.ft(hia))

# Ambers and the amber check, by position
# ---------------------------------------

def ajk(cls: List<&2, SV.Class>, +i: Nat, +j: Nat) -> Bool:
  match cls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      SV.bor(SV.band(SV.is_amber(h), SV.eq(j, i)), ajk(t, 1n+i, j))

def mem_ambers_ajk(cls: List<&2, SV.Class>, +i: Nat, +j: Nat) -> {SV.mem(j, SV.ambers.go(cls, i)) == ajk(cls, i, j) : Bool}:
  match cls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      CL.rr.c(SV.is_amber(h), i, j, SV.ambers.go(t, 1n+i), ajk(t, 1n+i, j), mem_ambers_ajk(t, 1n+i, j))

def ajk_lt(cls: List<&2, SV.Class>, +i: Nat, +j: Nat, +h: {SV.lt(j, i) == True{} : Bool}) -> {ajk(cls, i, j) == False{} : Bool}:
  match cls:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.bor_f(SV.band(SV.is_amber(y), SV.eq(j, i)), ajk(t, 1n+i, j), CL.band_f(SV.is_amber(y), SV.eq(j, i), Equal.trans(Bool, SV.eq(j, i), SV.eq(i, j), False{}, L.eq_sym(j, i), KB.ne_of_lt(j, i, h))),
        ajk_lt(t, 1n+i, j, KB.lt_up(j, i, h)))

def ajk_at(cls: List<&2, SV.Class>, +i: Nat, m: Nat) -> {ajk(cls, i, Nat.add(m, i)) == SV.is_amber(SV.class_at(cls, m)) : Bool}:
  match cls m:
    case Nil{} m:
      {==}
    case Con{+h, +t} 0n:
      %Equal.sym(Bool, ajk(t, 1n+i, i), False{}, ajk_lt(t, 1n+i, i, KB.lt_succ(i))) : {SV.bor(SV.band(SV.is_amber(h), SV.eq(i, i)), _) == SV.is_amber(h) : Bool}
      %Equal.sym(Bool, SV.band(SV.is_amber(h), SV.eq(i, i)), SV.is_amber(h), CL.band_t(SV.is_amber(h), SV.eq(i, i), L.eq_refl(i))) : {SV.bor(_, False{}) == SV.is_amber(h) : Bool}
      KB.bor_f(SV.is_amber(h))
    case Con{+h, +t} 1n++k:
      %Equal.sym(Bool, SV.band(SV.is_amber(h), SV.eq(1n+Nat.add(k, i), i)), False{}, CL.band_f(SV.is_amber(h), SV.eq(1n+Nat.add(k, i), i), CL.ne_add(k, i))) : {SV.bor(_, ajk(t, 1n+i, 1n+Nat.add(k, i))) == SV.is_amber(SV.class_at(t, k)) : Bool}
      %Equal.sym(Nat, 1n+Nat.add(k, i), Nat.add(k, 1n+i), LN.add_succ(k, i)) : {ajk(t, 1n+i, _) == SV.is_amber(SV.class_at(t, k)) : Bool}
      ajk_at(t, 1n+i, k)

# position j is among the ambers exactly when its class is amber
def mem_ambers(+cls: List<&2, SV.Class>, +j: Nat) -> {SV.mem(j, SV.ambers(cls)) == SV.is_amber(SV.class_at(cls, j)) : Bool}:
  Equal.trans(Bool, SV.mem(j, SV.ambers(cls)), ajk(cls, 0n, j), SV.is_amber(SV.class_at(cls, j)), mem_ambers_ajk(cls, 0n, j),
    (%Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {ajk(cls, 0n, _) == SV.is_amber(SV.class_at(cls, j)) : Bool}
      ajk_at(cls, 0n, j)))

def ack_go(+sk: SK.Sketch, +R: List<&2, Nat>, cls: List<&2, SV.Class>, +i: Nat, m: Nat, +h: {VD.ack(sk, R, cls, i) == True{} : Bool}) -> {VD.kamber.ok(sk, R, Nat.add(m, i), SV.class_at(cls, m)) == True{} : Bool}:
  match cls m:
    case Nil{} m:
      {==}
    case Con{+k, +t} 0n:
      L.band_l(VD.kamber.ok(sk, R, i, k), VD.ack(sk, R, t, 1n+i), h)
    case Con{+k, +t} 1n++n:
      (%Equal.sym(Nat, 1n+Nat.add(n, i), Nat.add(n, 1n+i), LN.add_succ(n, i)) : {VD.kamber.ok(sk, R, _, SV.class_at(t, n)) == True{} : Bool}
        ack_go(sk, R, t, 1n+i, n, L.band_r(VD.kamber.ok(sk, R, i, k), VD.ack(sk, R, t, 1n+i), h)))

# the amber check passes at every position
def ack_at(+sk: SK.Sketch, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +h: {VD.ack(sk, R, cls, 0n) == True{} : Bool}) -> {VD.kamber.ok(sk, R, c, SV.class_at(cls, c)) == True{} : Bool}:
  (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : {VD.kamber.ok(sk, R, _, SV.class_at(cls, c)) == True{} : Bool}
    ack_go(sk, R, cls, 0n, c, h))

# A constraint's own sides, by position
# -------------------------------------

def cats_nil(xs: List<&2, SK.Side>) -> {SK.cats(xs, Nil{}) == xs : List<&2, SK.Side>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, SK.Side>, List<&2, SK.Side>, y => Con{h, y}, SK.cats(t, Nil{}), t, cats_nil(t))

def csn0(+es: List<&2, SK.Ent>, rt: List<&2, SK.Rec>, +j: Nat) -> {SV.csides.go(es, rt, Nil{}, j) == Nil{} : List<&2, SK.Side>}:
  match rt:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      csn0(es, t, 1n+j)
    case Con{SK.Rec{id, False{}, k}, +t}:
      csn0(es, t, 1n+j)

def csn(+es: List<&2, SK.Ent>, rt: List<&2, SK.Rec>, +c: Nat, +j: Nat, +h: {SV.lt(c, j) == True{} : Bool}) -> {SV.csides.go(es, rt, [c], j) == Nil{} : List<&2, SK.Side>}:
  match rt:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      csn(es, t, c, 1n+j, KB.lt_up(c, j, h))
    case Con{SK.Rec{id, False{}, +k}, +t}:
      %Equal.sym(Bool, SV.eq(j, c), False{}, KB.ne_of_lt(c, j, h)) : {SV.csides.pick(SV.bor(_, False{}), SK.Constraint.sides(es, k), SV.csides.go(es, t, [c], 1n+j)) == Nil{} : List<&2, SK.Side>}
      csn(es, t, c, 1n+j, KB.lt_up(c, j, h))

def ne_succ(+m: Nat, +j: Nat) -> {SV.eq(j, 1n+Nat.add(m, j)) == False{} : Bool}:
  Equal.trans(Bool, SV.eq(j, 1n+Nat.add(m, j)), SV.eq(1n+Nat.add(m, j), j), False{}, L.eq_sym(j, 1n+Nat.add(m, j)), CL.ne_add(m, j))

def cso.go(+es: List<&2, SK.Ent>, d: Nat, rt: List<&2, SK.Rec>, +j: Nat, +id: Nat, +k: SK.Constraint, +tt: List<&2, SK.Rec>, hd: {KB.rdrop(d, rt) == Con{SK.Rec{id, False{}, k}, tt} : List<&2, SK.Rec>}) -> {SV.csides.go(es, rt, [Nat.add(d, j)], j) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}:
  match d rt:
    case 0n rt:
      %Equal.sym(List<&2, SK.Rec>, rt, Con{SK.Rec{id, False{}, k}, tt}, hd) : {SV.csides.go(es, _, [j], j) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      %Equal.sym(Bool, SV.eq(j, j), True{}, L.eq_refl(j)) : {SV.csides.pick(SV.bor(_, False{}), SK.Constraint.sides(es, k), SV.csides.go(es, tt, [j], 1n+j)) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      %Equal.sym(List<&2, SK.Side>, SV.csides.go(es, tt, [j], 1n+j), Nil{}, csn(es, tt, j, 1n+j, KB.lt_succ(j))) : {SK.cats(SK.Constraint.sides(es, k), _) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      cats_nil(SK.Constraint.sides(es, k))
    case 1n+m Nil{}:
      absurd({SV.csides.go(es, Nil{}, [Nat.add(1n+m, j)], j) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}, KB.nil_con(SK.Rec{id, False{}, k}, tt, hd))
    case 1n++m Con{SK.Rec{rid, True{}, rk}, +rt2}:
      %Equal.sym(Nat, 1n+Nat.add(m, j), Nat.add(m, 1n+j), LN.add_succ(m, j)) : {SV.csides.go(es, rt2, [_], 1n+j) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      cso.go(es, m, rt2, 1n+j, id, k, tt, hd)
    case 1n++m Con{SK.Rec{rid, False{}, +rk}, +rt2}:
      %Equal.sym(Bool, SV.eq(j, 1n+Nat.add(m, j)), False{}, ne_succ(m, j)) : {SV.csides.pick(SV.bor(_, False{}), SK.Constraint.sides(es, rk), SV.csides.go(es, rt2, [1n+Nat.add(m, j)], 1n+j)) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      %Equal.sym(Nat, 1n+Nat.add(m, j), Nat.add(m, 1n+j), LN.add_succ(m, j)) : {SV.csides.go(es, rt2, [_], 1n+j) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
      cso.go(es, m, rt2, 1n+j, id, k, tt, hd)


# the side conditions of the driving constraint at position c are its own
def csides_one(+vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +c: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, hd: {KB.rdrop(c, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}) -> {SV.csides(SK.Sketch{vs, es, rs}, [c]) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}:
  %Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : {SV.csides.go(es, rs, [_], 0n) == SK.Constraint.sides(es, k) : List<&2, SK.Side>}
  cso.go(es, c, rs, 0n, id, k, t, hd)

# Adding a constraint to the ones whose sides hold
# ------------------------------------------------

def pick_r(~F: O.OField, +x: M.Vec(~F), b: Bool, +xs: List<&2, SK.Side>, +r: List<&2, SK.Side>, h: SK.Sides(~F, x, SV.csides.pick(b, xs, r))) -> SK.Sides(~F, x, r):
  match b:
    case True{}:
      sides_r(~F, x, xs, r, h)
    case False{}:
      h

def ssn.d(~F: O.OField, +x: M.Vec(~F), b: Bool, +xs: List<&2, SK.Side>, +r1: List<&2, SK.Side>, +r3: List<&2, SK.Side>, +r2: List<&2, SK.Side>, h1: SK.Sides(~F, x, r1), h3: SK.Sides(~F, x, SV.csides.pick(SV.bor(b, False{}), xs, r3)),
  ih: SK.Sides(~F, x, r1) -> SK.Sides(~F, x, r3) -> SK.Sides(~F, x, r2)) -> SK.Sides(~F, x, SV.csides.pick(b, xs, r2)):
  match b:
    case True{}:
      +h3c = h3
      sides_join(~F, x, xs, r2, sides_l(~F, x, xs, r3, h3c), ih(h1, sides_r(~F, x, xs, r3, h3c)))
    case False{}:
      ih(h1, h3)

def ssn.c(~F: O.OField, +x: M.Vec(~F), a: Bool, +b: Bool, +xs: List<&2, SK.Side>, +r1: List<&2, SK.Side>, +r3: List<&2, SK.Side>, +r2: List<&2, SK.Side>, h1: SK.Sides(~F, x, SV.csides.pick(a, xs, r1)), h3: SK.Sides(~F, x, SV.csides.pick(SV.bor(b, False{}), xs, r3)),
  ih: SK.Sides(~F, x, r1) -> SK.Sides(~F, x, r3) -> SK.Sides(~F, x, r2)) -> SK.Sides(~F, x, SV.csides.pick(SV.bor(a, b), xs, r2)):
  match a:
    case True{}:
      +h1c = h1
      sides_join(~F, x, xs, r2, sides_l(~F, x, xs, r1, h1c), ih(sides_r(~F, x, xs, r1, h1c), pick_r(~F, x, SV.bor(b, False{}), xs, r3, h3)))
    case False{}:
      ssn.d(~F, x, b, xs, r1, r3, r2, h1, h3, ih)

def ssn(~F: O.OField, +x: M.Vec(~F), +es: List<&2, SK.Ent>, rt: List<&2, SK.Rec>, +cs: List<&2, Nat>, +c: Nat, +j: Nat, h1: SK.Sides(~F, x, SV.csides.go(es, rt, cs, j)), h3: SK.Sides(~F, x, SV.csides.go(es, rt, [c], j)))
  -> SK.Sides(~F, x, SV.csides.go(es, rt, CO.lsnoc(cs, c), j)):
  match rt:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{id, True{}, k}, +t}:
      ssn(~F, x, es, t, cs, c, 1n+j, h1, h3)
    case Con{SK.Rec{id, False{}, +k}, +t}:
      %Equal.sym(Bool, SV.mem(j, CO.lsnoc(cs, c)), SV.bor(SV.mem(j, cs), SV.eq(j, c)), KB.mem_snoc(j, cs, c)) : SK.Sides(~F, x, SV.csides.pick(_, SK.Constraint.sides(es, k), SV.csides.go(es, t, CO.lsnoc(cs, c), 1n+j)))
      ssn.c(~F, x, SV.mem(j, cs), SV.eq(j, c), SK.Constraint.sides(es, k), SV.csides.go(es, t, cs, 1n+j), SV.csides.go(es, t, [c], 1n+j), SV.csides.go(es, t, CO.lsnoc(cs, c), 1n+j), h1, h3,
        a1 => a3 => ssn(~F, x, es, t, cs, c, 1n+j, a1, a3))

# The walk along the constraints
# ------------------------------


def drv_at(+vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +i: Nat, +r: SK.Rec, +t: List<&2, SK.Rec>, hd: {KB.rdrop(i, rs) == Con{r, t} : List<&2, SK.Rec>}) -> {SV.driven(SK.Sketch{vs, es, rs}, i) == SV.driven.rec(r) : Bool}:
  Equal.trans(Bool, SV.driven.at(rs, i), SV.driven.at(KB.rdrop(i, rs), 0n), SV.driven.rec(r), KB.driven_drop(rs, i), Equal.cong(List<&2, SK.Rec>, Bool, z => SV.driven.at(z, 0n), KB.rdrop(i, rs), Con{r, t}, hd))

def dc_dr(+vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, hd: {KB.rdrop(i, rs) == Con{SK.Rec{id, True{}, k}, t} : List<&2, SK.Rec>}) -> {KB.dcond(SK.Sketch{vs, es, rs}, R, i) == False{} : Bool}:
  %Equal.sym(Bool, SV.driving(SK.Sketch{vs, es, rs}, i), False{}, CL.band_f(SV.lt(i, SV.ncons(SK.Sketch{vs, es, rs})), SV.bnot(SV.driven(SK.Sketch{vs, es, rs}, i)), (%Equal.sym(Bool, SV.driven(SK.Sketch{vs, es, rs}, i), True{}, drv_at(vs, es, rs, i, SK.Rec{id, True{}, k}, t, hd)) : {SV.bnot(_) == False{} : Bool}
    {==}))) : {SV.band(_, SV.bnot(SV.mem(i, R))) == False{} : Bool}
  {==}

def dc_red(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, +hred: {SV.mem(i, R) == True{} : Bool}) -> {KB.dcond(sk, R, i) == False{} : Bool}:
  CL.band_f(SV.driving(sk, i), SV.bnot(SV.mem(i, R)), (%Equal.sym(Bool, SV.mem(i, R), True{}, hred) : {SV.bnot(_) == False{} : Bool}
    {==}))

def dc_kept(+vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, +hred: {SV.mem(i, R) == False{} : Bool}) -> {KB.dcond(SK.Sketch{vs, es, rs}, R, i) == True{} : Bool}:
  %Equal.sym(Bool, SV.driven(SK.Sketch{vs, es, rs}, i), False{}, drv_at(vs, es, rs, i, SK.Rec{id, False{}, k}, t, hd)) : {SV.band(SV.band(SV.lt(i, SV.clen(rs)), SV.bnot(_)), SV.bnot(SV.mem(i, R))) == True{} : Bool}
  %Equal.sym(Bool, SV.mem(i, R), False{}, hred) : {SV.band(SV.band(SV.lt(i, SV.clen(rs)), True{}), SV.bnot(_)) == True{} : Bool}
  %Equal.sym(Bool, SV.band(SV.lt(i, SV.clen(rs)), True{}), SV.lt(i, SV.clen(rs)), CL.band_t(SV.lt(i, SV.clen(rs)), True{}, {==})) : {SV.band(_, True{}) == True{} : Bool}
  %Equal.sym(Bool, SV.lt(i, SV.clen(rs)), True{}, KB.lt_drop(rs, i, SK.Rec{id, False{}, k}, t, hd)) : {SV.band(_, True{}) == True{} : Bool}
  {==}

def knext(+vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +i: Nat, +hK: KB.KBP(SK.Sketch{vs, es, rs}, R, SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i)) -> KB.KBP(SK.Sketch{vs, es, rs}, R, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i), 1n+i):
  (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i), KB.kpk(KB.dcond(SK.Sketch{vs, es, rs}, R, i), SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i), KB.kb_next(SK.Sketch{vs, es, rs}, R, i)) : KB.KBP(SK.Sketch{vs, es, rs}, R, _, 1n+i)
    KB.kbp_next(SK.Sketch{vs, es, rs}, R, SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i, hK))

def snext.f(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +i: Nat, +hdc: {KB.dcond(SK.Sketch{vs, es, rs}, R, i) == False{} : Bool}, +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, R, i)))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i))):
  (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i), KB.kpk(KB.dcond(SK.Sketch{vs, es, rs}, R, i), SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i), KB.kb_next(SK.Sketch{vs, es, rs}, R, i)) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, _))
    (%Equal.sym(Bool, KB.dcond(SK.Sketch{vs, es, rs}, R, i), False{}, hdc) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, KB.kpk(_, SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i)))
      hS))

def snext.t(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +i: Nat, +hdc: {KB.dcond(SK.Sketch{vs, es, rs}, R, i) == True{} : Bool}, +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, R, i))), +hone: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, [i]))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i))):
  (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, R, 1n+i), KB.kpk(KB.dcond(SK.Sketch{vs, es, rs}, R, i), SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i), KB.kb_next(SK.Sketch{vs, es, rs}, R, i)) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, _))
    (%Equal.sym(Bool, KB.dcond(SK.Sketch{vs, es, rs}, R, i), True{}, hdc) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, KB.kpk(_, SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i)))
      ssn(~F, x, es, rs, SV.kept_before(SK.Sketch{vs, es, rs}, R, i), i, 0n, hS, hone)))

# the premises' equations: those of constraints none of which is red
def ni_mem.c(+v: Nat, +c: Nat, +t: List<&2, Nat>, +R: List<&2, Nat>, b: Bool, eb: {SV.eq(v, c) == b : Bool}, hm: {SV.bor(b, SV.mem(v, t)) == True{} : Bool}, +hn: {SV.band(SV.bnot(SV.mem(c, R)), SV.none_in(t, R)) == True{} : Bool},
  ih: {SV.mem(v, t) == True{} : Bool} -> {SV.none_in(t, R) == True{} : Bool} -> {SV.mem(v, R) == False{} : Bool}) -> {SV.mem(v, R) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, v, c, L.eq_ok(v, c, eb)) : {SV.mem(_, R) == False{} : Bool}
      KB.bnot_t(SV.mem(c, R), L.band_l(SV.bnot(SV.mem(c, R)), SV.none_in(t, R), hn))
    case False{}:
      ih(hm, L.band_r(SV.bnot(SV.mem(c, R)), SV.none_in(t, R), hn))

def ni_mem(+v: Nat, cs: List<&2, Nat>, +R: List<&2, Nat>, +hn: {SV.none_in(cs, R) == True{} : Bool}, hm: {SV.mem(v, cs) == True{} : Bool}) -> {SV.mem(v, R) == False{} : Bool}:
  match cs:
    case Nil{}:
      absurd({SV.mem(v, R) == False{} : Bool}, KA.ft(hm))
    case Con{+c, +t}:
      ni_mem.c(v, c, t, R, SV.eq(v, c), {==}, hm, hn, a => b => ni_mem(v, t, R, b, a))


def zof.c(~F: O.OField, +x: M.Vec(~F), +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(ES, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(ES, own, R, SV.dropped(cls), cls) == True{} : Bool}, +cs: List<&2, Nat>, +hn: {SV.none_in(cs, R) == True{} : Bool}, +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +hq: {OW.qdrop(k, ES) == Con{e, t} : List<&2, E.QExpr>}, b: Bool, eb: {SV.mem(SV.nth(own, k), cs) == b : Bool}, ih: SK.Zeros(~F, x, SV.eqs_of.go(t, own, cs, 1n+k)))
  -> SK.Zeros(~F, x, SV.solved.pick(b, e, SV.eqs_of.go(t, own, cs, 1n+k))):
  match b:
    case True{}:
      ((%OW.eqat_of(ES, k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        VR.pz(~F, x, ES, own, R, cls, hz, hd, k, ni_mem(SV.nth(own, k), cs, R, hn, eb))), ih)
    case False{}:
      ih

# the equations of constraints cs, none red: each is 0
def zof.go(~F: O.OField, +x: M.Vec(~F), +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(ES, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(ES, own, R, SV.dropped(cls), cls) == True{} : Bool}, ys: List<&2, E.QExpr>, +cs: List<&2, Nat>, +hn: {SV.none_in(cs, R) == True{} : Bool}, +k: Nat, +hq: {OW.qdrop(k, ES) == ys : List<&2, E.QExpr>}) -> SK.Zeros(~F, x, SV.eqs_of.go(ys, own, cs, k)):
  match ys:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      zof.c(~F, x, ES, own, R, cls, hz, hd, cs, hn, k, e, t, hq, SV.mem(SV.nth(own, k), cs), {==}, zof.go(~F, x, ES, own, R, cls, hz, hd, t, cs, hn, 1n+k, OW.qdrop_step(k, ES, e, t, hq)))


# the premises before i: their equations are 0 and their sides hold
def pre_z(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), 0n)), +hd: {VD.dck(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, 0n) == True{} : Bool}, +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i)) -> SK.Zeros(~F, x, SV.pre_eqs(SK.Sketch{vs, es, rs}, SV.reds(cls), i)):
  zof.go(~F, x, SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), cls, hz, hd, SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i),
    L.band_r(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls)), L.band_r(SV.below(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), SV.band(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls))), L.band_r(SV.distinct(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.band(SV.below(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), SV.band(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls)))), KB.kbp_bool(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i, hK)))),
    0n, {==})

# a kept constraint that is amber: its sides from its refutations
def amb_sides(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), 0n)), +hd: {VD.dck(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, 0n) == True{} : Bool}, +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +hb: {SV.mem(i, SV.ambers(cls)) == True{} : Bool}, +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i)) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, [i])):
  am.c(~F, x, SK.Sketch{vs, es, rs}, SV.reds(cls), i, SV.class_at(cls, i),
    Equal.trans(Bool, SV.is_amber(SV.class_at(cls, i)), SV.mem(i, SV.ambers(cls)), True{}, Equal.sym(Bool, SV.mem(i, SV.ambers(cls)), SV.is_amber(SV.class_at(cls, i)), mem_ambers(cls, i)), hb),
    ack_at(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, i, ha), pre_z(~F, x, vs, es, rs, cls, hz, hd, ha, hen, i, hK), sides_join(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SK.Sketch.sides.ents(es), hS, hen))

def sm.a(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), 0n)), +hd: {VD.dck(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, 0n) == True{} : Bool}, +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hrd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, +ea: {SV.mem(i, SV.reds(cls)) == False{} : Bool}, b: Bool, eb: {SV.mem(i, SV.ambers(cls)) == b : Bool},
  hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, b, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)})), +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), ih: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i))) -> KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i), 1n+i) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i))))
  -> SK.Sides(~F, x, SK.cats(SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)))):
  match b:
    case False{}:
      +hc = hck
      +hsk = sides_l(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)), hc)
      sides_join(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)), hsk,
        ih(sides_r(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)), hc),
          snext.t(~F, x, vs, es, rs, SV.reds(cls), i, dc_kept(vs, es, rs, SV.reds(cls), i, id, k, t, hrd, ea), hS,
            (%Equal.sym(List<&2, SK.Side>, SV.csides(SK.Sketch{vs, es, rs}, [i]), SK.Constraint.sides(es, k), csides_one(vs, es, rs, i, id, k, t, hrd)) : SK.Sides(~F, x, _)
              hsk)),
          knext(vs, es, rs, SV.reds(cls), i, hK)))
    case True{}:
      +hone = amb_sides(~F, x, vs, es, rs, cls, hz, hd, ha, hen, i, eb, hS, hK)
      sides_join(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)),
        (%csides_one(vs, es, rs, i, id, k, t, hrd) : SK.Sides(~F, x, _)
          hone),
        ih(hck, snext.t(~F, x, vs, es, rs, SV.reds(cls), i, dc_kept(vs, es, rs, SV.reds(cls), i, id, k, t, hrd, ea), hS, hone), knext(vs, es, rs, SV.reds(cls), i, hK)))

def sm.k(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), 0n)), +hd: {VD.dck(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, 0n) == True{} : Bool}, +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hrd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, a: Bool, +ea: {SV.mem(i, SV.reds(cls)) == a : Bool},
  hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.mem(i, SV.cat(SV.reds(cls), SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)})), +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), ih: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i))) -> KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i), 1n+i) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i))))
  -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, a, k}, SV.mark.cons(SV.reds(cls), t, 1n+i)})):
  match a:
    case True{}:
      ih((%ea : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.bor(_, SV.mem(i, SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
          (%SP.mem_cat(i, SV.reds(cls), SV.ambers(cls)) : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, _, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
            hck)),
        snext.f(~F, x, vs, es, rs, SV.reds(cls), i, dc_red(SK.Sketch{vs, es, rs}, SV.reds(cls), i, ea), hS), knext(vs, es, rs, SV.reds(cls), i, hK))
    case False{}:
      sm.a(~F, x, vs, es, rs, cls, hz, hd, ha, hen, i, id, k, t, hrd, ea, SV.mem(i, SV.ambers(cls)), {==},
        (%ea : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.bor(_, SV.mem(i, SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
          (%SP.mem_cat(i, SV.reds(cls), SV.ambers(cls)) : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, _, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
            hck)),
        hS, hK, ih)

# the records rt from position i: the side conditions of those not red
# hold, given those of the kept constraints before i
def sm.go(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), 0n)), +hd: {VD.dck(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(SK.Sketch{vs, es, rs}, SV.reds(cls), cls, 0n) == True{} : Bool}, +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), rt: List<&2, SK.Rec>, +i: Nat, +hrd: {KB.rdrop(i, rs) == rt : List<&2, SK.Rec>}, hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rt, i))),
  +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i)) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), rt, i))):
  match rt:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      sm.go(~F, x, vs, es, rs, cls, hz, hd, ha, hen, t, 1n+i, KB.rdrop_step(i, rs, SK.Rec{id, True{}, k}, t, hrd), hck, snext.f(~F, x, vs, es, rs, SV.reds(cls), i, dc_dr(vs, es, rs, SV.reds(cls), i, id, k, t, hrd), hS), knext(vs, es, rs, SV.reds(cls), i, hK))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      sm.k(~F, x, vs, es, rs, cls, hz, hd, ha, hen, i, id, k, t, hrd, SV.mem(i, SV.reds(cls)), {==}, hck, hS, hK, h1 => h2 => h3 => sm.go(~F, x, vs, es, rs, cls, hz, hd, ha, hen, t, 1n+i, KB.rdrop_step(i, rs, SK.Rec{id, False{}, k}, t, hrd), h1, h2, h3))

# where the system solved holds, the drop and amber checks pass, and the
# side conditions of the sketch less its red and amber constraints hold,
# every side condition of the sketch less its red constraints holds
def sides_mark(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))),
  +hd: {VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(sk, SV.reds(cls), cls, 0n) == True{} : Bool},
  +hsc: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)))) -> SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.reds(cls), sk))):
  match sk:
    case SK.Sketch{+vs, +es, +rs}:
      +hen = sides_l(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rs, 0n)), hsc)
      sides_join(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), rs, 0n)), hen,
        sm.go(~F, x, vs, es, rs, cls, hz, hd, ha, hen, rs, 0n, {==}, sides_r(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rs, 0n)), hsc),
          (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 0n), Nil{}, KB.kb_zero(SK.Sketch{vs, es, rs}, SV.reds(cls))) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, _))
            (%Equal.sym(List<&2, SK.Side>, SV.csides.go(es, rs, Nil{}, 0n), Nil{}, csn0(es, rs, 0n)) : SK.Sides(~F, x, _)
              Unit{})),
          (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 0n), Nil{}, KB.kb_zero(SK.Sketch{vs, es, rs}, SV.reds(cls))) : KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), _, 0n)
            KB.kbp_zero(SK.Sketch{vs, es, rs}, SV.reds(cls)))))
