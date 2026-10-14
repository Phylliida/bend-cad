# Proofs of the plan laws (DESIGN §8.4, §8.6; stated in ROADMAP.bend while
# sk-06 is open). Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ./fring.bend as FR
import ./ford.bend as FO
import ./fvec.bend as FV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certpf.bend as CP
import ./real.bend as RL
import ./dmat.bend as DM
import ./banach.bend as BA
import ./plan.bend as PL

# Side conditions
# ---------------

# H c - H r = H (c - r)
def es_lt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K), +r: N.NC(K), hk: {KA.klt(~K, N.nzero(K), KA.ksub(~K, c, r)) == True{} : Bool}) -> O.lt(F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r))):
  RL.lt_rw_r(~F, O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), Equal.sym(O.C(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), N.emap(K, F, H, KA.ksub(~K, c, r)), KA.es(~K, ~F, ~H, c, r)), FO.lt_subst_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), N.e_zero(K, F, H), KA.klt_ok(~K, ~F, ~H, N.nzero(K), KA.ksub(~K, c, r), hk)))

def es_le(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K), +r: N.NC(K), hk: {KA.kle(~K, N.nzero(K), KA.ksub(~K, c, r)) == True{} : Bool}) -> O.le(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r))):
  FV.le_rw_r(~F, O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), Equal.sym(O.C(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), N.emap(K, F, H, KA.ksub(~K, c, r)), KA.es(~K, ~F, ~H, c, r)), RL.le_rw_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), N.e_zero(K, F, H), KA.kle_ok(~K, ~F, ~H, N.nzero(K), KA.ksub(~K, c, r), hk)))

# v in the ball (c, r) with c - r > 0 (or >= 0) is positive (not negative)
def bin_pos(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +v: O.C(F), b: KB.KB<K>, hb: KB.bin(~K, ~F, ~H, v, b), hk: {KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, b), KB.KB.r(K, b))) == True{} : Bool}) -> O.lt(F, O.zero(F), v):
  match b:
    case KB.KB{+c, +r}:
      FO.lt_le_trans(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), v, es_lt(~K, ~F, ~H, c, r, hk), BA.box_lo(~F, v, N.emap(K, F, H, c), N.emap(K, F, H, r), hb))

def bin_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +v: O.C(F), b: KB.KB<K>, hb: KB.bin(~K, ~F, ~H, v, b), hk: {KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, b), KB.KB.r(K, b))) == True{} : Bool}) -> O.le(~F, O.zero(F), v):
  match b:
    case KB.KB{+c, +r}:
      DM.le_trans(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), v, es_le(~K, ~F, ~H, c, r, hk), BA.box_lo(~F, v, N.emap(K, F, H, c), N.emap(K, F, H, r), hb))

def sides_pf(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), +box: List<&2, KB.KB<K>>, +hx: KB.inbox(~K, ~F, ~H, x, box), ss: List<&2, SK.Side>, +ok: {PL.sides_ok(~K, box, ss) == True{} : Bool}) -> SK.Sides(~F, x, ss):
  match ss:
    case Nil{}:
      Unit{}
    case Con{SK.Gt0{+e}, +t}:
      +h1 = KA.band_l(PL.side_ok(~K, box, SK.Gt0{e}), PL.sides_ok(~K, box, t), ok)
      +hh = KA.band_l(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)
      (bin_pos(~K, ~F, ~H, O.eval(~F, x, e), KB.kball(~K, box, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), KA.band_r(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)), sides_pf(~K, ~F, ~H, x, box, hx, t, KA.band_r(PL.side_ok(~K, box, SK.Gt0{e}), PL.sides_ok(~K, box, t), ok)))
    case Con{SK.Ge0{+e}, +t}:
      +h1 = KA.band_l(PL.side_ok(~K, box, SK.Ge0{e}), PL.sides_ok(~K, box, t), ok)
      +hh = KA.band_l(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)
      (bin_nn(~K, ~F, ~H, O.eval(~F, x, e), KB.kball(~K, box, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), KA.band_r(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)), sides_pf(~K, ~F, ~H, x, box, hx, t, KA.band_r(PL.side_ok(~K, box, SK.Ge0{e}), PL.sides_ok(~K, box, t), ok)))

def box_sides.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K), +ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> SK.Sides(~F, x, sides):
  (hl, hr) = h
  +box = CK.zipb(~K, gc, gr)
  sides_pf(~K, ~F, ~H, x, box, CP.rbnd_inbox(~K, ~F, ~H, x, gc, gr, hr, KA.kvle_ok(~K, ~F, ~H, Nil{}, gr, KA.band_l(KA.kvle(~K, Nil{}, gr), PL.sides_ok(~K, box, sides), ok))), sides, KA.band_r(KA.kvle(~K, Nil{}, gr), PL.sides_ok(~K, box, sides), ok))

# LAW box_sides: every point of the box meets the certified side conditions
def box_sides(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K), ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> SK.Sides(~F, x, sides):
  box_sides.go(~K, ~F, ~H, sides, gc, gr, ok, x, h)
