# bend-cad: the blocks in turn, for solve_complete (DESIGN §10.4 "C6
# plan", C6c). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/pblkpf.draft lib/pblkpf.bend
#
# lib/numer.bend's pblocks builds the box in block order, each block
# reading its parameters' balls from the box so far and appending its
# own. Here: the solver's dyadic list operations agree with the checker's
# K-generic ones; pblocks' accumulator can be moved out (pb_acc); and, by
# induction over the solver's structure, every block gets block_sc's
# hypotheses (lib/scalepf.bend), so pblocks returns PBOk with the plan
# checker's walk accepting the final box, x in the box, and radii at most
# h times the chain T_k.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./kball.bend as KB
import ./kinst.bend as KI
import ./certdef.bend as C
import ./cert.bend as CK
import ./slope.bend as SL
import ./numer.bend as NU
import ./struct.bend as ST
import ./plan.bend as PL
import ./planpf.bend as PP
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./real.bend as RL
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./listpf.bend as L
import ./gjpf.bend as GJ
import ./normpf.bend as NP
import ./apxpf.bend as AP
import ./bndpf.bend as BP
import ./nwtpf.bend as NW
import ./keptpf.bend as KP
import ./structpf.bend as SP
import ./binvpf.bend as BI
import ./locpf.bend as LC
import ./nat.bend as LN
import ./tarjanpf.bend as TJ
import ./maxpf.bend as MX

def absurd(-A: Type, x: Empty) -> A:
  match x:


# The solver's lists, read by the checker
# ---------------------------------------

def dl_kl(xs: List<&2, S.D>, k: Nat) -> {NU.dlook(xs, k) == KB.klook(~KI.dnum(), xs, k) : S.D}:
  match xs k:
    case Nil{} k:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      dl_kl(t, j)

def dapp_ka(xs: List<&2, S.D>, +ys: List<&2, S.D>) -> {NU.dapp(xs, ys) == KA.kapp(~KI.dnum(), xs, ys) : List<&2, S.D>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %dapp_ka(t, ys) : {Con{h, NU.dapp(t, ys)} == Con{h, _} : List<&2, S.D>}
      {==}

def dtake_kt(n: Nat, xs: List<&2, S.D>) -> {NU.dtake(n, xs) == PL.ktake(~KI.dnum(), n, xs) : List<&2, S.D>}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{+h, t}:
      %dtake_kt(m, t) : {Con{h, NU.dtake(m, t)} == Con{h, _} : List<&2, S.D>}
      {==}

def ddrop_kd(n: Nat, xs: List<&2, S.D>) -> {NU.ddrop(n, xs) == PL.kdrop(~KI.dnum(), n, xs) : List<&2, S.D>}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{h, t}:
      ddrop_kd(m, t)

def klen_kapp(~K: N.Num, u: N.KVec(~K), +w: N.KVec(~K)) -> {KA.klen(~K, KA.kapp(~K, u, w)) == Nat.add(KA.klen(~K, u), KA.klen(~K, w)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{a, t}:
      %klen_kapp(~K, t, w) : {1n+KA.klen(~K, KA.kapp(~K, t, w)) == 1n+_ : Nat}
      {==}

# the first klen(u) entries of u ++ w are u, and the rest w
def kt_app(~K: N.Num, u: N.KVec(~K), +w: N.KVec(~K)) -> {PL.ktake(~K, KA.klen(~K, u), KA.kapp(~K, u, w)) == u : N.KVec(~K)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, t}:
      %kt_app(~K, t, w) : {Con{a, PL.ktake(~K, KA.klen(~K, t), KA.kapp(~K, t, w))} == Con{a, _} : N.KVec(~K)}
      {==}

def kd_app(~K: N.Num, u: N.KVec(~K), +w: N.KVec(~K)) -> {PL.kdrop(~K, KA.klen(~K, u), KA.kapp(~K, u, w)) == w : N.KVec(~K)}:
  match u:
    case Nil{}:
      {==}
    case Con{a, t}:
      kd_app(~K, t, w)

def kfit_len(~K: N.Num, u: N.KVec(~K)) -> {KA.kfit(~K, KA.klen(~K, u), u) == u : N.KVec(~K)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, t}:
      %kfit_len(~K, t) : {Con{a, KA.kfit(~K, KA.klen(~K, t), t)} == Con{a, _} : N.KVec(~K)}
      {==}

def kt_len(~K: N.Num, u: N.KVec(~K)) -> {PL.ktake(~K, KA.klen(~K, u), u) == u : N.KVec(~K)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, t}:
      %kt_len(~K, t) : {Con{a, PL.ktake(~K, KA.klen(~K, t), t)} == Con{a, _} : N.KVec(~K)}
      {==}

# Equal dyadics, as the checker sees them
# ---------------------------------------

def keq_refl.go(~F: O.OField, +a: S.D, c: Cmp, h: N.cmeans(F, c, M.ofd(~F, a), M.ofd(~F, a))) -> {PL.keq.go(c) == True{} : Bool}:
  match c:
    case LT{}:
      absurd({False{} == True{} : Bool}, O.lt_irrefl(F)(M.ofd(~F, a))(h))
    case EQ{}:
      {==}
    case GT{}:
      absurd({False{} == True{} : Bool}, O.lt_irrefl(F)(M.ofd(~F, a))(h))

def keq_refl(~F: O.OField, +a: S.D) -> {PL.keq(~KI.dnum(), a, a) == True{} : Bool}:
  keq_refl.go(~F, a, KI.dcmp(a, a), KI.dcmp_sound(~F, a, a))

def kband_i(a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {KA.band(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      absurd({KA.band(False{}, b) == True{} : Bool}, KA.ft(ha))

def kveq_refl(~F: O.OField, u: List<&2, S.D>) -> {PL.kveq(~KI.dnum(), u, u) == True{} : Bool}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      kband_i(PL.keq(~KI.dnum(), a, a), PL.kveq(~KI.dnum(), t, t), keq_refl(~F, a), kveq_refl(~F, t))

# |c - c| + r <= r
def kabs_z.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cmp, +a: N.NC(K), h: {N.emap(K, F, H, a) == O.zero(F) : O.C(F)}) -> {N.emap(K, F, H, KA.kabs.go(~K, c, a)) == O.zero(F) : O.C(F)}:
  match c:
    case LT{}:
      %KA.en(~K, ~F, ~H, a) : {_ == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, a), O.zero(F), h) : {O.neg(F, _) == O.zero(F) : O.C(F)}
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))
    case EQ{}:
      h
    case GT{}:
      h

def pc_refl(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +c: S.D, +r: S.D) -> {KA.kle(~KI.dnum(), N.nadd(KI.dnum(), KA.kabs(~KI.dnum(), KA.ksub(~KI.dnum(), c, c)), r), r) == True{} : Bool}:
  +z = KA.kabs(~KI.dnum(), KA.ksub(~KI.dnum(), c, c))
  +hz = kabs_z.go(~KI.dnum(), ~F, ~H, N.ncmp(KI.dnum(), KA.ksub(~KI.dnum(), c, c), N.nzero(KI.dnum())), KA.ksub(~KI.dnum(), c, c), (%KA.es(~KI.dnum(), ~F, ~H, c, c) : {_ == O.zero(F) : O.C(F)}
    FO.sub_of_eq(~F, N.emap(KI.dnum(), F, H, c), N.emap(KI.dnum(), F, H, c), {==})))
  AP.kle_of(~KI.dnum(), ~F, ~H, N.nadd(KI.dnum(), z, r), r, (%KA.ea(~KI.dnum(), ~F, ~H, z, r) : O.le(~F, _, N.emap(KI.dnum(), F, H, r))
    (%Equal.sym(O.C(F), N.emap(KI.dnum(), F, H, z), O.zero(F), hz) : O.le(~F, O.add(F, _, N.emap(KI.dnum(), F, H, r)), N.emap(KI.dnum(), F, H, r))
    RL.le_rw_l(~F, N.emap(KI.dnum(), F, H, r), O.add(F, O.zero(F), N.emap(KI.dnum(), F, H, r)), N.emap(KI.dnum(), F, H, r), FR.fring_eq(~F, [N.emap(KI.dnum(), F, H, r)], E.ZVar{0n}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, {==}), FO.le_refl(~F, N.emap(KI.dnum(), F, H, r))))))

# pblocks' accumulator, moved out
# --------------------------------

def pbacc(acc: List<&2, PL.PBlock<KI.dnum()>>, r: NU.PBR) -> NU.PBR:
  match r:
    case NU.PBOk{NU.PB{bs, gc, gr}}:
      NU.PBOk{NU.PB{NU.revpb.go(acc, bs), gc, gr}}
    case NU.PBRetry{}:
      NU.PBRetry{}
    case NU.PBStop{}:
      NU.PBStop{}

def pbacc_con(+b: PL.PBlock<KI.dnum()>, +acc: List<&2, PL.PBlock<KI.dnum()>>, r: NU.PBR) -> {pbacc(Con{b, acc}, r) == pbacc(acc, pbacc(Con{b, Nil{}}, r)) : NU.PBR}:
  match r:
    case NU.PBOk{NU.PB{bs, gc, gr}}:
      {==}
    case NU.PBRetry{}:
      {==}
    case NU.PBStop{}:
      {==}

def pb_acc(bs: List<&2, ST.SkB>, cur: NU.BR, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +acc: List<&2, PL.PBlock<KI.dnum()>>) -> {NU.pblocks(bs, cur, sys, g0b, p, o, gc, gr, acc) == pbacc(acc, NU.pblocks(bs, cur, sys, g0b, p, o, gc, gr, Nil{})) : NU.PBR}:
  match bs cur:
    case Nil{} cur:
      {==}
    case Con{ST.SkB{es, vs, +pars}, +t} NU.BRetry{}:
      {==}
    case Con{ST.SkB{es, vs, +pars}, +t} NU.BStop{}:
      {==}
    case Con{ST.SkB{es, vs, +pars}, +t} NU.BOk{+c}:
      +n = ST.len(es)
      +sys2 = PL.dropq(n, sys)
      +gc2 = NU.dapp(gc, NU.cert.yc(c))
      +gr2 = NU.dapp(gr, NU.dtake(n, NU.cert.yr(c)))
      +cur2 = NU.bcert(t, sys2, g0b, p, Nat.add(o, n), gc2, gr2)
      +b = {PL.PBlock{n, pars, c} : PL.PBlock<KI.dnum()>}
      +r0 = NU.pblocks(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Nil{})
      Equal.trans(NU.PBR, NU.pblocks(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{b, acc}), pbacc(Con{b, acc}, r0), pbacc(acc, NU.pblocks(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{b, Nil{}})),
        pb_acc(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{b, acc}),
        (%Equal.sym(NU.PBR, NU.pblocks(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{b, Nil{}}), pbacc(Con{b, Nil{}}, r0), pb_acc(t, cur2, sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{b, Nil{}})) : {pbacc(Con{b, acc}, r0) == pbacc(acc, _) : NU.PBR}
        pbacc_con(b, acc, r0)))

# The block's equations
# ---------------------

def reorder_app(+vp: List<&2, Nat>, +full: List<&2, E.QExpr>, a: List<&2, Nat>, +b: List<&2, Nat>) -> {PL.reorder(vp, full, ST.app(a, b)) == BI.eapp(PL.reorder(vp, full, a), PL.reorder(vp, full, b)) : List<&2, E.QExpr>}:
  match a:
    case Nil{}:
      {==}
    case Con{+j, t}:
      %reorder_app(vp, full, t, b) : {Con{PL.rnv(vp, PL.eqget(full, j)), PL.reorder(vp, full, ST.app(t, b))} == Con{PL.rnv(vp, PL.eqget(full, j)), _} : List<&2, E.QExpr>}
      {==}

def eqlen_reorder(+vp: List<&2, Nat>, +full: List<&2, E.QExpr>, a: List<&2, Nat>) -> {CK.eqlen(PL.reorder(vp, full, a)) == ST.len(a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{j, t}:
      %eqlen_reorder(vp, full, t) : {1n+CK.eqlen(PL.reorder(vp, full, t)) == 1n+_ : Nat}
      {==}

def takeq_eapp(a: List<&2, E.QExpr>, +b: List<&2, E.QExpr>) -> {PL.takeq(CK.eqlen(a), BI.eapp(a, b)) == a : List<&2, E.QExpr>}:
  match a:
    case Nil{}:
      {==}
    case Con{+e, t}:
      %takeq_eapp(t, b) : {Con{e, PL.takeq(CK.eqlen(t), BI.eapp(t, b))} == Con{e, _} : List<&2, E.QExpr>}
      {==}

def dropq_eapp(a: List<&2, E.QExpr>, +b: List<&2, E.QExpr>) -> {PL.dropq(CK.eqlen(a), BI.eapp(a, b)) == b : List<&2, E.QExpr>}:
  match a:
    case Nil{}:
      {==}
    case Con{e, t}:
      dropq_eapp(t, b)

def eqlen_renames(+o: Nat, +n: Nat, +pars: List<&2, Nat>, es: List<&2, E.QExpr>) -> {CK.eqlen(PL.renames(o, n, pars, es)) == CK.eqlen(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      %eqlen_renames(o, n, pars, t) : {1n+CK.eqlen(PL.renames(o, n, pars, t)) == 1n+_ : Nat}
      {==}


def nq_eq(+es: List<&2, Nat>, +good: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>) -> {ST.len(ST.positions(es, good)) == CK.eqlen(PL.reorder(vp, full, es)) : Nat}:
  Equal.trans(Nat, ST.len(ST.positions(es, good)), ST.len(es), CK.eqlen(PL.reorder(vp, full, es)), SP.positions_len(es, good), Equal.sym(Nat, CK.eqlen(PL.reorder(vp, full, es)), ST.len(es), eqlen_reorder(vp, full, es)))

# the block's n equations, and the rest
def tq_eq(+vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +es: List<&2, Nat>, +rest: List<&2, Nat>, +good: List<&2, Nat>) -> {PL.takeq(ST.len(ST.positions(es, good)), PL.reorder(vp, full, ST.app(es, rest))) == PL.reorder(vp, full, es) : List<&2, E.QExpr>}:
  %Equal.sym(Nat, ST.len(ST.positions(es, good)), CK.eqlen(PL.reorder(vp, full, es)), nq_eq(es, good, vp, full)) : {PL.takeq(_, PL.reorder(vp, full, ST.app(es, rest))) == PL.reorder(vp, full, es) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, PL.reorder(vp, full, ST.app(es, rest)), BI.eapp(PL.reorder(vp, full, es), PL.reorder(vp, full, rest)), reorder_app(vp, full, es, rest)) : {PL.takeq(CK.eqlen(PL.reorder(vp, full, es)), _) == PL.reorder(vp, full, es) : List<&2, E.QExpr>}
  takeq_eapp(PL.reorder(vp, full, es), PL.reorder(vp, full, rest))

def dq_eq(+vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +es: List<&2, Nat>, +rest: List<&2, Nat>, +good: List<&2, Nat>) -> {PL.dropq(ST.len(ST.positions(es, good)), PL.reorder(vp, full, ST.app(es, rest))) == PL.reorder(vp, full, rest) : List<&2, E.QExpr>}:
  %Equal.sym(Nat, ST.len(ST.positions(es, good)), CK.eqlen(PL.reorder(vp, full, es)), nq_eq(es, good, vp, full)) : {PL.dropq(_, PL.reorder(vp, full, ST.app(es, rest))) == PL.reorder(vp, full, rest) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, PL.reorder(vp, full, ST.app(es, rest)), BI.eapp(PL.reorder(vp, full, es), PL.reorder(vp, full, rest)), reorder_app(vp, full, es, rest)) : {PL.dropq(CK.eqlen(PL.reorder(vp, full, es)), _) == PL.reorder(vp, full, rest) : List<&2, E.QExpr>}
  dropq_eapp(PL.reorder(vp, full, es), PL.reorder(vp, full, rest))

# Constants held exactly
# ----------------------

def ps.go(+z: S.Z, m: Maybe<&2, Nat>, ih: {KB.held.go(~KI.dnum(), KI.dofq.go(z, m)) == True{} : Bool}) -> {KB.held.go(~KI.dnum(), KI.dofq.go(z, KI.plog.succ(m))) == True{} : Bool}:
  match m:
    case None{}:
      absurd({KB.held.go(~KI.dnum(), KI.dofq.go(z, KI.plog.succ(None{}))) == True{} : Bool}, KA.ft(ih))
    case Some{e}:
      {==}

# a power-of-two denominator is held
def ps(+z: S.Z, p: S.Pos, h: {SV.pow2(p) == True{} : Bool}) -> {KB.held.go(~KI.dnum(), KI.dofq.go(z, KI.plog(p))) == True{} : Bool}:
  match p:
    case S.XH{}:
      {==}
    case S.XO{+q}:
      ps.go(z, KI.plog(q), ps(z, q, h))
    case S.XI{q}:
      absurd({KB.held.go(~KI.dnum(), KI.dofq.go(z, KI.plog(S.XI{q}))) == True{} : Bool}, KA.ft(h))

def held_c(q: S.Q, h: {SV.dyconst(E.QCst{q}) == True{} : Bool}) -> {KB.held(~KI.dnum(), E.QCst{q}) == True{} : Bool}:
  match q:
    case S.Q{+z, +d}:
      ps(z, d, h)


def held_rn(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +vp: List<&2, Nat>, e: E.QExpr, +h: {SV.dyconst(e) == True{} : Bool}) -> {KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, e))) == True{} : Bool}:
  match e:
    case E.QVar{v}:
      {==}
    case E.QCst{+q}:
      held_c(q, h)
    case E.QAdd{+a, +b}:
      kband_i(KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, a))), KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, b))), held_rn(o, n, pars, vp, a, L.band_l(SV.dyconst(a), SV.dyconst(b), h)), held_rn(o, n, pars, vp, b, L.band_r(SV.dyconst(a), SV.dyconst(b), h)))
    case E.QSub{+a, +b}:
      kband_i(KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, a))), KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, b))), held_rn(o, n, pars, vp, a, L.band_l(SV.dyconst(a), SV.dyconst(b), h)), held_rn(o, n, pars, vp, b, L.band_r(SV.dyconst(a), SV.dyconst(b), h)))
    case E.QMul{+a, +b}:
      kband_i(KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, a))), KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, b))), held_rn(o, n, pars, vp, a, L.band_l(SV.dyconst(a), SV.dyconst(b), h)), held_rn(o, n, pars, vp, b, L.band_r(SV.dyconst(a), SV.dyconst(b), h)))
    case E.QNeg{+a}:
      held_rn(o, n, pars, vp, a, h)

def dyget(full: List<&2, E.QExpr>, j: Nat, h: {SV.dyeqs(full) == True{} : Bool}) -> {SV.dyconst(PL.eqget(full, j)) == True{} : Bool}:
  match full j:
    case Nil{} j:
      {==}
    case Con{+e, +t} 0n:
      L.band_l(SV.dyconst(e), SV.dyeqs(t), h)
    case Con{+e, +t} 1n+k:
      dyget(t, k, L.band_r(SV.dyconst(e), SV.dyeqs(t), h))

def held_blk(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +hd: {SV.dyeqs(full) == True{} : Bool}, es: List<&2, Nat>) -> {CK.allheld(~KI.dnum(), PL.renames(o, n, pars, PL.reorder(vp, full, es))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      kband_i(KB.held(~KI.dnum(), PL.rename(o, n, pars, PL.rnv(vp, PL.eqget(full, j)))), CK.allheld(~KI.dnum(), PL.renames(o, n, pars, PL.reorder(vp, full, t))), held_rn(o, n, pars, vp, PL.eqget(full, j), dyget(full, j, hd)), held_blk(o, n, pars, vp, full, hd, t))

# Renumbered equations stay below n + m
# -------------------------------------

# v < o: not o <= v
def ren_nlt(o: Nat, v: Nat, h: {KA.natle(1n+v, o) == True{} : Bool}) -> {KA.natle(o, v) == False{} : Bool}:
  match o v:
    case 0n v:
      absurd({KA.natle(0n, v) == False{} : Bool}, KA.ft(h))
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      ren_nlt(i, j, h)

def ren_var.go(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +v: Nat, b: Bool, e: {KA.natle(1n+v, o) == b : Bool}, hb: {KA.natle(1n+v, Nat.add(o, n)) == True{} : Bool}, hc: {SV.bor(KA.natle(o, v), SV.mem(v, pars)) == True{} : Bool}) -> {KA.natle(1n+PL.loc.go(b, o, n, pars, v), Nat.add(n, PL.nlen(pars))) == True{} : Bool}:
  match b:
    case True{}:
      LC.succ_le(n, PL.pos(v, pars), Nat.add(n, PL.nlen(pars)), L.le_add_mono(n, 1n+PL.pos(v, pars), PL.nlen(pars), LC.pos_lt(v, pars, L.bor_rf(KA.natle(o, v), SV.mem(v, pars), hc, ren_nlt(o, v, e)))))
    case False{}:
      L.le_trans(1n+PL.minus(o, v), n, Nat.add(n, PL.nlen(pars)), PP.natle_minus(o, v, n, hb, e), L.le_add_r(n, PL.nlen(pars)))

def ren_below1(+o: Nat, +n: Nat, +pars: List<&2, Nat>, r: E.QExpr, +hb: {SL.below(Nat.add(o, n), r) == True{} : Bool}, +hc: {SP.ecov(o, pars, r) == True{} : Bool}) -> {SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, r)) == True{} : Bool}:
  match r:
    case E.QVar{+v}:
      ren_var.go(o, n, pars, v, KA.natle(1n+v, o), {==}, hb, hc)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      kband_i(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), ren_below1(o, n, pars, a, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_l(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)), ren_below1(o, n, pars, b, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_r(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)))
    case E.QSub{+a, +b}:
      kband_i(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), ren_below1(o, n, pars, a, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_l(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)), ren_below1(o, n, pars, b, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_r(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)))
    case E.QMul{+a, +b}:
      kband_i(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), ren_below1(o, n, pars, a, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_l(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)), ren_below1(o, n, pars, b, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), L.band_r(SP.ecov(o, pars, a), SP.ecov(o, pars, b), hc)))
    case E.QNeg{+a}:
      ren_below1(o, n, pars, a, hb, hc)

def ren_below(+o: Nat, +n: Nat, +pars: List<&2, Nat>, rs: List<&2, E.QExpr>, +hb: {PL.eqs_below(Nat.add(o, n), rs) == True{} : Bool}, +hc: {SP.ecovs(o, pars, rs) == True{} : Bool}) -> {CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      kband_i(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, r)), CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, t)), ren_below1(o, n, pars, r, KA.band_l(SL.below(Nat.add(o, n), r), PL.eqs_below(Nat.add(o, n), t), hb), L.band_l(SP.ecov(o, pars, r), SP.ecovs(o, pars, t), hc)), ren_below(o, n, pars, t, KA.band_r(SL.below(Nat.add(o, n), r), PL.eqs_below(Nat.add(o, n), t), hb), L.band_r(SP.ecov(o, pars, r), SP.ecovs(o, pars, t), hc)))

# The block's equations vanish at x
# ---------------------------------

def zat.go(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +j: Nat, +g: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(j, g) == b : Bool}, hm: {SV.bor(b, SV.mem(j, t)) == True{} : Bool}, hg: {O.eval(~F, x, PL.eqget(full, g)) == O.zero(F) : O.C(F)}, ih: {SV.mem(j, t) == True{} : Bool} -> {O.eval(~F, x, PL.eqget(full, j)) == O.zero(F) : O.C(F)}) -> {O.eval(~F, x, PL.eqget(full, j)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, j, g, L.eq_ok(j, g, e)) : {O.eval(~F, x, PL.eqget(full, _)) == O.zero(F) : O.C(F)}
      hg
    case False{}:
      ih(hm)

# x solves the kept equations, so each kept one
def zat(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, good: List<&2, Nat>, +j: Nat, h: SK.Zeros(~F, x, KP.pickk(full, 0n, good)), hj: {SV.mem(j, good) == True{} : Bool}) -> {O.eval(~F, x, PL.eqget(full, j)) == O.zero(F) : O.C(F)}:
  match good:
    case Nil{}:
      absurd({O.eval(~F, x, PL.eqget(full, j)) == O.zero(F) : O.C(F)}, L.mem_nil(j, hj))
    case Con{+g, +t}:
      match h:
        case (hg, ht):
          zat.go(~F, x, full, j, g, t, SV.eq(j, g), {==}, hj, hg, hm => zat(~F, x, full, t, j, ht, hm))


def zero_rw(~F: O.OField, +a: O.C(F), +b: O.C(F), e: {a == b : O.C(F)}, h: {b == O.zero(F) : O.C(F)}) -> {a == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), a, b, e) : {_ == O.zero(F) : O.C(F)}
  h

# the block's equations in block order vanish at X's first o + n entries
def zeros_blk(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +hzg: SK.Zeros(~F, x, KP.pickk(full, 0n, good)), es: List<&2, Nat>, +hes: {L.subl(es, good) == True{} : Bool}, +hr: {LC.rowsok(full, vp, o, n, pars, es) == True{} : Bool}, +hX: {KA.natle(Nat.add(o, n), M.len(~F, LC.xperm(~F, x, vp))) == True{} : Bool}) -> SK.Zeros(~F, C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PL.reorder(vp, full, es)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+j, +t}:
      +rj = PL.rnv(vp, PL.eqget(full, j))
      +h1 = L.band_l(SV.inside(PL.eqget(full, j), vp), SV.band(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(full, vp, o, n, pars, t))), hr)
      +h2 = L.band_r(SV.inside(PL.eqget(full, j), vp), SV.band(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(full, vp, o, n, pars, t))), hr)
      +h3 = L.band_l(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(full, vp, o, n, pars, t)), h2)
      +h4 = L.band_r(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(full, vp, o, n, pars, t), L.band_r(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(full, vp, o, n, pars, t)), h2))
      (zero_rw(~F, O.eval(~F, C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), rj), O.eval(~F, x, PL.eqget(full, j)),
        (%Equal.sym(M.Vec(~F), C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.ftake(~F, Nat.add(o, n), LC.xperm(~F, x, vp)), LC.app_take(~F, o, n, LC.xperm(~F, x, vp))) : {O.eval(~F, _, rj) == O.eval(~F, x, PL.eqget(full, j)) : O.C(F)}
        Equal.trans(O.C(F), O.eval(~F, PP.ftake(~F, Nat.add(o, n), LC.xperm(~F, x, vp)), rj), O.eval(~F, LC.xperm(~F, x, vp), rj), O.eval(~F, x, PL.eqget(full, j)), LC.eval_ftake(~F, LC.xperm(~F, x, vp), Nat.add(o, n), hX, rj, h3), LC.eval_rnv(~F, x, vp, PL.eqget(full, j), h1))),
        zat(~F, x, full, good, j, hzg, L.subl_hd(j, t, good, hes))),
      zeros_blk(~F, x, vp, o, n, pars, full, good, hzg, t, L.subl_tl(j, t, good, hes), h4, hX))

def zeros_fv(~F: O.OField, +env: M.Vec(~F), es: List<&2, E.QExpr>, h: SK.Zeros(~F, env, es)) -> {C.fvals(~F, es, env) == GJ.zeros(~F, CK.eqlen(es)) : M.Vec(~F)}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      match h:
        case (he, ht):
          LC.con_eq(~F, O.eval(~F, env, e), O.zero(F), C.fvals(~F, t, env), GJ.zeros(~F, CK.eqlen(t)), he, zeros_fv(~F, env, t, ht))

# Slope grades
# ------------

def mj_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), e: E.QExpr) -> O.le(~F, O.zero(F), BP.mj(~F, bb, e)):
  match e:
    case E.QVar{i}:
      hb
    case E.QCst{+q}:
      FV.fabs_nn(~F, O.ofq(~F, q))
    case E.QAdd{+a, +b}:
      FO.nonneg_add(~F, BP.mj(~F, bb, a), BP.mj(~F, bb, b), mj_nn(~F, bb, hb, a), mj_nn(~F, bb, hb, b))
    case E.QSub{+a, +b}:
      FO.nonneg_add(~F, BP.mj(~F, bb, a), BP.mj(~F, bb, b), mj_nn(~F, bb, hb, a), mj_nn(~F, bb, hb, b))
    case E.QMul{+a, +b}:
      FO.mul_nonneg(~F, BP.mj(~F, bb, a), BP.mj(~F, bb, b), mj_nn(~F, bb, hb, a), mj_nn(~F, bb, hb, b))
    case E.QNeg{+a}:
      mj_nn(~F, bb, hb, a)

def lp_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), e: E.QExpr) -> O.le(~F, O.zero(F), BP.lp(~F, bb, e)):
  match e:
    case E.QVar{i}:
      NP.one_nn(~F)
    case E.QCst{q}:
      FO.le_refl(~F, O.zero(F))
    case E.QAdd{+a, +b}:
      FO.nonneg_add(~F, BP.lp(~F, bb, a), BP.lp(~F, bb, b), lp_nn(~F, bb, hb, a), lp_nn(~F, bb, hb, b))
    case E.QSub{+a, +b}:
      FO.nonneg_add(~F, BP.lp(~F, bb, a), BP.lp(~F, bb, b), lp_nn(~F, bb, hb, a), lp_nn(~F, bb, hb, b))
    case E.QMul{+a, +b}:
      FO.nonneg_add(~F, O.mul(F, BP.mj(~F, bb, a), BP.lp(~F, bb, b)), O.mul(F, BP.mj(~F, bb, b), BP.lp(~F, bb, a)), FO.mul_nonneg(~F, BP.mj(~F, bb, a), BP.lp(~F, bb, b), mj_nn(~F, bb, hb, a), lp_nn(~F, bb, hb, b)), FO.mul_nonneg(~F, BP.mj(~F, bb, b), BP.lp(~F, bb, a), mj_nn(~F, bb, hb, b), lp_nn(~F, bb, hb, a)))
    case E.QNeg{+a}:
      lp_nn(~F, bb, hb, a)

def ms_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), e: E.QExpr) -> O.le(~F, O.zero(F), BP.ms(~F, bb, e)):
  match e:
    case E.QVar{i}:
      NP.one_nn(~F)
    case E.QCst{q}:
      FO.le_refl(~F, O.zero(F))
    case E.QAdd{+a, +b}:
      FO.nonneg_add(~F, BP.ms(~F, bb, a), BP.ms(~F, bb, b), ms_nn(~F, bb, hb, a), ms_nn(~F, bb, hb, b))
    case E.QSub{+a, +b}:
      FO.nonneg_add(~F, BP.ms(~F, bb, a), BP.ms(~F, bb, b), ms_nn(~F, bb, hb, a), ms_nn(~F, bb, hb, b))
    case E.QMul{+a, +b}:
      FO.nonneg_add(~F, O.mul(F, BP.mj(~F, bb, a), BP.ms(~F, bb, b)), O.mul(F, BP.mj(~F, bb, b), BP.ms(~F, bb, a)), FO.mul_nonneg(~F, BP.mj(~F, bb, a), BP.ms(~F, bb, b), mj_nn(~F, bb, hb, a), ms_nn(~F, bb, hb, b)), FO.mul_nonneg(~F, BP.mj(~F, bb, b), BP.ms(~F, bb, a), mj_nn(~F, bb, hb, b), ms_nn(~F, bb, hb, a)))
    case E.QNeg{+a}:
      ms_nn(~F, bb, hb, a)

def ls_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), e: E.QExpr) -> O.le(~F, O.zero(F), BP.ls(~F, bb, e)):
  match e:
    case E.QVar{i}:
      FO.le_refl(~F, O.zero(F))
    case E.QCst{q}:
      FO.le_refl(~F, O.zero(F))
    case E.QAdd{+a, +b}:
      FO.nonneg_add(~F, BP.ls(~F, bb, a), BP.ls(~F, bb, b), ls_nn(~F, bb, hb, a), ls_nn(~F, bb, hb, b))
    case E.QSub{+a, +b}:
      FO.nonneg_add(~F, BP.ls(~F, bb, a), BP.ls(~F, bb, b), ls_nn(~F, bb, hb, a), ls_nn(~F, bb, hb, b))
    case E.QMul{+a, +b}:
      FO.nonneg_add(~F, O.add(F, O.mul(F, BP.mj(~F, bb, a), BP.ls(~F, bb, b)), O.mul(F, BP.ms(~F, bb, b), BP.lp(~F, bb, a))), O.add(F, O.mul(F, BP.mj(~F, bb, b), BP.ls(~F, bb, a)), O.mul(F, BP.ms(~F, bb, a), BP.lp(~F, bb, b))), FO.nonneg_add(~F, O.mul(F, BP.mj(~F, bb, a), BP.ls(~F, bb, b)), O.mul(F, BP.ms(~F, bb, b), BP.lp(~F, bb, a)), FO.mul_nonneg(~F, BP.mj(~F, bb, a), BP.ls(~F, bb, b), mj_nn(~F, bb, hb, a), ls_nn(~F, bb, hb, b)), FO.mul_nonneg(~F, BP.ms(~F, bb, b), BP.lp(~F, bb, a), ms_nn(~F, bb, hb, b), lp_nn(~F, bb, hb, a))), FO.nonneg_add(~F, O.mul(F, BP.mj(~F, bb, b), BP.ls(~F, bb, a)), O.mul(F, BP.ms(~F, bb, a), BP.lp(~F, bb, b)), FO.mul_nonneg(~F, BP.mj(~F, bb, b), BP.ls(~F, bb, a), mj_nn(~F, bb, hb, b), ls_nn(~F, bb, hb, a)), FO.mul_nonneg(~F, BP.ms(~F, bb, a), BP.lp(~F, bb, b), ms_nn(~F, bb, hb, a), lp_nn(~F, bb, hb, b))))
    case E.QNeg{+a}:
      ls_nn(~F, bb, hb, a)

# the block's Lambda and M: its equations' grades summed
def lsum(~F: O.OField, +bb: O.C(F), es: List<&2, E.QExpr>) -> O.C(F):
  match es:
    case Nil{}:
      O.zero(F)
    case Con{e, t}:
      O.add(F, BP.ls(~F, bb, e), lsum(~F, bb, t))

def msum(~F: O.OField, +bb: O.C(F), es: List<&2, E.QExpr>) -> O.C(F):
  match es:
    case Nil{}:
      O.zero(F)
    case Con{e, t}:
      O.add(F, BP.ms(~F, bb, e), msum(~F, bb, t))

def lsum_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), es: List<&2, E.QExpr>) -> O.le(~F, O.zero(F), lsum(~F, bb, es)):
  match es:
    case Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Con{+e, +t}:
      FO.nonneg_add(~F, BP.ls(~F, bb, e), lsum(~F, bb, t), ls_nn(~F, bb, hb, e), lsum_nn(~F, bb, hb, t))

def msum_nn(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), es: List<&2, E.QExpr>) -> O.le(~F, O.zero(F), msum(~F, bb, es)):
  match es:
    case Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Con{+e, +t}:
      FO.nonneg_add(~F, BP.ms(~F, bb, e), msum(~F, bb, t), ms_nn(~F, bb, hb, e), msum_nn(~F, bb, hb, t))

def eqok_le(~F: O.OField, +bb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +lam: O.C(F), +ms: O.C(F), es: List<&2, E.QExpr>, +hl: O.le(~F, lsum(~F, bb, es), lam), +hm: O.le(~F, msum(~F, bb, es), ms)) -> AP.eqok(~F, bb, lam, ms, es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (DM.le_trans(~F, BP.ls(~F, bb, e), lsum(~F, bb, Con{e, t}), lam, NW.le_addr(~F, BP.ls(~F, bb, e), lsum(~F, bb, t), lsum_nn(~F, bb, hb, t)), hl),
      (DM.le_trans(~F, BP.ms(~F, bb, e), msum(~F, bb, Con{e, t}), ms, NW.le_addr(~F, BP.ms(~F, bb, e), msum(~F, bb, t), msum_nn(~F, bb, hb, t)), hm),
      eqok_le(~F, bb, hb, lam, ms, t, DM.le_trans(~F, lsum(~F, bb, t), lsum(~F, bb, Con{e, t}), lam, NW.le_addl(~F, BP.ls(~F, bb, e), lsum(~F, bb, t), ls_nn(~F, bb, hb, e)), hl), DM.le_trans(~F, msum(~F, bb, t), msum(~F, bb, Con{e, t}), ms, NW.le_addl(~F, BP.ms(~F, bb, e), msum(~F, bb, t), ms_nn(~F, bb, hb, e)), hm))))

# Bounds on the block's vectors
# -----------------------------

def vall_xp(~F: O.OField, +x: M.Vec(~F), vp: List<&2, Nat>) -> M.vbnd.all(~F, LC.xperm(~F, x, vp), NP.vn(~F, x)):
  match vp:
    case Nil{}:
      Unit{}
    case Con{+v, t}:
      (AP.lkb(~F, x, v), vall_xp(~F, x, t))

def vall_ft(~F: O.OField, n: Nat, v: M.Vec(~F), +c: O.C(F), +h: M.vbnd.all(~F, v, c)) -> M.vbnd.all(~F, PP.ftake(~F, n, v), c):
  match n v:
    case 0n v:
      Unit{}
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{+a, +t}:
      (AP.both_l(M.bnd(~F, a, c), M.vbnd.all(~F, t, c), h), vall_ft(~F, k, t, c, AP.both_r(M.bnd(~F, a, c), M.vbnd.all(~F, t, c), h)))

def vall_fd(~F: O.OField, n: Nat, v: M.Vec(~F), +c: O.C(F), h: M.vbnd.all(~F, v, c)) -> M.vbnd.all(~F, PP.fdrop(~F, n, v), c):
  match n v:
    case 0n v:
      h
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{+a, +t}:
      vall_fd(~F, k, t, c, AP.both_r(M.bnd(~F, a, c), M.vbnd.all(~F, t, c), h))

def vall_look(~F: O.OField, v: M.Vec(~F), +c: O.C(F), +hc: O.le(~F, O.zero(F), c), h: M.vbnd.all(~F, v, c), k: Nat) -> M.bnd(~F, O.lookup(~F, v, k), c):
  match v k:
    case Nil{} k:
      FM.bnd_zero(~F, c, hc)
    case Con{+a, +t} 0n:
      AP.both_l(M.bnd(~F, a, c), M.vbnd.all(~F, t, c), h)
    case Con{+a, +t} 1n+j:
      vall_look(~F, t, c, hc, AP.both_r(M.bnd(~F, a, c), M.vbnd.all(~F, t, c), h), j)

def vall_zmap(~F: O.OField, +p: M.Vec(~F), pars: List<&2, Nat>, +c: O.C(F), +hc: O.le(~F, O.zero(F), c), +h: M.vbnd.all(~F, p, c)) -> M.vbnd.all(~F, PP.zmap(~F, p, pars), c):
  match pars:
    case Nil{}:
      Unit{}
    case Con{+v, t}:
      (vall_look(~F, p, c, hc, h, v), vall_zmap(~F, p, t, c, hc, h))

# |x_b ++ x_z| <= bb - 1, for bb = |x| + 1 (C5's hbb)
def hbb_of(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>) -> M.vbnd.all(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), O.sub(~F, O.add(F, NP.vn(~F, x), O.one(F)), O.one(F))):
  +hx = vall_xp(~F, x, vp)
  %FR.fring_eq(~F, [NP.vn(~F, x)], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}) : M.vbnd.all(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), _)
  NW.vall_app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars), NP.vn(~F, x), vall_ft(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)), NP.vn(~F, x), vall_fd(~F, o, LC.xperm(~F, x, vp), NP.vn(~F, x), hx)), vall_zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars, NP.vn(~F, x), FV.vmax_nn(~F, x), vall_ft(~F, o, LC.xperm(~F, x, vp), NP.vn(~F, x), hx)))

def len_ofdv(~F: O.OField, xs: List<&2, S.D>) -> {M.len(~F, M.ofdv(~F, xs)) == KA.klen(~KI.dnum(), xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %len_ofdv(~F, t) : {1n+M.len(~F, M.ofdv(~F, t)) == 1n+_ : Nat}
      {==}

def klen_pick(+xs: List<&2, S.D>, ks: List<&2, Nat>) -> {KA.klen(~KI.dnum(), NU.dpick(xs, ks)) == PL.nlen(ks) : Nat}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, t}:
      %klen_pick(xs, t) : {1n+KA.klen(~KI.dnum(), NU.dpick(xs, t)) == 1n+_ : Nat}
      {==}

def len_pick(~F: O.OField, +xs: List<&2, S.D>, +ks: List<&2, Nat>) -> {M.len(~F, M.ofdv(~F, NU.dpick(xs, ks))) == PL.nlen(ks) : Nat}:
  Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.dpick(xs, ks))), KA.klen(~KI.dnum(), NU.dpick(xs, ks)), PL.nlen(ks), len_ofdv(~F, NU.dpick(xs, ks)), klen_pick(xs, ks))

def look_ofdv(~F: O.OField, xs: List<&2, S.D>, k: Nat) -> {O.lookup(~F, M.ofdv(~F, xs), k) == M.ofd(~F, NU.dlook(xs, k)) : O.C(F)}:
  match xs k:
    case Nil{} k:
      DM.ofd_zero(~F)
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+j:
      look_ofdv(~F, t, j)

def rnn_look(~F: O.OField, w: M.Vec(~F), h: FV.rnn(~F, w), k: Nat) -> O.le(~F, O.zero(F), O.lookup(~F, w, k)):
  match w k:
    case Nil{} k:
      FO.le_refl(~F, O.zero(F))
    case Con{+a, +t} 0n:
      AP.both_l(O.le(~F, O.zero(F), a), FV.rnn(~F, t), h)
    case Con{+a, +t} 1n+j:
      rnn_look(~F, t, AP.both_r(O.le(~F, O.zero(F), a), FV.rnn(~F, t), h), j)

# the parameters' radii are radii of the box
def rnn_pick(~F: O.OField, +gr: List<&2, S.D>, pars: List<&2, Nat>, +h: FV.rnn(~F, M.ofdv(~F, gr))) -> FV.rnn(~F, M.ofdv(~F, NU.dpick(gr, pars))):
  match pars:
    case Nil{}:
      Unit{}
    case Con{+v, t}:
      ((%look_ofdv(~F, gr, v) : O.le(~F, O.zero(F), _)
      rnn_look(~F, M.ofdv(~F, gr), h, v)), rnn_pick(~F, gr, t, h))

def vall_pick(~F: O.OField, +gr: List<&2, S.D>, pars: List<&2, Nat>, +c: O.C(F), +hc: O.le(~F, O.zero(F), c), +h: M.vbnd.all(~F, M.ofdv(~F, gr), c)) -> M.vbnd.all(~F, M.ofdv(~F, NU.dpick(gr, pars)), c):
  match pars:
    case Nil{}:
      Unit{}
    case Con{+v, t}:
      ((%look_ofdv(~F, gr, v) : M.bnd(~F, _, c)
      vall_look(~F, M.ofdv(~F, gr), c, hc, h, v)), vall_pick(~F, gr, t, c, hc, h))

def pcont_pick(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, pars: List<&2, Nat>) -> {PL.pcont(~KI.dnum(), gc, gr, pars, NU.dpick(gc, pars), NU.dpick(gr, pars)) == True{} : Bool}:
  match pars:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      kband_i(KA.kle(~KI.dnum(), N.nadd(KI.dnum(), KA.kabs(~KI.dnum(), KA.ksub(~KI.dnum(), KB.klook(~KI.dnum(), gc, v), NU.dlook(gc, v))), KB.klook(~KI.dnum(), gr, v)), NU.dlook(gr, v)), PL.pcont(~KI.dnum(), gc, gr, t, NU.dpick(gc, t), NU.dpick(gr, t)),
        (%Equal.sym(S.D, NU.dlook(gc, v), KB.klook(~KI.dnum(), gc, v), dl_kl(gc, v)) : {KA.kle(~KI.dnum(), N.nadd(KI.dnum(), KA.kabs(~KI.dnum(), KA.ksub(~KI.dnum(), KB.klook(~KI.dnum(), gc, v), _)), KB.klook(~KI.dnum(), gr, v)), NU.dlook(gr, v)) == True{} : Bool}
        (%Equal.sym(S.D, NU.dlook(gr, v), KB.klook(~KI.dnum(), gr, v), dl_kl(gr, v)) : {KA.kle(~KI.dnum(), N.nadd(KI.dnum(), KA.kabs(~KI.dnum(), KA.ksub(~KI.dnum(), KB.klook(~KI.dnum(), gc, v), KB.klook(~KI.dnum(), gc, v))), KB.klook(~KI.dnum(), gr, v)), _) == True{} : Bool}
        pc_refl(~F, ~H, KB.klook(~KI.dnum(), gc, v), KB.klook(~KI.dnum(), gr, v)))),
        pcont_pick(~F, ~H, gc, gr, t))

def bnd_swap(~F: O.OField, +a: O.C(F), +b: O.C(F), +s: O.C(F), +c: O.C(F), h: M.bnd(~F, O.sub(~F, a, b), s), hs: M.bnd(~F, s, c)) -> M.bnd(~F, O.sub(~F, b, a), c):
  FM.bnd_mono(~F, O.sub(~F, b, a), s, c, KB.bnd_val(~F, O.neg(F, O.sub(~F, a, b)), O.sub(~F, b, a), s, FR.fring_eq(~F, [a, b], E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, {==}), FM.bnd_neg(~F, O.sub(~F, a, b), s, h)), AP.both_l(O.le(~F, O.zero(F), O.sub(~F, c, s)), O.le(~F, O.zero(F), O.add(F, c, s)), hs))

# |d1 - d2| <= r <= c entrywise gives |d2 - d1| <= c
def rbs(~F: O.OField, d1: M.Vec(~F), d2: M.Vec(~F), r: M.Vec(~F), +c: O.C(F), +h: BX.rbnd(~F, BX.vsub(~F, d1, d2), r), +hr: M.vbnd.all(~F, r, c), +hl1: {M.len(~F, d1) == M.len(~F, d2) : Nat}, +hl2: {M.len(~F, d2) == M.len(~F, r) : Nat}) -> M.vbnd.all(~F, BX.vsub(~F, d2, d1), c):
  match d1 d2 r:
    case Nil{} Nil{} r:
      Unit{}
    case Nil{} Con{b, t2} r:
      absurd(M.vbnd.all(~F, BX.vsub(~F, Con{b, t2}, Nil{}), c), FV.zero_ne(M.len(~F, t2), hl1))
    case Con{a, t1} Nil{} r:
      absurd(M.vbnd.all(~F, BX.vsub(~F, Nil{}, Con{a, t1}), c), FV.succ_ne(M.len(~F, t1), hl1))
    case Con{+a, +t1} Con{+b, +t2} Nil{}:
      absurd(M.vbnd.all(~F, BX.vsub(~F, Con{b, t2}, Con{a, t1}), c), FV.succ_ne(M.len(~F, t2), hl2))
    case Con{+a, +t1} Con{+b, +t2} Con{+s, +rs}:
      (bnd_swap(~F, a, b, s, c, AP.both_l(M.bnd(~F, O.sub(~F, a, b), s), BX.rbnd(~F, BX.vsub(~F, t1, t2), rs), h), AP.both_l(M.bnd(~F, s, c), M.vbnd.all(~F, rs, c), hr)),
      rbs(~F, t1, t2, rs, c, AP.both_r(M.bnd(~F, O.sub(~F, a, b), s), BX.rbnd(~F, BX.vsub(~F, t1, t2), rs), h), AP.both_r(M.bnd(~F, s, c), M.vbnd.all(~F, rs, c), hr), FV.succ_inj(M.len(~F, t1), M.len(~F, t2), hl1), FV.succ_inj(M.len(~F, t2), M.len(~F, rs), hl2)))

# the parameters' values are in their balls (C5's hzr)
def hzr_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +o: Nat, +p: M.Vec(~F), +hpb: PP.pbox(~KI.dnum(), ~F, ~H, gc, gr, o, p), +hgc: {KA.natle(o, KA.klen(~KI.dnum(), gc)) == True{} : Bool}, +pars: List<&2, Nat>, +hpo: {PL.pars_ok(o, pars) == True{} : Bool}) -> BX.rbnd(~F, BX.vsub(~F, PP.zmap(~F, p, pars), M.ofdv(~F, NU.dpick(gc, pars))), M.ofdv(~F, NU.dpick(gr, pars))):
  %AP.ofkv_d(~F, ~H, NU.dpick(gc, pars)) : BX.rbnd(~F, BX.vsub(~F, PP.zmap(~F, p, pars), _), M.ofdv(~F, NU.dpick(gr, pars)))
  %AP.ofkv_d(~F, ~H, NU.dpick(gr, pars)) : BX.rbnd(~F, BX.vsub(~F, PP.zmap(~F, p, pars), N.ofkv(~KI.dnum(), ~F, ~H, NU.dpick(gc, pars))), _)
  PP.pin_pc(~KI.dnum(), ~F, ~H, gc, gr, o, p, hpb, hgc, pars, NU.dpick(gc, pars), NU.dpick(gr, pars), hpo, pcont_pick(~F, ~H, gc, gr, pars))

# |pc - x_z| <= rho (C5's hzc), from hzr and the radii's bound
def hzc_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +o: Nat, +p: M.Vec(~F), +hpb: PP.pbox(~KI.dnum(), ~F, ~H, gc, gr, o, p), +hgc: {KA.natle(o, KA.klen(~KI.dnum(), gc)) == True{} : Bool}, +pars: List<&2, Nat>, +hpo: {PL.pars_ok(o, pars) == True{} : Bool}, +rho: O.C(F), +hpr: M.vbnd.all(~F, M.ofdv(~F, NU.dpick(gr, pars)), rho)) -> M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.dpick(gc, pars)), PP.zmap(~F, p, pars)), rho):
  rbs(~F, PP.zmap(~F, p, pars), M.ofdv(~F, NU.dpick(gc, pars)), M.ofdv(~F, NU.dpick(gr, pars)), rho, hzr_of(~F, ~H, gc, gr, o, p, hpb, hgc, pars, hpo), hpr,
    Equal.trans(Nat, M.len(~F, PP.zmap(~F, p, pars)), PL.nlen(pars), M.len(~F, M.ofdv(~F, NU.dpick(gc, pars))), PP.len_zmap(~F, p, pars), Equal.sym(Nat, M.len(~F, M.ofdv(~F, NU.dpick(gc, pars))), PL.nlen(pars), len_pick(~F, gc, pars))),
    Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.dpick(gc, pars))), PL.nlen(pars), M.len(~F, M.ofdv(~F, NU.dpick(gr, pars))), len_pick(~F, gc, pars), Equal.sym(Nat, M.len(~F, M.ofdv(~F, NU.dpick(gr, pars))), PL.nlen(pars), len_pick(~F, gr, pars))))

# The drawing near x
# ------------------

def lt_k(+k: Nat, +v: Nat, hk: {KA.natle(k, v) == True{} : Bool}, hv: {KA.natle(1n+v, k) == True{} : Bool}) -> Empty:
  L.lt_irr(v, L.le_trans(1n+v, k, v, hv, hk))

def near_at.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +m: Nat, +k: Nat, +v: Nat, +g: List<&2, S.D>, +x: M.Vec(~F), +d: O.C(F), +pins: List<&2, Nat>, +g0: List<&2, S.D>, b: Bool, e: {KA.nateq(k, v) == b : Bool}, hk: {KA.natle(k, v) == True{} : Bool}, h0: SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(k, pins), g, x, d, g0, k), ih: {KA.natle(1n+k, v) == True{} : Bool} -> SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(v, pins), g, x, d, g0, v)) -> SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(v, pins), g, x, d, g0, v):
  match b:
    case True{}:
      %GJ.nateq_ok(k, v, e) : SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(_, pins), g, x, d, g0, _)
      h0
    case False{}:
      ih(GJ.le_ne(k, v, hk, e))

def add1_le(+v: Nat, +k: Nat, +m: Nat, h: {KA.natle(1n+v, Nat.add(k, 1n+m)) == True{} : Bool}) -> {KA.natle(1n+v, 1n+Nat.add(k, m)) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(k, m), Nat.add(k, 1n+m), LN.add_succ(k, m)) : {KA.natle(1n+v, _) == True{} : Bool}
  h

def add0_le(+v: Nat, +k: Nat, h: {KA.natle(1n+v, Nat.add(k, 0n)) == True{} : Bool}) -> {KA.natle(1n+v, k) == True{} : Bool}:
  %Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : {KA.natle(1n+v, _) == True{} : Bool}
  h

# Near at one variable v (k <= v < k + m)
def near_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, m: Nat, +k: Nat, +v: Nat, +g: List<&2, S.D>, +x: M.Vec(~F), +d: O.C(F), +pins: List<&2, Nat>, +g0: List<&2, S.D>, +hk: {KA.natle(k, v) == True{} : Bool}, +hv: {KA.natle(1n+v, Nat.add(k, m)) == True{} : Bool}, h: SV.Near(~KI.dnum(), ~F, ~H, m, k, g, x, d, pins, g0)) -> SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(v, pins), g, x, d, g0, v):
  match m:
    case 0n:
      absurd(SV.Near.go(~KI.dnum(), ~F, ~H, SV.mem(v, pins), g, x, d, g0, v), lt_k(k, v, hk, add0_le(v, k, hv)))
    case 1n++j:
      match h:
        case (h0, h1):
          near_at.go(~F, ~H, j, k, v, g, x, d, pins, g0, KA.nateq(k, v), {==}, hk, h0, hk1 => near_at(~F, ~H, j, 1n+k, v, g, x, d, pins, g0, hk1, add1_le(v, k, j, hv), h1))

def close_bnd(~F: O.OField, +a: O.C(F), +b: O.C(F), +d: O.C(F), h: SV.Close(~F, a, b, d)) -> M.bnd(~F, O.sub(~F, a, b), d):
  match h:
    case (h1, h2):
      (FO.lt_le(~F, O.zero(F), O.sub(~F, d, O.sub(~F, a, b)), RL.sub_pos(~F, O.sub(~F, a, b), d, h1)), FM.nn_eq(~F, O.add(F, d, O.sub(~F, a, b)), O.sub(~F, d, O.sub(~F, b, a)), FR.fring_eq(~F, [a, b, d], E.ZSub{E.ZVar{2n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZAdd{E.ZVar{2n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==}), FO.lt_le(~F, O.zero(F), O.sub(~F, d, O.sub(~F, b, a)), RL.sub_pos(~F, O.sub(~F, b, a), d, h2))))

def lk_kv(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +g: List<&2, S.D>, +w: Nat) -> {O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, g), w) == M.ofd(~F, NU.dlook(g, w)) : O.C(F)}:
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, g), M.ofdv(~F, g), AP.ofkv_d(~F, ~H, g)) : {O.lookup(~F, _, w) == M.ofd(~F, NU.dlook(g, w)) : O.C(F)}
  look_ofdv(~F, g, w)

# a free variable's drawn value is within d of x
def near_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +nv: Nat, +w: Nat, +g: List<&2, S.D>, +x: M.Vec(~F), +d: O.C(F), +pins: List<&2, Nat>, +g0: List<&2, S.D>, +hf: {SV.mem(w, pins) == False{} : Bool}, +hw: {KA.natle(1n+w, nv) == True{} : Bool}, +hN: SV.Near(~KI.dnum(), ~F, ~H, nv, 0n, g, x, d, pins, g0)) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dlook(g, w)), O.lookup(~F, x, w)), d):
  close_bnd(~F, M.ofd(~F, NU.dlook(g, w)), O.lookup(~F, x, w), d, (%lk_kv(~F, ~H, g, w) : SV.Close(~F, _, O.lookup(~F, x, w), d)
    (%hf : SV.Near.go(~KI.dnum(), ~F, ~H, _, g, x, d, g0, w)
    near_at(~F, ~H, nv, 0n, w, g, x, d, pins, g0, {==}, hw, hN))))

def y0_close(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +nv: Nat, +g: List<&2, S.D>, +x: M.Vec(~F), +d: O.C(F), +pins: List<&2, Nat>, +g0: List<&2, S.D>, +hN: SV.Near(~KI.dnum(), ~F, ~H, nv, 0n, g, x, d, pins, g0), ws: List<&2, Nat>, +hf: {MX.disj(ws, pins) == True{} : Bool}, +hb: {SV.below(ws, nv) == True{} : Bool}) -> M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.dpick(g, ws)), LC.xperm(~F, x, ws)), d):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +t}:
      (near_bnd(~F, ~H, nv, w, g, x, d, pins, g0, MX.disj_hd(w, t, pins, hf), (%L.lt_sv(w, nv) : {_ == True{} : Bool}
        L.band_l(SV.lt(w, nv), SV.below(t, nv), hb)), hN),
      y0_close(~F, ~H, nv, g, x, d, pins, g0, hN, t, MX.disj_tl(w, t, pins, hf), L.band_r(SV.lt(w, nv), SV.below(t, nv), hb)))
