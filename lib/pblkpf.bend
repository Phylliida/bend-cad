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
