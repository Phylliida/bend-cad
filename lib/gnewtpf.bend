# bend-cad: lib/gnumer.bend's Newton, Y and radius search return exactly
# numer.bend's results sent through the map h : KI.dnum() -> K of laws R
# (lib/pops.bend), for every K and every operations W with such laws.
# Each lemma states GN.f(W, h args) = h(NU.f(args)) and is proven by
# rewriting the right side's images into GN's terms, bottom up, with the
# map's laws (lib/khom.bend), W's (lib/pops.bend), the checker's
# parametricity (lib/khompf.bend, lib/certhpf.bend) and the elimination's
# (lib/gelimpf.bend). Untrusted; PLAN-sk13w W4.


import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./karith.bend as KA
import ./kinst.bend as KI
import ./cert.bend as CK
import ./numer.bend as NU
import ./khom.bend as KH
import ./khompf.bend as KP
import ./certhpf.bend as CH
import ./pops.bend as PO
import ./gnumer.bend as GN
import ./gmap.bend as GM

# Lists
# -----

def dlook_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>, k: Nat) -> {GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dlook(xs, k)) : N.NC(K)}:
  match xs k:
    case Nil{} k:
      PO.l_ofd(K, W, R)(NU.dzero())
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      dlook_t(~K, ~W, ~R, t, j)

def dpick_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +xs: List<&2, S.D>, ks: List<&2, Nat>) -> {GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), ks) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dpick(xs, ks)) : N.KVec(~K)}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      %dlook_t(~K, ~W, ~R, xs, k) : {Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k), GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), t)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dpick(xs, t))} : N.KVec(~K)}
      %dpick_t(~K, ~W, ~R, xs, t) : {Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k), GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), t)} == Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k), _} : N.KVec(~K)}
      {==}

def dtake_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat, xs: List<&2, S.D>) -> {GN.dtake(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dtake(n, xs)) : N.KVec(~K)}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{+x, +t}:
      %dtake_t(~K, ~W, ~R, m, t) : {Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), GN.dtake(~K, ~W, m, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), _} : N.KVec(~K)}
      {==}

def cyc_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, c: C.Cert<KI.dnum()>) -> {GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.cert.yc(c)) : N.KVec(~K)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def cyr_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, c: C.Cert<KI.dnum()>) -> {GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.cert.yr(c)) : N.KVec(~K)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

# The Jacobian and the values: the checker's own
# ----------------------------------------------

def jac_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +eqs: List<&2, E.QExpr>, +n: Nat, +env: List<&2, S.D>) -> {GN.jac(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), env)) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.jac(eqs, n, env)) : N.KMat(~K)}:
  %CH.mcenters_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), CK.srows(~KI.dnum(), CK.zipb(~KI.dnum(), env, Nil{}), n, 0n, eqs)) : {GN.jac(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), env)) == _ : N.KMat(~K)}
  %CH.srows_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), CK.zipb(~KI.dnum(), env, Nil{}), n, 0n, eqs) : {GN.jac(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), env)) == CK.mcenters(~K, _) : N.KMat(~K)}
  %CH.zipb_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), env, Nil{}) : {GN.jac(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), env)) == CK.mcenters(~K, CK.srows(~K, _, n, 0n, eqs)) : N.KMat(~K)}
  {==}

def vals_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +eqs: List<&2, E.QExpr>, +env: List<&2, S.D>) -> {GN.vals(~K, ~W, eqs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), env)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.vals(eqs, env)) : N.KVec(~K)}:
  CH.kvals_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), env, eqs)

# One Newton step
# ---------------

def nstep_round_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, ys: List<&2, S.D>, ds: List<&2, S.D>, +p: Nat) -> {GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ds), p) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.nstep.round(ys, ds, p)) : N.KVec(~K)}:
  match ys ds:
    case Nil{} ds:
      {==}
    case Con{+y, +yt} Nil{}:
      %PO.l_round(K, W, R)(y, p) : {Con{PO.round(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), p), GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), Nil{}, p)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.nstep.round(yt, Nil{}, p))} : N.KVec(~K)}
      %nstep_round_t(~K, ~W, ~R, yt, Nil{}, p) : {Con{PO.round(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), p), GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), Nil{}, p)} == Con{PO.round(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), p), _} : N.KVec(~K)}
      {==}
    case Con{+y, +yt} Con{+d, +dt}:
      %PO.l_round(K, W, R)(S.D.sub(y, d), p) : {Con{PO.round(K, W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), d)), p), GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), dt), p)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.nstep.round(yt, dt, p))} : N.KVec(~K)}
      %KP.ksub_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), y, d) : {Con{PO.round(K, W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), d)), p), GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), dt), p)} == Con{PO.round(K, W, _, p), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.nstep.round(yt, dt, p))} : N.KVec(~K)}
      %nstep_round_t(~K, ~W, ~R, yt, dt, p) : {Con{PO.round(K, W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), d)), p), GN.nstep.round(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), dt), p)} == Con{PO.round(K, W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), d)), p), _} : N.KVec(~K)}
      {==}

# Newton's states
# ---------------

def classify_go_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, same: Bool, +y2: List<&2, S.D>) -> {GN.classify.go(~K, ~W, same, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GM.hns(~K, ~PO.hom(K, W, R), NU.classify.go(same, y2)) : GN.GNS<K>}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def dclose_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>, ys: List<&2, S.D>, +t: S.D) -> {GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)) == NU.dclose(xs, ys, t) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %KP.kle_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dabs(S.D.sub(x, y)), t) : {KA.band(KA.kle(~K, GN.dabs(~K, ~W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t))) == KA.band(_, NU.dclose(xt, yt, t)) : Bool}
      %KP.kabs_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), S.D.sub(x, y)) : {KA.band(KA.kle(~K, GN.dabs(~K, ~W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t))) == KA.band(KA.kle(~K, _, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), NU.dclose(xt, yt, t)) : Bool}
      %KP.ksub_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), x, y) : {KA.band(KA.kle(~K, GN.dabs(~K, ~W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t))) == KA.band(KA.kle(~K, KA.kabs(~K, _), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), NU.dclose(xt, yt, t)) : Bool}
      %dclose_t(~K, ~W, ~R, xt, yt, t) : {KA.band(KA.kle(~K, GN.dabs(~K, ~W, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xt), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yt), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t))) == KA.band(KA.kle(~K, KA.kabs(~K, KA.ksub(~K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), t)), _) : Bool}
      {==}

def classify_far_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, near: Bool, +ys: List<&2, S.D>, +p: Nat, +y2: List<&2, S.D>) -> {GN.classify.far(~K, ~W, near, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GM.hns(~K, ~PO.hom(K, W, R), NU.classify.far(near, ys, p, y2)) : GN.GNS<K>}:
  match near:
    case False{}:
      {==}
    case True{}:
      %classify_go_t(~K, ~W, ~R, NU.dclose(ys, y2, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)}), y2) : {GN.classify.go(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)})), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == _ : GN.GNS<K>}
      %dclose_t(~K, ~W, ~R, ys, y2, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)}) : {GN.classify.go(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)})), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GN.classify.go(~K, ~W, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) : GN.GNS<K>}
      %PO.l_ofd(K, W, R)(S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)}) : {GN.classify.go(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)})), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GN.classify.go(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), _), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) : GN.GNS<K>}
      {==}

def classify_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +ys: List<&2, S.D>, +p: Nat, m: Maybe<&2, List<&2, S.D>>) -> {GN.classify(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, GM.hmv(~K, ~PO.hom(K, W, R), m)) == GM.hns(~K, ~PO.hom(K, W, R), NU.classify(ys, p, m)) : GN.GNS<K>}:
  match m:
    case None{}:
      {==}
    case Some{+y2}:
      %classify_far_t(~K, ~W, ~R, NU.dclose(ys, y2, NU.far()), ys, p, y2) : {GN.classify.far(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, NU.far())), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == _ : GN.GNS<K>}
      %dclose_t(~K, ~W, ~R, ys, y2, NU.far()) : {GN.classify.far(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, NU.far())), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GN.classify.far(~K, ~W, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) : GN.GNS<K>}
      %PO.l_ofd(K, W, R)(NU.far()) : {GN.classify.far(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), PO.ofd(K, W, NU.far())), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) == GN.classify.far(~K, ~W, GN.dclose(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2), _), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys), p, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y2)) : GN.GNS<K>}
      {==}

# Y
# -

def ysigv_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +b: Nat, xs: List<&2, S.D>) -> {GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.ysigv(b, xs)) : N.KVec(~K)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %PO.l_sig(K, W, R)(x, b) : {Con{PO.sig(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), b), GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.ysigv(b, t))} : N.KVec(~K)}
      %ysigv_t(~K, ~W, ~R, b, t) : {Con{PO.sig(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), b), GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{PO.sig(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), b), _} : N.KVec(~K)}
      {==}

def ysig_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +b: Nat, a: List<&2, List<&2, S.D>>) -> {GN.ysig(~K, ~W, b, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a)) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.ysig(b, a)) : N.KMat(~K)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %ysigv_t(~K, ~W, ~R, b, r) : {Con{GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), GN.ysig(~K, ~W, b, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.ysig(b, t))} : N.KMat(~K)}
      %ysig_t(~K, ~W, ~R, b, t) : {Con{GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), GN.ysig(~K, ~W, b, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{GN.ysigv(~K, ~W, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), _} : N.KMat(~K)}
      {==}

# The radius search's growth
# --------------------------

def grow_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +r: S.D) -> {GN.grow(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.grow(r)) : N.NC(K)}:
  %PO.l_sigup(K, W, R)(S.D.mul(r, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), 8n) : {GN.grow(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r)) == _ : N.NC(K)}
  %KH.h_mul(KI.dnum(), K, PO.hom(K, W, R))(r, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}) : {GN.grow(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r)) == PO.sigup(K, W, _, 8n) : N.NC(K)}
  %PO.l_ofd(K, W, R)(S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}) : {GN.grow(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r)) == PO.sigup(K, W, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r), _), 8n) : N.NC(K)}
  {==}
