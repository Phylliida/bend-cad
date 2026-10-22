# bend-cad: the block certificate checker (lib/cert.bend) gives the same
# verdict through a map of computing numbers h : K -> L (lib/khom.bend):
# CK.check in L of a certificate's image is CK.check in K of the
# certificate, and the checker's intermediate vectors (the equations'
# values, the slope enclosures, G r and the self-map's bound) in L are the
# images of K's. Untrusted; for the word verdict (PLAN-sk13w W5).


import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./khom.bend as KH
import ./khompf.bend as KP

# Pieces
# ------

def zipb_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, cs: N.KVec(~K), rs: N.KVec(~K)) -> {CK.zipb(~L, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs)) == KH.hbv(~K, ~L, ~H, CK.zipb(~K, cs, rs)) : List<&2, KB.KB<L>>}:
  match cs rs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+r, +rt}:
      %KH.h_zero(K, L, H) : {Con{KB.KB{N.nzero(L), KH.hmap(K, L, H, r)}, CK.zipb(~L, Nil{}, KH.hv(~K, ~L, ~H, rt))} == Con{KB.KB{_, KH.hmap(K, L, H, r)}, KH.hbv(~K, ~L, ~H, CK.zipb(~K, Nil{}, rt))} : List<&2, KB.KB<L>>}
      %zipb_h(~K, ~L, ~H, Nil{}, rt) : {Con{KB.KB{N.nzero(L), KH.hmap(K, L, H, r)}, CK.zipb(~L, Nil{}, KH.hv(~K, ~L, ~H, rt))} == Con{KB.KB{N.nzero(L), KH.hmap(K, L, H, r)}, _} : List<&2, KB.KB<L>>}
      {==}
    case Con{+c, +ct} Nil{}:
      %KH.h_zero(K, L, H) : {Con{KB.KB{KH.hmap(K, L, H, c), N.nzero(L)}, CK.zipb(~L, KH.hv(~K, ~L, ~H, ct), Nil{})} == Con{KB.KB{KH.hmap(K, L, H, c), _}, KH.hbv(~K, ~L, ~H, CK.zipb(~K, ct, Nil{}))} : List<&2, KB.KB<L>>}
      %zipb_h(~K, ~L, ~H, ct, Nil{}) : {Con{KB.KB{KH.hmap(K, L, H, c), N.nzero(L)}, CK.zipb(~L, KH.hv(~K, ~L, ~H, ct), Nil{})} == Con{KB.KB{KH.hmap(K, L, H, c), N.nzero(L)}, _} : List<&2, KB.KB<L>>}
      {==}
    case Con{+c, +ct} Con{+r, +rt}:
      %zipb_h(~K, ~L, ~H, ct, rt) : {Con{KB.KB{KH.hmap(K, L, H, c), KH.hmap(K, L, H, r)}, CK.zipb(~L, KH.hv(~K, ~L, ~H, ct), KH.hv(~K, ~L, ~H, rt))} == Con{KB.KB{KH.hmap(K, L, H, c), KH.hmap(K, L, H, r)}, _} : List<&2, KB.KB<L>>}
      {==}

def srows_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>) -> {CK.srows(~L, KH.hbv(~K, ~L, ~H, box), cnt, lo, eqs) == KH.hbm(~K, ~L, ~H, CK.srows(~K, box, cnt, lo, eqs)) : List<&2, List<&2, KB.KB<L>>>}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %KP.krange_h(~K, ~L, ~H, box, e, cnt, lo) : {Con{KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, cnt, lo), CK.srows(~L, KH.hbv(~K, ~L, ~H, box), cnt, lo, es)} == Con{_, KH.hbm(~K, ~L, ~H, CK.srows(~K, box, cnt, lo, es))} : List<&2, List<&2, KB.KB<L>>>}
      %srows_h(~K, ~L, ~H, box, cnt, lo, es) : {Con{KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, cnt, lo), CK.srows(~L, KH.hbv(~K, ~L, ~H, box), cnt, lo, es)} == Con{KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, cnt, lo), _} : List<&2, List<&2, KB.KB<L>>>}
      {==}

def mcenters_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, rows: List<&2, List<&2, KB.KB<K>>>) -> {CK.mcenters(~L, KH.hbm(~K, ~L, ~H, rows)) == KH.hm(~K, ~L, ~H, CK.mcenters(~K, rows)) : N.KMat(~L)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %KP.bcenters_h(~K, ~L, ~H, r) : {Con{KB.bcenters(~L, KH.hbv(~K, ~L, ~H, r)), CK.mcenters(~L, KH.hbm(~K, ~L, ~H, rs))} == Con{_, KH.hm(~K, ~L, ~H, CK.mcenters(~K, rs))} : N.KMat(~L)}
      %mcenters_h(~K, ~L, ~H, rs) : {Con{KB.bcenters(~L, KH.hbv(~K, ~L, ~H, r)), CK.mcenters(~L, KH.hbm(~K, ~L, ~H, rs))} == Con{KB.bcenters(~L, KH.hbv(~K, ~L, ~H, r)), _} : N.KMat(~L)}
      {==}

def mradii_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, rows: List<&2, List<&2, KB.KB<K>>>) -> {CK.mradii(~L, KH.hbm(~K, ~L, ~H, rows)) == KH.hm(~K, ~L, ~H, CK.mradii(~K, rows)) : N.KMat(~L)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %KP.bradii_h(~K, ~L, ~H, r) : {Con{KB.bradii(~L, KH.hbv(~K, ~L, ~H, r)), CK.mradii(~L, KH.hbm(~K, ~L, ~H, rs))} == Con{_, KH.hm(~K, ~L, ~H, CK.mradii(~K, rs))} : N.KMat(~L)}
      %mradii_h(~K, ~L, ~H, rs) : {Con{KB.bradii(~L, KH.hbv(~K, ~L, ~H, r)), CK.mradii(~L, KH.hbm(~K, ~L, ~H, rs))} == Con{KB.bradii(~L, KH.hbv(~K, ~L, ~H, r)), _} : N.KMat(~L)}
      {==}

def kvals_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +env: N.KVec(~K), eqs: List<&2, E.QExpr>) -> {CK.kvals(~L, KH.hv(~K, ~L, ~H, env), eqs) == KH.hv(~K, ~L, ~H, CK.kvals(~K, env, eqs)) : N.KVec(~L)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %KP.keval_h(~K, ~L, ~H, env, e) : {Con{KB.keval(~L, KH.hv(~K, ~L, ~H, env), e), CK.kvals(~L, KH.hv(~K, ~L, ~H, env), es)} == Con{_, KH.hv(~K, ~L, ~H, CK.kvals(~K, env, es))} : N.KVec(~L)}
      %kvals_h(~K, ~L, ~H, env, es) : {Con{KB.keval(~L, KH.hv(~K, ~L, ~H, env), e), CK.kvals(~L, KH.hv(~K, ~L, ~H, env), es)} == Con{KB.keval(~L, KH.hv(~K, ~L, ~H, env), e), _} : N.KVec(~L)}
      {==}

def allheld_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, eqs: List<&2, E.QExpr>) -> {CK.allheld(~L, eqs) == CK.allheld(~K, eqs) : Bool}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %KP.held_h(~K, ~L, ~H, e) : {KA.band(KB.held(~L, e), CK.allheld(~L, es)) == KA.band(_, CK.allheld(~K, es)) : Bool}
      %allheld_h(~K, ~L, ~H, es) : {KA.band(KB.held(~L, e), CK.allheld(~L, es)) == KA.band(KB.held(~L, e), _) : Bool}
      {==}

def mlen_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K)) -> {CK.mlen(~L, KH.hm(~K, ~L, ~H, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %mlen_h(~K, ~L, ~H, rs) : {1n+CK.mlen(~L, KH.hm(~K, ~L, ~H, rs)) == 1n+_ : Nat}
      {==}

# A certificate's fields through h
# --------------------------------

def yc_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)) == KH.hv(~K, ~L, ~H, C.Cert.yc(K, c)) : N.KVec(~L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def yr_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c)) == KH.hv(~K, ~L, ~H, C.Cert.yr(K, c)) : N.KVec(~L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def q_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.q(L, KH.hcert(~K, ~L, ~H, c)) == KH.hmap(K, L, H, C.Cert.q(K, c)) : N.NC(L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def ym_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.ym(L, KH.hcert(~K, ~L, ~H, c)) == KH.hm(~K, ~L, ~H, C.Cert.ym(K, c)) : N.KMat(~L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def pc_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.pc(L, KH.hcert(~K, ~L, ~H, c)) == KH.hv(~K, ~L, ~H, C.Cert.pc(K, c)) : N.KVec(~L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

def pr_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: C.Cert<K>) -> {C.Cert.pr(L, KH.hcert(~K, ~L, ~H, c)) == KH.hv(~K, ~L, ~H, C.Cert.pr(K, c)) : N.KVec(~L)}:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      {==}

# The conditions
# --------------

def shape_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.shape(~K, eqs, n, yc, yr, ym, pc, pr) : Bool}:
  %mlen_h(~K, ~L, ~H, ym) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(_, n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, yc) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(_, n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, yr) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(_, n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, pc) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(_, KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, pr) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, pc)), _), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.kvle_h(~K, ~L, ~H, Nil{}, yr) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, pc)), KA.klen(~L, KH.hv(~K, ~L, ~H, pr))), KA.band(_, KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.kvle_h(~K, ~L, ~H, Nil{}, pr) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, pc)), KA.klen(~L, KH.hv(~K, ~L, ~H, pr))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, yr)), KA.band(_, KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %allheld_h(~K, ~L, ~H, eqs) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, pc)), KA.klen(~L, KH.hv(~K, ~L, ~H, pr))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, yr)), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, pr)), KA.band(_, CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, pc) : {CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~L, KH.hm(~K, ~L, ~H, ym)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yc)), n), KA.band(KA.natle(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, pc)), KA.klen(~L, KH.hv(~K, ~L, ~H, pr))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, yr)), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, pr)), KA.band(CK.allheld(~L, eqs), CK.allbelow(Nat.add(n, _), eqs))))))))) : Bool}
  {==}

def factor_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +q: N.NC(K)) -> {CK.factor(~L, KH.hmap(K, L, H, q)) == CK.factor(~K, q) : Bool}:
  %KP.kle0_h(~K, ~L, ~H, q) : {CK.factor(~L, KH.hmap(K, L, H, q)) == KA.band(_, KA.klt(~K, q, N.none(K))) : Bool}
  %KP.klt1_h(~K, ~L, ~H, q) : {CK.factor(~L, KH.hmap(K, L, H, q)) == KA.band(KA.kle(~L, N.nzero(L), KH.hmap(K, L, H, q)), _) : Bool}
  {==}

def box_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KH.hbv(~K, ~L, ~H, CK.box(~K, n, yc, yr, pc, pr)) : List<&2, KB.KB<L>>}:
  %zipb_h(~K, ~L, ~H, KA.kapp(~K, yc, pc), KA.kapp(~K, KA.kfit(~K, n, yr), pr)) : {CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : List<&2, KB.KB<L>>}
  %KP.kapp_h(~K, ~L, ~H, yc, pc) : {CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.zipb(~L, _, KH.hv(~K, ~L, ~H, KA.kapp(~K, KA.kfit(~K, n, yr), pr))) : List<&2, KB.KB<L>>}
  %KP.kapp_h(~K, ~L, ~H, KA.kfit(~K, n, yr), pr) : {CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.zipb(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), _) : List<&2, KB.KB<L>>}
  %KP.kfit_h(~K, ~L, ~H, n, yr) : {CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.zipb(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), KA.kapp(~L, _, KH.hv(~K, ~L, ~H, pr))) : List<&2, KB.KB<L>>}
  {==}

def rowsy_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KH.hbm(~K, ~L, ~H, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)) : List<&2, List<&2, KB.KB<L>>>}:
  %srows_h(~K, ~L, ~H, CK.box(~K, n, yc, yr, pc, pr), n, 0n, eqs) : {CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : List<&2, List<&2, KB.KB<L>>>}
  %box_h(~K, ~L, ~H, n, yc, yr, pc, pr) : {CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.srows(~L, _, n, 0n, eqs) : List<&2, List<&2, KB.KB<L>>>}
  {==}

def rowsz_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KH.hbm(~K, ~L, ~H, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)) : List<&2, List<&2, KB.KB<L>>>}:
  %srows_h(~K, ~L, ~H, CK.box(~K, n, yc, yr, pc, pr), KA.klen(~K, pc), n, eqs) : {CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : List<&2, List<&2, KB.KB<L>>>}
  %box_h(~K, ~L, ~H, n, yc, yr, pc, pr) : {CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.srows(~L, _, KA.klen(~K, pc), n, eqs) : List<&2, List<&2, KB.KB<L>>>}
  %KP.klen_h(~K, ~L, ~H, pc) : {CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.srows(~L, CK.box(~L, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)), _, n, eqs) : List<&2, List<&2, KB.KB<L>>>}
  {==}

def imm_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +n: Nat, +a: N.KMat(~K), +b: N.KMat(~K)) -> {CK.imm(~L, n, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KH.hm(~K, ~L, ~H, CK.imm(~K, n, a, b)) : N.KMat(~L)}:
  %KP.kmadd_h(~K, ~L, ~H, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, a, b))) : {CK.imm(~L, n, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == _ : N.KMat(~L)}
  %KP.kident_h(~K, ~L, ~H, n) : {CK.imm(~L, n, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KA.kmadd(~L, _, KH.hm(~K, ~L, ~H, KA.kmneg(~K, KA.kmatmul(~K, a, b)))) : N.KMat(~L)}
  %KP.kmneg_h(~K, ~L, ~H, KA.kmatmul(~K, a, b)) : {CK.imm(~L, n, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KA.kmadd(~L, KA.kident(~L, n), _) : N.KMat(~L)}
  %KP.kmatmul_h(~K, ~L, ~H, a, b) : {CK.imm(~L, n, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KA.kmadd(~L, KA.kident(~L, n), KA.kmneg(~L, _)) : N.KMat(~L)}
  {==}

def gvec_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr)) : N.KVec(~L)}:
  %KP.kvadd_h(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)))), yr), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr))) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, KA.kmabs(~K, CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)))), yr) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, _, KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %KP.kmabs_h(~K, ~L, ~H, CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)))) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, _, KH.hv(~K, ~L, ~H, yr)), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %imm_h(~K, ~L, ~H, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, _), KH.hv(~K, ~L, ~H, yr)), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %mcenters_h(~K, ~L, ~H, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), _)), KH.hv(~K, ~L, ~H, yr)), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %rowsy_h(~K, ~L, ~H, eqs, n, yc, yr, pc, pr) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, _))), KH.hv(~K, ~L, ~H, yr)), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, KA.kmabs(~K, ym), KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr))))), KH.hv(~K, ~L, ~H, yr)), _) : N.KVec(~L)}
  %KP.kmabs_h(~K, ~L, ~H, ym) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr))))), KH.hv(~K, ~L, ~H, yr)), KA.kmatvec(~L, _, KH.hv(~K, ~L, ~H, KA.kmatvec(~K, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))) : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), yr) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr))))), KH.hv(~K, ~L, ~H, yr)), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), _)) : N.KVec(~L)}
  %mradii_h(~K, ~L, ~H, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr))))), KH.hv(~K, ~L, ~H, yr)), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, _, KH.hv(~K, ~L, ~H, yr)))) : N.KVec(~L)}
  %rowsy_h(~K, ~L, ~H, eqs, n, yc, yr, pc, pr) : {CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kmatvec(~L, KA.kmabs(~L, CK.imm(~L, n, KH.hm(~K, ~L, ~H, ym), CK.mcenters(~L, CK.rowsy(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr))))), KH.hv(~K, ~L, ~H, yr)), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, CK.mradii(~L, _), KH.hv(~K, ~L, ~H, yr)))) : N.KVec(~L)}
  {==}

def svec_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KH.hv(~K, ~L, ~H, CK.svec(~K, eqs, n, yc, yr, ym, pc, pr)) : N.KVec(~L)}:
  %KP.kvadd_h(~K, ~L, ~H, KA.kvadd(~K, KA.kvabs(~K, KA.kmatvec(~K, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs))), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr))), CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr)) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : N.KVec(~L)}
  %KP.kvadd_h(~K, ~L, ~H, KA.kvabs(~K, KA.kmatvec(~K, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs))), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr))) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, _, KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kvabs_h(~K, ~L, ~H, KA.kmatvec(~K, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs))) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, _, KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs)) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, _), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %kvals_h(~K, ~L, ~H, KA.kapp(~K, yc, pc), eqs) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), _)), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kapp_h(~K, ~L, ~H, yc, pc) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, _, eqs))), KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), _), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmabs_h(~K, ~L, ~H, ym) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, _, KH.hv(~K, ~L, ~H, KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmatvec_h(~K, ~L, ~H, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), _)), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmadd_h(~K, ~L, ~H, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, _, KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %KP.kmabs_h(~K, ~L, ~H, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, _, KH.hm(~K, ~L, ~H, CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)))), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %mcenters_h(~K, ~L, ~H, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, KA.kmabs(~L, _), KH.hm(~K, ~L, ~H, CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)))), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %rowsz_h(~K, ~L, ~H, eqs, n, yc, yr, pc, pr) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, KA.kmabs(~L, CK.mcenters(~L, _)), KH.hm(~K, ~L, ~H, CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)))), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %mradii_h(~K, ~L, ~H, CK.rowsz(~K, eqs, n, yc, yr, pc, pr)) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, KA.kmabs(~L, CK.mcenters(~L, CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)))), _), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %rowsz_h(~K, ~L, ~H, eqs, n, yc, yr, pc, pr) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, KA.kmabs(~L, CK.mcenters(~L, CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)))), CK.mradii(~L, _)), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))) : N.KVec(~L)}
  %gvec_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.svec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvadd(~L, KA.kvadd(~L, KA.kvabs(~L, KA.kmatvec(~L, KH.hm(~K, ~L, ~H, ym), CK.kvals(~L, KA.kapp(~L, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, pc)), eqs))), KA.kmatvec(~L, KA.kmabs(~L, KH.hm(~K, ~L, ~H, ym)), KA.kmatvec(~L, KA.kmadd(~L, KA.kmabs(~L, CK.mcenters(~L, CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)))), CK.mradii(~L, CK.rowsz(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)))), KH.hv(~K, ~L, ~H, pr)))), _) : N.KVec(~L)}
  {==}

def ccon_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.ccon(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.ccon(~K, eqs, n, yc, yr, q, ym, pc, pr) : Bool}:
  %KP.kvle_h(~K, ~L, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr), KA.kvscale(~K, q, yr)) : {CK.ccon(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : Bool}
  %gvec_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.ccon(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvle(~L, _, KH.hv(~K, ~L, ~H, KA.kvscale(~K, q, yr))) : Bool}
  %KP.kvscale_h(~K, ~L, ~H, q, yr) : {CK.ccon(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvle(~L, CK.gvec(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)), _) : Bool}
  {==}

def cself_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.cself(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.cself(~K, eqs, n, yc, yr, ym, pc, pr) : Bool}:
  %KP.kvle_h(~K, ~L, ~H, CK.svec(~K, eqs, n, yc, yr, ym, pc, pr), yr) : {CK.cself(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == _ : Bool}
  %svec_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.cself(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.kvle(~L, _, KH.hv(~K, ~L, ~H, yr)) : Bool}
  {==}

def cpos_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +n: Nat, +yr: N.KVec(~K)) -> {CK.cpos(~L, n, KH.hv(~K, ~L, ~H, yr)) == CK.cpos(~K, n, yr) : Bool}:
  %KP.klen_h(~K, ~L, ~H, yr) : {CK.cpos(~L, n, KH.hv(~K, ~L, ~H, yr)) == KA.band(KA.nateq(_, n), KA.kvlt(~K, Nil{}, yr)) : Bool}
  %KP.kvlt_h(~K, ~L, ~H, Nil{}, yr) : {CK.cpos(~L, n, KH.hv(~K, ~L, ~H, yr)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, yr)), n), _) : Bool}
  {==}

def rest3_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.rest3(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.rest3(~K, eqs, n, yc, yr, ym, pc, pr) : Bool}:
  %cself_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.rest3(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(_, CK.cpos(~K, n, yr)) : Bool}
  %cpos_h(~K, ~L, ~H, n, yr) : {CK.rest3(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(CK.cself(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)), _) : Bool}
  {==}

def rest2_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.rest2(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.rest2(~K, eqs, n, yc, yr, q, ym, pc, pr) : Bool}:
  %ccon_h(~K, ~L, ~H, eqs, n, yc, yr, q, ym, pc, pr) : {CK.rest2(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(_, CK.rest3(~K, eqs, n, yc, yr, ym, pc, pr)) : Bool}
  %rest3_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.rest2(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(CK.ccon(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)), _) : Bool}
  {==}

def rest1_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.rest1(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.rest1(~K, eqs, n, yc, yr, q, ym, pc, pr) : Bool}:
  %factor_h(~K, ~L, ~H, q) : {CK.rest1(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(_, CK.rest2(~K, eqs, n, yc, yr, q, ym, pc, pr)) : Bool}
  %rest2_h(~K, ~L, ~H, eqs, n, yc, yr, q, ym, pc, pr) : {CK.rest1(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(CK.factor(~L, KH.hmap(K, L, H, q)), _) : Bool}
  {==}

def check_go_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {CK.check.go(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) : Bool}:
  %shape_h(~K, ~L, ~H, eqs, n, yc, yr, ym, pc, pr) : {CK.check.go(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(_, CK.rest1(~K, eqs, n, yc, yr, q, ym, pc, pr)) : Bool}
  %rest1_h(~K, ~L, ~H, eqs, n, yc, yr, q, ym, pc, pr) : {CK.check.go(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hmap(K, L, H, q), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == KA.band(CK.shape(~L, eqs, n, KH.hv(~K, ~L, ~H, yc), KH.hv(~K, ~L, ~H, yr), KH.hm(~K, ~L, ~H, ym), KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)), _) : Bool}
  {==}

def check_c_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>) -> {CK.check.c(~L, eqs, n, KH.hcert(~K, ~L, ~H, c)) == CK.check.c(~K, eqs, n, c) : Bool}:
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      check_go_h(~K, ~L, ~H, eqs, n, yc, yr, q, ym, pc, pr)

# the checker's verdict on a certificate's image is its verdict on the
# certificate
def ccheck_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, b: C.Block, c: C.Cert<K>) -> {CK.check(~L, b, KH.hcert(~K, ~L, ~H, c)) == CK.check(~K, b, c) : Bool}:
  match b:
    case C.Block{+eqs, +n}:
      check_c_h(~K, ~L, ~H, eqs, n, c)
