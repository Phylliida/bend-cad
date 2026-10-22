# bend-cad: the plan checker (lib/plan.bend) gives the same verdict through
# a map of computing numbers h : K -> L (lib/khom.bend): PL.check in L of the
# box's and the plan's images is PL.check in K of the box and the plan, and
# so is PL.check_sides. Untrusted; for the word verdict (PLAN-sk13w W5).

# Generated from tools/drafts/planhpf.draft by tools/expand.py; edit the
# draft.


import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/sketch.bend as SK
import ./certdef.bend as C
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./plan.bend as PL
import ./khom.bend as KH
import ./khompf.bend as KP
import ./certhpf.bend as CH

# Lists and equality
# ------------------

def ktake_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat, u: N.KVec(~K)) -> {PL.ktake(~L, n, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, PL.ktake(~K, n, u)) : N.KVec(~L)}:
  match n u:
    case 0n u:
      {==}
    case 1n++k Nil{}:
      {==}
    case 1n++k Con{+a, +t}:
      %ktake_h(~K, ~L, ~H, k, t) : {Con{KH.hmap(K, L, H, a), PL.ktake(~L, k, KH.hv(~K, ~L, ~H, t))} == Con{KH.hmap(K, L, H, a), _} : N.KVec(~L)}
      {==}

def pkdrop_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat, u: N.KVec(~K)) -> {PL.kdrop(~L, n, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, PL.kdrop(~K, n, u)) : N.KVec(~L)}:
  match n u:
    case 0n u:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{a, t}:
      pkdrop_h(~K, ~L, ~H, k, t)

def keq_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K), +b: N.NC(K)) -> {PL.keq(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)) == PL.keq(~K, a, b) : Bool}:
  %KH.h_cmp(K, L, H)(a, b) : {PL.keq.go(N.ncmp(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b))) == PL.keq.go(_) : Bool}
  {==}

def keq0r_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K)) -> {PL.keq(~L, KH.hmap(K, L, H, a), N.nzero(L)) == PL.keq(~K, a, N.nzero(K)) : Bool}:
  %KP.hz_r(~K, ~L, ~H) : {PL.keq(~L, KH.hmap(K, L, H, a), _) == PL.keq(~K, a, N.nzero(K)) : Bool}
  keq_h(~K, ~L, ~H, a, N.nzero(K))

def kveq_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K), w: N.KVec(~K)) -> {PL.kveq(~L, KH.hv(~K, ~L, ~H, u), KH.hv(~K, ~L, ~H, w)) == PL.kveq(~K, u, w) : Bool}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +ws}:
      {==}
    case Con{+a, +us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %keq_h(~K, ~L, ~H, a, b) : {KA.band(PL.keq(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), PL.kveq(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(_, PL.kveq(~K, us, ws)) : Bool}
      %kveq_h(~K, ~L, ~H, us, ws) : {KA.band(PL.keq(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), PL.kveq(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(PL.keq(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), _) : Bool}
      {==}

def pinz_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, np: Nat, gr: N.KVec(~K)) -> {PL.pinz(~L, np, KH.hv(~K, ~L, ~H, gr)) == PL.pinz(~K, np, gr) : Bool}:
  match np gr:
    case 0n gr:
      {==}
    case 1n++k Nil{}:
      {==}
    case 1n++k Con{+x, +t}:
      %keq0r_h(~K, ~L, ~H, x) : {KA.band(PL.keq(~L, KH.hmap(K, L, H, x), N.nzero(L)), PL.pinz(~L, k, KH.hv(~K, ~L, ~H, t))) == KA.band(_, PL.pinz(~K, k, t)) : Bool}
      %pinz_h(~K, ~L, ~H, k, t) : {KA.band(PL.keq(~L, KH.hmap(K, L, H, x), N.nzero(L)), PL.pinz(~L, k, KH.hv(~K, ~L, ~H, t))) == KA.band(PL.keq(~L, KH.hmap(K, L, H, x), N.nzero(L)), _) : Bool}
      {==}

# The checker
# -----------

def pcont_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +gc: N.KVec(~K), +gr: N.KVec(~K), pars: List<&2, Nat>, pc: N.KVec(~K), pr: N.KVec(~K)) -> {PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), pars, KH.hv(~K, ~L, ~H, pc), KH.hv(~K, ~L, ~H, pr)) == PL.pcont(~K, gc, gr, pars, pc, pr) : Bool}:
  match pars pc pr:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{+r, +rs}:
      {==}
    case Nil{} Con{+c, +cs} Nil{}:
      {==}
    case Nil{} Con{+c, +cs} Con{+r, +rs}:
      {==}
    case Con{+v, +vs} Nil{} Nil{}:
      {==}
    case Con{+v, +vs} Nil{} Con{+r, +rs}:
      {==}
    case Con{+v, +vs} Con{+c, +cs} Nil{}:
      {==}
    case Con{+v, +vs} Con{+c, +cs} Con{+r, +rs}:
      %KP.kle_h(~K, ~L, ~H, N.nadd(K, KA.kabs(~K, KA.ksub(~K, KB.klook(~K, gc, v), c)), KB.klook(~K, gr, v)), r) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(_, PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %KH.h_add(K, L, H)(KA.kabs(~K, KA.ksub(~K, KB.klook(~K, gc, v), c)), KB.klook(~K, gr, v)) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, _, KH.hmap(K, L, H, r)), PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %KP.kabs_h(~K, ~L, ~H, KA.ksub(~K, KB.klook(~K, gc, v), c)) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, N.nadd(L, _, KH.hmap(K, L, H, KB.klook(~K, gr, v))), KH.hmap(K, L, H, r)), PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %KP.ksub_h(~K, ~L, ~H, KB.klook(~K, gc, v), c) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, _), KH.hmap(K, L, H, KB.klook(~K, gr, v))), KH.hmap(K, L, H, r)), PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %KP.klook_h(~K, ~L, ~H, gc, v) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, _, KH.hmap(K, L, H, c))), KH.hmap(K, L, H, KB.klook(~K, gr, v))), KH.hmap(K, L, H, r)), PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %KP.klook_h(~K, ~L, ~H, gr, v) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), _), KH.hmap(K, L, H, r)), PL.pcont(~K, gc, gr, vs, cs, rs)) : Bool}
      %pcont_h(~K, ~L, ~H, gc, gr, vs, cs, rs) : {KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vs, KH.hv(~K, ~L, ~H, cs), KH.hv(~K, ~L, ~H, rs))) == KA.band(KA.kle(~L, N.nadd(L, KA.kabs(~L, KA.ksub(~L, KB.klook(~L, KH.hv(~K, ~L, ~H, gc), v), KH.hmap(K, L, H, c))), KB.klook(~L, KH.hv(~K, ~L, ~H, gr), v)), KH.hmap(K, L, H, r)), _) : Bool}
      {==}

# a block's checks
def block_ok_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>) -> {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == PL.block_ok(~K, gc, gr, es, o, n, pars, c) : Bool}:
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), _), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %CH.ccheck_h(~K, ~L, ~H, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(_, KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %kveq_h(~K, ~L, ~H, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(_, KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %CH.yc_h(~K, ~L, ~H, c) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, _, KH.hv(~K, ~L, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %ktake_h(~K, ~L, ~H, n, PL.kdrop(~K, o, gc)) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), _), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %pkdrop_h(~K, ~L, ~H, o, gc) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, _)), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %kveq_h(~K, ~L, ~H, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(_, PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %KP.kfit_h(~K, ~L, ~H, n, C.Cert.yr(K, c)) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, _, KH.hv(~K, ~L, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %CH.yr_h(~K, ~L, ~H, c) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, _), KH.hv(~K, ~L, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %ktake_h(~K, ~L, ~H, n, PL.kdrop(~K, o, gr)) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c))), _), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %pkdrop_h(~K, ~L, ~H, o, gr) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c))), PL.ktake(~L, n, _)), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) : Bool}
  %pcont_h(~K, ~L, ~H, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c))), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gr)))), _))))))) : Bool}
  %CH.pc_h(~K, ~L, ~H, c) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c))), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gr)))), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), pars, _, KH.hv(~K, ~L, ~H, C.Cert.pr(K, c)))))))))) : Bool}
  %CH.pr_h(~K, ~L, ~H, c) : {PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)) == KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~L, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, KH.hcert(~K, ~L, ~H, c)), KA.band(PL.kveq(~L, C.Cert.yc(L, KH.hcert(~K, ~L, ~H, c)), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gc)))), KA.band(PL.kveq(~L, KA.kfit(~L, n, C.Cert.yr(L, KH.hcert(~K, ~L, ~H, c))), PL.ktake(~L, n, PL.kdrop(~L, o, KH.hv(~K, ~L, ~H, gr)))), PL.pcont(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), pars, C.Cert.pc(L, KH.hcert(~K, ~L, ~H, c)), _)))))))) : Bool}
  {==}

def walk_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +gc: N.KVec(~K), +gr: N.KVec(~K), bs: List<&2, PL.PBlock<K>>, +es: List<&2, E.QExpr>, +o: Nat) -> {PL.walk(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), KH.hpbs(~K, ~L, ~H, bs), es, o) == PL.walk(~K, gc, gr, bs, es, o) : Bool}:
  match bs:
    case Nil{}:
      %KP.klen_h(~K, ~L, ~H, gc) : {KA.band(KA.nateq(o, KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), PL.isnil(es)) == KA.band(KA.nateq(o, _), PL.isnil(es)) : Bool}
      {==}
    case Con{PL.PBlock{+n, +pars, +c}, +t}:
      %block_ok_h(~K, ~L, ~H, gc, gr, es, o, n, pars, c) : {KA.band(PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)), PL.walk(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), KH.hpbs(~K, ~L, ~H, t), PL.dropq(n, es), Nat.add(o, n))) == KA.band(_, PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n))) : Bool}
      %walk_h(~K, ~L, ~H, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)) : {KA.band(PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)), PL.walk(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), KH.hpbs(~K, ~L, ~H, t), PL.dropq(n, es), Nat.add(o, n))) == KA.band(PL.block_ok(~L, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), es, o, n, pars, KH.hcert(~K, ~L, ~H, c)), _) : Bool}
      {==}

def check_p_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>) -> {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == PL.check.p(~K, eqs, gc, gr, np, bs) : Bool}:
  %KP.klen_h(~K, ~L, ~H, gr) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(_, KA.klen(~K, gc)), KA.band(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, gr)), _), KA.band(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))))) : Bool}
  %KP.kvle_h(~K, ~L, ~H, Nil{}, gr) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, gr)), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(_, KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, gr)), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, gr)), KA.band(KA.natle(np, _), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))))) : Bool}
  %pinz_h(~K, ~L, ~H, np, gr) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, gr)), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, gr)), KA.band(KA.natle(np, KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(_, PL.walk(~K, gc, gr, bs, eqs, np))))) : Bool}
  %walk_h(~K, ~L, ~H, gc, gr, bs, eqs, np) : {PL.check.p(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(KA.nateq(KA.klen(~L, KH.hv(~K, ~L, ~H, gr)), KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, gr)), KA.band(KA.natle(np, KA.klen(~L, KH.hv(~K, ~L, ~H, gc))), KA.band(PL.pinz(~L, np, KH.hv(~K, ~L, ~H, gr)), _)))) : Bool}
  {==}

def kperm_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +u: N.KVec(~K), vp: List<&2, Nat>) -> {PL.kperm(~L, KH.hv(~K, ~L, ~H, u), vp) == KH.hv(~K, ~L, ~H, PL.kperm(~K, u, vp)) : N.KVec(~L)}:
  match vp:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      %KP.klook_h(~K, ~L, ~H, u, v) : {Con{KB.klook(~L, KH.hv(~K, ~L, ~H, u), v), PL.kperm(~L, KH.hv(~K, ~L, ~H, u), t)} == Con{_, KH.hv(~K, ~L, ~H, PL.kperm(~K, u, t))} : N.KVec(~L)}
      %kperm_h(~K, ~L, ~H, u, t) : {Con{KB.klook(~L, KH.hv(~K, ~L, ~H, u), v), PL.kperm(~L, KH.hv(~K, ~L, ~H, u), t)} == Con{KB.klook(~L, KH.hv(~K, ~L, ~H, u), v), _} : N.KVec(~L)}
      {==}

def check_r_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>) -> {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) : Bool}:
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, _, 0n), KA.band(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), 0n), KA.band(PL.pars_ok(_, vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))))) : Bool}
  %KP.klen_h(~K, ~L, ~H, gc) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), 0n), KA.band(PL.pars_ok(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(_, eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))))) : Bool}
  %check_p_h(~K, ~L, ~H, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), 0n), KA.band(PL.pars_ok(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), eqs), _))))) : Bool}
  %kperm_h(~K, ~L, ~H, gc, vp) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), 0n), KA.band(PL.pars_ok(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), eqs), PL.check.p(~L, PL.reorder(vp, eqs, ep), _, KH.hv(~K, ~L, ~H, PL.kperm(~K, gr, vp)), np, KH.hpbs(~K, ~L, ~H, bs))))))) : Bool}
  %kperm_h(~K, ~L, ~H, gr, vp) : {PL.check.r(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), vp, ep, np, KH.hpbs(~K, ~L, ~H, bs)) == KA.band(PL.present(vp, KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), 0n), KA.band(PL.pars_ok(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~L, KH.hv(~K, ~L, ~H, gc)), eqs), PL.check.p(~L, PL.reorder(vp, eqs, ep), PL.kperm(~L, KH.hv(~K, ~L, ~H, gc), vp), _, np, KH.hpbs(~K, ~L, ~H, bs))))))) : Bool}
  {==}

# the plan checks against the box's image and the plan's image exactly when
# it checks against the box and the plan
def pcheck_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>) -> {PL.check(~L, eqs, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr), KH.hplan(~K, ~L, ~H, p)) == PL.check(~K, eqs, gc, gr, p) : Bool}:
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      check_r_h(~K, ~L, ~H, eqs, gc, gr, vp, ep, np, bs)

# Side conditions
# ---------------

def side_ok_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +box: List<&2, KB.KB<K>>, s: SK.Side) -> {PL.side_ok(~L, KH.hbv(~K, ~L, ~H, box), s) == PL.side_ok(~K, box, s) : Bool}:
  match s:
    case SK.Gt0{+e}:
      %KP.held_h(~K, ~L, ~H, e) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(_, KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e))))) : Bool}
      %KP.klt0_h(~K, ~L, ~H, KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), _) : Bool}
      %KP.ksub_h(~K, ~L, ~H, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e))) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), _)) : Bool}
      %KP.kbc_h(~K, ~L, ~H, KB.kball(~K, box, e)) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, _, KH.hmap(K, L, H, KB.KB.r(K, KB.kball(~K, box, e)))))) : Bool}
      %KP.kball_h(~K, ~L, ~H, box, e) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, _), KH.hmap(K, L, H, KB.KB.r(K, KB.kball(~K, box, e)))))) : Bool}
      %KP.kbr_h(~K, ~L, ~H, KB.kball(~K, box, e)) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), _))) : Bool}
      %KP.kball_h(~K, ~L, ~H, box, e) : {KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.klt(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, _)))) : Bool}
      {==}
    case SK.Ge0{+e}:
      %KP.held_h(~K, ~L, ~H, e) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(_, KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e))))) : Bool}
      %KP.kle0_h(~K, ~L, ~H, KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), _) : Bool}
      %KP.ksub_h(~K, ~L, ~H, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e))) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), _)) : Bool}
      %KP.kbc_h(~K, ~L, ~H, KB.kball(~K, box, e)) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, _, KH.hmap(K, L, H, KB.KB.r(K, KB.kball(~K, box, e)))))) : Bool}
      %KP.kball_h(~K, ~L, ~H, box, e) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, _), KH.hmap(K, L, H, KB.KB.r(K, KB.kball(~K, box, e)))))) : Bool}
      %KP.kbr_h(~K, ~L, ~H, KB.kball(~K, box, e)) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), _))) : Bool}
      %KP.kball_h(~K, ~L, ~H, box, e) : {KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e))))) == KA.band(KB.held(~L, e), KA.kle(~L, N.nzero(L), KA.ksub(~L, KB.KB.c(L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e)), KB.KB.r(L, _)))) : Bool}
      {==}

def sides_ok_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +box: List<&2, KB.KB<K>>, ss: List<&2, SK.Side>) -> {PL.sides_ok(~L, KH.hbv(~K, ~L, ~H, box), ss) == PL.sides_ok(~K, box, ss) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      %side_ok_h(~K, ~L, ~H, box, s) : {KA.band(PL.side_ok(~L, KH.hbv(~K, ~L, ~H, box), s), PL.sides_ok(~L, KH.hbv(~K, ~L, ~H, box), t)) == KA.band(_, PL.sides_ok(~K, box, t)) : Bool}
      %sides_ok_h(~K, ~L, ~H, box, t) : {KA.band(PL.side_ok(~L, KH.hbv(~K, ~L, ~H, box), s), PL.sides_ok(~L, KH.hbv(~K, ~L, ~H, box), t)) == KA.band(PL.side_ok(~L, KH.hbv(~K, ~L, ~H, box), s), _) : Bool}
      {==}

# every side condition holds over the box's image exactly when over the box
def check_sides_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> {PL.check_sides(~L, sides, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr)) == PL.check_sides(~K, sides, gc, gr) : Bool}:
  %KP.kvle_h(~K, ~L, ~H, Nil{}, gr) : {PL.check_sides(~L, sides, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr)) == KA.band(_, PL.sides_ok(~K, CK.zipb(~K, gc, gr), sides)) : Bool}
  %sides_ok_h(~K, ~L, ~H, CK.zipb(~K, gc, gr), sides) : {PL.check_sides(~L, sides, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr)) == KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, gr)), _) : Bool}
  %CH.zipb_h(~K, ~L, ~H, gc, gr) : {PL.check_sides(~L, sides, KH.hv(~K, ~L, ~H, gc), KH.hv(~K, ~L, ~H, gr)) == KA.band(KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, gr)), PL.sides_ok(~L, _, sides)) : Bool}
  {==}
