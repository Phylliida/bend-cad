# bend-cad: one constraint's equations through the elimination, for the
# single pass (PLAN-sk13a S4). Proofs only.
#
# The pass walks every position k of the sketch's equations
# (lib/pass.bend: cwalk), reducing those constraint c owns against the
# basis B (its rows EP.rinv). Through the walk, B is the solved equations
# before c (P) followed by c's own before k that are not dropped
# (own_rest), so B is the spec's basis at k, and:
# - a zero residual is a drop, Derivable from B (lib/drvpf.bend);
# - a nonzero one is NotDerivable from B (lib/indpf.bend) and joins it.
# The drops d the walk ends with agree, below k, with the ones it has so
# far (d = X ++ drops so far, X at k or later), so the spec's statements
# about d at k are about what the walk saw: DropsOk.
# The walk also keeps B = picked(positions bp), bp = bp0 ++ us (c's
# equations that joined, distinct, owned by c, not dropped).
#
# Generated from tools/drafts/cwpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./listpf.bend as L
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DR
import ./indpf.bend as IN
import ./conflict.bend as CO
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Lists
# -----

# us below k and none in d: none in k :: d
def nonein_cons(us: List<&2, Nat>, +k: Nat, +d: List<&2, Nat>, +h1: {SV.none_in(us, d) == True{} : Bool}, +h2: {SV.below(us, k) == True{} : Bool}) -> {SV.none_in(us, Con{k, d}) == True{} : Bool}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +hu = Equal.trans(Bool, SV.eq(u, k), SV.eq(k, u), False{}, LI.eq_sym(u, k), KB.ne_of_lt(u, k, LI.band_l(SV.lt(u, k), SV.below(t, k), h2)))
      +hd = KB.bnot_t(SV.mem(u, d), LI.band_l(SV.bnot(SV.mem(u, d)), SV.none_in(t, d), h1))
      LI.band_i(SV.bnot(SV.mem(u, Con{k, d})), SV.none_in(t, Con{k, d}), KB.bnot_f(SV.mem(u, Con{k, d}), LI.bor_f(SV.eq(u, k), SV.mem(u, d), hu, hd)),
        nonein_cons(t, k, d, LI.band_r(SV.bnot(SV.mem(u, d)), SV.none_in(t, d), h1), LI.band_r(SV.lt(u, k), SV.below(t, k), h2)))

def qs_eq(B: List<&2, E.QExpr>, +e: E.QExpr) -> {SP.qsnoc(B, e) == EP.qsnoc(B, e) : List<&2, E.QExpr>}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, E.QExpr>, SP.qsnoc(t, e), EP.qsnoc(t, e), qs_eq(t, e)) : {Con{b, _} == Con{b, EP.qsnoc(t, e)} : List<&2, E.QExpr>}
      {==}

def qs_cat(Q: List<&2, E.QExpr>, +Y: List<&2, E.QExpr>, +e: E.QExpr) -> {EP.qsnoc(SK.cat(Q, Y), e) == SK.cat(Q, EP.qsnoc(Y, e)) : List<&2, E.QExpr>}:
  match Q:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, E.QExpr>, EP.qsnoc(SK.cat(t, Y), e), SK.cat(t, EP.qsnoc(Y, e)), qs_cat(t, Y, e)) : {Con{b, _} == Con{b, SK.cat(t, EP.qsnoc(Y, e))} : List<&2, E.QExpr>}
      {==}

def picked_snoc(+es: List<&2, E.QExpr>, bp: List<&2, Nat>, +k: Nat) -> {SV.picked(es, CO.lsnoc(bp, k)) == EP.qsnoc(SV.picked(es, bp), SV.eqat(es, k)) : List<&2, E.QExpr>}:
  match bp:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, E.QExpr>, SV.picked(es, CO.lsnoc(t, k)), EP.qsnoc(SV.picked(es, t), SV.eqat(es, k)), picked_snoc(es, t, k)) : {Con{SV.eqat(es, b), _} == Con{SV.eqat(es, b), EP.qsnoc(SV.picked(es, t), SV.eqat(es, k))} : List<&2, E.QExpr>}
      {==}

def cat_lsnoc(X: List<&2, Nat>, +us: List<&2, Nat>, +k: Nat) -> {CO.lsnoc(SV.cat(X, us), k) == SV.cat(X, CO.lsnoc(us, k)) : List<&2, Nat>}:
  match X:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, Nat>, CO.lsnoc(SV.cat(t, us), k), SV.cat(t, CO.lsnoc(us, k)), cat_lsnoc(t, us, k)) : {Con{b, _} == Con{b, SV.cat(t, CO.lsnoc(us, k))} : List<&2, Nat>}
      {==}

def catcons_snoc(X: List<&2, Nat>, +k: Nat, +Y: List<&2, Nat>) -> {SV.cat(X, Con{k, Y}) == SV.cat(CO.lsnoc(X, k), Y) : List<&2, Nat>}:
  match X:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, Nat>, SV.cat(t, Con{k, Y}), SV.cat(CO.lsnoc(t, k), Y), catcons_snoc(t, k, Y)) : {Con{b, _} == Con{b, SV.cat(CO.lsnoc(t, k), Y)} : List<&2, Nat>}
      {==}

def rlen_rsnoc(rows: List<&2, EL.Row>, +x: EL.Row) -> {EL.rlen(EL.rsnoc(rows, x)) == 1n+EL.rlen(rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %rlen_rsnoc(t, x) : {1n+EL.rlen(EL.rsnoc(t, x)) == 1n+_ : Nat}
      {==}

def neqs_qsnoc(B: List<&2, E.QExpr>, +e: E.QExpr) -> {SV.neqs(EP.qsnoc(B, e)) == 1n+SV.neqs(B) : Nat}:
  match B:
    case Nil{}:
      {==}
    case Con{b, +t}:
      %neqs_qsnoc(t, e) : {1n+SV.neqs(EP.qsnoc(t, e)) == 1n+_ : Nat}
      {==}

def geall_snoc(X: List<&2, Nat>, +k: Nat, +h: {OW.geall(X, 1n+k) == True{} : Bool}) -> {OW.geall(CO.lsnoc(X, k), k) == True{} : Bool}:
  match X:
    case Nil{}:
      OW.ge_con(k, k, Nil{}, KB.lt_irr(k), {==})
    case Con{+x, +t}:
      OW.ge_con(x, k, CO.lsnoc(t, k), KB.nlt_down(x, k, OW.ge_head(x, 1n+k, t, h)), geall_snoc(t, k, OW.ge_tail(x, 1n+k, t, h)))

# k is in neither X (at k + 1 or later) nor d (below k)
def mem_notk(+X: List<&2, Nat>, +d: List<&2, Nat>, +k: Nat, hX: {OW.geall(X, 1n+k) == True{} : Bool}, hd: {SV.below(d, k) == True{} : Bool}) -> {SV.mem(k, SV.cat(X, d)) == False{} : Bool}:
  Equal.trans(Bool, SV.mem(k, SV.cat(X, d)), SV.bor(SV.mem(k, X), SV.mem(k, d)), False{}, SP.mem_cat(k, X, d),
    LI.bor_f(SV.mem(k, X), SV.mem(k, d), SP.ge_notmem(X, 1n+k, k, hX, KB.lt_succ(k)), KB.below_notmem(d, k, hd)))

def mem_kin(+X: List<&2, Nat>, +d: List<&2, Nat>, +k: Nat) -> {SV.mem(k, SV.cat(X, Con{k, d})) == True{} : Bool}:
  Equal.trans(Bool, SV.mem(k, SV.cat(X, Con{k, d})), SV.bor(SV.mem(k, X), SV.mem(k, Con{k, d})), True{}, SP.mem_cat(k, X, Con{k, d}),
    LI.bor_r(SV.mem(k, X), SV.mem(k, Con{k, d}), LI.mem_hd(k, d)))

# The walk's state
# ----------------

def cw.rows(w: PA.CW) -> List<&2, EL.Row>:
  match w:
    case PA.CW{rows, B, bp, ds, us}:
      rows

def cw.B(w: PA.CW) -> List<&2, E.QExpr>:
  match w:
    case PA.CW{rows, B, bp, ds, us}:
      B

def cw.bp(w: PA.CW) -> List<&2, Nat>:
  match w:
    case PA.CW{rows, B, bp, ds, us}:
      bp

def cw.ds(w: PA.CW) -> List<&2, SV.Drop>:
  match w:
    case PA.CW{rows, B, bp, ds, us}:
      ds

def cwb(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>) -> Bool:
  SV.band(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))))

def cwb_rinv(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {EP.rinv(B, rows, 0n) == True{} : Bool}:
  L.band_l(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h)

def cwb_dbelow(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {SV.below(SV.drops(ds), k) == True{} : Bool}:
  L.band_l(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h))

def cwb_ddist(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {SV.distinct(SV.drops(ds)) == True{} : Bool}:
  L.band_l(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h)))

def cwb_down(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {KB.allo(SV.owners(sk), SV.drops(ds), c) == True{} : Bool}:
  L.band_l(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), L.band_r(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h))))

def cwb_udisj(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {SV.none_in(us, SV.drops(ds)) == True{} : Bool}:
  L.band_l(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))), L.band_r(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), L.band_r(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h)))))

def cwb_udist(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {SV.distinct(us) == True{} : Bool}:
  L.band_l(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)), L.band_r(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))), L.band_r(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), L.band_r(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h))))))

def cwb_ubelow(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {SV.below(us, k) == True{} : Bool}:
  L.band_l(SV.below(us, k), KB.allo(SV.owners(sk), us, c), L.band_r(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)), L.band_r(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))), L.band_r(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), L.band_r(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h)))))))

def cwb_uown(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h: {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}) -> {KB.allo(SV.owners(sk), us, c) == True{} : Bool}:
  L.band_r(SV.below(us, k), KB.allo(SV.owners(sk), us, c), L.band_r(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)), L.band_r(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))), L.band_r(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), L.band_r(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), L.band_r(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h)))))))

def cwb_mk(+sk: SK.Sketch, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, h_rinv: {EP.rinv(B, rows, 0n) == True{} : Bool}, h_dbelow: {SV.below(SV.drops(ds), k) == True{} : Bool}, h_ddist: {SV.distinct(SV.drops(ds)) == True{} : Bool}, h_down: {KB.allo(SV.owners(sk), SV.drops(ds), c) == True{} : Bool}, h_udisj: {SV.none_in(us, SV.drops(ds)) == True{} : Bool}, h_udist: {SV.distinct(us) == True{} : Bool}, h_ubelow: {SV.below(us, k) == True{} : Bool}, h_uown: {KB.allo(SV.owners(sk), us, c) == True{} : Bool}) -> {cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}:
  L.band_i(EP.rinv(B, rows, 0n), SV.band(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))))), h_rinv, L.band_i(SV.below(SV.drops(ds), k), SV.band(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))))), h_dbelow, L.band_i(SV.distinct(SV.drops(ds)), SV.band(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))))), h_ddist, L.band_i(KB.allo(SV.owners(sk), SV.drops(ds), c), SV.band(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)))), h_down, L.band_i(SV.none_in(us, SV.drops(ds)), SV.band(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c))), h_udisj, L.band_i(SV.distinct(us), SV.band(SV.below(us, k), KB.allo(SV.owners(sk), us, c)), h_udist, L.band_i(SV.below(us, k), KB.allo(SV.owners(sk), us, c), h_ubelow, h_uown)))))))

# at position k: B is P followed by c's own before k not dropped, its
# rows' basis, and the equations at bp = bp0 ++ us
def cw.us(w: PA.CW) -> List<&2, Nat>:
  match w:
    case PA.CW{rows, B, bp, ds, us}:
      us

def CWInv(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW) -> Data:
  SK.Both({cwb(sk, c, k, cw.rows(st), cw.B(st), cw.ds(st), cw.us(st)) == True{} : Bool}, SK.Both({EL.rlen(cw.rows(st)) == SV.neqs(cw.B(st)) : Nat}, SK.Both({cw.B(st) == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(cw.ds(st)), k)) : List<&2, E.QExpr>},
    SK.Both({cw.B(st) == SV.picked(SK.Sketch.eqs(sk), cw.bp(st)) : List<&2, E.QExpr>}, {cw.bp(st) == SV.cat(bp0, cw.us(st)) : List<&2, Nat>}))))

# The invariant from k to k + 1
# -----------------------------


def or_skip(+sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>, +k: Nat, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == False{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.own_rest(sk, c, d, 1n+k) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}:
  Equal.trans(List<&2, E.QExpr>, SV.own_rest(sk, c, d, 1n+k), SP.oadd(SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d))), SV.own_rest(sk, c, d, k), SV.eqat(SK.Sketch.eqs(sk), k)), SV.own_rest(sk, c, d, k),
    SP.or_step(SK.Sketch.eqs(sk), SK.Sketch.eqs(sk), SV.owners(sk), c, d, k, 0n, {==}, KB.lt_z(k), hk),
    (%Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), False{}, heq) : {SP.oadd(SV.band(_, SV.bnot(SV.mem(k, d))), SV.own_rest(sk, c, d, k), SV.eqat(SK.Sketch.eqs(sk), k)) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}
      {==}))

def or_drop(+sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>, +k: Nat, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.own_rest(sk, c, Con{k, d}, 1n+k) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}:
  Equal.trans(List<&2, E.QExpr>, SV.own_rest(sk, c, Con{k, d}, 1n+k), SP.oadd(SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, Con{k, d}))), SV.own_rest(sk, c, Con{k, d}, k), SV.eqat(SK.Sketch.eqs(sk), k)), SV.own_rest(sk, c, d, k),
    SP.or_step(SK.Sketch.eqs(sk), SK.Sketch.eqs(sk), SV.owners(sk), c, Con{k, d}, k, 0n, {==}, KB.lt_z(k), hk),
    (%Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), True{}, heq) : {SP.oadd(SV.band(_, SV.bnot(SV.mem(k, Con{k, d}))), SV.own_rest(sk, c, Con{k, d}, k), SV.eqat(SK.Sketch.eqs(sk), k)) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}
      (%Equal.sym(Bool, SV.mem(k, Con{k, d}), True{}, LI.mem_hd(k, d)) : {SP.oadd(SV.band(True{}, SV.bnot(_)), SV.own_rest(sk, c, Con{k, d}, k), SV.eqat(SK.Sketch.eqs(sk), k)) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}
        SP.or_cat(SK.Sketch.eqs(sk), SV.owners(sk), c, [k], d, k, 0n, OW.ge_con(k, k, Nil{}, KB.lt_irr(k), {==})))))

def inv_skip(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, st: PA.CW, hi: CWInv(sk, R, D, c, bp0, k, st), +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == False{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> CWInv(sk, R, D, c, bp0, 1n+k, st):
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      (+hb, q1) = hi
      (hl, q2) = q1
      (hB, q3) = q2
      (hp, hbp) = q3
      (cwb_mk(sk, c, 1n+k, rows, B, ds, us, cwb_rinv(sk, c, k, rows, B, ds, us, hb), KB.below_up(SV.drops(ds), k, cwb_dbelow(sk, c, k, rows, B, ds, us, hb)), cwb_ddist(sk, c, k, rows, B, ds, us, hb), cwb_down(sk, c, k, rows, B, ds, us, hb), cwb_udisj(sk, c, k, rows, B, ds, us, hb), cwb_udist(sk, c, k, rows, B, ds, us, hb), KB.below_up(us, k, cwb_ubelow(sk, c, k, rows, B, ds, us, hb)), cwb_uown(sk, c, k, rows, B, ds, us, hb)),
        (hl, (Equal.trans(List<&2, E.QExpr>, B, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), k)), SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), 1n+k)), hB, Equal.cong(List<&2, E.QExpr>, List<&2, E.QExpr>, y => SK.cat(SV.presolved(sk, R, D, c), y), SV.own_rest(sk, c, SV.drops(ds), k), SV.own_rest(sk, c, SV.drops(ds), 1n+k), Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, SV.drops(ds), 1n+k), SV.own_rest(sk, c, SV.drops(ds), k), or_skip(sk, c, SV.drops(ds), k, heq, hk)))),
        (hp, hbp))))

def inv_drop(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, hi: CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool})
  -> CWInv(sk, R, D, c, bp0, 1n+k, PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}):
  (+hb, q1) = hi
  (hl, q2) = q1
  (hB, q3) = q2
  (hp, hbp) = q3
  +hdb = cwb_dbelow(sk, c, k, rows, B, ds, us, hb)
  (cwb_mk(sk, c, 1n+k, rows, B, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us, cwb_rinv(sk, c, k, rows, B, ds, us, hb),
      LI.band_i(SV.lt(k, 1n+k), SV.below(SV.drops(ds), 1n+k), KB.lt_succ(k), KB.below_up(SV.drops(ds), k, hdb)),
      LI.band_i(SV.bnot(SV.mem(k, SV.drops(ds))), SV.distinct(SV.drops(ds)), KB.bnot_f(SV.mem(k, SV.drops(ds)), KB.below_notmem(SV.drops(ds), k, hdb)), cwb_ddist(sk, c, k, rows, B, ds, us, hb)),
      LI.band_i(SV.eq(SV.nth(SV.owners(sk), k), c), KB.allo(SV.owners(sk), SV.drops(ds), c), heq, cwb_down(sk, c, k, rows, B, ds, us, hb)),
      nonein_cons(us, k, SV.drops(ds), cwb_udisj(sk, c, k, rows, B, ds, us, hb), cwb_ubelow(sk, c, k, rows, B, ds, us, hb)), cwb_udist(sk, c, k, rows, B, ds, us, hb), KB.below_up(us, k, cwb_ubelow(sk, c, k, rows, B, ds, us, hb)), cwb_uown(sk, c, k, rows, B, ds, us, hb)),
    (hl, (Equal.trans(List<&2, E.QExpr>, B, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), k)), SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k)), hB, Equal.cong(List<&2, E.QExpr>, List<&2, E.QExpr>, y => SK.cat(SV.presolved(sk, R, D, c), y), SV.own_rest(sk, c, SV.drops(ds), k), SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k), Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k), SV.own_rest(sk, c, SV.drops(ds), k), or_drop(sk, c, SV.drops(ds), k, heq, hk)))),
    (hp, hbp))))


def keep_B(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat, +B: List<&2, E.QExpr>, +d: List<&2, Nat>, +e: E.QExpr, hB: {B == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, k)) : List<&2, E.QExpr>}, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool},
  +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hm: {SV.mem(k, d) == False{} : Bool}, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}) -> {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, 1n+k)) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, d, 1n+k), SP.oadd(SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d))), SV.own_rest(sk, c, d, k), SV.eqat(SK.Sketch.eqs(sk), k)), SP.or_step(SK.Sketch.eqs(sk), SK.Sketch.eqs(sk), SV.owners(sk), c, d, k, 0n, {==}, KB.lt_z(k), hk)) : {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), _) : List<&2, E.QExpr>}
  %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), True{}, heq) : {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), SP.oadd(SV.band(_, SV.bnot(SV.mem(k, d))), SV.own_rest(sk, c, d, k), SV.eqat(SK.Sketch.eqs(sk), k))) : List<&2, E.QExpr>}
  %Equal.sym(Bool, SV.mem(k, d), False{}, hm) : {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), SP.oadd(SV.band(True{}, SV.bnot(_)), SV.own_rest(sk, c, d, k), SV.eqat(SK.Sketch.eqs(sk), k))) : List<&2, E.QExpr>}
  %Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), SP.qsnoc(SV.own_rest(sk, c, d, k), _)) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, SP.qsnoc(SV.own_rest(sk, c, d, k), e), EP.qsnoc(SV.own_rest(sk, c, d, k), e), qs_eq(SV.own_rest(sk, c, d, k), e)) : {EP.qsnoc(B, e) == SK.cat(SV.presolved(sk, R, D, c), _) : List<&2, E.QExpr>}
  %qs_cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, k), e) : {EP.qsnoc(B, e) == _ : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, B, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, k)), hB) : {EP.qsnoc(_, e) == EP.qsnoc(SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, k)), e) : List<&2, E.QExpr>}
  {==}

def inv_keep(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, hi: CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr})
  -> CWInv(sk, R, D, c, bp0, 1n+k, PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}):
  (+hb, q1) = hi
  (+hl, q2) = q1
  (hB, q3) = q2
  (hp, hbp) = q3
  +hdb = cwb_dbelow(sk, c, k, rows, B, ds, us, hb)
  +hub = cwb_ubelow(sk, c, k, rows, B, ds, us, hb)
  (cwb_mk(sk, c, 1n+k, EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), ds, CO.lsnoc(us, k), EP.new_rinv(B, rows, e, cwb_rinv(sk, c, k, rows, B, ds, us, hb), hl, hne),
      KB.below_up(SV.drops(ds), k, hdb), cwb_ddist(sk, c, k, rows, B, ds, us, hb), cwb_down(sk, c, k, rows, B, ds, us, hb),
      KB.nonein_snoc(us, k, SV.drops(ds), cwb_udisj(sk, c, k, rows, B, ds, us, hb), KB.below_notmem(SV.drops(ds), k, hdb)),
      KB.dist_snoc(us, k, cwb_udist(sk, c, k, rows, B, ds, us, hb), KB.below_notmem(us, k, hub)),
      KB.below_snoc(us, k, 1n+k, KB.below_up(us, k, hub), KB.lt_succ(k)),
      KB.allo_snoc(SV.owners(sk), us, k, c, cwb_uown(sk, c, k, rows, B, ds, us, hb), heq)),
    (Equal.trans(Nat, EL.rlen(EL.rsnoc(rows, EL.row_of(EL.resid(rows, e)))), 1n+EL.rlen(rows), SV.neqs(EP.qsnoc(B, e)), rlen_rsnoc(rows, EL.row_of(EL.resid(rows, e))),
       Equal.trans(Nat, 1n+EL.rlen(rows), 1n+SV.neqs(B), SV.neqs(EP.qsnoc(B, e)), Equal.cong(Nat, Nat, x => 1n+x, EL.rlen(rows), SV.neqs(B), hl), Equal.sym(Nat, SV.neqs(EP.qsnoc(B, e)), 1n+SV.neqs(B), neqs_qsnoc(B, e)))),
    (keep_B(sk, R, D, c, k, B, SV.drops(ds), e, hB, heq, hk, KB.below_notmem(SV.drops(ds), k, hdb), he),
    ((%Equal.sym(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), CO.lsnoc(bp, k)), EP.qsnoc(SV.picked(SK.Sketch.eqs(sk), bp), SV.eqat(SK.Sketch.eqs(sk), k)), picked_snoc(SK.Sketch.eqs(sk), bp, k)) : {EP.qsnoc(B, e) == _ : List<&2, E.QExpr>}
        (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : {EP.qsnoc(B, e) == EP.qsnoc(SV.picked(SK.Sketch.eqs(sk), bp), _) : List<&2, E.QExpr>}
          (%hp : {EP.qsnoc(B, e) == EP.qsnoc(_, e) : List<&2, E.QExpr>}
            {==}))),
      (%Equal.sym(List<&2, Nat>, bp, SV.cat(bp0, us), hbp) : {CO.lsnoc(_, k) == SV.cat(bp0, CO.lsnoc(us, k)) : List<&2, Nat>}
        cat_lsnoc(bp0, us, k))))))

# The walk
# --------
# From position k with state st, ending in fin: fin's drops are some X at k
# or later followed by st's; DropsOk's facts from k on hold for fin's drops;
# and fin satisfies the invariant at the end.


# fin's drops: some X at k or later, then d
def XRel(+dF: List<&2, Nat>, +d: List<&2, Nat>, +k: Nat) -> Data:
  Sigma<&2, &2, List<&2, Nat>, X => SK.Both({dF == SV.cat(X, d) : List<&2, Nat>}, {OW.geall(X, k) == True{} : Bool})>

def CWRes(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, own_k: List<&2, Nat>, +st: PA.CW, +fin: PA.CW) -> Type:
  XRel(SV.drops(cw.ds(fin)), SV.drops(cw.ds(st)), k) & (SV.drops_ok.go(sk, R, D, c, SV.drops(cw.ds(fin)), own_k, k) & CWInv(sk, R, D, c, bp0, SV.neqs(SK.Sketch.eqs(sk)), fin))

def xr_up(+k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: XRel(dF, d, 1n+k)) -> XRel(dF, d, k):
  (+X, xq) = xr
  (hX, hg) = xq
  (X, (hX, OW.geall_up(X, k, hg)))

def xr_drop(+k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: XRel(dF, Con{k, d}, 1n+k)) -> XRel(dF, d, k):
  (+X, xq) = xr
  (hX, hg) = xq
  (CO.lsnoc(X, k), (Equal.trans(List<&2, Nat>, dF, SV.cat(X, Con{k, d}), SV.cat(CO.lsnoc(X, k), d), hX, catcons_snoc(X, k, d)), geall_snoc(X, k, hg)))

def mem_x_f(+k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: XRel(dF, d, 1n+k), hd: {SV.below(d, k) == True{} : Bool}) -> {SV.mem(k, dF) == False{} : Bool}:
  (+X, xq) = xr
  (hX, hg) = xq
  (%Equal.sym(List<&2, Nat>, dF, SV.cat(X, d), hX) : {SV.mem(k, _) == False{} : Bool}
    mem_notk(X, d, k, hg, hd))

def mem_x_t(+k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: XRel(dF, Con{k, d}, 1n+k)) -> {SV.mem(k, dF) == True{} : Bool}:
  (+X, xq) = xr
  (hX, hg) = xq
  (%Equal.sym(List<&2, Nat>, dF, SV.cat(X, Con{k, d}), hX) : {SV.mem(k, _) == True{} : Bool}
    mem_kin(X, d, k))

def or_x(+sk: SK.Sketch, +c: Nat, +k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: XRel(dF, d, k)) -> {SV.own_rest(sk, c, dF, k) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}:
  (+X, xq) = xr
  (hX, hg) = xq
  (%Equal.sym(List<&2, Nat>, dF, SV.cat(X, d), hX) : {SV.own_rest(sk, c, _, k) == SV.own_rest(sk, c, d, k) : List<&2, E.QExpr>}
    SP.or_cat(SK.Sketch.eqs(sk), SV.owners(sk), c, X, d, k, 0n, hg))

def res_skip(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +o: Nat, +ot: List<&2, Nat>, st: PA.CW, +fin: PA.CW, +heo: {SV.eq(o, c) == False{} : Bool}, hi: CWInv(sk, R, D, c, bp0, k, st), r: CWRes(sk, R, D, c, bp0, 1n+k, ot, st, fin))
  -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, fin):
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      (+hb, hq1) = hi
      (+xr, q) = r
      (dr, fr) = q
      (xr_up(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr), (((%Equal.sym(Bool, SV.eq(o, c), False{}, heo) : SV.drops_ok.at(sk, R, D, c, SV.drops(cw.ds(fin)), _, k)
          mem_x_f(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr, cwb_dbelow(sk, c, k, rows, B, ds, us, hb))), dr), fr))

def res_drop(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +o: Nat, +ot: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +fin: PA.CW, +heo: {SV.eq(o, c) == True{} : Bool},
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}, hi: CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}),
  r: CWRes(sk, R, D, c, bp0, 1n+k, ot, PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, fin)) -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, fin):
  (+hb, q1) = hi
  (hl, q2) = q1
  (+hB, q3) = q2
  (+xr, q) = r
  (dr, fr) = q
  +xr2 = xr_drop(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr)
  +LS = DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B)
  (xr2, (((%Equal.sym(Bool, SV.eq(o, c), True{}, heo) : SV.drops_ok.at(sk, R, D, c, SV.drops(cw.ds(fin)), _, k)
      (%Equal.sym(Bool, SV.mem(k, SV.drops(cw.ds(fin))), True{}, mem_x_t(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr)) : SV.drops_ok.mem(sk, R, D, c, SV.drops(cw.ds(fin)), _, k)
        (LS, (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : SV.Ident(_, SV.lin(LS, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(cw.ds(fin)), k))))
          (%Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, SV.drops(cw.ds(fin)), k), SV.own_rest(sk, c, SV.drops(ds), k), or_x(sk, c, k, SV.drops(cw.ds(fin)), SV.drops(ds), xr2)) : SV.Ident(e, SV.lin(LS, SK.cat(SV.presolved(sk, R, D, c), _)))
            (%hB : SV.Ident(e, SV.lin(LS, _))
              DR.derivable(B, rows, e, cwb_rinv(sk, c, k, rows, B, ds, us, hb), hnil))))))), dr), fr))

def res_keep(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +o: Nat, +ot: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +fin: PA.CW, +heo: {SV.eq(o, c) == True{} : Bool},
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}, hi: CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}),
  r: CWRes(sk, R, D, c, bp0, 1n+k, ot, PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, fin)) -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, fin):
  (+hb, q1) = hi
  (+hl, q2) = q1
  (+hB, q3) = q2
  (+xr, q) = r
  (dr, fr) = q
  +xr1 = xr_up(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr)
  (xr1, (((%Equal.sym(Bool, SV.eq(o, c), True{}, heo) : SV.drops_ok.at(sk, R, D, c, SV.drops(cw.ds(fin)), _, k)
      (%Equal.sym(Bool, SV.mem(k, SV.drops(cw.ds(fin))), False{}, mem_x_f(k, SV.drops(cw.ds(fin)), SV.drops(ds), xr, cwb_dbelow(sk, c, k, rows, B, ds, us, hb))) : SV.drops_ok.mem(sk, R, D, c, SV.drops(cw.ds(fin)), _, k)
        (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : (@ls: List<&2, S.Q> -> SV.Ident(_, SV.lin(ls, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(cw.ds(fin)), k)))) -> Empty)
          (%Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, SV.drops(cw.ds(fin)), k), SV.own_rest(sk, c, SV.drops(ds), k), or_x(sk, c, k, SV.drops(cw.ds(fin)), SV.drops(ds), xr1)) : (@ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, SK.cat(SV.presolved(sk, R, D, c), _))) -> Empty)
            (%hB : (@ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, _)) -> Empty)
              IN.indep(B, rows, e, cwb_rinv(sk, c, k, rows, B, ds, us, hb), hl, hne)))))), dr), fr))


def cw_ok.k(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +eb: {EP.isnil(EP.resp(EL.resid(rows, e))) == b : Bool}, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>},
  +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hi: CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), ih: @st2: PA.CW -> CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes(sk, R, D, c, bp0, 1n+k, ot, st2, PA.cwalk(t, SV.owners(sk), c, 1n+k, st2)))
  -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(EP.isnil(EP.resp(EL.resid(rows, e))), k, e, EL.resid(rows, e), rows, B, bp, ds, us))):
  match b:
    case True{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), True{}, eb) : CWRes(sk, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us)))
      res_drop(sk, R, D, c, bp0, k, o, ot, rows, B, bp, ds, us, e, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}), Equal.trans(Bool, SV.eq(o, c), SV.eq(SV.nth(SV.owners(sk), k), c), True{}, Equal.cong(Nat, Bool, x => SV.eq(x, c), o, SV.nth(SV.owners(sk), k), Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho))), heq), OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), eb, hi,
        ih(PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, inv_drop(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt)))
    case False{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), False{}, eb) : CWRes(sk, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us)))
      res_keep(sk, R, D, c, bp0, k, o, ot, rows, B, bp, ds, us, e, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}), Equal.trans(Bool, SV.eq(o, c), SV.eq(SV.nth(SV.owners(sk), k), c), True{}, Equal.cong(Nat, Bool, x => SV.eq(x, c), o, SV.nth(SV.owners(sk), k), Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho))), heq), OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), eb, hi,
        ih(PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, inv_keep(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt, eb, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq))))

def cw_ok.s(st: PA.CW, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>},
  +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, hi: CWInv(sk, R, D, c, bp0, k, st), ih: @st2: PA.CW -> CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes(sk, R, D, c, bp0, 1n+k, ot, st2, PA.cwalk(t, SV.owners(sk), c, 1n+k, st2))) -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.res(k, e, st))):
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      cw_ok.k(EP.isnil(EP.resp(EL.resid(rows, e))), e, t, o, ot, sk, R, D, c, bp0, k, rows, B, bp, ds, us, {==}, heq, hq, ho, hlt, hi, ih)

def cw_ok.o(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW, +eb: {SV.eq(SV.nth(SV.owners(sk), k), c) == b : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>},
  +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hi: CWInv(sk, R, D, c, bp0, k, st), ih: @st2: PA.CW -> CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes(sk, R, D, c, bp0, 1n+k, ot, st2, PA.cwalk(t, SV.owners(sk), c, 1n+k, st2))) -> CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st)):
  match b:
    case True{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), True{}, eb) : CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st)))
      cw_ok.s(st, e, t, o, ot, sk, R, D, c, bp0, k, eb, hq, ho, hlt, hi, ih)
    case False{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), False{}, eb) : CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st)))
      res_skip(sk, R, D, c, bp0, k, o, ot, st, PA.cwalk(t, SV.owners(sk), c, 1n+k, st), (%OW.nth_of(SV.owners(sk), k, o, ot, ho) : {SV.eq(_, c) == False{} : Bool}
        eb), hi, ih(st, inv_skip(sk, R, D, c, bp0, k, st, hi, eb, hlt)))

def len_nc(+o: Nat, +ot: List<&2, Nat>, h: {SV.len(Con{o, ot}) == SV.neqs(Nil{}) : Nat}) -> Empty:
  OW.zs(SV.len(ot), Equal.sym(Nat, 1n+SV.len(ot), 0n, h))

def len_cn(+e: E.QExpr, +t: List<&2, E.QExpr>, h: {SV.len(Nil{}) == SV.neqs(Con{e, t}) : Nat}) -> Empty:
  OW.zs(SV.neqs(t), h)

# the walk from position k
def cw_ok(es: List<&2, E.QExpr>, own_k: List<&2, Nat>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == own_k : List<&2, Nat>}, +hl: {SV.len(own_k) == SV.neqs(es) : Nat},
  +hk: {Nat.add(k, SV.neqs(es)) == SV.neqs(SK.Sketch.eqs(sk)) : Nat}, +hi: CWInv(sk, R, D, c, bp0, k, st)) -> CWRes(sk, R, D, c, bp0, k, own_k, st, PA.cwalk(es, SV.owners(sk), c, k, st)):
  match es own_k:
    case Nil{} Nil{}:
      ((Nil{}, ({==}, {==})), (Unit{}, (%Equal.trans(Nat, k, Nat.add(k, 0n), SV.neqs(SK.Sketch.eqs(sk)), LN.add_zero(k), hk) : CWInv(sk, R, D, c, bp0, _, st)
        hi)))
    case Nil{} Con{+o, +ot}:
      absurd(CWRes(sk, R, D, c, bp0, k, Con{o, ot}, st, st), len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd(CWRes(sk, R, D, c, bp0, k, Nil{}, st, PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st)), len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      cw_ok.o(SV.eq(SV.nth(SV.owners(sk), k), c), e, t, o, ot, sk, R, D, c, bp0, k, st, {==}, hq, ho, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), hi,
        st2 => h2 => cw_ok(t, ot, sk, R, D, c, bp0, 1n+k, st2, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), OW.ndrop_step(k, SV.owners(sk), o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl),
          Equal.trans(Nat, 1n+Nat.add(k, SV.neqs(t)), Nat.add(k, 1n+SV.neqs(t)), SV.neqs(SK.Sketch.eqs(sk)), LN.add_succ(k, SV.neqs(t)), hk), h2))

# From the pass's state
# ---------------------

def inv_b(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW, hi: CWInv(sk, R, D, c, bp0, k, st)) -> {cwb(sk, c, k, cw.rows(st), cw.B(st), cw.ds(st), cw.us(st)) == True{} : Bool}:
  (h, q) = hi
  h

def own_rest_zero(+sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>) -> {SV.own_rest(sk, c, d, 0n) == Nil{} : List<&2, E.QExpr>}:
  SP.or_nil(SK.Sketch.eqs(sk), SV.owners(sk), c, d, 0n, 0n, {==})

def qcat_nil(xs: List<&2, E.QExpr>) -> {xs == SK.cat(xs, Nil{}) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %qcat_nil(t) : {Con{h, t} == Con{h, _} : List<&2, E.QExpr>}
      {==}

def ncat_nil(xs: List<&2, Nat>) -> {xs == SV.cat(xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %ncat_nil(t) : {Con{h, t} == Con{h, _} : List<&2, Nat>}
      {==}

# the walk starts with the solved equations before c, their rows and
# positions, and nothing dropped or added
def cw_start(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hB: {B == SV.presolved(sk, R, D, c) : List<&2, E.QExpr>}, hp: {B == SV.picked(SK.Sketch.eqs(sk), bp) : List<&2, E.QExpr>}) -> CWInv(sk, R, D, c, bp, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}):
  (cwb_mk(sk, c, 0n, rows, B, Nil{}, Nil{}, hr, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    (hl, ((%Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, Nil{}, 0n), Nil{}, own_rest_zero(sk, c, Nil{})) : {B == SK.cat(SV.presolved(sk, R, D, c), _) : List<&2, E.QExpr>}
      (%qcat_nil(SV.presolved(sk, R, D, c)) : {B == _ : List<&2, E.QExpr>}
        hB)), (hp, ncat_nil(bp)))))


def drops_ok_of(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, h1: {SV.distinct(d) == True{} : Bool}, h2: {SV.below(d, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, dr: SV.drops_ok.go(sk, R, D, c, d, SV.owners(sk), 0n)) -> SV.DropsOk(sk, R, D, c, d):
  (LI.band_i(SV.distinct(d), SV.below(d, SV.neqs(SK.Sketch.eqs(sk))), h1, h2), dr)

def cw_final.r2(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, dr: SV.drops_ok.go(sk, R, D, c, SV.drops(cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}))), SV.owners(sk), 0n), +fr: CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})))
  -> (SV.DropsOk(sk, R, D, c, SV.drops(cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})))) & CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}))):
  +hb = inv_b(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}), fr)
  (drops_ok_of(sk, R, D, c, SV.drops(cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}))), cwb_ddist(sk, c, SV.neqs(SK.Sketch.eqs(sk)), cw.rows(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.B(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.us(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), hb), cwb_dbelow(sk, c, SV.neqs(SK.Sketch.eqs(sk)), cw.rows(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.B(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), cw.us(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})), hb), dr), fr)

def cw_final.r(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, r: CWRes(sk, R, D, c, bp, 0n, SV.owners(sk), PA.CW{rows, B, bp, Nil{}, Nil{}}, PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})))
  -> (SV.DropsOk(sk, R, D, c, SV.drops(cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})))) & CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}))):
  (xr, q) = r
  (dr, fr) = q
  cw_final.r2(sk, R, D, c, rows, B, bp, dr, fr)

# the walk's end: DropsOk for its drops, and the invariant at the end
def cw_final(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hB: {B == SV.presolved(sk, R, D, c) : List<&2, E.QExpr>}, hp: {B == SV.picked(SK.Sketch.eqs(sk), bp) : List<&2, E.QExpr>}) -> (SV.DropsOk(sk, R, D, c, SV.drops(cw.ds(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}})))) & CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}))):
  cw_final.r(sk, R, D, c, rows, B, bp, cw_ok(SK.Sketch.eqs(sk), SV.owners(sk), sk, R, D, c, bp, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, {==}, {==}, OW.len_owners(sk), {==}, cw_start(sk, R, D, c, rows, B, bp, hr, hl, hB, hp)))

# The walk drops only c's equations
# ---------------------------------

def cwo.pick(b: Bool, +own: List<&2, Nat>, +c: Nat, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +ho: {SV.eq(SV.nth(own, k), c) == True{} : Bool},
  +h: {KB.allo(own, SV.drops(ds), c) == True{} : Bool}) -> {KB.allo(own, SV.drops(cw.ds(PA.cw.pick(b, k, e, r, rows, B, bp, ds, us))), c) == True{} : Bool}:
  match b:
    case True{}:
      LI.band_i(SV.eq(SV.nth(own, k), c), KB.allo(own, SV.drops(ds), c), ho, h)
    case False{}:
      h

def cwo.at(b: Bool, +own: List<&2, Nat>, +c: Nat, +k: Nat, +e: E.QExpr, st: PA.CW, +eb: {SV.eq(SV.nth(own, k), c) == b : Bool}, +h: {KB.allo(own, SV.drops(cw.ds(st)), c) == True{} : Bool})
  -> {KB.allo(own, SV.drops(cw.ds(PA.cw.at(b, k, e, st))), c) == True{} : Bool}:
  match b:
    case True{}:
      match st:
        case PA.CW{+rows, +B, +bp, +ds, +us}:
          cwo.pick(EP.isnil(EP.resp(EL.resid(rows, e))), own, c, k, e, EL.resid(rows, e), rows, B, bp, ds, us, eb, h)
    case False{}:
      h

def cw_own(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, +st: PA.CW, +h: {KB.allo(own, SV.drops(cw.ds(st)), c) == True{} : Bool}) -> {KB.allo(own, SV.drops(cw.ds(PA.cwalk(es, own, c, k, st))), c) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      cw_own(t, own, c, 1n+k, PA.cw.at(SV.eq(SV.nth(own, k), c), k, e, st), cwo.at(SV.eq(SV.nth(own, k), c), own, c, k, e, st, {==}, h))
