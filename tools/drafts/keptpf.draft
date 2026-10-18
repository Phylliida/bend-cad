# bend-cad: the kept system is the full system at the kept indices
# (DESIGN §10.4, C2c). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/keptpf.draft lib/keptpf.bend
#
# The sketch less its red constraints has as equations the full system's
# equations whose constraint is not red (keepq), and those are the full
# system at the indices T whose owner is not red, in order (pickk). The
# red stage matched equations S: none owned by a red constraint, all
# below the equation count (lib/redpf.bend: red_nred, red_below), so S
# lies in T, and it is as long as the kept system, which is as long as T:
# S and T are the same set. good is iota filtered by S, so it is iota
# filtered by T, which is T. Hence kept = the full system at good, and
# reading the kept system through the positions of good is reading the
# full system directly (kept_reorder).

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./solve.bend as SO
import ./plan.bend as PL
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D
import ./redpf.bend as RP
import ./tarjanpf.bend as TJ
import ./structpf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The kept equations, by owner
# ----------------------------

def keepq.go(b: Bool, e: E.QExpr, rest: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{e, rest}

# the equations xs (owners os) whose owner is not in red
def keepq(xs: List<&2, E.QExpr>, os: List<&2, Nat>, +red: List<&2, Nat>) -> List<&2, E.QExpr>:
  match xs os:
    case Nil{} os:
      Nil{}
    case Con{e, et} Nil{}:
      Nil{}
    case Con{e, et} Con{o, ot}:
      keepq.go(SV.mem(o, red), e, keepq(et, ot, red))

def kq_drop(c: List<&2, E.QExpr>, +re: List<&2, E.QExpr>, +ro: List<&2, Nat>, +i: Nat, +red: List<&2, Nat>, +h: {SV.mem(i, red) == True{} : Bool}) -> {keepq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), red) == keepq(re, ro, red) : List<&2, E.QExpr>}:
  match c:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Bool, SV.mem(i, red), True{}, h) : {keepq.go(_, e, keepq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), red)) == keepq(re, ro, red) : List<&2, E.QExpr>}
      kq_drop(t, re, ro, i, red, h)

def kq_keep(c: List<&2, E.QExpr>, +re: List<&2, E.QExpr>, +ro: List<&2, Nat>, +i: Nat, +red: List<&2, Nat>, +h: {SV.mem(i, red) == False{} : Bool}) -> {keepq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), red) == SK.cat(c, keepq(re, ro, red)) : List<&2, E.QExpr>}:
  match c:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Bool, SV.mem(i, red), False{}, h) : {keepq.go(_, e, keepq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), red)) == Con{e, SK.cat(t, keepq(re, ro, red))} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, keepq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), red), SK.cat(t, keepq(re, ro, red)), kq_keep(t, re, ro, i, red, h)) : {Con{e, _} == Con{e, SK.cat(t, keepq(re, ro, red))} : List<&2, E.QExpr>}
      {==}

def kept_go(+es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +red: List<&2, Nat>, b: Bool, +e: {SV.mem(i, red) == b : Bool}, ih: {SK.Sketch.eqs.go(es, SV.mark.cons(red, t, 1n+i)) == keepq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), red) : List<&2, E.QExpr>}) -> {SK.Sketch.eqs.go(es, Con{SK.Rec{id, b, kd}, SV.mark.cons(red, t, 1n+i)}) == keepq(SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t)), SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, kd)), i), SV.owners.go(es, t, 1n+i)), red) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      +c = SK.Constraint.eqs(es, kd)
      +re = SK.Sketch.eqs.go(es, t)
      +ro = SV.owners.go(es, t, 1n+i)
      %Equal.sym(List<&2, E.QExpr>, keepq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), red), keepq(re, ro, red), kq_drop(c, re, ro, i, red, e)) : {SK.Sketch.eqs.go(es, SV.mark.cons(red, t, 1n+i)) == _ : List<&2, E.QExpr>}
      ih
    case False{}:
      +c = SK.Constraint.eqs(es, kd)
      +re = SK.Sketch.eqs.go(es, t)
      +ro = SV.owners.go(es, t, 1n+i)
      %Equal.sym(List<&2, E.QExpr>, keepq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), red), SK.cat(c, keepq(re, ro, red)), kq_keep(c, re, ro, i, red, e)) : {SK.cat(c, SK.Sketch.eqs.go(es, SV.mark.cons(red, t, 1n+i))) == _ : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SK.Sketch.eqs.go(es, SV.mark.cons(red, t, 1n+i)), keepq(re, ro, red), ih) : {SK.cat(c, _) == SK.cat(c, keepq(re, ro, red)) : List<&2, E.QExpr>}
      {==}

# marking red constraints driven keeps the equations of the others
def kept_eq(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +red: List<&2, Nat>) -> {SK.Sketch.eqs.go(es, SV.mark.cons(red, cs, i)) == keepq(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, i), red) : List<&2, E.QExpr>}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +kd}, +t}:
      kept_eq(es, t, 1n+i, red)
    case Con{SK.Rec{+id, False{}, +kd}, +t}:
      kept_go(es, id, kd, t, i, red, SV.mem(i, red), {==}, kept_eq(es, t, 1n+i, red))

def kept_keepq(sk: SK.Sketch, +red: List<&2, Nat>) -> {SK.Sketch.eqs(SV.mark(red, sk)) == keepq(SK.Sketch.eqs(sk), SV.owners(sk), red) : List<&2, E.QExpr>}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      kept_eq(es, cs, 0n, red)

def len_cat_reps(n: Nat, +i: Nat, +rest: List<&2, Nat>) -> {SV.len(SV.cat(SV.reps(n, i), rest)) == Nat.add(n, SV.len(rest)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Nat, SV.len(SV.cat(SV.reps(m, i), rest)), Nat.add(m, SV.len(rest)), len_cat_reps(m, i, rest)) : {1n+_ == 1n+Nat.add(m, SV.len(rest)) : Nat}
      {==}

# one owner per equation
def own_len(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat) -> {SV.len(SV.owners.go(es, cs, i)) == SV.neqs(SK.Sketch.eqs.go(es, cs)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +kd}, +t}:
      own_len(es, t, 1n+i)
    case Con{SK.Rec{+id, False{}, +kd}, +t}:
      +c = SK.Constraint.eqs(es, kd)
      +n = SV.neqs(c)
      %Equal.sym(Nat, SV.len(SV.cat(SV.reps(n, i), SV.owners.go(es, t, 1n+i))), Nat.add(n, SV.len(SV.owners.go(es, t, 1n+i))), len_cat_reps(n, i, SV.owners.go(es, t, 1n+i))) : {_ == SV.neqs(SK.cat(c, SK.Sketch.eqs.go(es, t))) : Nat}
      %Equal.sym(Nat, SV.neqs(SK.cat(c, SK.Sketch.eqs.go(es, t))), Nat.add(n, SV.neqs(SK.Sketch.eqs.go(es, t))), RP.neqs_cat(c, SK.Sketch.eqs.go(es, t))) : {Nat.add(n, SV.len(SV.owners.go(es, t, 1n+i))) == _ : Nat}
      %Equal.sym(Nat, SV.len(SV.owners.go(es, t, 1n+i)), SV.neqs(SK.Sketch.eqs.go(es, t)), own_len(es, t, 1n+i)) : {Nat.add(n, _) == Nat.add(n, SV.neqs(SK.Sketch.eqs.go(es, t))) : Nat}
      {==}

def owners_len(sk: SK.Sketch) -> {SV.len(SV.owners(sk)) == SV.neqs(SK.Sketch.eqs(sk)) : Nat}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      own_len(es, cs, 0n)

def lenq_neqs(es: List<&2, E.QExpr>) -> {ST.len.q(es) == SV.neqs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, +t}:
      %Equal.sym(Nat, ST.len.q(t), SV.neqs(t), lenq_neqs(t)) : {1n+_ == 1n+SV.neqs(t) : Nat}
      {==}

# Picking equations by index
# --------------------------

# equation j - k of et for each j of xs
def pickk(+et: List<&2, E.QExpr>, +k: Nat, xs: List<&2, Nat>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+j, t}:
      Con{PL.eqget(et, PL.minus(k, j)), pickk(et, k, t)}

def sel2.go(b: Bool, +k: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{k, rest}

# the indices (from k) whose owner in ot is not in red
def sel2(ot: List<&2, Nat>, +k: Nat, +red: List<&2, Nat>) -> List<&2, Nat>:
  match ot:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      sel2.go(SV.mem(o, red), k, sel2(t, 1n+k, red))

# every entry is at least m
def geb(xs: List<&2, Nat>, +m: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(KA.natle(m, x), geb(t, m))

def geb_weak(xs: List<&2, Nat>, +m: Nat, +h: {geb(xs, 1n+m) == True{} : Bool}) -> {geb(xs, m) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(KA.natle(m, x), geb(t, m), KA.natle_pred(m, x, L.band_l(KA.natle(1n+m, x), geb(t, 1n+m), h)), geb_weak(t, m, L.band_r(KA.natle(1n+m, x), geb(t, 1n+m), h)))


def sel2_ge.go(b: Bool, +k: Nat, +r: List<&2, Nat>, +h: {geb(r, k) == True{} : Bool}) -> {geb(sel2.go(b, k, r), k) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.band_i(KA.natle(k, k), geb(r, k), KA.natle_refl(k), h)

def sel2_ge(ot: List<&2, Nat>, +k: Nat, +red: List<&2, Nat>) -> {geb(sel2(ot, k, red), k) == True{} : Bool}:
  match ot:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      sel2_ge.go(SV.mem(o, red), k, sel2(t, 1n+k, red), geb_weak(sel2(t, 1n+k, red), k, sel2_ge(t, 1n+k, red)))

def minus_self(k: Nat) -> {PL.minus(k, k) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      minus_self(j)

def minus_succ(k: Nat, j: Nat, h: {KA.natle(k, j) == True{} : Bool}) -> {PL.minus(k, 1n+j) == 1n+PL.minus(k, j) : Nat}:
  match k j:
    case 0n j:
      {==}
    case 1n+k2 0n:
      absurd({PL.minus(1n+k2, 1n) == 1n+PL.minus(1n+k2, 0n) : Nat}, KA.ft(h))
    case 1n+k2 1n+j2:
      minus_succ(k2, j2, h)

def pk_elt(+e: E.QExpr, +et: List<&2, E.QExpr>, +k: Nat, j: Nat, h: {KA.natle(1n+k, j) == True{} : Bool}) -> {PL.eqget(Con{e, et}, PL.minus(k, j)) == PL.eqget(et, PL.minus(1n+k, j)) : E.QExpr}:
  match j:
    case 0n:
      absurd({PL.eqget(Con{e, et}, PL.minus(k, 0n)) == PL.eqget(et, PL.minus(1n+k, 0n)) : E.QExpr}, KA.ft(h))
    case 1n++j2:
      %Equal.sym(Nat, PL.minus(k, 1n+j2), 1n+PL.minus(k, j2), minus_succ(k, j2, h)) : {PL.eqget(Con{e, et}, _) == PL.eqget(et, PL.minus(k, j2)) : E.QExpr}
      {==}

# indices all past k: picking from e :: et at k is picking from et at k + 1
def pk_shift(+e: E.QExpr, +et: List<&2, E.QExpr>, +k: Nat, xs: List<&2, Nat>, +h: {geb(xs, 1n+k) == True{} : Bool}) -> {pickk(Con{e, et}, k, xs) == pickk(et, 1n+k, xs) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(E.QExpr, PL.eqget(Con{e, et}, PL.minus(k, j)), PL.eqget(et, PL.minus(1n+k, j)), pk_elt(e, et, k, j, L.band_l(KA.natle(1n+k, j), geb(t, 1n+k), h))) : {Con{_, pickk(Con{e, et}, k, t)} == Con{PL.eqget(et, PL.minus(1n+k, j)), pickk(et, 1n+k, t)} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, pickk(Con{e, et}, k, t), pickk(et, 1n+k, t), pk_shift(e, et, k, t, L.band_r(KA.natle(1n+k, j), geb(t, 1n+k), h))) : {Con{PL.eqget(et, PL.minus(1n+k, j)), _} == Con{PL.eqget(et, PL.minus(1n+k, j)), pickk(et, 1n+k, t)} : List<&2, E.QExpr>}
      {==}

def kq_go(+e: E.QExpr, +et: List<&2, E.QExpr>, +ot: List<&2, Nat>, +k: Nat, +red: List<&2, Nat>, b: Bool, ih: {keepq(et, ot, red) == pickk(et, 1n+k, sel2(ot, 1n+k, red)) : List<&2, E.QExpr>}) -> {keepq.go(b, e, keepq(et, ot, red)) == pickk(Con{e, et}, k, sel2.go(b, k, sel2(ot, 1n+k, red))) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      +r = sel2(ot, 1n+k, red)
      %Equal.sym(List<&2, E.QExpr>, pickk(Con{e, et}, k, r), pickk(et, 1n+k, r), pk_shift(e, et, k, r, sel2_ge(ot, 1n+k, red))) : {keepq(et, ot, red) == _ : List<&2, E.QExpr>}
      ih
    case False{}:
      +r = sel2(ot, 1n+k, red)
      %Equal.sym(Nat, PL.minus(k, k), 0n, minus_self(k)) : {Con{e, keepq(et, ot, red)} == Con{PL.eqget(Con{e, et}, _), pickk(Con{e, et}, k, r)} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, pickk(Con{e, et}, k, r), pickk(et, 1n+k, r), pk_shift(e, et, k, r, sel2_ge(ot, 1n+k, red))) : {Con{e, keepq(et, ot, red)} == Con{e, _} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, keepq(et, ot, red), pickk(et, 1n+k, r), ih) : {Con{e, _} == Con{e, pickk(et, 1n+k, r)} : List<&2, E.QExpr>}
      {==}

# keeping by owner is picking the indices of non-red owners
def kq_pick(et: List<&2, E.QExpr>, ot: List<&2, Nat>, +k: Nat, +red: List<&2, Nat>, hl: {SV.neqs(et) == SV.len(ot) : Nat}) -> {keepq(et, ot, red) == pickk(et, k, sel2(ot, k, red)) : List<&2, E.QExpr>}:
  match et ot:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot2}:
      absurd({Nil{} == pickk(Nil{}, k, sel2(Con{o, ot2}, k, red)) : List<&2, E.QExpr>}, KA.ft(D.eq_of(0n, 1n+SV.len(ot2), hl)))
    case Con{+e, +et2} Nil{}:
      absurd({Nil{} == pickk(Con{e, et2}, k, Nil{}) : List<&2, E.QExpr>}, KA.ft(D.eq_of(1n+SV.neqs(et2), 0n, hl)))
    case Con{+e, +et2} Con{+o, +ot2}:
      kq_go(e, et2, ot2, k, red, SV.mem(o, red), kq_pick(et2, ot2, 1n+k, red, LN.succ_inj(SV.neqs(et2), SV.len(ot2), hl)))

def pk_len(+et: List<&2, E.QExpr>, +k: Nat, xs: List<&2, Nat>) -> {SV.neqs(pickk(et, k, xs)) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Nat, SV.neqs(pickk(et, k, t)), SV.len(t), pk_len(et, k, t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

# Which indices are kept
# ----------------------

def sel2go_mem(b: Bool, +k: Nat, +r: List<&2, Nat>, +x: Nat, h: {SV.mem(x, r) == True{} : Bool}) -> {SV.mem(x, sel2.go(b, k, r)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.mem_tl(x, k, r, h)

# index i of ot (owner not red) is in sel2(ot, k, red) as k + i
def sel2_mem(ot: List<&2, Nat>, +k: Nat, i: Nat, +red: List<&2, Nat>, hi: {KA.natle(1n+i, SV.len(ot)) == True{} : Bool}, hn: {SV.mem(SV.nth(ot, i), red) == False{} : Bool}) -> {SV.mem(Nat.add(k, i), sel2(ot, k, red)) == True{} : Bool}:
  match ot i:
    case Nil{} i:
      absurd({SV.mem(Nat.add(k, i), Nil{}) == True{} : Bool}, KA.ft(hi))
    case Con{+o, +t} 0n:
      %Equal.sym(Bool, SV.mem(o, red), False{}, hn) : {SV.mem(Nat.add(k, 0n), sel2.go(_, k, sel2(t, 1n+k, red))) == True{} : Bool}
      %LN.add_zero(k) : {SV.mem(_, Con{k, sel2(t, 1n+k, red)}) == True{} : Bool}
      L.mem_hd(k, sel2(t, 1n+k, red))
    case Con{+o, +t} 1n++i2:
      %LN.add_succ(k, i2) : {SV.mem(_, sel2.go(SV.mem(o, red), k, sel2(t, 1n+k, red))) == True{} : Bool}
      sel2go_mem(SV.mem(o, red), k, sel2(t, 1n+k, red), Nat.add(1n+k, i2), sel2_mem(t, 1n+k, i2, red, hi, hn))

def nlt_rw(+m: Nat, +a: Nat, +n: Nat, e: {a == n : Nat}, h: {KA.natle(1n+m, n) == True{} : Bool}) -> {KA.natle(1n+m, a) == True{} : Bool}:
  %Equal.sym(Nat, a, n, e) : {KA.natle(1n+m, _) == True{} : Bool}
  h

# the matched equations S (below n = |own|, none owned by red) lie in T
def st_go(xs: List<&2, Nat>, +own: List<&2, Nat>, +red: List<&2, Nat>, +n: Nat, +hb: {SV.below(xs, n) == True{} : Bool}, +hl: {SV.len(own) == n : Nat}, +hn: {RP.nred(own, red, xs) == True{} : Bool}) -> {L.subl(xs, sel2(own, 0n, red)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      L.subl_con(m, t, sel2(own, 0n, red), sel2_mem(own, 0n, m, red, nlt_rw(m, SV.len(own), n, hl, D.below_hd(m, t, n, hb)), L.bnot_f(SV.mem(SV.nth(own, m), red), L.band_l(SV.bnot(SV.mem(SV.nth(own, m), red)), RP.nred(own, red, t), hn))), st_go(t, own, red, n, D.below_tl(m, t, n, hb), hl, L.band_r(SV.bnot(SV.mem(SV.nth(own, m), red)), RP.nred(own, red, t), hn)))

# Filtering iota
# --------------

# each entry of xs is in a exactly when in b (as the solver tests it)
def mag(xs: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(TJ.biff(ST.mem(x, a), ST.mem(x, b)), mag(t, a, b))

def inter_cong(xs: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {mag(xs, a, b) == True{} : Bool}) -> {ST.inter(xs, a) == ST.inter(xs, b) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, ST.mem(x, a), ST.mem(x, b), TJ.biff_eq(ST.mem(x, a), ST.mem(x, b), L.band_l(TJ.biff(ST.mem(x, a), ST.mem(x, b)), mag(t, a, b), h))) : {ST.minus.go(ST.bnot(_), x, ST.inter(t, a)) == ST.minus.go(ST.bnot(ST.mem(x, b)), x, ST.inter(t, b)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, ST.inter(t, a), ST.inter(t, b), inter_cong(t, a, b, L.band_r(TJ.biff(ST.mem(x, a), ST.mem(x, b)), mag(t, a, b), h))) : {ST.minus.go(ST.bnot(ST.mem(x, b)), x, _) == ST.minus.go(ST.bnot(ST.mem(x, b)), x, ST.inter(t, b)) : List<&2, Nat>}
      {==}

def st_eqv(+x: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, h1: {L.subl(a, b) == True{} : Bool}, h2: {L.subl(b, a) == True{} : Bool}) -> {ST.mem(x, a) == ST.mem(x, b) : Bool}:
  %L.mem_sv(x, a) : {_ == ST.mem(x, b) : Bool}
  %L.mem_sv(x, b) : {SV.mem(x, a) == _ : Bool}
  TJ.mem_eqv(x, a, b, h1, h2)

def mag_sub(xs: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h1: {L.subl(a, b) == True{} : Bool}, +h2: {L.subl(b, a) == True{} : Bool}) -> {mag(xs, a, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(TJ.biff(ST.mem(x, a), ST.mem(x, b)), mag(t, a, b), TJ.biff_i(ST.mem(x, a), ST.mem(x, b), st_eqv(x, a, b, h1, h2)), mag_sub(t, a, b, h1, h2))

# k < j: j /= k
def ne_of_gt(j: Nat, k: Nat, h: {KA.natle(1n+k, j) == True{} : Bool}) -> {KA.nateq(j, k) == False{} : Bool}:
  match j k:
    case 0n k:
      absurd({KA.nateq(0n, k) == False{} : Bool}, KA.ft(h))
    case 1n+j2 0n:
      {==}
    case 1n+j2 1n+k2:
      ne_of_gt(j2, k2, h)

def mag_iota.hd(+j: Nat, +k: Nat, +y: List<&2, Nat>, h: {KA.natle(1n+k, j) == True{} : Bool}) -> {TJ.biff(ST.mem(j, Con{k, y}), ST.mem(j, y)) == True{} : Bool}:
  %Equal.sym(Bool, KA.nateq(j, k), False{}, ne_of_gt(j, k, h)) : {TJ.biff(ST.bor(_, ST.mem(j, y)), ST.mem(j, y)) == True{} : Bool}
  TJ.biff_refl(ST.mem(j, y))

# the entries of iota(n, j), all past k, are in k :: y exactly when in y
def mag_iota(n: Nat, +j: Nat, +k: Nat, +y: List<&2, Nat>, +h: {KA.natle(1n+k, j) == True{} : Bool}) -> {mag(ST.iota(n, j), Con{k, y}, y) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.band_i(TJ.biff(ST.mem(j, Con{k, y}), ST.mem(j, y)), mag(ST.iota(m, 1n+j), Con{k, y}, y), mag_iota.hd(j, k, y, h), mag_iota(m, 1n+j, k, y, KA.natle_succ(1n+k, j, h)))

# all of xs past k: k not in xs
def notin_geb(xs: List<&2, Nat>, +k: Nat, +h: {geb(xs, 1n+k) == True{} : Bool}) -> {ST.mem(k, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, KA.nateq(k, x), False{}, KA.natlt_ne(k, x, L.band_l(KA.natle(1n+k, x), geb(t, 1n+k), h))) : {ST.bor(_, ST.mem(k, t)) == False{} : Bool}
      notin_geb(t, k, L.band_r(KA.natle(1n+k, x), geb(t, 1n+k), h))

def selfil.go(b: Bool, +k: Nat, +t: List<&2, Nat>, +red: List<&2, Nat>, ih: {ST.inter(ST.iota(SV.len(t), 1n+k), sel2(t, 1n+k, red)) == sel2(t, 1n+k, red) : List<&2, Nat>}) -> {ST.inter(Con{k, ST.iota(SV.len(t), 1n+k)}, sel2.go(b, k, sel2(t, 1n+k, red))) == sel2.go(b, k, sel2(t, 1n+k, red)) : List<&2, Nat>}:
  match b:
    case True{}:
      +y = sel2(t, 1n+k, red)
      %Equal.sym(Bool, ST.mem(k, y), False{}, notin_geb(y, k, sel2_ge(t, 1n+k, red))) : {ST.minus.go(ST.bnot(_), k, ST.inter(ST.iota(SV.len(t), 1n+k), y)) == y : List<&2, Nat>}
      ih
    case False{}:
      +y = sel2(t, 1n+k, red)
      %Equal.sym(Bool, KA.nateq(k, k), True{}, KA.nateq_refl(k)) : {ST.minus.go(ST.bnot(ST.bor(_, ST.mem(k, y))), k, ST.inter(ST.iota(SV.len(t), 1n+k), Con{k, y})) == Con{k, y} : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, ST.inter(ST.iota(SV.len(t), 1n+k), Con{k, y}), ST.inter(ST.iota(SV.len(t), 1n+k), y), inter_cong(ST.iota(SV.len(t), 1n+k), Con{k, y}, y, mag_iota(SV.len(t), 1n+k, k, y, KA.natle_refl(1n+k)))) : {Con{k, _} == Con{k, y} : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, ST.inter(ST.iota(SV.len(t), 1n+k), y), y, ih) : {Con{k, _} == Con{k, y} : List<&2, Nat>}
      {==}

# iota filtered by the kept indices is the kept indices
def selfil(ot: List<&2, Nat>, +k: Nat, +red: List<&2, Nat>) -> {ST.inter(ST.iota(SV.len(ot), k), sel2(ot, k, red)) == sel2(ot, k, red) : List<&2, Nat>}:
  match ot:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      selfil.go(SV.mem(o, red), k, t, red, selfil(t, 1n+k, red))

# Reading the kept system
# -----------------------

def eqget_pick.go(+et: List<&2, E.QExpr>, +x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, e: {KA.nateq(x, y) == b : Bool}, h: {SV.mem(x, Con{y, t}) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {PL.eqget(pickk(et, 0n, t), ST.pos(x, t)) == PL.eqget(et, x) : E.QExpr}) -> {PL.eqget(Con{PL.eqget(et, y), pickk(et, 0n, t)}, ST.pos.go(b, ST.pos(x, t))) == PL.eqget(et, x) : E.QExpr}:
  match b:
    case True{}:
      %KA.nateq_ok(x, y, e) : {PL.eqget(et, _) == PL.eqget(et, x) : E.QExpr}
      {==}
    case False{}:
      ih(L.mem_tl_inv(x, y, t, h, SP.sv_ne(x, y, e)))

# entry pos(x, xs) of the system picked at xs is equation x
def eqget_pick(+et: List<&2, E.QExpr>, xs: List<&2, Nat>, +x: Nat, h: {SV.mem(x, xs) == True{} : Bool}) -> {PL.eqget(pickk(et, 0n, xs), ST.pos(x, xs)) == PL.eqget(et, x) : E.QExpr}:
  match xs:
    case Nil{}:
      absurd({PL.eqget(Nil{}, 0n) == PL.eqget(et, x) : E.QExpr}, KA.ft(h))
    case Con{+y, +t}:
      eqget_pick.go(et, x, y, t, KA.nateq(x, y), {==}, h, p => eqget_pick(et, t, x, p))

# reading the picked system through positions in good is reading et
def re_pick(ys: List<&2, Nat>, +vp: List<&2, Nat>, +et: List<&2, E.QExpr>, +good: List<&2, Nat>, +hs: {L.subl(ys, good) == True{} : Bool}) -> {PL.reorder(vp, pickk(et, 0n, good), ST.positions(ys, good)) == PL.reorder(vp, et, ys) : List<&2, E.QExpr>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(E.QExpr, PL.eqget(pickk(et, 0n, good), ST.pos(y, good)), PL.eqget(et, y), eqget_pick(et, good, y, L.subl_hd(y, t, good, hs))) : {Con{PL.rnv(vp, _), PL.reorder(vp, pickk(et, 0n, good), ST.positions(t, good))} == Con{PL.rnv(vp, PL.eqget(et, y)), PL.reorder(vp, et, t)} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, PL.reorder(vp, pickk(et, 0n, good), ST.positions(t, good)), PL.reorder(vp, et, t), re_pick(t, vp, et, good, L.subl_tl(y, t, good, hs))) : {Con{PL.rnv(vp, PL.eqget(et, y)), _} == Con{PL.rnv(vp, PL.eqget(et, y)), PL.reorder(vp, et, t)} : List<&2, E.QExpr>}
      {==}

# The kept system of a sketch
# ---------------------------
# own: the sketch's owners, red: its red constraints, S: the equations
# the red stage matched, T: the indices whose owner is not red.

def kept_pick(+sk: SK.Sketch) -> {SO.kept(sk) == pickk(SK.Sketch.eqs(sk), 0n, sel2(SV.owners(sk), 0n, SO.red_of(sk))) : List<&2, E.QExpr>}:
  +full = SK.Sketch.eqs(sk)
  +own = SV.owners(sk)
  +red = SO.red_of(sk)
  %Equal.sym(List<&2, E.QExpr>, SO.kept(sk), keepq(full, own, red), kept_keepq(sk, red)) : {_ == pickk(full, 0n, sel2(own, 0n, red)) : List<&2, E.QExpr>}
  kq_pick(full, own, 0n, red, Equal.sym(Nat, SV.len(own), SV.neqs(full), owners_len(sk)))

def st_sub(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {L.subl(ST.somes(SO.CS.vm(SO.rs_of(sk))), sel2(SV.owners(sk), 0n, SO.red_of(sk))) == True{} : Bool}:
  +nv = SO.nvars(sk)
  st_go(ST.somes(SO.CS.vm(SO.rs_of(sk))), SV.owners(sk), SO.red_of(sk), SV.neqs(SK.Sketch.eqs(sk)), RP.red_below(sk, nv, ha), owners_len(sk), RP.red_nred(sk, nv, ha))

def len_ts(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SV.len(sel2(SV.owners(sk), 0n, SO.red_of(sk))) == SV.len(ST.somes(SO.CS.vm(SO.rs_of(sk)))) : Nat}:
  +full = SK.Sketch.eqs(sk)
  +t = sel2(SV.owners(sk), 0n, SO.red_of(sk))
  +ss = ST.somes(SO.CS.vm(SO.rs_of(sk)))
  %Equal.sym(Nat, SV.len(ss), SV.neqs(SO.kept(sk)), RP.red_cnt(sk, SO.nvars(sk), ha)) : {SV.len(t) == _ : Nat}
  %Equal.sym(List<&2, E.QExpr>, SO.kept(sk), pickk(full, 0n, t), kept_pick(sk)) : {SV.len(t) == SV.neqs(_) : Nat}
  Equal.sym(Nat, SV.neqs(pickk(full, 0n, t)), SV.len(t), pk_len(full, 0n, t))

def ts_sub(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {L.subl(sel2(SV.owners(sk), 0n, SO.red_of(sk)), ST.somes(SO.CS.vm(SO.rs_of(sk)))) == True{} : Bool}:
  +t = sel2(SV.owners(sk), 0n, SO.red_of(sk))
  +ss = ST.somes(SO.CS.vm(SO.rs_of(sk)))
  SP.pigc(ss, t, RP.red_dist(sk, SO.nvars(sk), ha), st_sub(sk, ha), SP.le_of_eq(SV.len(t), SV.len(ss), len_ts(sk, ha)))

# the kept indices are those whose constraint is not red
def good_t(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SO.good_of(sk) == sel2(SV.owners(sk), 0n, SO.red_of(sk)) : List<&2, Nat>}:
  +full = SK.Sketch.eqs(sk)
  +own = SV.owners(sk)
  +t = sel2(own, 0n, SO.red_of(sk))
  +ss = ST.somes(SO.CS.vm(SO.rs_of(sk)))
  %Equal.sym(List<&2, Nat>, ST.inter(ST.iota(ST.len.q(full), 0n), ss), ST.inter(ST.iota(ST.len.q(full), 0n), t), inter_cong(ST.iota(ST.len.q(full), 0n), ss, t, mag_sub(ST.iota(ST.len.q(full), 0n), ss, t, st_sub(sk, ha), ts_sub(sk, ha)))) : {_ == t : List<&2, Nat>}
  %Equal.sym(Nat, ST.len.q(full), SV.neqs(full), lenq_neqs(full)) : {ST.inter(ST.iota(_, 0n), t) == t : List<&2, Nat>}
  %owners_len(sk) : {ST.inter(ST.iota(_, 0n), t) == t : List<&2, Nat>}
  selfil(own, 0n, SO.red_of(sk))

# the kept system is the full system at the kept indices
def kept_good(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SO.kept(sk) == pickk(SK.Sketch.eqs(sk), 0n, SO.good_of(sk)) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, Nat>, SO.good_of(sk), sel2(SV.owners(sk), 0n, SO.red_of(sk)), good_t(sk, ha)) : {SO.kept(sk) == pickk(SK.Sketch.eqs(sk), 0n, _) : List<&2, E.QExpr>}
  kept_pick(sk)

# as many kept equations as kept indices
def kept_len(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SV.neqs(SO.kept(sk)) == SV.len(SO.good_of(sk)) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, SO.kept(sk), pickk(SK.Sketch.eqs(sk), 0n, SO.good_of(sk)), kept_good(sk, ha)) : {SV.neqs(_) == SV.len(SO.good_of(sk)) : Nat}
  pk_len(SK.Sketch.eqs(sk), 0n, SO.good_of(sk))

# reading the kept system through positions in good is reading the full
# system at the indices themselves
def kept_reorder(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}, +vp: List<&2, Nat>, ys: List<&2, Nat>, hs: {L.subl(ys, SO.good_of(sk)) == True{} : Bool}) -> {PL.reorder(vp, SO.kept(sk), ST.positions(ys, SO.good_of(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, SO.kept(sk), pickk(SK.Sketch.eqs(sk), 0n, SO.good_of(sk)), kept_good(sk, ha)) : {PL.reorder(vp, _, ST.positions(ys, SO.good_of(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}
  re_pick(ys, vp, SK.Sketch.eqs(sk), SO.good_of(sk), hs)
