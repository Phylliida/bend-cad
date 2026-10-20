# bend-cad: the solved equations, constraint by constraint, for the single
# pass (PLAN-sk13a S4). Proofs only.
# - own_rest(sk, c, d, i + 1) is own_rest(sk, c, d, i) with equation i
#   after it, if c owns it and it is not in d (or_step); entries of d at
#   i or later do not matter (or_cat).
# - presolved(sk, R, D, c + 1) is presolved(sk, R, D, c) followed by c's
#   own equations not dropped, when c is kept (ps_kept: owners are sorted);
#   it is presolved(sk, R, D, c) when c is red or owns nothing (ps_same);
#   it is nothing at 0 (ps_zero).
# - solved(sk, R, D) is presolved at the number of constraints.
# Walks over the equations from position j, with es_j = qdrop(j, ES) and
# own_j = ndrop(j, own).

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./kbpf.bend as KB
import ./ownpf.bend as OW

def absurd(-A: Type, x: Empty) -> A:
  match x:

def qsnoc(xs: List<&2, E.QExpr>, +e: E.QExpr) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Con{e, Nil{}}
    case Con{h, t}:
      Con{h, qsnoc(t, e)}

# X, with e after it if b
def oadd(b: Bool, +X: List<&2, E.QExpr>, +e: E.QExpr) -> List<&2, E.QExpr>:
  match b:
    case True{}:
      qsnoc(X, e)
    case False{}:
      X

def band_ag(b: Bool, +x1: Bool, +x2: Bool, h: {b == True{} : Bool} -> {x1 == x2 : Bool}) -> {SV.band(b, x1) == SV.band(b, x2) : Bool}:
  match b:
    case True{}:
      h({==})
    case False{}:
      {==}

def qisnil(xs: List<&2, E.QExpr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def qnil_con(+e: E.QExpr, +t: List<&2, E.QExpr>, h: {Nil{} == Con{e, t} : List<&2, E.QExpr>}) -> Empty:
  KA.tf(Equal.cong(List<&2, E.QExpr>, Bool, x => qisnil(x), Nil{}, Con{e, t}, h))

# a position with an equation is below their number
def lt_qdrop.go(xs: List<&2, E.QExpr>, j: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, h: {OW.qdrop(j, xs) == Con{e, t} : List<&2, E.QExpr>}) -> {SV.lt(j, SV.neqs(xs)) == True{} : Bool}:
  match xs j:
    case Nil{} 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, qnil_con(e, t, h))
    case Nil{} 1n+i:
      absurd({SV.lt(1n+i, 0n) == True{} : Bool}, qnil_con(e, t, h))
    case Con{x, xt} 0n:
      {==}
    case Con{x, xt} 1n+i:
      lt_qdrop.go(xt, i, e, t, h)

def lt_qdrop(+ES: List<&2, E.QExpr>, j: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, h: {OW.qdrop(j, ES) == Con{e, t} : List<&2, E.QExpr>}) -> {SV.lt(j, SV.neqs(ES)) == True{} : Bool}:
  lt_qdrop.go(ES, j, e, t, h)

# no position with an equation: not below their number
def nlt_qdrop(xs: List<&2, E.QExpr>, j: Nat, h: {OW.qdrop(j, xs) == Nil{} : List<&2, E.QExpr>}) -> {SV.lt(j, SV.neqs(xs)) == False{} : Bool}:
  match xs j:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+i:
      {==}
    case Con{+x, +xt} 0n:
      absurd({SV.lt(0n, SV.neqs(Con{x, xt})) == False{} : Bool}, qnil_con(x, xt, Equal.sym(List<&2, E.QExpr>, Con{x, xt}, Nil{}, h)))
    case Con{x, xt} 1n+i:
      nlt_qdrop(xt, i, h)

# c's own equations from i on
# ---------------------------

def or_nil(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +j: Nat, +h: {SV.lt(j, i) == False{} : Bool}) -> {SV.own_rest.go(es, own, c, d, i, j) == Nil{} : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      %Equal.sym(Bool, SV.lt(j, i), False{}, h) : {SV.solved.pick(SV.band(_, SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)) == Nil{} : List<&2, E.QExpr>}
      or_nil(t, own, c, d, i, 1n+j, KB.nlt_up(j, i, h))

def pk_nil(b: Bool, +e: E.QExpr) -> {SV.solved.pick(b, e, Nil{}) == oadd(b, Nil{}, e) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pk_oadd(x: Bool, q: Bool, +e: E.QExpr, +X: List<&2, E.QExpr>, +f: E.QExpr) -> {SV.solved.pick(x, e, oadd(q, X, f)) == oadd(q, SV.solved.pick(x, e, X), f) : List<&2, E.QExpr>}:
  match x q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def or_step.eq(+e: E.QExpr, +t: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, hq: {OW.qdrop(i, ES) == Con{e, t} : List<&2, E.QExpr>})
  -> {SV.own_rest.go(Con{e, t}, own, c, d, 1n+i, i) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, i), SV.eqat(ES, i)) : List<&2, E.QExpr>}:
  %Equal.sym(Bool, SV.lt(i, 1n+i), True{}, KB.lt_succ(i)) : {SV.solved.pick(SV.band(_, SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d)))), e, SV.own_rest.go(t, own, c, d, 1n+i, 1n+i)) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, i), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, SV.own_rest.go(t, own, c, d, 1n+i, 1n+i), Nil{}, or_nil(t, own, c, d, 1n+i, 1n+i, KB.lt_irr(1n+i))) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e, _) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, i), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(Bool, SV.lt(i, i), False{}, KB.lt_irr(i)) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e, Nil{}) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.solved.pick(SV.band(_, SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+i)), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, SV.own_rest.go(t, own, c, d, i, 1n+i), Nil{}, or_nil(t, own, c, d, i, 1n+i, KB.nlt_up(i, i, KB.lt_irr(i)))) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e, Nil{}) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), _, SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(E.QExpr, SV.eqat(ES, i), e, OW.eqat_of(ES, i, e, t, hq)) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e, Nil{}) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), Nil{}, _) : List<&2, E.QExpr>}
  pk_nil(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e)

def or_step.lt(+e: E.QExpr, +t: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +j: Nat, +hlt: {SV.lt(j, i) == True{} : Bool},
  ih: {SV.own_rest.go(t, own, c, d, 1n+i, 1n+j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(t, own, c, d, i, 1n+j), SV.eqat(ES, i)) : List<&2, E.QExpr>})
  -> {SV.own_rest.go(Con{e, t}, own, c, d, 1n+i, j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, j), SV.eqat(ES, i)) : List<&2, E.QExpr>}:
  %Equal.sym(Bool, SV.lt(j, 1n+i), True{}, KB.lt_up(j, i, hlt)) : {SV.solved.pick(SV.band(_, SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, 1n+i, 1n+j)) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.solved.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(Bool, SV.lt(j, i), True{}, hlt) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), e, SV.own_rest.go(t, own, c, d, 1n+i, 1n+j)) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.solved.pick(SV.band(_, SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, SV.own_rest.go(t, own, c, d, 1n+i, 1n+j), oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(t, own, c, d, i, 1n+j), SV.eqat(ES, i)), ih) : {SV.solved.pick(SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), e, _) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.solved.pick(SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)), SV.eqat(ES, i)) : List<&2, E.QExpr>}
  pk_oadd(SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), e, SV.own_rest.go(t, own, c, d, i, 1n+j), SV.eqat(ES, i))

def or_step.c(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +j: Nat, +eb: {SV.eq(j, i) == b : Bool},
  +hq: {OW.qdrop(j, ES) == Con{e, t} : List<&2, E.QExpr>}, +hji: {SV.lt(i, j) == False{} : Bool},
  ih: {SV.lt(i, 1n+j) == False{} : Bool} -> {SV.own_rest.go(t, own, c, d, 1n+i, 1n+j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(t, own, c, d, i, 1n+j), SV.eqat(ES, i)) : List<&2, E.QExpr>})
  -> {SV.own_rest.go(Con{e, t}, own, c, d, 1n+i, j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, j), SV.eqat(ES, i)) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      %Equal.sym(Nat, j, i, LI.eq_ok(j, i, eb)) : {SV.own_rest.go(Con{e, t}, own, c, d, 1n+i, _) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(Con{e, t}, own, c, d, i, _), SV.eqat(ES, i)) : List<&2, E.QExpr>}
      or_step.eq(e, t, ES, own, c, d, i, (%LI.eq_ok(j, i, eb) : {OW.qdrop(_, ES) == Con{e, t} : List<&2, E.QExpr>}
        hq))
    case False{}:
      +hlt = KB.lt_of_nlt(j, i, hji, eb)
      or_step.lt(e, t, ES, own, c, d, i, j, hlt, ih(KB.lt_nle_s(j, i, hlt)))

# c's own equations before i + 1: those before i, then equation i if c
# owns it and it is not in d (i an equation's position, j <= i)
def or_step(es: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +j: Nat, +hq: {OW.qdrop(j, ES) == es : List<&2, E.QExpr>}, +hji: {SV.lt(i, j) == False{} : Bool}, +hi: {SV.lt(i, SV.neqs(ES)) == True{} : Bool})
  -> {SV.own_rest.go(es, own, c, d, 1n+i, j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), SV.own_rest.go(es, own, c, d, i, j), SV.eqat(ES, i)) : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      absurd({SV.own_rest.go(Nil{}, own, c, d, 1n+i, j) == oadd(SV.band(SV.eq(SV.nth(own, i), c), SV.bnot(SV.mem(i, d))), Nil{}, SV.eqat(ES, i)) : List<&2, E.QExpr>},
        KA.ft(Equal.trans(Bool, False{}, SV.lt(i, SV.neqs(ES)), True{}, Equal.sym(Bool, SV.lt(i, SV.neqs(ES)), False{}, KB.nlt_le(j, i, SV.neqs(ES), nlt_qdrop(ES, j, hq), hji)), hi)))
    case Con{+e, +t}:
      or_step.c(SV.eq(j, i), e, t, ES, own, c, d, i, j, {==}, hq, hji, h2 => or_step(t, ES, own, c, d, i, 1n+j, OW.qdrop_step(j, ES, e, t, hq), h2, hi))

def mem_cat(+v: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {SV.mem(v, SV.cat(xs, ys)) == SV.bor(SV.mem(v, xs), SV.mem(v, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, SV.mem(v, SV.cat(t, ys)), SV.bor(SV.mem(v, t), SV.mem(v, ys)), mem_cat(v, t, ys)) : {SV.bor(SV.eq(v, h), _) == SV.bor(SV.bor(SV.eq(v, h), SV.mem(v, t)), SV.mem(v, ys)) : Bool}
      KB.bor_assoc(SV.eq(v, h), SV.mem(v, t), SV.mem(v, ys))

def ne_lt.go(b: Bool, +j: Nat, +x: Nat, +i: Nat, e: {SV.eq(j, x) == b : Bool}, hj: {SV.lt(j, i) == True{} : Bool}, hx: {SV.lt(x, i) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.lt(x, i), False{}, (%LI.eq_ok(j, x, e) : {True{} == SV.lt(_, i) : Bool}
        Equal.sym(Bool, SV.lt(j, i), True{}, hj)), hx)))
    case False{}:
      {==}

def ne_lt(+j: Nat, +x: Nat, +i: Nat, hj: {SV.lt(j, i) == True{} : Bool}, hx: {SV.lt(x, i) == False{} : Bool}) -> {SV.eq(j, x) == False{} : Bool}:
  ne_lt.go(SV.eq(j, x), j, x, i, {==}, hj, hx)

# every entry at least i, j below i: j is none of them
def ge_notmem(xs: List<&2, Nat>, +i: Nat, +j: Nat, +h: {OW.geall(xs, i) == True{} : Bool}, +hj: {SV.lt(j, i) == True{} : Bool}) -> {SV.mem(j, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.bor_f(SV.eq(j, x), SV.mem(j, t), ne_lt(j, x, i, hj, OW.ge_head(x, i, t, h)), ge_notmem(t, i, j, OW.ge_tail(x, i, t, h), hj))

def or_cat.h(+o: Nat, +c: Nat, +X: List<&2, Nat>, +d: List<&2, Nat>, +i: Nat, +j: Nat, +hg: {OW.geall(X, i) == True{} : Bool}, +hl: {SV.lt(j, i) == True{} : Bool})
  -> {SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, SV.cat(X, d)))) == SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d))) : Bool}:
  %Equal.sym(Bool, SV.mem(j, SV.cat(X, d)), SV.bor(SV.mem(j, X), SV.mem(j, d)), mem_cat(j, X, d)) : {SV.band(SV.eq(o, c), SV.bnot(_)) == SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d))) : Bool}
  %Equal.sym(Bool, SV.mem(j, X), False{}, ge_notmem(X, i, j, hg, hl)) : {SV.band(SV.eq(o, c), SV.bnot(SV.bor(_, SV.mem(j, d)))) == SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d))) : Bool}
  {==}

# drops at i or later do not change c's own equations before i
def or_cat(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +X: List<&2, Nat>, +d: List<&2, Nat>, +i: Nat, +j: Nat, +hg: {OW.geall(X, i) == True{} : Bool})
  -> {SV.own_rest.go(es, own, c, SV.cat(X, d), i, j) == SV.own_rest.go(es, own, c, d, i, j) : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, t}:
      %Equal.sym(List<&2, E.QExpr>, SV.own_rest.go(t, own, c, SV.cat(X, d), i, 1n+j), SV.own_rest.go(t, own, c, d, i, 1n+j), or_cat(t, own, c, X, d, i, 1n+j, hg)) : {SV.solved.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d))))), e, _) == SV.solved.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)) : List<&2, E.QExpr>}
      %band_ag(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d)))), hl => Equal.sym(Bool, SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d)))), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), or_cat.h(SV.nth(own, j), c, X, d, i, j, hg, hl))) : {SV.solved.pick(_, e, SV.own_rest.go(t, own, c, d, i, 1n+j)) == SV.solved.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, i, 1n+j)) : List<&2, E.QExpr>}
      {==}

# The solved equations before c
# -----------------------------

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

def beq_eq(a: Bool, b: Bool, h: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, KA.ft(h))
    case False{} False{}:
      {==}

# at the equations from j that c owns, D and d agree
def agree(own: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +j: Nat) -> Bool:
  match own:
    case Nil{}:
      True{}
    case Con{o, t}:
      SV.band(SV.bor(SV.bnot(SV.eq(o, c)), beq(SV.mem(j, D), SV.mem(j, d))), agree(t, D, d, c, 1n+j))

def len_nc(+o: Nat, +ot: List<&2, Nat>, h: {SV.len(Con{o, ot}) == SV.neqs(Nil{}) : Nat}) -> Empty:
  OW.zs(SV.len(ot), Equal.sym(Nat, 1n+SV.len(ot), 0n, h))

def len_cn(+e: E.QExpr, +t: List<&2, E.QExpr>, h: {SV.len(Nil{}) == SV.neqs(Con{e, t}) : Nat}) -> Empty:
  OW.zs(SV.neqs(t), h)

# no owner from j is before c: no solved equation before c from j
def ps_nil(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +j: Nat, +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hg: {OW.geall(own_j, c) == True{} : Bool})
  -> {SV.presolved.go(es, own, R, D, c, j) == Nil{} : List<&2, E.QExpr>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.presolved.go(Nil{}, own, R, D, c, j) == Nil{} : List<&2, E.QExpr>}, len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.presolved.go(Con{e, t}, own, R, D, c, j) == Nil{} : List<&2, E.QExpr>}, len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : {SV.solved.pick(SV.band(SV.lt(_, c), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) == Nil{} : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), False{}, OW.ge_head(o, c, ot, hg)) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) == Nil{} : List<&2, E.QExpr>}
      ps_nil(t, ot, own, R, D, c, 1n+j, OW.ndrop_step(j, own, o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), OW.ge_tail(o, c, ot, hg))

def cat_pick(b: Bool, +e: E.QExpr, +A: List<&2, E.QExpr>, +B: List<&2, E.QExpr>) -> {SV.solved.pick(b, e, SK.cat(A, B)) == SK.cat(SV.solved.pick(b, e, A), B) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# not o < c, o /= c: not o < c + 1
def nlt_succ(o: Nat, c: Nat, h1: {SV.lt(o, c) == False{} : Bool}, h2: {SV.eq(o, c) == False{} : Bool}) -> {SV.lt(o, 1n+c) == False{} : Bool}:
  match o c:
    case 0n 0n:
      absurd({SV.lt(0n, 1n) == False{} : Bool}, KA.tf(h2))
    case 0n 1n+m:
      absurd({SV.lt(0n, 2n+m) == False{} : Bool}, KA.tf(h1))
    case 1n+i 0n:
      KB.lt_z(i)
    case 1n+i 1n+m:
      nlt_succ(i, m, h1, h2)

def ps_kept.c(b1: Bool, b2: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +j: Nat, +N: Nat,
  +e1: {SV.lt(o, c) == b1 : Bool}, +e2: {SV.eq(o, c) == b2 : Bool}, +hN: {SV.lt(j, N) == True{} : Bool}, +hR: {SV.mem(c, R) == False{} : Bool},
  +hag: {SV.bor(SV.bnot(SV.eq(o, c)), beq(SV.mem(j, D), SV.mem(j, d))) == True{} : Bool},
  hnil: {SV.lt(o, c) == False{} : Bool} -> {SV.presolved.go(t, own, R, D, c, 1n+j) == Nil{} : List<&2, E.QExpr>}, +ih: {SV.presolved.go(t, own, R, D, 1n+c, 1n+j) == SK.cat(SV.presolved.go(t, own, R, D, c, 1n+j), SV.own_rest.go(t, own, c, d, N, 1n+j)) : List<&2, E.QExpr>})
  -> {SV.solved.pick(SV.band(SV.lt(o, 1n+c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}:
  match b1 b2:
    case True{} True{}:
      absurd({SV.solved.pick(SV.band(SV.lt(o, 1n+c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}, KA.tf(Equal.trans(Bool, True{}, SV.lt(o, c), False{}, Equal.sym(Bool, SV.lt(o, c), True{}, e1), KB.eq_lt(o, c, e2))))
    case True{} False{}:
      %Equal.sym(Bool, SV.lt(o, 1n+c), True{}, KB.lt_up(o, c, e1)) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), True{}, e1) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.eq(o, c), False{}, e2) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(_, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(j, N), True{}, hN) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(_, SV.band(False{}, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.presolved.go(t, own, R, D, 1n+c, 1n+j), SK.cat(SV.presolved.go(t, own, R, D, c, 1n+j), SV.own_rest.go(t, own, c, d, N, 1n+j)), ih) : {SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, _) == SK.cat(SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.own_rest.go(t, own, c, d, N, 1n+j)) : List<&2, E.QExpr>}
      cat_pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, SV.presolved.go(t, own, R, D, c, 1n+j), SV.own_rest.go(t, own, c, d, N, 1n+j))
    case False{} True{}:
      +oc = LI.eq_ok(o, c, e2)
      %Equal.sym(Bool, SV.lt(o, 1n+c), True{}, (%Equal.sym(Nat, o, c, oc) : {SV.lt(_, 1n+c) == True{} : Bool}
        KB.lt_succ(c))) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.mem(o, R), False{}, (%Equal.sym(Nat, o, c, oc) : {SV.mem(_, R) == False{} : Bool}
        hR)) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(_), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(_), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), False{}, e1) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(_, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.eq(o, c), True{}, e2) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(_, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(j, N), True{}, hN) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(False{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(_, SV.band(True{}, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.presolved.go(t, own, R, D, 1n+c, 1n+j), SK.cat(SV.presolved.go(t, own, R, D, c, 1n+j), SV.own_rest.go(t, own, c, d, N, 1n+j)), ih) : {SV.solved.pick(SV.bnot(SV.mem(j, D)), e, _) == SK.cat(SV.presolved.go(t, own, R, D, c, 1n+j), SV.solved.pick(SV.bnot(SV.mem(j, d)), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.presolved.go(t, own, R, D, c, 1n+j), Nil{}, hnil(e1)) : {SV.solved.pick(SV.bnot(SV.mem(j, D)), e, SK.cat(_, SV.own_rest.go(t, own, c, d, N, 1n+j))) == SK.cat(_, SV.solved.pick(SV.bnot(SV.mem(j, d)), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.mem(j, D), SV.mem(j, d), beq_eq(SV.mem(j, D), SV.mem(j, d), (%e2 : {SV.bor(SV.bnot(_), beq(SV.mem(j, D), SV.mem(j, d))) == True{} : Bool}
        hag))) : {SV.solved.pick(SV.bnot(_), e, SV.own_rest.go(t, own, c, d, N, 1n+j)) == SV.solved.pick(SV.bnot(SV.mem(j, d)), e, SV.own_rest.go(t, own, c, d, N, 1n+j)) : List<&2, E.QExpr>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, SV.lt(o, 1n+c), False{}, nlt_succ(o, c, e1, e2)) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), False{}, e1) : {SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(o, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.eq(o, c), False{}, e2) : {SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(_, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(j, N), True{}, hN) : {SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(_, SV.band(False{}, SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      ih

# when c is kept: the solved equations before c + 1 are those before c,
# then c's own not in d (D agreeing with d on c's equations)
def ps_kept(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +ES: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +j: Nat,
  +hq: {OW.qdrop(j, ES) == es : List<&2, E.QExpr>}, +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hs: {OW.sorted(own) == True{} : Bool},
  +hR: {SV.mem(c, R) == False{} : Bool}, +hag: {agree(own_j, D, d, c, j) == True{} : Bool})
  -> {SV.presolved.go(es, own, R, D, 1n+c, j) == SK.cat(SV.presolved.go(es, own, R, D, c, j), SV.own_rest.go(es, own, c, d, SV.neqs(ES), j)) : List<&2, E.QExpr>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.presolved.go(Nil{}, own, R, D, 1n+c, j) == SK.cat(SV.presolved.go(Nil{}, own, R, D, c, j), SV.own_rest.go(Nil{}, own, c, d, SV.neqs(ES), j)) : List<&2, E.QExpr>}, len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.presolved.go(Con{e, t}, own, R, D, 1n+c, j) == SK.cat(SV.presolved.go(Con{e, t}, own, R, D, c, j), SV.own_rest.go(Con{e, t}, own, c, d, SV.neqs(ES), j)) : List<&2, E.QExpr>}, len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      +N = SV.neqs(ES)
      +hl2 = LN.succ_inj(SV.len(ot), SV.neqs(t), hl)
      +ho2 = OW.ndrop_step(j, own, o, ot, ho)
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : {SV.solved.pick(SV.band(SV.lt(_, 1n+c), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SK.cat(SV.solved.pick(SV.band(SV.lt(_, c), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)), SV.solved.pick(SV.band(SV.lt(j, N), SV.band(SV.eq(_, c), SV.bnot(SV.mem(j, d)))), e, SV.own_rest.go(t, own, c, d, N, 1n+j))) : List<&2, E.QExpr>}
      ps_kept.c(SV.lt(o, c), SV.eq(o, c), e, t, o, own, R, D, d, c, j, N, {==}, {==}, lt_qdrop(ES, j, e, t, hq), hR,
        LI.band_l(SV.bor(SV.bnot(SV.eq(o, c)), beq(SV.mem(j, D), SV.mem(j, d))), agree(ot, D, d, c, 1n+j), hag),
        hn => ps_nil(t, ot, own, R, D, c, 1n+j, ho2, hl2, OW.up_of(own, j, o, ot, c, hs, ho, hn)),
        ps_kept(t, ot, ES, own, R, D, d, c, 1n+j, OW.qdrop_step(j, ES, e, t, hq), ho2, hl2, hs, hR, LI.band_r(SV.bor(SV.bnot(SV.eq(o, c)), beq(SV.mem(j, D), SV.mem(j, d))), agree(ot, D, d, c, 1n+j), hag)))

# every equation from j that c owns has c in R (c red, or owning none)
def zc(own: List<&2, Nat>, +c: Nat, +R: List<&2, Nat>) -> Bool:
  match own:
    case Nil{}:
      True{}
    case Con{o, t}:
      SV.band(SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(c, R)), zc(t, c, R))

def zc_red(xs: List<&2, Nat>, +c: Nat, +R: List<&2, Nat>, +h: {SV.mem(c, R) == True{} : Bool}) -> {zc(xs, c, R) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.band_i(SV.bor(SV.bnot(SV.eq(x, c)), SV.mem(c, R)), zc(t, c, R), LI.bor_r(SV.bnot(SV.eq(x, c)), SV.mem(c, R), h), zc_red(t, c, R, h))

def zc_noc(xs: List<&2, Nat>, +c: Nat, +R: List<&2, Nat>, +h: {OW.noc(xs, c) == True{} : Bool}) -> {zc(xs, c, R) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.band_i(SV.bor(SV.bnot(SV.eq(x, c)), SV.mem(c, R)), zc(t, c, R), LI.bor_l(SV.bnot(SV.eq(x, c)), SV.mem(c, R), LI.band_l(SV.bnot(SV.eq(x, c)), OW.noc(t, c), h)), zc_noc(t, c, R, LI.band_r(SV.bnot(SV.eq(x, c)), OW.noc(t, c), h)))

def ps_same.c(b1: Bool, b2: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +j: Nat,
  +e1: {SV.lt(o, c) == b1 : Bool}, +e2: {SV.eq(o, c) == b2 : Bool}, +hz: {SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(c, R)) == True{} : Bool}, +ih: {SV.presolved.go(t, own, R, D, 1n+c, 1n+j) == SV.presolved.go(t, own, R, D, c, 1n+j) : List<&2, E.QExpr>})
  -> {SV.solved.pick(SV.band(SV.lt(o, 1n+c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}:
  match b1 b2:
    case True{} True{}:
      absurd({SV.solved.pick(SV.band(SV.lt(o, 1n+c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}, KA.tf(Equal.trans(Bool, True{}, SV.lt(o, c), False{}, Equal.sym(Bool, SV.lt(o, c), True{}, e1), KB.eq_lt(o, c, e2))))
    case True{} False{}:
      %Equal.sym(Bool, SV.lt(o, 1n+c), True{}, KB.lt_up(o, c, e1)) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), True{}, e1) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.presolved.go(t, own, R, D, 1n+c, 1n+j), SV.presolved.go(t, own, R, D, c, 1n+j), ih) : {SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, _) == SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      {==}
    case False{} True{}:
      +oc = LI.eq_ok(o, c, e2)
      %Equal.sym(Bool, SV.lt(o, 1n+c), True{}, (%Equal.sym(Nat, o, c, oc) : {SV.lt(_, 1n+c) == True{} : Bool}
        KB.lt_succ(c))) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.mem(o, R), True{}, (%Equal.sym(Nat, o, c, oc) : {SV.mem(_, R) == True{} : Bool}
        (%e2 : {SV.bor(SV.bnot(_), SV.mem(c, R)) == True{} : Bool}
          hz))) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(_), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), False{}, e1) : {SV.solved.pick(SV.band(True{}, SV.band(SV.bnot(True{}), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      ih
    case False{} False{}:
      %Equal.sym(Bool, SV.lt(o, 1n+c), False{}, nlt_succ(o, c, e1, e2)) : {SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(o, c), SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, c), False{}, e1) : {SV.solved.pick(SV.band(False{}, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      ih

# when c is red or owns nothing: the solved equations before c + 1 are those before c
def ps_same(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +j: Nat,
  +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hz: {zc(own_j, c, R) == True{} : Bool})
  -> {SV.presolved.go(es, own, R, D, 1n+c, j) == SV.presolved.go(es, own, R, D, c, j) : List<&2, E.QExpr>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.presolved.go(Nil{}, own, R, D, 1n+c, j) == SV.presolved.go(Nil{}, own, R, D, c, j) : List<&2, E.QExpr>}, len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.presolved.go(Con{e, t}, own, R, D, 1n+c, j) == SV.presolved.go(Con{e, t}, own, R, D, c, j) : List<&2, E.QExpr>}, len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : {SV.solved.pick(SV.band(SV.lt(_, 1n+c), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, 1n+c, 1n+j)) == SV.solved.pick(SV.band(SV.lt(_, c), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, c, 1n+j)) : List<&2, E.QExpr>}
      ps_same.c(SV.lt(o, c), SV.eq(o, c), e, t, o, own, R, D, c, j, {==}, {==},
        LI.band_l(SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(c, R)), zc(ot, c, R), hz),
        ps_same(t, ot, own, R, D, c, 1n+j, OW.ndrop_step(j, own, o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), LI.band_r(SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(c, R)), zc(ot, c, R), hz)))

def geall_zero(xs: List<&2, Nat>) -> {OW.geall(xs, 0n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      OW.ge_con(x, 0n, t, KB.lt_z(x), geall_zero(t))

# with every owner below n: the solved equations are those before n
def solved_ps(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +n: Nat, +j: Nat,
  +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hb: {SV.below(own_j, n) == True{} : Bool})
  -> {SV.solved.go(es, own, R, D, j) == SV.presolved.go(es, own, R, D, n, j) : List<&2, E.QExpr>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.solved.go(Nil{}, own, R, D, j) == SV.presolved.go(Nil{}, own, R, D, n, j) : List<&2, E.QExpr>}, len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.solved.go(Con{e, t}, own, R, D, j) == SV.presolved.go(Con{e, t}, own, R, D, n, j) : List<&2, E.QExpr>}, len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : {SV.solved.pick(SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D))), e, SV.solved.go(t, own, R, D, 1n+j)) == SV.solved.pick(SV.band(SV.lt(_, n), SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, n, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(Bool, SV.lt(o, n), True{}, LI.band_l(SV.lt(o, n), SV.below(ot, n), hb)) : {SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, SV.solved.go(t, own, R, D, 1n+j)) == SV.solved.pick(SV.band(_, SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D)))), e, SV.presolved.go(t, own, R, D, n, 1n+j)) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.solved.go(t, own, R, D, 1n+j), SV.presolved.go(t, own, R, D, n, 1n+j), solved_ps(t, ot, own, R, D, n, 1n+j, OW.ndrop_step(j, own, o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), LI.band_r(SV.lt(o, n), SV.below(ot, n), hb))) : {SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, _) == SV.solved.pick(SV.band(SV.bnot(SV.mem(o, R)), SV.bnot(SV.mem(j, D))), e, SV.presolved.go(t, own, R, D, n, 1n+j)) : List<&2, E.QExpr>}
      {==}

# The sketch's
# ------------

def presolved_kept(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +hR: {SV.mem(c, R) == False{} : Bool}, +hag: {agree(SV.owners(sk), D, d, c, 0n) == True{} : Bool})
  -> {SV.presolved(sk, R, D, 1n+c) == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, d, SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>}:
  ps_kept(SK.Sketch.eqs(sk), SV.owners(sk), SK.Sketch.eqs(sk), SV.owners(sk), R, D, d, c, 0n, {==}, {==}, OW.len_owners(sk), OW.sorted_owners(sk), hR, hag)

def presolved_same(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +hz: {zc(SV.owners(sk), c, R) == True{} : Bool}) -> {SV.presolved(sk, R, D, 1n+c) == SV.presolved(sk, R, D, c) : List<&2, E.QExpr>}:
  ps_same(SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), R, D, c, 0n, {==}, OW.len_owners(sk), hz)

def presolved_zero(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>) -> {SV.presolved(sk, R, D, 0n) == Nil{} : List<&2, E.QExpr>}:
  ps_nil(SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), R, D, 0n, 0n, {==}, OW.len_owners(sk), geall_zero(SV.owners(sk)))

def solved_end(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>) -> {SV.solved(sk, R, D) == SV.presolved(sk, R, D, SV.ncons(sk)) : List<&2, E.QExpr>}:
  solved_ps(SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), R, D, SV.ncons(sk), 0n, {==}, OW.len_owners(sk), OW.below_ncons(sk))

