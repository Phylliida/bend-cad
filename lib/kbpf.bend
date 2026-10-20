# bend-cad: the kept constraints before a constraint, for the single pass
# (PLAN-sk13a S4). Proofs only.
# - kept_before(sk, R, c) grows by c exactly when c is driving and not in
#   R (kb_step), from nothing (kb_zero): so the pass's own list of kept
#   constraints is the spec's, for the final red list.
# - A list built so (each new entry driving, not red, and above the ones
#   before) is the deletion filter's candidates: distinct, below c,
#   driving, not red (kbp_snoc).

import Base
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./listpf.bend as LI
import ./conflict.bend as CO

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Order of numbers
# ----------------

def lt_zero(b: Nat, h: {SV.lt(b, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match b:
    case 0n:
      h
    case 1n+j:
      h

def lt_irr(a: Nat) -> {SV.lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      lt_irr(b)

def lt_succ(a: Nat) -> {SV.lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      lt_succ(b)

def lt_up(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.lt(1n+i, 1n) == True{} : Bool}, KA.ft(h))
    case 1n+i 1n+j:
      lt_up(i, j, h)

# a < b + 1 and a /= b: a < b
def lt_down(a: Nat, b: Nat, h: {SV.lt(a, 1n+b) == True{} : Bool}, hn: {SV.eq(a, b) == False{} : Bool}) -> {SV.lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, KA.tf(hn))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.lt(1n+i, 0n) == True{} : Bool}, KA.ft(lt_zero(i, h)))
    case 1n+i 1n+j:
      lt_down(i, j, h, hn)

# a < b: not b <= a
def lt_nle(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.lt(0n, 1n+i) == False{} : Bool}, KA.ft(h))
    case 1n+i 1n+j:
      lt_nle(i, j, h)

# not a < b + 1: not a < b
def nlt_down(a: Nat, b: Nat, h: {SV.lt(a, 1n+b) == False{} : Bool}) -> {SV.lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      absurd({SV.lt(0n, 1n+j) == False{} : Bool}, KA.tf(h))
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      nlt_down(i, j, h)

# not a < b: not a + 1 < b
def nlt_up(a: Nat, b: Nat, h: {SV.lt(a, b) == False{} : Bool}) -> {SV.lt(1n+a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      absurd({SV.lt(1n, 1n+j) == False{} : Bool}, KA.tf(h))
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      nlt_up(i, j, h)

def eq_lt(+a: Nat, +b: Nat, h: {SV.eq(a, b) == True{} : Bool}) -> {SV.lt(a, b) == False{} : Bool}:
  %LI.eq_ok(a, b, h) : {SV.lt(a, _) == False{} : Bool}
  lt_irr(a)

# The constraints from position i
# -------------------------------

def rdrop(k: Nat, rs: List<&2, SK.Rec>) -> List<&2, SK.Rec>:
  match k rs:
    case 0n rs:
      rs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{r, t}:
      rdrop(j, t)

def rtl(rs: List<&2, SK.Rec>) -> List<&2, SK.Rec>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      t

def rdrop_tl(k: Nat, rs: List<&2, SK.Rec>) -> {rdrop(1n+k, rs) == rtl(rdrop(k, rs)) : List<&2, SK.Rec>}:
  match k rs:
    case 0n Nil{}:
      {==}
    case 0n Con{r, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{r, t}:
      rdrop_tl(j, t)

def rdrop_step(+i: Nat, +cs: List<&2, SK.Rec>, +r: SK.Rec, +t: List<&2, SK.Rec>, hd: {rdrop(i, cs) == Con{r, t} : List<&2, SK.Rec>}) -> {rdrop(1n+i, cs) == t : List<&2, SK.Rec>}:
  Equal.trans(List<&2, SK.Rec>, rdrop(1n+i, cs), rtl(rdrop(i, cs)), t, rdrop_tl(i, cs), Equal.cong(List<&2, SK.Rec>, List<&2, SK.Rec>, x => rtl(x), rdrop(i, cs), Con{r, t}, hd))

def isnilr(rs: List<&2, SK.Rec>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      False{}

def nil_con(+r: SK.Rec, +t: List<&2, SK.Rec>, h: {Nil{} == Con{r, t} : List<&2, SK.Rec>}) -> Empty:
  KA.tf(Equal.cong(List<&2, SK.Rec>, Bool, x => isnilr(x), Nil{}, Con{r, t}, h))

def driven_drop(cs: List<&2, SK.Rec>, i: Nat) -> {SV.driven.at(cs, i) == SV.driven.at(rdrop(i, cs), 0n) : Bool}:
  match cs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{r, t} 0n:
      {==}
    case Con{r, t} 1n+j:
      driven_drop(t, j)

# a constraint at position i: i is below their number
def lt_drop(cs: List<&2, SK.Rec>, i: Nat, +r: SK.Rec, +t: List<&2, SK.Rec>, hd: {rdrop(i, cs) == Con{r, t} : List<&2, SK.Rec>}) -> {SV.lt(i, SV.clen(cs)) == True{} : Bool}:
  match cs i:
    case Nil{} 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, nil_con(r, t, hd))
    case Nil{} 1n+j:
      absurd({SV.lt(1n+j, 0n) == True{} : Bool}, nil_con(r, t, hd))
    case Con{x, xt} 0n:
      {==}
    case Con{x, xt} 1n+j:
      lt_drop(xt, j, r, t, hd)

# none at position i: i is not below their number
def nlt_drop(cs: List<&2, SK.Rec>, i: Nat, hd: {rdrop(i, cs) == Nil{} : List<&2, SK.Rec>}) -> {SV.lt(i, SV.clen(cs)) == False{} : Bool}:
  match cs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, xt} 0n:
      absurd({SV.lt(0n, 1n+SV.clen(xt)) == False{} : Bool}, nil_con(x, xt, Equal.sym(List<&2, SK.Rec>, Con{x, xt}, Nil{}, hd)))
    case Con{x, xt} 1n+j:
      nlt_drop(xt, j, hd)

# not c < i and c < n: i < n
def lt_trans_nl(a: Nat, b: Nat, n: Nat, hi: {SV.lt(b, a) == False{} : Bool}, h: {SV.lt(b, n) == True{} : Bool}) -> {SV.lt(a, n) == True{} : Bool}:
  match a b n:
    case 0n b 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, KA.ft(lt_zero(b, h)))
    case 0n b 1n+m:
      {==}
    case 1n+i 0n n:
      absurd({SV.lt(1n+i, n) == True{} : Bool}, KA.tf(hi))
    case 1n+i 1n+j 0n:
      absurd({SV.lt(1n+i, 0n) == True{} : Bool}, KA.ft(h))
    case 1n+i 1n+j 1n+m:
      lt_trans_nl(i, j, m, hi, h)

def nlt_le.go(b: Bool, +i: Nat, +c: Nat, +n: Nat, e: {SV.lt(c, n) == b : Bool}, h: {SV.lt(i, n) == False{} : Bool}, hi: {SV.lt(c, i) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.lt(i, n), False{}, Equal.sym(Bool, SV.lt(i, n), True{}, lt_trans_nl(i, c, n, hi, e)), h)))
    case False{}:
      {==}

# none at position i, i <= c: none at c
def nlt_le(+i: Nat, +c: Nat, +n: Nat, h: {SV.lt(i, n) == False{} : Bool}, hi: {SV.lt(c, i) == False{} : Bool}) -> {SV.lt(c, n) == False{} : Bool}:
  nlt_le.go(SV.lt(c, n), i, c, n, {==}, h, hi)


def lt_z(a: Nat) -> {SV.lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      {==}

# a < b: not b < a + 1
def lt_nle_s(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.lt(b, 1n+a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.lt(0n, 1n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+j:
      lt_z(j)
    case 1n+i 0n:
      absurd({SV.lt(0n, 2n+i) == False{} : Bool}, KA.ft(h))
    case 1n+i 1n+j:
      lt_nle_s(i, j, h)

# not c < i and i /= c: i < c
def lt_of_nlt(a: Nat, b: Nat, h: {SV.lt(b, a) == False{} : Bool}, hn: {SV.eq(a, b) == False{} : Bool}) -> {SV.lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.lt(0n, 0n) == True{} : Bool}, KA.tf(hn))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.lt(1n+i, 0n) == True{} : Bool}, KA.tf(h))
    case 1n+i 1n+j:
      lt_of_nlt(i, j, h, hn)

# Growing the kept constraints
# ----------------------------

# kb, with c after it if b
def kpk(b: Bool, +kb: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match b:
    case True{}:
      CO.lsnoc(kb, c)
    case False{}:
      kb

# c is driving and not in R
def dcond(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat) -> Bool:
  SV.band(SV.driving(sk, c), SV.bnot(SV.mem(c, R)))

# none from position i on is before c
def kg_nil(rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +i: Nat, +h: {SV.lt(i, c) == False{} : Bool}) -> {SV.kept.go(rs, R, c, i) == Nil{} : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, t}:
      kg_nil(t, R, c, 1n+i, nlt_up(i, c, h))
    case Con{SK.Rec{id, False{}, k}, t}:
      %Equal.sym(Bool, SV.lt(i, c), False{}, h) : {SV.kept.pick(SV.band(_, SV.bnot(SV.mem(i, R))), i, SV.kept.go(t, R, c, 1n+i)) == Nil{} : List<&2, Nat>}
      kg_nil(t, R, c, 1n+i, nlt_up(i, c, h))

def pk_nil(b: Bool, +c: Nat) -> {SV.kept.pick(b, c, Nil{}) == kpk(b, Nil{}, c) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pk_kpk(x: Bool, q: Bool, +i: Nat, +X: List<&2, Nat>, +c: Nat) -> {SV.kept.pick(x, i, kpk(q, X, c)) == kpk(q, SV.kept.pick(x, i, X), c) : List<&2, Nat>}:
  match x q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# at position c itself
def kb_step.at(rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +hd: {rdrop(c, cs) == rs : List<&2, SK.Rec>})
  -> {SV.kept.go(rs, R, 1n+c, c) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(rs, R, c, c), c) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      %Equal.sym(Bool, SV.lt(c, SV.clen(cs)), False{}, nlt_drop(cs, c, hd)) : {Nil{} == kpk(SV.band(SV.band(_, SV.bnot(SV.driven.at(cs, c))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      {==}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      %Equal.sym(List<&2, Nat>, SV.kept.go(t, R, 1n+c, 1n+c), Nil{}, kg_nil(t, R, 1n+c, 1n+c, lt_irr(1n+c))) : {_ == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(t, R, c, 1n+c), c) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.kept.go(t, R, c, 1n+c), Nil{}, kg_nil(t, R, c, 1n+c, nlt_up(c, c, lt_irr(c)))) : {Nil{} == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), _, c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.lt(c, SV.clen(cs)), True{}, lt_drop(cs, c, SK.Rec{id, True{}, k}, t, hd)) : {Nil{} == kpk(SV.band(SV.band(_, SV.bnot(SV.driven.at(cs, c))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.driven.at(cs, c), SV.driven.at(rdrop(c, cs), 0n), driven_drop(cs, c)) : {Nil{} == kpk(SV.band(SV.band(True{}, SV.bnot(_)), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      %Equal.sym(List<&2, SK.Rec>, rdrop(c, cs), Con{SK.Rec{id, True{}, k}, t}, hd) : {Nil{} == kpk(SV.band(SV.band(True{}, SV.bnot(SV.driven.at(_, 0n))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      {==}
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      %Equal.sym(Bool, SV.lt(c, 1n+c), True{}, lt_succ(c)) : {SV.kept.pick(SV.band(_, SV.bnot(SV.mem(c, R))), c, SV.kept.go(t, R, 1n+c, 1n+c)) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(Con{SK.Rec{id, False{}, k}, t}, R, c, c), c) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.kept.go(t, R, 1n+c, 1n+c), Nil{}, kg_nil(t, R, 1n+c, 1n+c, lt_irr(1n+c))) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, _) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(Con{SK.Rec{id, False{}, k}, t}, R, c, c), c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.lt(c, c), False{}, lt_irr(c)) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, Nil{}) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.pick(SV.band(_, SV.bnot(SV.mem(c, R))), c, SV.kept.go(t, R, c, 1n+c)), c) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.kept.go(t, R, c, 1n+c), Nil{}, kg_nil(t, R, c, 1n+c, nlt_up(c, c, lt_irr(c)))) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, Nil{}) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), _, c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.lt(c, SV.clen(cs)), True{}, lt_drop(cs, c, SK.Rec{id, False{}, k}, t, hd)) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, Nil{}) == kpk(SV.band(SV.band(_, SV.bnot(SV.driven.at(cs, c))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.driven.at(cs, c), SV.driven.at(rdrop(c, cs), 0n), driven_drop(cs, c)) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, Nil{}) == kpk(SV.band(SV.band(True{}, SV.bnot(_)), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      %Equal.sym(List<&2, SK.Rec>, rdrop(c, cs), Con{SK.Rec{id, False{}, k}, t}, hd) : {SV.kept.pick(SV.bnot(SV.mem(c, R)), c, Nil{}) == kpk(SV.band(SV.band(True{}, SV.bnot(SV.driven.at(_, 0n))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      pk_nil(SV.bnot(SV.mem(c, R)), c)

def kb_step.eq(+rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +i: Nat, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +hd: {rdrop(i, cs) == rs : List<&2, SK.Rec>}, +e: {i == c : Nat})
  -> {SV.kept.go(rs, R, 1n+c, i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(rs, R, c, i), c) : List<&2, Nat>}:
  %Equal.sym(Nat, i, c, e) : {SV.kept.go(rs, R, 1n+c, _) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(rs, R, c, _), c) : List<&2, Nat>}
  kb_step.at(rs, R, c, vs, es, cs, (%e : {rdrop(_, cs) == rs : List<&2, SK.Rec>}
    hd))

def kb_step.lt(dr: Bool, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +i: Nat, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +hlt: {SV.lt(i, c) == True{} : Bool},
  ih: {SV.kept.go(t, R, 1n+c, 1n+i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(t, R, c, 1n+i), c) : List<&2, Nat>})
  -> {SV.kept.go(Con{SK.Rec{id, dr, k}, t}, R, 1n+c, i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(Con{SK.Rec{id, dr, k}, t}, R, c, i), c) : List<&2, Nat>}:
  match dr:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, SV.lt(i, 1n+c), True{}, lt_up(i, c, hlt)) : {SV.kept.pick(SV.band(_, SV.bnot(SV.mem(i, R))), i, SV.kept.go(t, R, 1n+c, 1n+i)) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.pick(SV.band(SV.lt(i, c), SV.bnot(SV.mem(i, R))), i, SV.kept.go(t, R, c, 1n+i)), c) : List<&2, Nat>}
      %Equal.sym(Bool, SV.lt(i, c), True{}, hlt) : {SV.kept.pick(SV.bnot(SV.mem(i, R)), i, SV.kept.go(t, R, 1n+c, 1n+i)) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.pick(SV.band(_, SV.bnot(SV.mem(i, R))), i, SV.kept.go(t, R, c, 1n+i)), c) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.kept.go(t, R, 1n+c, 1n+i), kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(t, R, c, 1n+i), c), ih) : {SV.kept.pick(SV.bnot(SV.mem(i, R)), i, _) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.pick(SV.bnot(SV.mem(i, R)), i, SV.kept.go(t, R, c, 1n+i)), c) : List<&2, Nat>}
      pk_kpk(SV.bnot(SV.mem(i, R)), dcond(SK.Sketch{vs, es, cs}, R, c), i, SV.kept.go(t, R, c, 1n+i), c)

def kb_step.con(b: Bool, +id: Nat, +dr: Bool, +k: SK.Constraint, +t: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +i: Nat, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +e: {SV.eq(i, c) == b : Bool},
  +hd: {rdrop(i, cs) == Con{SK.Rec{id, dr, k}, t} : List<&2, SK.Rec>}, +hi: {SV.lt(c, i) == False{} : Bool},
  ih: {SV.lt(c, 1n+i) == False{} : Bool} -> {SV.kept.go(t, R, 1n+c, 1n+i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(t, R, c, 1n+i), c) : List<&2, Nat>})
  -> {SV.kept.go(Con{SK.Rec{id, dr, k}, t}, R, 1n+c, i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(Con{SK.Rec{id, dr, k}, t}, R, c, i), c) : List<&2, Nat>}:
  match b:
    case True{}:
      kb_step.eq(Con{SK.Rec{id, dr, k}, t}, R, c, i, vs, es, cs, hd, LI.eq_ok(i, c, e))
    case False{}:
      +hlt = lt_of_nlt(i, c, hi, e)
      kb_step.lt(dr, id, k, t, R, c, i, vs, es, cs, hlt, ih(lt_nle_s(i, c, hlt)))

# from position i <= c, the positions up to c: those up to c - 1, and c
# if it is driving and not in R
def kb_step(rs: List<&2, SK.Rec>, +R: List<&2, Nat>, +c: Nat, +i: Nat, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +hd: {rdrop(i, cs) == rs : List<&2, SK.Rec>}, +hi: {SV.lt(c, i) == False{} : Bool})
  -> {SV.kept.go(rs, R, 1n+c, i) == kpk(dcond(SK.Sketch{vs, es, cs}, R, c), SV.kept.go(rs, R, c, i), c) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      %Equal.sym(Bool, SV.lt(c, SV.clen(cs)), False{}, nlt_le(i, c, SV.clen(cs), nlt_drop(cs, i, hd), hi)) : {Nil{} == kpk(SV.band(SV.band(_, SV.bnot(SV.driven.at(cs, c))), SV.bnot(SV.mem(c, R))), Nil{}, c) : List<&2, Nat>}
      {==}
    case Con{SK.Rec{+id, +dr, +k}, +t}:
      kb_step.con(SV.eq(i, c), id, dr, k, t, R, c, i, vs, es, cs, {==}, hd, hi, h2 => kb_step(t, R, c, 1n+i, vs, es, cs, rdrop_step(i, cs, SK.Rec{id, dr, k}, t, hd), h2))

# the kept constraints before c + 1: those before c, and c if it is
# driving and not in R
def kb_next(sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat) -> {SV.kept_before(sk, R, 1n+c) == kpk(dcond(sk, R, c), SV.kept_before(sk, R, c), c) : List<&2, Nat>}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kb_step(cs, R, c, 0n, vs, es, cs, {==}, lt_z(c))

def kb_zero(sk: SK.Sketch, +R: List<&2, Nat>) -> {SV.kept_before(sk, R, 0n) == Nil{} : List<&2, Nat>}:
  match sk:
    case SK.Sketch{vs, es, cs}:
      kg_nil(cs, R, 0n, 0n, {==})

# Lists built by adding at the end
# --------------------------------

def bor_f(a: Bool) -> {SV.bor(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bor_assoc(a: Bool, +b: Bool, +c: Bool) -> {SV.bor(a, SV.bor(b, c)) == SV.bor(SV.bor(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_snoc(+v: Nat, xs: List<&2, Nat>, +x: Nat) -> {SV.mem(v, CO.lsnoc(xs, x)) == SV.bor(SV.mem(v, xs), SV.eq(v, x)) : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, SV.bor(SV.eq(v, x), False{}), SV.eq(v, x), bor_f(SV.eq(v, x))) : {_ == SV.eq(v, x) : Bool}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, SV.mem(v, CO.lsnoc(t, x)), SV.bor(SV.mem(v, t), SV.eq(v, x)), mem_snoc(v, t, x)) : {SV.bor(SV.eq(v, h), _) == SV.bor(SV.bor(SV.eq(v, h), SV.mem(v, t)), SV.eq(v, x)) : Bool}
      bor_assoc(SV.eq(v, h), SV.mem(v, t), SV.eq(v, x))

def bnot_t(b: Bool, h: {SV.bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

def bnot_f(+b: Bool, h: {b == False{} : Bool}) -> {SV.bnot(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {SV.bnot(_) == True{} : Bool}
  {==}

# x < c: c is not x
def ne_of_lt(x: Nat, c: Nat, h: {SV.lt(x, c) == True{} : Bool}) -> {SV.eq(c, x) == False{} : Bool}:
  match x c:
    case 0n 0n:
      absurd({SV.eq(0n, 0n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      ne_of_lt(i, j, h)

def below_up(xs: List<&2, Nat>, +c: Nat, +h: {SV.below(xs, c) == True{} : Bool}) -> {SV.below(xs, 1n+c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.band_i(SV.lt(x, 1n+c), SV.below(t, 1n+c), lt_up(x, c, LI.band_l(SV.lt(x, c), SV.below(t, c), h)), below_up(t, c, LI.band_r(SV.lt(x, c), SV.below(t, c), h)))

def below_notmem(xs: List<&2, Nat>, +c: Nat, +h: {SV.below(xs, c) == True{} : Bool}) -> {SV.mem(c, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.bor_f(SV.eq(c, x), SV.mem(c, t), ne_of_lt(x, c, LI.band_l(SV.lt(x, c), SV.below(t, c), h)), below_notmem(t, c, LI.band_r(SV.lt(x, c), SV.below(t, c), h)))

def below_snoc(xs: List<&2, Nat>, +x: Nat, +n: Nat, +hb: {SV.below(xs, n) == True{} : Bool}, +hx: {SV.lt(x, n) == True{} : Bool}) -> {SV.below(CO.lsnoc(xs, x), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      LI.band_i(SV.lt(x, n), True{}, hx, {==})
    case Con{+h, +t}:
      LI.band_i(SV.lt(h, n), SV.below(CO.lsnoc(t, x), n), LI.band_l(SV.lt(h, n), SV.below(t, n), hb), below_snoc(t, x, n, LI.band_r(SV.lt(h, n), SV.below(t, n), hb), hx))

def alld_snoc(+sk: SK.Sketch, xs: List<&2, Nat>, +x: Nat, +hb: {SV.all_driving(sk, xs) == True{} : Bool}, +hx: {SV.driving(sk, x) == True{} : Bool}) -> {SV.all_driving(sk, CO.lsnoc(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      LI.band_i(SV.driving(sk, x), True{}, hx, {==})
    case Con{+h, +t}:
      LI.band_i(SV.driving(sk, h), SV.all_driving(sk, CO.lsnoc(t, x)), LI.band_l(SV.driving(sk, h), SV.all_driving(sk, t), hb), alld_snoc(sk, t, x, LI.band_r(SV.driving(sk, h), SV.all_driving(sk, t), hb), hx))

def nonein_snoc(xs: List<&2, Nat>, +x: Nat, +R: List<&2, Nat>, +hb: {SV.none_in(xs, R) == True{} : Bool}, +hx: {SV.mem(x, R) == False{} : Bool}) -> {SV.none_in(CO.lsnoc(xs, x), R) == True{} : Bool}:
  match xs:
    case Nil{}:
      LI.band_i(SV.bnot(SV.mem(x, R)), True{}, bnot_f(SV.mem(x, R), hx), {==})
    case Con{+h, +t}:
      LI.band_i(SV.bnot(SV.mem(h, R)), SV.none_in(CO.lsnoc(t, x), R), LI.band_l(SV.bnot(SV.mem(h, R)), SV.none_in(t, R), hb), nonein_snoc(t, x, R, LI.band_r(SV.bnot(SV.mem(h, R)), SV.none_in(t, R), hb), hx))

def dist_snoc(xs: List<&2, Nat>, +x: Nat, +hd: {SV.distinct(xs) == True{} : Bool}, +hn: {SV.mem(x, xs) == False{} : Bool}) -> {SV.distinct(CO.lsnoc(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hm = bnot_t(SV.mem(h, t), LI.band_l(SV.bnot(SV.mem(h, t)), SV.distinct(t), hd))
      +he = Equal.trans(Bool, SV.eq(h, x), SV.eq(x, h), False{}, LI.eq_sym(h, x), LI.bor_fl(SV.eq(x, h), SV.mem(x, t), hn))
      LI.band_i(SV.bnot(SV.mem(h, CO.lsnoc(t, x))), SV.distinct(CO.lsnoc(t, x)),
        bnot_f(SV.mem(h, CO.lsnoc(t, x)), Equal.trans(Bool, SV.mem(h, CO.lsnoc(t, x)), SV.bor(SV.mem(h, t), SV.eq(h, x)), False{}, mem_snoc(h, t, x), LI.bor_f(SV.mem(h, t), SV.eq(h, x), hm, he))),
        dist_snoc(t, x, LI.band_r(SV.bnot(SV.mem(h, t)), SV.distinct(t), hd), LI.bor_fr(SV.eq(x, h), SV.mem(x, t), hn)))

# The deletion filter's candidates
# --------------------------------

# kb is distinct, below c, driving, and not in R
def KBP(+sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat) -> Data:
  SK.Both({SV.distinct(kb) == True{} : Bool}, SK.Both({SV.below(kb, c) == True{} : Bool}, SK.Both({SV.all_driving(sk, kb) == True{} : Bool}, {SV.none_in(kb, R) == True{} : Bool})))

def kbp_zero(+sk: SK.Sketch, +R: List<&2, Nat>) -> KBP(sk, R, Nil{}, 0n):
  ({==}, ({==}, ({==}, {==})))

def kbp_bool(+sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, h: KBP(sk, R, kb, c)) -> {SV.band(SV.distinct(kb), SV.band(SV.below(kb, c), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, R)))) == True{} : Bool}:
  (h1, q1) = h
  (h2, q2) = q1
  (h3, h4) = q2
  LI.band_i(SV.distinct(kb), SV.band(SV.below(kb, c), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, R))), h1,
    LI.band_i(SV.below(kb, c), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, R)), h2, LI.band_i(SV.all_driving(sk, kb), SV.none_in(kb, R), h3, h4)))

def kbp_next.go(b: Bool, +sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, +e: {dcond(sk, R, c) == b : Bool}, h: KBP(sk, R, kb, c)) -> KBP(sk, R, kpk(b, kb, c), 1n+c):
  match b:
    case True{}:
      (h1, q1) = h
      (+h2, q2) = q1
      (h3, h4) = q2
      ( dist_snoc(kb, c, h1, below_notmem(kb, c, h2)),
      ( below_snoc(kb, c, 1n+c, below_up(kb, c, h2), lt_succ(c)),
      ( alld_snoc(sk, kb, c, h3, LI.band_l(SV.driving(sk, c), SV.bnot(SV.mem(c, R)), e)),
        nonein_snoc(kb, c, R, h4, bnot_t(SV.mem(c, R), LI.band_r(SV.driving(sk, c), SV.bnot(SV.mem(c, R)), e))))))
    case False{}:
      (h1, q1) = h
      (h2, q2) = q1
      (h1, (below_up(kb, c, h2), q2))

# the candidates grow as the kept constraints do
def kbp_next(+sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, h: KBP(sk, R, kb, c)) -> KBP(sk, R, kpk(dcond(sk, R, c), kb, c), 1n+c):
  kbp_next.go(dcond(sk, R, c), sk, R, kb, c, {==}, h)

# Owners
# ------

# every entry of xs is owned by c
def allo(+own: List<&2, Nat>, xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      SV.band(SV.eq(SV.nth(own, x), c), allo(own, t, c))

def allo_snoc(+own: List<&2, Nat>, xs: List<&2, Nat>, +x: Nat, +c: Nat, +h: {allo(own, xs, c) == True{} : Bool}, +hx: {SV.eq(SV.nth(own, x), c) == True{} : Bool}) -> {allo(own, CO.lsnoc(xs, x), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      LI.band_i(SV.eq(SV.nth(own, x), c), True{}, hx, {==})
    case Con{+y, +t}:
      LI.band_i(SV.eq(SV.nth(own, y), c), allo(own, CO.lsnoc(t, x), c), LI.band_l(SV.eq(SV.nth(own, y), c), allo(own, t, c), h), allo_snoc(own, t, x, c, LI.band_r(SV.eq(SV.nth(own, y), c), allo(own, t, c), h), hx))
