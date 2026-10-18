# bend-cad: Tarjan's components partition the equations they start from
# (DESIGN §10.4 (6); ROADMAP: solve_complete). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/tarjanpf.draft lib/tarjanpf.bend
#
# lib/struct.bend's tarjan walks from each root in turn, with an explicit
# call stack cs and component stack st. Through the walk (tinv), with R the
# reached equations (st, then the components found so far):
# - R is distinct and inside good, an equation is in R exactly when it has
#   an index, and R with the roots still to come covers good;
# - the call stack's equations lie on st in order, the bottom one at st's
#   very bottom (segs);
# - during a search from a root numbered base, everything on st has
#   base <= low <= idx, and st's bottom (the root) has idx = base.
# Popping st down to v leaves R as it was, read through rev.go. So a root,
# when it finishes, has low = idx = base and pops the whole stack, and at
# the end st is empty: the components partition good. The fuel covers one
# step per root, per edge and per finish (wm, which every step lowers).

import Base
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./nat.bend as LN
import ./natring.bend as NR
import ./listpf.bend as L
import ./dfspf.bend as D

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Booleans
# --------

def nilb(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# a and b agree
def biff(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

def biff_eq(a: Bool, b: Bool, h: {biff(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, KA.ft(h))
    case False{} False{}:
      {==}

def biff_refl(a: Bool) -> {biff(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def biff_i(+a: Bool, +b: Bool, e: {a == b : Bool}) -> {biff(a, b) == True{} : Bool}:
  %e : {biff(a, _) == True{} : Bool}
  biff_refl(a)

def bor_swap(p: Bool, q: Bool, -r: Bool) -> {SV.bor(p, SV.bor(q, r)) == SV.bor(q, SV.bor(p, r)) : Bool}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bswap2(p: Bool, q: Bool, r: Bool, -d: Bool) -> {SV.band(SV.bnot(SV.bor(p, q)), SV.band(SV.bnot(r), d)) == SV.band(SV.bnot(SV.bor(p, r)), SV.band(SV.bnot(q), d)) : Bool}:
  match p q r:
    case True{} q r:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# Numbers
# -------

# u /= h, as the stack's test sees it
def ne_nateq(+u: Nat, +h: Nat, e: {SV.eq(u, h) == False{} : Bool}) -> {KA.nateq(h, u) == False{} : Bool}:
  %L.eq_sv(h, u) : {_ == False{} : Bool}
  %L.eq_sym(u, h) : {_ == False{} : Bool}
  e

def nateq_ne(+v: Nat, +h: Nat, e: {KA.nateq(h, v) == False{} : Bool}) -> {SV.eq(v, h) == False{} : Bool}:
  %Equal.sym(Bool, SV.eq(v, h), SV.eq(h, v), L.eq_sym(v, h)) : {_ == False{} : Bool}
  %Equal.sym(Bool, SV.eq(h, v), KA.nateq(h, v), L.eq_sv(h, v)) : {_ == False{} : Bool}
  e

# u <= m, u /= m: u < m
def lt_of_ne(u: Nat, m: Nat, h1: {KA.natle(u, m) == True{} : Bool}, h2: {SV.eq(u, m) == False{} : Bool}) -> {KA.natle(1n+u, m) == True{} : Bool}:
  match u m:
    case 0n 0n:
      absurd({KA.natle(1n, 0n) == True{} : Bool}, KA.tf(h2))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({KA.natle(2n+i, 0n) == True{} : Bool}, KA.ft(h1))
    case 1n+i 1n+j:
      lt_of_ne(i, j, h1, h2)

def nmin_le.go(b: Bool, +a: Nat, +c: Nat, e: {KA.natle(a, c) == b : Bool}) -> {KA.natle(ST.nmin.go(b, a, c), a) == True{} : Bool}:
  match b:
    case True{}:
      KA.natle_refl(a)
    case False{}:
      KA.natle_flip(a, c, e)

# min(a, c) <= a
def nmin_le(+a: Nat, +c: Nat) -> {KA.natle(ST.nmin(a, c), a) == True{} : Bool}:
  nmin_le.go(KA.natle(a, c), a, c, {==})

def nmin_ge.go(b: Bool, +x: Nat, +a: Nat, +c: Nat, ha: {KA.natle(x, a) == True{} : Bool}, hc: {KA.natle(x, c) == True{} : Bool}) -> {KA.natle(x, ST.nmin.go(b, a, c)) == True{} : Bool}:
  match b:
    case True{}:
      ha
    case False{}:
      hc

# x <= a, x <= c: x <= min(a, c)
def nmin_ge(+x: Nat, +a: Nat, +c: Nat, ha: {KA.natle(x, a) == True{} : Bool}, hc: {KA.natle(x, c) == True{} : Bool}) -> {KA.natle(x, ST.nmin(a, c)) == True{} : Bool}:
  nmin_ge.go(KA.natle(a, c), x, a, c, ha, hc)

# Lists
# -----

def app_nil(xs: List<&2, Nat>) -> {ST.app(xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(t, Nil{}), t, app_nil(t)) : {Con{h, _} == Con{h, t} : List<&2, Nat>}
      {==}

def app_assoc(a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>) -> {ST.app(ST.app(a, b), c) == ST.app(a, ST.app(b, c)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(ST.app(t, b), c), ST.app(t, ST.app(b, c)), app_assoc(t, b, c)) : {Con{h, _} == Con{h, ST.app(t, ST.app(b, c))} : List<&2, Nat>}
      {==}

def len_sv(xs: List<&2, Nat>) -> {ST.len(xs) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, ST.len(t), SV.len(t), len_sv(t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def app_subl_l(a: List<&2, Nat>, +b: List<&2, Nat>) -> {L.subl(a, ST.app(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      L.subl_con(h, t, Con{h, ST.app(t, b)}, L.mem_hd(h, ST.app(t, b)), L.subl_cons_r(t, h, ST.app(t, b), app_subl_l(t, b)))

def app_subl_r(a: List<&2, Nat>, +b: List<&2, Nat>) -> {L.subl(b, ST.app(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      L.subl_refl(b)
    case Con{+h, +t}:
      L.subl_cons_r(b, h, ST.app(t, b), app_subl_r(t, b))

def subl_app(a: List<&2, Nat>, +b: List<&2, Nat>, +z: List<&2, Nat>, +ha: {L.subl(a, z) == True{} : Bool}, hb: {L.subl(b, z) == True{} : Bool}) -> {L.subl(ST.app(a, b), z) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+h, +t}:
      L.subl_con(h, ST.app(t, b), z, L.subl_hd(h, t, z, ha), subl_app(t, b, z, L.subl_tl(h, t, z, ha), hb))

# b within c: a ++ b within a ++ c
def app_mono(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, h: {L.subl(b, c) == True{} : Bool}) -> {L.subl(ST.app(a, b), ST.app(a, c)) == True{} : Bool}:
  subl_app(a, b, ST.app(a, c), app_subl_l(a, c), L.subl_trans(b, c, ST.app(a, c), h, app_subl_r(a, c)))

def mem_app_l(+u: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, a) == True{} : Bool}) -> {SV.mem(u, ST.app(a, b)) == True{} : Bool}:
  L.subl_mem(u, a, ST.app(a, b), h, app_subl_l(a, b))

def mem_app_r(+u: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, b) == True{} : Bool}) -> {SV.mem(u, ST.app(a, b)) == True{} : Bool}:
  L.subl_mem(u, b, ST.app(a, b), h, app_subl_r(a, b))

def notin_app_l(+u: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, ST.app(a, b)) == False{} : Bool}) -> {SV.mem(u, a) == False{} : Bool}:
  L.notin_subl(u, a, ST.app(a, b), h, app_subl_l(a, b))

def dist_app_l(a: List<&2, Nat>, +b: List<&2, Nat>, +h: {SV.distinct(ST.app(a, b)) == True{} : Bool}) -> {SV.distinct(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.dist_con(x, t, notin_app_l(x, t, b, L.dist_hd(x, ST.app(t, b), h)), dist_app_l(t, b, L.dist_tl(x, ST.app(t, b), h)))

# rev.go(a, b) within z when a and b are
def rg_subl(a: List<&2, Nat>, +b: List<&2, Nat>, +z: List<&2, Nat>, +ha: {L.subl(a, z) == True{} : Bool}, hb: {L.subl(b, z) == True{} : Bool}) -> {L.subl(ST.rev.go(a, b), z) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+h, +t}:
      rg_subl(t, Con{h, b}, z, L.subl_tl(h, t, z, ha), L.subl_con(h, b, z, L.subl_hd(h, t, z, ha), hb))

def rg_app(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {L.subl(ST.rev.go(a, b), ST.app(a, b)) == True{} : Bool}:
  rg_subl(a, b, ST.app(a, b), app_subl_l(a, b), app_subl_r(a, b))

def app_rg(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {L.subl(ST.app(a, b), ST.rev.go(a, b)) == True{} : Bool}:
  +h = D.rev_go_subl(a, b)
  subl_app(a, b, ST.rev.go(a, b), L.band_l(L.subl(a, ST.rev.go(a, b)), L.subl(b, ST.rev.go(a, b)), h), L.band_r(L.subl(a, ST.rev.go(a, b)), L.subl(b, ST.rev.go(a, b)), h))

# moving an entry to the front keeps membership and distinctness
def mem_move(+u: Nat, t: List<&2, Nat>, +h: Nat, +b: List<&2, Nat>) -> {SV.mem(u, ST.app(t, Con{h, b})) == SV.mem(u, Con{h, ST.app(t, b)}) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +t2}:
      %Equal.sym(Bool, SV.mem(u, ST.app(t2, Con{h, b})), SV.mem(u, Con{h, ST.app(t2, b)}), mem_move(u, t2, h, b)) : {SV.bor(SV.eq(u, x), _) == SV.bor(SV.eq(u, h), SV.bor(SV.eq(u, x), SV.mem(u, ST.app(t2, b)))) : Bool}
      bor_swap(SV.eq(u, x), SV.eq(u, h), SV.mem(u, ST.app(t2, b)))

def dist_move(t: List<&2, Nat>, +h: Nat, +b: List<&2, Nat>) -> {SV.distinct(ST.app(t, Con{h, b})) == SV.distinct(Con{h, ST.app(t, b)}) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +t2}:
      +a = ST.app(t2, b)
      %Equal.sym(Bool, SV.mem(x, ST.app(t2, Con{h, b})), SV.mem(x, Con{h, a}), mem_move(x, t2, h, b)) : {SV.band(SV.bnot(_), SV.distinct(ST.app(t2, Con{h, b}))) == SV.band(SV.bnot(SV.bor(SV.eq(h, x), SV.mem(h, a))), SV.band(SV.bnot(SV.mem(x, a)), SV.distinct(a))) : Bool}
      %Equal.sym(Bool, SV.distinct(ST.app(t2, Con{h, b})), SV.distinct(Con{h, a}), dist_move(t2, h, b)) : {SV.band(SV.bnot(SV.bor(SV.eq(x, h), SV.mem(x, a))), _) == SV.band(SV.bnot(SV.bor(SV.eq(h, x), SV.mem(h, a))), SV.band(SV.bnot(SV.mem(x, a)), SV.distinct(a))) : Bool}
      %Equal.sym(Bool, SV.eq(x, h), SV.eq(h, x), L.eq_sym(x, h)) : {SV.band(SV.bnot(SV.bor(_, SV.mem(x, a))), SV.band(SV.bnot(SV.mem(h, a)), SV.distinct(a))) == SV.band(SV.bnot(SV.bor(SV.eq(h, x), SV.mem(h, a))), SV.band(SV.bnot(SV.mem(x, a)), SV.distinct(a))) : Bool}
      bswap2(SV.eq(h, x), SV.mem(x, a), SV.mem(h, a), SV.distinct(a))

# reversing the front part keeps distinctness
def dist_rg(a: List<&2, Nat>, +b: List<&2, Nat>) -> {SV.distinct(ST.rev.go(a, b)) == SV.distinct(ST.app(a, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, SV.distinct(ST.rev.go(t, Con{h, b})), SV.distinct(ST.app(t, Con{h, b})), dist_rg(t, Con{h, b})) : {_ == SV.distinct(Con{h, ST.app(t, b)}) : Bool}
      dist_move(t, h, b)

# membership is the same in two lists each within the other
def mem_eqv.go(+u: Nat, +r1: List<&2, Nat>, +r2: List<&2, Nat>, b: Bool, e: {SV.mem(u, r2) == b : Bool}, h1: {L.subl(r1, r2) == True{} : Bool}, h2: {L.subl(r2, r1) == True{} : Bool}) -> {SV.mem(u, r1) == b : Bool}:
  match b:
    case True{}:
      L.subl_mem(u, r2, r1, e, h2)
    case False{}:
      L.notin_subl(u, r1, r2, e, h1)

def mem_eqv(+u: Nat, +r1: List<&2, Nat>, +r2: List<&2, Nat>, h1: {L.subl(r1, r2) == True{} : Bool}, h2: {L.subl(r2, r1) == True{} : Bool}) -> {SV.mem(u, r1) == SV.mem(u, r2) : Bool}:
  mem_eqv.go(u, r1, r2, SV.mem(u, r2), {==}, h1, h2)

# Popping the stack
# -----------------
# tpop(st, b, v, acc, ..) pops st down to v (b: st's top is v): what is left
# is after(st, b, v), and the component is upto(st, b, v, acc).

def after(st: List<&2, Nat>, b: Bool, +v: Nat) -> List<&2, Nat>:
  match st b:
    case Nil{} b:
      Nil{}
    case Con{h, t} True{}:
      t
    case Con{h, +t} False{}:
      after(t, KA.nateq(ST.hd(t), v), v)

def upto(st: List<&2, Nat>, b: Bool, +v: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match st b:
    case Nil{} b:
      acc
    case Con{h, t} True{}:
      Con{h, acc}
    case Con{h, +t} False{}:
      upto(t, KA.nateq(ST.hd(t), v), v, Con{h, acc})

# st below its first v
def aft(+v: Nat, +st: List<&2, Nat>) -> List<&2, Nat>:
  after(st, KA.nateq(ST.hd(st), v), v)

def tpop_eq(st: List<&2, Nat>, b: Bool, +v: Nat, acc: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>) -> {ST.tpop(st, b, v, acc, c, idx, low, cs, out) == ST.TS{c, idx, low, after(st, b, v), cs, Con{upto(st, b, v, acc), out}} : ST.TS}:
  match st b:
    case Nil{} b:
      {==}
    case Con{h, t} True{}:
      {==}
    case Con{h, +t} False{}:
      tpop_eq(t, KA.nateq(ST.hd(t), v), v, Con{h, acc}, c, idx, low, cs, out)

# read through rev.go, popping changes nothing
def rgid(st: List<&2, Nat>, b: Bool, +v: Nat, acc: List<&2, Nat>, +cc: List<&2, Nat>) -> {ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, acc), cc)) == ST.rev.go(st, ST.app(acc, cc)) : List<&2, Nat>}:
  match st b:
    case Nil{} b:
      {==}
    case Con{h, t} True{}:
      {==}
    case Con{h, +t} False{}:
      rgid(t, KA.nateq(ST.hd(t), v), v, Con{h, acc}, cc)

def after_sub(st: List<&2, Nat>, b: Bool, +v: Nat) -> {L.subl(after(st, b, v), st) == True{} : Bool}:
  match st b:
    case Nil{} b:
      {==}
    case Con{+h, +t} True{}:
      L.subl_cons_r(t, h, t, L.subl_refl(t))
    case Con{+h, +t} False{}:
      L.subl_cons_r(after(t, KA.nateq(ST.hd(t), v), v), h, t, after_sub(t, KA.nateq(ST.hd(t), v), v))

# u is not st's top: below u is the same in h :: t and in t
def aft_skip(+h: Nat, +t: List<&2, Nat>, +u: Nat, hn: {KA.nateq(h, u) == False{} : Bool}) -> {aft(u, Con{h, t}) == aft(u, t) : List<&2, Nat>}:
  %Equal.sym(Bool, KA.nateq(h, u), False{}, hn) : {after(Con{h, t}, _, u) == aft(u, t) : List<&2, Nat>}
  {==}

def aft_aft.go(+h: Nat, +t: List<&2, Nat>, +v: Nat, +u: Nat, b: Bool, e: {KA.nateq(h, v) == b : Bool}, +hd: {SV.distinct(Con{h, t}) == True{} : Bool}, hv: {SV.mem(v, Con{h, t}) == True{} : Bool}, +hu: {SV.mem(u, after(Con{h, t}, b, v)) == True{} : Bool}, ih: {SV.distinct(t) == True{} : Bool} -> {SV.mem(v, t) == True{} : Bool} -> {SV.mem(u, aft(v, t)) == True{} : Bool} -> {aft(u, t) == aft(u, aft(v, t)) : List<&2, Nat>}) -> {aft(u, Con{h, t}) == aft(u, after(Con{h, t}, b, v)) : List<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Nat>, aft(u, Con{h, t}), aft(u, t), aft_skip(h, t, u, ne_nateq(u, h, L.mem_ne(u, h, t, hu, L.dist_hd(h, t, hd))))) : {_ == aft(u, t) : List<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Nat>, aft(u, Con{h, t}), aft(u, t), aft_skip(h, t, u, ne_nateq(u, h, L.mem_ne(u, h, t, L.subl_mem(u, aft(v, t), t, hu, after_sub(t, KA.nateq(ST.hd(t), v), v)), L.dist_hd(h, t, hd))))) : {_ == aft(u, aft(v, t)) : List<&2, Nat>}
      ih(L.dist_tl(h, t, hd), L.mem_tl_inv(v, h, t, hv, nateq_ne(v, h, e)), hu)

# st distinct, v in st, u below v: below u is the same in st and below v
def aft_aft(st: List<&2, Nat>, +v: Nat, +u: Nat, hd: {SV.distinct(st) == True{} : Bool}, hv: {SV.mem(v, st) == True{} : Bool}, hu: {SV.mem(u, aft(v, st)) == True{} : Bool}) -> {aft(u, st) == aft(u, aft(v, st)) : List<&2, Nat>}:
  match st:
    case Nil{}:
      absurd({aft(u, Nil{}) == aft(u, aft(v, Nil{})) : List<&2, Nat>}, KA.ft(hv))
    case Con{+h, +t}:
      aft_aft.go(h, t, v, u, KA.nateq(h, v), {==}, hd, hv, hu, p => q => r => aft_aft(t, v, u, p, q, r))

# The call stack on the component stack
# -------------------------------------
# segs(cs, st): each frame's equation is on st, in the call stack's order,
# and nothing lies below the bottom frame's.

def segs(cs: List<&2, ST.TF>, +st: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      nilb(st)
    case Con{ST.TF{+v, r}, ct}:
      SV.band(SV.mem(v, st), segs(ct, aft(v, st)))

def segs_push(+w: Nat, rest: List<&2, Nat>, +cs: List<&2, ST.TF>, +st: List<&2, Nat>, h: {segs(cs, st) == True{} : Bool}) -> {segs(Con{ST.TF{w, rest}, cs}, Con{w, st}) == True{} : Bool}:
  %Equal.sym(Bool, KA.nateq(w, w), True{}, KA.nateq_refl(w)) : {SV.band(SV.mem(w, Con{w, st}), segs(cs, after(Con{w, st}, _, w))) == True{} : Bool}
  L.band_i(SV.mem(w, Con{w, st}), segs(cs, st), L.mem_hd(w, st), h)

# a frame finishes without popping: the frame below is still in place
def segs_keep(+v: Nat, +u: Nat, r2: List<&2, Nat>, +ct2: List<&2, ST.TF>, +st: List<&2, Nat>, hd: {SV.distinct(st) == True{} : Bool}, hv: {SV.mem(v, st) == True{} : Bool}, +h: {segs(Con{ST.TF{u, r2}, ct2}, aft(v, st)) == True{} : Bool}) -> {segs(Con{ST.TF{u, r2}, ct2}, st) == True{} : Bool}:
  +hu = L.band_l(SV.mem(u, aft(v, st)), segs(ct2, aft(u, aft(v, st))), h)
  %Equal.sym(List<&2, Nat>, aft(u, st), aft(u, aft(v, st)), aft_aft(st, v, u, hd, hv, hu)) : {SV.band(SV.mem(u, st), segs(ct2, _)) == True{} : Bool}
  L.band_i(SV.mem(u, st), segs(ct2, aft(u, aft(v, st))), L.subl_mem(u, aft(v, st), st, hu, after_sub(st, KA.nateq(ST.hd(st), v), v)), L.band_r(SV.mem(u, aft(v, st)), segs(ct2, aft(u, aft(v, st))), h))

# Low links on the stack
# ----------------------

# base <= low(u) <= idx(u)
def okat(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat) -> Bool:
  SV.band(KA.natle(base, ST.look.of(ST.getm(low, u))), KA.natle(ST.look.of(ST.getm(low, u)), ST.look.of(ST.getm(idx, u))))

def stok(st: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>) -> Bool:
  match st:
    case Nil{}:
      True{}
    case Con{+u, t}:
      SV.band(okat(base, idx, low, u), stok(t, base, idx, low))

def okat_seti(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat, +w: Nat, +x: Maybe<&2, Nat>, hne: {SV.eq(u, w) == False{} : Bool}, h: {okat(base, idx, low, u) == True{} : Bool}) -> {okat(base, ST.setm(idx, w, x), low, u) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, w, x), u), ST.getm(idx, u), L.getm_set_ne(idx, w, u, x, hne)) : {SV.band(KA.natle(base, ST.look.of(ST.getm(low, u))), KA.natle(ST.look.of(ST.getm(low, u)), ST.look.of(_))) == True{} : Bool}
  h

def okat_setl(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat, +w: Nat, +y: Maybe<&2, Nat>, hne: {SV.eq(u, w) == False{} : Bool}, h: {okat(base, idx, low, u) == True{} : Bool}) -> {okat(base, idx, ST.setm(low, w, y), u) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(low, w, y), u), ST.getm(low, u), L.getm_set_ne(low, w, u, y, hne)) : {SV.band(KA.natle(base, ST.look.of(_)), KA.natle(ST.look.of(_), ST.look.of(ST.getm(idx, u)))) == True{} : Bool}
  h

# v's low drops to x (base <= x)
def okat_low(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Nat, hx: {KA.natle(base, x) == True{} : Bool}, hl: {KA.natle(1n+v, L.mlen(low)) == True{} : Bool}, +h: {okat(base, idx, low, v) == True{} : Bool}) -> {okat(base, idx, ST.setm(low, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), x)}), v) == True{} : Bool}:
  +lv = ST.look.of(ST.getm(low, v))
  +iv = ST.look.of(ST.getm(idx, v))
  +nm = ST.nmin(lv, x)
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(low, v, Some{nm}), v), Some{nm}, L.getm_set_eq(low, v, Some{nm}, hl)) : {SV.band(KA.natle(base, ST.look.of(_)), KA.natle(ST.look.of(_), iv)) == True{} : Bool}
  L.band_i(KA.natle(base, nm), KA.natle(nm, iv), nmin_ge(base, lv, x, L.band_l(KA.natle(base, lv), KA.natle(lv, iv), h), hx), KA.natle_trans(nm, lv, iv, nmin_le(lv, x), L.band_r(KA.natle(base, lv), KA.natle(lv, iv), h)))

def okat_push(+base: Nat, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +w: Nat, hc: {KA.natle(base, c) == True{} : Bool}, hi: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}, hl: {KA.natle(1n+w, L.mlen(low)) == True{} : Bool}) -> {okat(base, ST.setm(idx, w, Some{c}), ST.setm(low, w, Some{c}), w) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, w, Some{c}), w), Some{c}, L.getm_set_eq(idx, w, Some{c}, hi)) : {SV.band(KA.natle(base, ST.look.of(ST.getm(ST.setm(low, w, Some{c}), w))), KA.natle(ST.look.of(ST.getm(ST.setm(low, w, Some{c}), w)), ST.look.of(_))) == True{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(low, w, Some{c}), w), Some{c}, L.getm_set_eq(low, w, Some{c}, hl)) : {SV.band(KA.natle(base, ST.look.of(_)), KA.natle(ST.look.of(_), c)) == True{} : Bool}
  L.band_i(KA.natle(base, c), KA.natle(c, c), hc, KA.natle_refl(c))

def ne_of_notin(+u: Nat, +w: Nat, +t: List<&2, Nat>, hn: {SV.mem(w, Con{u, t}) == False{} : Bool}) -> {SV.eq(u, w) == False{} : Bool}:
  %L.eq_sym(w, u) : {_ == False{} : Bool}
  L.bor_fl(SV.eq(w, u), SV.mem(w, t), hn)

def stok_seti(st: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +w: Nat, +x: Maybe<&2, Nat>, +hn: {SV.mem(w, st) == False{} : Bool}, +h: {stok(st, base, idx, low) == True{} : Bool}) -> {stok(st, base, ST.setm(idx, w, x), low) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      L.band_i(okat(base, ST.setm(idx, w, x), low, u), stok(t, base, ST.setm(idx, w, x), low), okat_seti(base, idx, low, u, w, x, ne_of_notin(u, w, t, hn), L.band_l(okat(base, idx, low, u), stok(t, base, idx, low), h)), stok_seti(t, base, idx, low, w, x, L.bor_fr(SV.eq(w, u), SV.mem(w, t), hn), L.band_r(okat(base, idx, low, u), stok(t, base, idx, low), h)))

def stok_setl(st: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +w: Nat, +y: Maybe<&2, Nat>, +hn: {SV.mem(w, st) == False{} : Bool}, +h: {stok(st, base, idx, low) == True{} : Bool}) -> {stok(st, base, idx, ST.setm(low, w, y)) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      L.band_i(okat(base, idx, ST.setm(low, w, y), u), stok(t, base, idx, ST.setm(low, w, y)), okat_setl(base, idx, low, u, w, y, ne_of_notin(u, w, t, hn), L.band_l(okat(base, idx, low, u), stok(t, base, idx, low), h)), stok_setl(t, base, idx, low, w, y, L.bor_fr(SV.eq(w, u), SV.mem(w, t), hn), L.band_r(okat(base, idx, low, u), stok(t, base, idx, low), h)))

# pushing w (fresh) numbered c >= base
def stok_push(+st: List<&2, Nat>, +base: Nat, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +w: Nat, +hn: {SV.mem(w, st) == False{} : Bool}, hc: {KA.natle(base, c) == True{} : Bool}, hi: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}, hl: {KA.natle(1n+w, L.mlen(low)) == True{} : Bool}, h: {stok(st, base, idx, low) == True{} : Bool}) -> {stok(Con{w, st}, base, ST.setm(idx, w, Some{c}), ST.setm(low, w, Some{c})) == True{} : Bool}:
  L.band_i(okat(base, ST.setm(idx, w, Some{c}), ST.setm(low, w, Some{c}), w), stok(st, base, ST.setm(idx, w, Some{c}), ST.setm(low, w, Some{c})), okat_push(base, c, idx, low, w, hc, hi, hl), stok_setl(st, base, ST.setm(idx, w, Some{c}), low, w, Some{c}, hn, stok_seti(st, base, idx, low, w, Some{c}, hn, h)))

def okat_lowne(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat, +v: Nat, +x: Nat, b: Bool, e: {SV.eq(u, v) == b : Bool}, hx: {KA.natle(base, x) == True{} : Bool}, hl: {KA.natle(1n+u, L.mlen(low)) == True{} : Bool}, h: {okat(base, idx, low, u) == True{} : Bool}) -> {okat(base, idx, ST.setm(low, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), x)}), u) == True{} : Bool}:
  match b:
    case True{}:
      +ee = L.eq_ok(u, v, e)
      %ee : {okat(base, idx, ST.setm(low, _, Some{ST.nmin(ST.look.of(ST.getm(low, _)), x)}), u) == True{} : Bool}
      okat_low(base, idx, low, u, x, hx, hl, h)
    case False{}:
      okat_setl(base, idx, low, u, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), x)}, e, h)

# v's low drops to x >= base
def stok_low(st: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Nat, +hx: {KA.natle(base, x) == True{} : Bool}, +hb: {SV.below(st, L.mlen(low)) == True{} : Bool}, +h: {stok(st, base, idx, low) == True{} : Bool}) -> {stok(st, base, idx, ST.setm(low, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), x)})) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +y = {Some{ST.nmin(ST.look.of(ST.getm(low, v)), x)} : Maybe<&2, Nat>}
      L.band_i(okat(base, idx, ST.setm(low, v, y), u), stok(t, base, idx, ST.setm(low, v, y)), okat_lowne(base, idx, low, u, v, x, SV.eq(u, v), {==}, hx, D.below_hd(u, t, L.mlen(low), hb), L.band_l(okat(base, idx, low, u), stok(t, base, idx, low), h)), stok_low(t, base, idx, low, v, x, hx, D.below_tl(u, t, L.mlen(low), hb), L.band_r(okat(base, idx, low, u), stok(t, base, idx, low), h)))

def stok_after(st: List<&2, Nat>, b: Bool, +v: Nat, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, h: {stok(st, base, idx, low) == True{} : Bool}) -> {stok(after(st, b, v), base, idx, low) == True{} : Bool}:
  match st b:
    case Nil{} b:
      {==}
    case Con{+u, +t} True{}:
      L.band_r(okat(base, idx, low, u), stok(t, base, idx, low), h)
    case Con{+u, +t} False{}:
      stok_after(t, KA.nateq(ST.hd(t), v), v, base, idx, low, L.band_r(okat(base, idx, low, u), stok(t, base, idx, low), h))

def stok_at.go(+x: Nat, +t: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat, b: Bool, e: {SV.eq(u, x) == b : Bool}, hm: {SV.bor(b, SV.mem(u, t)) == True{} : Bool}, +h: {stok(Con{x, t}, base, idx, low) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {stok(t, base, idx, low) == True{} : Bool} -> {okat(base, idx, low, u) == True{} : Bool}) -> {okat(base, idx, low, u) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, u, x, L.eq_ok(u, x, e)) : {okat(base, idx, low, _) == True{} : Bool}
      L.band_l(okat(base, idx, low, x), stok(t, base, idx, low), h)
    case False{}:
      ih(hm, L.band_r(okat(base, idx, low, x), stok(t, base, idx, low), h))

def stok_at(st: List<&2, Nat>, +base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +u: Nat, hm: {SV.mem(u, st) == True{} : Bool}, h: {stok(st, base, idx, low) == True{} : Bool}) -> {okat(base, idx, low, u) == True{} : Bool}:
  match st:
    case Nil{}:
      absurd({okat(base, idx, low, u) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      stok_at.go(x, t, base, idx, low, u, SV.eq(u, x), {==}, hm, h, p => q => stok_at(t, base, idx, low, u, p, q))

# The bottom of the stack
# -----------------------

# st's last entry has index base
def lastok(st: List<&2, Nat>, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat) -> Bool:
  match st:
    case Nil{}:
      True{}
    case Con{h, Nil{}}:
      SV.eq(ST.look.of(ST.getm(idx, h)), base)
    case Con{h, Con{h2, t}}:
      lastok(Con{h2, t}, idx, base)

def lastok_tl(+h: Nat, t: List<&2, Nat>, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, hl: {lastok(Con{h, t}, idx, base) == True{} : Bool}) -> {lastok(t, idx, base) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{h2, t2}:
      hl

def lastok_set(st: List<&2, Nat>, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, +w: Nat, +x: Maybe<&2, Nat>, hn: {SV.mem(w, st) == False{} : Bool}, h: {lastok(st, idx, base) == True{} : Bool}) -> {lastok(st, ST.setm(idx, w, x), base) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{+u, Nil{}}:
      %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, w, x), u), ST.getm(idx, u), L.getm_set_ne(idx, w, u, x, ne_of_notin(u, w, Nil{}, hn))) : {SV.eq(ST.look.of(_), base) == True{} : Bool}
      h
    case Con{+u, Con{+h2, +t}}:
      lastok_set(Con{h2, t}, idx, base, w, x, L.bor_fr(SV.eq(w, u), SV.mem(w, Con{h2, t}), hn), h)

def lastok_after(st: List<&2, Nat>, b: Bool, +v: Nat, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, h: {lastok(st, idx, base) == True{} : Bool}) -> {lastok(after(st, b, v), idx, base) == True{} : Bool}:
  match st b:
    case Nil{} b:
      {==}
    case Con{+u, +t} True{}:
      lastok_tl(u, t, idx, base, h)
    case Con{+u, +t} False{}:
      lastok_after(t, KA.nateq(ST.hd(t), v), v, idx, base, lastok_tl(u, t, idx, base, h))

# pushing onto a stack holding v keeps its bottom
def lastok_cons(+w: Nat, st: List<&2, Nat>, +v: Nat, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, hm: {SV.mem(v, st) == True{} : Bool}, h: {lastok(st, idx, base) == True{} : Bool}) -> {lastok(Con{w, st}, idx, base) == True{} : Bool}:
  match st:
    case Nil{}:
      absurd({lastok(Con{w, Nil{}}, idx, base) == True{} : Bool}, KA.ft(hm))
    case Con{h2, t}:
      h

def lastok_one(+h: Nat, t: List<&2, Nat>, +r: Nat, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, er: {h == r : Nat}, hn: {nilb(t) == True{} : Bool}, hl: {lastok(Con{h, t}, idx, base) == True{} : Bool}) -> {SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}:
  match t:
    case Nil{}:
      %er : {SV.eq(ST.look.of(ST.getm(idx, _)), base) == True{} : Bool}
      hl
    case Con{h2, t2}:
      absurd({SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}, KA.ft(hn))

def lastok_root.go(+h: Nat, +t: List<&2, Nat>, +r: Nat, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, b: Bool, e: {KA.nateq(h, r) == b : Bool}, +hl: {lastok(Con{h, t}, idx, base) == True{} : Bool}, hm: {SV.mem(r, Con{h, t}) == True{} : Bool}, hn: {nilb(after(Con{h, t}, b, r)) == True{} : Bool}, ih: {lastok(t, idx, base) == True{} : Bool} -> {SV.mem(r, t) == True{} : Bool} -> {nilb(aft(r, t)) == True{} : Bool} -> {SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}) -> {SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}:
  match b:
    case True{}:
      lastok_one(h, t, r, idx, base, KA.nateq_ok(h, r, e), hn, hl)
    case False{}:
      ih(lastok_tl(h, t, idx, base, hl), L.mem_tl_inv(r, h, t, hm, nateq_ne(r, h, e)), hn)

# r in st with nothing below it: r is st's last entry, numbered base
def lastok_root(st: List<&2, Nat>, +r: Nat, +idx: List<&2, Maybe<&2, Nat>>, +base: Nat, hl: {lastok(st, idx, base) == True{} : Bool}, hm: {SV.mem(r, st) == True{} : Bool}, hn: {nilb(aft(r, st)) == True{} : Bool}) -> {SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}:
  match st:
    case Nil{}:
      absurd({SV.eq(ST.look.of(ST.getm(idx, r)), base) == True{} : Bool}, KA.ft(hm))
    case Con{+h, +t}:
      lastok_root.go(h, t, r, idx, base, KA.nateq(h, r), {==}, hl, hm, hn, p => q => s => lastok_root(t, r, idx, base, p, q, s))

# Indices and the reached equations
# ---------------------------------
# agree(n, idx, rr): each u < n has an index exactly when it is in rr.

def agree(n: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n++m:
      SV.band(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr))

def agree_at.go(+m: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +u: Nat, b: Bool, e: {SV.eq(u, m) == b : Bool}, hu: {KA.natle(u, m) == True{} : Bool}, +h: {agree(1n+m, idx, rr) == True{} : Bool}, ih: {KA.natle(1n+u, m) == True{} : Bool} -> {agree(m, idx, rr) == True{} : Bool} -> {L.issome(ST.getm(idx, u)) == SV.mem(u, rr) : Bool}) -> {L.issome(ST.getm(idx, u)) == SV.mem(u, rr) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, u, m, L.eq_ok(u, m, e)) : {L.issome(ST.getm(idx, _)) == SV.mem(_, rr) : Bool}
      biff_eq(L.issome(ST.getm(idx, m)), SV.mem(m, rr), L.band_l(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h))
    case False{}:
      ih(lt_of_ne(u, m, hu, e), L.band_r(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h))

def agree_at(n: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +u: Nat, hu: {KA.natle(1n+u, n) == True{} : Bool}, h: {agree(n, idx, rr) == True{} : Bool}) -> {L.issome(ST.getm(idx, u)) == SV.mem(u, rr) : Bool}:
  match n:
    case 0n:
      absurd({L.issome(ST.getm(idx, u)) == SV.mem(u, rr) : Bool}, KA.ft(hu))
    case 1n++m:
      agree_at.go(m, idx, rr, u, SV.eq(u, m), {==}, hu, h, p => q => agree_at(m, idx, rr, u, p, q))

def agree_hd.go(+m: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +w: Nat, +c: Nat, b: Bool, e: {SV.eq(m, w) == b : Bool}, hl: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}, h: {biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)) == True{} : Bool}) -> {biff(L.issome(ST.getm(ST.setm(idx, w, Some{c}), m)), SV.bor(b, SV.mem(m, rr))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, m, w, L.eq_ok(m, w, e)) : {biff(L.issome(ST.getm(ST.setm(idx, w, Some{c}), _)), True{}) == True{} : Bool}
      %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, w, Some{c}), w), Some{c}, L.getm_set_eq(idx, w, Some{c}, hl)) : {biff(L.issome(_), True{}) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, w, Some{c}), m), ST.getm(idx, m), L.getm_set_ne(idx, w, m, Some{c}, e)) : {biff(L.issome(_), SV.mem(m, rr)) == True{} : Bool}
      h

# w gets an index and joins rr
def agree_push(n: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +w: Nat, +c: Nat, +hl: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}, +h: {agree(n, idx, rr) == True{} : Bool}) -> {agree(n, ST.setm(idx, w, Some{c}), Con{w, rr}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      +hh = L.band_l(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h)
      L.band_i(biff(L.issome(ST.getm(ST.setm(idx, w, Some{c}), m)), SV.mem(m, Con{w, rr})), agree(m, ST.setm(idx, w, Some{c}), Con{w, rr}), agree_hd.go(m, idx, rr, w, c, SV.eq(m, w), {==}, hl, hh), agree_push(m, idx, rr, w, c, hl, L.band_r(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h)))

# rr and rr2 each within the other
def agree_eqv(n: Nat, +idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +rr2: List<&2, Nat>, +h1: {L.subl(rr, rr2) == True{} : Bool}, +h2: {L.subl(rr2, rr) == True{} : Bool}, +h: {agree(n, idx, rr) == True{} : Bool}) -> {agree(n, idx, rr2) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.band_i(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr2)), agree(m, idx, rr2), (%mem_eqv(m, rr, rr2, h1, h2) : {biff(L.issome(ST.getm(idx, m)), _) == True{} : Bool}
        L.band_l(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h)), agree_eqv(m, idx, rr, rr2, h1, h2, L.band_r(biff(L.issome(ST.getm(idx, m)), SV.mem(m, rr)), agree(m, idx, rr), h)))

# small facts used by the steps
def lt_nq(+u: Nat, +good: List<&2, Nat>, +nq: Nat, hm: {SV.mem(u, good) == True{} : Bool}, hb: {SV.below(good, nq) == True{} : Bool}) -> {KA.natle(1n+u, nq) == True{} : Bool}:
  %L.lt_sv(u, nq) : {_ == True{} : Bool}
  D.below_mem(u, good, nq, hm, hb)

def lt_ml(+u: Nat, +xs: List<&2, Maybe<&2, Nat>>, +nq: Nat, hm: {SV.eq(L.mlen(xs), nq) == True{} : Bool}, h: {KA.natle(1n+u, nq) == True{} : Bool}) -> {KA.natle(1n+u, L.mlen(xs)) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(xs), nq, L.eq_ok(L.mlen(xs), nq, hm)) : {KA.natle(1n+u, _) == True{} : Bool}
  h

def ml_set(+xs: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Maybe<&2, Nat>, +nq: Nat, h: {SV.eq(L.mlen(xs), nq) == True{} : Bool}) -> {SV.eq(L.mlen(ST.setm(xs, v, x)), nq) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(ST.setm(xs, v, x)), L.mlen(xs), L.mlen_set(xs, v, x)) : {SV.eq(_, nq) == True{} : Bool}
  h

def st_below(+st: List<&2, Nat>, +cc: List<&2, Nat>, +good: List<&2, Nat>, +nq: Nat, +low: List<&2, Maybe<&2, Nat>>, hi: {L.subl(ST.app(st, cc), good) == True{} : Bool}, hb: {SV.below(good, nq) == True{} : Bool}, hm: {SV.eq(L.mlen(low), nq) == True{} : Bool}) -> {SV.below(st, L.mlen(low)) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(low), nq, L.eq_ok(L.mlen(low), nq, hm)) : {SV.below(st, _) == True{} : Bool}
  D.below_subl(st, good, nq, L.subl_trans(st, ST.app(st, cc), good, app_subl_l(st, cc), hi), hb)

# u has no index: it is not in rr
def notin_of(+idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +n: Nat, +u: Nat, hu: {KA.natle(1n+u, n) == True{} : Bool}, ha: {agree(n, idx, rr) == True{} : Bool}, e: {ST.getm(idx, u) == None{} : Maybe<&2, Nat>}) -> {SV.mem(u, rr) == False{} : Bool}:
  %agree_at(n, idx, rr, u, hu, ha) : {_ == False{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, ST.getm(idx, u), None{}, e) : {L.issome(_) == False{} : Bool}
  {==}

def in_of(+idx: List<&2, Maybe<&2, Nat>>, +rr: List<&2, Nat>, +n: Nat, +u: Nat, +i: Nat, hu: {KA.natle(1n+u, n) == True{} : Bool}, ha: {agree(n, idx, rr) == True{} : Bool}, e: {ST.getm(idx, u) == Some{i} : Maybe<&2, Nat>}) -> {SV.mem(u, rr) == True{} : Bool}:
  %agree_at(n, idx, rr, u, hu, ha) : {_ == True{} : Bool}
  %Equal.sym(Maybe<&2, Nat>, ST.getm(idx, u), Some{i}, e) : {L.issome(_) == True{} : Bool}
  {==}

def mem_of_st(+w: Nat, +st: List<&2, Nat>, eo: {ST.mem(w, st) == True{} : Bool}) -> {SV.mem(w, st) == True{} : Bool}:
  %Equal.sym(Bool, SV.mem(w, st), ST.mem(w, st), L.mem_sv(w, st)) : {_ == True{} : Bool}
  eo

def idx_is(+idx: List<&2, Maybe<&2, Nat>>, +w: Nat, +iw: Nat, +lw: Nat, e: {ST.getm(idx, w) == Some{iw} : Maybe<&2, Nat>}, h: {KA.natle(lw, ST.look.of(ST.getm(idx, w))) == True{} : Bool}) -> {KA.natle(lw, iw) == True{} : Bool}:
  %e : {KA.natle(lw, ST.look.of(_)) == True{} : Bool}
  h

# w on the stack, indexed iw: base <= iw
def base_le(+base: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +w: Nat, +iw: Nat, e: {ST.getm(idx, w) == Some{iw} : Maybe<&2, Nat>}, +h: {okat(base, idx, low, w) == True{} : Bool}) -> {KA.natle(base, iw) == True{} : Bool}:
  +lw = ST.look.of(ST.getm(low, w))
  KA.natle_trans(base, lw, iw, L.band_l(KA.natle(base, lw), KA.natle(lw, ST.look.of(ST.getm(idx, w))), h), idx_is(idx, w, iw, lw, e, L.band_r(KA.natle(base, lw), KA.natle(lw, ST.look.of(ST.getm(idx, w))), h)))

def last_one(+idx: List<&2, Maybe<&2, Nat>>, +r: Nat, +c: Nat, hl: {KA.natle(1n+r, L.mlen(idx)) == True{} : Bool}) -> {lastok(Con{r, Nil{}}, ST.setm(idx, r, Some{c}), c) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(idx, r, Some{c}), r), Some{c}, L.getm_set_eq(idx, r, Some{c}, hl)) : {SV.eq(ST.look.of(_), c) == True{} : Bool}
  L.eq_refl(c)

# The frames' equations still to visit
# ------------------------------------

def frs(cs: List<&2, ST.TF>, +good: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{ST.TF{v, r}, ct}:
      SV.band(L.subl(r, good), frs(ct, good))

def ne_sub(b: Bool, +j: Nat, +rest: List<&2, Nat>, +ys: List<&2, Nat>, hj: {SV.mem(j, ys) == True{} : Bool}, hr: {L.subl(rest, ys) == True{} : Bool}) -> {L.subl(ST.needs.ne(b, j, rest), ys) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      L.subl_con(j, rest, ys, hj, hr)

def no_sub(+e: Nat, +vm: List<&2, Maybe<&2, Nat>>, +x: Nat, m: Maybe<&2, Nat>, em: {ST.getm(vm, x) == m : Maybe<&2, Nat>}, +rest: List<&2, Nat>, hr: {L.subl(rest, ST.somes(vm)) == True{} : Bool}) -> {L.subl(ST.needs.of(e, m, rest), ST.somes(vm)) == True{} : Bool}:
  match m:
    case None{}:
      hr
    case Some{+j}:
      ne_sub(KA.nateq(j, e), j, rest, ST.somes(vm), L.some_mem(vm, x, j, em), hr)

# what e needs is matched to something
def needs_sub(+e: Nat, +vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> {L.subl(ST.needs.go(e, vm, xs), ST.somes(vm)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      no_sub(e, vm, x, ST.getm(vm, x), {==}, ST.needs.go(e, vm, t), needs_sub(e, vm, t))

def ne_len(b: Bool, +j: Nat, +rest: List<&2, Nat>) -> {KA.natle(SV.len(ST.needs.ne(b, j, rest)), 1n+SV.len(rest)) == True{} : Bool}:
  match b:
    case True{}:
      KA.natle_succ(SV.len(rest), SV.len(rest), KA.natle_refl(SV.len(rest)))
    case False{}:
      KA.natle_refl(1n+SV.len(rest))

def no_len(+e: Nat, m: Maybe<&2, Nat>, +rest: List<&2, Nat>) -> {KA.natle(SV.len(ST.needs.of(e, m, rest)), 1n+SV.len(rest)) == True{} : Bool}:
  match m:
    case None{}:
      KA.natle_succ(SV.len(rest), SV.len(rest), KA.natle_refl(SV.len(rest)))
    case Some{+j}:
      ne_len(KA.nateq(j, e), j, rest)

# e needs at most as many equations as it has variables
def needs_len(+e: Nat, +vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> {KA.natle(SV.len(ST.needs.go(e, vm, xs)), SV.len(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      KA.natle_trans(SV.len(ST.needs.go(e, vm, Con{x, t})), 1n+SV.len(ST.needs.go(e, vm, t)), 1n+SV.len(t), no_len(e, ST.getm(vm, x), ST.needs.go(e, vm, t)), needs_len(e, vm, t))

# The work left
# -------------
# wm: one step per root to come, per frame (its finish) and per equation it
# still has to visit, and for each equation not yet reached one push and
# one step per variable it uses.

def tll(xs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def uw(m: Maybe<&2, Nat>, a: List<&2, Nat>) -> Nat:
  match m:
    case None{}:
      1n+SV.len(a)
    case Some{x}:
      0n

def um(idx: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>) -> Nat:
  match idx:
    case Nil{}:
      0n
    case Con{m, t}:
      Nat.add(uw(m, ST.hdl(adj)), um(t, tll(adj)))

def flen(cs: List<&2, ST.TF>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{ST.TF{v, r}, t}:
      1n+Nat.add(SV.len(r), flen(t))

def wm(+adj: List<&2, List<&2, Nat>>, roots: List<&2, Nat>, s: ST.TS) -> Nat:
  match s:
    case ST.TS{c, idx, low, st, cs, out}:
      Nat.add(SV.len(roots), Nat.add(flen(cs), um(idx, adj)))

def hdl_nth(adj: List<&2, List<&2, Nat>>) -> {ST.hdl(adj) == ST.nthl(adj, 0n) : List<&2, Nat>}:
  match adj:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def nth_tll(adj: List<&2, List<&2, Nat>>, +j: Nat) -> {ST.nthl(adj, 1n+j) == ST.nthl(tll(adj), j) : List<&2, Nat>}:
  match adj:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# reaching w takes its share off the work left
def um_push(idx: List<&2, Maybe<&2, Nat>>, w: Nat, +adj: List<&2, List<&2, Nat>>, +c: Nat, e: {ST.getm(idx, w) == None{} : Maybe<&2, Nat>}, hl: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}) -> {um(idx, adj) == Nat.add(1n+SV.len(ST.nthl(adj, w)), um(ST.setm(idx, w, Some{c}), adj)) : Nat}:
  match idx w:
    case Nil{} w:
      absurd({um(Nil{}, adj) == Nat.add(1n+SV.len(ST.nthl(adj, w)), um(ST.setm(Nil{}, w, Some{c}), adj)) : Nat}, KA.ft(hl))
    case Con{+m, +t} 0n:
      %Equal.sym(Maybe<&2, Nat>, m, None{}, e) : {Nat.add(uw(_, ST.hdl(adj)), um(t, tll(adj))) == Nat.add(1n+SV.len(ST.nthl(adj, 0n)), um(t, tll(adj))) : Nat}
      %hdl_nth(adj) : {Nat.add(1n+SV.len(ST.hdl(adj)), um(t, tll(adj))) == Nat.add(1n+SV.len(_), um(t, tll(adj))) : Nat}
      {==}
    case Con{+m, +t} 1n++j:
      %Equal.sym(Nat, um(t, tll(adj)), Nat.add(1n+SV.len(ST.nthl(tll(adj), j)), um(ST.setm(t, j, Some{c}), tll(adj))), um_push(t, j, tll(adj), c, e, hl)) : {Nat.add(uw(m, ST.hdl(adj)), _) == Nat.add(1n+SV.len(ST.nthl(adj, 1n+j)), Nat.add(uw(m, ST.hdl(adj)), um(ST.setm(t, j, Some{c}), tll(adj)))) : Nat}
      %Equal.sym(List<&2, Nat>, ST.nthl(adj, 1n+j), ST.nthl(tll(adj), j), nth_tll(adj, j)) : {Nat.add(uw(m, ST.hdl(adj)), Nat.add(1n+SV.len(ST.nthl(tll(adj), j)), um(ST.setm(t, j, Some{c}), tll(adj)))) == Nat.add(1n+SV.len(_), Nat.add(uw(m, ST.hdl(adj)), um(ST.setm(t, j, Some{c}), tll(adj)))) : Nat}
      LN.add_swap(uw(m, ST.hdl(adj)), 1n+SV.len(ST.nthl(tll(adj), j)), um(ST.setm(t, j, Some{c}), tll(adj)))

def total_split(adj: List<&2, List<&2, Nat>>) -> {ST.total(adj) == Nat.add(SV.len(ST.hdl(adj)), ST.total(tll(adj))) : Nat}:
  match adj:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, ST.len(h), SV.len(h), len_sv(h)) : {Nat.add(_, ST.total(t)) == Nat.add(SV.len(h), ST.total(t)) : Nat}
      {==}

# at the start: at most one push per equation and one step per edge
def um_init(n: Nat, +adj: List<&2, List<&2, Nat>>) -> {KA.natle(um(ST.nones(n), adj), Nat.add(n, ST.total(adj))) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      +lh = SV.len(ST.hdl(adj))
      +tt = ST.total(tll(adj))
      %Equal.sym(Nat, ST.total(adj), Nat.add(lh, tt), total_split(adj)) : {KA.natle(Nat.add(lh, um(ST.nones(m), tll(adj))), Nat.add(m, _)) == True{} : Bool}
      %LN.add_swap(lh, m, tt) : {KA.natle(Nat.add(lh, um(ST.nones(m), tll(adj))), _) == True{} : Bool}
      KA.natle_add_mono(lh, um(ST.nones(m), tll(adj)), Nat.add(m, tt), um_init(m, tll(adj)))

def step1(+a: Nat, +x: Nat) -> {KA.natle(1n+Nat.add(a, x), Nat.add(a, 1n+x)) == True{} : Bool}:
  %LN.add_succ(a, x) : {KA.natle(1n+Nat.add(a, x), _) == True{} : Bool}
  KA.natle_refl(1n+Nat.add(a, x))

def ar_in(+a: Nat, +bb: Nat, +u: Nat, h: {KA.natle(a, bb) == True{} : Bool}) -> {KA.natle(Nat.add(1n+Nat.add(a, 0n), u), Nat.add(1n+bb, u)) == True{} : Bool}:
  %LN.add_zero(a) : {KA.natle(Nat.add(1n+_, u), Nat.add(1n+bb, u)) == True{} : Bool}
  KA.natle_add_rr(a, bb, u, h)

def ar_root(+lr: Nat, +a: Nat, +bb: Nat, +u: Nat, h: {KA.natle(a, bb) == True{} : Bool}) -> {KA.natle(1n+Nat.add(lr, Nat.add(1n+Nat.add(a, 0n), u)), 1n+Nat.add(lr, Nat.add(1n+bb, u))) == True{} : Bool}:
  KA.natle_add_mono(lr, Nat.add(1n+Nat.add(a, 0n), u), Nat.add(1n+bb, u), ar_in(a, bb, u, h))

def ar_edge(+lr: Nat, +f: Nat, +a: Nat, +bb: Nat, +u: Nat, h: {KA.natle(a, bb) == True{} : Bool}) -> {KA.natle(1n+Nat.add(lr, Nat.add(1n+Nat.add(a, 1n+f), u)), Nat.add(lr, Nat.add(2n+f, Nat.add(1n+bb, u)))) == True{} : Bool}:
  %NR.ring_eq([lr, f, a, bb, u], NR.NAdd{NR.NAdd{NR.NCst{3n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{1n}, NR.NVar{4n}}}}, NR.NVar{2n}}, NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}}, NR.NVar{4n}}}}, {==}) : {KA.natle(_, Nat.add(lr, Nat.add(2n+f, Nat.add(1n+bb, u)))) == True{} : Bool}
  %NR.ring_eq([lr, f, a, bb, u], NR.NAdd{NR.NAdd{NR.NCst{3n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{1n}, NR.NVar{4n}}}}, NR.NVar{3n}}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NAdd{NR.NCst{2n}, NR.NVar{1n}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}, NR.NVar{4n}}}}, {==}) : {KA.natle(NR.eval([lr, f, a, bb, u], NR.NAdd{NR.NAdd{NR.NCst{3n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{1n}, NR.NVar{4n}}}}, NR.NVar{2n}}), _) == True{} : Bool}
  KA.natle_add_mono(NR.eval([lr, f, a, bb, u], NR.NAdd{NR.NCst{3n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{1n}, NR.NVar{4n}}}}), a, bb, h)

# The invariant
# -------------
# R = st ++ the components found: distinct, with an index exactly when in
# R, inside good, and with the roots to come covering good; the call
# stack on st (segs), low links on st within [base, idx] (stok), st's
# bottom numbered base (lastok); frames visit only equations of good.

def tinv(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))))

def tinv_dist(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {SV.distinct(ST.app(st, ST.cats(out))) == True{} : Bool}:
  L.band_l(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)

def tinv_agree(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {agree(nq, idx, ST.app(st, ST.cats(out))) == True{} : Bool}:
  L.band_l(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h))

def tinv_ing(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {L.subl(ST.app(st, ST.cats(out)), good) == True{} : Bool}:
  L.band_l(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))

def tinv_cov(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))) == True{} : Bool}:
  L.band_l(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h))))

def tinv_rg(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {L.subl(roots, good) == True{} : Bool}:
  L.band_l(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))))

def tinv_mi(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {SV.eq(L.mlen(idx), nq) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h))))))

def tinv_ml(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {SV.eq(L.mlen(low), nq) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))))))

def tinv_segs(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {segs(cs, st) == True{} : Bool}:
  L.band_l(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), L.band_r(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h))))))))

def tinv_stok(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {stok(st, base, idx, low) == True{} : Bool}:
  L.band_l(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))), L.band_r(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), L.band_r(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))))))))

def tinv_last(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {lastok(st, idx, base) == True{} : Bool}:
  L.band_l(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)), L.band_r(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))), L.band_r(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), L.band_r(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h))))))))))

def tinv_bc(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {KA.natle(base, c) == True{} : Bool}:
  L.band_l(KA.natle(base, c), frs(cs, good), L.band_r(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)), L.band_r(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))), L.band_r(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), L.band_r(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))))))))))

def tinv_fr(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h: {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}) -> {frs(cs, good) == True{} : Bool}:
  L.band_r(KA.natle(base, c), frs(cs, good), L.band_r(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)), L.band_r(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))), L.band_r(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), L.band_r(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), L.band_r(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), L.band_r(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), L.band_r(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), L.band_r(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), L.band_r(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), L.band_r(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h)))))))))))

def tinv_mk(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +cs: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, h_dist: {SV.distinct(ST.app(st, ST.cats(out))) == True{} : Bool}, h_agree: {agree(nq, idx, ST.app(st, ST.cats(out))) == True{} : Bool}, h_ing: {L.subl(ST.app(st, ST.cats(out)), good) == True{} : Bool}, h_cov: {L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))) == True{} : Bool}, h_rg: {L.subl(roots, good) == True{} : Bool}, h_mi: {SV.eq(L.mlen(idx), nq) == True{} : Bool}, h_ml: {SV.eq(L.mlen(low), nq) == True{} : Bool}, h_segs: {segs(cs, st) == True{} : Bool}, h_stok: {stok(st, base, idx, low) == True{} : Bool}, h_last: {lastok(st, idx, base) == True{} : Bool}, h_bc: {KA.natle(base, c) == True{} : Bool}, h_fr: {frs(cs, good) == True{} : Bool}) -> {tinv(nq, good, base, roots, c, idx, low, st, cs, out) == True{} : Bool}:
  L.band_i(SV.distinct(ST.app(st, ST.cats(out))), SV.band(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))))), h_dist, L.band_i(agree(nq, idx, ST.app(st, ST.cats(out))), SV.band(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))))), h_agree, L.band_i(L.subl(ST.app(st, ST.cats(out)), good), SV.band(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))))), h_ing, L.band_i(L.subl(good, ST.app(roots, ST.app(st, ST.cats(out)))), SV.band(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))))), h_cov, L.band_i(L.subl(roots, good), SV.band(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))))), h_rg, L.band_i(SV.eq(L.mlen(idx), nq), SV.band(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))))), h_mi, L.band_i(SV.eq(L.mlen(low), nq), SV.band(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))))), h_ml, L.band_i(segs(cs, st), SV.band(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)))), h_segs, L.band_i(stok(st, base, idx, low), SV.band(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good))), h_stok, L.band_i(lastok(st, idx, base), SV.band(KA.natle(base, c), frs(cs, good)), h_last, L.band_i(KA.natle(base, c), frs(cs, good), h_bc, h_fr)))))))))))

def tinvs(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, s: ST.TS) -> Bool:
  match s:
    case ST.TS{c, idx, low, st, cs, out}:
      tinv(nq, good, base, roots, c, idx, low, st, cs, out)

# a step's outcome: the invariant, and less work left than w0
def stepok(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +s: ST.TS, +w0: Nat) -> Bool:
  SV.band(tinvs(nq, good, base, roots, s), KA.natle(1n+wm(adj, roots, s), w0))

def so_inv(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +s: ST.TS, +w0: Nat, h: {stepok(adj, nq, good, base, roots, s, w0) == True{} : Bool}) -> {tinvs(nq, good, base, roots, s) == True{} : Bool}:
  L.band_l(tinvs(nq, good, base, roots, s), KA.natle(1n+wm(adj, roots, s), w0), h)

def so_w(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +s: ST.TS, +w0: Nat, h: {stepok(adj, nq, good, base, roots, s, w0) == True{} : Bool}) -> {KA.natle(1n+wm(adj, roots, s), w0) == True{} : Bool}:
  L.band_r(tinvs(nq, good, base, roots, s), KA.natle(1n+wm(adj, roots, s), w0), h)

# A root
# ------

def w_root(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +r: Nat, +rt: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, e: {ST.getm(idx, r) == None{} : Maybe<&2, Nat>}, hl: {KA.natle(1n+r, L.mlen(idx)) == True{} : Bool}) -> {KA.natle(1n+wm(adj, rt, ST.TS{1n+c, ST.setm(idx, r, Some{c}), ST.setm(low, r, Some{c}), Con{r, Nil{}}, Con{ST.TF{r, ST.needs(adj, em, r)}, Nil{}}, out}), wm(adj, Con{r, rt}, ST.TS{c, idx, low, Nil{}, Nil{}, out})) == True{} : Bool}:
  +u2 = um(ST.setm(idx, r, Some{c}), adj)
  +a = SV.len(ST.needs(adj, em, r))
  +bb = SV.len(ST.nthl(adj, r))
  %Equal.sym(Nat, um(idx, adj), Nat.add(1n+bb, u2), um_push(idx, r, adj, c, e, hl)) : {KA.natle(1n+Nat.add(SV.len(rt), Nat.add(1n+Nat.add(a, 0n), u2)), 1n+Nat.add(SV.len(rt), _)) == True{} : Bool}
  ar_root(SV.len(rt), a, bb, u2, needs_len(r, em, ST.nthl(adj, r)))

# a new root r: pushed, numbered c, the new base
def root_none(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +r: Nat, +rt: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, +e: {ST.getm(idx, r) == None{} : Maybe<&2, Nat>}, +h: {tinv(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out) == True{} : Bool}) -> {stepok(adj, nq, good, c, rt, ST.tpush(adj, em, r, ST.TS{c, idx, low, Nil{}, Nil{}, out}), wm(adj, Con{r, rt}, ST.TS{c, idx, low, Nil{}, Nil{}, out})) == True{} : Bool}:
  +cc = ST.cats(out)
  +ns = ST.needs(adj, em, r)
  +i2 = ST.setm(idx, r, Some{c})
  +l2 = ST.setm(low, r, Some{c})
  +s2 = {ST.TS{1n+c, i2, l2, Con{r, Nil{}}, Con{ST.TF{r, ns}, Nil{}}, out} : ST.TS}
  +hrg = tinv_rg(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hrm = L.subl_hd(r, rt, good, hrg)
  +hlt = lt_nq(r, good, nq, hrm, hb)
  +hmi = tinv_mi(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hml = tinv_ml(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hli = lt_ml(r, idx, nq, hmi, hlt)
  +hll = lt_ml(r, low, nq, hml, hlt)
  +hag = tinv_agree(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hn = notin_of(idx, cc, nq, r, hlt, hag, e)
  +hcv = tinv_cov(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hi = tinv_mk(nq, good, c, rt, 1n+c, i2, l2, Con{r, Nil{}}, Con{ST.TF{r, ns}, Nil{}}, out, L.dist_con(r, cc, hn, tinv_dist(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)), agree_push(nq, idx, cc, r, c, hli, hag), L.subl_con(r, cc, good, hrm, tinv_ing(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)), L.subl_trans(good, Con{r, ST.app(rt, cc)}, ST.app(rt, Con{r, cc}), hcv, L.subl_con(r, ST.app(rt, cc), ST.app(rt, Con{r, cc}), mem_app_r(r, rt, Con{r, cc}, L.mem_hd(r, cc)), app_mono(rt, cc, Con{r, cc}, L.subl_cons_r(cc, r, cc, L.subl_refl(cc))))), L.subl_tl(r, rt, good, hrg), ml_set(idx, r, Some{c}, nq, hmi), ml_set(low, r, Some{c}, nq, hml), segs_push(r, ns, Nil{}, Nil{}, {==}), stok_push(Nil{}, c, c, idx, low, r, {==}, KA.natle_refl(c), hli, hll, {==}), last_one(idx, r, c, hli), KA.natle_succ(c, c, KA.natle_refl(c)), L.band_i(L.subl(ns, good), True{}, L.subl_trans(ns, ST.somes(em), good, needs_sub(r, em, ST.nthl(adj, r)), hs), {==}))
  L.band_i(tinvs(nq, good, c, rt, s2), KA.natle(1n+wm(adj, rt, s2), wm(adj, Con{r, rt}, ST.TS{c, idx, low, Nil{}, Nil{}, out})), hi, w_root(adj, em, r, rt, c, idx, low, out, e, hli))

# a root already reached: skipped
def root_some(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +r: Nat, +rt: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, +hb: {SV.below(good, nq) == True{} : Bool}, +i: Nat, e: {ST.getm(idx, r) == Some{i} : Maybe<&2, Nat>}, +h: {tinv(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out) == True{} : Bool}) -> {stepok(adj, nq, good, c, rt, ST.TS{c, idx, low, Nil{}, Nil{}, out}, wm(adj, Con{r, rt}, ST.TS{c, idx, low, Nil{}, Nil{}, out})) == True{} : Bool}:
  +cc = ST.cats(out)
  +s = {ST.TS{c, idx, low, Nil{}, Nil{}, out} : ST.TS}
  +hrg = tinv_rg(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hlt = lt_nq(r, good, nq, L.subl_hd(r, rt, good, hrg), hb)
  +hag = tinv_agree(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h)
  +hrc = in_of(idx, cc, nq, r, i, hlt, hag, e)
  +hi = tinv_mk(nq, good, c, rt, c, idx, low, Nil{}, Nil{}, out, tinv_dist(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h), hag, tinv_ing(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h), L.subl_trans(good, Con{r, ST.app(rt, cc)}, ST.app(rt, cc), tinv_cov(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h), L.subl_con(r, ST.app(rt, cc), ST.app(rt, cc), mem_app_r(r, rt, cc, hrc), L.subl_refl(ST.app(rt, cc)))), L.subl_tl(r, rt, good, hrg), tinv_mi(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h), tinv_ml(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out, h), {==}, {==}, {==}, KA.natle_refl(c), {==})
  L.band_i(tinvs(nq, good, c, rt, s), KA.natle(1n+wm(adj, rt, s), wm(adj, Con{r, rt}, s)), hi, KA.natle_refl(1n+wm(adj, rt, s)))

def root_m(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +r: Nat, +rt: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, +h: {tinv(nq, good, base, Con{r, rt}, c, idx, low, Nil{}, Nil{}, out) == True{} : Bool}, m: Maybe<&2, Nat>, e: {ST.getm(idx, r) == m : Maybe<&2, Nat>}) -> {stepok(adj, nq, good, c, rt, ST.troot(m, adj, em, r, ST.TS{c, idx, low, Nil{}, Nil{}, out}), wm(adj, Con{r, rt}, ST.TS{c, idx, low, Nil{}, Nil{}, out})) == True{} : Bool}:
  match m:
    case None{}:
      root_none(adj, em, nq, good, base, r, rt, c, idx, low, out, hs, hb, e, h)
    case Some{+i}:
      root_some(adj, nq, good, base, r, rt, c, idx, low, out, hb, i, e, h)

def root_go(st: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +r: Nat, +rt: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, h: {tinv(nq, good, base, Con{r, rt}, c, idx, low, st, Nil{}, out) == True{} : Bool}) -> {stepok(adj, nq, good, c, rt, ST.troot(ST.getm(idx, r), adj, em, r, ST.TS{c, idx, low, st, Nil{}, out}), wm(adj, Con{r, rt}, ST.TS{c, idx, low, st, Nil{}, out})) == True{} : Bool}:
  match st:
    case Nil{}:
      root_m(adj, em, nq, good, base, r, rt, c, idx, low, out, hs, hb, h, ST.getm(idx, r), {==})
    case Con{+x, +t}:
      absurd({stepok(adj, nq, good, c, rt, ST.troot(ST.getm(idx, r), adj, em, r, ST.TS{c, idx, low, Con{x, t}, Nil{}, out}), wm(adj, Con{r, rt}, ST.TS{c, idx, low, Con{x, t}, Nil{}, out})) == True{} : Bool}, KA.ft(tinv_segs(nq, good, base, Con{r, rt}, c, idx, low, Con{x, t}, Nil{}, out, h)))

# An edge
# -------
# The top frame v visits w: unreached (push it), on the stack (v's low
# drops to w's index), or in a finished component (nothing).

def w_edge(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +w: Nat, +rest: List<&2, Nat>, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, e: {ST.getm(idx, w) == None{} : Maybe<&2, Nat>}, hl: {KA.natle(1n+w, L.mlen(idx)) == True{} : Bool}) -> {KA.natle(1n+wm(adj, roots, ST.TS{1n+c, ST.setm(idx, w, Some{c}), ST.setm(low, w, Some{c}), Con{w, st}, Con{ST.TF{w, ST.needs(adj, em, w)}, Con{ST.TF{v, rest}, ct}}, out}), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})) == True{} : Bool}:
  +u2 = um(ST.setm(idx, w, Some{c}), adj)
  +a = SV.len(ST.needs(adj, em, w))
  +bb = SV.len(ST.nthl(adj, w))
  +f = Nat.add(SV.len(rest), flen(ct))
  +lr = SV.len(roots)
  %Equal.sym(Nat, um(idx, adj), Nat.add(1n+bb, u2), um_push(idx, w, adj, c, e, hl)) : {KA.natle(1n+Nat.add(lr, Nat.add(1n+Nat.add(a, 1n+f), u2)), Nat.add(lr, Nat.add(2n+f, _))) == True{} : Bool}
  ar_edge(lr, f, a, bb, u2, needs_len(w, em, ST.nthl(adj, w)))

# w unreached: pushed, numbered c
def edge_none(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +w: Nat, +rest: List<&2, Nat>, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out) == True{} : Bool}, +e: {ST.getm(idx, w) == None{} : Maybe<&2, Nat>}) -> {stepok(adj, nq, good, base, roots, ST.tpush(adj, em, w, ST.TS{c, idx, low, st, Con{ST.TF{v, rest}, ct}, out}), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})) == True{} : Bool}:
  +cc = ST.cats(out)
  +rr = ST.app(st, cc)
  +cs0 = {Con{ST.TF{v, Con{w, rest}}, ct} : List<&2, ST.TF>}
  +cs1 = {Con{ST.TF{v, rest}, ct} : List<&2, ST.TF>}
  +ns = ST.needs(adj, em, w)
  +i2 = ST.setm(idx, w, Some{c})
  +l2 = ST.setm(low, w, Some{c})
  +s2 = {ST.TS{1n+c, i2, l2, Con{w, st}, Con{ST.TF{w, ns}, cs1}, out} : ST.TS}
  +hfr = tinv_fr(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hwr = L.band_l(L.subl(Con{w, rest}, good), frs(ct, good), hfr)
  +hwg = L.subl_hd(w, rest, good, hwr)
  +hfr1 = L.band_i(L.subl(rest, good), frs(ct, good), L.subl_tl(w, rest, good, hwr), L.band_r(L.subl(Con{w, rest}, good), frs(ct, good), hfr))
  +hsg = tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hv = L.band_l(SV.mem(v, st), segs(ct, aft(v, st)), hsg)
  +hlt = lt_nq(w, good, nq, hwg, hb)
  +hmi = tinv_mi(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hml = tinv_ml(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hli = lt_ml(w, idx, nq, hmi, hlt)
  +hll = lt_ml(w, low, nq, hml, hlt)
  +hag = tinv_agree(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hn = notin_of(idx, rr, nq, w, hlt, hag, e)
  +hns = notin_app_l(w, st, cc, hn)
  +hbc = tinv_bc(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hi = tinv_mk(nq, good, base, roots, 1n+c, i2, l2, Con{w, st}, Con{ST.TF{w, ns}, cs1}, out, L.dist_con(w, rr, hn, tinv_dist(nq, good, base, roots, c, idx, low, st, cs0, out, h)), agree_push(nq, idx, rr, w, c, hli, hag), L.subl_con(w, rr, good, hwg, tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h)), L.subl_trans(good, ST.app(roots, rr), ST.app(roots, Con{w, rr}), tinv_cov(nq, good, base, roots, c, idx, low, st, cs0, out, h), app_mono(roots, rr, Con{w, rr}, L.subl_cons_r(rr, w, rr, L.subl_refl(rr)))), tinv_rg(nq, good, base, roots, c, idx, low, st, cs0, out, h), ml_set(idx, w, Some{c}, nq, hmi), ml_set(low, w, Some{c}, nq, hml), segs_push(w, ns, cs1, st, hsg), stok_push(st, base, c, idx, low, w, hns, hbc, hli, hll, tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h)), lastok_cons(w, st, v, i2, base, hv, lastok_set(st, idx, base, w, Some{c}, hns, tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h))), KA.natle_succ(base, c, hbc), L.band_i(L.subl(ns, good), frs(cs1, good), L.subl_trans(ns, ST.somes(em), good, needs_sub(w, em, ST.nthl(adj, w)), hs), hfr1))
  L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), wm(adj, roots, ST.TS{c, idx, low, st, cs0, out})), hi, w_edge(adj, em, roots, c, idx, low, st, v, w, rest, ct, out, e, hli))

# w reached: v's low drops to w's index if w is on the stack
def edge_on(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +w: Nat, +rest: List<&2, Nat>, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +hb: {SV.below(good, nq) == True{} : Bool}, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out) == True{} : Bool}, +iw: Nat, e: {ST.getm(idx, w) == Some{iw} : Maybe<&2, Nat>}, on: Bool, eo: {ST.mem(w, st) == on : Bool}) -> {stepok(adj, nq, good, base, roots, ST.tedge.on(on, v, iw, ST.TS{c, idx, low, st, Con{ST.TF{v, rest}, ct}, out}), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})) == True{} : Bool}:
  match on:
    case True{}:
      +cc = ST.cats(out)
      +cs0 = {Con{ST.TF{v, Con{w, rest}}, ct} : List<&2, ST.TF>}
      +cs1 = {Con{ST.TF{v, rest}, ct} : List<&2, ST.TF>}
      +l2 = ST.setm(low, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), iw)})
      +s2 = {ST.TS{c, idx, l2, st, cs1, out} : ST.TS}
      +hfr = tinv_fr(nq, good, base, roots, c, idx, low, st, cs0, out, h)
      +hwr = L.band_l(L.subl(Con{w, rest}, good), frs(ct, good), hfr)
      +hfr1 = L.band_i(L.subl(rest, good), frs(ct, good), L.subl_tl(w, rest, good, hwr), L.band_r(L.subl(Con{w, rest}, good), frs(ct, good), hfr))
      +hsk = tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h)
      +hml = tinv_ml(nq, good, base, roots, c, idx, low, st, cs0, out, h)
      +hbw = base_le(base, idx, low, w, iw, e, stok_at(st, base, idx, low, w, mem_of_st(w, st, eo), hsk))
      +hbl = st_below(st, cc, good, nq, low, tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h), hb, hml)
      +hi = tinv_mk(nq, good, base, roots, c, idx, l2, st, cs1, out, tinv_dist(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_agree(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_cov(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_rg(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_mi(nq, good, base, roots, c, idx, low, st, cs0, out, h), ml_set(low, v, Some{ST.nmin(ST.look.of(ST.getm(low, v)), iw)}, nq, hml), tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h), stok_low(st, base, idx, low, v, iw, hbw, hbl, hsk), tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_bc(nq, good, base, roots, c, idx, low, st, cs0, out, h), hfr1)
      L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), wm(adj, roots, ST.TS{c, idx, low, st, cs0, out})), hi, step1(SV.len(roots), Nat.add(1n+Nat.add(SV.len(rest), flen(ct)), um(idx, adj))))
    case False{}:
      +cs0 = {Con{ST.TF{v, Con{w, rest}}, ct} : List<&2, ST.TF>}
      +cs1 = {Con{ST.TF{v, rest}, ct} : List<&2, ST.TF>}
      +s2 = {ST.TS{c, idx, low, st, cs1, out} : ST.TS}
      +hfr = tinv_fr(nq, good, base, roots, c, idx, low, st, cs0, out, h)
      +hwr = L.band_l(L.subl(Con{w, rest}, good), frs(ct, good), hfr)
      +hfr1 = L.band_i(L.subl(rest, good), frs(ct, good), L.subl_tl(w, rest, good, hwr), L.band_r(L.subl(Con{w, rest}, good), frs(ct, good), hfr))
      +hi = tinv_mk(nq, good, base, roots, c, idx, low, st, cs1, out, tinv_dist(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_agree(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_cov(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_rg(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_mi(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ml(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_bc(nq, good, base, roots, c, idx, low, st, cs0, out, h), hfr1)
      L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), wm(adj, roots, ST.TS{c, idx, low, st, cs0, out})), hi, step1(SV.len(roots), Nat.add(1n+Nat.add(SV.len(rest), flen(ct)), um(idx, adj))))

def edge_m(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +w: Nat, +rest: List<&2, Nat>, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out) == True{} : Bool}, m: Maybe<&2, Nat>, e: {ST.getm(idx, w) == m : Maybe<&2, Nat>}) -> {stepok(adj, nq, good, base, roots, ST.tedge(m, ST.mem(w, st), adj, em, v, w, ST.TS{c, idx, low, st, Con{ST.TF{v, rest}, ct}, out}), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})) == True{} : Bool}:
  match m:
    case None{}:
      edge_none(adj, em, nq, good, base, roots, c, idx, low, st, v, w, rest, ct, out, hs, hb, h, e)
    case Some{+iw}:
      edge_on(adj, nq, good, base, roots, c, idx, low, st, v, w, rest, ct, out, hb, h, iw, e, ST.mem(w, st), {==})

# A frame finishes
# ----------------
# v (its frame done) is a root of a component when low = idx: st is popped
# down to v. Then the frame below, if any, takes v's low.

def rg_back(+st: List<&2, Nat>, +b: Bool, +v: Nat, +cc: List<&2, Nat>) -> {L.subl(ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)), ST.app(st, cc)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)), ST.rev.go(st, ST.app(Nil{}, cc)), rgid(st, b, v, Nil{}, cc)) : {L.subl(_, ST.app(st, cc)) == True{} : Bool}
  rg_app(st, cc)

def rg_fwd(+st: List<&2, Nat>, +b: Bool, +v: Nat, +cc: List<&2, Nat>) -> {L.subl(ST.app(st, cc), ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)), ST.rev.go(st, ST.app(Nil{}, cc)), rgid(st, b, v, Nil{}, cc)) : {L.subl(ST.app(st, cc), _) == True{} : Bool}
  app_rg(st, cc)

def pop_sub1(+st: List<&2, Nat>, +b: Bool, +v: Nat, +cc: List<&2, Nat>) -> {L.subl(ST.app(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)), ST.app(st, cc)) == True{} : Bool}:
  +s2 = after(st, b, v)
  +x = ST.app(upto(st, b, v, Nil{}), cc)
  L.subl_trans(ST.app(s2, x), ST.rev.go(s2, x), ST.app(st, cc), app_rg(s2, x), rg_back(st, b, v, cc))

def pop_sub2(+st: List<&2, Nat>, +b: Bool, +v: Nat, +cc: List<&2, Nat>) -> {L.subl(ST.app(st, cc), ST.app(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc))) == True{} : Bool}:
  +s2 = after(st, b, v)
  +x = ST.app(upto(st, b, v, Nil{}), cc)
  L.subl_trans(ST.app(st, cc), ST.rev.go(s2, x), ST.app(s2, x), rg_fwd(st, b, v, cc), rg_app(s2, x))

def pop_dist(+st: List<&2, Nat>, +b: Bool, +v: Nat, +cc: List<&2, Nat>, h: {SV.distinct(ST.app(st, cc)) == True{} : Bool}) -> {SV.distinct(ST.app(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc))) == True{} : Bool}:
  %dist_rg(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)) : {_ == True{} : Bool}
  %Equal.sym(List<&2, Nat>, ST.rev.go(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc)), ST.rev.go(st, ST.app(Nil{}, cc)), rgid(st, b, v, Nil{}, cc)) : {SV.distinct(_) == True{} : Bool}
  %Equal.sym(Bool, SV.distinct(ST.rev.go(st, cc)), SV.distinct(ST.app(st, cc)), dist_rg(st, cc)) : {_ == True{} : Bool}
  h

# st popped down to v (v's frame done)
def pop_inv(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out) == True{} : Bool}) -> {tinv(nq, good, base, roots, c, idx, low, aft(v, st), ct, Con{upto(st, KA.nateq(ST.hd(st), v), v, Nil{}), out}) == True{} : Bool}:
  +b = KA.nateq(ST.hd(st), v)
  +cs0 = {Con{ST.TF{v, Nil{}}, ct} : List<&2, ST.TF>}
  +cc = ST.cats(out)
  +rr = ST.app(st, cc)
  +r2 = ST.app(after(st, b, v), ST.app(upto(st, b, v, Nil{}), cc))
  +hs1 = pop_sub1(st, b, v, cc)
  +hs2 = pop_sub2(st, b, v, cc)
  +hsg = tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  tinv_mk(nq, good, base, roots, c, idx, low, aft(v, st), ct, Con{upto(st, b, v, Nil{}), out}, pop_dist(st, b, v, cc, tinv_dist(nq, good, base, roots, c, idx, low, st, cs0, out, h)), agree_eqv(nq, idx, rr, r2, hs2, hs1, tinv_agree(nq, good, base, roots, c, idx, low, st, cs0, out, h)), L.subl_trans(r2, rr, good, hs1, tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h)), L.subl_trans(good, ST.app(roots, rr), ST.app(roots, r2), tinv_cov(nq, good, base, roots, c, idx, low, st, cs0, out, h), app_mono(roots, rr, r2, hs2)), tinv_rg(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_mi(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ml(nq, good, base, roots, c, idx, low, st, cs0, out, h), L.band_r(SV.mem(v, st), segs(ct, aft(v, st)), hsg), stok_after(st, b, v, base, idx, low, tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h)), lastok_after(st, b, v, idx, base, tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h)), tinv_bc(nq, good, base, roots, c, idx, low, st, cs0, out, h), L.band_r(L.subl(Nil{}, good), frs(ct, good), tinv_fr(nq, good, base, roots, c, idx, low, st, cs0, out, h)))

# the top frame u's low drops to x >= base
def low_inv(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +u: Nat, +r2: List<&2, Nat>, +ct2: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +x: Nat, hx: {KA.natle(base, x) == True{} : Bool}, hb: {SV.below(good, nq) == True{} : Bool}, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{u, r2}, ct2}, out) == True{} : Bool}) -> {tinv(nq, good, base, roots, c, idx, ST.setm(low, u, Some{ST.nmin(ST.look.of(ST.getm(low, u)), x)}), st, Con{ST.TF{u, r2}, ct2}, out) == True{} : Bool}:
  +cs = {Con{ST.TF{u, r2}, ct2} : List<&2, ST.TF>}
  +hml = tinv_ml(nq, good, base, roots, c, idx, low, st, cs, out, h)
  +hbl = st_below(st, ST.cats(out), good, nq, low, tinv_ing(nq, good, base, roots, c, idx, low, st, cs, out, h), hb, hml)
  tinv_mk(nq, good, base, roots, c, idx, ST.setm(low, u, Some{ST.nmin(ST.look.of(ST.getm(low, u)), x)}), st, cs, out, tinv_dist(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_agree(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_ing(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_cov(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_rg(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_mi(nq, good, base, roots, c, idx, low, st, cs, out, h), ml_set(low, u, Some{ST.nmin(ST.look.of(ST.getm(low, u)), x)}, nq, hml), tinv_segs(nq, good, base, roots, c, idx, low, st, cs, out, h), stok_low(st, base, idx, low, u, x, hx, hbl, tinv_stok(nq, good, base, roots, c, idx, low, st, cs, out, h)), tinv_last(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_bc(nq, good, base, roots, c, idx, low, st, cs, out, h), tinv_fr(nq, good, base, roots, c, idx, low, st, cs, out, h))

# v's frame done without popping: the frame below is next on st
def keep_inv(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +u: Nat, +r2: List<&2, Nat>, +ct2: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Nil{}}, Con{ST.TF{u, r2}, ct2}}, out) == True{} : Bool}) -> {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{u, r2}, ct2}, out) == True{} : Bool}:
  +ct = {Con{ST.TF{u, r2}, ct2} : List<&2, ST.TF>}
  +cs0 = {Con{ST.TF{v, Nil{}}, ct} : List<&2, ST.TF>}
  +hsg = tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hd = tinv_dist(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  tinv_mk(nq, good, base, roots, c, idx, low, st, ct, out, hd, tinv_agree(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ing(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_cov(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_rg(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_mi(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_ml(nq, good, base, roots, c, idx, low, st, cs0, out, h), segs_keep(v, u, r2, ct2, st, dist_app_l(st, ST.cats(out), hd), L.band_l(SV.mem(v, st), segs(ct, aft(v, st)), hsg), L.band_r(SV.mem(v, st), segs(ct, aft(v, st)), hsg)), tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h), tinv_bc(nq, good, base, roots, c, idx, low, st, cs0, out, h), L.band_r(L.subl(Nil{}, good), frs(ct, good), tinv_fr(nq, good, base, roots, c, idx, low, st, cs0, out, h)))

def le_of_eq(+iv: Nat, +base: Nat, +lv: Nat, e: {iv == base : Nat}, h: {KA.natle(base, lv) == True{} : Bool}) -> {KA.natle(iv, lv) == True{} : Bool}:
  %Equal.sym(Nat, iv, base, e) : {KA.natle(_, lv) == True{} : Bool}
  h

# the bottom frame (a root) always has low = idx = base
def root_eq(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +out: List<&2, List<&2, Nat>>, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Nil{}}, Nil{}}, out) == True{} : Bool}) -> {KA.nateq(ST.look.of(ST.getm(low, v)), ST.look.of(ST.getm(idx, v))) == True{} : Bool}:
  +cs0 = {Con{ST.TF{v, Nil{}}, Nil{}} : List<&2, ST.TF>}
  +lv = ST.look.of(ST.getm(low, v))
  +iv = ST.look.of(ST.getm(idx, v))
  +hsg = tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h)
  +hv = L.band_l(SV.mem(v, st), segs(Nil{}, aft(v, st)), hsg)
  +hok = stok_at(st, base, idx, low, v, hv, tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h))
  +hib = L.eq_ok(iv, base, lastok_root(st, v, idx, base, tinv_last(nq, good, base, roots, c, idx, low, st, cs0, out, h), hv, L.band_r(SV.mem(v, st), segs(Nil{}, aft(v, st)), hsg)))
  KA.nateq_of(lv, iv, KA.natle_antisym(lv, iv, L.band_r(KA.natle(base, lv), KA.natle(lv, iv), hok), le_of_eq(iv, base, lv, hib, L.band_l(KA.natle(base, lv), KA.natle(lv, iv), hok))))

# base <= v's low (v the top frame)
def base_lv(+nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +ct: List<&2, ST.TF>, +out: List<&2, List<&2, Nat>>, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out) == True{} : Bool}) -> {KA.natle(base, ST.look.of(ST.getm(low, v))) == True{} : Bool}:
  +cs0 = {Con{ST.TF{v, Nil{}}, ct} : List<&2, ST.TF>}
  +lv = ST.look.of(ST.getm(low, v))
  +hok = stok_at(st, base, idx, low, v, L.band_l(SV.mem(v, st), segs(ct, aft(v, st)), tinv_segs(nq, good, base, roots, c, idx, low, st, cs0, out, h)), tinv_stok(nq, good, base, roots, c, idx, low, st, cs0, out, h))
  L.band_l(KA.natle(base, lv), KA.natle(lv, ST.look.of(ST.getm(idx, v))), hok)

def fin_go(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +roots: List<&2, Nat>, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +st: List<&2, Nat>, +v: Nat, +out: List<&2, List<&2, Nat>>, +hb: {SV.below(good, nq) == True{} : Bool}, b: Bool, ct: List<&2, ST.TF>, e: {KA.nateq(ST.look.of(ST.getm(low, v)), ST.look.of(ST.getm(idx, v))) == b : Bool}, +h: {tinv(nq, good, base, roots, c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out) == True{} : Bool}) -> {stepok(adj, nq, good, base, roots, ST.tfin.up(ct, ST.look.of(ST.getm(low, v)), ST.tfin.root(b, v, ST.TS{c, idx, low, st, ct, out})), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out})) == True{} : Bool}:
  match b ct:
    case True{} Nil{}:
      +bb = KA.nateq(ST.hd(st), v)
      +s2 = {ST.TS{c, idx, low, after(st, bb, v), Nil{}, Con{upto(st, bb, v, Nil{}), out}} : ST.TS}
      +w0 = wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, Nil{}}, out})
      %Equal.sym(ST.TS, ST.tpop(st, bb, v, Nil{}, c, idx, low, Nil{}, out), s2, tpop_eq(st, bb, v, Nil{}, c, idx, low, Nil{}, out)) : {stepok(adj, nq, good, base, roots, _, w0) == True{} : Bool}
      L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), w0), pop_inv(nq, good, base, roots, c, idx, low, st, v, Nil{}, out, h), step1(SV.len(roots), Nat.add(0n, um(idx, adj))))
    case True{} Con{ST.TF{+u, +r2}, +ct2}:
      +bb = KA.nateq(ST.hd(st), v)
      +ctt = {Con{ST.TF{u, r2}, ct2} : List<&2, ST.TF>}
      +lv = ST.look.of(ST.getm(low, v))
      +sp = {ST.TS{c, idx, low, after(st, bb, v), ctt, Con{upto(st, bb, v, Nil{}), out}} : ST.TS}
      +s2 = ST.tlow(u, lv, sp)
      +w0 = wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, ctt}, out})
      %Equal.sym(ST.TS, ST.tpop(st, bb, v, Nil{}, c, idx, low, ctt, out), sp, tpop_eq(st, bb, v, Nil{}, c, idx, low, ctt, out)) : {stepok(adj, nq, good, base, roots, ST.tlow(u, lv, _), w0) == True{} : Bool}
      L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), w0), low_inv(nq, good, base, roots, c, idx, low, after(st, bb, v), u, r2, ct2, Con{upto(st, bb, v, Nil{}), out}, lv, base_lv(nq, good, base, roots, c, idx, low, st, v, ctt, out, h), hb, pop_inv(nq, good, base, roots, c, idx, low, st, v, ctt, out, h)), step1(SV.len(roots), Nat.add(flen(ctt), um(idx, adj))))
    case False{} Nil{}:
      absurd({stepok(adj, nq, good, base, roots, ST.tfin.up(Nil{}, ST.look.of(ST.getm(low, v)), ST.tfin.root(False{}, v, ST.TS{c, idx, low, st, Nil{}, out})), wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, Nil{}}, out})) == True{} : Bool}, L.tnf(KA.nateq(ST.look.of(ST.getm(low, v)), ST.look.of(ST.getm(idx, v))), root_eq(nq, good, base, roots, c, idx, low, st, v, out, h), e))
    case False{} Con{ST.TF{+u, +r2}, +ct2}:
      +ctt = {Con{ST.TF{u, r2}, ct2} : List<&2, ST.TF>}
      +lv = ST.look.of(ST.getm(low, v))
      +s2 = ST.tlow(u, lv, ST.TS{c, idx, low, st, ctt, out})
      +w0 = wm(adj, roots, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, ctt}, out})
      L.band_i(tinvs(nq, good, base, roots, s2), KA.natle(1n+wm(adj, roots, s2), w0), low_inv(nq, good, base, roots, c, idx, low, st, u, r2, ct2, out, lv, base_lv(nq, good, base, roots, c, idx, low, st, v, ctt, out, h), hb, keep_inv(nq, good, base, roots, c, idx, low, st, v, u, r2, ct2, out, h)), step1(SV.len(roots), Nat.add(flen(ctt), um(idx, adj))))

# The walk
# --------

def tend2(+good: List<&2, Nat>, +out: List<&2, List<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.cats(out)), SV.band(L.subl(good, ST.cats(out)), L.subl(ST.cats(out), good)))

# the components found partition good
def tend(+good: List<&2, Nat>, s: ST.TS) -> Bool:
  match s:
    case ST.TS{c, idx, low, st, cs, out}:
      tend2(good, out)

def tdone(st: List<&2, Nat>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +c: Nat, +idx: List<&2, Maybe<&2, Nat>>, +low: List<&2, Maybe<&2, Nat>>, +out: List<&2, List<&2, Nat>>, +h: {tinv(nq, good, base, Nil{}, c, idx, low, st, Nil{}, out) == True{} : Bool}) -> {tend(good, ST.TS{c, idx, low, st, Nil{}, out}) == True{} : Bool}:
  match st:
    case Nil{}:
      L.band_i(SV.distinct(ST.cats(out)), SV.band(L.subl(good, ST.cats(out)), L.subl(ST.cats(out), good)), tinv_dist(nq, good, base, Nil{}, c, idx, low, Nil{}, Nil{}, out, h), L.band_i(L.subl(good, ST.cats(out)), L.subl(ST.cats(out), good), tinv_cov(nq, good, base, Nil{}, c, idx, low, Nil{}, Nil{}, out, h), tinv_ing(nq, good, base, Nil{}, c, idx, low, Nil{}, Nil{}, out, h)))
    case Con{+x, +t}:
      absurd({tend(good, ST.TS{c, idx, low, Con{x, t}, Nil{}, out}) == True{} : Bool}, KA.ft(tinv_segs(nq, good, base, Nil{}, c, idx, low, Con{x, t}, Nil{}, out, h)))

# from a state meeting the invariant, with more fuel than work left, the
# walk ends with the components partitioning good
def twalk(f: Nat, roots: List<&2, Nat>, s: ST.TS, +adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +nq: Nat, +good: List<&2, Nat>, +base: Nat, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, h: {tinvs(nq, good, base, roots, s) == True{} : Bool}, hw: {KA.natle(1n+wm(adj, roots, s), f) == True{} : Bool}) -> {tend(good, ST.tarjan(f, adj, em, roots, s)) == True{} : Bool}:
  match f roots s:
    case 0n +roots +s:
      absurd({tend(good, ST.tarjan(0n, adj, em, roots, s)) == True{} : Bool}, KA.ft(hw))
    case 1n++g Nil{} ST.TS{+c, +idx, +low, +st, Nil{}, +out}:
      tdone(st, nq, good, base, c, idx, low, out, h)
    case 1n++g Con{+r, +rt} ST.TS{+c, +idx, +low, +st, Nil{}, +out}:
      +s0 = {ST.TS{c, idx, low, st, Nil{}, out} : ST.TS}
      +s2 = ST.troot(ST.getm(idx, r), adj, em, r, s0)
      +w0 = wm(adj, Con{r, rt}, s0)
      +k = root_go(st, adj, em, nq, good, base, r, rt, c, idx, low, out, hs, hb, h)
      twalk(g, rt, s2, adj, em, nq, good, c, hs, hb, so_inv(adj, nq, good, c, rt, s2, w0, k), KA.natle_trans(1n+wm(adj, rt, s2), w0, g, so_w(adj, nq, good, c, rt, s2, w0, k), hw))
    case 1n++g Nil{} ST.TS{+c, +idx, +low, +st, Con{ST.TF{+v, Con{+w, +rest}}, +ct}, +out}:
      +rs = {Nil{} : List<&2, Nat>}
      +s2 = ST.tedge(ST.getm(idx, w), ST.mem(w, st), adj, em, v, w, ST.TS{c, idx, low, st, Con{ST.TF{v, rest}, ct}, out})
      +w0 = wm(adj, rs, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})
      +k = edge_m(adj, em, nq, good, base, rs, c, idx, low, st, v, w, rest, ct, out, hs, hb, h, ST.getm(idx, w), {==})
      twalk(g, rs, s2, adj, em, nq, good, base, hs, hb, so_inv(adj, nq, good, base, rs, s2, w0, k), KA.natle_trans(1n+wm(adj, rs, s2), w0, g, so_w(adj, nq, good, base, rs, s2, w0, k), hw))
    case 1n++g Con{+r, +rt} ST.TS{+c, +idx, +low, +st, Con{ST.TF{+v, Con{+w, +rest}}, +ct}, +out}:
      +rs = {Con{r, rt} : List<&2, Nat>}
      +s2 = ST.tedge(ST.getm(idx, w), ST.mem(w, st), adj, em, v, w, ST.TS{c, idx, low, st, Con{ST.TF{v, rest}, ct}, out})
      +w0 = wm(adj, rs, ST.TS{c, idx, low, st, Con{ST.TF{v, Con{w, rest}}, ct}, out})
      +k = edge_m(adj, em, nq, good, base, rs, c, idx, low, st, v, w, rest, ct, out, hs, hb, h, ST.getm(idx, w), {==})
      twalk(g, rs, s2, adj, em, nq, good, base, hs, hb, so_inv(adj, nq, good, base, rs, s2, w0, k), KA.natle_trans(1n+wm(adj, rs, s2), w0, g, so_w(adj, nq, good, base, rs, s2, w0, k), hw))
    case 1n++g Nil{} ST.TS{+c, +idx, +low, +st, Con{ST.TF{+v, Nil{}}, +ct}, +out}:
      +rs = {Nil{} : List<&2, Nat>}
      +s2 = ST.tfin(v, ST.TS{c, idx, low, st, ct, out})
      +w0 = wm(adj, rs, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out})
      +k = fin_go(adj, nq, good, base, rs, c, idx, low, st, v, out, hb, KA.nateq(ST.look.of(ST.getm(low, v)), ST.look.of(ST.getm(idx, v))), ct, {==}, h)
      twalk(g, rs, s2, adj, em, nq, good, base, hs, hb, so_inv(adj, nq, good, base, rs, s2, w0, k), KA.natle_trans(1n+wm(adj, rs, s2), w0, g, so_w(adj, nq, good, base, rs, s2, w0, k), hw))
    case 1n++g Con{+r, +rt} ST.TS{+c, +idx, +low, +st, Con{ST.TF{+v, Nil{}}, +ct}, +out}:
      +rs = {Con{r, rt} : List<&2, Nat>}
      +s2 = ST.tfin(v, ST.TS{c, idx, low, st, ct, out})
      +w0 = wm(adj, rs, ST.TS{c, idx, low, st, Con{ST.TF{v, Nil{}}, ct}, out})
      +k = fin_go(adj, nq, good, base, rs, c, idx, low, st, v, out, hb, KA.nateq(ST.look.of(ST.getm(low, v)), ST.look.of(ST.getm(idx, v))), ct, {==}, h)
      twalk(g, rs, s2, adj, em, nq, good, base, hs, hb, so_inv(adj, nq, good, base, rs, s2, w0, k), KA.natle_trans(1n+wm(adj, rs, s2), w0, g, so_w(adj, nq, good, base, rs, s2, w0, k), hw))

# The components
# --------------

def mem_swap(+u: Nat, +a: List<&2, Nat>, b: List<&2, Nat>, +c: List<&2, Nat>) -> {SV.mem(u, ST.app(a, ST.app(b, c))) == SV.mem(u, ST.app(b, ST.app(a, c))) : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+x, +b2}:
      %Equal.sym(Bool, SV.mem(u, ST.app(a, Con{x, ST.app(b2, c)})), SV.mem(u, Con{x, ST.app(a, ST.app(b2, c))}), mem_move(u, a, x, ST.app(b2, c))) : {_ == SV.bor(SV.eq(u, x), SV.mem(u, ST.app(b2, ST.app(a, c)))) : Bool}
      %Equal.sym(Bool, SV.mem(u, ST.app(a, ST.app(b2, c))), SV.mem(u, ST.app(b2, ST.app(a, c))), mem_swap(u, a, b2, c)) : {SV.bor(SV.eq(u, x), _) == SV.bor(SV.eq(u, x), SV.mem(u, ST.app(b2, ST.app(a, c)))) : Bool}
      {==}

def dist_swap(+a: List<&2, Nat>, b: List<&2, Nat>, +c: List<&2, Nat>) -> {SV.distinct(ST.app(a, ST.app(b, c))) == SV.distinct(ST.app(b, ST.app(a, c))) : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+x, +b2}:
      +rhs = SV.distinct(Con{x, ST.app(b2, ST.app(a, c))})
      %Equal.sym(Bool, SV.distinct(ST.app(a, Con{x, ST.app(b2, c)})), SV.distinct(Con{x, ST.app(a, ST.app(b2, c))}), dist_move(a, x, ST.app(b2, c))) : {_ == rhs : Bool}
      %Equal.sym(Bool, SV.distinct(ST.app(a, ST.app(b2, c))), SV.distinct(ST.app(b2, ST.app(a, c))), dist_swap(a, b2, c)) : {SV.band(SV.bnot(SV.mem(x, ST.app(a, ST.app(b2, c)))), _) == rhs : Bool}
      %Equal.sym(Bool, SV.mem(x, ST.app(a, ST.app(b2, c))), SV.mem(x, ST.app(b2, ST.app(a, c))), mem_swap(x, a, b2, c)) : {SV.band(SV.bnot(_), SV.distinct(ST.app(b2, ST.app(a, c)))) == rhs : Bool}
      {==}

def swap_subl(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>) -> {L.subl(ST.app(a, ST.app(b, c)), ST.app(b, ST.app(a, c))) == True{} : Bool}:
  +z = ST.app(b, ST.app(a, c))
  subl_app(a, ST.app(b, c), z, L.subl_trans(a, ST.app(a, c), z, app_subl_l(a, c), app_subl_r(b, ST.app(a, c))), subl_app(b, c, z, app_subl_l(b, ST.app(a, c)), L.subl_trans(c, ST.app(a, c), z, app_subl_r(a, c), app_subl_r(b, ST.app(a, c)))))

def rv_s1(xs: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>) -> {L.subl(ST.cats(ST.revl.go(xs, acc)), ST.app(ST.cats(xs), ST.cats(acc))) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subl_refl(ST.cats(acc))
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(ST.app(h, ST.cats(t)), ST.cats(acc)), ST.app(h, ST.app(ST.cats(t), ST.cats(acc))), app_assoc(h, ST.cats(t), ST.cats(acc))) : {L.subl(ST.cats(ST.revl.go(t, Con{h, acc})), _) == True{} : Bool}
      L.subl_trans(ST.cats(ST.revl.go(t, Con{h, acc})), ST.app(ST.cats(t), ST.app(h, ST.cats(acc))), ST.app(h, ST.app(ST.cats(t), ST.cats(acc))), rv_s1(t, Con{h, acc}), swap_subl(ST.cats(t), h, ST.cats(acc)))

def rv_s2(xs: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>) -> {L.subl(ST.app(ST.cats(xs), ST.cats(acc)), ST.cats(ST.revl.go(xs, acc))) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subl_refl(ST.cats(acc))
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(ST.app(h, ST.cats(t)), ST.cats(acc)), ST.app(h, ST.app(ST.cats(t), ST.cats(acc))), app_assoc(h, ST.cats(t), ST.cats(acc))) : {L.subl(_, ST.cats(ST.revl.go(t, Con{h, acc}))) == True{} : Bool}
      L.subl_trans(ST.app(h, ST.app(ST.cats(t), ST.cats(acc))), ST.app(ST.cats(t), ST.app(h, ST.cats(acc))), ST.cats(ST.revl.go(t, Con{h, acc})), swap_subl(h, ST.cats(t), ST.cats(acc)), rv_s2(t, Con{h, acc}))

def rv_d(xs: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>) -> {SV.distinct(ST.cats(ST.revl.go(xs, acc))) == SV.distinct(ST.app(ST.cats(xs), ST.cats(acc))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(ST.app(h, ST.cats(t)), ST.cats(acc)), ST.app(h, ST.app(ST.cats(t), ST.cats(acc))), app_assoc(h, ST.cats(t), ST.cats(acc))) : {SV.distinct(ST.cats(ST.revl.go(t, Con{h, acc}))) == SV.distinct(_) : Bool}
      %Equal.sym(Bool, SV.distinct(ST.cats(ST.revl.go(t, Con{h, acc}))), SV.distinct(ST.app(ST.cats(t), ST.app(h, ST.cats(acc)))), rv_d(t, Con{h, acc})) : {_ == SV.distinct(ST.app(h, ST.app(ST.cats(t), ST.cats(acc)))) : Bool}
      dist_swap(ST.cats(t), h, ST.cats(acc))

def rv_dt(+out: List<&2, List<&2, Nat>>, h: {SV.distinct(ST.cats(out)) == True{} : Bool}) -> {SV.distinct(ST.cats(ST.revl.go(out, Nil{}))) == True{} : Bool}:
  %Equal.sym(Bool, SV.distinct(ST.cats(ST.revl.go(out, Nil{}))), SV.distinct(ST.app(ST.cats(out), Nil{})), rv_d(out, Nil{})) : {_ == True{} : Bool}
  %Equal.sym(List<&2, Nat>, ST.app(ST.cats(out), Nil{}), ST.cats(out), app_nil(ST.cats(out))) : {SV.distinct(_) == True{} : Bool}
  h

def rv_st1(+out: List<&2, List<&2, Nat>>) -> {L.subl(ST.cats(ST.revl.go(out, Nil{})), ST.cats(out)) == True{} : Bool}:
  %app_nil(ST.cats(out)) : {L.subl(ST.cats(ST.revl.go(out, Nil{})), _) == True{} : Bool}
  rv_s1(out, Nil{})

def rv_st2(+out: List<&2, List<&2, Nat>>) -> {L.subl(ST.cats(out), ST.cats(ST.revl.go(out, Nil{}))) == True{} : Bool}:
  %app_nil(ST.cats(out)) : {L.subl(_, ST.cats(ST.revl.go(out, Nil{}))) == True{} : Bool}
  rv_s2(out, Nil{})

# the components, oldest first, still partition good
def revl_part(+out: List<&2, List<&2, Nat>>, +good: List<&2, Nat>, +h: {tend2(good, out) == True{} : Bool}) -> {tend2(good, ST.revl.go(out, Nil{})) == True{} : Bool}:
  +co = ST.cats(out)
  +cr = ST.cats(ST.revl.go(out, Nil{}))
  +h2 = L.band_r(SV.distinct(co), SV.band(L.subl(good, co), L.subl(co, good)), h)
  L.band_i(SV.distinct(cr), SV.band(L.subl(good, cr), L.subl(cr, good)), rv_dt(out, L.band_l(SV.distinct(co), SV.band(L.subl(good, co), L.subl(co, good)), h)), L.band_i(L.subl(good, cr), L.subl(cr, good), L.subl_trans(good, co, cr, L.band_l(L.subl(good, co), L.subl(co, good), h2), rv_st2(out)), L.subl_trans(cr, co, good, rv_st1(out), L.band_r(L.subl(good, co), L.subl(co, good), h2))))

def tend_out(+good: List<&2, Nat>, s: ST.TS, h: {tend(good, s) == True{} : Bool}) -> {tend2(good, ST.ts.out(s)) == True{} : Bool}:
  match s:
    case ST.TS{c, idx, low, st, cs, out}:
      h

# The start
# ---------

def getm_nones(n: Nat, k: Nat) -> {ST.getm(ST.nones(n), k) == None{} : Maybe<&2, Nat>}:
  match n k:
    case 0n k:
      {==}
    case 1n+m 0n:
      {==}
    case 1n+m 1n+j:
      getm_nones(m, j)

def mlen_nones(n: Nat) -> {L.mlen(ST.nones(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      %Equal.sym(Nat, L.mlen(ST.nones(m)), m, mlen_nones(m)) : {1n+_ == 1n+m : Nat}
      {==}

def agn_hd(+nq: Nat, +m: Nat) -> {biff(L.issome(ST.getm(ST.nones(nq), m)), SV.mem(m, Nil{})) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.nones(nq), m), None{}, getm_nones(nq, m)) : {biff(L.issome(_), False{}) == True{} : Bool}
  {==}

def agree_nones(n: Nat, +nq: Nat) -> {agree(n, ST.nones(nq), Nil{}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.band_i(biff(L.issome(ST.getm(ST.nones(nq), m)), SV.mem(m, Nil{})), agree(m, ST.nones(nq), Nil{}), agn_hd(nq, m), agree_nones(m, nq))

def tinit(+nq: Nat, +good: List<&2, Nat>) -> {tinvs(nq, good, 0n, good, ST.TS{0n, ST.nones(nq), ST.nones(nq), Nil{}, Nil{}, Nil{}}) == True{} : Bool}:
  tinv_mk(nq, good, 0n, good, 0n, ST.nones(nq), ST.nones(nq), Nil{}, Nil{}, Nil{}, {==}, agree_nones(nq, nq), {==}, app_subl_l(good, Nil{}), L.subl_refl(good), D.eq_of(L.mlen(ST.nones(nq)), nq, mlen_nones(nq)), D.eq_of(L.mlen(ST.nones(nq)), nq, mlen_nones(nq)), {==}, {==}, {==}, {==}, {==})

# the fuel comps gives tarjan covers the work
def fuel_ok(+tt: Nat, +nq: Nat, +lg: Nat, +u0: Nat, h1: {KA.natle(lg, nq) == True{} : Bool}, h2: {KA.natle(u0, Nat.add(nq, tt)) == True{} : Bool}) -> {KA.natle(1n+Nat.add(lg, u0), Nat.add(Nat.add(tt, nq), Nat.add(nq, Nat.add(nq, 2n)))) == True{} : Bool}:
  %NR.ring_eq([tt, nq], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}}}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NVar{1n}, NR.NCst{2n}}}}, {==}) : {KA.natle(1n+Nat.add(lg, u0), _) == True{} : Bool}
  KA.natle_trans(1n+Nat.add(lg, u0), 1n+Nat.add(nq, Nat.add(nq, tt)), NR.eval([tt, nq], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}}}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}), KA.natle_add2(lg, u0, nq, Nat.add(nq, tt), h1, h2), KA.natle_add_r(1n+Nat.add(nq, Nat.add(nq, tt)), 1n+nq))

# Tarjan's components partition the equations good it starts from, when
# the equations they need (em's entries) are in good, good lies below nq
# and has at most nq entries
def comps_part(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +nq: Nat, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, hl: {KA.natle(SV.len(good), nq) == True{} : Bool}) -> {tend2(good, ST.comps(adj, em, good, nq)) == True{} : Bool}:
  +fuel = Nat.add(Nat.add(ST.total(adj), nq), Nat.add(nq, Nat.add(nq, 2n)))
  +s0 = {ST.TS{0n, ST.nones(nq), ST.nones(nq), Nil{}, Nil{}, Nil{}} : ST.TS}
  +t = ST.tarjan(fuel, adj, em, good, s0)
  revl_part(ST.ts.out(t), good, tend_out(good, t, twalk(fuel, good, s0, adj, em, nq, good, 0n, hs, hb, tinit(nq, good), fuel_ok(ST.total(adj), nq, SV.len(good), um(ST.nones(nq), adj), hl, um_init(nq, adj)))))
