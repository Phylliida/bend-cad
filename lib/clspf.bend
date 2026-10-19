# bend-cad: the interim classes (lib/solve.bend: cls_of, sk-09's red
# stage as Over and Kept classes) make the same constraints driven as the
# red stage's list: mark(reds(cls_mk(red, why, n)), sk) = mark(red, sk)
# when n is the number of constraints. red is newest first and reds
# ascending, so the two agree as sets, position by position: walking the
# constraints, the red positions already passed form a prefix below the
# current one. Proofs only.

import Base
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./why.bend as WY
import ./listpf.bend as L
import ./solve.bend as SO

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Order on positions
# ------------------

# a < b: b is not a
def lt_ne(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.eq(0n, 0n) == False{} : Bool}, L.tnf(False{}, h, {==}))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.eq(0n, 1n+i) == False{} : Bool}, L.tnf(False{}, h, {==}))
    case 1n+i 1n+j:
      lt_ne(i, j, h)

def lt_ne2(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.eq(0n, 0n) == False{} : Bool}, L.tnf(False{}, h, {==}))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.eq(1n+i, 0n) == False{} : Bool}, L.tnf(False{}, h, {==}))
    case 1n+i 1n+j:
      lt_ne2(i, j, h)

def lt_succ(a: Nat, b: Nat, h: {SV.lt(a, b) == True{} : Bool}) -> {SV.lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SV.lt(0n, 1n) == True{} : Bool}, L.tnf(False{}, h, {==}))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SV.lt(1n+i, 1n) == True{} : Bool}, L.tnf(False{}, h, {==}))
    case 1n+i 1n+j:
      lt_succ(i, j, h)

def lt_self(i: Nat) -> {SV.lt(i, 1n+i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+k:
      lt_self(k)

# Lists below a position
# ----------------------

def below_succ(xs: List<&2, Nat>, +p: Nat, +h: {SV.below(xs, p) == True{} : Bool}) -> {SV.below(xs, 1n+p) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      L.band_i(SV.lt(a, 1n+p), SV.below(t, 1n+p), lt_succ(a, p, L.band_l(SV.lt(a, p), SV.below(t, p), h)), below_succ(t, p, L.band_r(SV.lt(a, p), SV.below(t, p), h)))

def below_snoc(xs: List<&2, Nat>, +i: Nat, +h: {SV.below(xs, i) == True{} : Bool}) -> {SV.below(SV.cat(xs, Con{i, Nil{}}), 1n+i) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.band_i(SV.lt(i, 1n+i), True{}, lt_self(i), {==})
    case Con{+a, +t}:
      L.band_i(SV.lt(a, 1n+i), SV.below(SV.cat(t, Con{i, Nil{}}), 1n+i), lt_succ(a, i, L.band_l(SV.lt(a, i), SV.below(t, i), h)), below_snoc(t, i, L.band_r(SV.lt(a, i), SV.below(t, i), h)))

# p is not in a list below it, so a prefix below p does not change p's
# membership
def mem_cat_low(+p: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SV.below(xs, p) == True{} : Bool}) -> {SV.mem(p, SV.cat(xs, ys)) == SV.mem(p, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(Bool, SV.eq(p, a), False{}, lt_ne(a, p, L.band_l(SV.lt(a, p), SV.below(t, p), h))) : {SV.bor(_, SV.mem(p, SV.cat(t, ys))) == SV.mem(p, ys) : Bool}
      mem_cat_low(p, t, ys, L.band_r(SV.lt(a, p), SV.below(t, p), h))

def cat_snoc(xs: List<&2, Nat>, +i: Nat, +ys: List<&2, Nat>) -> {SV.cat(xs, Con{i, ys}) == SV.cat(SV.cat(xs, Con{i, Nil{}}), ys) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, zs => Con{a, zs}, SV.cat(t, Con{i, ys}), SV.cat(SV.cat(t, Con{i, Nil{}}), ys), cat_snoc(t, i, ys))

# The interim classes' red positions
# ----------------------------------
# R(m, i) = reds.go(cls.go(m, red, why, i), i): the red positions among
# i .. i + m - 1, ascending.

def isred_over(y: WY.Why) -> {SV.is_red(SO.over_of(y)) == True{} : Bool}:
  match y:
    case WY.Why{j, s, w}:
      {==}

def isred_at(b: Bool, +red: List<&2, Nat>, +why: List<&2, WY.Why>, +c: Nat) -> {SV.is_red(SO.cls_at(b, red, why, c)) == b : Bool}:
  match b:
    case True{}:
      isred_over(SO.whyat(red, why, c))
    case False{}:
      {==}

def step(+m: Nat, +red: List<&2, Nat>, +why: List<&2, WY.Why>, +i: Nat) -> {SV.reds.go(SO.cls.go(1n+m, red, why, i), i) == SV.pos.pick(SV.mem(i, red), i, SV.reds.go(SO.cls.go(m, red, why, 1n+i), 1n+i)) : List<&2, Nat>}:
  %isred_at(SV.mem(i, red), red, why, i) : {SV.pos.pick(SV.is_red(SO.cls_at(SV.mem(i, red), red, why, i)), i, SV.reds.go(SO.cls.go(m, red, why, 1n+i), 1n+i)) == SV.pos.pick(_, i, SV.reds.go(SO.cls.go(m, red, why, 1n+i), 1n+i)) : List<&2, Nat>}
  {==}

def rge.pick(b: Bool, +i: Nat, +p: Nat, +r: List<&2, Nat>, +hp: {SV.lt(p, i) == True{} : Bool}, hr: {SV.mem(p, r) == False{} : Bool}) -> {SV.mem(p, SV.pos.pick(b, i, r)) == False{} : Bool}:
  match b:
    case True{}:
      L.bor_f(SV.eq(p, i), SV.mem(p, r), lt_ne2(p, i, hp), hr)
    case False{}:
      hr

# every position in R(m, i) is at least i
def rge(m: Nat, +red: List<&2, Nat>, +why: List<&2, WY.Why>, +i: Nat, +p: Nat, +h: {SV.lt(p, i) == True{} : Bool}) -> {SV.mem(p, SV.reds.go(SO.cls.go(m, red, why, i), i)) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(List<&2, Nat>, SV.reds.go(SO.cls.go(1n+k, red, why, i), i), SV.pos.pick(SV.mem(i, red), i, SV.reds.go(SO.cls.go(k, red, why, 1n+i), 1n+i)), step(k, red, why, i)) : {SV.mem(p, _) == False{} : Bool}
      rge.pick(SV.mem(i, red), i, p, SV.reds.go(SO.cls.go(k, red, why, 1n+i), 1n+i), h, rge(k, red, why, 1n+i, p, lt_succ(p, i, h)))

def mem_pick_self(b: Bool, +i: Nat, +r: List<&2, Nat>, h: {SV.mem(i, r) == False{} : Bool}) -> {SV.mem(i, SV.pos.pick(b, i, r)) == b : Bool}:
  match b:
    case True{}:
      L.bor_l(SV.eq(i, i), SV.mem(i, r), L.eq_refl(i))
    case False{}:
      h

# the prefix after position i
def pickA(b: Bool, +xs: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match b:
    case True{}:
      SV.cat(xs, Con{i, Nil{}})
    case False{}:
      xs

def cat_pick(b: Bool, +xs: List<&2, Nat>, +i: Nat, +r: List<&2, Nat>) -> {SV.cat(xs, SV.pos.pick(b, i, r)) == SV.cat(pickA(b, xs, i), r) : List<&2, Nat>}:
  match b:
    case True{}:
      cat_snoc(xs, i, r)
    case False{}:
      {==}

def below_pick(b: Bool, +xs: List<&2, Nat>, +i: Nat, +h: {SV.below(xs, i) == True{} : Bool}) -> {SV.below(pickA(b, xs, i), 1n+i) == True{} : Bool}:
  match b:
    case True{}:
      below_snoc(xs, i, h)
    case False{}:
      below_succ(xs, i, h)

# Agreement, position by position
# -------------------------------

# x and y agree at the positions of cs, from i
def Ag(+x: List<&2, Nat>, +y: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat) -> Data:
  match cs:
    case Nil{}:
      Unit
    case Con{r, t}:
      SK.Both({SV.mem(i, x) == SV.mem(i, y) : Bool}, Ag(x, y, t, 1n+i))

def mark_ext(+x: List<&2, Nat>, +y: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat, h: Ag(x, y, cs, i)) -> {SV.mark.cons(x, cs, i) == SV.mark.cons(y, cs, i) : List<&2, SK.Rec>}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, +dr, +k}, +t}:
      (e, rest) = h
      %e : {Con{SK.Rec{id, SV.bor(dr, SV.mem(i, x)), k}, SV.mark.cons(x, t, 1n+i)} == Con{SK.Rec{id, SV.bor(dr, _), k}, SV.mark.cons(y, t, 1n+i)} : List<&2, SK.Rec>}
      %mark_ext(x, y, t, 1n+i, rest) : {Con{SK.Rec{id, SV.bor(dr, SV.mem(i, x)), k}, SV.mark.cons(x, t, 1n+i)} == Con{SK.Rec{id, SV.bor(dr, SV.mem(i, x)), k}, _} : List<&2, SK.Rec>}
      {==}

# x (the interim classes' red positions) agrees with red from i on, given
# that x is a prefix below i followed by R(len(cs), i)
def ag_cls(+x: List<&2, Nat>, +red: List<&2, Nat>, +why: List<&2, WY.Why>, cs: List<&2, SK.Rec>, +i: Nat, +pre: List<&2, Nat>, +hx: {x == SV.cat(pre, SV.reds.go(SO.cls.go(SV.clen(cs), red, why, i), i)) : List<&2, Nat>}, +hp: {SV.below(pre, i) == True{} : Bool}) -> Ag(x, red, cs, i):
  match cs:
    case Nil{}:
      Unit{}
    case Con{r, +t}:
      +r1 = SV.reds.go(SO.cls.go(1n+SV.clen(t), red, why, i), i)
      +rt = SV.reds.go(SO.cls.go(SV.clen(t), red, why, 1n+i), 1n+i)
      +b = SV.mem(i, red)
      +st = step(SV.clen(t), red, why, i)
      +e1 = Equal.cong(List<&2, Nat>, Bool, zs => SV.mem(i, zs), x, SV.cat(pre, r1), hx)
      +e2 = mem_cat_low(i, pre, r1, hp)
      +e3 = Equal.cong(List<&2, Nat>, Bool, zs => SV.mem(i, zs), r1, SV.pos.pick(b, i, rt), st)
      +e4 = mem_pick_self(b, i, rt, rge(SV.clen(t), red, why, 1n+i, i, lt_self(i)))
      +ei = Equal.trans(Bool, SV.mem(i, x), SV.mem(i, SV.cat(pre, r1)), b, e1, Equal.trans(Bool, SV.mem(i, SV.cat(pre, r1)), SV.mem(i, r1), b, e2, Equal.trans(Bool, SV.mem(i, r1), SV.mem(i, SV.pos.pick(b, i, rt)), b, e3, e4)))
      +c1 = Equal.cong(List<&2, Nat>, List<&2, Nat>, zs => SV.cat(pre, zs), r1, SV.pos.pick(b, i, rt), st)
      +hx2 = Equal.trans(List<&2, Nat>, x, SV.cat(pre, r1), SV.cat(pickA(b, pre, i), rt), hx, Equal.trans(List<&2, Nat>, SV.cat(pre, r1), SV.cat(pre, SV.pos.pick(b, i, rt)), SV.cat(pickA(b, pre, i), rt), c1, cat_pick(b, pre, i, rt)))
      (ei, ag_cls(x, red, why, t, 1n+i, pickA(b, pre, i), hx2, below_pick(b, pre, i, hp)))

# The interim classes make the red stage's constraints driven, and no
# others
def mark_cls(+red: List<&2, Nat>, +why: List<&2, WY.Why>, sk: SK.Sketch) -> {SV.mark(SV.reds(SO.cls_mk(red, why, SV.ncons(sk))), sk) == SV.mark(red, sk) : SK.Sketch}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      +x = SV.reds(SO.cls_mk(red, why, SV.clen(cs)))
      Equal.cong(List<&2, SK.Rec>, SK.Sketch, zs => SK.Sketch{vs, es, zs}, SV.mark.cons(x, cs, 0n), SV.mark.cons(red, cs, 0n), mark_ext(x, red, cs, 0n, ag_cls(x, red, why, cs, 0n, Nil{}, {==}, {==})))

# for the solver's own classes
def mark_cls_of(+sk: SK.Sketch) -> {SV.mark(SV.reds(SO.cls_of(sk)), sk) == SV.mark(SO.red_of(sk), sk) : SK.Sketch}:
  mark_cls(SO.red_of(sk), SO.why_of(sk), sk)
