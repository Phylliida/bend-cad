# bend-cad: list and matching facts first proven for sk-09's red stage,
# kept for what still uses them (lib/maxpf.bend, lib/structpf.bend,
# lib/keptpf.bend, lib/gmpf.bend, lib/passpf.bend). Proofs only.
#
# - Owner lists by position (drop): at a constraint, the equations from k
#   on are owned as the rest of the constraints say.
# - Bounds and membership (below_mono, below_notmem).
# - One unit's search (lib/struct.bend: grp): the matched equations stay
#   owned by earlier constraints that are not red (gok, grp_ok), and a
#   failed search's witness checks (lib/why.bend).
# - nones: an empty matching.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./why.bend as WY
import ./karith.bend as KA
import ./struct.bend as ST
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Owners
# ------

def drop(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k xs:
    case 0n xs:
      xs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      drop(j, t)

def tl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def drop_tl(k: Nat, xs: List<&2, Nat>) -> {drop(1n+k, xs) == tl(drop(k, xs)) : List<&2, Nat>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      drop_tl(j, t)

def nth_drop(k: Nat, xs: List<&2, Nat>) -> {SV.nth(xs, k) == SV.nth(drop(k, xs), 0n) : Nat}:
  match k xs:
    case 0n xs:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      nth_drop(j, t)

def drop_nil(n: Nat) -> {drop(n, Nil{}) == Nil{} : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def drop_add(k: Nat, +n: Nat, xs: List<&2, Nat>) -> {drop(Nat.add(k, n), xs) == drop(n, drop(k, xs)) : List<&2, Nat>}:
  match k xs:
    case 0n xs:
      {==}
    case 1n+j Nil{}:
      %Equal.sym(List<&2, Nat>, drop(n, Nil{}), Nil{}, drop_nil(n)) : {drop(Nat.add(1n+j, n), Nil{}) == _ : List<&2, Nat>}
      {==}
    case 1n+j Con{h, t}:
      drop_add(j, n, t)

def drop_reps(n: Nat, +i: Nat, +o: List<&2, Nat>) -> {drop(n, SV.cat(SV.reps(n, i), o)) == o : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      drop_reps(m, i, o)

# the next equation is owned by i
def own_at(+k: Nat, +own: List<&2, Nat>, +n: Nat, +i: Nat, +o: List<&2, Nat>, hd: {drop(k, own) == SV.cat(SV.reps(1n+n, i), o) : List<&2, Nat>}) -> {SV.nth(own, k) == i : Nat}:
  %Equal.sym(Nat, SV.nth(own, k), SV.nth(drop(k, own), 0n), nth_drop(k, own)) : {_ == i : Nat}
  %Equal.sym(List<&2, Nat>, drop(k, own), SV.cat(SV.reps(1n+n, i), o), hd) : {SV.nth(_, 0n) == i : Nat}
  {==}

def drop_step(+k: Nat, +own: List<&2, Nat>, +n: Nat, +i: Nat, +o: List<&2, Nat>, hd: {drop(k, own) == SV.cat(SV.reps(1n+n, i), o) : List<&2, Nat>}) -> {drop(1n+k, own) == SV.cat(SV.reps(n, i), o) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, drop(1n+k, own), tl(drop(k, own)), drop_tl(k, own)) : {_ == SV.cat(SV.reps(n, i), o) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, drop(k, own), SV.cat(SV.reps(1n+n, i), o), hd) : {tl(_) == SV.cat(SV.reps(n, i), o) : List<&2, Nat>}
  {==}

# Numbers
# -------

def below_mono(xs: List<&2, Nat>, +a: Nat, +b: Nat, +h: {SV.below(xs, a) == True{} : Bool}, +hab: {KA.natle(a, b) == True{} : Bool}) -> {SV.below(xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.lt(x, b), SV.below(t, b), %Equal.sym(Bool, SV.lt(x, b), KA.natle(1n+x, b), L.lt_sv(x, b)) : {_ == True{} : Bool}
        KA.natle_trans(1n+x, a, b, %L.lt_sv(x, a) : {_ == True{} : Bool}
          L.band_l(SV.lt(x, a), SV.below(t, a), h), hab), below_mono(t, a, b, L.band_r(SV.lt(x, a), SV.below(t, a), h), hab))

def below_notmem.go(+k: Nat, +xs: List<&2, Nat>, c: Bool, e: {SV.mem(k, xs) == c : Bool}, h: {SV.below(xs, k) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.natlt_irr(k, %L.lt_sv(k, k) : {_ == True{} : Bool}
        D.below_mem(k, xs, k, e, h)))
    case False{}:
      {==}

# everything in xs is below k: k is not in xs
def below_notmem(+k: Nat, +xs: List<&2, Nat>, h: {SV.below(xs, k) == True{} : Bool}) -> {SV.mem(k, xs) == False{} : Bool}:
  below_notmem.go(k, xs, SV.mem(k, xs), {==}, h)

def lt_succ(+k: Nat) -> {SV.lt(k, 1n+k) == True{} : Bool}:
  D.lt_self(k)

# Matched equations and their owners
# ----------------------------------

# while constraint i is matched, with red so far: m's owner is i, or an
# earlier constraint not red
def okown(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +m: Nat) -> Bool:
  SV.bor(SV.eq(SV.nth(own, m), i), SV.band(SV.lt(SV.nth(own, m), i), SV.bnot(SV.mem(SV.nth(own, m), red))))

def allown(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+m, t}:
      SV.band(okown(own, red, i, m), allown(own, red, i, t))

def allown_mem.go(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +m: Nat, +x: Nat, +t: List<&2, Nat>, c: Bool, e: {SV.eq(m, x) == c : Bool}, hm: {SV.bor(c, SV.mem(m, t)) == True{} : Bool}, h: {allown(own, red, i, Con{x, t}) == True{} : Bool}, ih: {SV.mem(m, t) == True{} : Bool} -> {allown(own, red, i, t) == True{} : Bool} -> {okown(own, red, i, m) == True{} : Bool}) -> {okown(own, red, i, m) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, m, x, L.eq_ok(m, x, e)) : {okown(own, red, i, _) == True{} : Bool}
      L.band_l(okown(own, red, i, x), allown(own, red, i, t), h)
    case False{}:
      ih(hm, L.band_r(okown(own, red, i, x), allown(own, red, i, t), h))

def allown_mem(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +m: Nat, xs: List<&2, Nat>, hm: {SV.mem(m, xs) == True{} : Bool}, h: {allown(own, red, i, xs) == True{} : Bool}) -> {okown(own, red, i, m) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({okown(own, red, i, m) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      allown_mem.go(own, red, i, m, x, t, SV.eq(m, x), {==}, hm, h, p => q => allown_mem(own, red, i, m, t, p, q))

def allown_subl(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hs: {L.subl(xs, ys) == True{} : Bool}, +h: {allown(own, red, i, ys) == True{} : Bool}) -> {allown(own, red, i, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(okown(own, red, i, x), allown(own, red, i, t), allown_mem(own, red, i, x, ys, L.subl_hd(x, t, ys, hs), h), allown_subl(own, red, i, t, ys, L.subl_tl(x, t, ys, hs), h))

def okown_self(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +k: Nat, h: {SV.nth(own, k) == i : Nat}) -> {okown(own, red, i, k) == True{} : Bool}:
  %Equal.sym(Nat, SV.nth(own, k), i, h) : {SV.bor(SV.eq(_, i), SV.band(SV.lt(_, i), SV.bnot(SV.mem(_, red)))) == True{} : Bool}
  L.bor_l(SV.eq(i, i), SV.band(SV.lt(i, i), SV.bnot(SV.mem(i, red))), L.eq_refl(i))

# A red constraint's record
# -------------------------

# constraint i failed (red being the red ones before it) with record r
def fgood(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, r: ST.Red) -> Bool:
  match r:
    case ST.Red{+j, +s, +w}:
      SV.band(SV.eq(SV.nth(own, j), i), SV.band(SV.mem(j, s), SV.band(WY.overdet(full, s, w), allown(own, red, i, s))))

# The group of constraint i
# -------------------------

def gok(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)))))

# the group's state before equation k, n equations left; c: the number of
# matched equations it will end with
def gin(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +k: Nat, +n: Nat, st: ST.GS) -> Bool:
  match st:
    case ST.GOk{+vm}:
      SV.band(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), n), c))
    case ST.GFail{r}:
      fgood(full, own, red, i, r)

# the group's end, its equations below k
def gres(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +k: Nat, g: ST.GS) -> Bool:
  match g:
    case ST.GOk{+vm}:
      SV.band(gok(own, red, i, nv, k, vm), SV.eq(SV.len(ST.somes(vm)), c))
    case ST.GFail{r}:
      fgood(full, own, red, i, r)

def gok_d(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(own, red, i, nv, k, vm) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)))), h)

def gok_r(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(own, red, i, nv, k, vm) == True{} : Bool}) -> {SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)))) == True{} : Bool}:
  L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)))), h)

def gok_b(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(own, red, i, nv, k, vm) == True{} : Bool}) -> {SV.below(ST.somes(vm), k) == True{} : Bool}:
  L.band_l(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm))), gok_r(own, red, i, nv, k, vm, h))

def gok_m(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(own, red, i, nv, k, vm) == True{} : Bool}) -> {L.mlen(vm) == nv : Nat}:
  L.eq_ok(L.mlen(vm), nv, L.band_l(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)), L.band_r(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm))), gok_r(own, red, i, nv, k, vm, h))))

def gok_o(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(own, red, i, nv, k, vm) == True{} : Bool}) -> {allown(own, red, i, ST.somes(vm)) == True{} : Bool}:
  L.band_r(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)), L.band_r(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm))), gok_r(own, red, i, nv, k, vm, h)))

def gok_mk(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, hd: {SV.distinct(ST.somes(vm)) == True{} : Bool}, hb: {SV.below(ST.somes(vm), k) == True{} : Bool}, hm: {L.mlen(vm) == nv : Nat}, ho: {allown(own, red, i, ST.somes(vm)) == True{} : Bool}) -> {gok(own, red, i, nv, k, vm) == True{} : Bool}:
  L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)))), hd, L.band_i(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm))), hb, L.band_i(SV.eq(L.mlen(vm), nv), allown(own, red, i, ST.somes(vm)), D.eq_of(L.mlen(vm), nv, hm), ho)))

def adjb_vm(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +nv: Nat, hm: {L.mlen(vm) == nv : Nat}, ha: {D.adjb(adj, nv) == True{} : Bool}) -> {D.adjb(adj, L.mlen(vm)) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(vm), nv, hm) : {D.adjb(adj, _) == True{} : Bool}
  ha

def fuel_vm(+vm: List<&2, Maybe<&2, Nat>>, +nv: Nat, +f: Nat, hm: {L.mlen(vm) == nv : Nat}, hf: {KA.natle(1n+nv, f) == True{} : Bool}) -> {KA.natle(1n+L.mlen(vm), f) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(vm), nv, hm) : {KA.natle(1n+_, f) == True{} : Bool}
  hf

# k + 1 + m = kend <= nq: k < nq
def lt_grp(+k: Nat, +m: Nat, +kend: Nat, +nq: Nat, hk: {Nat.add(k, 1n+m) == kend : Nat}, hK: {KA.natle(kend, nq) == True{} : Bool}) -> {SV.lt(k, nq) == True{} : Bool}:
  %Equal.sym(Bool, SV.lt(k, nq), KA.natle(1n+k, nq), L.lt_sv(k, nq)) : {_ == True{} : Bool}
  KA.natle_trans(1n+k, kend, nq, %hk : {KA.natle(1n+k, _) == True{} : Bool}
    %LN.add_succ(k, m) : {KA.natle(1n+k, _) == True{} : Bool}
      KA.natle_add_r(k, m), hK)

def lt_le(+k: Nat, +nq: Nat, h: {SV.lt(k, nq) == True{} : Bool}) -> {KA.natle(k, nq) == True{} : Bool}:
  KA.natle_pred(k, nq, %L.lt_sv(k, nq) : {_ == True{} : Bool}
    h)

def cnt_step(+l: Nat, +m: Nat, +c: Nat, +l2: Nat, hn: {l2 == 1n+l : Nat}, hc: {SV.eq(Nat.add(l, 1n+m), c) == True{} : Bool}) -> {SV.eq(Nat.add(l2, m), c) == True{} : Bool}:
  %Equal.sym(Nat, l2, 1n+l, hn) : {SV.eq(Nat.add(_, m), c) == True{} : Bool}
  %Equal.sym(Nat, 1n+Nat.add(l, m), Nat.add(l, 1n+m), LN.add_succ(l, m)) : {SV.eq(_, c) == True{} : Bool}
  hc

# one equation of the group, k, searched for in vm: the group's next state
def grp_step(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +k: Nat, +m: Nat, +f: Nat, +vm: List<&2, Maybe<&2, Nat>>, a: ST.DS, +hres: {D.res(f, k, ST.adj(full), vm, Nil{}, ST.DS{False{}, vm, Nil{}}, ST.nthl(ST.adj(full), k), a) == True{} : Bool}, +hg: {gok(own, red, i, nv, k, vm) == True{} : Bool}, hc: {SV.eq(Nat.add(SV.len(ST.somes(vm)), 1n+m), c) == True{} : Bool}, +hown: {SV.nth(own, k) == i : Nat}, +hlt: {SV.lt(k, SV.neqs(full)) == True{} : Bool}) -> {gin(full, own, red, i, nv, c, 1n+k, m, ST.gstep(k, a, vm)) == True{} : Bool}:
  match a:
    case ST.DS{True{}, +vm2, vis}:
      +hs = D.so_s(vm, k, vm2, hres)
      L.band_i(gok(own, red, i, nv, 1n+k, vm2), SV.eq(Nat.add(SV.len(ST.somes(vm2)), m), c), gok_mk(own, red, i, nv, 1n+k, vm2, D.so_d(vm, k, vm2, hres), D.below_subl(ST.somes(vm2), Con{k, ST.somes(vm)}, 1n+k, hs, L.band_i(SV.lt(k, 1n+k), SV.below(ST.somes(vm), 1n+k), lt_succ(k), below_mono(ST.somes(vm), k, 1n+k, gok_b(own, red, i, nv, k, vm, hg), KA.natle_succ(k, k, KA.natle_refl(k))))), Equal.trans(Nat, L.mlen(vm2), L.mlen(vm), nv, D.so_m(vm, k, vm2, hres), gok_m(own, red, i, nv, k, vm, hg)), allown_subl(own, red, i, ST.somes(vm2), Con{k, ST.somes(vm)}, hs, L.band_i(okown(own, red, i, k), allown(own, red, i, ST.somes(vm)), okown_self(own, red, i, k, hown), gok_o(own, red, i, nv, k, vm, hg)))), cnt_step(SV.len(ST.somes(vm)), m, c, SV.len(ST.somes(vm2)), D.so_n(vm, k, vm2, hres), hc))
    case ST.DS{False{}, vm2, +vis}:
      +adj = ST.adj(full)
      +hv = L.band_l(D.vis_ok(vm, adj, Nil{}, f, vis), SV.band(L.subl(ST.nthl(adj, k), vis), True{}), hres)
      +hn = L.band_l(L.subl(ST.nthl(adj, k), vis), True{}, L.band_r(D.vis_ok(vm, adj, Nil{}, f, vis), SV.band(L.subl(ST.nthl(adj, k), vis), True{}), hres))
      +lk = ST.look(vm, vis)
      L.band_i(SV.eq(SV.nth(own, k), i), SV.band(SV.mem(k, Con{k, lk}), SV.band(WY.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk}))), D.eq_of(SV.nth(own, k), i, hown), L.band_i(SV.mem(k, Con{k, lk}), SV.band(WY.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk})), L.mem_hd(k, lk), L.band_i(WY.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk}), D.wit_ok(full, vm, k, f, vis, below_notmem(k, ST.somes(vm), gok_b(own, red, i, nv, k, vm, hg)), gok_d(own, red, i, nv, k, vm, hg), below_mono(ST.somes(vm), k, SV.neqs(full), gok_b(own, red, i, nv, k, vm, hg), lt_le(k, SV.neqs(full), hlt)), hlt, hv, hn), L.band_i(okown(own, red, i, k), allown(own, red, i, lk), okown_self(own, red, i, k, hown), allown_subl(own, red, i, lk, ST.somes(vm), L.look_subl(vm, vis, D.vo_a(vm, adj, Nil{}, f, vis, hv)), gok_o(own, red, i, nv, k, vm, hg))))))

def gend(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +k: Nat, +kend: Nat, +vm: List<&2, Maybe<&2, Nat>>, hk: {Nat.add(k, 0n) == kend : Nat}, +hg: {SV.band(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c)) == True{} : Bool}) -> {SV.band(gok(own, red, i, nv, kend, vm), SV.eq(SV.len(ST.somes(vm)), c)) == True{} : Bool}:
  %Equal.trans(Nat, k, Nat.add(k, 0n), kend, LN.add_zero(k), hk) : {SV.band(gok(own, red, i, nv, _, vm), SV.eq(SV.len(ST.somes(vm)), c)) == True{} : Bool}
  L.band_i(gok(own, red, i, nv, k, vm), SV.eq(SV.len(ST.somes(vm)), c), L.band_l(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c), hg), %Equal.sym(Nat, SV.len(ST.somes(vm)), Nat.add(SV.len(ST.somes(vm)), 0n), LN.add_zero(SV.len(ST.somes(vm)))) : {SV.eq(_, c) == True{} : Bool}
    L.band_r(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c), hg))

# the n equations k, k + 1, ... of constraint i, from the state st
def grp_ok(n: Nat, +k: Nat, +f: Nat, st: ST.GS, +full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +kend: Nat, +o: List<&2, Nat>, +hd: {drop(k, own) == SV.cat(SV.reps(n, i), o) : List<&2, Nat>}, +hk: {Nat.add(k, n) == kend : Nat}, +hK: {KA.natle(kend, SV.neqs(full)) == True{} : Bool}, +ha: {D.adjb(ST.adj(full), nv) == True{} : Bool}, +hf: {KA.natle(1n+nv, f) == True{} : Bool}, +hg: {gin(full, own, red, i, nv, c, k, n, st) == True{} : Bool}) -> {gres(full, own, red, i, nv, c, kend, ST.grp(n, k, ST.adj(full), f, st)) == True{} : Bool}:
  match n st:
    case 0n ST.GOk{+vm}:
      gend(full, own, red, i, nv, c, k, kend, vm, hk, hg)
    case 0n ST.GFail{r}:
      hg
    case 1n++m ST.GOk{+vm}:
      +adj = ST.adj(full)
      +hgok = L.band_l(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 1n+m), c), hg)
      +hm = gok_m(own, red, i, nv, k, vm, hgok)
      +a = ST.search(f, adj, vm, k)
      grp_ok(m, 1n+k, f, ST.gstep(k, a, vm), full, own, red, i, nv, c, kend, o, drop_step(k, own, m, i, o, hd), LN.succ_add(k, m, kend, hk), hK, ha, hf, grp_step(full, own, red, i, nv, c, k, m, f, vm, a, D.search_ok(f, adj, vm, k, below_notmem(k, ST.somes(vm), gok_b(own, red, i, nv, k, vm, hgok)), gok_d(own, red, i, nv, k, vm, hgok), adjb_vm(adj, vm, nv, hm, ha), fuel_vm(vm, nv, f, hm, hf)), hgok, L.band_r(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 1n+m), c), hg), own_at(k, own, m, i, o, hd), lt_grp(k, m, kend, SV.neqs(full), hk, hK)))
    case 1n++m ST.GFail{r}:
      hg

# The red list's shape
# --------------------
# The walk only ever puts the current position in front of the red list.

# every x of xs is in red or at least i
def allge(xs: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(SV.bor(SV.mem(x, red), KA.natle(i, x)), allge(t, red, i))

def allge_refl(xs: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +h: {L.subl(xs, red) == True{} : Bool}) -> {allge(xs, red, i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, red), KA.natle(i, x)), allge(t, red, i), L.bor_l(SV.mem(x, red), KA.natle(i, x), L.subl_hd(x, t, red, h)), allge_refl(t, red, i, L.subl_tl(x, t, red, h)))

def or_le(a: Bool, +x: Nat, +i: Nat, h: {SV.bor(a, KA.natle(1n+i, x)) == True{} : Bool}) -> {SV.bor(a, KA.natle(i, x)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      KA.natle_pred(i, x, h)

def allge_weak(xs: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +h: {allge(xs, red, 1n+i) == True{} : Bool}) -> {allge(xs, red, i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, red), KA.natle(i, x)), allge(t, red, i), or_le(SV.mem(x, red), x, i, L.band_l(SV.bor(SV.mem(x, red), KA.natle(1n+i, x)), allge(t, red, 1n+i), h)), allge_weak(t, red, i, L.band_r(SV.bor(SV.mem(x, red), KA.natle(1n+i, x)), allge(t, red, 1n+i), h)))

def ge_or.go(+x: Nat, +i: Nat, +red: List<&2, Nat>, c: Bool, e: {SV.eq(x, i) == c : Bool}, h: {SV.bor(c, SV.mem(x, red)) == True{} : Bool}) -> {SV.bor(SV.mem(x, red), KA.natle(i, x)) == True{} : Bool}:
  match c:
    case True{}:
      L.bor_r(SV.mem(x, red), KA.natle(i, x), %Equal.sym(Nat, x, i, L.eq_ok(x, i, e)) : {KA.natle(i, _) == True{} : Bool}
        KA.natle_refl(i))
    case False{}:
      L.bor_l(SV.mem(x, red), KA.natle(i, x), h)

def ge_step(+x: Nat, +i: Nat, +red: List<&2, Nat>, +red2: List<&2, Nat>, c: Bool, e: {SV.mem(x, red2) == c : Bool}, h: {SV.bor(c, KA.natle(1n+i, x)) == True{} : Bool}, hs: {L.subl(red2, Con{i, red}) == True{} : Bool}) -> {SV.bor(SV.mem(x, red), KA.natle(i, x)) == True{} : Bool}:
  match c:
    case True{}:
      ge_or.go(x, i, red, SV.eq(x, i), {==}, L.subl_mem(x, red2, Con{i, red}, e, hs))
    case False{}:
      L.bor_r(SV.mem(x, red), KA.natle(i, x), KA.natle_pred(i, x, h))

def allge_step(xs: List<&2, Nat>, +red: List<&2, Nat>, +red2: List<&2, Nat>, +i: Nat, +h: {allge(xs, red2, 1n+i) == True{} : Bool}, +hs: {L.subl(red2, Con{i, red}) == True{} : Bool}) -> {allge(xs, red, i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, red), KA.natle(i, x)), allge(t, red, i), ge_step(x, i, red, red2, SV.mem(x, red2), {==}, L.band_l(SV.bor(SV.mem(x, red2), KA.natle(1n+i, x)), allge(t, red2, 1n+i), h), hs), allge_step(t, red, red2, i, L.band_r(SV.bor(SV.mem(x, red2), KA.natle(1n+i, x)), allge(t, red2, 1n+i), h), hs))

def ge_not.go(+i: Nat, +x: Nat, +red: List<&2, Nat>, c: Bool, e: {SV.eq(i, x) == c : Bool}, hx: {SV.bor(SV.mem(x, red), KA.natle(1n+i, x)) == True{} : Bool}, hn: {SV.mem(i, red) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.natlt_irr(i, L.bor_rf(SV.mem(i, red), KA.natle(1n+i, i), %Equal.sym(Nat, i, x, L.eq_ok(i, x, e)) : {SV.bor(SV.mem(_, red), KA.natle(1n+i, _)) == True{} : Bool}
        hx, hn)))
    case False{}:
      {==}

# i is not red before position i + 1 ... nor after: i is not in xs
def allge_notmem(xs: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +h: {allge(xs, red, 1n+i) == True{} : Bool}, +hn: {SV.mem(i, red) == False{} : Bool}) -> {SV.mem(i, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.bor_f(SV.eq(i, x), SV.mem(i, t), ge_not.go(i, x, red, SV.eq(i, x), {==}, L.band_l(SV.bor(SV.mem(x, red), KA.natle(1n+i, x)), allge(t, red, 1n+i), h), hn), allge_notmem(t, red, i, L.band_r(SV.bor(SV.mem(x, red), KA.natle(1n+i, x)), allge(t, red, 1n+i), h), hn))

# The walk
# --------

# at constraint i: every matched equation's owner is earlier and not red
def pre(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+m, t}:
      SV.band(SV.band(SV.lt(SV.nth(own, m), i), SV.bnot(SV.mem(SV.nth(own, m), red))), pre(own, red, i, t))

# no entry of xs is owned by a constraint in red
def nred(+own: List<&2, Nat>, +red: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+m, t}:
      SV.band(SV.bnot(SV.mem(SV.nth(own, m), red)), nred(own, red, t))

def pre_nred(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +h: {pre(own, red, i, xs) == True{} : Bool}) -> {nred(own, red, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      L.band_i(SV.bnot(SV.mem(SV.nth(own, m), red)), nred(own, red, t), L.band_r(SV.lt(SV.nth(own, m), i), SV.bnot(SV.mem(SV.nth(own, m), red)), L.band_l(SV.band(SV.lt(SV.nth(own, m), i), SV.bnot(SV.mem(SV.nth(own, m), red))), pre(own, red, i, t), h)), pre_nred(own, red, i, t, L.band_r(SV.band(SV.lt(SV.nth(own, m), i), SV.bnot(SV.mem(SV.nth(own, m), red))), pre(own, red, i, t), h)))

# below a, a <= b: below b
def below_le(xs: List<&2, Nat>, +a: Nat, +b: Nat, +h: {SV.below(xs, a) == True{} : Bool}, +hab: {KA.natle(a, b) == True{} : Bool}) -> {SV.below(xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.lt(x, b), SV.below(t, b), (%Equal.sym(Bool, SV.lt(x, b), KA.natle(1n+x, b), L.lt_sv(x, b)) : {_ == True{} : Bool}
        KA.natle_trans(1n+x, a, b, D.below_hd(x, t, a, h), hab)), below_le(t, a, b, D.below_tl(x, t, a, h), hab))

# the red constraints (newest first) and why: each one's record is good,
# with the constraints red before it, which are all earlier
def good(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, rs: List<&2, Nat>, ws: List<&2, WY.Why>) -> Bool:
  match rs ws:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{c, rt} Nil{}:
      False{}
    case Con{+c, +rt} Con{WY.Why{+j, +s, +w}, yt}:
      SV.band(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))))

def lt_up(+o: Nat, +i: Nat, h: {SV.lt(o, i) == True{} : Bool}) -> {SV.lt(o, 1n+i) == True{} : Bool}:
  %Equal.sym(Bool, SV.lt(o, 1n+i), KA.natle(1n+o, 1n+i), L.lt_sv(o, 1n+i)) : {_ == True{} : Bool}
  KA.natle_succ(1n+o, i, %L.lt_sv(o, i) : {_ == True{} : Bool}
    h)

def lt_ne.go(+o: Nat, +i: Nat, c: Bool, e: {SV.eq(o, i) == c : Bool}, h: {SV.lt(o, i) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.natlt_irr(i, %L.lt_sv(i, i) : {_ == True{} : Bool}
        %L.eq_ok(o, i, e) : {SV.lt(_, i) == True{} : Bool}
          h))
    case False{}:
      {==}

def lt_ne(+o: Nat, +i: Nat, h: {SV.lt(o, i) == True{} : Bool}) -> {SV.eq(o, i) == False{} : Bool}:
  lt_ne.go(o, i, SV.eq(o, i), {==}, h)

def pre_allown(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +h: {pre(own, red, i, xs) == True{} : Bool}) -> {allown(own, red, i, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      L.band_i(okown(own, red, i, m), allown(own, red, i, t), L.bor_r(SV.eq(o, i), SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), L.band_l(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)), pre_allown(own, red, i, t, L.band_r(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)))

def pre_weak(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +h: {pre(own, red, i, xs) == True{} : Bool}) -> {pre(own, red, 1n+i, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      +hm = L.band_l(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)
      L.band_i(SV.band(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, red))), pre(own, red, 1n+i, t), L.band_i(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, red)), lt_up(o, i, L.band_l(SV.lt(o, i), SV.bnot(SV.mem(o, red)), hm)), L.band_r(SV.lt(o, i), SV.bnot(SV.mem(o, red)), hm)), pre_weak(own, red, i, t, L.band_r(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)))

# after constraint i failed: matched equations are still earlier and not red
def pre_fail(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +h: {pre(own, red, i, xs) == True{} : Bool}) -> {pre(own, Con{i, red}, 1n+i, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      +hm = L.band_l(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)
      +hl = L.band_l(SV.lt(o, i), SV.bnot(SV.mem(o, red)), hm)
      L.band_i(SV.band(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, Con{i, red}))), pre(own, Con{i, red}, 1n+i, t), L.band_i(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, Con{i, red})), lt_up(o, i, hl), L.bnot_t(SV.mem(o, Con{i, red}), L.bor_f(SV.eq(o, i), SV.mem(o, red), lt_ne(o, i, hl), L.bnot_f(SV.mem(o, red), L.band_r(SV.lt(o, i), SV.bnot(SV.mem(o, red)), hm))))), pre_fail(own, red, i, t, L.band_r(SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red))), pre(own, red, i, t), h)))

def okstep.go(+o: Nat, +i: Nat, +red: List<&2, Nat>, c: Bool, e: {SV.eq(o, i) == c : Bool}, +h: {SV.bor(c, SV.band(SV.lt(o, i), SV.bnot(SV.mem(o, red)))) == True{} : Bool}, hr: {SV.below(red, i) == True{} : Bool}) -> {SV.band(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, red))) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, o, i, L.eq_ok(o, i, e)) : {SV.band(SV.lt(_, 1n+i), SV.bnot(SV.mem(_, red))) == True{} : Bool}
      L.band_i(SV.lt(i, 1n+i), SV.bnot(SV.mem(i, red)), lt_succ(i), L.bnot_t(SV.mem(i, red), below_notmem(i, red, hr)))
    case False{}:
      L.band_i(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, red)), lt_up(o, i, L.band_l(SV.lt(o, i), SV.bnot(SV.mem(o, red)), h)), L.band_r(SV.lt(o, i), SV.bnot(SV.mem(o, red)), h))

# after constraint i was kept: matched equations are earlier than i + 1 and
# not red
def own_step(+own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>, +h: {allown(own, red, i, xs) == True{} : Bool}, +hr: {SV.below(red, i) == True{} : Bool}) -> {pre(own, red, 1n+i, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      L.band_i(SV.band(SV.lt(o, 1n+i), SV.bnot(SV.mem(o, red))), pre(own, red, 1n+i, t), okstep.go(o, i, red, SV.eq(o, i), {==}, L.band_l(okown(own, red, i, m), allown(own, red, i, t), h), hr), own_step(own, red, i, t, L.band_r(okown(own, red, i, m), allown(own, red, i, t), h), hr))

def neqs_cat(a: List<&2, E.QExpr>, +b: List<&2, E.QExpr>) -> {SV.neqs(SK.cat(a, b)) == Nat.add(SV.neqs(a), SV.neqs(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat, SV.neqs(SK.cat(t, b)), Nat.add(SV.neqs(t), SV.neqs(b)), neqs_cat(t, b)) : {1n+_ == 1n+Nat.add(SV.neqs(t), SV.neqs(b)) : Nat}
      {==}

def hd_step(+k: Nat, +own: List<&2, Nat>, +es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, hd: {drop(k, own) == SV.owners.go(es, Con{SK.Rec{id, False{}, kd}, t}, i) : List<&2, Nat>}) -> {drop(Nat.add(k, SV.neqs(SK.Constraint.eqs(es, kd))), own) == SV.owners.go(es, t, 1n+i) : List<&2, Nat>}:
  +n = SV.neqs(SK.Constraint.eqs(es, kd))
  +o = SV.owners.go(es, t, 1n+i)
  %Equal.sym(List<&2, Nat>, drop(Nat.add(k, n), own), drop(n, drop(k, own)), drop_add(k, n, own)) : {_ == o : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, drop(k, own), SV.cat(SV.reps(n, i), o), hd) : {drop(n, _) == o : List<&2, Nat>}
  drop_reps(n, i, o)

def hk_step(+k: Nat, +es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +nq: Nat, hk: {KA.natle(Nat.add(k, SV.neqs(SK.Sketch.eqs.go(es, Con{SK.Rec{id, False{}, kd}, t}))), nq) == True{} : Bool}) -> {KA.natle(Nat.add(Nat.add(k, SV.neqs(SK.Constraint.eqs(es, kd))), SV.neqs(SK.Sketch.eqs.go(es, t))), nq) == True{} : Bool}:
  +n = SV.neqs(SK.Constraint.eqs(es, kd))
  +r = SV.neqs(SK.Sketch.eqs.go(es, t))
  %LN.add_assoc(k, n, r) : {KA.natle(_, nq) == True{} : Bool}
  %neqs_cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t)) : {KA.natle(Nat.add(k, _), nq) == True{} : Bool}
  hk

def somes_nones(n: Nat) -> {ST.somes(ST.nones(n)) == Nil{} : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      somes_nones(m)

def mlen_nones(n: Nat) -> {L.mlen(ST.nones(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      %Equal.sym(Nat, L.mlen(ST.nones(m)), m, mlen_nones(m)) : {1n+_ == 1n+m : Nat}
      {==}

def sk.ents(sk: SK.Sketch) -> List<&2, SK.Ent>:
  match sk:
    case SK.Sketch{vs, es, cs}:
      es

def sk.cons(sk: SK.Sketch) -> List<&2, SK.Rec>:
  match sk:
    case SK.Sketch{vs, es, cs}:
      cs

def cnt0(+nv: Nat, +x: Nat) -> {Nat.add(SV.len(ST.somes(ST.nones(nv))), x) == x : Nat}:
  %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, somes_nones(nv)) : {Nat.add(SV.len(_), x) == x : Nat}
  {==}

def q(xs: List<&2, Nat>, +rs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(SV.bor(SV.mem(x, rs), SV.below(rs, x)), q(t, rs))

def q_of(xs: List<&2, Nat>, +rs: List<&2, Nat>, +h: {L.subl(xs, rs) == True{} : Bool}) -> {q(xs, rs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, rs), SV.below(rs, x)), q(t, rs), L.bor_l(SV.mem(x, rs), SV.below(rs, x), L.subl_hd(x, t, rs, h)), q_of(t, rs, L.subl_tl(x, t, rs, h)))

def q2(a: Bool, +c: Nat, +x: Nat, +rt: List<&2, Nat>, h: {SV.bor(a, SV.band(SV.lt(c, x), SV.below(rt, x))) == True{} : Bool}) -> {SV.bor(a, SV.below(rt, x)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.band_r(SV.lt(c, x), SV.below(rt, x), h)

def q1(+x: Nat, +c: Nat, +rt: List<&2, Nat>, b: Bool, e: {SV.eq(x, c) == b : Bool}, h: {SV.bor(SV.bor(b, SV.mem(x, rt)), SV.band(SV.lt(c, x), SV.below(rt, x))) == True{} : Bool}, hb: {SV.below(rt, c) == True{} : Bool}) -> {SV.bor(SV.mem(x, rt), SV.below(rt, x)) == True{} : Bool}:
  match b:
    case True{}:
      L.bor_r(SV.mem(x, rt), SV.below(rt, x), %Equal.sym(Nat, x, c, L.eq_ok(x, c, e)) : {SV.below(rt, _) == True{} : Bool}
        hb)
    case False{}:
      q2(SV.mem(x, rt), c, x, rt, h)

def q_step(xs: List<&2, Nat>, +c: Nat, +rt: List<&2, Nat>, +h: {q(xs, Con{c, rt}) == True{} : Bool}, +hb: {SV.below(rt, c) == True{} : Bool}) -> {q(xs, rt) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, rt), SV.below(rt, x)), q(t, rt), q1(x, c, rt, SV.eq(x, c), {==}, L.band_l(SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)), q(t, Con{c, rt}), h), hb), q_step(t, c, rt, L.band_r(SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)), q(t, Con{c, rt}), h), hb))

# o < c and o not in rt, while every x of xs is in c :: rt or above it: o is
# not in xs
def notr.ho(+o: Nat, +x: Nat, +c: Nat, +rt: List<&2, Nat>, e: {SV.eq(o, x) == True{} : Bool}, hx: {SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)) == True{} : Bool}) -> {SV.bor(SV.mem(o, Con{c, rt}), SV.below(Con{c, rt}, o)) == True{} : Bool}:
  %Equal.sym(Nat, o, x, L.eq_ok(o, x, e)) : {SV.bor(SV.mem(_, Con{c, rt}), SV.below(Con{c, rt}, _)) == True{} : Bool}
  hx

def notr.go(+o: Nat, +c: Nat, +rt: List<&2, Nat>, +x: Nat, b: Bool, e: {SV.eq(o, x) == b : Bool}, hx: {SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)) == True{} : Bool}, +hl: {SV.lt(o, c) == True{} : Bool}, hn: {SV.mem(o, rt) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +ho = notr.ho(o, x, c, rt, e, hx)
      absurd({True{} == False{} : Bool}, KA.natlt_irr(o, KA.natle_trans(1n+o, 1n+c, o, KA.natle_succ(1n+o, c, %L.lt_sv(o, c) : {_ == True{} : Bool}
        hl), %L.lt_sv(c, o) : {_ == True{} : Bool}
        L.band_l(SV.lt(c, o), SV.below(rt, o), L.bor_rf(SV.mem(o, Con{c, rt}), SV.below(Con{c, rt}, o), ho, L.bor_f(SV.eq(o, c), SV.mem(o, rt), lt_ne(o, c, hl), hn))))))
    case False{}:
      {==}

def notr(+o: Nat, +c: Nat, +rt: List<&2, Nat>, xs: List<&2, Nat>, +h: {q(xs, Con{c, rt}) == True{} : Bool}, +hl: {SV.lt(o, c) == True{} : Bool}, +hn: {SV.mem(o, rt) == False{} : Bool}) -> {SV.mem(o, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.bor_f(SV.eq(o, x), SV.mem(o, t), notr.go(o, c, rt, x, SV.eq(o, x), {==}, L.band_l(SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)), q(t, Con{c, rt}), h), hl, hn), notr(o, c, rt, t, L.band_r(SV.bor(SV.mem(x, Con{c, rt}), SV.below(Con{c, rt}, x)), q(t, Con{c, rt}), h), hl, hn))

def clean1(a: Bool, +o: Nat, +c: Nat, +rt: List<&2, Nat>, +r: List<&2, Nat>, +h: {SV.bor(a, SV.band(SV.lt(o, c), SV.bnot(SV.mem(o, rt)))) == True{} : Bool}, hq: {q(r, Con{c, rt}) == True{} : Bool}) -> {SV.bor(a, SV.bnot(SV.mem(o, r))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.bnot_t(SV.mem(o, r), notr(o, c, rt, r, hq, L.band_l(SV.lt(o, c), SV.bnot(SV.mem(o, rt)), h), L.bnot_f(SV.mem(o, rt), L.band_r(SV.lt(o, c), SV.bnot(SV.mem(o, rt)), h))))

# the witness is clean against the whole red list r
def clean_of(+own: List<&2, Nat>, +r: List<&2, Nat>, +c: Nat, +rt: List<&2, Nat>, s: List<&2, Nat>, +ha: {allown(own, rt, c, s) == True{} : Bool}, +hq: {q(r, Con{c, rt}) == True{} : Bool}) -> {WY.clean(own, r, c, s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      L.band_i(SV.bor(SV.eq(o, c), SV.bnot(SV.mem(o, r))), WY.clean(own, r, c, t), clean1(SV.eq(o, c), o, c, rt, r, L.band_l(okown(own, rt, c, m), allown(own, rt, c, t), ha), hq), clean_of(own, r, c, rt, t, L.band_r(okown(own, rt, c, m), allown(own, rt, c, t), ha), hq))

def expl_go(+sk: SK.Sketch, +r: List<&2, Nat>, rs: List<&2, Nat>, ws: List<&2, WY.Why>, +hg: {good(SK.Sketch.eqs(sk), SV.owners(sk), rs, ws) == True{} : Bool}, +hq: {q(r, rs) == True{} : Bool}) -> {WY.explained.go(sk, r, rs, ws) == True{} : Bool}:
  match rs ws:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      absurd({False{} == True{} : Bool}, KA.ft(hg))
    case Con{c, rt} Nil{}:
      absurd({False{} == True{} : Bool}, KA.ft(hg))
    case Con{+c, +rt} Con{WY.Why{+j, +s, +w}, +yt}:
      +full = SK.Sketch.eqs(sk)
      +own = SV.owners(sk)
      +g1 = L.band_r(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))), hg)
      +g2 = L.band_r(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)))), g1)
      +g3 = L.band_r(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))), g2)
      +g4 = L.band_r(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)), g3)
      +hb = L.band_l(SV.below(rt, c), good(full, own, rt, yt), g4)
      L.band_i(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(WY.clean(own, r, c, s), WY.explained.go(sk, r, rt, yt)))), L.band_l(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))), hg), L.band_i(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(WY.clean(own, r, c, s), WY.explained.go(sk, r, rt, yt))), L.band_l(SV.mem(j, s), SV.band(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)))), g1), L.band_i(WY.overdet(full, s, w), SV.band(WY.clean(own, r, c, s), WY.explained.go(sk, r, rt, yt)), L.band_l(WY.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))), g2), L.band_i(WY.clean(own, r, c, s), WY.explained.go(sk, r, rt, yt), clean_of(own, r, c, rt, s, L.band_l(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)), g3), hq), expl_go(sk, r, rt, yt, L.band_r(SV.below(rt, c), good(full, own, rt, yt), g4), q_step(r, c, rt, hq, hb))))))

# good records explain the red constraints
def explained_of(+sk: SK.Sketch, +r: List<&2, Nat>, +ws: List<&2, WY.Why>, hg: {good(SK.Sketch.eqs(sk), SV.owners(sk), r, ws) == True{} : Bool}) -> {WY.explained(sk, r, ws) == True{} : Bool}:
  expl_go(sk, r, r, ws, hg, q_of(r, r, L.subl_refl(r)))
