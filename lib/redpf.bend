# bend-cad: the red stage (lib/solve.bend: kuhnc, run), for the solver's
# totality (ROADMAP: solve_total). Proofs only.
#
# The red stage walks the constraints; constraint i (counting driven ones)
# owns the equations k .. k + n - 1 of the sketch's exact system, and they
# are matched as a unit (lib/struct.bend: grp). Through the walk:
# - the matching's matched equations are distinct and below k, and each
#   is owned by an earlier constraint that is not red;
# - each red constraint's record is good: its equation is its own, its
#   witness over-determines its variables (lib/dfspf.bend: wit_ok), and
#   every equation of the witness is the red constraint's own or owned by
#   an earlier constraint that was not red at the time;
# - at the end there are as many matched equations as the kept system has.
#
# own is the sketch's owner list (spec/solve.bend: owners); at constraint i
# the equations from k on are owned as the rest of the walk says
# (drop(k, own) is owners.go of the remaining constraints from i).

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D
import ./solve.bend as SO

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
        L.le_trans(1n+x, a, b, %L.lt_sv(x, a) : {_ == True{} : Bool}
          L.band_l(SV.lt(x, a), SV.below(t, a), h), hab), below_mono(t, a, b, L.band_r(SV.lt(x, a), SV.below(t, a), h), hab))

def below_notmem.go(+k: Nat, +xs: List<&2, Nat>, c: Bool, e: {SV.mem(k, xs) == c : Bool}, h: {SV.below(xs, k) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, L.lt_irr(k, %L.lt_sv(k, k) : {_ == True{} : Bool}
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
      absurd({okown(own, red, i, m) == True{} : Bool}, L.ft(hm))
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
      SV.band(SV.eq(SV.nth(own, j), i), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), allown(own, red, i, s))))

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
  L.le_trans(1n+k, kend, nq, %hk : {KA.natle(1n+k, _) == True{} : Bool}
    %LN.add_succ(k, m) : {KA.natle(1n+k, _) == True{} : Bool}
      L.le_add_r(k, m), hK)

def lt_le(+k: Nat, +nq: Nat, h: {SV.lt(k, nq) == True{} : Bool}) -> {KA.natle(k, nq) == True{} : Bool}:
  L.le_pred(k, nq, %L.lt_sv(k, nq) : {_ == True{} : Bool}
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
      L.band_i(gok(own, red, i, nv, 1n+k, vm2), SV.eq(Nat.add(SV.len(ST.somes(vm2)), m), c), gok_mk(own, red, i, nv, 1n+k, vm2, D.so_d(vm, k, vm2, hres), D.below_subl(ST.somes(vm2), Con{k, ST.somes(vm)}, 1n+k, hs, L.band_i(SV.lt(k, 1n+k), SV.below(ST.somes(vm), 1n+k), lt_succ(k), below_mono(ST.somes(vm), k, 1n+k, gok_b(own, red, i, nv, k, vm, hg), L.le_succ(k, k, L.le_refl(k))))), Equal.trans(Nat, L.mlen(vm2), L.mlen(vm), nv, D.so_m(vm, k, vm2, hres), gok_m(own, red, i, nv, k, vm, hg)), allown_subl(own, red, i, ST.somes(vm2), Con{k, ST.somes(vm)}, hs, L.band_i(okown(own, red, i, k), allown(own, red, i, ST.somes(vm)), okown_self(own, red, i, k, hown), gok_o(own, red, i, nv, k, vm, hg)))), cnt_step(SV.len(ST.somes(vm)), m, c, SV.len(ST.somes(vm2)), D.so_n(vm, k, vm2, hres), hc))
    case ST.DS{False{}, vm2, +vis}:
      +adj = ST.adj(full)
      +hv = L.band_l(D.vis_ok(vm, adj, Nil{}, f, vis), SV.band(L.subl(ST.nthl(adj, k), vis), True{}), hres)
      +hn = L.band_l(L.subl(ST.nthl(adj, k), vis), True{}, L.band_r(D.vis_ok(vm, adj, Nil{}, f, vis), SV.band(L.subl(ST.nthl(adj, k), vis), True{}), hres))
      +lk = ST.look(vm, vis)
      L.band_i(SV.eq(SV.nth(own, k), i), SV.band(SV.mem(k, Con{k, lk}), SV.band(SV.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk}))), D.eq_of(SV.nth(own, k), i, hown), L.band_i(SV.mem(k, Con{k, lk}), SV.band(SV.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk})), L.mem_hd(k, lk), L.band_i(SV.overdet(full, Con{k, lk}, vis), allown(own, red, i, Con{k, lk}), D.wit_ok(full, vm, k, f, vis, below_notmem(k, ST.somes(vm), gok_b(own, red, i, nv, k, vm, hg)), gok_d(own, red, i, nv, k, vm, hg), below_mono(ST.somes(vm), k, SV.neqs(full), gok_b(own, red, i, nv, k, vm, hg), lt_le(k, SV.neqs(full), hlt)), hlt, hv, hn), L.band_i(okown(own, red, i, k), allown(own, red, i, lk), okown_self(own, red, i, k, hown), allown_subl(own, red, i, lk, ST.somes(vm), L.look_subl(vm, vis, D.vo_a(vm, adj, Nil{}, f, vis, hv)), gok_o(own, red, i, nv, k, vm, hg))))))

def gend(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +i: Nat, +nv: Nat, +c: Nat, +k: Nat, +kend: Nat, +vm: List<&2, Maybe<&2, Nat>>, hk: {Nat.add(k, 0n) == kend : Nat}, +hg: {SV.band(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c)) == True{} : Bool}) -> {SV.band(gok(own, red, i, nv, kend, vm), SV.eq(SV.len(ST.somes(vm)), c)) == True{} : Bool}:
  %Equal.trans(Nat, k, Nat.add(k, 0n), kend, LN.add_zero(k), hk) : {SV.band(gok(own, red, i, nv, _, vm), SV.eq(SV.len(ST.somes(vm)), c)) == True{} : Bool}
  L.band_i(gok(own, red, i, nv, k, vm), SV.eq(SV.len(ST.somes(vm)), c), L.band_l(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c), hg), %Equal.sym(Nat, SV.len(ST.somes(vm)), Nat.add(SV.len(ST.somes(vm)), 0n), LN.add_zero(SV.len(ST.somes(vm)))) : {SV.eq(_, c) == True{} : Bool}
    L.band_r(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 0n), c), hg))

def kend_step(+k: Nat, +m: Nat, +kend: Nat, hk: {Nat.add(k, 1n+m) == kend : Nat}) -> {Nat.add(1n+k, m) == kend : Nat}:
  %Equal.sym(Nat, 1n+Nat.add(k, m), Nat.add(k, 1n+m), LN.add_succ(k, m)) : {_ == kend : Nat}
  hk

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
      grp_ok(m, 1n+k, f, ST.gstep(k, a, vm), full, own, red, i, nv, c, kend, o, drop_step(k, own, m, i, o, hd), kend_step(k, m, kend, hk), hK, ha, hf, grp_step(full, own, red, i, nv, c, k, m, f, vm, a, D.search_ok(f, adj, vm, k, below_notmem(k, ST.somes(vm), gok_b(own, red, i, nv, k, vm, hgok)), gok_d(own, red, i, nv, k, vm, hgok), adjb_vm(adj, vm, nv, hm, ha), fuel_vm(vm, nv, f, hm, hf)), hgok, L.band_r(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(SV.len(ST.somes(vm)), 1n+m), c), hg), own_at(k, own, m, i, o, hd), lt_grp(k, m, kend, SV.neqs(full), hk, hK)))
    case 1n++m ST.GFail{r}:
      hg

# The red list's shape
# --------------------
# The walk only ever puts the current position in front of the red list.

def cfin_s1(+i: Nat, g: ST.GS, st: SO.CS) -> {L.subl(SO.CS.red(st), SO.CS.red(SO.cfin(i, g, st))) == True{} : Bool}:
  match g st:
    case ST.GOk{vm2} SO.CS{vm, red, why}:
      L.subl_refl(red)
    case ST.GFail{ST.Red{j, s, w}} SO.CS{vm, +red, why}:
      L.subl_cons_r(red, i, red, L.subl_refl(red))

def cfin_s2(+i: Nat, g: ST.GS, st: SO.CS) -> {L.subl(SO.CS.red(SO.cfin(i, g, st)), Con{i, SO.CS.red(st)}) == True{} : Bool}:
  match g st:
    case ST.GOk{vm2} SO.CS{vm, +red, why}:
      L.subl_cons_r(red, i, red, L.subl_refl(red))
    case ST.GFail{ST.Red{j, s, w}} SO.CS{vm, +red, why}:
      L.subl_refl(Con{i, red})

# the red list only grows
def shape1(cs: List<&2, SK.Rec>, +es: List<&2, SK.Ent>, +i: Nat, +k: Nat, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: SO.CS) -> {L.subl(SO.CS.red(st), SO.CS.red(SO.kuhnc(cs, es, i, k, adj, f, st))) == True{} : Bool}:
  match cs:
    case Nil{}:
      L.subl_refl(SO.CS.red(st))
    case Con{SK.Rec{id, True{}, kd}, +t}:
      shape1(t, es, 1n+i, k, adj, f, st)
    case Con{SK.Rec{id, False{}, +kd}, +t}:
      +n = SV.neqs(SK.Constraint.eqs(es, kd))
      +st2 = SO.cfin(i, ST.grp(n, k, adj, f, ST.GOk{SO.CS.vm(st)}), st)
      L.subl_trans(SO.CS.red(st), SO.CS.red(st2), SO.CS.red(SO.kuhnc(t, es, 1n+i, Nat.add(k, n), adj, f, st2)), cfin_s1(i, ST.grp(n, k, adj, f, ST.GOk{SO.CS.vm(st)}), st), shape1(t, es, 1n+i, Nat.add(k, n), adj, f, st2))

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
      L.le_pred(i, x, h)

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
        L.le_refl(i))
    case False{}:
      L.bor_l(SV.mem(x, red), KA.natle(i, x), h)

def ge_step(+x: Nat, +i: Nat, +red: List<&2, Nat>, +red2: List<&2, Nat>, c: Bool, e: {SV.mem(x, red2) == c : Bool}, h: {SV.bor(c, KA.natle(1n+i, x)) == True{} : Bool}, hs: {L.subl(red2, Con{i, red}) == True{} : Bool}) -> {SV.bor(SV.mem(x, red), KA.natle(i, x)) == True{} : Bool}:
  match c:
    case True{}:
      ge_or.go(x, i, red, SV.eq(x, i), {==}, L.subl_mem(x, red2, Con{i, red}, e, hs))
    case False{}:
      L.bor_r(SV.mem(x, red), KA.natle(i, x), L.le_pred(i, x, h))

def allge_step(xs: List<&2, Nat>, +red: List<&2, Nat>, +red2: List<&2, Nat>, +i: Nat, +h: {allge(xs, red2, 1n+i) == True{} : Bool}, +hs: {L.subl(red2, Con{i, red}) == True{} : Bool}) -> {allge(xs, red, i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bor(SV.mem(x, red), KA.natle(i, x)), allge(t, red, i), ge_step(x, i, red, red2, SV.mem(x, red2), {==}, L.band_l(SV.bor(SV.mem(x, red2), KA.natle(1n+i, x)), allge(t, red2, 1n+i), h), hs), allge_step(t, red, red2, i, L.band_r(SV.bor(SV.mem(x, red2), KA.natle(1n+i, x)), allge(t, red2, 1n+i), h), hs))

# the red list grows only by positions from i on
def shape2(cs: List<&2, SK.Rec>, +es: List<&2, SK.Ent>, +i: Nat, +k: Nat, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: SO.CS) -> {allge(SO.CS.red(SO.kuhnc(cs, es, i, k, adj, f, st)), SO.CS.red(st), i) == True{} : Bool}:
  match cs:
    case Nil{}:
      allge_refl(SO.CS.red(st), SO.CS.red(st), i, L.subl_refl(SO.CS.red(st)))
    case Con{SK.Rec{id, True{}, kd}, +t}:
      allge_weak(SO.CS.red(SO.kuhnc(t, es, 1n+i, k, adj, f, st)), SO.CS.red(st), i, shape2(t, es, 1n+i, k, adj, f, st))
    case Con{SK.Rec{id, False{}, +kd}, +t}:
      +n = SV.neqs(SK.Constraint.eqs(es, kd))
      +st2 = SO.cfin(i, ST.grp(n, k, adj, f, ST.GOk{SO.CS.vm(st)}), st)
      allge_step(SO.CS.red(SO.kuhnc(t, es, 1n+i, Nat.add(k, n), adj, f, st2)), SO.CS.red(st), SO.CS.red(st2), i, shape2(t, es, 1n+i, Nat.add(k, n), adj, f, st2), cfin_s2(i, ST.grp(n, k, adj, f, ST.GOk{SO.CS.vm(st)}), st))

def ge_not.go(+i: Nat, +x: Nat, +red: List<&2, Nat>, c: Bool, e: {SV.eq(i, x) == c : Bool}, hx: {SV.bor(SV.mem(x, red), KA.natle(1n+i, x)) == True{} : Bool}, hn: {SV.mem(i, red) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, L.lt_irr(i, L.bor_rf(SV.mem(i, red), KA.natle(1n+i, i), %Equal.sym(Nat, i, x, L.eq_ok(i, x, e)) : {SV.bor(SV.mem(_, red), KA.natle(1n+i, _)) == True{} : Bool}
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
        L.le_trans(1n+x, a, b, D.below_hd(x, t, a, h), hab)), below_le(t, a, b, D.below_tl(x, t, a, h), hab))

# the red constraints (newest first) and why: each one's record is good,
# with the constraints red before it, which are all earlier
def good(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, rs: List<&2, Nat>, ws: List<&2, SV.Why>) -> Bool:
  match rs ws:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{c, rt} Nil{}:
      False{}
    case Con{+c, +rt} Con{SV.Why{+j, +s, +w}, yt}:
      SV.band(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))))

# the walk's state at constraint i, equation k
def kin(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, st: SO.CS) -> Bool:
  match st:
    case SO.CS{+vm, +red, +why}:
      SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))))))

# the walk's end: good records, and as many matched equations as l0 and the
# kept equations of the constraints walked, distinct, none owned by a red
# constraint
def kres(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS) -> Bool:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))))

def kin_r1(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))))) == True{} : Bool}:
  L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))))), h)

def kin_r2(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)))) == True{} : Bool}:
  L.band_r(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)))), kin_r1(full, own, nv, i, k, vm, red, why, h))

def kin_r3(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))) == True{} : Bool}:
  L.band_r(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))), kin_r2(full, own, nv, i, k, vm, red, why, h))

def kin_r4(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.band(good(full, own, red, why), SV.below(red, i)) == True{} : Bool}:
  L.band_r(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)), kin_r3(full, own, nv, i, k, vm, red, why, h))

def kin_d(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))))), h)

def kin_b(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.below(ST.somes(vm), k) == True{} : Bool}:
  L.band_l(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)))), kin_r1(full, own, nv, i, k, vm, red, why, h))

def kin_m(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.eq(L.mlen(vm), nv) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))), kin_r2(full, own, nv, i, k, vm, red, why, h))

def kin_p(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {pre(own, red, i, ST.somes(vm)) == True{} : Bool}:
  L.band_l(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)), kin_r3(full, own, nv, i, k, vm, red, why, h))

def kin_g(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {good(full, own, red, why) == True{} : Bool}:
  L.band_l(good(full, own, red, why), SV.below(red, i), kin_r4(full, own, nv, i, k, vm, red, why, h))

def kin_rb(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {SV.below(red, i) == True{} : Bool}:
  L.band_r(good(full, own, red, why), SV.below(red, i), kin_r4(full, own, nv, i, k, vm, red, why, h))

def kin_mk(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, hd: {SV.distinct(ST.somes(vm)) == True{} : Bool}, hb: {SV.below(ST.somes(vm), k) == True{} : Bool}, hm: {SV.eq(L.mlen(vm), nv) == True{} : Bool}, hp: {pre(own, red, i, ST.somes(vm)) == True{} : Bool}, hg: {good(full, own, red, why) == True{} : Bool}, hr: {SV.below(red, i) == True{} : Bool}) -> {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}:
  L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))))), hd, L.band_i(SV.below(ST.somes(vm), k), SV.band(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)))), hb, L.band_i(SV.eq(L.mlen(vm), nv), SV.band(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i))), hm, L.band_i(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)), hp, L.band_i(good(full, own, red, why), SV.below(red, i), hg, hr)))))

def lt_up(+o: Nat, +i: Nat, h: {SV.lt(o, i) == True{} : Bool}) -> {SV.lt(o, 1n+i) == True{} : Bool}:
  %Equal.sym(Bool, SV.lt(o, 1n+i), KA.natle(1n+o, 1n+i), L.lt_sv(o, 1n+i)) : {_ == True{} : Bool}
  L.le_succ(1n+o, i, %L.lt_sv(o, i) : {_ == True{} : Bool}
    h)

def lt_ne.go(+o: Nat, +i: Nat, c: Bool, e: {SV.eq(o, i) == c : Bool}, h: {SV.lt(o, i) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, L.lt_irr(i, %L.lt_sv(i, i) : {_ == True{} : Bool}
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

# a driven constraint: nothing changes but the position
def kin_drv(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, +h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {kin(full, own, nv, 1n+i, k, SO.CS{vm, red, why}) == True{} : Bool}:
  kin_mk(full, own, nv, 1n+i, k, vm, red, why, kin_d(full, own, nv, i, k, vm, red, why, h), kin_b(full, own, nv, i, k, vm, red, why, h), kin_m(full, own, nv, i, k, vm, red, why, h), pre_weak(own, red, i, ST.somes(vm), kin_p(full, own, nv, i, k, vm, red, why, h)), kin_g(full, own, nv, i, k, vm, red, why, h), below_mono(red, i, 1n+i, kin_rb(full, own, nv, i, k, vm, red, why, h), L.le_succ(i, i, L.le_refl(i))))

# after constraint i's group ended with g
def kin_step(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +i: Nat, +k: Nat, +n: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, g: ST.GS, +hg: {gres(full, own, red, i, nv, Nat.add(SV.len(ST.somes(vm)), n), Nat.add(k, n), g) == True{} : Bool}, +h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}) -> {kin(full, own, nv, 1n+i, Nat.add(k, n), SO.cfin(i, g, SO.CS{vm, red, why})) == True{} : Bool}:
  match g:
    case ST.GOk{+vm2}:
      +ho = L.band_l(gok(own, red, i, nv, Nat.add(k, n), vm2), SV.eq(SV.len(ST.somes(vm2)), Nat.add(SV.len(ST.somes(vm)), n)), hg)
      kin_mk(full, own, nv, 1n+i, Nat.add(k, n), vm2, red, why, gok_d(own, red, i, nv, Nat.add(k, n), vm2, ho), gok_b(own, red, i, nv, Nat.add(k, n), vm2, ho), D.eq_of(L.mlen(vm2), nv, gok_m(own, red, i, nv, Nat.add(k, n), vm2, ho)), own_step(own, red, i, ST.somes(vm2), gok_o(own, red, i, nv, Nat.add(k, n), vm2, ho), kin_rb(full, own, nv, i, k, vm, red, why, h)), kin_g(full, own, nv, i, k, vm, red, why, h), below_mono(red, i, 1n+i, kin_rb(full, own, nv, i, k, vm, red, why, h), L.le_succ(i, i, L.le_refl(i))))
    case ST.GFail{ST.Red{+j, +s, +w}}:
      +hr = kin_rb(full, own, nv, i, k, vm, red, why, h)
      +h1 = L.band_r(SV.eq(SV.nth(own, j), i), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), allown(own, red, i, s))), hg)
      +h2 = L.band_r(SV.mem(j, s), SV.band(SV.overdet(full, s, w), allown(own, red, i, s)), h1)
      kin_mk(full, own, nv, 1n+i, Nat.add(k, n), vm, Con{i, red}, Con{SV.Why{j, s, w}, why}, kin_d(full, own, nv, i, k, vm, red, why, h), below_mono(ST.somes(vm), k, Nat.add(k, n), kin_b(full, own, nv, i, k, vm, red, why, h), L.le_add_r(k, n)), kin_m(full, own, nv, i, k, vm, red, why, h), pre_fail(own, red, i, ST.somes(vm), kin_p(full, own, nv, i, k, vm, red, why, h)), L.band_i(SV.eq(SV.nth(own, j), i), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, red, i, s), SV.band(SV.below(red, i), good(full, own, red, why))))), L.band_l(SV.eq(SV.nth(own, j), i), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), allown(own, red, i, s))), hg), L.band_i(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, red, i, s), SV.band(SV.below(red, i), good(full, own, red, why)))), L.band_l(SV.mem(j, s), SV.band(SV.overdet(full, s, w), allown(own, red, i, s)), h1), L.band_i(SV.overdet(full, s, w), SV.band(allown(own, red, i, s), SV.band(SV.below(red, i), good(full, own, red, why))), L.band_l(SV.overdet(full, s, w), allown(own, red, i, s), h2), L.band_i(allown(own, red, i, s), SV.band(SV.below(red, i), good(full, own, red, why)), L.band_r(SV.overdet(full, s, w), allown(own, red, i, s), h2), L.band_i(SV.below(red, i), good(full, own, red, why), hr, kin_g(full, own, nv, i, k, vm, red, why, h)))))), L.band_i(SV.lt(i, 1n+i), SV.below(red, 1n+i), lt_succ(i), below_mono(red, i, 1n+i, hr, L.le_succ(i, i, L.le_refl(i)))))

# the walk's end
def kfin_nil(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, +h: {kin(full, own, nv, i, k, SO.CS{vm, red, why}) == True{} : Bool}, hk: {KA.natle(Nat.add(k, 0n), SV.neqs(full)) == True{} : Bool}) -> {kres(full, own, nv, es, Nil{}, i, SV.len(ST.somes(vm)), SO.CS{vm, red, why}) == True{} : Bool}:
  L.band_i(good(full, own, red, why), SV.band(SV.eq(L.mlen(vm), nv), SV.band(SV.eq(SV.len(ST.somes(vm)), Nat.add(SV.len(ST.somes(vm)), 0n)), SV.band(SV.distinct(ST.somes(vm)), SV.band(nred(own, red, ST.somes(vm)), SV.below(ST.somes(vm), SV.neqs(full)))))), kin_g(full, own, nv, i, k, vm, red, why, h), L.band_i(SV.eq(L.mlen(vm), nv), SV.band(SV.eq(SV.len(ST.somes(vm)), Nat.add(SV.len(ST.somes(vm)), 0n)), SV.band(SV.distinct(ST.somes(vm)), SV.band(nred(own, red, ST.somes(vm)), SV.below(ST.somes(vm), SV.neqs(full))))), kin_m(full, own, nv, i, k, vm, red, why, h), L.band_i(SV.eq(SV.len(ST.somes(vm)), Nat.add(SV.len(ST.somes(vm)), 0n)), SV.band(SV.distinct(ST.somes(vm)), SV.band(nred(own, red, ST.somes(vm)), SV.below(ST.somes(vm), SV.neqs(full)))), %LN.add_zero(SV.len(ST.somes(vm))) : {SV.eq(SV.len(ST.somes(vm)), _) == True{} : Bool}
    L.eq_refl(SV.len(ST.somes(vm))), L.band_i(SV.distinct(ST.somes(vm)), SV.band(nred(own, red, ST.somes(vm)), SV.below(ST.somes(vm), SV.neqs(full))), kin_d(full, own, nv, i, k, vm, red, why, h), L.band_i(nred(own, red, ST.somes(vm)), SV.below(ST.somes(vm), SV.neqs(full)), pre_nred(own, red, i, ST.somes(vm), L.band_l(pre(own, red, i, ST.somes(vm)), SV.band(good(full, own, red, why), SV.below(red, i)), kin_r3(full, own, nv, i, k, vm, red, why, h))), below_le(ST.somes(vm), k, SV.neqs(full), kin_b(full, own, nv, i, k, vm, red, why, h), (%Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : {KA.natle(_, SV.neqs(full)) == True{} : Bool}
      hk)))))))

# a driven constraint walked over
def kfin_drv(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, t, 1n+i, l0, fin) == True{} : Bool}) -> {kres(full, own, nv, es, Con{SK.Rec{id, True{}, kd}, t}, i, l0, fin) == True{} : Bool}:
  match fin:
    case SO.CS{vmf, redf, whyf}:
      h

# constraint i (kept: its equations counted) walked over
def kfin_step(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +k: Nat, +vm: List<&2, Maybe<&2, Nat>>, +red: List<&2, Nat>, +why: List<&2, SV.Why>, g: ST.GS, fin: SO.CS, +hres: {kres(full, own, nv, es, t, 1n+i, SV.len(ST.somes(SO.CS.vm(SO.cfin(i, g, SO.CS{vm, red, why})))), fin) == True{} : Bool}, +hs1: {L.subl(SO.CS.red(SO.cfin(i, g, SO.CS{vm, red, why})), SO.CS.red(fin)) == True{} : Bool}, +hs2: {allge(SO.CS.red(fin), SO.CS.red(SO.cfin(i, g, SO.CS{vm, red, why})), 1n+i) == True{} : Bool}, +hg: {gres(full, own, red, i, nv, Nat.add(SV.len(ST.somes(vm)), SV.neqs(SK.Constraint.eqs(es, kd))), Nat.add(k, SV.neqs(SK.Constraint.eqs(es, kd))), g) == True{} : Bool}, +hr: {SV.below(red, i) == True{} : Bool}) -> {kres(full, own, nv, es, Con{SK.Rec{id, False{}, kd}, t}, i, SV.len(ST.somes(vm)), fin) == True{} : Bool}:
  match g fin:
    case ST.GOk{+vm2} SO.CS{+vmf, +redf, +whyf}:
      +n = SV.neqs(SK.Constraint.eqs(es, kd))
      +l0 = SV.len(ST.somes(vm))
      +mm = SV.mark.cons(redf, t, 1n+i)
      +r = SV.neqs(SK.Sketch.eqs.go(es, mm))
      %Equal.sym(Bool, SV.mem(i, redf), False{}, allge_notmem(redf, red, i, hs2, below_notmem(i, red, hr))) : {SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, Con{SK.Rec{id, _, kd}, mm})))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))))) == True{} : Bool}
      %Equal.sym(Nat, SV.neqs(SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, mm))), Nat.add(n, r), neqs_cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, mm))) : {SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, _)), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(l0, Nat.add(n, r)), Nat.add(Nat.add(l0, n), r), LN.add_assoc(l0, n, r)) : {SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), _), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))))) == True{} : Bool}
      %L.eq_ok(SV.len(ST.somes(vm2)), Nat.add(l0, n), L.band_r(gok(own, red, i, nv, Nat.add(k, n), vm2), SV.eq(SV.len(ST.somes(vm2)), Nat.add(l0, n)), hg)) : {SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(_, r)), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))))) == True{} : Bool}
      hres
    case ST.GFail{ST.Red{j, s, w}} SO.CS{+vmf, +redf, +whyf}:
      %Equal.sym(Bool, SV.mem(i, redf), True{}, L.subl_hd(i, red, redf, hs1)) : {SV.band(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(SV.len(ST.somes(vm)), SV.neqs(SK.Sketch.eqs.go(es, Con{SK.Rec{id, _, kd}, SV.mark.cons(redf, t, 1n+i)})))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))))) == True{} : Bool}
      hres

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

# the walk from constraint i (equation k), state st
def kuhnc_ok(cs: List<&2, SK.Rec>, +es: List<&2, SK.Ent>, +i: Nat, +k: Nat, +f: Nat, st: SO.CS, +full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +hd: {drop(k, own) == SV.owners.go(es, cs, i) : List<&2, Nat>}, +hk: {KA.natle(Nat.add(k, SV.neqs(SK.Sketch.eqs.go(es, cs))), SV.neqs(full)) == True{} : Bool}, +ha: {D.adjb(ST.adj(full), nv) == True{} : Bool}, +hf: {KA.natle(1n+nv, f) == True{} : Bool}, +hs: {kin(full, own, nv, i, k, st) == True{} : Bool}) -> {kres(full, own, nv, es, cs, i, SV.len(ST.somes(SO.CS.vm(st))), SO.kuhnc(cs, es, i, k, ST.adj(full), f, st)) == True{} : Bool}:
  match cs st:
    case Nil{} SO.CS{+vm, +red, +why}:
      kfin_nil(full, own, nv, es, i, k, vm, red, why, hs, hk)
    case Con{SK.Rec{+id, True{}, +kd}, +t} SO.CS{+vm, +red, +why}:
      kfin_drv(full, own, nv, es, id, kd, t, i, SV.len(ST.somes(vm)), SO.kuhnc(t, es, 1n+i, k, ST.adj(full), f, SO.CS{vm, red, why}), kuhnc_ok(t, es, 1n+i, k, f, SO.CS{vm, red, why}, full, own, nv, hd, hk, ha, hf, kin_drv(full, own, nv, i, k, vm, red, why, hs)))
    case Con{SK.Rec{+id, False{}, +kd}, +t} SO.CS{+vm, +red, +why}:
      +adj = ST.adj(full)
      +n = SV.neqs(SK.Constraint.eqs(es, kd))
      +l0 = SV.len(ST.somes(vm))
      +g = ST.grp(n, k, adj, f, ST.GOk{vm})
      +st2 = SO.cfin(i, g, SO.CS{vm, red, why})
      +hk2 = hk_step(k, es, id, kd, t, SV.neqs(full), hk)
      +hgres = grp_ok(n, k, f, ST.GOk{vm}, full, own, red, i, nv, Nat.add(l0, n), Nat.add(k, n), SV.owners.go(es, t, 1n+i), hd, {==}, L.le_trans(Nat.add(k, n), Nat.add(Nat.add(k, n), SV.neqs(SK.Sketch.eqs.go(es, t))), SV.neqs(full), L.le_add_r(Nat.add(k, n), SV.neqs(SK.Sketch.eqs.go(es, t))), hk2), ha, hf, L.band_i(gok(own, red, i, nv, k, vm), SV.eq(Nat.add(l0, n), Nat.add(l0, n)), gok_mk(own, red, i, nv, k, vm, kin_d(full, own, nv, i, k, vm, red, why, hs), kin_b(full, own, nv, i, k, vm, red, why, hs), L.eq_ok(L.mlen(vm), nv, kin_m(full, own, nv, i, k, vm, red, why, hs)), pre_allown(own, red, i, ST.somes(vm), kin_p(full, own, nv, i, k, vm, red, why, hs))), L.eq_refl(Nat.add(l0, n))))
      +fin = SO.kuhnc(t, es, 1n+i, Nat.add(k, n), adj, f, st2)
      kfin_step(full, own, nv, es, id, kd, t, i, k, vm, red, why, g, fin, kuhnc_ok(t, es, 1n+i, Nat.add(k, n), f, st2, full, own, nv, hd_step(k, own, es, id, kd, t, i, hd), hk2, ha, hf, kin_step(full, own, nv, i, k, n, vm, red, why, g, hgres, hs)), shape1(t, es, 1n+i, Nat.add(k, n), adj, f, st2), shape2(t, es, 1n+i, Nat.add(k, n), adj, f, st2), hgres, kin_rb(full, own, nv, i, k, vm, red, why, hs))

# The whole walk
# --------------

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

def kin0(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat) -> {kin(full, own, nv, 0n, 0n, SO.CS{ST.nones(nv), Nil{}, Nil{}}) == True{} : Bool}:
  kin_mk(full, own, nv, 0n, 0n, ST.nones(nv), Nil{}, Nil{}, %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, somes_nones(nv)) : {SV.distinct(_) == True{} : Bool}
    {==}, %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, somes_nones(nv)) : {SV.below(_, 0n) == True{} : Bool}
    {==}, D.eq_of(L.mlen(ST.nones(nv)), nv, mlen_nones(nv)), %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, somes_nones(nv)) : {pre(own, Nil{}, 0n, _) == True{} : Bool}
    {==}, {==}, {==})

def sk.ents(sk: SK.Sketch) -> List<&2, SK.Ent>:
  match sk:
    case SK.Sketch{vs, es, cs}:
      es

def sk.cons(sk: SK.Sketch) -> List<&2, SK.Rec>:
  match sk:
    case SK.Sketch{vs, es, cs}:
      cs

def run_kres(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {kres(SK.Sketch.eqs(sk), SV.owners(sk), nv, sk.ents(sk), sk.cons(sk), 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(sk, nv)) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      +full = SK.Sketch.eqs.go(es, cs)
      kuhnc_ok(cs, es, 0n, 0n, 1n+nv, SO.CS{ST.nones(nv), Nil{}, Nil{}}, full, SV.owners.go(es, cs, 0n), nv, {==}, L.le_refl(SV.neqs(full)), ha, L.le_refl(1n+nv), kin0(full, SV.owners.go(es, cs, 0n), nv))

def kres_good(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {good(full, own, SO.CS.red(fin), SO.CS.why(fin)) == True{} : Bool}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.band_l(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h)

def kres_mlen(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {L.mlen(SO.CS.vm(fin)) == nv : Nat}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.eq_ok(L.mlen(vmf), nv, L.band_l(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))), L.band_r(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h)))

def kres_cnt(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {SV.len(ST.somes(SO.CS.vm(fin))) == Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(SO.CS.red(fin), cs, i)))) : Nat}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.eq_ok(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i)))), L.band_l(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))), L.band_r(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))), L.band_r(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h))))

def kres_dist(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {SV.distinct(ST.somes(SO.CS.vm(fin))) == True{} : Bool}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.band_l(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))), L.band_r(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))), L.band_r(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))), L.band_r(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h))))

def kres_nred(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {nred(own, SO.CS.red(fin), ST.somes(SO.CS.vm(fin))) == True{} : Bool}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.band_l(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)), L.band_r(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))), L.band_r(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))), L.band_r(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))), L.band_r(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h)))))

def kres_below(+full: List<&2, E.QExpr>, +own: List<&2, Nat>, +nv: Nat, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +i: Nat, +l0: Nat, fin: SO.CS, h: {kres(full, own, nv, es, cs, i, l0, fin) == True{} : Bool}) -> {SV.below(ST.somes(SO.CS.vm(fin)), SV.neqs(full)) == True{} : Bool}:
  match fin:
    case SO.CS{+vmf, +redf, +whyf}:
      L.band_r(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)), L.band_r(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))), L.band_r(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))), L.band_r(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full))))), L.band_r(good(full, own, redf, whyf), SV.band(SV.eq(L.mlen(vmf), nv), SV.band(SV.eq(SV.len(ST.somes(vmf)), Nat.add(l0, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(redf, cs, i))))), SV.band(SV.distinct(ST.somes(vmf)), SV.band(nred(own, redf, ST.somes(vmf)), SV.below(ST.somes(vmf), SV.neqs(full)))))), h)))))

# The red stage's results
# -----------------------

def red_good(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {good(SK.Sketch.eqs(sk), SV.owners(sk), SO.CS.red(SO.run(sk, nv)), SO.CS.why(SO.run(sk, nv))) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kres_good(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(SK.Sketch{vs, es, cs}, nv), run_kres(SK.Sketch{vs, es, cs}, nv, ha))

def red_mlen(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {L.mlen(SO.CS.vm(SO.run(sk, nv))) == nv : Nat}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kres_mlen(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(SK.Sketch{vs, es, cs}, nv), run_kres(SK.Sketch{vs, es, cs}, nv, ha))

def cnt0(+nv: Nat, +x: Nat) -> {Nat.add(SV.len(ST.somes(ST.nones(nv))), x) == x : Nat}:
  %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, somes_nones(nv)) : {Nat.add(SV.len(_), x) == x : Nat}
  {==}

# as many matched equations as kept ones
def red_cnt(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {SV.len(ST.somes(SO.CS.vm(SO.run(sk, nv)))) == SV.neqs(SK.Sketch.eqs(SV.mark(SO.CS.red(SO.run(sk, nv)), sk))) : Nat}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      +fin = SO.run(SK.Sketch{vs, es, cs}, nv)
      %cnt0(nv, SV.neqs(SK.Sketch.eqs.go(es, SV.mark.cons(SO.CS.red(fin), cs, 0n)))) : {SV.len(ST.somes(SO.CS.vm(fin))) == _ : Nat}
      kres_cnt(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), fin, run_kres(SK.Sketch{vs, es, cs}, nv, ha))

# the matched equations are distinct
def red_dist(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {SV.distinct(ST.somes(SO.CS.vm(SO.run(sk, nv)))) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kres_dist(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(SK.Sketch{vs, es, cs}, nv), run_kres(SK.Sketch{vs, es, cs}, nv, ha))

# no matched equation is owned by a red constraint
def red_nred(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {nred(SV.owners(sk), SO.CS.red(SO.run(sk, nv)), ST.somes(SO.CS.vm(SO.run(sk, nv)))) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kres_nred(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(SK.Sketch{vs, es, cs}, nv), run_kres(SK.Sketch{vs, es, cs}, nv, ha))

# the matched equations are equations of the system
def red_below(sk: SK.Sketch, +nv: Nat, ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), nv) == True{} : Bool}) -> {SV.below(ST.somes(SO.CS.vm(SO.run(sk, nv))), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      kres_below(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), nv, es, cs, 0n, SV.len(ST.somes(ST.nones(nv))), SO.run(SK.Sketch{vs, es, cs}, nv), run_kres(SK.Sketch{vs, es, cs}, nv, ha))

# Explained
# ---------
# The red list R is newest first, so every entry is greater than the ones
# after it. q(xs, rs): every x of xs is in rs, or above all of rs.

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
      absurd({True{} == False{} : Bool}, L.lt_irr(o, L.le_trans(1n+o, 1n+c, o, L.le_succ(1n+o, c, %L.lt_sv(o, c) : {_ == True{} : Bool}
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
def clean_of(+own: List<&2, Nat>, +r: List<&2, Nat>, +c: Nat, +rt: List<&2, Nat>, s: List<&2, Nat>, +ha: {allown(own, rt, c, s) == True{} : Bool}, +hq: {q(r, Con{c, rt}) == True{} : Bool}) -> {SV.clean(own, r, c, s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      +o = SV.nth(own, m)
      L.band_i(SV.bor(SV.eq(o, c), SV.bnot(SV.mem(o, r))), SV.clean(own, r, c, t), clean1(SV.eq(o, c), o, c, rt, r, L.band_l(okown(own, rt, c, m), allown(own, rt, c, t), ha), hq), clean_of(own, r, c, rt, t, L.band_r(okown(own, rt, c, m), allown(own, rt, c, t), ha), hq))

def expl_go(+sk: SK.Sketch, +r: List<&2, Nat>, rs: List<&2, Nat>, ws: List<&2, SV.Why>, +hg: {good(SK.Sketch.eqs(sk), SV.owners(sk), rs, ws) == True{} : Bool}, +hq: {q(r, rs) == True{} : Bool}) -> {SV.explained.go(sk, r, rs, ws) == True{} : Bool}:
  match rs ws:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      absurd({False{} == True{} : Bool}, L.ft(hg))
    case Con{c, rt} Nil{}:
      absurd({False{} == True{} : Bool}, L.ft(hg))
    case Con{+c, +rt} Con{SV.Why{+j, +s, +w}, +yt}:
      +full = SK.Sketch.eqs(sk)
      +own = SV.owners(sk)
      +g1 = L.band_r(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))), hg)
      +g2 = L.band_r(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)))), g1)
      +g3 = L.band_r(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))), g2)
      +g4 = L.band_r(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)), g3)
      +hb = L.band_l(SV.below(rt, c), good(full, own, rt, yt), g4)
      L.band_i(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(SV.clean(own, r, c, s), SV.explained.go(sk, r, rt, yt)))), L.band_l(SV.eq(SV.nth(own, j), c), SV.band(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))))), hg), L.band_i(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(SV.clean(own, r, c, s), SV.explained.go(sk, r, rt, yt))), L.band_l(SV.mem(j, s), SV.band(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)))), g1), L.band_i(SV.overdet(full, s, w), SV.band(SV.clean(own, r, c, s), SV.explained.go(sk, r, rt, yt)), L.band_l(SV.overdet(full, s, w), SV.band(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt))), g2), L.band_i(SV.clean(own, r, c, s), SV.explained.go(sk, r, rt, yt), clean_of(own, r, c, rt, s, L.band_l(allown(own, rt, c, s), SV.band(SV.below(rt, c), good(full, own, rt, yt)), g3), hq), expl_go(sk, r, rt, yt, L.band_r(SV.below(rt, c), good(full, own, rt, yt), g4), q_step(r, c, rt, hq, hb))))))

# good records explain the red constraints
def explained_of(+sk: SK.Sketch, +r: List<&2, Nat>, +ws: List<&2, SV.Why>, hg: {good(SK.Sketch.eqs(sk), SV.owners(sk), r, ws) == True{} : Bool}) -> {SV.explained(sk, r, ws) == True{} : Bool}:
  expl_go(sk, r, r, ws, hg, q_of(r, r, L.subl_refl(r)))
