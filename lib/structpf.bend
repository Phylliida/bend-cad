# bend-cad: the solver's structure, for solve_complete (DESIGN §10.4, C2b).
# Proofs only.
# Generated: python3 tools/expand.py tools/drafts/structpf.draft lib/structpf.bend
#
# The variable side (lib/struct.bend: kuhnd over the kept equations good)
# ends with every kept equation matched, and the pins and the matched
# variables together are all the variables, each once. Tarjan's
# components partition good (lib/tarjanpf.bend). The blocks hold the
# components' equations in order; each block is valid: the ones emitted
# one by one passed the solver's own check, and what is left after a
# failed check is valid because every variable a kept equation uses is a
# pin or matched to a kept equation, which is in an earlier block or in
# what is left. So vp (the pins, then each block's unknowns) lists every
# variable once, and the plan checker's walk finds, block by block, the
# sizes, parameters and variable bounds it wants (swalk).

import Base
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ./karith.bend as KA
import ./struct.bend as ST
import ./solve.bend as SO
import ./plan.bend as PL
import ./cert.bend as CK
import ./slope.bend as SL
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D
import ./redpf.bend as RP
import ./maxpf.bend as MX
import ./tarjanpf.bend as TJ

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Lists
# -----

def pigc.one(+y: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, b: Bool, e: {SV.mem(y, xs) == b : Bool}, hy: {SV.mem(y, ys) == True{} : Bool}, dx: {SV.distinct(xs) == True{} : Bool}, hs: {L.subl(xs, ys) == True{} : Bool}, hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, KA.natlt_irr(SV.len(xs), KA.natle_trans(1n+SV.len(xs), 1n+SV.len(L.rem(y, ys)), SV.len(xs), L.pig(xs, L.rem(y, ys), dx, L.subl_rem(xs, y, ys, hs, e)), KA.natle_trans(1n+SV.len(L.rem(y, ys)), SV.len(ys), SV.len(xs), L.rem_len(y, ys, hy), hl))))

def pigc.go(zs: List<&2, Nat>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hz: {L.subl(zs, ys) == True{} : Bool}, +dx: {SV.distinct(xs) == True{} : Bool}, +hs: {L.subl(xs, ys) == True{} : Bool}, +hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {L.subl(zs, xs) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      L.subl_con(z, t, xs, pigc.one(z, xs, ys, SV.mem(z, xs), {==}, L.subl_hd(z, t, ys, hz), dx, hs, hl), pigc.go(t, xs, ys, L.subl_tl(z, t, ys, hz), dx, hs, hl))

# xs within ys, distinct and no shorter: ys within xs
def pigc(+xs: List<&2, Nat>, +ys: List<&2, Nat>, dx: {SV.distinct(xs) == True{} : Bool}, hs: {L.subl(xs, ys) == True{} : Bool}, hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {L.subl(ys, xs) == True{} : Bool}:
  pigc.go(ys, xs, ys, L.subl_refl(ys), dx, hs, hl)

# two distinct lists, each within the other, are as long
def len_eq(+xs: List<&2, Nat>, +ys: List<&2, Nat>, dx: {SV.distinct(xs) == True{} : Bool}, dy: {SV.distinct(ys) == True{} : Bool}, h1: {L.subl(xs, ys) == True{} : Bool}, h2: {L.subl(ys, xs) == True{} : Bool}) -> {SV.len(xs) == SV.len(ys) : Nat}:
  KA.natle_antisym(SV.len(xs), SV.len(ys), L.pig(xs, ys, dx, h1), L.pig(ys, xs, dy, h2))

def sv_ne(+u: Nat, +x: Nat, e: {KA.nateq(u, x) == False{} : Bool}) -> {SV.eq(u, x) == False{} : Bool}:
  %Equal.sym(Bool, SV.eq(u, x), KA.nateq(u, x), L.eq_sv(u, x)) : {_ == False{} : Bool}
  e

def sv_eq(+u: Nat, +x: Nat, e: {KA.nateq(u, x) == True{} : Bool}) -> {SV.eq(u, x) == True{} : Bool}:
  %Equal.sym(Bool, SV.eq(u, x), KA.nateq(u, x), L.eq_sv(u, x)) : {_ == True{} : Bool}
  e

def pos_in.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +r: List<&2, Nat>, b: Bool, e: {KA.nateq(u, x) == b : Bool}, h: {SV.mem(u, Con{x, t}) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {KA.natle(1n+ST.pos(u, ST.app(t, r)), SV.len(t)) == True{} : Bool}) -> {KA.natle(1n+ST.pos.go(b, ST.pos(u, ST.app(t, r))), 1n+SV.len(t)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(L.mem_tl_inv(u, x, t, h, sv_ne(u, x, e)))

# u in k: its position in k ++ r is below |k|
def pos_in(+u: Nat, k: List<&2, Nat>, +r: List<&2, Nat>, h: {SV.mem(u, k) == True{} : Bool}) -> {KA.natle(1n+ST.pos(u, ST.app(k, r)), SV.len(k)) == True{} : Bool}:
  match k:
    case Nil{}:
      absurd({KA.natle(1n+ST.pos(u, ST.app(Nil{}, r)), 0n) == True{} : Bool}, KA.ft(h))
    case Con{+x, +t}:
      pos_in.go(u, x, t, r, KA.nateq(u, x), {==}, h, p => pos_in(u, t, r, p))

def pos_out.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +r: List<&2, Nat>, b: Bool, e: {KA.nateq(u, x) == b : Bool}, +h: {SV.mem(u, Con{x, t}) == False{} : Bool}, ih: {SV.mem(u, t) == False{} : Bool} -> {KA.natle(SV.len(t), ST.pos(u, ST.app(t, r))) == True{} : Bool}) -> {KA.natle(1n+SV.len(t), ST.pos.go(b, ST.pos(u, ST.app(t, r)))) == True{} : Bool}:
  match b:
    case True{}:
      absurd({KA.natle(1n+SV.len(t), 0n) == True{} : Bool}, L.tnf(SV.eq(u, x), sv_eq(u, x, e), L.bor_fl(SV.eq(u, x), SV.mem(u, t), h)))
    case False{}:
      ih(L.bor_fr(SV.eq(u, x), SV.mem(u, t), h))

# u not in k: its position in k ++ r is at least |k|
def pos_out(+u: Nat, k: List<&2, Nat>, +r: List<&2, Nat>, h: {SV.mem(u, k) == False{} : Bool}) -> {KA.natle(SV.len(k), ST.pos(u, ST.app(k, r))) == True{} : Bool}:
  match k:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      pos_out.go(u, x, t, r, KA.nateq(u, x), {==}, h, p => pos_out(u, t, r, p))

def pos_mem.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +vp: List<&2, Nat>, b: Bool, e: {SV.eq(u, x) == b : Bool}, h: {SV.bor(b, SV.mem(u, t)) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {SV.mem(ST.pos(u, vp), ST.positions(t, vp)) == True{} : Bool}) -> {SV.mem(ST.pos(u, vp), Con{ST.pos(x, vp), ST.positions(t, vp)}) == True{} : Bool}:
  match b:
    case True{}:
      %L.eq_ok(u, x, e) : {SV.mem(ST.pos(u, vp), Con{ST.pos(_, vp), ST.positions(t, vp)}) == True{} : Bool}
      L.mem_hd(ST.pos(u, vp), ST.positions(t, vp))
    case False{}:
      L.mem_tl(ST.pos(u, vp), ST.pos(x, vp), ST.positions(t, vp), ih(h))

# u in xs: its position in vp is among xs's positions
def pos_mem(+u: Nat, xs: List<&2, Nat>, +vp: List<&2, Nat>, h: {SV.mem(u, xs) == True{} : Bool}) -> {SV.mem(ST.pos(u, vp), ST.positions(xs, vp)) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(ST.pos(u, vp), Nil{}) == True{} : Bool}, KA.ft(h))
    case Con{+x, +t}:
      pos_mem.go(u, x, t, vp, SV.eq(u, x), {==}, h, p => pos_mem(u, t, vp, p))

def positions_len(xs: List<&2, Nat>, +vp: List<&2, Nat>) -> {ST.len(ST.positions(xs, vp)) == ST.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat, ST.len(ST.positions(t, vp)), ST.len(t), positions_len(t, vp)) : {1n+_ == 1n+ST.len(t) : Nat}
      {==}

def look_app(+m: List<&2, Maybe<&2, Nat>>, a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.look(m, ST.app(a, b)) == ST.app(ST.look(m, a), ST.look(m, b)) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, Nat>, ST.look(m, ST.app(t, b)), ST.app(ST.look(m, t), ST.look(m, b)), look_app(m, t, b)) : {Con{ST.look.of(ST.getm(m, x)), _} == Con{ST.look.of(ST.getm(m, x)), ST.app(ST.look(m, t), ST.look(m, b))} : List<&2, Nat>}
      {==}

def look_has.go(+m: List<&2, Maybe<&2, Nat>>, +x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(x, y) == b : Bool}, h: {SV.bor(b, SV.mem(x, t)) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {SV.mem(ST.look.of(ST.getm(m, x)), ST.look(m, t)) == True{} : Bool}) -> {SV.mem(ST.look.of(ST.getm(m, x)), Con{ST.look.of(ST.getm(m, y)), ST.look(m, t)}) == True{} : Bool}:
  match b:
    case True{}:
      %L.eq_ok(x, y, e) : {SV.mem(ST.look.of(ST.getm(m, x)), Con{ST.look.of(ST.getm(m, _)), ST.look(m, t)}) == True{} : Bool}
      L.mem_hd(ST.look.of(ST.getm(m, x)), ST.look(m, t))
    case False{}:
      L.mem_tl(ST.look.of(ST.getm(m, x)), ST.look.of(ST.getm(m, y)), ST.look(m, t), ih(h))

# x in ys: m(x) in m(ys)
def look_has(+m: List<&2, Maybe<&2, Nat>>, +x: Nat, ys: List<&2, Nat>, h: {SV.mem(x, ys) == True{} : Bool}) -> {SV.mem(ST.look.of(ST.getm(m, x)), ST.look(m, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({SV.mem(ST.look.of(ST.getm(m, x)), Nil{}) == True{} : Bool}, KA.ft(h))
    case Con{+y, +t}:
      look_has.go(m, x, y, t, SV.eq(x, y), {==}, h, p => look_has(m, x, t, p))

def look_mono(+m: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {L.subl(xs, ys) == True{} : Bool}) -> {L.subl(ST.look(m, xs), ST.look(m, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(ST.look.of(ST.getm(m, x)), ST.look(m, t), ST.look(m, ys), look_has(m, x, ys, L.subl_hd(x, t, ys, h)), look_mono(m, t, ys, L.subl_tl(x, t, ys, h)))

def len_app(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {SV.len(ST.app(xs, ys)) == Nat.add(SV.len(xs), SV.len(ys)) : Nat}:
  MX.len_app(xs, ys)

# u in b, a ++ b distinct: u not in a
def dist_notin(+u: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, +hd: {SV.distinct(ST.app(a, b)) == True{} : Bool}, +hm: {SV.mem(u, b) == True{} : Bool}) -> {SV.mem(u, a) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.bor_f(SV.eq(u, x), SV.mem(u, t), L.mem_ne(u, x, ST.app(t, b), TJ.mem_app_r(u, t, b, hm), L.dist_hd(x, ST.app(t, b), hd)), dist_notin(u, t, b, L.dist_tl(x, ST.app(t, b), hd), hm))

# The variables equations use
# ---------------------------

def addv_sub.go(b: Bool, +v: Nat, +acc: List<&2, Nat>) -> {L.subl(ST.addv.go(b, v, acc), Con{v, acc}) == True{} : Bool}:
  match b:
    case True{}:
      L.subl_cons_r(acc, v, acc, L.subl_refl(acc))
    case False{}:
      L.subl_refl(Con{v, acc})

def addv_acc.go(b: Bool, +v: Nat, +acc: List<&2, Nat>) -> {L.subl(acc, ST.addv.go(b, v, acc)) == True{} : Bool}:
  match b:
    case True{}:
      L.subl_refl(acc)
    case False{}:
      L.subl_cons_r(acc, v, acc, L.subl_refl(acc))

def addv_has.go(b: Bool, +v: Nat, +acc: List<&2, Nat>, e: {ST.mem(v, acc) == b : Bool}) -> {SV.mem(v, ST.addv.go(b, v, acc)) == True{} : Bool}:
  match b:
    case True{}:
      MX.sv_mem(v, acc, e)
    case False{}:
      L.mem_hd(v, acc)

def ua_sub(xs: List<&2, Nat>, +acc: List<&2, Nat>, +z: List<&2, Nat>, +hx: {L.subl(xs, z) == True{} : Bool}, ha: {L.subl(acc, z) == True{} : Bool}) -> {L.subl(ST.uses.add(xs, acc), z) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+x, +t}:
      ua_sub(t, ST.addv(x, acc), z, L.subl_tl(x, t, z, hx), L.subl_trans(ST.addv(x, acc), Con{x, acc}, z, addv_sub.go(ST.mem(x, acc), x, acc), L.subl_con(x, acc, z, L.subl_hd(x, t, z, hx), ha)))

def ua_acc(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {L.subl(acc, ST.uses.add(xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subl_refl(acc)
    case Con{+x, +t}:
      L.subl_trans(acc, ST.addv(x, acc), ST.uses.add(t, ST.addv(x, acc)), addv_acc.go(ST.mem(x, acc), x, acc), ua_acc(t, ST.addv(x, acc)))

def ua_xs(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {L.subl(xs, ST.uses.add(xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, ST.uses.add(t, ST.addv(x, acc)), L.subl_mem(x, ST.addv(x, acc), ST.uses.add(t, ST.addv(x, acc)), addv_has.go(ST.mem(x, acc), x, acc, {==}), ua_acc(t, ST.addv(x, acc))), ua_xs(t, ST.addv(x, acc)))

# every equation of js uses only variables in z
def alladj(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +z: List<&2, Nat>) -> Bool:
  match js:
    case Nil{}:
      True{}
    case Con{j, t}:
      SV.band(L.subl(ST.nthl(adj, j), z), alladj(t, adj, z))

def ug_sub(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +acc: List<&2, Nat>, +z: List<&2, Nat>, +h: {alladj(js, adj, z) == True{} : Bool}, ha: {L.subl(acc, z) == True{} : Bool}) -> {L.subl(ST.uses.go(js, adj, acc), z) == True{} : Bool}:
  match js:
    case Nil{}:
      ha
    case Con{+j, +t}:
      ug_sub(t, adj, ST.uses.add(ST.nthl(adj, j), acc), z, L.band_r(L.subl(ST.nthl(adj, j), z), alladj(t, adj, z), h), ua_sub(ST.nthl(adj, j), acc, z, L.band_l(L.subl(ST.nthl(adj, j), z), alladj(t, adj, z), h), ha))

def ug_acc(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +acc: List<&2, Nat>) -> {L.subl(acc, ST.uses.go(js, adj, acc)) == True{} : Bool}:
  match js:
    case Nil{}:
      L.subl_refl(acc)
    case Con{+j, +t}:
      L.subl_trans(acc, ST.uses.add(ST.nthl(adj, j), acc), ST.uses.go(t, adj, ST.uses.add(ST.nthl(adj, j), acc)), ua_acc(ST.nthl(adj, j), acc), ug_acc(t, adj, ST.uses.add(ST.nthl(adj, j), acc)))

def ug_has.go(+e: Nat, +j: Nat, +t: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +acc: List<&2, Nat>, b: Bool, eb: {SV.eq(e, j) == b : Bool}, h: {SV.bor(b, SV.mem(e, t)) == True{} : Bool}, ih: {SV.mem(e, t) == True{} : Bool} -> {L.subl(ST.nthl(adj, e), ST.uses.go(t, adj, ST.uses.add(ST.nthl(adj, j), acc))) == True{} : Bool}) -> {L.subl(ST.nthl(adj, e), ST.uses.go(t, adj, ST.uses.add(ST.nthl(adj, j), acc))) == True{} : Bool}:
  match b:
    case True{}:
      %L.eq_ok(e, j, eb) : {L.subl(ST.nthl(adj, e), ST.uses.go(t, adj, ST.uses.add(ST.nthl(adj, _), acc))) == True{} : Bool}
      L.subl_trans(ST.nthl(adj, e), ST.uses.add(ST.nthl(adj, e), acc), ST.uses.go(t, adj, ST.uses.add(ST.nthl(adj, e), acc)), ua_xs(ST.nthl(adj, e), acc), ug_acc(t, adj, ST.uses.add(ST.nthl(adj, e), acc)))
    case False{}:
      ih(h)

def ug_has(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +acc: List<&2, Nat>, +e: Nat, h: {SV.mem(e, js) == True{} : Bool}) -> {L.subl(ST.nthl(adj, e), ST.uses.go(js, adj, acc)) == True{} : Bool}:
  match js:
    case Nil{}:
      absurd({L.subl(ST.nthl(adj, e), acc) == True{} : Bool}, KA.ft(h))
    case Con{+j, +t}:
      ug_has.go(e, j, t, adj, acc, SV.eq(e, j), {==}, h, p => ug_has(t, adj, ST.uses.add(ST.nthl(adj, j), acc), e, p))

# what js uses is within z when each of js's equations is
def uses_sub(+js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +z: List<&2, Nat>, h: {alladj(js, adj, z) == True{} : Bool}) -> {L.subl(ST.uses(js, adj), z) == True{} : Bool}:
  TJ.rg_subl(ST.uses.go(js, adj, Nil{}), Nil{}, z, ug_sub(js, adj, Nil{}, z, h, {==}), {==})

# e in js: what e uses is in what js uses
def uses_has(+js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +e: Nat, h: {SV.mem(e, js) == True{} : Bool}) -> {L.subl(ST.nthl(adj, e), ST.uses(js, adj)) == True{} : Bool}:
  +g = ST.uses.go(js, adj, Nil{})
  L.subl_trans(ST.nthl(adj, e), g, ST.rev.go(g, Nil{}), ug_has(js, adj, Nil{}, e, h), L.band_l(L.subl(g, ST.rev.go(g, Nil{})), L.subl(Nil{}, ST.rev.go(g, Nil{})), D.rev_go_subl(g, Nil{})))

def alladj_in(xs: List<&2, Nat>, +ys: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +h: {L.subl(xs, ys) == True{} : Bool}) -> {alladj(xs, adj, ST.uses(ys, adj)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(L.subl(ST.nthl(adj, x), ST.uses(ys, adj)), alladj(t, adj, ST.uses(ys, adj)), uses_has(ys, adj, x, L.subl_hd(x, t, ys, h)), alladj_in(t, ys, adj, L.subl_tl(x, t, ys, h)))

# xs within ys: what xs uses is in what ys uses
def uses_mono(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, h: {L.subl(xs, ys) == True{} : Bool}) -> {L.subl(ST.uses(xs, adj), ST.uses(ys, adj)) == True{} : Bool}:
  uses_sub(xs, adj, ST.uses(ys, adj), alladj_in(xs, ys, adj, h))

def allin_subl(xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {ST.all_in(xs, ys) == True{} : Bool}) -> {L.subl(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, ys, MX.sv_mem(x, ys, KA.band_l(ST.mem(x, ys), ST.all_in(t, ys), h)), allin_subl(t, ys, KA.band_r(ST.mem(x, ys), ST.all_in(t, ys), h)))

# Lists of blocks
# ---------------

def nleq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{b, t}:
      False{}
    case Con{a, s} Nil{}:
      False{}
    case Con{a, s} Con{b, t}:
      SV.band(SV.eq(a, b), nleq(s, t))

def nleq_ok(xs: List<&2, Nat>, ys: List<&2, Nat>, +h: {nleq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +t}:
      absurd({Nil{} == Con{b, t} : List<&2, Nat>}, KA.ft(h))
    case Con{+a, +s} Nil{}:
      absurd({Con{a, s} == Nil{} : List<&2, Nat>}, KA.ft(h))
    case Con{+a, +s} Con{+b, +t}:
      %L.eq_ok(a, b, L.band_l(SV.eq(a, b), nleq(s, t), h)) : {Con{a, s} == Con{_, t} : List<&2, Nat>}
      %nleq_ok(s, t, L.band_r(SV.eq(a, b), nleq(s, t), h)) : {Con{a, s} == Con{a, _} : List<&2, Nat>}
      {==}

def nleq_refl(xs: List<&2, Nat>) -> {nleq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.eq(x, x), nleq(t, t), L.eq_refl(x), nleq_refl(t))

# each block's unknowns are its equations' mates
def lkb(+vm: List<&2, Maybe<&2, Nat>>, bs: List<&2, ST.SB>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{ST.SB{es, vs}, t}:
      SV.band(nleq(vs, ST.look(vm, es)), lkb(vm, t))

# each block is valid: its equations use only its unknowns and earlier
# variables (known, then the earlier blocks' unknowns)
def vchain(bs: List<&2, ST.SB>, +known: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{ST.SB{es, +vs}, t}:
      SV.band(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(t, ST.app(known, vs), adj))

def sbapp(xs: List<&2, ST.SB>, ys: List<&2, ST.SB>) -> List<&2, ST.SB>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, sbapp(t, ys)}

def sbapp_assoc(a: List<&2, ST.SB>, +b: List<&2, ST.SB>, +c: List<&2, ST.SB>) -> {sbapp(sbapp(a, b), c) == sbapp(a, sbapp(b, c)) : List<&2, ST.SB>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, ST.SB>, sbapp(sbapp(t, b), c), sbapp(t, sbapp(b, c)), sbapp_assoc(t, b, c)) : {Con{h, _} == Con{h, sbapp(t, sbapp(b, c))} : List<&2, ST.SB>}
      {==}

def revb_sbapp(xs: List<&2, ST.SB>, +ys: List<&2, ST.SB>) -> {ST.revb.go(xs, ys) == sbapp(ST.revb.go(xs, Nil{}), ys) : List<&2, ST.SB>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +r = ST.revb.go(t, Nil{})
      %Equal.sym(List<&2, ST.SB>, ST.revb.go(t, Con{h, ys}), sbapp(r, Con{h, ys}), revb_sbapp(t, Con{h, ys})) : {_ == sbapp(ST.revb.go(t, Con{h, Nil{}}), ys) : List<&2, ST.SB>}
      %Equal.sym(List<&2, ST.SB>, ST.revb.go(t, Con{h, Nil{}}), sbapp(r, Con{h, Nil{}}), revb_sbapp(t, Con{h, Nil{}})) : {sbapp(r, Con{h, ys}) == sbapp(_, ys) : List<&2, ST.SB>}
      %Equal.sym(List<&2, ST.SB>, sbapp(sbapp(r, Con{h, Nil{}}), ys), sbapp(r, sbapp(Con{h, Nil{}}, ys)), sbapp_assoc(r, Con{h, Nil{}}, ys)) : {sbapp(r, Con{h, ys}) == _ : List<&2, ST.SB>}
      {==}

def alleqs_sbapp(xs: List<&2, ST.SB>, +ys: List<&2, ST.SB>) -> {ST.alleqs(sbapp(xs, ys)) == ST.app(ST.alleqs(xs), ST.alleqs(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{ST.SB{+es, +vs}, +t}:
      %Equal.sym(List<&2, Nat>, ST.alleqs(sbapp(t, ys)), ST.app(ST.alleqs(t), ST.alleqs(ys)), alleqs_sbapp(t, ys)) : {ST.app(es, _) == ST.app(ST.app(es, ST.alleqs(t)), ST.alleqs(ys)) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, ST.app(ST.app(es, ST.alleqs(t)), ST.alleqs(ys)), ST.app(es, ST.app(ST.alleqs(t), ST.alleqs(ys))), TJ.app_assoc(es, ST.alleqs(t), ST.alleqs(ys)))

def allvars_sbapp(xs: List<&2, ST.SB>, +ys: List<&2, ST.SB>) -> {ST.allvars(sbapp(xs, ys)) == ST.app(ST.allvars(xs), ST.allvars(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{ST.SB{+es, +vs}, +t}:
      %Equal.sym(List<&2, Nat>, ST.allvars(sbapp(t, ys)), ST.app(ST.allvars(t), ST.allvars(ys)), allvars_sbapp(t, ys)) : {ST.app(vs, _) == ST.app(ST.app(vs, ST.allvars(t)), ST.allvars(ys)) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, ST.app(ST.app(vs, ST.allvars(t)), ST.allvars(ys)), ST.app(vs, ST.app(ST.allvars(t), ST.allvars(ys))), TJ.app_assoc(vs, ST.allvars(t), ST.allvars(ys)))

def lkb_join(xs: List<&2, ST.SB>, +ys: List<&2, ST.SB>, +vm: List<&2, Maybe<&2, Nat>>, +h1: {lkb(vm, xs) == True{} : Bool}, h2: {lkb(vm, ys) == True{} : Bool}) -> {lkb(vm, sbapp(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h2
    case Con{ST.SB{+es, +vs}, +t}:
      L.band_i(nleq(vs, ST.look(vm, es)), lkb(vm, sbapp(t, ys)), L.band_l(nleq(vs, ST.look(vm, es)), lkb(vm, t), h1), lkb_join(t, ys, vm, L.band_r(nleq(vs, ST.look(vm, es)), lkb(vm, t), h1), h2))

def vchain_join(xs: List<&2, ST.SB>, +ys: List<&2, ST.SB>, +known: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +h1: {vchain(xs, known, adj) == True{} : Bool}, h2: {vchain(ys, ST.app(known, ST.allvars(xs)), adj) == True{} : Bool}) -> {vchain(sbapp(xs, ys), known, adj) == True{} : Bool}:
  match xs:
    case Nil{}:
      %TJ.app_nil(known) : {vchain(ys, _, adj) == True{} : Bool}
      h2
    case Con{ST.SB{+es, +vs}, +t}:
      L.band_i(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(sbapp(t, ys), ST.app(known, vs), adj), L.band_l(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(t, ST.app(known, vs), adj), h1), vchain_join(t, ys, ST.app(known, vs), adj, L.band_r(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(t, ST.app(known, vs), adj), h1), (%Equal.sym(List<&2, Nat>, ST.app(ST.app(known, vs), ST.allvars(t)), ST.app(known, ST.app(vs, ST.allvars(t))), TJ.app_assoc(known, vs, ST.allvars(t))) : {vchain(ys, _, adj) == True{} : Bool}
        h2)))

# with mates as unknowns, the unknowns are the equations' mates
def lkb_vars(+vm: List<&2, Maybe<&2, Nat>>, bs: List<&2, ST.SB>, +h: {lkb(vm, bs) == True{} : Bool}) -> {ST.allvars(bs) == ST.look(vm, ST.alleqs(bs)) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{ST.SB{+es, +vs}, +t}:
      +h1 = L.band_l(nleq(vs, ST.look(vm, es)), lkb(vm, t), h)
      %Equal.sym(List<&2, Nat>, ST.look(vm, ST.app(es, ST.alleqs(t))), ST.app(ST.look(vm, es), ST.look(vm, ST.alleqs(t))), look_app(vm, es, ST.alleqs(t))) : {ST.app(vs, ST.allvars(t)) == _ : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, vs, ST.look(vm, es), nleq_ok(vs, ST.look(vm, es), h1)) : {ST.app(_, ST.allvars(t)) == ST.app(ST.look(vm, es), ST.look(vm, ST.alleqs(t))) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, ST.allvars(t), ST.look(vm, ST.alleqs(t)), lkb_vars(vm, t, L.band_r(nleq(vs, ST.look(vm, es)), lkb(vm, t), h))) : {ST.app(ST.look(vm, es), _) == ST.app(ST.look(vm, es), ST.look(vm, ST.alleqs(t))) : List<&2, Nat>}
      {==}

# The blocks
# ----------
# blocks(cs, ok, adj, vm, known, acc): ok is the check of cs's first
# component against known (the pins, then acc's unknowns); acc holds the
# blocks so far, newest first. With tt the equations of acc and cs: the
# blocks hold tt in order, and given that every variable tt uses is a pin
# or a mate of tt, each block is valid with its mates as unknowns.

def snoc_eqs(+acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>) -> {ST.alleqs(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})) == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), es) : List<&2, Nat>}:
  +r = ST.revb.go(acc, Nil{})
  %Equal.sym(List<&2, ST.SB>, ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}}), sbapp(r, Con{ST.SB{es, vs}, Nil{}}), revb_sbapp(acc, Con{ST.SB{es, vs}, Nil{}})) : {ST.alleqs(_) == ST.app(ST.alleqs(r), es) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, ST.alleqs(sbapp(r, Con{ST.SB{es, vs}, Nil{}})), ST.app(ST.alleqs(r), ST.app(es, Nil{})), alleqs_sbapp(r, Con{ST.SB{es, vs}, Nil{}})) : {_ == ST.app(ST.alleqs(r), es) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, ST.app(es, Nil{}), es, TJ.app_nil(es)) : {ST.app(ST.alleqs(r), _) == ST.app(ST.alleqs(r), es) : List<&2, Nat>}
  {==}

def snoc_vars(+acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>) -> {ST.allvars(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})) == ST.app(ST.allvars(ST.revb.go(acc, Nil{})), vs) : List<&2, Nat>}:
  +r = ST.revb.go(acc, Nil{})
  %Equal.sym(List<&2, ST.SB>, ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}}), sbapp(r, Con{ST.SB{es, vs}, Nil{}}), revb_sbapp(acc, Con{ST.SB{es, vs}, Nil{}})) : {ST.allvars(_) == ST.app(ST.allvars(r), vs) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, ST.allvars(sbapp(r, Con{ST.SB{es, vs}, Nil{}})), ST.app(ST.allvars(r), ST.app(vs, Nil{})), allvars_sbapp(r, Con{ST.SB{es, vs}, Nil{}})) : {_ == ST.app(ST.allvars(r), vs) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, ST.app(vs, Nil{}), vs, TJ.app_nil(vs)) : {ST.app(ST.allvars(r), _) == ST.app(ST.allvars(r), vs) : List<&2, Nat>}
  {==}

# a block of tt's equations next: acc's equations, then cs's
def next_eqs(+acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>, +cc: List<&2, Nat>) -> {ST.app(ST.alleqs(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})), cc) == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.app(es, cc)) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, ST.alleqs(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})), ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), es), snoc_eqs(acc, es, vs)) : {ST.app(_, cc) == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.app(es, cc)) : List<&2, Nat>}
  TJ.app_assoc(ST.alleqs(ST.revb.go(acc, Nil{})), es, cc)

# the blocks hold acc's equations, then cs's
def bl_eqs(cs: List<&2, List<&2, Nat>>, ok: Bool, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +known: List<&2, Nat>, +acc: List<&2, ST.SB>) -> {ST.alleqs(ST.blocks(cs, ok, adj, vm, known, acc)) == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.cats(cs)) : List<&2, Nat>}:
  match cs ok:
    case Nil{} ok:
      %Equal.sym(List<&2, Nat>, ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), Nil{}), ST.alleqs(ST.revb.go(acc, Nil{})), TJ.app_nil(ST.alleqs(ST.revb.go(acc, Nil{})))) : {ST.alleqs(ST.revb.go(acc, Nil{})) == _ : List<&2, Nat>}
      {==}
    case Con{+comp, +rest} True{}:
      +known2 = ST.app(known, ST.look(vm, comp))
      +b = {ST.SB{comp, ST.look(vm, comp)} : ST.SB}
      %Equal.sym(List<&2, Nat>, ST.alleqs(ST.blocks(rest, ST.valid(ST.hdl(rest), adj, vm, known2), adj, vm, known2, Con{b, acc})), ST.app(ST.alleqs(ST.revb.go(acc, Con{b, Nil{}})), ST.cats(rest)), bl_eqs(rest, ST.valid(ST.hdl(rest), adj, vm, known2), adj, vm, known2, Con{b, acc})) : {_ == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.app(comp, ST.cats(rest))) : List<&2, Nat>}
      next_eqs(acc, comp, ST.look(vm, comp), ST.cats(rest))
    case Con{+comp, +rest} False{}:
      snoc_eqs(acc, ST.cats(Con{comp, rest}), ST.look(vm, ST.cats(Con{comp, rest})))

def binv(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +pins: List<&2, Nat>, +bs: List<&2, ST.SB>) -> Bool:
  SV.band(vchain(bs, pins, adj), lkb(vm, bs))

def rot3(+p: List<&2, Nat>, +a: List<&2, Nat>, +l: List<&2, Nat>) -> {L.subl(ST.app(p, ST.app(a, l)), ST.app(l, ST.app(p, a))) == True{} : Bool}:
  +z = ST.app(l, ST.app(p, a))
  TJ.subl_app(p, ST.app(a, l), z, L.subl_trans(p, ST.app(p, a), z, TJ.app_subl_l(p, a), TJ.app_subl_r(l, ST.app(p, a))), TJ.subl_app(a, l, z, L.subl_trans(a, ST.app(p, a), z, TJ.app_subl_r(p, a), TJ.app_subl_r(l, ST.app(p, a))), TJ.app_subl_l(l, ST.app(p, a))))

# adding block b = SB{es, vs} after the blocks r: still valid with mates
def binv_snoc(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +pins: List<&2, Nat>, +acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>, +h: {binv(adj, vm, pins, ST.revb.go(acc, Nil{})) == True{} : Bool}, hv: {L.subl(ST.uses(es, adj), ST.app(vs, ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))))) == True{} : Bool}, hl: {nleq(vs, ST.look(vm, es)) == True{} : Bool}) -> {binv(adj, vm, pins, ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})) == True{} : Bool}:
  +r = ST.revb.go(acc, Nil{})
  +b1 = {Con{ST.SB{es, vs}, Nil{}} : List<&2, ST.SB>}
  %Equal.sym(List<&2, ST.SB>, ST.revb.go(acc, b1), sbapp(r, b1), revb_sbapp(acc, b1)) : {binv(adj, vm, pins, _) == True{} : Bool}
  L.band_i(vchain(sbapp(r, b1), pins, adj), lkb(vm, sbapp(r, b1)), vchain_join(r, b1, pins, adj, L.band_l(vchain(r, pins, adj), lkb(vm, r), h), L.band_i(L.subl(ST.uses(es, adj), ST.app(vs, ST.app(pins, ST.allvars(r)))), True{}, hv, {==})), lkb_join(r, b1, vm, L.band_r(vchain(r, pins, adj), lkb(vm, r), h), L.band_i(nleq(vs, ST.look(vm, es)), True{}, hl, {==})))

# the block of what is left (after a failed check) is valid
def left_ok(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +pins: List<&2, Nat>, +r: List<&2, ST.SB>, +lft: List<&2, Nat>, +tt: List<&2, Nat>, +et: {tt == ST.app(ST.alleqs(r), lft) : List<&2, Nat>}, hlk: {lkb(vm, r) == True{} : Bool}, hall: {L.subl(ST.uses(tt, adj), ST.app(pins, ST.look(vm, tt))) == True{} : Bool}) -> {L.subl(ST.uses(lft, adj), ST.app(ST.look(vm, lft), ST.app(pins, ST.allvars(r)))) == True{} : Bool}:
  +a = ST.alleqs(r)
  %Equal.sym(List<&2, Nat>, ST.allvars(r), ST.look(vm, a), lkb_vars(vm, r, hlk)) : {L.subl(ST.uses(lft, adj), ST.app(ST.look(vm, lft), ST.app(pins, _))) == True{} : Bool}
  L.subl_trans(ST.uses(lft, adj), ST.uses(tt, adj), ST.app(ST.look(vm, lft), ST.app(pins, ST.look(vm, a))), uses_mono(lft, tt, adj, (%Equal.sym(List<&2, Nat>, tt, ST.app(a, lft), et) : {L.subl(lft, _) == True{} : Bool}
    TJ.app_subl_r(a, lft))), L.subl_trans(ST.uses(tt, adj), ST.app(pins, ST.look(vm, tt)), ST.app(ST.look(vm, lft), ST.app(pins, ST.look(vm, a))), hall, (%Equal.sym(List<&2, Nat>, tt, ST.app(a, lft), et) : {L.subl(ST.app(pins, ST.look(vm, _)), ST.app(ST.look(vm, lft), ST.app(pins, ST.look(vm, a)))) == True{} : Bool}
    (%Equal.sym(List<&2, Nat>, ST.look(vm, ST.app(a, lft)), ST.app(ST.look(vm, a), ST.look(vm, lft)), look_app(vm, a, lft)) : {L.subl(ST.app(pins, _), ST.app(ST.look(vm, lft), ST.app(pins, ST.look(vm, a)))) == True{} : Bool}
      rot3(pins, ST.look(vm, a), ST.look(vm, lft))))))

def known_next(+pins: List<&2, Nat>, +known: List<&2, Nat>, +acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>, ek: {known == ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))) : List<&2, Nat>}) -> {ST.app(known, vs) == ST.app(pins, ST.allvars(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}}))) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, ST.allvars(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})), ST.app(ST.allvars(ST.revb.go(acc, Nil{})), vs), snoc_vars(acc, es, vs)) : {ST.app(known, vs) == ST.app(pins, _) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, known, ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))), ek) : {ST.app(_, vs) == ST.app(pins, ST.app(ST.allvars(ST.revb.go(acc, Nil{})), vs)) : List<&2, Nat>}
  TJ.app_assoc(pins, ST.allvars(ST.revb.go(acc, Nil{})), vs)

def tt_next(+tt: List<&2, Nat>, +acc: List<&2, ST.SB>, +es: List<&2, Nat>, +vs: List<&2, Nat>, +cc: List<&2, Nat>, et: {tt == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.app(es, cc)) : List<&2, Nat>}) -> {tt == ST.app(ST.alleqs(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})), cc) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, ST.app(ST.alleqs(ST.revb.go(acc, Con{ST.SB{es, vs}, Nil{}})), cc), ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.app(es, cc)), next_eqs(acc, es, vs, cc)) : {tt == _ : List<&2, Nat>}
  et

def valid_subl(+comp: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +known: List<&2, Nat>, +pins: List<&2, Nat>, +acc: List<&2, ST.SB>, eok: {True{} == ST.valid(comp, adj, vm, known) : Bool}, ek: {known == ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))) : List<&2, Nat>}) -> {L.subl(ST.uses(comp, adj), ST.app(ST.look(vm, comp), ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))))) == True{} : Bool}:
  %ek : {L.subl(ST.uses(comp, adj), ST.app(ST.look(vm, comp), _)) == True{} : Bool}
  allin_subl(ST.uses(comp, adj), ST.app(ST.look(vm, comp), known), Equal.sym(Bool, True{}, ST.valid(comp, adj, vm, known), eok))

# every block valid, with its mates as unknowns
def bl_ok(cs: List<&2, List<&2, Nat>>, ok: Bool, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +known: List<&2, Nat>, +acc: List<&2, ST.SB>, +pins: List<&2, Nat>, +tt: List<&2, Nat>, eok: {ok == ST.valid(ST.hdl(cs), adj, vm, known) : Bool}, +ek: {known == ST.app(pins, ST.allvars(ST.revb.go(acc, Nil{}))) : List<&2, Nat>}, et: {tt == ST.app(ST.alleqs(ST.revb.go(acc, Nil{})), ST.cats(cs)) : List<&2, Nat>}, +h: {binv(adj, vm, pins, ST.revb.go(acc, Nil{})) == True{} : Bool}, +hall: {L.subl(ST.uses(tt, adj), ST.app(pins, ST.look(vm, tt))) == True{} : Bool}) -> {binv(adj, vm, pins, ST.blocks(cs, ok, adj, vm, known, acc)) == True{} : Bool}:
  match cs ok:
    case Nil{} ok:
      h
    case Con{+comp, +rest} True{}:
      +lc = ST.look(vm, comp)
      +known2 = ST.app(known, lc)
      +b = {ST.SB{comp, lc} : ST.SB}
      bl_ok(rest, ST.valid(ST.hdl(rest), adj, vm, known2), adj, vm, known2, Con{b, acc}, pins, tt, {==}, known_next(pins, known, acc, comp, lc, ek), tt_next(tt, acc, comp, lc, ST.cats(rest), et), binv_snoc(adj, vm, pins, acc, comp, lc, h, valid_subl(comp, adj, vm, known, pins, acc, eok, ek), nleq_refl(lc)), hall)
    case Con{+comp, +rest} False{}:
      +lft = ST.cats(Con{comp, rest})
      +r = ST.revb.go(acc, Nil{})
      binv_snoc(adj, vm, pins, acc, lft, ST.look(vm, lft), h, left_ok(adj, vm, pins, r, lft, tt, et, L.band_r(vchain(r, pins, adj), lkb(vm, r), h), hall), nleq_refl(ST.look(vm, lft)))

# Counting lists
# --------------

def iota_ge.go(+k: Nat, +x: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(x, k) == b : Bool}, h: {SV.bor(b, SV.mem(x, t)) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {KA.natle(1n+k, x) == True{} : Bool}) -> {KA.natle(k, x) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, k, L.eq_ok(x, k, e)) : {KA.natle(k, _) == True{} : Bool}
      KA.natle_refl(k)
    case False{}:
      KA.natle_pred(k, x, ih(h))

def iota_ge(n: Nat, +k: Nat, +x: Nat, h: {SV.mem(x, ST.iota(n, k)) == True{} : Bool}) -> {KA.natle(k, x) == True{} : Bool}:
  match n:
    case 0n:
      absurd({KA.natle(k, x) == True{} : Bool}, KA.ft(h))
    case 1n++m:
      iota_ge.go(k, x, ST.iota(m, 1n+k), SV.eq(x, k), {==}, h, p => iota_ge(m, 1n+k, x, p))

def iota_new(m: Nat, +k: Nat, b: Bool, e: {SV.mem(k, ST.iota(m, 1n+k)) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.natlt_irr(k, iota_ge(m, 1n+k, k, e)))
    case False{}:
      {==}

def iota_dist(n: Nat, +k: Nat) -> {SV.distinct(ST.iota(n, k)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.dist_con(k, ST.iota(m, 1n+k), iota_new(m, k, SV.mem(k, ST.iota(m, 1n+k)), {==}), iota_dist(m, 1n+k))

def iota_len(n: Nat, +k: Nat) -> {SV.len(ST.iota(n, k)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      %Equal.sym(Nat, SV.len(ST.iota(m, 1n+k)), m, iota_len(m, 1n+k)) : {1n+_ == 1n+m : Nat}
      {==}

def inter_dist(xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SV.distinct(xs) == True{} : Bool}) -> {SV.distinct(ST.inter(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      MX.mg_dist(ST.bnot(ST.mem(x, ys)), x, ST.inter(t, ys), t, L.dist_hd(x, t, h), MX.inter_subx(t, ys), inter_dist(t, ys, L.dist_tl(x, t, h)))

def mem_down.go(+x: Nat, +m: Nat, b: Bool, e: {SV.eq(x, m) == b : Bool}, h: {KA.natle(x, m) == True{} : Bool}, ih: {KA.natle(1n+x, m) == True{} : Bool} -> {SV.mem(x, ST.down(m)) == True{} : Bool}) -> {SV.bor(b, SV.mem(x, ST.down(m))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(TJ.lt_of_ne(x, m, h, e))

# x < n: x in n - 1, .., 0
def mem_down(+x: Nat, n: Nat, h: {KA.natle(1n+x, n) == True{} : Bool}) -> {SV.mem(x, ST.down(n)) == True{} : Bool}:
  match n:
    case 0n:
      absurd({SV.mem(x, Nil{}) == True{} : Bool}, KA.ft(h))
    case 1n++m:
      mem_down.go(x, m, SV.eq(x, m), {==}, h, p => mem_down(x, m, p))

def below_down(xs: List<&2, Nat>, +n: Nat, +h: {SV.below(xs, n) == True{} : Bool}) -> {L.subl(xs, ST.down(n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, ST.down(n), mem_down(x, n, D.below_hd(x, t, n, h)), below_down(t, n, D.below_tl(x, t, n, h)))

def ne_succ(k: Nat, +i: Nat) -> {SV.eq(Nat.add(k, 1n+i), k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+k2:
      ne_succ(k2, i)

# Nat.add(k, j) in keys(vm, k): entry j of vm is matched
def keys_some(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, j: Nat, h: {SV.mem(Nat.add(k, j), MX.keys(vm, k)) == True{} : Bool}) -> {L.issome(ST.getm(vm, j)) == True{} : Bool}:
  match vm j:
    case Nil{} j:
      absurd({L.issome(ST.getm(Nil{}, j)) == True{} : Bool}, KA.ft(h))
    case Con{None{}, +t} 0n:
      absurd({L.issome(None{}) == True{} : Bool}, KA.natlt_irr(k, MX.keys_ge(t, 1n+k, k, MX.mem_k0(k, MX.keys(t, 1n+k), h))))
    case Con{Some{x}, +t} 0n:
      {==}
    case Con{None{}, +t} 1n++i:
      keys_some(t, 1n+k, i, MX.mem_ks(k, i, MX.keys(t, 1n+k), h))
    case Con{Some{x}, +t} 1n++i:
      keys_some(t, 1n+k, i, MX.mem_ks(k, i, MX.keys(t, 1n+k), L.mem_tl_inv(Nat.add(k, 1n+i), k, MX.keys(t, 1n+k), h, ne_succ(k, i))))

def cr_e(+a: Nat, +b: Nat, +f: Nat, +nv: Nat, h1: {Nat.add(a, f) == nv : Nat}, h2: {Nat.add(b, f) == nv : Nat}) -> {Nat.add(f, a) == Nat.add(f, b) : Nat}:
  %LN.add_comm(a, f) : {_ == Nat.add(f, b) : Nat}
  %Equal.sym(Nat, Nat.add(a, f), nv, h1) : {_ == Nat.add(f, b) : Nat}
  %LN.add_comm(b, f) : {nv == _ : Nat}
  %Equal.sym(Nat, Nat.add(b, f), nv, h2) : {nv == _ : Nat}
  {==}

# a + f = nv = b + f: a = b
def cancel_r(+a: Nat, +b: Nat, +f: Nat, +nv: Nat, h1: {Nat.add(a, f) == nv : Nat}, h2: {Nat.add(b, f) == nv : Nat}) -> {a == b : Nat}:
  LN.add_cancel(f, a, b, cr_e(a, b, f, nv, h1, h2))

def le_rw_l(+a: Nat, +b: Nat, +c: Nat, e: {a == c : Nat}, h: {KA.natle(a, b) == True{} : Bool}) -> {KA.natle(c, b) == True{} : Bool}:
  %e : {KA.natle(_, b) == True{} : Bool}
  h

# The variable side's end
# -----------------------
# vm: each kept equation's variable, fs: the pins (the failed searches)

def vside(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>) -> Bool:
  SV.band(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))))

def vside_kg(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.subl(MX.keys(vm, 0n), good) == True{} : Bool}:
  L.band_l(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h)

def vside_vd(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))

def vside_fd(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.distinct(fs) == True{} : Bool}:
  L.band_l(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h)))

def vside_ff(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {MX.disj(fs, ST.somes(vm)) == True{} : Bool}:
  L.band_l(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))))

def vside_all(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))) == True{} : Bool}:
  L.band_l(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h)))))

def vside_mb(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))))))

def vside_fb(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.below(fs, nv) == True{} : Bool}:
  L.band_l(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h)))))))

def vside_gd(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.distinct(good) == True{} : Bool}:
  L.band_l(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))), L.band_r(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))))))))

def vside_gb(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.below(good, nq) == True{} : Bool}:
  L.band_l(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)), L.band_r(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))), L.band_r(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h)))))))))

def vside_gs(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.eq(SV.len(good), SV.len(ST.somes(vm))) == True{} : Bool}:
  L.band_l(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv), L.band_r(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)), L.band_r(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))), L.band_r(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))))))))))

def vside_cnt(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv) == True{} : Bool}:
  L.band_r(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv), L.band_r(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)), L.band_r(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))), L.band_r(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), L.band_r(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), L.band_r(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), L.band_r(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h))))))))))

def vside_mk(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h_kg: {L.subl(MX.keys(vm, 0n), good) == True{} : Bool}, h_vd: {SV.distinct(ST.somes(vm)) == True{} : Bool}, h_fd: {SV.distinct(fs) == True{} : Bool}, h_ff: {MX.disj(fs, ST.somes(vm)) == True{} : Bool}, h_all: {L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))) == True{} : Bool}, h_mb: {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool}, h_fb: {SV.below(fs, nv) == True{} : Bool}, h_gd: {SV.distinct(good) == True{} : Bool}, h_gb: {SV.below(good, nq) == True{} : Bool}, h_gs: {SV.eq(SV.len(good), SV.len(ST.somes(vm))) == True{} : Bool}, h_cnt: {SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv) == True{} : Bool}) -> {vside(nq, nv, good, vm, fs) == True{} : Bool}:
  L.band_i(L.subl(MX.keys(vm, 0n), good), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))))), h_kg, L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))))), h_vd, L.band_i(SV.distinct(fs), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))))), h_fd, L.band_i(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))))), h_ff, L.band_i(L.subl(ST.down(nv), ST.app(fs, ST.somes(vm))), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))))), h_all, L.band_i(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))))), h_mb, L.band_i(SV.below(fs, nv), SV.band(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)))), h_fb, L.band_i(SV.distinct(good), SV.band(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv))), h_gd, L.band_i(SV.below(good, nq), SV.band(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv)), h_gb, L.band_i(SV.eq(SV.len(good), SV.len(ST.somes(vm))), SV.eq(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv), h_gs, h_cnt))))))))))

def vsides(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, kd: ST.KD) -> Bool:
  match kd:
    case ST.KD{vm, fs, dd}:
      vside(nq, nv, good, vm, fs)

def all_len(+fs: List<&2, Nat>, +ss: List<&2, Nat>, +nv: Nat, hc: {Nat.add(SV.len(ss), SV.len(fs)) == nv : Nat}) -> {KA.natle(SV.len(ST.down(nv)), SV.len(ST.app(fs, ss))) == True{} : Bool}:
  %Equal.sym(Nat, SV.len(ST.down(nv)), nv, MX.down_len(nv)) : {KA.natle(_, SV.len(ST.app(fs, ss))) == True{} : Bool}
  %Equal.sym(Nat, SV.len(ST.app(fs, ss)), Nat.add(SV.len(fs), SV.len(ss)), len_app(fs, ss)) : {KA.natle(nv, _) == True{} : Bool}
  %LN.add_comm(SV.len(ss), SV.len(fs)) : {KA.natle(nv, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(SV.len(ss), SV.len(fs)), nv, hc) : {KA.natle(nv, _) == True{} : Bool}
  KA.natle_refl(nv)

def vend.go(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +kn: Nat, kd: ST.KD, +h: {MX.kinvs(ST.transpose(nv, 0n, ST.inter(ST.iota(ST.len.q(full), 0n), ST.somes(vmr)), ST.adj(full)), ST.len.q(full), ST.down(nv), SV.len(ST.down(nv)), Nil{}, kd) == True{} : Bool}, +hp: {SV.band(SV.distinct(ST.KD.red(kd)), SV.band(SV.below(ST.KD.red(kd), nv), SV.eq(Nat.add(kn, SV.len(ST.KD.red(kd))), nv))) == True{} : Bool}, hdr: {SV.distinct(ST.somes(vmr)) == True{} : Bool}, hcr: {SV.len(ST.somes(vmr)) == kn : Nat}) -> {vsides(ST.len.q(full), nv, ST.inter(ST.iota(ST.len.q(full), 0n), ST.somes(vmr)), kd) == True{} : Bool}:
  match kd:
    case ST.KD{+vm, +fs, +dd}:
      +adj = ST.adj(full)
      +nq = ST.len.q(full)
      +good = ST.inter(ST.iota(nq, 0n), ST.somes(vmr))
      +adjt = ST.transpose(nv, 0n, good, adj)
      +us = ST.down(nv)
      +c = SV.len(ST.down(nv))
      +js = {Nil{} : List<&2, Nat>}
      +a = SV.len(ST.somes(vm))
      +f = SV.len(fs)
      +g = SV.len(good)
      +hp2 = L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.eq(Nat.add(kn, f), nv)), hp)
      +hc = MX.cnt_end(a, f, nv, MX.kinv_cnt(adjt, nq, us, c, js, vm, fs, dd, h))
      +hk = L.eq_ok(Nat.add(kn, f), nv, L.band_r(SV.below(fs, nv), SV.eq(Nat.add(kn, f), nv), hp2))
      +hak = cancel_r(a, kn, f, nv, hc, hk)
      +hkg = MX.keys_tr(vm, 0n, nv, 0n, good, adj, MX.kinv_valid(adjt, nq, us, c, js, vm, fs, dd, h))
      +hgd = inter_dist(ST.iota(nq, 0n), ST.somes(vmr), iota_dist(nq, 0n))
      +hvd = MX.kinv_dist(adjt, nq, us, c, js, vm, fs, dd, h)
      +hfd = MX.kinv_fdist(adjt, nq, us, c, js, vm, fs, dd, h)
      +hff = MX.kinv_ffree(adjt, nq, us, c, js, vm, fs, dd, h)
      +hmus = MX.kinv_mus(adjt, nq, us, c, js, vm, fs, dd, h)
      +hg1 = KA.natle_rw(g, SV.len(ST.somes(vmr)), a, (%Equal.sym(Nat, a, kn, hak) : {SV.len(ST.somes(vmr)) == _ : Nat}
        hcr), L.pig(good, ST.somes(vmr), hgd, MX.inter_sub(ST.iota(nq, 0n), ST.somes(vmr))))
      +hg2 = le_rw_l(SV.len(MX.keys(vm, 0n)), g, a, MX.keys_len(vm, 0n), L.pig(MX.keys(vm, 0n), good, MX.keys_dist(vm, 0n), hkg))
      vside_mk(nq, nv, good, vm, fs, hkg, hvd, hfd, hff, pigc(ST.app(fs, ST.somes(vm)), us, MX.dist_app(fs, ST.somes(vm), hfd, hvd, hff), TJ.subl_app(fs, ST.somes(vm), us, MX.kinv_fus(adjt, nq, us, c, js, vm, fs, dd, h), hmus), all_len(fs, ST.somes(vm), nv, hc)), hmus, L.band_l(SV.below(fs, nv), SV.eq(Nat.add(kn, f), nv), hp2), hgd, D.below_subl(good, ST.iota(nq, 0n), nq, MX.inter_subx(ST.iota(nq, 0n), ST.somes(vmr)), MX.iota_below(nq, 0n)), D.eq_of(g, a, KA.natle_antisym(g, a, hg1, hg2)), D.eq_of(Nat.add(a, f), nv, hc))

# the variable side over the sketch's kept equations
def vend(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {vsides(ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))) == True{} : Bool}:
  +full = SK.Sketch.eqs(sk)
  +adj = ST.adj(full)
  +nq = ST.len.q(full)
  +nv = SO.nvars(sk)
  +vmr = SO.CS.vm(SO.rs_of(sk))
  +kn = SV.neqs(SO.kept(sk))
  +good = ST.inter(ST.iota(nq, 0n), ST.somes(vmr))
  +adjt = ST.transpose(nv, 0n, good, adj)
  +hbg = D.below_subl(good, ST.iota(nq, 0n), nq, MX.inter_subx(ST.iota(nq, 0n), ST.somes(vmr)), MX.iota_below(nq, 0n))
  vend.go(full, nv, vmr, kn, MX.kvs(adj, nq, nv, good), MX.kwalk(ST.down(nv), adjt, nq, ST.down(nv), SV.len(ST.down(nv)), 1n+nq, ST.KD{ST.nones(nq), Nil{}, Nil{}}, MX.down_dist(nv), L.subl_refl(ST.down(nv)), MX.adjb_tr(nv, 0n, good, adj, nq, hbg), KA.natle_refl(1n+nq), MX.kinit(adjt, nq, ST.down(nv), ST.down(nv))), MX.pins_kv(full, nv, vmr, kn, MX.red_valid(sk, nv), RP.red_dist(sk, nv, ha), RP.red_mlen(sk, nv, ha), RP.red_cnt(sk, nv, ha)), RP.red_dist(sk, nv, ha), RP.red_cnt(sk, nv, ha))

# What follows from the variable side's end
# -----------------------------------------

def le_of_eq(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {KA.natle(a, b) == True{} : Bool}:
  %e : {KA.natle(a, _) == True{} : Bool}
  KA.natle_refl(a)

def allm_mem.go(+x: Nat, +y: Nat, +t: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, b: Bool, e: {SV.eq(x, y) == b : Bool}, hm: {SV.bor(b, SV.mem(x, t)) == True{} : Bool}, +h: {L.allm(vm, Con{y, t}) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {L.allm(vm, t) == True{} : Bool} -> {L.issome(ST.getm(vm, x)) == True{} : Bool}) -> {L.issome(ST.getm(vm, x)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, y, L.eq_ok(x, y, e)) : {L.issome(ST.getm(vm, _)) == True{} : Bool}
      L.band_l(L.issome(ST.getm(vm, y)), L.allm(vm, t), h)
    case False{}:
      ih(hm, L.band_r(L.issome(ST.getm(vm, y)), L.allm(vm, t), h))

def allm_mem(+x: Nat, ys: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, hm: {SV.mem(x, ys) == True{} : Bool}, h: {L.allm(vm, ys) == True{} : Bool}) -> {L.issome(ST.getm(vm, x)) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({L.issome(ST.getm(vm, x)) == True{} : Bool}, KA.ft(hm))
    case Con{+y, +t}:
      allm_mem.go(x, y, t, vm, SV.eq(x, y), {==}, hm, h, p => q => allm_mem(x, t, vm, p, q))

def allm_keys(xs: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +h: {L.subl(xs, MX.keys(vm, 0n)) == True{} : Bool}) -> {L.allm(vm, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(L.issome(ST.getm(vm, x)), L.allm(vm, t), keys_some(vm, 0n, x, L.subl_hd(x, t, MX.keys(vm, 0n), h)), allm_keys(t, vm, L.subl_tl(x, t, MX.keys(vm, 0n), h)))

def allm_subl(xs: List<&2, Nat>, +ys: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hs: {L.subl(xs, ys) == True{} : Bool}, +h: {L.allm(vm, ys) == True{} : Bool}) -> {L.allm(vm, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(L.issome(ST.getm(vm, x)), L.allm(vm, t), allm_mem(x, ys, vm, L.subl_hd(x, t, ys, hs), h), allm_subl(t, ys, vm, L.subl_tl(x, t, ys, hs), h))

def vs_glen(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {SV.len(good) == SV.len(ST.somes(vm)) : Nat}:
  L.eq_ok(SV.len(good), SV.len(ST.somes(vm)), vside_gs(nq, nv, good, vm, fs, h))

# every kept equation is matched
def vs_sat(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.allm(vm, good) == True{} : Bool}:
  +ks = MX.keys(vm, 0n)
  +hl = KA.natle_rw(SV.len(good), SV.len(ST.somes(vm)), SV.len(ks), Equal.sym(Nat, SV.len(ks), SV.len(ST.somes(vm)), MX.keys_len(vm, 0n)), le_of_eq(SV.len(good), SV.len(ST.somes(vm)), vs_glen(nq, nv, good, vm, fs, h)))
  allm_keys(good, vm, pigc(ks, good, MX.keys_dist(vm, 0n), vside_kg(nq, nv, good, vm, fs, h), hl))

# the matched variables are the kept equations' mates
def vs_look(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.subl(ST.somes(vm), ST.look(vm, good)) == True{} : Bool}:
  +sat = vs_sat(nq, nv, good, vm, fs, h)
  +lk = ST.look(vm, good)
  +hl = KA.natle_rw(SV.len(ST.somes(vm)), SV.len(good), SV.len(lk), Equal.sym(Nat, SV.len(lk), SV.len(good), L.look_len(vm, good)), le_of_eq(SV.len(ST.somes(vm)), SV.len(good), Equal.sym(Nat, SV.len(good), SV.len(ST.somes(vm)), vs_glen(nq, nv, good, vm, fs, h))))
  pigc(lk, ST.somes(vm), L.look_dist(vm, good, vside_gd(nq, nv, good, vm, fs, h), sat, vside_vd(nq, nv, good, vm, fs, h)), L.look_subl(vm, good, sat), hl)

def ab_down(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +nv: Nat, +ha: {D.adjb(adj, nv) == True{} : Bool}) -> {alladj(js, adj, ST.down(nv)) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.band_i(L.subl(ST.nthl(adj, j), ST.down(nv)), alladj(t, adj, ST.down(nv)), below_down(ST.nthl(adj, j), nv, D.nthl_below(adj, j, nv, ha)), ab_down(t, adj, nv, ha))

# every variable a kept equation uses is a pin or a kept equation's mate
def vs_hall(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +h: {vside(nq, nv, good, vm, fs) == True{} : Bool}, +ha: {D.adjb(adj, nv) == True{} : Bool}) -> {L.subl(ST.uses(good, adj), ST.app(fs, ST.look(vm, good))) == True{} : Bool}:
  L.subl_trans(ST.uses(good, adj), ST.down(nv), ST.app(fs, ST.look(vm, good)), uses_sub(good, adj, ST.down(nv), ab_down(good, adj, nv, ha)), L.subl_trans(ST.down(nv), ST.app(fs, ST.somes(vm)), ST.app(fs, ST.look(vm, good)), vside_all(nq, nv, good, vm, fs, h), TJ.app_mono(fs, ST.somes(vm), ST.look(vm, good), vs_look(nq, nv, good, vm, fs, h))))

def move_subl(+a: List<&2, Nat>, +k: Nat, +b: List<&2, Nat>) -> {L.subl(ST.app(a, Con{k, b}), Con{k, ST.app(a, b)}) == True{} : Bool}:
  +z = {Con{k, ST.app(a, b)} : List<&2, Nat>}
  TJ.subl_app(a, Con{k, b}, z, L.subl_cons_r(a, k, ST.app(a, b), TJ.app_subl_l(a, b)), L.subl_con(k, b, z, L.mem_hd(k, ST.app(a, b)), L.subl_cons_r(b, k, ST.app(a, b), TJ.app_subl_r(a, b))))

# the equations invert maps variables to: the matched ones
def inv_keys(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, +em: List<&2, Maybe<&2, Nat>>) -> {L.subl(ST.somes(ST.invert(vm, k, em)), ST.app(MX.keys(vm, k), ST.somes(em))) == True{} : Bool}:
  match vm:
    case Nil{}:
      L.subl_refl(ST.somes(em))
    case Con{None{}, +t}:
      inv_keys(t, 1n+k, em)
    case Con{Some{+j}, +t}:
      +kt = MX.keys(t, 1n+k)
      L.subl_trans(ST.somes(ST.invert(t, 1n+k, ST.setm(em, j, Some{k}))), ST.app(kt, ST.somes(ST.setm(em, j, Some{k}))), Con{k, ST.app(kt, ST.somes(em))}, inv_keys(t, 1n+k, ST.setm(em, j, Some{k})), L.subl_trans(ST.app(kt, ST.somes(ST.setm(em, j, Some{k}))), ST.app(kt, Con{k, ST.somes(em)}), Con{k, ST.app(kt, ST.somes(em))}, TJ.app_mono(kt, ST.somes(ST.setm(em, j, Some{k})), Con{k, ST.somes(em)}, L.set_subl(em, j, k)), move_subl(kt, k, ST.somes(em))))

def sn_subl(+nv: Nat, +good: List<&2, Nat>) -> {L.subl(ST.somes(ST.nones(nv)), good) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, ST.somes(ST.nones(nv)), Nil{}, RP.somes_nones(nv)) : {L.subl(_, good) == True{} : Bool}
  {==}

# the equations Tarjan steps to are kept ones
def vs_inv(+nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vside(nq, nv, good, vm, fs) == True{} : Bool}) -> {L.subl(ST.somes(ST.invert(vm, 0n, ST.nones(nv))), good) == True{} : Bool}:
  L.subl_trans(ST.somes(ST.invert(vm, 0n, ST.nones(nv))), ST.app(MX.keys(vm, 0n), ST.somes(ST.nones(nv))), good, inv_keys(vm, 0n, ST.nones(nv)), TJ.subl_app(MX.keys(vm, 0n), ST.somes(ST.nones(nv)), good, vside_kg(nq, nv, good, vm, fs, h), sn_subl(nv, good)))

# The blocks over the kept equations
# ----------------------------------

# the solver's blocks, given the variable side's end (vm, pins fs)
def kblocks(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>) -> List<&2, ST.SB>:
  ST.blocks.of(adj, vm, fs, ST.comps(adj, ST.invert(vm, 0n, ST.nones(nv)), good, nq))

def sfacts(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>) -> Bool:
  SV.band(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))))

def sfacts_cd(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {SV.distinct(ST.alleqs(bs)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h)

def sfacts_cg(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {L.subl(good, ST.alleqs(bs)) == True{} : Bool}:
  L.band_l(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h))

def sfacts_gc(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {L.subl(ST.alleqs(bs), good) == True{} : Bool}:
  L.band_l(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h)))

def sfacts_ch(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {vchain(bs, fs, adj) == True{} : Bool}:
  L.band_l(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), L.band_r(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h))))

def sfacts_lk(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {lkb(vm, bs) == True{} : Bool}:
  L.band_l(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))), L.band_r(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), L.band_r(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h)))))

def sfacts_vpd(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {SV.distinct(ST.app(fs, ST.allvars(bs))) == True{} : Bool}:
  L.band_l(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)), L.band_r(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))), L.band_r(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), L.band_r(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h))))))

def sfacts_vpl(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv) == True{} : Bool}:
  L.band_l(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv), L.band_r(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)), L.band_r(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))), L.band_r(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), L.band_r(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h)))))))

def sfacts_vpb(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}) -> {SV.below(ST.app(fs, ST.allvars(bs)), nv) == True{} : Bool}:
  L.band_r(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv), L.band_r(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)), L.band_r(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))), L.band_r(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), L.band_r(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), L.band_r(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), L.band_r(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h)))))))

def sfacts_mk(+adj: List<&2, List<&2, Nat>>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h_cd: {SV.distinct(ST.alleqs(bs)) == True{} : Bool}, h_cg: {L.subl(good, ST.alleqs(bs)) == True{} : Bool}, h_gc: {L.subl(ST.alleqs(bs), good) == True{} : Bool}, h_ch: {vchain(bs, fs, adj) == True{} : Bool}, h_lk: {lkb(vm, bs) == True{} : Bool}, h_vpd: {SV.distinct(ST.app(fs, ST.allvars(bs))) == True{} : Bool}, h_vpl: {SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv) == True{} : Bool}, h_vpb: {SV.below(ST.app(fs, ST.allvars(bs)), nv) == True{} : Bool}) -> {sfacts(adj, nv, good, vm, fs, bs) == True{} : Bool}:
  L.band_i(SV.distinct(ST.alleqs(bs)), SV.band(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))))), h_cd, L.band_i(L.subl(good, ST.alleqs(bs)), SV.band(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))))), h_cg, L.band_i(L.subl(ST.alleqs(bs), good), SV.band(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))))), h_gc, L.band_i(vchain(bs, fs, adj), SV.band(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)))), h_ch, L.band_i(lkb(vm, bs), SV.band(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv))), h_lk, L.band_i(SV.distinct(ST.app(fs, ST.allvars(bs))), SV.band(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv)), h_vpd, L.band_i(SV.eq(SV.len(ST.app(fs, ST.allvars(bs))), nv), SV.below(ST.app(fs, ST.allvars(bs)), nv), h_vpl, h_vpb)))))))

def rw_dist(+x: List<&2, Nat>, +y: List<&2, Nat>, e: {x == y : List<&2, Nat>}, h: {SV.distinct(y) == True{} : Bool}) -> {SV.distinct(x) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, x, y, e) : {SV.distinct(_) == True{} : Bool}
  h

def rw_subl_r(+z: List<&2, Nat>, +x: List<&2, Nat>, +y: List<&2, Nat>, e: {x == y : List<&2, Nat>}, h: {L.subl(z, y) == True{} : Bool}) -> {L.subl(z, x) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, x, y, e) : {L.subl(z, _) == True{} : Bool}
  h

def rw_subl_l(+x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>, e: {x == y : List<&2, Nat>}, h: {L.subl(y, z) == True{} : Bool}) -> {L.subl(x, z) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, x, y, e) : {L.subl(_, z) == True{} : Bool}
  h

def vp_len(+fs: List<&2, Nat>, +a: List<&2, Nat>, +good: List<&2, Nat>, +ss: List<&2, Nat>, +nv: Nat, ha: {SV.len(a) == SV.len(good) : Nat}, hg: {SV.len(good) == SV.len(ss) : Nat}, hc: {Nat.add(SV.len(ss), SV.len(fs)) == nv : Nat}) -> {SV.len(ST.app(fs, a)) == nv : Nat}:
  %Equal.sym(Nat, SV.len(ST.app(fs, a)), Nat.add(SV.len(fs), SV.len(a)), len_app(fs, a)) : {_ == nv : Nat}
  %Equal.sym(Nat, SV.len(a), SV.len(good), ha) : {Nat.add(SV.len(fs), _) == nv : Nat}
  %Equal.sym(Nat, SV.len(good), SV.len(ss), hg) : {Nat.add(SV.len(fs), _) == nv : Nat}
  %LN.add_comm(SV.len(ss), SV.len(fs)) : {_ == nv : Nat}
  hc

def blocks_ok(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +h: {vside(nq, nv, good, vm, fs) == True{} : Bool}, +ha: {D.adjb(adj, nv) == True{} : Bool}) -> {sfacts(adj, nv, good, vm, fs, kblocks(adj, nq, nv, good, vm, fs)) == True{} : Bool}:
  +em = ST.invert(vm, 0n, ST.nones(nv))
  +cs = ST.comps(adj, em, good, nq)
  +cc = ST.cats(cs)
  +gd = vside_gd(nq, nv, good, vm, fs, h)
  +hl3 = KA.natle_rw(SV.len(good), SV.len(ST.down(nq)), nq, MX.down_len(nq), L.pig(good, ST.down(nq), gd, below_down(good, nq, vside_gb(nq, nv, good, vm, fs, h))))
  +hcp = TJ.comps_part(adj, em, good, nq, vs_inv(nq, nv, good, vm, fs, h), vside_gb(nq, nv, good, vm, fs, h), hl3)
  +hcp2 = L.band_r(SV.distinct(cc), SV.band(L.subl(good, cc), L.subl(cc, good)), hcp)
  +hcd = L.band_l(SV.distinct(cc), SV.band(L.subl(good, cc), L.subl(cc, good)), hcp)
  +hgc = L.band_l(L.subl(good, cc), L.subl(cc, good), hcp2)
  +hcg = L.band_r(L.subl(good, cc), L.subl(cc, good), hcp2)
  +ok0 = ST.valid(ST.hdl(cs), adj, vm, fs)
  +bs = ST.blocks(cs, ok0, adj, vm, fs, Nil{})
  +heq = {bl_eqs(cs, ok0, adj, vm, fs, Nil{}) : {ST.alleqs(bs) == cc : List<&2, Nat>}}
  +a = ST.alleqs(bs)
  +hall = L.subl_trans(ST.uses(cc, adj), ST.uses(good, adj), ST.app(fs, ST.look(vm, cc)), uses_mono(cc, good, adj, hcg), L.subl_trans(ST.uses(good, adj), ST.app(fs, ST.look(vm, good)), ST.app(fs, ST.look(vm, cc)), vs_hall(nq, nv, good, vm, fs, adj, h, ha), TJ.app_mono(fs, ST.look(vm, good), ST.look(vm, cc), look_mono(vm, good, cc, hgc))))
  +hb = bl_ok(cs, ok0, adj, vm, fs, Nil{}, fs, cc, {==}, Equal.sym(List<&2, Nat>, ST.app(fs, Nil{}), fs, TJ.app_nil(fs)), {==}, {==}, hall)
  +hlk = L.band_r(vchain(bs, fs, adj), lkb(vm, bs), hb)
  +had = rw_dist(a, cc, heq, hcd)
  +hga = rw_subl_r(good, a, cc, heq, hgc)
  +hag = rw_subl_l(a, cc, good, heq, hcg)
  +sat = allm_subl(a, good, vm, hag, vs_sat(nq, nv, good, vm, fs, h))
  +la = ST.look(vm, a)
  +hv = lkb_vars(vm, bs, hlk)
  sfacts_mk(adj, nv, good, vm, fs, bs, had, hga, hag, L.band_l(vchain(bs, fs, adj), lkb(vm, bs), hb), hlk, (%Equal.sym(List<&2, Nat>, ST.allvars(bs), la, hv) : {SV.distinct(ST.app(fs, _)) == True{} : Bool}
    MX.dist_app(fs, la, vside_fd(nq, nv, good, vm, fs, h), L.look_dist(vm, a, had, sat, vside_vd(nq, nv, good, vm, fs, h)), MX.disj_sub(fs, ST.somes(vm), la, vside_ff(nq, nv, good, vm, fs, h), L.look_subl(vm, a, sat)))), (%Equal.sym(List<&2, Nat>, ST.allvars(bs), la, hv) : {SV.eq(SV.len(ST.app(fs, _)), nv) == True{} : Bool}
    D.eq_of(SV.len(ST.app(fs, la)), nv, vp_len(fs, la, good, ST.somes(vm), nv, (%Equal.sym(Nat, SV.len(la), SV.len(a), L.look_len(vm, a)) : {_ == SV.len(good) : Nat}
      len_eq(a, good, had, gd, hag, hga)), vs_glen(nq, nv, good, vm, fs, h), L.eq_ok(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv, vside_cnt(nq, nv, good, vm, fs, h))))), (%Equal.sym(List<&2, Nat>, ST.allvars(bs), la, hv) : {SV.below(ST.app(fs, _), nv) == True{} : Bool}
    MX.below_app(fs, la, nv, vside_fb(nq, nv, good, vm, fs, h), D.below_subl(la, ST.down(nv), nv, L.subl_trans(la, ST.somes(vm), ST.down(nv), L.look_subl(vm, a, sat), vside_mb(nq, nv, good, vm, fs, h)), MX.down_below(nv)))))

# The plan checker's walk, its structural part
# --------------------------------------------
# swalk mirrors lib/plan.bend's walk: per block (size n, parameters pars,
# at offset o), the equations left are at least n, o + n <= nv, every
# parameter is earlier, the block's equations (renumbered) use only
# variables below o + n, and each such variable is the block's own
# (>= o) or a parameter; at the end o = nv and no equation is left.

# every variable of e is o or later, or a parameter
def ecov(+o: Nat, +pars: List<&2, Nat>, e: E.QExpr) -> Bool:
  match e:
    case E.QVar{+j}:
      SV.bor(KA.natle(o, j), SV.mem(j, pars))
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      SV.band(ecov(o, pars, a), ecov(o, pars, b))
    case E.QSub{a, b}:
      SV.band(ecov(o, pars, a), ecov(o, pars, b))
    case E.QMul{a, b}:
      SV.band(ecov(o, pars, a), ecov(o, pars, b))
    case E.QNeg{a}:
      ecov(o, pars, a)

def ecovs(+o: Nat, +pars: List<&2, Nat>, es: List<&2, E.QExpr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      SV.band(ecov(o, pars, e), ecovs(o, pars, t))

def swalk(bs: List<&2, ST.SkB>, +es: List<&2, E.QExpr>, +o: Nat, +nv: Nat) -> Bool:
  match bs:
    case Nil{}:
      SV.band(KA.nateq(o, nv), PL.isnil(es))
    case Con{ST.SkB{qs, vs, +pars}, t}:
      +n = ST.len(qs)
      SV.band(KA.natle(n, CK.eqlen(es)), SV.band(KA.natle(Nat.add(o, n), nv), SV.band(PL.pars_ok(o, pars), SV.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), SV.band(ecovs(o, pars, PL.takeq(n, es)), swalk(t, PL.dropq(n, es), Nat.add(o, n), nv))))))

# a block of size n (= len(qs))
def swalk_con(+qs: List<&2, Nat>, +vs: List<&2, Nat>, +pars: List<&2, Nat>, +t: List<&2, ST.SkB>, +es: List<&2, E.QExpr>, +o: Nat, +nv: Nat, +n: Nat, en: {ST.len(qs) == n : Nat}, h: {SV.band(KA.natle(n, CK.eqlen(es)), SV.band(KA.natle(Nat.add(o, n), nv), SV.band(PL.pars_ok(o, pars), SV.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), SV.band(ecovs(o, pars, PL.takeq(n, es)), swalk(t, PL.dropq(n, es), Nat.add(o, n), nv)))))) == True{} : Bool}) -> {swalk(Con{ST.SkB{qs, vs, pars}, t}, es, o, nv) == True{} : Bool}:
  %Equal.sym(Nat, ST.len(qs), n, en) : {SV.band(KA.natle(_, CK.eqlen(es)), SV.band(KA.natle(Nat.add(o, _), nv), SV.band(PL.pars_ok(o, pars), SV.band(PL.eqs_below(Nat.add(o, _), PL.takeq(_, es)), SV.band(ecovs(o, pars, PL.takeq(_, es)), swalk(t, PL.dropq(_, es), Nat.add(o, _), nv)))))) == True{} : Bool}
  h

# Reordered equations
# -------------------

def takeq_re(a: List<&2, Nat>, +b: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>) -> {PL.takeq(ST.len(a), PL.reorder(vp, full, ST.app(a, b))) == PL.reorder(vp, full, a) : List<&2, E.QExpr>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, E.QExpr>, PL.takeq(ST.len(t), PL.reorder(vp, full, ST.app(t, b))), PL.reorder(vp, full, t), takeq_re(t, b, vp, full)) : {Con{PL.rnv(vp, PL.eqget(full, x)), _} == Con{PL.rnv(vp, PL.eqget(full, x)), PL.reorder(vp, full, t)} : List<&2, E.QExpr>}
      {==}

def dropq_re(a: List<&2, Nat>, +b: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>) -> {PL.dropq(ST.len(a), PL.reorder(vp, full, ST.app(a, b))) == PL.reorder(vp, full, b) : List<&2, E.QExpr>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      dropq_re(t, b, vp, full)

def re_len(xs: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>) -> {CK.eqlen(PL.reorder(vp, full, xs)) == ST.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat, CK.eqlen(PL.reorder(vp, full, t)), ST.len(t), re_len(t, vp, full)) : {1n+_ == 1n+ST.len(t) : Nat}
      {==}

def len_app_ge(a: List<&2, Nat>, +b: List<&2, Nat>) -> {KA.natle(ST.len(a), ST.len(ST.app(a, b))) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      len_app_ge(t, b)

def lag(a: List<&2, Nat>, +b: List<&2, Nat>) -> {KA.natle(SV.len(a), SV.len(ST.app(a, b))) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      lag(t, b)

def eqget_eqat(es: List<&2, E.QExpr>, j: Nat) -> {PL.eqget(es, j) == SV.eqat(es, j) : E.QExpr}:
  match es j:
    case Nil{} j:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+i:
      eqget_eqat(t, i)

def pos_go_eq(b: Bool, +r1: Nat, +r2: Nat, e: {r1 == r2 : Nat}) -> {PL.pos.go(b, r1) == ST.pos.go(b, r2) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      %e : {1n+r1 == 1n+_ : Nat}
      {==}

def pos_eq(+v: Nat, xs: List<&2, Nat>) -> {PL.pos(v, xs) == ST.pos(v, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      pos_go_eq(KA.nateq(v, h), PL.pos(v, t), ST.pos(v, t), pos_eq(v, t))

# every entry of xs sits below m in vp
def posb(xs: List<&2, Nat>, +vp: List<&2, Nat>, +m: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(KA.natle(1n+ST.pos(x, vp), m), posb(t, vp, m))

def posb_of(ys: List<&2, Nat>, +k: List<&2, Nat>, +r: List<&2, Nat>, +h: {L.subl(ys, k) == True{} : Bool}) -> {posb(ys, ST.app(k, r), SV.len(k)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.band_i(KA.natle(1n+ST.pos(y, ST.app(k, r)), SV.len(k)), posb(t, ST.app(k, r), SV.len(k)), pos_in(y, k, r, L.subl_hd(y, t, k, h)), posb_of(t, k, r, L.subl_tl(y, t, k, h)))

def posb_at.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +vp: List<&2, Nat>, +m: Nat, b: Bool, e: {SV.eq(u, x) == b : Bool}, hm: {SV.bor(b, SV.mem(u, t)) == True{} : Bool}, +h: {posb(Con{x, t}, vp, m) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {posb(t, vp, m) == True{} : Bool} -> {KA.natle(1n+ST.pos(u, vp), m) == True{} : Bool}) -> {KA.natle(1n+ST.pos(u, vp), m) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, u, x, L.eq_ok(u, x, e)) : {KA.natle(1n+ST.pos(_, vp), m) == True{} : Bool}
      L.band_l(KA.natle(1n+ST.pos(x, vp), m), posb(t, vp, m), h)
    case False{}:
      ih(hm, L.band_r(KA.natle(1n+ST.pos(x, vp), m), posb(t, vp, m), h))

def posb_at(+u: Nat, xs: List<&2, Nat>, +vp: List<&2, Nat>, +m: Nat, hm: {SV.mem(u, xs) == True{} : Bool}, h: {posb(xs, vp, m) == True{} : Bool}) -> {KA.natle(1n+ST.pos(u, vp), m) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({KA.natle(1n+ST.pos(u, vp), m) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      posb_at.go(u, x, t, vp, m, SV.eq(u, x), {==}, hm, h, p => q => posb_at(u, t, vp, m, p, q))

def posb_sub(xs: List<&2, Nat>, +ys: List<&2, Nat>, +vp: List<&2, Nat>, +m: Nat, +hs: {L.subl(xs, ys) == True{} : Bool}, +h: {posb(ys, vp, m) == True{} : Bool}) -> {posb(xs, vp, m) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(KA.natle(1n+ST.pos(x, vp), m), posb(t, vp, m), posb_at(x, ys, vp, m, L.subl_hd(x, t, ys, hs), h), posb_sub(t, ys, vp, m, L.subl_tl(x, t, ys, hs), h))

# renumbered, e uses only variables below m
def rnv_below(e: E.QExpr, +vp: List<&2, Nat>, +m: Nat, +w: List<&2, Nat>, +hin: {SV.inside(e, w) == True{} : Bool}, +hw: {posb(w, vp, m) == True{} : Bool}) -> {SL.below(m, PL.rnv(vp, e)) == True{} : Bool}:
  match e:
    case E.QVar{+j}:
      %Equal.sym(Nat, PL.pos(j, vp), ST.pos(j, vp), pos_eq(j, vp)) : {KA.natle(1n+_, m) == True{} : Bool}
      posb_at(j, w, vp, m, hin, hw)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      KA.band_i(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), rnv_below(a, vp, m, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_below(b, vp, m, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QSub{+a, +b}:
      KA.band_i(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), rnv_below(a, vp, m, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_below(b, vp, m, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QMul{+a, +b}:
      KA.band_i(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), rnv_below(a, vp, m, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_below(b, vp, m, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QNeg{+a}:
      rnv_below(a, vp, m, w, hin, hw)

# every entry of xs, in vp, is o or later, or a parameter
def covb(xs: List<&2, Nat>, +vp: List<&2, Nat>, +o: Nat, +pars: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(SV.bor(KA.natle(o, ST.pos(x, vp)), SV.mem(ST.pos(x, vp), pars)), covb(t, vp, o, pars))

def covb_at.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +vp: List<&2, Nat>, +o: Nat, +pars: List<&2, Nat>, b: Bool, e: {SV.eq(u, x) == b : Bool}, hm: {SV.bor(b, SV.mem(u, t)) == True{} : Bool}, +h: {covb(Con{x, t}, vp, o, pars) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {covb(t, vp, o, pars) == True{} : Bool} -> {SV.bor(KA.natle(o, ST.pos(u, vp)), SV.mem(ST.pos(u, vp), pars)) == True{} : Bool}) -> {SV.bor(KA.natle(o, ST.pos(u, vp)), SV.mem(ST.pos(u, vp), pars)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, u, x, L.eq_ok(u, x, e)) : {SV.bor(KA.natle(o, ST.pos(_, vp)), SV.mem(ST.pos(_, vp), pars)) == True{} : Bool}
      L.band_l(SV.bor(KA.natle(o, ST.pos(x, vp)), SV.mem(ST.pos(x, vp), pars)), covb(t, vp, o, pars), h)
    case False{}:
      ih(hm, L.band_r(SV.bor(KA.natle(o, ST.pos(x, vp)), SV.mem(ST.pos(x, vp), pars)), covb(t, vp, o, pars), h))

def covb_at(+u: Nat, xs: List<&2, Nat>, +vp: List<&2, Nat>, +o: Nat, +pars: List<&2, Nat>, hm: {SV.mem(u, xs) == True{} : Bool}, h: {covb(xs, vp, o, pars) == True{} : Bool}) -> {SV.bor(KA.natle(o, ST.pos(u, vp)), SV.mem(ST.pos(u, vp), pars)) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.bor(KA.natle(o, ST.pos(u, vp)), SV.mem(ST.pos(u, vp), pars)) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      covb_at.go(u, x, t, vp, o, pars, SV.eq(u, x), {==}, hm, h, p => q => covb_at(u, t, vp, o, pars, p, q))

# renumbered, every variable of e is o or later, or a parameter
def rnv_cov(e: E.QExpr, +vp: List<&2, Nat>, +o: Nat, +pars: List<&2, Nat>, +w: List<&2, Nat>, +hin: {SV.inside(e, w) == True{} : Bool}, +hw: {covb(w, vp, o, pars) == True{} : Bool}) -> {ecov(o, pars, PL.rnv(vp, e)) == True{} : Bool}:
  match e:
    case E.QVar{+j}:
      %Equal.sym(Nat, PL.pos(j, vp), ST.pos(j, vp), pos_eq(j, vp)) : {SV.bor(KA.natle(o, _), SV.mem(_, pars)) == True{} : Bool}
      covb_at(j, w, vp, o, pars, hin, hw)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      L.band_i(ecov(o, pars, PL.rnv(vp, a)), ecov(o, pars, PL.rnv(vp, b)), rnv_cov(a, vp, o, pars, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_cov(b, vp, o, pars, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QSub{+a, +b}:
      L.band_i(ecov(o, pars, PL.rnv(vp, a)), ecov(o, pars, PL.rnv(vp, b)), rnv_cov(a, vp, o, pars, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_cov(b, vp, o, pars, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QMul{+a, +b}:
      L.band_i(ecov(o, pars, PL.rnv(vp, a)), ecov(o, pars, PL.rnv(vp, b)), rnv_cov(a, vp, o, pars, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hin), hw), rnv_cov(b, vp, o, pars, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hin), hw))
    case E.QNeg{+a}:
      rnv_cov(a, vp, o, pars, w, hin, hw)

def ins_get(+full: List<&2, E.QExpr>, +x: Nat, +w: List<&2, Nat>, h: {L.subl(ST.nthl(ST.adj(full), x), w) == True{} : Bool}) -> {SV.inside(PL.eqget(full, x), w) == True{} : Bool}:
  %Equal.sym(E.QExpr, PL.eqget(full, x), SV.eqat(full, x), eqget_eqat(full, x)) : {SV.inside(_, w) == True{} : Bool}
  D.adj_inside(full, x, w, h)

def eb_re(xs: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +m: Nat, +w: List<&2, Nat>, +hx: {alladj(xs, ST.adj(full), w) == True{} : Bool}, +hw: {posb(w, vp, m) == True{} : Bool}) -> {PL.eqs_below(m, PL.reorder(vp, full, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      KA.band_i(SL.below(m, PL.rnv(vp, PL.eqget(full, x))), PL.eqs_below(m, PL.reorder(vp, full, t)), rnv_below(PL.eqget(full, x), vp, m, w, ins_get(full, x, w, L.band_l(L.subl(ST.nthl(ST.adj(full), x), w), alladj(t, ST.adj(full), w), hx)), hw), eb_re(t, vp, full, m, w, L.band_r(L.subl(ST.nthl(ST.adj(full), x), w), alladj(t, ST.adj(full), w), hx), hw))

def ec_re(xs: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +o: Nat, +pars: List<&2, Nat>, +w: List<&2, Nat>, +hx: {alladj(xs, ST.adj(full), w) == True{} : Bool}, +hw: {covb(w, vp, o, pars) == True{} : Bool}) -> {ecovs(o, pars, PL.reorder(vp, full, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(ecov(o, pars, PL.rnv(vp, PL.eqget(full, x))), ecovs(o, pars, PL.reorder(vp, full, t)), rnv_cov(PL.eqget(full, x), vp, o, pars, w, ins_get(full, x, w, L.band_l(L.subl(ST.nthl(ST.adj(full), x), w), alladj(t, ST.adj(full), w), hx)), hw), ec_re(t, vp, full, o, pars, w, L.band_r(L.subl(ST.nthl(ST.adj(full), x), w), alladj(t, ST.adj(full), w), hx), hw))

# Entries not among the unknowns
# ------------------------------

def st_false(+x: Nat, +ys: List<&2, Nat>, e: {ST.mem(x, ys) == False{} : Bool}) -> {SV.mem(x, ys) == False{} : Bool}:
  %Equal.sym(Bool, SV.mem(x, ys), ST.mem(x, ys), L.mem_sv(x, ys)) : {_ == False{} : Bool}
  e

def sv_false(+x: Nat, +ys: List<&2, Nat>, e: {SV.mem(x, ys) == False{} : Bool}) -> {ST.mem(x, ys) == False{} : Bool}:
  %L.mem_sv(x, ys) : {_ == False{} : Bool}
  e

def app_r_of(+u: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, ST.app(a, b)) == True{} : Bool}, +hn: {SV.mem(u, a) == False{} : Bool}) -> {SV.mem(u, b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      app_r_of(u, t, b, L.bor_rf(SV.eq(u, x), SV.mem(u, ST.app(t, b)), h, L.bor_fl(SV.eq(u, x), SV.mem(u, t), hn)), L.bor_fr(SV.eq(u, x), SV.mem(u, t), hn))

def minus_sub.go(b: Bool, +x: Nat, +ys: List<&2, Nat>, +z: List<&2, Nat>, +rest: List<&2, Nat>, e: {ST.mem(x, ys) == b : Bool}, hx: {SV.mem(x, ST.app(ys, z)) == True{} : Bool}, hr: {L.subl(rest, z) == True{} : Bool}) -> {L.subl(ST.minus.go(b, x, rest), z) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      L.subl_con(x, rest, z, app_r_of(x, ys, z, hx, st_false(x, ys, e)), hr)

# xs within ys ++ z: xs less ys is within z
def minus_sub(xs: List<&2, Nat>, +ys: List<&2, Nat>, +z: List<&2, Nat>, +h: {L.subl(xs, ST.app(ys, z)) == True{} : Bool}) -> {L.subl(ST.minus(xs, ys), z) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      minus_sub.go(ST.mem(x, ys), x, ys, z, ST.minus(t, ys), {==}, L.subl_hd(x, t, ST.app(ys, z), h), minus_sub(t, ys, z, L.subl_tl(x, t, ST.app(ys, z), h)))

def mm_hd(+u: Nat, +x: Nat, +ys: List<&2, Nat>, e: {SV.eq(u, x) == True{} : Bool}, hn: {SV.mem(u, ys) == False{} : Bool}) -> {ST.mem(x, ys) == False{} : Bool}:
  sv_false(x, ys, (%L.eq_ok(u, x, e) : {SV.mem(_, ys) == False{} : Bool}
    hn))

def minus_mem.go(+u: Nat, +x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, b: Bool, +e: {SV.eq(u, x) == b : Bool}, hx: {SV.bor(b, SV.mem(u, t)) == True{} : Bool}, +hn: {SV.mem(u, ys) == False{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {SV.mem(u, ST.minus(t, ys)) == True{} : Bool}) -> {SV.mem(u, ST.minus.go(ST.mem(x, ys), x, ST.minus(t, ys))) == True{} : Bool}:
  match b:
    case True{}:
      MX.mg_keep(ST.mem(x, ys), mm_hd(u, x, ys, e, hn), x, ST.minus(t, ys), u, e)
    case False{}:
      MX.mg_mem(ST.mem(x, ys), x, ST.minus(t, ys), u, ih(hx))

# u in xs, not in ys: u in xs less ys
def minus_mem(+u: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, hx: {SV.mem(u, xs) == True{} : Bool}, +hn: {SV.mem(u, ys) == False{} : Bool}) -> {SV.mem(u, ST.minus(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(u, Nil{}) == True{} : Bool}, KA.ft(hx))
    case Con{+x, +t}:
      minus_mem.go(u, x, t, ys, SV.eq(u, x), {==}, hx, hn, p => minus_mem(u, t, ys, p, hn))

def pok(xs: List<&2, Nat>, +vp: List<&2, Nat>, +o: Nat, +h: {posb(xs, vp, o) == True{} : Bool}) -> {PL.pars_ok(o, ST.positions(xs, vp)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      KA.band_i(KA.natle(1n+ST.pos(x, vp), o), PL.pars_ok(o, ST.positions(t, vp)), L.band_l(KA.natle(1n+ST.pos(x, vp), o), posb(t, vp, o), h), pok(t, vp, o, L.band_r(KA.natle(1n+ST.pos(x, vp), o), posb(t, vp, o), h)))

# One block
# ---------

def swap2(+a: List<&2, Nat>, +b: List<&2, Nat>) -> {L.subl(ST.app(a, b), ST.app(b, a)) == True{} : Bool}:
  TJ.subl_app(a, b, ST.app(b, a), TJ.app_subl_r(b, a), TJ.app_subl_l(b, a))

def posb_rw(+w: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +m1: Nat, +m2: Nat, ea: {a == b : List<&2, Nat>}, em: {m1 == m2 : Nat}, h: {posb(w, a, m1) == True{} : Bool}) -> {posb(w, b, m2) == True{} : Bool}:
  %ea : {posb(w, _, m2) == True{} : Bool}
  %em : {posb(w, a, _) == True{} : Bool}
  h

def c1_of(+es: List<&2, Nat>, +rest: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>) -> {KA.natle(ST.len(es), CK.eqlen(PL.reorder(vp, full, ST.app(es, rest)))) == True{} : Bool}:
  %Equal.sym(Nat, CK.eqlen(PL.reorder(vp, full, ST.app(es, rest))), ST.len(ST.app(es, rest)), re_len(ST.app(es, rest), vp, full)) : {KA.natle(ST.len(es), _) == True{} : Bool}
  len_app_ge(es, rest)

def c2_of(+es: List<&2, Nat>, +vs: List<&2, Nat>, +known: List<&2, Nat>, +tl: List<&2, Nat>, +o: Nat, +vp: List<&2, Nat>, +nv: Nat, ev: {vp == ST.app(known, ST.app(vs, tl)) : List<&2, Nat>}, hk: {SV.len(known) == o : Nat}, hl: {SV.len(vp) == nv : Nat}, hn: {ST.len(es) == SV.len(vs) : Nat}) -> {KA.natle(Nat.add(o, ST.len(es)), nv) == True{} : Bool}:
  %Equal.sym(Nat, ST.len(es), SV.len(vs), hn) : {KA.natle(Nat.add(o, _), nv) == True{} : Bool}
  %hk : {KA.natle(Nat.add(_, SV.len(vs)), nv) == True{} : Bool}
  %hl : {KA.natle(Nat.add(SV.len(known), SV.len(vs)), _) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, vp, ST.app(known, ST.app(vs, tl)), ev) : {KA.natle(Nat.add(SV.len(known), SV.len(vs)), SV.len(_)) == True{} : Bool}
  %Equal.sym(Nat, SV.len(ST.app(known, ST.app(vs, tl))), Nat.add(SV.len(known), SV.len(ST.app(vs, tl))), len_app(known, ST.app(vs, tl))) : {KA.natle(Nat.add(SV.len(known), SV.len(vs)), _) == True{} : Bool}
  KA.natle_add_mono(SV.len(known), SV.len(vs), SV.len(ST.app(vs, tl)), lag(vs, tl))

def c3_of(+mw: List<&2, Nat>, +known: List<&2, Nat>, +vs: List<&2, Nat>, +tl: List<&2, Nat>, +o: Nat, +vp: List<&2, Nat>, ev: {vp == ST.app(known, ST.app(vs, tl)) : List<&2, Nat>}, hk: {SV.len(known) == o : Nat}, h: {L.subl(mw, known) == True{} : Bool}) -> {PL.pars_ok(o, ST.positions(mw, vp)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, vp, ST.app(known, ST.app(vs, tl)), ev) : {PL.pars_ok(o, ST.positions(mw, _)) == True{} : Bool}
  %hk : {PL.pars_ok(_, ST.positions(mw, ST.app(known, ST.app(vs, tl)))) == True{} : Bool}
  pok(mw, ST.app(known, ST.app(vs, tl)), SV.len(known), posb_of(mw, known, ST.app(vs, tl), h))

def ev_assoc(+known: List<&2, Nat>, +vs: List<&2, Nat>, +tl: List<&2, Nat>, +vp: List<&2, Nat>, ev: {vp == ST.app(known, ST.app(vs, tl)) : List<&2, Nat>}) -> {ST.app(ST.app(known, vs), tl) == vp : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, vp, ST.app(known, ST.app(vs, tl)), ev) : {ST.app(ST.app(known, vs), tl) == _ : List<&2, Nat>}
  TJ.app_assoc(known, vs, tl)

def kv_len(+known: List<&2, Nat>, +vs: List<&2, Nat>, +es: List<&2, Nat>, +o: Nat, hk: {SV.len(known) == o : Nat}, hn: {ST.len(es) == SV.len(vs) : Nat}) -> {SV.len(ST.app(known, vs)) == Nat.add(o, ST.len(es)) : Nat}:
  %Equal.sym(Nat, SV.len(ST.app(known, vs)), Nat.add(SV.len(known), SV.len(vs)), len_app(known, vs)) : {_ == Nat.add(o, ST.len(es)) : Nat}
  %Equal.sym(Nat, SV.len(known), o, hk) : {Nat.add(_, SV.len(vs)) == Nat.add(o, ST.len(es)) : Nat}
  %Equal.sym(Nat, ST.len(es), SV.len(vs), hn) : {Nat.add(o, SV.len(vs)) == Nat.add(o, _) : Nat}
  {==}

def covb_go.hd(b: Bool, +u: Nat, +w: List<&2, Nat>, +known: List<&2, Nat>, +vs: List<&2, Nat>, +tl: List<&2, Nat>, +o: Nat, e: {SV.mem(u, vs) == b : Bool}, hu: {SV.mem(u, w) == True{} : Bool}, hk: {SV.len(known) == o : Nat}, hd: {SV.distinct(ST.app(known, ST.app(vs, tl))) == True{} : Bool}) -> {SV.bor(KA.natle(o, ST.pos(u, ST.app(known, ST.app(vs, tl)))), SV.mem(ST.pos(u, ST.app(known, ST.app(vs, tl))), ST.positions(ST.minus(w, vs), ST.app(known, ST.app(vs, tl))))) == True{} : Bool}:
  match b:
    case True{}:
      L.bor_l(KA.natle(o, ST.pos(u, ST.app(known, ST.app(vs, tl)))), SV.mem(ST.pos(u, ST.app(known, ST.app(vs, tl))), ST.positions(ST.minus(w, vs), ST.app(known, ST.app(vs, tl)))), (%hk : {KA.natle(_, ST.pos(u, ST.app(known, ST.app(vs, tl)))) == True{} : Bool}
        pos_out(u, known, ST.app(vs, tl), dist_notin(u, known, ST.app(vs, tl), hd, TJ.mem_app_l(u, vs, tl, e)))))
    case False{}:
      L.bor_r(KA.natle(o, ST.pos(u, ST.app(known, ST.app(vs, tl)))), SV.mem(ST.pos(u, ST.app(known, ST.app(vs, tl))), ST.positions(ST.minus(w, vs), ST.app(known, ST.app(vs, tl)))), pos_mem(u, ST.minus(w, vs), ST.app(known, ST.app(vs, tl)), minus_mem(u, w, vs, hu, e)))

def covb_go(ws: List<&2, Nat>, +w: List<&2, Nat>, +known: List<&2, Nat>, +vs: List<&2, Nat>, +tl: List<&2, Nat>, +o: Nat, +hws: {L.subl(ws, w) == True{} : Bool}, +hk: {SV.len(known) == o : Nat}, +hd: {SV.distinct(ST.app(known, ST.app(vs, tl))) == True{} : Bool}) -> {covb(ws, ST.app(known, ST.app(vs, tl)), o, ST.positions(ST.minus(w, vs), ST.app(known, ST.app(vs, tl)))) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +v2 = ST.app(known, ST.app(vs, tl))
      L.band_i(SV.bor(KA.natle(o, ST.pos(u, v2)), SV.mem(ST.pos(u, v2), ST.positions(ST.minus(w, vs), v2))), covb(t, v2, o, ST.positions(ST.minus(w, vs), v2)), covb_go.hd(SV.mem(u, vs), u, w, known, vs, tl, o, {==}, L.subl_hd(u, t, w, hws), hk, hd), covb_go(t, w, known, vs, tl, o, L.subl_tl(u, t, w, hws), hk, hd))

def covb_rw(+w: List<&2, Nat>, +o: Nat, +mw: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, ea: {a == b : List<&2, Nat>}, h: {covb(w, b, o, ST.positions(mw, b)) == True{} : Bool}) -> {covb(w, a, o, ST.positions(mw, a)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, a, b, ea) : {covb(w, _, o, ST.positions(mw, _)) == True{} : Bool}
  h

def c4_of(+es: List<&2, Nat>, +rest: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +m: Nat, +w: List<&2, Nat>, had: {alladj(es, ST.adj(full), w) == True{} : Bool}, hpb: {posb(w, vp, m) == True{} : Bool}) -> {PL.eqs_below(m, PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest)))) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest))), PL.reorder(vp, full, es), takeq_re(es, rest, vp, full)) : {PL.eqs_below(m, _) == True{} : Bool}
  eb_re(es, vp, full, m, w, had, hpb)

def c5_of(+es: List<&2, Nat>, +rest: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +o: Nat, +pars: List<&2, Nat>, +w: List<&2, Nat>, had: {alladj(es, ST.adj(full), w) == True{} : Bool}, hcv: {covb(w, vp, o, pars) == True{} : Bool}) -> {ecovs(o, pars, PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest)))) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest))), PL.reorder(vp, full, es), takeq_re(es, rest, vp, full)) : {ecovs(o, pars, _) == True{} : Bool}
  ec_re(es, vp, full, o, pars, w, had, hcv)

def c6_of(+es: List<&2, Nat>, +rest: List<&2, Nat>, +vp: List<&2, Nat>, +full: List<&2, E.QExpr>, +tb: List<&2, ST.SkB>, +m: Nat, +nv: Nat, h6: {swalk(tb, PL.reorder(vp, full, rest), m, nv) == True{} : Bool}) -> {swalk(tb, PL.dropq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest))), m, nv) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, PL.dropq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest))), PL.reorder(vp, full, rest), dropq_re(es, rest, vp, full)) : {swalk(tb, _, m, nv) == True{} : Bool}
  h6

# one block of the walk, given the rest
def sw_blk(+es: List<&2, Nat>, +vs: List<&2, Nat>, +known: List<&2, Nat>, +tl: List<&2, Nat>, +rest: List<&2, Nat>, +o: Nat, +full: List<&2, E.QExpr>, +vp: List<&2, Nat>, +nv: Nat, +tb: List<&2, ST.SkB>, +ev: {vp == ST.app(known, ST.app(vs, tl)) : List<&2, Nat>}, +hk: {SV.len(known) == o : Nat}, +hd: {SV.distinct(vp) == True{} : Bool}, +hl: {SV.len(vp) == nv : Nat}, +hn: {ST.len(es) == SV.len(vs) : Nat}, +hw: {L.subl(ST.uses(es, ST.adj(full)), ST.app(vs, known)) == True{} : Bool}, h6: {swalk(tb, PL.reorder(vp, full, rest), Nat.add(o, ST.len(es)), nv) == True{} : Bool}) -> {SV.band(KA.natle(ST.len(es), CK.eqlen(PL.reorder(vp, full, ST.app(es, rest)))), SV.band(KA.natle(Nat.add(o, ST.len(es)), nv), SV.band(PL.pars_ok(o, ST.positions(ST.minus(ST.uses(es, ST.adj(full)), vs), vp)), SV.band(PL.eqs_below(Nat.add(o, ST.len(es)), PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest)))), SV.band(ecovs(o, ST.positions(ST.minus(ST.uses(es, ST.adj(full)), vs), vp), PL.takeq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest)))), swalk(tb, PL.dropq(ST.len(es), PL.reorder(vp, full, ST.app(es, rest))), Nat.add(o, ST.len(es)), nv)))))) == True{} : Bool}:
  +adj = ST.adj(full)
  +w = ST.uses(es, adj)
  +n = ST.len(es)
  +rr = PL.reorder(vp, full, ST.app(es, rest))
  +mw = ST.minus(w, vs)
  +pars = ST.positions(mw, vp)
  +v2 = ST.app(known, ST.app(vs, tl))
  +hdv = rw_dist(v2, vp, Equal.sym(List<&2, Nat>, vp, v2, ev), hd)
  +hwk = L.subl_trans(w, ST.app(vs, known), ST.app(known, vs), hw, swap2(vs, known))
  +hpb = posb_rw(w, ST.app(ST.app(known, vs), tl), vp, SV.len(ST.app(known, vs)), Nat.add(o, n), ev_assoc(known, vs, tl, vp, ev), kv_len(known, vs, es, o, hk, hn), posb_of(w, ST.app(known, vs), tl, hwk))
  +hcv = covb_rw(w, o, mw, vp, v2, ev, covb_go(w, w, known, vs, tl, o, L.subl_refl(w), hk, hdv))
  +had = alladj_in(es, es, adj, L.subl_refl(es))
  +b6 = SV.band(ecovs(o, pars, PL.takeq(n, rr)), swalk(tb, PL.dropq(n, rr), Nat.add(o, n), nv))
  +b5 = SV.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, rr)), b6)
  +b4 = SV.band(PL.pars_ok(o, pars), b5)
  +b3 = SV.band(KA.natle(Nat.add(o, n), nv), b4)
  +p6 = L.band_i(ecovs(o, pars, PL.takeq(n, rr)), swalk(tb, PL.dropq(n, rr), Nat.add(o, n), nv), c5_of(es, rest, vp, full, o, pars, w, had, hcv), c6_of(es, rest, vp, full, tb, Nat.add(o, n), nv, h6))
  +p5 = L.band_i(PL.eqs_below(Nat.add(o, n), PL.takeq(n, rr)), b6, c4_of(es, rest, vp, full, Nat.add(o, n), w, had, hpb), p6)
  +p4 = L.band_i(PL.pars_ok(o, pars), b5, c3_of(mw, known, vs, tl, o, vp, ev, hk, minus_sub(w, vs, known, hw)), p5)
  +p3 = L.band_i(KA.natle(Nat.add(o, n), nv), b4, c2_of(es, vs, known, tl, o, vp, nv, ev, hk, hl, hn), p4)
  L.band_i(KA.natle(n, CK.eqlen(rr)), b3, c1_of(es, rest, vp, full), p3)

# The walk over the blocks
# ------------------------

def o_nv(+known: List<&2, Nat>, +o: Nat, +vp: List<&2, Nat>, +nv: Nat, ev: {vp == ST.app(known, Nil{}) : List<&2, Nat>}, hk: {SV.len(known) == o : Nat}, hl: {SV.len(vp) == nv : Nat}) -> {o == nv : Nat}:
  %hk : {_ == nv : Nat}
  %hl : {SV.len(known) == _ : Nat}
  %Equal.sym(List<&2, Nat>, vp, ST.app(known, Nil{}), ev) : {SV.len(known) == SV.len(_) : Nat}
  %Equal.sym(List<&2, Nat>, ST.app(known, Nil{}), known, TJ.app_nil(known)) : {SV.len(known) == SV.len(_) : Nat}
  {==}

def hn_of(+es: List<&2, Nat>, +vs: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {nleq(vs, ST.look(vm, es)) == True{} : Bool}) -> {ST.len(es) == SV.len(vs) : Nat}:
  %Equal.sym(Nat, ST.len(es), SV.len(es), TJ.len_sv(es)) : {_ == SV.len(vs) : Nat}
  %Equal.sym(List<&2, Nat>, vs, ST.look(vm, es), nleq_ok(vs, ST.look(vm, es), h)) : {SV.len(es) == SV.len(_) : Nat}
  Equal.sym(Nat, SV.len(ST.look(vm, es)), SV.len(es), L.look_len(vm, es))

def ev_next(+known: List<&2, Nat>, +vs: List<&2, Nat>, +tl: List<&2, Nat>, +vp: List<&2, Nat>, ev: {vp == ST.app(known, ST.app(vs, tl)) : List<&2, Nat>}) -> {vp == ST.app(ST.app(known, vs), tl) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, ST.app(ST.app(known, vs), tl), ST.app(known, ST.app(vs, tl)), TJ.app_assoc(known, vs, tl)) : {vp == _ : List<&2, Nat>}
  ev

# the walk from offset o (known: the variables before), the blocks bs
def sw_go(bs: List<&2, ST.SB>, +known: List<&2, Nat>, +o: Nat, +vm: List<&2, Maybe<&2, Nat>>, +full: List<&2, E.QExpr>, +vp: List<&2, Nat>, +nv: Nat, +good: List<&2, Nat>, +ev: {vp == ST.app(known, ST.allvars(bs)) : List<&2, Nat>}, +hk: {SV.len(known) == o : Nat}, +hd: {SV.distinct(vp) == True{} : Bool}, +hl: {SV.len(vp) == nv : Nat}, +hc: {vchain(bs, known, ST.adj(full)) == True{} : Bool}, +hlk: {lkb(vm, bs) == True{} : Bool}) -> {swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), vp), good), PL.reorder(vp, full, ST.alleqs(bs)), o, nv) == True{} : Bool}:
  match bs:
    case Nil{}:
      L.band_i(KA.nateq(o, nv), True{}, KA.nateq_of(o, nv, o_nv(known, o, vp, nv, ev, hk, hl)), {==})
    case Con{ST.SB{+es, +vs}, +t}:
      +adj = ST.adj(full)
      +tl = ST.allvars(t)
      +rest = ST.alleqs(t)
      +hc1 = L.band_l(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(t, ST.app(known, vs), adj), hc)
      +hc2 = L.band_r(L.subl(ST.uses(es, adj), ST.app(vs, known)), vchain(t, ST.app(known, vs), adj), hc)
      +hl1 = L.band_l(nleq(vs, ST.look(vm, es)), lkb(vm, t), hlk)
      +hl2 = L.band_r(nleq(vs, ST.look(vm, es)), lkb(vm, t), hlk)
      +hn = hn_of(es, vs, vm, hl1)
      +tb = ST.renum.bs(ST.skbs(t, adj, vp), good)
      +ih = sw_go(t, ST.app(known, vs), Nat.add(o, ST.len(es)), vm, full, vp, nv, good, ev_next(known, vs, tl, vp, ev), kv_len(known, vs, es, o, hk, hn), hd, hl, hc2, hl2)
      swalk_con(ST.positions(es, good), vs, ST.positions(ST.minus(ST.uses(es, adj), vs), vp), tb, PL.reorder(vp, full, ST.app(es, rest)), o, nv, ST.len(es), positions_len(es, good), sw_blk(es, vs, known, tl, rest, o, full, vp, nv, tb, ev, hk, hd, hl, hn, hc1, ih))

# The solver's structure
# ----------------------
# For the kept equations good of the system full over nv variables, with
# the variable side ending at mates vm and pins fs, and the blocks bs
# built from them: the blocks hold good, each valid with mates as
# unknowns; vp (the pins, then the blocks' unknowns) is every variable
# once; and the checker's walk finds its structural conjuncts.

def skok(+full: List<&2, E.QExpr>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>) -> Bool:
  SV.band(sfacts(ST.adj(full), nv, good, vm, fs, bs), swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv))

def skok_sf(+full: List<&2, E.QExpr>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {skok(full, nv, good, vm, fs, bs) == True{} : Bool}) -> {sfacts(ST.adj(full), nv, good, vm, fs, bs) == True{} : Bool}:
  L.band_l(sfacts(ST.adj(full), nv, good, vm, fs, bs), swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv), h)

def skok_sw(+full: List<&2, E.QExpr>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h: {skok(full, nv, good, vm, fs, bs) == True{} : Bool}) -> {swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv) == True{} : Bool}:
  L.band_r(sfacts(ST.adj(full), nv, good, vm, fs, bs), swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv), h)

def skok_mk(+full: List<&2, E.QExpr>, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, h_sf: {sfacts(ST.adj(full), nv, good, vm, fs, bs) == True{} : Bool}, h_sw: {swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv) == True{} : Bool}) -> {skok(full, nv, good, vm, fs, bs) == True{} : Bool}:
  L.band_i(sfacts(ST.adj(full), nv, good, vm, fs, bs), swalk(ST.renum.bs(ST.skbs(bs, ST.adj(full), ST.app(fs, ST.allvars(bs))), good), PL.reorder(ST.app(fs, ST.allvars(bs)), full, ST.alleqs(bs)), ST.len(fs), nv), h_sf, h_sw)

def skok_of(+full: List<&2, E.QExpr>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +h: {vside(nq, nv, good, vm, fs) == True{} : Bool}, +ha: {D.adjb(ST.adj(full), nv) == True{} : Bool}) -> {skok(full, nv, good, vm, fs, kblocks(ST.adj(full), nq, nv, good, vm, fs)) == True{} : Bool}:
  +adj = ST.adj(full)
  +bs = kblocks(adj, nq, nv, good, vm, fs)
  +vp = ST.app(fs, ST.allvars(bs))
  +sf = blocks_ok(adj, nq, nv, good, vm, fs, h, ha)
  skok_mk(full, nv, good, vm, fs, bs, sf, sw_go(bs, fs, ST.len(fs), vm, full, vp, nv, good, {==}, Equal.sym(Nat, ST.len(fs), SV.len(fs), TJ.len_sv(fs)), sfacts_vpd(adj, nv, good, vm, fs, bs, sf), L.eq_ok(SV.len(vp), nv, sfacts_vpl(adj, nv, good, vm, fs, bs, sf)), sfacts_ch(adj, nv, good, vm, fs, bs, sf), sfacts_lk(adj, nv, good, vm, fs, bs, sf)))

def skel_kd(kd: ST.KD, +full: List<&2, E.QExpr>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, h: {vsides(nq, nv, good, kd) == True{} : Bool}, +ha: {D.adjb(ST.adj(full), nv) == True{} : Bool}) -> {skok(full, nv, good, ST.KD.vm(kd), ST.KD.red(kd), kblocks(ST.adj(full), nq, nv, good, ST.KD.vm(kd), ST.KD.red(kd))) == True{} : Bool}:
  match kd:
    case ST.KD{+vm, +fs, dd}:
      skok_of(full, nq, nv, good, vm, fs, h, ha)

# the solver's structure of a sketch's kept equations
def struct_ok(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {skok(SK.Sketch.eqs(sk), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))))) == True{} : Bool}:
  +full = SK.Sketch.eqs(sk)
  skel_kd(MX.kvs(ST.adj(full), ST.len.q(full), SO.nvars(sk), SO.good_of(sk)), full, ST.len.q(full), SO.nvars(sk), SO.good_of(sk), vend(sk, ha), ha)
