# bend-cad: the solver's totality (ROADMAP: solve_total), proven. Proofs
# only.
#
# For a well-formed sketch whose variables cover it, whatever the drawing
# and the level, the structure stage never fails: the red constraints,
# reasons and pins solve reports are those of the sketch alone; every red
# constraint is explained (lib/redpf.bend); the sketch less them passes
# the well-formedness check (lib/wfcpf.bend); the pins are distinct
# variables; and with them the kept system is square.
#
# The pins are the structure's (the variable side's failed searches, so
# distinct variables), when that makes the kept system square; otherwise
# the red stage's free variables, which do: its matching has as many
# matched equations as the kept system (lib/redpf.bend: red_cnt) and is as
# long as there are variables, so the free ones make up the rest.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./wfdec.bend as WF
import ./solve.bend as SO
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D
import ./redpf.bend as RP
import ./wfcpf.bend as WC
import ./covpf.bend as CV

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The variables, latest first
# ---------------------------

def down_below(n: Nat) -> {SV.below(ST.down(n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.band_i(SV.lt(m, 1n+m), SV.below(ST.down(m), 1n+m), D.lt_self(m), RP.below_mono(ST.down(m), m, 1n+m, down_below(m), L.le_succ(m, m, L.le_refl(m))))

def down_dist(n: Nat) -> {SV.distinct(ST.down(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.dist_con(m, ST.down(m), RP.below_notmem(m, ST.down(m), down_below(m)), down_dist(m))

# The variable side's failed searches
# -----------------------------------

def red.eqs(+st: ST.KS) -> List<&2, Nat>:
  ST.red.eqs(ST.ks.red(st))

def ks_sub(+j: Nat, a: ST.DS, st: ST.KS) -> {L.subl(red.eqs(ST.kstep(j, a, st)), Con{j, red.eqs(st)}) == True{} : Bool}:
  match a st:
    case ST.DS{True{}, vm2, vis} ST.KS{vm, +red}:
      L.subl_cons_r(ST.red.eqs(red), j, ST.red.eqs(red), L.subl_refl(ST.red.eqs(red)))
    case ST.DS{False{}, vm2, vis} ST.KS{vm, +red}:
      L.subl_refl(Con{j, ST.red.eqs(red)})

def ks_dist(+j: Nat, a: ST.DS, st: ST.KS, hd: {SV.distinct(red.eqs(st)) == True{} : Bool}, hn: {SV.mem(j, red.eqs(st)) == False{} : Bool}) -> {SV.distinct(red.eqs(ST.kstep(j, a, st))) == True{} : Bool}:
  match a st:
    case ST.DS{True{}, vm2, vis} ST.KS{vm, red}:
      hd
    case ST.DS{False{}, vm2, vis} ST.KS{vm, +red}:
      L.dist_con(j, ST.red.eqs(red), hn, hd)

# no entry of xs is in ys
def disj(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(SV.bnot(SV.mem(x, ys)), disj(t, ys))

def disj_step(t: List<&2, Nat>, +j: Nat, +old: List<&2, Nat>, +nw: List<&2, Nat>, +h: {disj(t, old) == True{} : Bool}, +hj: {SV.mem(j, t) == False{} : Bool}, +hs: {L.subl(nw, Con{j, old}) == True{} : Bool}) -> {disj(t, nw) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      L.band_i(SV.bnot(SV.mem(x, nw)), disj(r, nw), L.bnot_t(SV.mem(x, nw), L.notin_subl(x, nw, Con{j, old}, L.bor_f(SV.eq(x, j), SV.mem(x, old), %L.eq_sym(j, x) : {_ == False{} : Bool}
        L.bor_fl(SV.eq(j, x), SV.mem(j, r), hj), L.bnot_f(SV.mem(x, old), L.band_l(SV.bnot(SV.mem(x, old)), disj(r, old), h))), hs)), disj_step(r, j, old, nw, L.band_r(SV.bnot(SV.mem(x, old)), disj(r, old), h), L.bor_fr(SV.eq(j, x), SV.mem(j, r), hj), hs))

def disj_hd(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, h: {disj(Con{x, t}, ys) == True{} : Bool}) -> {SV.mem(x, ys) == False{} : Bool}:
  L.bnot_f(SV.mem(x, ys), L.band_l(SV.bnot(SV.mem(x, ys)), disj(t, ys), h))

def disj_tl(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, h: {disj(Con{x, t}, ys) == True{} : Bool}) -> {disj(t, ys) == True{} : Bool}:
  L.band_r(SV.bnot(SV.mem(x, ys)), disj(t, ys), h)

# the failed searches are among js and before
def kuhn_sub(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: ST.KS, +u: List<&2, Nat>, +hj: {L.subl(js, u) == True{} : Bool}, +hs: {L.subl(red.eqs(st), u) == True{} : Bool}) -> {L.subl(red.eqs(ST.kuhn(js, adj, f, st)), u) == True{} : Bool}:
  match js:
    case Nil{}:
      hs
    case Con{+j, +t}:
      +a = ST.search(f, adj, ST.KS.vm(st), j)
      kuhn_sub(t, adj, f, ST.kstep(j, a, st), u, L.subl_tl(j, t, u, hj), L.subl_trans(red.eqs(ST.kstep(j, a, st)), Con{j, red.eqs(st)}, u, ks_sub(j, a, st), L.subl_con(j, red.eqs(st), u, L.subl_hd(j, t, u, hj), hs)))

# ... each at most once
def kuhn_dist(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: ST.KS, +hd: {SV.distinct(js) == True{} : Bool}, +hr: {SV.distinct(red.eqs(st)) == True{} : Bool}, +hx: {disj(js, red.eqs(st)) == True{} : Bool}) -> {SV.distinct(red.eqs(ST.kuhn(js, adj, f, st))) == True{} : Bool}:
  match js:
    case Nil{}:
      hr
    case Con{+j, +t}:
      +a = ST.search(f, adj, ST.KS.vm(st), j)
      kuhn_dist(t, adj, f, ST.kstep(j, a, st), L.dist_tl(j, t, hd), ks_dist(j, a, st, hr, disj_hd(j, t, red.eqs(st), hx)), disj_step(t, j, red.eqs(st), red.eqs(ST.kstep(j, a, st)), disj_tl(j, t, red.eqs(st), hx), L.dist_hd(j, t, hd), ks_sub(j, a, st)))

def dnil(xs: List<&2, Nat>) -> {disj(xs, Nil{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      dnil(t)

# the variable side's pins: distinct variables
def kpins(+nv: Nat, +adjt: List<&2, List<&2, Nat>>, +f: Nat, +ne: Nat) -> {SV.band(SV.distinct(red.eqs(ST.kuhn(ST.down(nv), adjt, f, ST.KS{ST.nones(ne), Nil{}}))), SV.below(red.eqs(ST.kuhn(ST.down(nv), adjt, f, ST.KS{ST.nones(ne), Nil{}})), nv)) == True{} : Bool}:
  +p = red.eqs(ST.kuhn(ST.down(nv), adjt, f, ST.KS{ST.nones(ne), Nil{}}))
  L.band_i(SV.distinct(p), SV.below(p, nv), kuhn_dist(ST.down(nv), adjt, f, ST.KS{ST.nones(ne), Nil{}}, down_dist(nv), {==}, dnil(ST.down(nv))), D.below_subl(p, ST.down(nv), nv, kuhn_sub(ST.down(nv), adjt, f, ST.KS{ST.nones(ne), Nil{}}, ST.down(nv), L.subl_refl(ST.down(nv)), {==}), down_below(nv)))

def ntake_app(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {SO.ntake(ST.len(xs), ST.app(xs, ys)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, SO.ntake(ST.len(t), ST.app(t, ys)), t, ntake_app(t, ys)) : {Con{h, _} == Con{h, t} : List<&2, Nat>}
      {==}

# the structure's pins are its variable side's failed searches
def skp(+adj: List<&2, List<&2, Nat>>, +ne: Nat, +nv: Nat, +red: List<&2, ST.Red>, +good: List<&2, Nat>, +st: ST.KS) -> {SO.skel.pins(ST.skel.pins(adj, ne, nv, red, good, st)) == red.eqs(st) : List<&2, Nat>}:
  ntake_app(red.eqs(st), ST.allvars(ST.blocks.of(adj, ST.KS.vm(st), red.eqs(st), ST.comps(adj, ST.invert(ST.KS.vm(st), 0n, ST.nones(nv)), good, ne))))

def pins_vars(+adj: List<&2, List<&2, Nat>>, +ne: Nat, +nv: Nat, +red: List<&2, ST.Red>, +good: List<&2, Nat>, +adjt: List<&2, List<&2, Nat>>) -> {SV.band(SV.distinct(SO.skel.pins(ST.skel.vars(adj, ne, nv, red, good, adjt))), SV.below(SO.skel.pins(ST.skel.vars(adj, ne, nv, red, good, adjt)), nv)) == True{} : Bool}:
  +kv = ST.kuhn(ST.down(nv), adjt, 1n+ne, ST.KS{ST.nones(ne), Nil{}})
  %Equal.sym(List<&2, Nat>, SO.skel.pins(ST.skel.pins(adj, ne, nv, red, good, kv)), red.eqs(kv), skp(adj, ne, nv, red, good, kv)) : {SV.band(SV.distinct(_), SV.below(_, nv)) == True{} : Bool}
  kpins(nv, adjt, 1n+ne, ne)

# the structure's pins: distinct variables
def pins_struct(+es: List<&2, E.QExpr>, +nv: Nat) -> {SV.band(SV.distinct(SO.skel.pins(ST.structure(es, nv))), SV.below(SO.skel.pins(ST.structure(es, nv)), nv)) == True{} : Bool}:
  +adj = ST.adj(es)
  +ne = ST.len.q(es)
  +ke = ST.kuhn(ST.iota(ne, 0n), adj, 1n+nv, ST.KS{ST.nones(nv), Nil{}})
  +good = ST.minus(ST.iota(ne, 0n), ST.red.eqs(ST.ks.red(ke)))
  pins_vars(adj, ne, nv, ST.ks.red(ke), good, ST.transpose(nv, 0n, good, adj))

# The pins
# --------

def pick_ok(+kn: Nat, +nv: Nat, +p: List<&2, Nat>, +q: List<&2, Nat>, b: Bool, e: {KA.nateq(Nat.add(kn, SV.len(p)), nv) == b : Bool}, +hp: {SV.band(SV.distinct(p), SV.below(p, nv)) == True{} : Bool}, +hq: {SV.band(SV.distinct(q), SV.band(SV.below(q, nv), SV.eq(Nat.add(kn, SV.len(q)), nv))) == True{} : Bool}) -> {SV.band(SV.distinct(SO.pick(b, p, q)), SV.band(SV.below(SO.pick(b, p, q), nv), SV.eq(Nat.add(kn, SV.len(SO.pick(b, p, q))), nv))) == True{} : Bool}:
  match b:
    case True{}:
      L.band_i(SV.distinct(p), SV.band(SV.below(p, nv), SV.eq(Nat.add(kn, SV.len(p)), nv)), L.band_l(SV.distinct(p), SV.below(p, nv), hp), L.band_i(SV.below(p, nv), SV.eq(Nat.add(kn, SV.len(p)), nv), L.band_r(SV.distinct(p), SV.below(p, nv), hp), D.eq_of(Nat.add(kn, SV.len(p)), nv, WF.nateq_ok(Nat.add(kn, SV.len(p)), nv, e))))
    case False{}:
      hq

def mlen_le(+vm: List<&2, Maybe<&2, Nat>>, +nv: Nat, h: {L.mlen(vm) == nv : Nat}) -> {KA.natle(Nat.add(0n, L.mlen(vm)), nv) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(vm), nv, h) : {KA.natle(_, nv) == True{} : Bool}
  L.le_refl(nv)

def qsq(+kn: Nat, +nv: Nat, +vm: List<&2, Maybe<&2, Nat>>, hc: {SV.len(ST.somes(vm)) == kn : Nat}, hm: {L.mlen(vm) == nv : Nat}) -> {SV.eq(Nat.add(kn, SV.len(ST.holes(vm, 0n))), nv) == True{} : Bool}:
  D.eq_of(Nat.add(kn, SV.len(ST.holes(vm, 0n))), nv, %hc : {Nat.add(_, SV.len(ST.holes(vm, 0n))) == nv : Nat}
    %hm : {Nat.add(SV.len(ST.somes(vm)), SV.len(ST.holes(vm, 0n))) == _ : Nat}
      L.holes_len(vm, 0n))

# the red stage's free variables: distinct, below nv, and as many as the
# kept system needs
def qpins(+kn: Nat, +nv: Nat, +vm: List<&2, Maybe<&2, Nat>>, +hc: {SV.len(ST.somes(vm)) == kn : Nat}, +hm: {L.mlen(vm) == nv : Nat}) -> {SV.band(SV.distinct(ST.holes(vm, 0n)), SV.band(SV.below(ST.holes(vm, 0n), nv), SV.eq(Nat.add(kn, SV.len(ST.holes(vm, 0n))), nv))) == True{} : Bool}:
  L.band_i(SV.distinct(ST.holes(vm, 0n)), SV.band(SV.below(ST.holes(vm, 0n), nv), SV.eq(Nat.add(kn, SV.len(ST.holes(vm, 0n))), nv)), L.holes_dist(vm, 0n), L.band_i(SV.below(ST.holes(vm, 0n), nv), SV.eq(Nat.add(kn, SV.len(ST.holes(vm, 0n))), nv), L.holes_below(vm, 0n, nv, mlen_le(vm, nv, hm)), qsq(kn, nv, vm, hc, hm)))

# the solver's pins: distinct variables, and with them the kept system is
# square
def pins_tot(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SV.band(SV.distinct(SO.pins_of(sk)), SV.band(SV.below(SO.pins_of(sk), SO.nvars(sk)), SV.eq(Nat.add(SV.neqs(SO.kept(sk)), SV.len(SO.pins_of(sk))), SO.nvars(sk)))) == True{} : Bool}:
  +nv = SO.nvars(sk)
  +kn = SV.neqs(SO.kept(sk))
  +p = SO.skel.pins(SO.skel_of(sk))
  +vm = SO.CS.vm(SO.rs_of(sk))
  pick_ok(kn, nv, p, ST.holes(vm, 0n), KA.nateq(Nat.add(kn, SV.len(p)), nv), {==}, pins_struct(SO.kept(sk), nv), qpins(kn, nv, vm, RP.red_cnt(sk, nv, ha), RP.red_mlen(sk, nv, ha)))

# The law
# -------

def solve_total(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> M.Both({SO.Out.red(SO.solve_l(sk, g0, l)) == SO.red_of(sk) : List<&2, Nat>}, M.Both({SO.Out.why(SO.solve_l(sk, g0, l)) == SO.why_of(sk) : List<&2, SV.Why>}, M.Both({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>}, M.Both({SV.explained(sk, SO.red_of(sk), SO.why_of(sk)) == True{} : Bool}, M.Both({WF.wf_dec(SV.mark(SO.red_of(sk), sk)) == True{} : Bool}, M.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, M.Both({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}, {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat}))))))):
  +hwf = WC.wf_dec_ok(sk, w)
  +ha = CV.cov(sk, SO.nvars(sk), cov, hwf)
  +hp = pins_tot(sk, ha)
  +nv = SO.nvars(sk)
  +pins = SO.pins_of(sk)
  +kn = SV.neqs(SO.kept(sk))
  +hp2 = L.band_r(SV.distinct(pins), SV.band(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv)), hp)
  ({==}, ({==}, ({==}, (RP.explained_of(sk, SO.red_of(sk), SO.why_of(sk), RP.red_good(sk, nv, ha)), (WC.wf_mark(SO.red_of(sk), sk, hwf), (L.band_l(SV.distinct(pins), SV.band(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv)), hp), (L.band_l(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv), hp2), L.eq_ok(Nat.add(kn, SV.len(pins)), nv, L.band_r(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv), hp2)))))))))
