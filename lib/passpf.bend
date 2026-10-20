# bend-cad: the single pass is honest (PLAN-sk13a S4, law 4). Proofs
# only.
#
# Honest(sk, classes(sk)): each constraint's class is the honest one
# given the final classes' red positions and dropped equations. The pass
# never sees the final lists; its state is related to them below c:
# - kb, its kept constraints, is kept_before(sk, RF, c) (lib/kbpf.bend);
# - B, its basis, is presolved(sk, RF, DF, c) (lib/solvedpf.bend), with
#   echelon rows, positions bp and a valid matching of exactly bp;
# and the final lists are read position by position: c is red exactly when
# its class is, and k is dropped exactly when its owner's class drops it
# (lib/clslpf.bend), which holds because every class drops only its own
# equations (downs, proven first, from the walk alone).
# Then each driving constraint's class follows from its decisions:
# Conflict (lib/prepf.bend), Over by a failed unit (lib/gmpf.bend), Kept
# or Amber by DropsOk (lib/cwpf.bend), the unit's matching and the side
# tests.
#
# Generated from tools/drafts/passpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./struct.bend as ST
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./refute.bend as RF
import ./conflict.bend as CO
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./prepf.bend as PR
import ./cwpf.bend as CW
import ./gmpf.bend as GM
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./solve.bend as SO
import ./redpf.bend as RP
import ../spec/box.bend as BX
import ./wfcpf.bend as WC
import ./covpf.bend as CV

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Every class drops only its own equations
# ----------------------------------------

def onea_kd(m: Maybe<&2, List<&2, SV.Ref>>, +dd: List<&2, SV.Drop>) -> {SV.kdrops(PA.one.a(m, dd)) == SV.drops(dd) : List<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{rs}:
      {==}

def onek_kd(a: Bool, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> {SV.kdrops(PA.one.k(a, sk, kb, c, dd)) == SV.drops(dd) : List<&2, Nat>}:
  match a:
    case True{}:
      onea_kd(PA.srefs(SV.csides(sk, [c]), sk, kb, c, 0n), dd)
    case False{}:
      {==}

def one_down.g(g: ST.GS, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +h: {KB.allo(SV.owners(sk), SV.drops(dd), c) == True{} : Bool}) -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.g(g, sk, c, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us}))), c) == True{} : Bool}:
  match g:
    case ST.GFail{ST.Red{j, s, x}}:
      {==}
    case ST.GOk{vm2}:
      %Equal.sym(List<&2, Nat>, SV.kdrops(PA.one.k(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)), SV.drops(dd), onek_kd(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)) : {KB.allo(SV.owners(sk), _, c) == True{} : Bool}
      h

def one_down.w(w: PA.CW, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +h: {KB.allo(SV.owners(sk), SV.drops(CW.cw.ds(w)), c) == True{} : Bool})
  -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}:
  match w:
    case PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      one_down.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, c, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, h)

def one_down.c(b: Bool, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +eb: {CO.refutable(sk, c, kb) == b : Bool})
  -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(CO.refutable(sk, c, kb), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, CO.refutable(sk, c, kb), True{}, eb) : {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, CO.refutable(sk, c, kb), False{}, eb) : {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}
      one_down.w(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}), sk, c, kb, rows, B, bp, vm, CW.cw_own(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, {==}))

def one_down(st: PA.PS, +sk: SK.Sketch, +c: Nat) -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, st))), c) == True{} : Bool}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      one_down.c(CO.refutable(sk, c, kb), sk, c, kb, rows, B, bp, vm, {==})

def pass_down(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS) -> {CL.downs(SV.owners(sk), PA.pass(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st), i) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      L.band_i(True{}, CL.downs(SV.owners(sk), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st), 1n+i), {==}, pass_down(t, sk, 1n+i, st))
    case Con{SK.Rec{id, False{}, k}, +t}:
      L.band_i(KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), i), CL.downs(SV.owners(sk), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), 1n+i),
        one_down(st, sk, i), pass_down(t, sk, 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))))

# the final classes drop only their own equations
def classes_down(+sk: SK.Sketch) -> {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}:
  pass_down(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)))

# Lists for the pass's invariant
# ------------------------------

# k is a solved position before c: c's constraint is earlier, not red, k
# not dropped
def psel(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat) -> Bool:
  SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))

def allpre(xs: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+k, t}:
      SV.band(psel(own, R, D, c, k), allpre(t, own, R, D, c))

def allpre_up(xs: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +h: {allpre(xs, own, R, D, c) == True{} : Bool}) -> {allpre(xs, own, R, D, 1n+c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      +hp = L.band_l(psel(own, R, D, c, k), allpre(t, own, R, D, c), h)
      +hq = L.band_r(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))), hp)
      L.band_i(psel(own, R, D, 1n+c, k), allpre(t, own, R, D, 1n+c),
        L.band_i(SV.lt(SV.nth(own, k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))), KB.lt_up(SV.nth(own, k), c, L.band_l(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))), hp)), hq),
        allpre_up(t, own, R, D, c, L.band_r(psel(own, R, D, c, k), allpre(t, own, R, D, c), h)))

def allpre_cat(xs: List<&2, Nat>, +ys: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +h1: {allpre(xs, own, R, D, c) == True{} : Bool}, +h2: {allpre(ys, own, R, D, c) == True{} : Bool}) -> {allpre(SV.cat(xs, ys), own, R, D, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      h2
    case Con{+k, +t}:
      L.band_i(psel(own, R, D, c, k), allpre(SV.cat(t, ys), own, R, D, c), L.band_l(psel(own, R, D, c, k), allpre(t, own, R, D, c), h1), allpre_cat(t, ys, own, R, D, c, L.band_r(psel(own, R, D, c, k), allpre(t, own, R, D, c), h1), h2))

def mem_ext.c(b: Bool, +k: Nat, +x: Nat, +t: List<&2, Nat>, e: {SV.eq(k, x) == b : Bool}, hm: {SV.bor(b, SV.mem(k, t)) == True{} : Bool}) -> Either<&2, &2, {k == x : Nat}, {SV.mem(k, t) == True{} : Bool}>:
  match b:
    case True{}:
      Inl{L.eq_ok(k, x, e)}
    case False{}:
      Inr{hm}

# k in x :: t: k is x, or in t
def mem_ext(+k: Nat, +x: Nat, +t: List<&2, Nat>, hm: {SV.mem(k, Con{x, t}) == True{} : Bool}) -> Either<&2, &2, {k == x : Nat}, {SV.mem(k, t) == True{} : Bool}>:
  mem_ext.c(SV.eq(k, x), k, x, t, {==}, hm)

def allpre_mem.e(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat, +x: Nat, +t: List<&2, Nat>, h: {SV.band(psel(own, R, D, c, x), allpre(t, own, R, D, c)) == True{} : Bool},
  m: Either<&2, &2, {k == x : Nat}, {SV.mem(k, t) == True{} : Bool}>, ih: {SV.mem(k, t) == True{} : Bool} -> {allpre(t, own, R, D, c) == True{} : Bool} -> {psel(own, R, D, c, k) == True{} : Bool}) -> {psel(own, R, D, c, k) == True{} : Bool}:
  match m:
    case Inl{e}:
      (%Equal.sym(Nat, k, x, e) : {psel(own, R, D, c, _) == True{} : Bool}
        L.band_l(psel(own, R, D, c, x), allpre(t, own, R, D, c), h))
    case Inr{hm}:
      ih(hm, L.band_r(psel(own, R, D, c, x), allpre(t, own, R, D, c), h))

def allpre_mem(xs: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat, h: {allpre(xs, own, R, D, c) == True{} : Bool}, hm: {SV.mem(k, xs) == True{} : Bool}) -> {psel(own, R, D, c, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({psel(own, R, D, c, k) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      allpre_mem.e(own, R, D, c, k, x, t, h, mem_ext(k, x, t, hm), q => r => allpre_mem(t, own, R, D, c, k, r, q))

def allo_mem.e(+own: List<&2, Nat>, +c: Nat, +k: Nat, +x: Nat, +t: List<&2, Nat>, h: {SV.band(SV.eq(SV.nth(own, x), c), KB.allo(own, t, c)) == True{} : Bool},
  m: Either<&2, &2, {k == x : Nat}, {SV.mem(k, t) == True{} : Bool}>, ih: {SV.mem(k, t) == True{} : Bool} -> {KB.allo(own, t, c) == True{} : Bool} -> {SV.eq(SV.nth(own, k), c) == True{} : Bool}) -> {SV.eq(SV.nth(own, k), c) == True{} : Bool}:
  match m:
    case Inl{e}:
      (%Equal.sym(Nat, k, x, e) : {SV.eq(SV.nth(own, _), c) == True{} : Bool}
        L.band_l(SV.eq(SV.nth(own, x), c), KB.allo(own, t, c), h))
    case Inr{hm}:
      ih(hm, L.band_r(SV.eq(SV.nth(own, x), c), KB.allo(own, t, c), h))

def allo_mem(+own: List<&2, Nat>, xs: List<&2, Nat>, +c: Nat, +k: Nat, h: {KB.allo(own, xs, c) == True{} : Bool}, hm: {SV.mem(k, xs) == True{} : Bool}) -> {SV.eq(SV.nth(own, k), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.eq(SV.nth(own, k), c) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      allo_mem.e(own, c, k, x, t, h, mem_ext(k, x, t, hm), q => r => allo_mem(own, t, c, k, r, q))

def nonein_mem.e(+k: Nat, +x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, h: {SV.band(SV.bnot(SV.mem(x, ys)), SV.none_in(t, ys)) == True{} : Bool},
  m: Either<&2, &2, {k == x : Nat}, {SV.mem(k, t) == True{} : Bool}>, ih: {SV.mem(k, t) == True{} : Bool} -> {SV.none_in(t, ys) == True{} : Bool} -> {SV.mem(k, ys) == False{} : Bool}) -> {SV.mem(k, ys) == False{} : Bool}:
  match m:
    case Inl{e}:
      (%Equal.sym(Nat, k, x, e) : {SV.mem(_, ys) == False{} : Bool}
        KB.bnot_t(SV.mem(x, ys), L.band_l(SV.bnot(SV.mem(x, ys)), SV.none_in(t, ys), h)))
    case Inr{hm}:
      ih(hm, L.band_r(SV.bnot(SV.mem(x, ys)), SV.none_in(t, ys), h))

# none of xs in ys, k in xs: k not in ys
def nonein_mem(xs: List<&2, Nat>, +ys: List<&2, Nat>, +k: Nat, h: {SV.none_in(xs, ys) == True{} : Bool}, hm: {SV.mem(k, xs) == True{} : Bool}) -> {SV.mem(k, ys) == False{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(k, ys) == False{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      nonein_mem.e(k, x, t, ys, h, mem_ext(k, x, t, hm), q => r => nonein_mem(t, ys, k, r, q))

def below_cat(xs: List<&2, Nat>, +ys: List<&2, Nat>, +n: Nat, +h1: {SV.below(xs, n) == True{} : Bool}, +h2: {SV.below(ys, n) == True{} : Bool}) -> {SV.below(SV.cat(xs, ys), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      h2
    case Con{+x, +t}:
      L.band_i(SV.lt(x, n), SV.below(SV.cat(t, ys), n), L.band_l(SV.lt(x, n), SV.below(t, n), h1), below_cat(t, ys, n, L.band_r(SV.lt(x, n), SV.below(t, n), h1), h2))

def dist_cat(xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {SV.distinct(xs) == True{} : Bool}, +hy: {SV.distinct(ys) == True{} : Bool}, +hn: {SV.none_in(xs, ys) == True{} : Bool}) -> {SV.distinct(SV.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +t}:
      +h1 = KB.bnot_t(SV.mem(x, t), L.band_l(SV.bnot(SV.mem(x, t)), SV.distinct(t), hx))
      +h2 = KB.bnot_t(SV.mem(x, ys), L.band_l(SV.bnot(SV.mem(x, ys)), SV.none_in(t, ys), hn))
      L.band_i(SV.bnot(SV.mem(x, SV.cat(t, ys))), SV.distinct(SV.cat(t, ys)),
        KB.bnot_f(SV.mem(x, SV.cat(t, ys)), Equal.trans(Bool, SV.mem(x, SV.cat(t, ys)), SV.bor(SV.mem(x, t), SV.mem(x, ys)), False{}, SP.mem_cat(x, t, ys), L.bor_f(SV.mem(x, t), SV.mem(x, ys), h1, h2))),
        dist_cat(t, ys, L.band_r(SV.bnot(SV.mem(x, t)), SV.distinct(t), hx), hy, L.band_r(SV.bnot(SV.mem(x, ys)), SV.none_in(t, ys), hn)))

# solved positions before c are not c's own
def nonein_pre(xs: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +us: List<&2, Nat>, +hp: {allpre(xs, own, R, D, c) == True{} : Bool}, +hu: {KB.allo(own, us, c) == True{} : Bool}) -> {SV.none_in(xs, us) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hl = L.band_l(SV.lt(SV.nth(own, x), c), SV.band(SV.bnot(SV.mem(SV.nth(own, x), R)), SV.bnot(SV.mem(x, D))), L.band_l(psel(own, R, D, c, x), allpre(t, own, R, D, c), hp))
      L.band_i(SV.bnot(SV.mem(x, us)), SV.none_in(t, us), KB.bnot_f(SV.mem(x, us), CL.allo_nm(own, us, c, x, hu, Equal.trans(Bool, SV.eq(SV.nth(own, x), c), SV.eq(c, SV.nth(own, x)), False{}, L.eq_sym(SV.nth(own, x), c), KB.ne_of_lt(SV.nth(own, x), c, hl)))),
        nonein_pre(t, own, R, D, c, us, L.band_r(psel(own, R, D, c, x), allpre(t, own, R, D, c), hp), hu))

def clean_of.c(b: Bool, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +k: Nat, +bp: List<&2, Nat>, +us: List<&2, Nat>, e: {SV.mem(k, bp) == b : Bool}, +hm: {SV.bor(b, SV.mem(k, us)) == True{} : Bool},
  +hp: {allpre(bp, own, R, D, c) == True{} : Bool}, +hu: {KB.allo(own, us, c) == True{} : Bool}, +hn: {SV.none_in(us, d) == True{} : Bool})
  -> {SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), psel(own, R, D, c, k)) == True{} : Bool}:
  match b:
    case True{}:
      L.bor_r(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), psel(own, R, D, c, k), allpre_mem(bp, own, R, D, c, k, hp, e))
    case False{}:
      L.bor_l(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), psel(own, R, D, c, k),
        L.band_i(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d)), allo_mem(own, us, c, k, hu, hm), KB.bnot_f(SV.mem(k, d), nonein_mem(us, d, k, hn, hm))))

# an Over set within the solved positions bp and c's us: its equations
# are c's own not dropped, or solved before c
def clean_of(s: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +bp: List<&2, Nat>, +us: List<&2, Nat>, +hs: {L.subl(s, SV.cat(bp, us)) == True{} : Bool},
  +hp: {allpre(bp, own, R, D, c) == True{} : Bool}, +hu: {KB.allo(own, us, c) == True{} : Bool}, +hn: {SV.none_in(us, d) == True{} : Bool}) -> {SV.clean(own, R, D, d, c, s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      L.band_i(SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), psel(own, R, D, c, k)), SV.clean(own, R, D, d, c, t),
        clean_of.c(SV.mem(k, bp), own, R, D, d, c, k, bp, us, {==}, Equal.trans(Bool, SV.bor(SV.mem(k, bp), SV.mem(k, us)), SV.mem(k, SV.cat(bp, us)), True{}, Equal.sym(Bool, SV.mem(k, SV.cat(bp, us)), SV.bor(SV.mem(k, bp), SV.mem(k, us)), SP.mem_cat(k, bp, us)), L.subl_hd(k, t, SV.cat(bp, us), hs)), hp, hu, hn),
        clean_of(t, own, R, D, d, c, bp, us, L.subl_tl(k, t, SV.cat(bp, us), hs), hp, hu, hn))

def beq_refl(a: Bool) -> {SP.beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the final drops at c's equations are its class's
def drop_at(+own: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +K: SV.Class, +d: List<&2, Nat>, +k: Nat, +hD: {CL.downs(own, cls, 0n) == True{} : Bool}, +hK: {SV.class_at(cls, c) == K : SV.Class}, +hkd: {SV.kdrops(K) == d : List<&2, Nat>},
  +nc: {SV.nth(own, k) == c : Nat}) -> {SV.mem(k, SV.dropped(cls)) == SV.mem(k, d) : Bool}:
  Equal.trans(Bool, SV.mem(k, SV.dropped(cls)), SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(own, k)))), SV.mem(k, d), CL.mem_dropped(own, cls, k, hD),
    (%Equal.sym(Nat, SV.nth(own, k), c, nc) : {SV.mem(k, SV.kdrops(SV.class_at(cls, _))) == SV.mem(k, d) : Bool}
      (%Equal.sym(SV.Class, SV.class_at(cls, c), K, hK) : {SV.mem(k, SV.kdrops(_)) == SV.mem(k, d) : Bool}
        (%Equal.sym(List<&2, Nat>, SV.kdrops(K), d, hkd) : {SV.mem(k, _) == SV.mem(k, d) : Bool}
          {==}))))

def agree_of.c(b: Bool, +own: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +K: SV.Class, +d: List<&2, Nat>, +j: Nat, +o: Nat, +ot: List<&2, Nat>, e: {SV.eq(o, c) == b : Bool}, +ho: {OW.ndrop(j, own) == Con{o, ot} : List<&2, Nat>},
  +hD: {CL.downs(own, cls, 0n) == True{} : Bool}, +hK: {SV.class_at(cls, c) == K : SV.Class}, +hkd: {SV.kdrops(K) == d : List<&2, Nat>}) -> {SV.bor(SV.bnot(b), SP.beq(SV.mem(j, SV.dropped(cls)), SV.mem(j, d))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.mem(j, SV.dropped(cls)), SV.mem(j, d), drop_at(own, cls, c, K, d, j, hD, hK, hkd, Equal.trans(Nat, SV.nth(own, j), o, c, OW.nth_of(own, j, o, ot, ho), L.eq_ok(o, c, e)))) : {SP.beq(_, SV.mem(j, d)) == True{} : Bool}
      beq_refl(SV.mem(j, d))
    case False{}:
      {==}

def agree_of(own_j: List<&2, Nat>, +own: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +K: SV.Class, +d: List<&2, Nat>, +j: Nat, +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>},
  +hD: {CL.downs(own, cls, 0n) == True{} : Bool}, +hK: {SV.class_at(cls, c) == K : SV.Class}, +hkd: {SV.kdrops(K) == d : List<&2, Nat>}) -> {SP.agree(own_j, SV.dropped(cls), d, c, j) == True{} : Bool}:
  match own_j:
    case Nil{}:
      {==}
    case Con{+o, +ot}:
      L.band_i(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(j, SV.dropped(cls)), SV.mem(j, d))), SP.agree(ot, SV.dropped(cls), d, c, 1n+j),
        agree_of.c(SV.eq(o, c), own, cls, c, K, d, j, o, ot, {==}, ho, hD, hK, hkd),
        agree_of(ot, own, cls, c, K, d, 1n+j, OW.ndrop_step(j, own, o, ot, ho), hD, hK, hkd))

# c's own equations not dropped: solved positions before c + 1
def allpre_us(us: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +K: SV.Class, +d: List<&2, Nat>, +hD: {CL.downs(own, cls, 0n) == True{} : Bool}, +hK: {SV.class_at(cls, c) == K : SV.Class}, +hkd: {SV.kdrops(K) == d : List<&2, Nat>},
  +hu: {KB.allo(own, us, c) == True{} : Bool}, +hred: {SV.mem(c, R) == False{} : Bool}, +hn: {SV.none_in(us, d) == True{} : Bool}) -> {allpre(us, own, R, SV.dropped(cls), 1n+c) == True{} : Bool}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +nc = L.eq_ok(SV.nth(own, u), c, L.band_l(SV.eq(SV.nth(own, u), c), KB.allo(own, t, c), hu))
      +hdn = KB.bnot_t(SV.mem(u, d), L.band_l(SV.bnot(SV.mem(u, d)), SV.none_in(t, d), hn))
      L.band_i(psel(own, R, SV.dropped(cls), 1n+c, u), allpre(t, own, R, SV.dropped(cls), 1n+c),
        L.band_i(SV.lt(SV.nth(own, u), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(own, u), R)), SV.bnot(SV.mem(u, SV.dropped(cls)))),
          (%Equal.sym(Nat, SV.nth(own, u), c, nc) : {SV.lt(_, 1n+c) == True{} : Bool}
            KB.lt_succ(c)),
          L.band_i(SV.bnot(SV.mem(SV.nth(own, u), R)), SV.bnot(SV.mem(u, SV.dropped(cls))),
            (%Equal.sym(Nat, SV.nth(own, u), c, nc) : {SV.bnot(SV.mem(_, R)) == True{} : Bool}
              KB.bnot_f(SV.mem(c, R), hred)),
            KB.bnot_f(SV.mem(u, SV.dropped(cls)), Equal.trans(Bool, SV.mem(u, SV.dropped(cls)), SV.mem(u, d), False{}, drop_at(own, cls, c, K, d, u, hD, hK, hkd, nc), hdn)))),
        allpre_us(t, own, R, cls, c, K, d, hD, hK, hkd, L.band_r(SV.eq(SV.nth(own, u), c), KB.allo(own, t, c), hu), hred, L.band_r(SV.bnot(SV.mem(u, d)), SV.none_in(t, d), hn)))

# The sketch's
# ------------

def drv_recs(sk: SK.Sketch, +i: Nat) -> {SV.driven(sk, i) == SV.driven.at(PA.recs(sk), i) : Bool}:
  match sk:
    case SK.Sketch{vs, es, cs}:
      {==}

def ncons_recs(sk: SK.Sketch) -> {SV.ncons(sk) == SV.clen(PA.recs(sk)) : Nat}:
  match sk:
    case SK.Sketch{vs, es, cs}:
      {==}

def drv_at(+sk: SK.Sketch, +i: Nat, +r: SK.Rec, +t: List<&2, SK.Rec>, hd: {KB.rdrop(i, PA.recs(sk)) == Con{r, t} : List<&2, SK.Rec>}) -> {SV.driven(sk, i) == SV.driven.rec(r) : Bool}:
  Equal.trans(Bool, SV.driven(sk, i), SV.driven.at(PA.recs(sk), i), SV.driven.rec(r), drv_recs(sk, i),
    Equal.trans(Bool, SV.driven.at(PA.recs(sk), i), SV.driven.at(KB.rdrop(i, PA.recs(sk)), 0n), SV.driven.rec(r), KB.driven_drop(PA.recs(sk), i), Equal.cong(List<&2, SK.Rec>, Bool, z => SV.driven.at(z, 0n), KB.rdrop(i, PA.recs(sk)), Con{r, t}, hd)))

def driving_at(+sk: SK.Sketch, +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hd: {KB.rdrop(i, PA.recs(sk)) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}) -> {SV.driving(sk, i) == True{} : Bool}:
  %Equal.sym(Bool, SV.driven(sk, i), False{}, drv_at(sk, i, SK.Rec{id, False{}, k}, t, hd)) : {SV.band(SV.lt(i, SV.ncons(sk)), SV.bnot(_)) == True{} : Bool}
  %Equal.sym(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), ncons_recs(sk)) : {SV.band(SV.lt(i, _), True{}) == True{} : Bool}
  Equal.trans(Bool, SV.band(SV.lt(i, SV.clen(PA.recs(sk))), True{}), SV.lt(i, SV.clen(PA.recs(sk))), True{}, CL.band_t(SV.lt(i, SV.clen(PA.recs(sk))), True{}, {==}), KB.lt_drop(PA.recs(sk), i, SK.Rec{id, False{}, k}, t, hd))

def clsn_pass(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS) -> {SV.clsn(PA.pass(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)) == SV.clen(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      %clsn_pass(t, sk, 1n+i, st) : {1n+SV.clsn(PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st)) == 1n+_ : Nat}
      {==}
    case Con{SK.Rec{id, False{}, k}, +t}:
      %clsn_pass(t, sk, 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))) : {1n+SV.clsn(PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)))) == 1n+_ : Nat}
      {==}

def noc_owners(sk: SK.Sketch, +i: Nat, +h: {SV.driven(sk, i) == True{} : Bool}) -> {OW.noc(SV.owners(sk), i) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      OW.owners_noc(es, cs, 0n, cs, i, {==}, KB.lt_z(i), h)

def vlen_eq(vs: List<&2, SK.VKind>) -> {PA.vlen(vs) == SO.vlen(vs) : Nat}:
  match vs:
    case Nil{}:
      {==}
    case Con{v, +t}:
      %vlen_eq(t) : {1n+PA.vlen(t) == 1n+_ : Nat}
      {==}

def nv_eq(sk: SK.Sketch) -> {PA.nvars(sk) == SO.nvars(sk) : Nat}:
  match sk:
    case SK.Sketch{+vs, es, cs}:
      vlen_eq(vs)

# The pass's invariant
# --------------------
# At position c, the state PS{kb, rows, B, bp, vm} against the final red
# list R and dropped list D.

def ps.kb(st: PA.PS) -> List<&2, Nat>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      kb

def ps.rows(st: PA.PS) -> List<&2, EL.Row>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      rows

def ps.B(st: PA.PS) -> List<&2, E.QExpr>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      B

def ps.bp(st: PA.PS) -> List<&2, Nat>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      bp

def ps.vm(st: PA.PS) -> List<&2, Maybe<&2, Nat>>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      vm

def pib(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>) -> Bool:
  SV.band(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))))

def pib_rinv(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {EP.rinv(B, rows, 0n) == True{} : Bool}:
  L.band_l(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h)

def pib_dist(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h))

def pib_mlen(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {SV.eq(L.mlen(vm), PA.nvars(sk)) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h)))

def pib_valid(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm) == True{} : Bool}:
  L.band_l(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h))))

def pib_s1(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {L.subl(ST.somes(vm), bp) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), L.band_r(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h)))))

def pib_s2(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {L.subl(bp, ST.somes(vm)) == True{} : Bool}:
  L.band_l(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))), L.band_r(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), L.band_r(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h))))))

def pib_bpd(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {SV.distinct(bp) == True{} : Bool}:
  L.band_l(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)), L.band_r(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))), L.band_r(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), L.band_r(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h)))))))

def pib_bpb(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}:
  L.band_l(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i), L.band_r(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)), L.band_r(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))), L.band_r(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), L.band_r(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h))))))))

def pib_pre(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}) -> {allpre(bp, SV.owners(sk), R, D, i) == True{} : Bool}:
  L.band_r(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i), L.band_r(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)), L.band_r(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))), L.band_r(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), L.band_r(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), L.band_r(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), L.band_r(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h))))))))

def pib_mk(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h_rinv: {EP.rinv(B, rows, 0n) == True{} : Bool}, h_dist: {SV.distinct(ST.somes(vm)) == True{} : Bool}, h_mlen: {SV.eq(L.mlen(vm), PA.nvars(sk)) == True{} : Bool}, h_valid: {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm) == True{} : Bool}, h_s1: {L.subl(ST.somes(vm), bp) == True{} : Bool}, h_s2: {L.subl(bp, ST.somes(vm)) == True{} : Bool}, h_bpd: {SV.distinct(bp) == True{} : Bool}, h_bpb: {SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, h_pre: {allpre(bp, SV.owners(sk), R, D, i) == True{} : Bool}) -> {pib(sk, R, D, i, rows, B, bp, vm) == True{} : Bool}:
  L.band_i(EP.rinv(B, rows, 0n), SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))))), h_rinv, L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))))), h_dist, L.band_i(SV.eq(L.mlen(vm), PA.nvars(sk)), SV.band(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))))), h_mlen, L.band_i(MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), vm), SV.band(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))))), h_valid, L.band_i(L.subl(ST.somes(vm), bp), SV.band(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)))), h_s1, L.band_i(L.subl(bp, ST.somes(vm)), SV.band(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i))), h_s2, L.band_i(SV.distinct(bp), SV.band(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i)), h_bpd, L.band_i(SV.below(bp, SV.neqs(SK.Sketch.eqs(sk))), allpre(bp, SV.owners(sk), R, D, i), h_bpb, h_pre))))))))


def PInv(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS) -> Data:
  SK.Both({pib(sk, R, D, i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st)) == True{} : Bool}, SK.Both({ps.kb(st) == SV.kept_before(sk, R, i) : List<&2, Nat>}, SK.Both(KB.KBP(sk, R, ps.kb(st), i),
    SK.Both({EL.rlen(ps.rows(st)) == SV.neqs(ps.B(st)) : Nat}, SK.Both({ps.B(st) == SV.presolved(sk, R, D, i) : List<&2, E.QExpr>}, {ps.B(st) == SV.picked(SK.Sketch.eqs(sk), ps.bp(st)) : List<&2, E.QExpr>})))))



# c is red, or driven: nothing changes but the position
def step_same(+sk: SK.Sketch, +i: Nat, +st: PA.PS, hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, st), +hz: {SP.zc(SV.owners(sk), i, SV.reds(PA.classes(sk))) == True{} : Bool}, +hdc: {KB.dcond(sk, SV.reds(PA.classes(sk)), i) == False{} : Bool})
  -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, st):
  (+hb, q1) = hi
  (+hk, q2) = q1
  (hK, q3) = q2
  (hl, q4) = q3
  (hB, hp) = q4
  (pib_mk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), pib_rinv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_dist(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_mlen(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_valid(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_s1(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_s2(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_bpd(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb), pib_bpb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb),
      allpre_up(ps.bp(st), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st), hb))),
    (Equal.trans(List<&2, Nat>, ps.kb(st), SV.kept_before(sk, SV.reds(PA.classes(sk)), i), SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i), hk, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i), SV.kept_before(sk, SV.reds(PA.classes(sk)), i),
        (%hdc : {SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i) == KB.kpk(_, SV.kept_before(sk, SV.reds(PA.classes(sk)), i), i) : List<&2, Nat>}
          KB.kb_next(sk, SV.reds(PA.classes(sk)), i)))),
    ((%hdc : KB.KBP(sk, SV.reds(PA.classes(sk)), KB.kpk(_, ps.kb(st), i), 1n+i)
        KB.kbp_next(sk, SV.reds(PA.classes(sk)), ps.kb(st), i, hK)),
    (hl,
    (Equal.trans(List<&2, E.QExpr>, ps.B(st), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i), hB, Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SP.presolved_same(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, hz))),
      hp)))))


def dcond_t(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hred: {SV.mem(i, R) == False{} : Bool}) -> {KB.dcond(sk, R, i) == True{} : Bool}:
  %Equal.sym(Bool, SV.driving(sk, i), True{}, hdrv) : {SV.band(_, SV.bnot(SV.mem(i, R))) == True{} : Bool}
  %Equal.sym(Bool, SV.mem(i, R), False{}, hred) : {SV.band(True{}, SV.bnot(_)) == True{} : Bool}
  {==}

def dcond_f(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, +hred: {SV.mem(i, R) == True{} : Bool}) -> {KB.dcond(sk, R, i) == False{} : Bool}:
  CL.band_f(SV.driving(sk, i), SV.bnot(SV.mem(i, R)), (%Equal.sym(Bool, SV.mem(i, R), True{}, hred) : {SV.bnot(_) == False{} : Bool}
    {==}))

# c is kept: its equations not dropped join the basis, its unit the
# matching, and c the kept constraints
def step_kept(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +vm2: List<&2, Maybe<&2, Nat>>, +K: SV.Class, hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hcw: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool},
  +hK: {SV.class_at(PA.classes(sk), i) == K : SV.Class}, +hkd: {SV.kdrops(K) == SV.drops(dd) : List<&2, Nat>}, +hred: {SV.mem(i, SV.reds(PA.classes(sk))) == False{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, PA.PS{CO.lsnoc(kb, i), rows2, B2, bp2, vm2}):
  (+hb, q1) = hi
  (+hk, q2) = q1
  (hKB, q3) = q2
  (hl, q4) = q3
  (hB, hp) = q4
  (+hcb, c1) = hcw
  (hcl, c2) = c1
  (hcB, c3) = c2
  (hcp, hbp2) = c3
  +d = SV.drops(dd)
  +hdc = dcond_t(sk, SV.reds(PA.classes(sk)), i, hdrv, hred)
  +hown = CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)
  +hdis = CW.cwb_udisj(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)
  +hbpd = dist_cat(bp, us, pib_bpd(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), nonein_pre(bp, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, us, pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), hown))
  +hbpb = below_cat(bp, us, SV.neqs(SK.Sketch.eqs(sk)), pib_bpb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), CW.cwb_ubelow(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb))
  +hpre = allpre_cat(bp, us, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, allpre_up(bp, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb)), allpre_us(us, SV.owners(sk), SV.reds(PA.classes(sk)), PA.classes(sk), i, K, d, hD, hK, hkd, hown, hred, hdis))
  +E2 = Equal.sym(List<&2, Nat>, bp2, SV.cat(bp, us), hbp2)
  (pib_mk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, rows2, B2, bp2, vm2, CW.cwb_rinv(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), GM.gok_dist(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_mlen(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_valid(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok),
      (%E2 : {L.subl(ST.somes(vm2), _) == True{} : Bool}
        GM.gok_s1(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok)),
      (%E2 : {L.subl(_, ST.somes(vm2)) == True{} : Bool}
        GM.gok_s2(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok)),
      (%E2 : {SV.distinct(_) == True{} : Bool}
        hbpd),
      (%E2 : {SV.below(_, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}
        hbpb),
      (%E2 : {allpre(_, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i) == True{} : Bool}
        hpre)),
    (Equal.trans(List<&2, Nat>, CO.lsnoc(kb, i), CO.lsnoc(SV.kept_before(sk, SV.reds(PA.classes(sk)), i), i), SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => CO.lsnoc(z, i), kb, SV.kept_before(sk, SV.reds(PA.classes(sk)), i), hk),
        Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i), CO.lsnoc(SV.kept_before(sk, SV.reds(PA.classes(sk)), i), i), (%hdc : {SV.kept_before(sk, SV.reds(PA.classes(sk)), 1n+i) == KB.kpk(_, SV.kept_before(sk, SV.reds(PA.classes(sk)), i), i) : List<&2, Nat>}
          KB.kb_next(sk, SV.reds(PA.classes(sk)), i)))),
    ((%hdc : KB.KBP(sk, SV.reds(PA.classes(sk)), KB.kpk(_, kb, i), 1n+i)
        KB.kbp_next(sk, SV.reds(PA.classes(sk)), kb, i, hKB)),
    (hcl,
    (Equal.trans(List<&2, E.QExpr>, B2, SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, d, SV.neqs(SK.Sketch.eqs(sk)))), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i), hcB,
        Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i), SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, d, SV.neqs(SK.Sketch.eqs(sk)))), SP.presolved_kept(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), d, i, hred, agree_of(SV.owners(sk), SV.owners(sk), PA.classes(sk), i, K, d, 0n, {==}, hD, hK, hkd)))),
      hcp)))))

# Each driving constraint's class
# -------------------------------

def pinv_kb(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> {ps.kb(st) == SV.kept_before(sk, R, i) : List<&2, Nat>}:
  (h1, q1) = hi
  (h2, q2) = q1
  h2

def pinv_kbp(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> KB.KBP(sk, R, ps.kb(st), i):
  (h1, q1) = hi
  (h2, q2) = q1
  (h3, q3) = q2
  h3

def pinv_b(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> {pib(sk, R, D, i, ps.rows(st), ps.B(st), ps.bp(st), ps.vm(st)) == True{} : Bool}:
  (h1, q1) = hi
  h1

def pinv_rlen(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> {EL.rlen(ps.rows(st)) == SV.neqs(ps.B(st)) : Nat}:
  (h1, q1) = hi
  (h2, q2) = q1
  (h3, q3) = q2
  (h4, q4) = q3
  h4

def pinv_B(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> {ps.B(st) == SV.presolved(sk, R, D, i) : List<&2, E.QExpr>}:
  (h1, q1) = hi
  (h2, q2) = q1
  (h3, q3) = q2
  (h4, q4) = q3
  (h5, h6) = q4
  h5

def pinv_p(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, +st: PA.PS, hi: PInv(sk, R, D, i, st)) -> {ps.B(st) == SV.picked(SK.Sketch.eqs(sk), ps.bp(st)) : List<&2, E.QExpr>}:
  (h1, q1) = hi
  (h2, q2) = q1
  (h3, q3) = q2
  (h4, q4) = q3
  (h5, h6) = q4
  h6

# the pass's class at c and its state after
def StepRes(+sk: SK.Sketch, +i: Nat, +o: PA.PO) -> Type:
  SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PO.k(o)) & PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, PA.PO.st(o))

def red_of(+sk: SK.Sketch, +i: Nat, +K: SV.Class, +hK: {SV.class_at(PA.classes(sk), i) == K : SV.Class}) -> {SV.mem(i, SV.reds(PA.classes(sk))) == SV.is_red(K) : Bool}:
  Equal.trans(Bool, SV.mem(i, SV.reds(PA.classes(sk))), SV.is_red(SV.class_at(PA.classes(sk), i)), SV.is_red(K), CL.mem_reds(PA.classes(sk), i), Equal.cong(SV.Class, Bool, z => SV.is_red(z), SV.class_at(PA.classes(sk), i), K, hK))

def onea_red(m: Maybe<&2, List<&2, SV.Ref>>, +dd: List<&2, SV.Drop>) -> {SV.is_red(PA.one.a(m, dd)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{rs}:
      {==}

def onek_red(a: Bool, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> {SV.is_red(PA.one.k(a, sk, kb, c, dd)) == False{} : Bool}:
  match a:
    case True{}:
      onea_red(PA.srefs(SV.csides(sk, [c]), sk, kb, c, 0n), dd)
    case False{}:
      {==}

def step.conf(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hr: {CO.refutable(sk, i, kb) == True{} : Bool},
  +hK: {SV.class_at(PA.classes(sk), i) == SV.Conflict{CO.support(sk, i, kb)} : SV.Class}) -> StepRes(sk, i, PA.PO{SV.Conflict{CO.support(sk, i, kb)}, PA.PS{kb, rows, B, bp, vm}}):
  +hred = red_of(sk, i, SV.Conflict{CO.support(sk, i, kb)}, hK)
  (PR.conflict(sk, SV.reds(PA.classes(sk)), i, kb, pinv_kbp(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), hr), step_same(sk, i, PA.PS{kb, rows, B, bp, vm}, hi, SP.zc_red(SV.owners(sk), i, SV.reds(PA.classes(sk)), hred), dcond_f(sk, SV.reds(PA.classes(sk)), i, hred)))

def bpus_dist(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +us: List<&2, Nat>, +hb: {pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm) == True{} : Bool},
  +hud: {SV.distinct(us) == True{} : Bool}, +hown: {KB.allo(SV.owners(sk), us, i) == True{} : Bool}) -> {SV.distinct(SV.cat(bp, us)) == True{} : Bool}:
  dist_cat(bp, us, pib_bpd(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), hud, nonein_pre(bp, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, us, pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), hown))

def step.over(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +j: Nat, +s: List<&2, Nat>, +x: List<&2, Nat>,
  +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool}, hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i),
  gr: GM.GRes(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, ST.GFail{ST.Red{j, s, x}}), +hK: {SV.class_at(PA.classes(sk), i) == SV.Over{j, s, x} : SV.Class}) -> StepRes(sk, i, PA.PO{SV.Over{j, s, x}, PA.PS{kb, rows, B, bp, vm}}):
  (+hb2, hov) = gr
  +hred = red_of(sk, i, SV.Over{j, s, x}, hK)
  +hr2 = L.band_r(SV.mem(j, us), SV.band(SV.mem(j, s), L.subl(s, SV.cat(bp, us))), hb2)
  ((hnr, (SV.drops(dd), (hdo, (L.band_i(SV.eq(SV.nth(SV.owners(sk), j), i), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.drops(dd), i, s)),
      allo_mem(SV.owners(sk), us, i, j, CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), L.band_l(SV.mem(j, us), SV.band(SV.mem(j, s), L.subl(s, SV.cat(bp, us))), hb2)),
      L.band_i(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.drops(dd), i, s), L.band_l(SV.mem(j, s), L.subl(s, SV.cat(bp, us)), hr2),
        clean_of(s, SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.drops(dd), i, bp, us, L.band_r(SV.mem(j, s), L.subl(s, SV.cat(bp, us)), hr2), pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_udisj(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)))), hov)))),
    step_same(sk, i, PA.PS{kb, rows, B, bp, vm}, hi, SP.zc_red(SV.owners(sk), i, SV.reds(PA.classes(sk)), hred), dcond_f(sk, SV.reds(PA.classes(sk)), i, hred)))


def imp_at(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rs: List<&2, SV.Ref>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>}, +hkb: {kb == SV.kept_before(sk, SV.reds(PA.classes(sk)), i) : List<&2, Nat>}, +j: Nat, hj: {SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool})
  -> SV.Implied(sk, SV.reds(PA.classes(sk)), i, j):
  (%hkb : PR.ImpK(sk, _, i, j)
    PR.srefs_some(SV.csides(sk, [i]), sk, kb, i, 0n, rs, em, j, hj))

def notimp(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == None{} : Maybe<&2, List<&2, SV.Ref>>}, +hkb: {kb == SV.kept_before(sk, SV.reds(PA.classes(sk)), i) : List<&2, Nat>}) -> &j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(PA.classes(sk)), i, j)):
  (%hkb : PR.NotK(sk, _, i, 0n, SV.slen(SV.csides(sk, [i])))
    PR.srefs_none(SV.csides(sk, [i]), sk, kb, i, 0n, em))

def noamb(+sk: SK.Sketch, +i: Nat, +dd: List<&2, SV.Drop>, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == False{} : Bool}, ha: {SV.is_amberable(sk, i, SV.drops(dd)) == True{} : Bool}) -> &j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(PA.classes(sk)), i, j)):
  absurd(&j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(PA.classes(sk)), i, j)), KA.tf(Equal.trans(Bool, True{}, SV.is_amberable(sk, i, SV.drops(dd)), False{}, Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), True{}, ha), ea)))

def step.a(m: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +dd: List<&2, SV.Drop>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == m : Maybe<&2, List<&2, SV.Ref>>}, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == True{} : Bool},
  hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), hmt: SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))), +hkb: {kb == SV.kept_before(sk, SV.reds(PA.classes(sk)), i) : List<&2, Nat>})
  -> SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.a(PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), dd)):
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, List<&2, SV.Ref>>, PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), None{}, em) : SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.a(_, dd))
      (hnr, (hdo, (hmt, ha => notimp(sk, i, kb, em, hkb))))
    case Some{+rs}:
      %Equal.sym(Maybe<&2, List<&2, SV.Ref>>, PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), Some{rs}, em) : SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.a(_, dd))
      (hnr, (hdo, (ea, j => hj => imp_at(sk, i, kb, rs, em, hkb, j, hj))))

def step.k(a: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +dd: List<&2, SV.Drop>, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == a : Bool}, hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), hmt: SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))),
  +hkb: {kb == SV.kept_before(sk, SV.reds(PA.classes(sk)), i) : List<&2, Nat>}) -> SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)):
  match a:
    case True{}:
      %Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), True{}, ea) : SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.k(_, sk, kb, i, dd))
      step.a(PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), sk, i, kb, dd, {==}, ea, hnr, hdo, hmt, hkb)
    case False{}:
      %Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), False{}, ea) : SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.one.k(_, sk, kb, i, dd))
      (hnr, (hdo, (hmt, ha => noamb(sk, i, dd, ea, ha))))


def mt_eq(+sk: SK.Sketch, +i: Nat, +bp: List<&2, Nat>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, hcB: {B2 == SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>},
  hcp: {B2 == SV.picked(SK.Sketch.eqs(sk), bp2) : List<&2, E.QExpr>}, hbp2: {bp2 == SV.cat(bp, us) : List<&2, Nat>}) -> {SV.picked(SK.Sketch.eqs(sk), SV.cat(bp, us)) == SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>}:
  Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), SV.cat(bp, us)), SV.picked(SK.Sketch.eqs(sk), bp2), SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))),
    Equal.cong(List<&2, Nat>, List<&2, E.QExpr>, z => SV.picked(SK.Sketch.eqs(sk), z), SV.cat(bp, us), bp2, Equal.sym(List<&2, Nat>, bp2, SV.cat(bp, us), hbp2)),
    Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), bp2), B2, SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))), Equal.sym(List<&2, E.QExpr>, B2, SV.picked(SK.Sketch.eqs(sk), bp2), hcp), hcB))

def mt_of(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +vm2: List<&2, Maybe<&2, Nat>>,
  +hb: {pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm) == True{} : Bool}, +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool},
  hcB: {B2 == SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>}, hcp: {B2 == SV.picked(SK.Sketch.eqs(sk), bp2) : List<&2, E.QExpr>}, hbp2: {bp2 == SV.cat(bp, us) : List<&2, Nat>},
  +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool}) -> SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))):
  (%mt_eq(sk, i, bp, B2, bp2, dd, us, hcB, hcp, hbp2) : SV.Matchable(_)
    GM.matchable_of(SK.Sketch.eqs(sk), vm2, SV.cat(bp, us), GM.gok_valid(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_s2(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok),
      bpus_dist(sk, i, rows, B, bp, vm, us, hb, CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb))))

def step.ok(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +vm2: List<&2, Maybe<&2, Nat>>,
  +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i),
  +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool}, +hK: {SV.class_at(PA.classes(sk), i) == PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd) : SV.Class}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> StepRes(sk, i, PA.PO{PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), PA.PS{CO.lsnoc(kb, i), rows2, B2, bp2, vm2}}):
  (+hcb, c1) = hci
  (hcl, c2) = c1
  (hcB, c3) = c2
  (hcp, hbp2) = c3
  +hb = pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
  (step.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, i, kb, dd, {==}, hnr, hdo, mt_of(sk, i, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, hb, hcb, hcB, hcp, hbp2, hgok), pinv_kb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)),
    step_kept(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hi, hci, hgok, hK, onek_kd(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd),
      Equal.trans(Bool, SV.mem(i, SV.reds(PA.classes(sk))), SV.is_red(PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), False{}, red_of(sk, i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hK), onek_red(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), hdrv, hD))


def step.g(g: ST.GS, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i), gr: GM.GRes(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, g),
  +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}) -> StepRes(sk, i, PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  match g:
    case ST.GFail{ST.Red{+j, +s, +x}}:
      step.over(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, j, s, x, hi, hdo, CW.inv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}, hci), hnr, gr, hK)
    case ST.GOk{+vm2}:
      step.ok(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, hi, hdo, hci, hnr, gr, hK, hdrv, hD)

def gli_of(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hb: {pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm) == True{} : Bool}, +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {GM.gli(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, vm) == True{} : Bool}:
  GM.gli_mk(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, vm, pib_dist(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), pib_mlen(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), pib_valid(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb),
    pib_s1(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), pib_s2(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb),
    bpus_dist(sk, i, rows, B, bp, vm, us, hb, CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)),
    below_cat(bp, us, SV.neqs(SK.Sketch.eqs(sk)), pib_bpb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb), CW.cwb_ubelow(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)), hA)


def step.w2(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)), +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i),
  +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> StepRes(sk, i, PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  step.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hdo, hci, hnr,
    GM.gl_ok(us, SK.Sketch.eqs(sk), PA.nvars(sk), bp, vm, gli_of(sk, i, rows, B, bp, vm, rows2, B2, dd, us, pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), CW.inv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}, hci), hA)), hK, hdrv, hD)

def step.w3(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), hcw: (SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(dd)) & CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us})), hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i),
  +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> StepRes(sk, i, PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  (hdo, hci) = hcw
  step.w2(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hdo, hci, hnr, hK, hA, hdrv, hD)

def step.w(w: PA.CW, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}),
  hcw: (SV.DropsOk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, SV.drops(CW.cw.ds(w))) & CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), w)), hnr: SV.NoRefute(sk, SV.reds(PA.classes(sk)), i), +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}) -> StepRes(sk, i, PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)):
  match w:
    case PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      step.w3(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hcw, hnr, hK, hA, hdrv, hD)


def step.c(b: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +eb: {CO.refutable(sk, i, kb) == b : Bool}, +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}),
  +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.c(CO.refutable(sk, i, kb), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}) -> StepRes(sk, i, PA.one.c(CO.refutable(sk, i, kb), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)):
  match b:
    case True{}:
      %Equal.sym(Bool, CO.refutable(sk, i, kb), True{}, eb) : StepRes(sk, i, PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm))
      step.conf(sk, i, kb, rows, B, bp, vm, hi, eb, (%eb : {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class}
        hK))
    case False{}:
      %Equal.sym(Bool, CO.refutable(sk, i, kb), False{}, eb) : StepRes(sk, i, PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm))
      +hkb = pinv_kb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
      step.w(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), i, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}), sk, i, kb, rows, B, bp, vm, hi,
        CW.cw_final(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, pib_rinv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), pinv_rlen(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), pinv_B(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), pinv_p(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)),
        PR.norefute(sk, SV.reds(PA.classes(sk)), i, (%hkb : {CO.refutable(sk, i, _) == False{} : Bool}
          eb)),
        (%eb : {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class}
          hK), hA, hdrv, hD)

# a driving constraint at i: its class and the next state
def hon.d(st: PA.PS, +sk: SK.Sketch, +i: Nat, +hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, st), +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)) : SV.Class},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}) -> StepRes(sk, i, PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)):
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      step.c(CO.refutable(sk, i, kb), sk, i, kb, rows, B, bp, vm, {==}, hi, hK, hA, hdrv, hD)

# The pass is honest
# ------------------

def fate_of(+sk: SK.Sketch, +i: Nat, +K: SV.Class, +hK: {SV.class_at(PA.classes(sk), i) == K : SV.Class}, +hdr: {SV.driven(sk, i) == False{} : Bool}, f: SV.Fate.driving(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, K)) -> SV.Fate(sk, PA.classes(sk), i):
  (%Equal.sym(Bool, SV.driven(sk, i), False{}, hdr) : SV.Fate.pick(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, _, SV.class_at(PA.classes(sk), i))
    (%Equal.sym(SV.Class, SV.class_at(PA.classes(sk), i), K, hK) : SV.Fate.pick(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, False{}, _)
      f))

def fate_dr(+sk: SK.Sketch, +i: Nat, +hK: {SV.class_at(PA.classes(sk), i) == SV.Kept{Nil{}} : SV.Class}, +hdr: {SV.driven(sk, i) == True{} : Bool}) -> SV.Fate(sk, PA.classes(sk), i):
  (%Equal.sym(Bool, SV.driven(sk, i), True{}, hdr) : SV.Fate.pick(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, _, SV.class_at(PA.classes(sk), i))
    (%Equal.sym(SV.Class, SV.class_at(PA.classes(sk), i), SV.Kept{Nil{}}, hK) : SV.Fate.pick(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, True{}, _)
      {==}))

def dcond_dr(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, +hdr: {SV.driven(sk, i) == True{} : Bool}) -> {KB.dcond(sk, R, i) == False{} : Bool}:
  %Equal.sym(Bool, SV.driving(sk, i), False{}, CL.band_f(SV.lt(i, SV.ncons(sk)), SV.bnot(SV.driven(sk, i)), (%Equal.sym(Bool, SV.driven(sk, i), True{}, hdr) : {SV.bnot(_) == False{} : Bool}
    {==}))) : {SV.band(_, SV.bnot(SV.mem(i, R))) == False{} : Bool}
  {==}


def hon.con(+sk: SK.Sketch, +i: Nat, +st: PA.PS, +t: List<&2, SK.Rec>, +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)) : SV.Class}, +hdr: {SV.driven(sk, i) == False{} : Bool}, sr: StepRes(sk, i, PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)),
  ih: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))) -> SV.Honest.go(sk, PA.classes(sk), SV.clen(t), 1n+i)) -> SV.Honest.go(sk, PA.classes(sk), 1n+SV.clen(t), i):
  (f1, inv1) = sr
  (fate_of(sk, i, PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), hK, hdr, f1), ih(inv1))

# from position i on, given the classes from i are the pass's from there
def hon(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS, +hd: {KB.rdrop(i, PA.recs(sk)) == rs : List<&2, SK.Rec>}, +hc: {CL.cdrop(i, PA.classes(sk)) == PA.pass(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st) : List<&2, SV.Class>},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}, hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, st)) -> SV.Honest.go(sk, PA.classes(sk), SV.clen(rs), i):
  match rs:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      +hdr = drv_at(sk, i, SK.Rec{id, True{}, k}, t, hd)
      (fate_dr(sk, i, CL.ca_of(PA.classes(sk), i, SV.Kept{Nil{}}, PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st), hc), hdr),
        hon(t, sk, 1n+i, st, KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, True{}, k}, t, hd), CL.cdrop_step(PA.classes(sk), i, SV.Kept{Nil{}}, PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st), hc), hA, hD,
          step_same(sk, i, st, hi, SP.zc_noc(SV.owners(sk), i, SV.reds(PA.classes(sk)), noc_owners(sk, i, hdr)), dcond_dr(sk, SV.reds(PA.classes(sk)), i, hdr))))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      +hK = CL.ca_of(PA.classes(sk), i, PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), hc)
      hon.con(sk, i, st, t, hK, drv_at(sk, i, SK.Rec{id, False{}, k}, t, hd), hon.d(st, sk, i, hi, hK, hA, driving_at(sk, i, id, k, t, hd), hD),
        h2 => hon(t, sk, 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, False{}, k}, t, hd), CL.cdrop_step(PA.classes(sk), i, PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), hc), hA, hD, h2))

def pinv0(+sk: SK.Sketch) -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 0n, PA.start(PA.nvars(sk))):
  (pib_mk(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 0n, Nil{}, Nil{}, Nil{}, ST.nones(PA.nvars(sk)), {==},
      (%Equal.sym(List<&2, Nat>, ST.somes(ST.nones(PA.nvars(sk))), Nil{}, RP.somes_nones(PA.nvars(sk))) : {SV.distinct(_) == True{} : Bool}
        {==}),
      (%Equal.sym(Nat, L.mlen(ST.nones(PA.nvars(sk))), PA.nvars(sk), RP.mlen_nones(PA.nvars(sk))) : {SV.eq(_, PA.nvars(sk)) == True{} : Bool}
        L.eq_refl(PA.nvars(sk))),
      MX.valid_nones(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk), 0n),
      (%Equal.sym(List<&2, Nat>, ST.somes(ST.nones(PA.nvars(sk))), Nil{}, RP.somes_nones(PA.nvars(sk))) : {L.subl(_, Nil{}) == True{} : Bool}
        {==}),
      {==}, {==}, {==}, {==}),
    (Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(PA.classes(sk)), 0n), Nil{}, KB.kb_zero(sk, SV.reds(PA.classes(sk)))),
    (KB.kbp_zero(sk, SV.reds(PA.classes(sk))),
    ({==},
    (Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 0n), Nil{}, SP.presolved_zero(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)))),
      {==})))))

# the pass's classes are honest (law 4's search half: spec/solve.bend, Honest)
def pass_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> SV.Honest(sk, PA.classes(sk)):
  +ha0 = CV.cov(sk, SO.nvars(sk), cov, WC.wf_dec_ok(sk, w))
  +hA = GM.adjb_dadjs(SK.Sketch.eqs(sk), PA.nvars(sk), (%Equal.sym(Nat, PA.nvars(sk), SO.nvars(sk), nv_eq(sk)) : {D.adjb(ST.adj(SK.Sketch.eqs(sk)), _) == True{} : Bool}
    ha0))
  (Equal.trans(Nat, SV.clsn(PA.classes(sk)), SV.clen(PA.recs(sk)), SV.ncons(sk), clsn_pass(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk))), Equal.sym(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), ncons_recs(sk))),
    (%Equal.sym(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), ncons_recs(sk)) : SV.Honest.go(sk, PA.classes(sk), _, 0n)
      hon(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), {==}, {==}, hA, classes_down(sk), pinv0(sk))))

# The state the pass ends with
# ----------------------------

def pinv_sr(+sk: SK.Sketch, +i: Nat, +o: PA.PO, sr: StepRes(sk, i, o)) -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), 1n+i, PA.PO.st(o)):
  (f, p) = sr
  p

def pinv_add(+sk: SK.Sketch, +n: Nat, +i: Nat, +st: PA.PS, h: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), Nat.add(n, 1n+i), st)) -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), Nat.add(1n+n, i), st):
  (%Equal.sym(Nat, 1n+Nat.add(n, i), Nat.add(n, 1n+i), LN.add_succ(n, i)) : PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), _, st)
    h)

# the invariant at the end of the walk from position i
def pass_inv(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS, +hd: {KB.rdrop(i, PA.recs(sk)) == rs : List<&2, SK.Rec>}, +hc: {CL.cdrop(i, PA.classes(sk)) == PA.pass(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st) : List<&2, SV.Class>},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}, hi: PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, st)) -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), Nat.add(SV.clen(rs), i), PA.pass_st(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)):
  match rs:
    case Nil{}:
      hi
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      +hdr = drv_at(sk, i, SK.Rec{id, True{}, k}, t, hd)
      pinv_add(sk, SV.clen(t), i, PA.pass_st(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st),
        pass_inv(t, sk, 1n+i, st, KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, True{}, k}, t, hd), CL.cdrop_step(PA.classes(sk), i, SV.Kept{Nil{}}, PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st), hc), hA, hD,
          step_same(sk, i, st, hi, SP.zc_noc(SV.owners(sk), i, SV.reds(PA.classes(sk)), noc_owners(sk, i, hdr)), dcond_dr(sk, SV.reds(PA.classes(sk)), i, hdr))))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      +hK = CL.ca_of(PA.classes(sk), i, PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), hc)
      pinv_add(sk, SV.clen(t), i, PA.pass_st(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))),
        pass_inv(t, sk, 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, False{}, k}, t, hd), CL.cdrop_step(PA.classes(sk), i, PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st)), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), hc), hA, hD,
          pinv_sr(sk, i, PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st), hon.d(st, sk, i, hi, hK, hA, driving_at(sk, i, id, k, t, hd), hD))))

def adjb_of(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}:
  GM.adjb_dadjs(SK.Sketch.eqs(sk), PA.nvars(sk), (%Equal.sym(Nat, PA.nvars(sk), SO.nvars(sk), nv_eq(sk)) : {D.adjb(ST.adj(SK.Sketch.eqs(sk)), _) == True{} : Bool}
    CV.cov(sk, SO.nvars(sk), cov, WC.wf_dec_ok(sk, w))))

# the pass's final state: its basis is the system solved, its matching a
# valid matching of exactly its positions
def final_inv(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk)):
  (%Equal.sym(Nat, SV.ncons(sk), Nat.add(SV.clen(PA.recs(sk)), 0n), Equal.trans(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), Nat.add(SV.clen(PA.recs(sk)), 0n), ncons_recs(sk), LN.add_zero(SV.clen(PA.recs(sk))))) : PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), _, PA.final_st(sk))
    pass_inv(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), {==}, {==}, adjb_of(sk, w, cov), classes_down(sk), pinv0(sk)))
