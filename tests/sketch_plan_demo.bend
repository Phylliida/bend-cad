# The sketch-level laws at work on a real sketch. Four free points A, B, P,
# Q with |AP| = |BP| = 3 and |AQ| = |PQ| = 3 (driving distance dimensions).
# The plan of tests/chain_data.bend pins A = (0, 0) and B = (4, 0) (radius 0
# in the box) and certifies P, then Q; it checks on the sketch's own exact
# system (Sketch.eqs), and the sketch's side conditions (each distance's
# d ≥ 0) check over the box. So in every complete ordered field the box
# holds a geometry meaning the sketch, and in every ordered field at most
# one: P = (2, √5), Q = (1 - √15/2, √5/2 + √3), the other three choices of
# branch lying outside the box.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../lib/karith.bend as KA
import ../lib/kball.bend as KB
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ../lib/planpf.bend as PP
import ./chain_data.bend as D

def three() -> E.QExpr:
  E.QCst{S.Q{S.Zpos{S.XI{S.XH{}}}, S.XH{}}}

def pt(id: Nat, x: Nat, y: Nat) -> SK.Ent:
  SK.Ent{id, False{}, SK.GPoint{x, y}}

def dist(id: Nat, p: Nat, q: Nat) -> SK.Rec:
  SK.Rec{id, False{}, SK.Distance{p, q, three()}}

# variables: 0, 1 A; 2, 3 B; 4, 5 P; 6, 7 Q. Points 0 A, 1 B, 2 P, 3 Q.
def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}],
    [pt(0n, 0n, 1n), pt(1n, 2n, 3n), pt(2n, 4n, 5n), pt(3n, 6n, 7n)],
    [dist(0n, 0n, 2n), dist(1n, 1n, 2n), dist(2n, 0n, 3n), dist(3n, 2n, 3n)]}

def wf() -> SK.Sketch.wf(sk()):
  ((Unit{}, (Unit{}, (Unit{}, (Unit{}, Unit{})))), (({==}, {==}), (Unit{}, (({==}, {==}), (Unit{}, (({==}, {==}), (Unit{}, (({==}, {==}), (Unit{}, Unit{})))))))))

def plan_ok() -> {PL.check(~KI.dnum(), SK.Sketch.eqs(sk()), D.ch_gc(), D.ch_gr(), D.ch_plan()) == True{} : Bool}:
  {==}

def sides_ok() -> {PL.check_sides(~KI.dnum(), SK.Sketch.sides(sk()), D.ch_gc(), D.ch_gr()) == True{} : Bool}:
  {==}


# What the demo concludes, without the checker's numbers
# -------------------------------------------------------
# A type that names the box over the dyadics would make Bend unfold each
# 40-bit center into a tree of 2^40 ones in F (O.ofp doubles by adding),
# so the statement below mentions only small rationals: the pins. The
# proof is generic in the checker's numbers and instantiated once.

def q0() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def q4() -> S.Q:
  S.Q{S.Zpos{S.XO{S.XO{S.XH{}}}}, S.XH{}}

# A = (0, 0) and B = (4, 0)
def Pins(~F: O.OField, +x: M.Vec(~F)) -> Data:
  M.Both({O.lookup(~F, x, 0n) == O.ofq(~F, q0()) : O.C(F)},
  M.Both({O.lookup(~F, x, 1n) == O.ofq(~F, q0()) : O.C(F)},
  M.Both({O.lookup(~F, x, 2n) == O.ofq(~F, q4()) : O.C(F)},
  {O.lookup(~F, x, 3n) == O.ofq(~F, q0()) : O.C(F)})))

# the box pins variable i to q
def PinAt(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +i: Nat, +q: S.Q) -> Data:
  M.Both({KA.natle(1n+i, KA.klen(~K, gc)) == True{} : Bool},
  M.Both({KB.klook(~K, gr, i) == N.nzero(K) : N.NC(K)},
  {N.nofq(K, q) == Some{KB.klook(~K, gc, i)} : Maybe<&2, N.NC(K)>}))

def pin_val.b(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x), +i: Nat, +q: S.Q, hi: {KA.natle(1n+i, KA.klen(~K, gc)) == True{} : Bool}, t: M.Both({KB.klook(~K, gr, i) == N.nzero(K) : N.NC(K)}, {N.nofq(K, q) == Some{KB.klook(~K, gc, i)} : Maybe<&2, N.NC(K)>})) -> {O.lookup(~F, x, i) == O.ofq(~F, q) : O.C(F)}:
  (+hr, +hq) = t
  Equal.trans(O.C(F), O.lookup(~F, x, i), N.emap(K, F, H, KB.klook(~K, gc, i)), O.ofq(~F, q), PP.box_pin(~K, ~F, ~H, gc, gr, x, h, i, hi, hr), N.e_ofq(K, F, H)(q, KB.klook(~K, gc, i), hq))

def pin_val(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x), +i: Nat, +q: S.Q, hp: PinAt(~K, gc, gr, i, q)) -> {O.lookup(~F, x, i) == O.ofq(~F, q) : O.C(F)}:
  (+hi, +t) = hp
  pin_val.b(~K, ~F, ~H, gc, gr, x, h, i, q, hi, t)

def PinsAt(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> Data:
  M.Both(PinAt(~K, gc, gr, 0n, q0()), M.Both(PinAt(~K, gc, gr, 1n, q0()), M.Both(PinAt(~K, gc, gr, 2n, q4()), PinAt(~K, gc, gr, 3n, q0()))))

def pins.c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), +h: BX.inbox(~K, ~F, ~H, gc, gr, x), hp: M.Both(PinAt(~K, gc, gr, 2n, q4()), PinAt(~K, gc, gr, 3n, q0()))) -> M.Both({O.lookup(~F, x, 2n) == O.ofq(~F, q4()) : O.C(F)}, {O.lookup(~F, x, 3n) == O.ofq(~F, q0()) : O.C(F)}):
  (+h2, +h3) = hp
  (pin_val(~K, ~F, ~H, gc, gr, x, h, 2n, q4(), h2), pin_val(~K, ~F, ~H, gc, gr, x, h, 3n, q0(), h3))

def pins.b(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), +h: BX.inbox(~K, ~F, ~H, gc, gr, x), hp: M.Both(PinAt(~K, gc, gr, 1n, q0()), M.Both(PinAt(~K, gc, gr, 2n, q4()), PinAt(~K, gc, gr, 3n, q0())))) -> M.Both({O.lookup(~F, x, 1n) == O.ofq(~F, q0()) : O.C(F)}, M.Both({O.lookup(~F, x, 2n) == O.ofq(~F, q4()) : O.C(F)}, {O.lookup(~F, x, 3n) == O.ofq(~F, q0()) : O.C(F)})):
  (+h1, +t) = hp
  (pin_val(~K, ~F, ~H, gc, gr, x, h, 1n, q0(), h1), pins.c(~K, ~F, ~H, gc, gr, x, h, t))

def pins(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), +h: BX.inbox(~K, ~F, ~H, gc, gr, x), hp: PinsAt(~K, gc, gr)) -> Pins(~F, x):
  (+h0, +t) = hp
  (pin_val(~K, ~F, ~H, gc, gr, x, h, 0n, q0(), h0), pins.b(~K, ~F, ~H, gc, gr, x, h, t))

def exists.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +hp: PinsAt(~K, gc, gr), s: &x: M.Vec(~F) -> (BX.inbox(~K, ~F, ~H, gc, gr, x) & SK.Sketch.means(~F, x, sk()))) -> &x: M.Vec(~F) -> (SK.Sketch.means(~F, x, sk()) & Pins(~F, x)):
  (+x, hm) = s
  (+h, m) = hm
  (x, (m, pins(~K, ~F, ~H, gc, gr, x, h, hp)))

def exists.k(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, SK.Sketch.eqs(sk()), gc, gr, p) == True{} : Bool}, os: {PL.check_sides(~K, SK.Sketch.sides(sk()), gc, gr) == True{} : Bool}, hp: PinsAt(~K, gc, gr)) -> &x: M.Vec(~F) -> (SK.Sketch.means(~F, x, sk()) & Pins(~F, x)):
  exists.go(~K, ~F, ~H, gc, gr, hp, PP.sketch_exists(~K, ~F, ~R, ~H, sk(), wf(), gc, gr, p, ok, os))

def pins_ok() -> PinsAt(~KI.dnum(), D.ch_gc(), D.ch_gr()):
  (({==}, ({==}, {==})), (({==}, ({==}, {==})), (({==}, ({==}, {==})), ({==}, ({==}, {==})))))

# In every complete ordered field there is a geometry meaning the sketch
# with A = (0, 0) and B = (4, 0). (Over ℚ there is none: P = (2, ±√5).)
def exists(~F: O.OField, ~R: CR.Complete<F>) -> &x: M.Vec(~F) -> (SK.Sketch.means(~F, x, sk()) & Pins(~F, x)):
  exists.k(~KI.dnum(), ~F, ~R, ~KI.demb(~F), D.ch_gc(), D.ch_gr(), D.ch_plan(), plan_ok(), sides_ok(), pins_ok())
