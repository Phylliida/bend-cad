# bend-cad: a regular point stays regular in the solver's block order
# (DESIGN §10.4, C2d). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/permpf.draft lib/permpf.bend
#
# Regular (spec/deriv.bend) takes the kept equations in order and the free
# variables ascending; the plan takes the equations block by block (a
# list a of indices, the same set as good) and the unknowns block by block
# (a list v, the same set as the free variables us). The Jacobian in
# block order is the other one with rows and columns permuted, so it is
# injective too: given w with J' w = 0, read w at each free variable's
# position in v (reix); each row of J times that is a row of J' times w,
# the sum taken in another order (dsum_perm), so it is 0, so the read
# vector is 0, so w is. lib/gjpf.bend then gives the inverse (inv_of_inj).

import Base
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./maxpf.bend as MX
import ./solve.bend as SO
import ../spec/sketch.bend as SK
import ./struct.bend as ST
import ./plan.bend as PL
import ./nat.bend as LN
import ./listpf.bend as L
import ./dfspf.bend as D
import ./flaws.bend as FL
import ./gjpf.bend as GJ
import ./tarjanpf.bend as TJ
import ./structpf.bend as SP
import ./keptpf.bend as KP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Removing an entry
# -----------------
# L.rem(x, ys): ys without x

def rem_sub.go(b: Bool, +x: Nat, +y: Nat, +t: List<&2, Nat>, ih: {L.subl(L.rem(x, t), t) == True{} : Bool}) -> {L.subl(L.rem.go(b, y, L.rem(x, t)), Con{y, t}) == True{} : Bool}:
  match b:
    case True{}:
      L.subl_cons_r(L.rem(x, t), y, t, ih)
    case False{}:
      L.subl_con(y, L.rem(x, t), Con{y, t}, L.mem_hd(y, t), L.subl_cons_r(L.rem(x, t), y, t, ih))

def rem_sub(+x: Nat, ys: List<&2, Nat>) -> {L.subl(L.rem(x, ys), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      rem_sub.go(SV.eq(y, x), x, y, t, rem_sub(x, t))

def rem_t.go(b: Bool, +h: Nat, +y: Nat, +t: List<&2, Nat>, +r: List<&2, Nat>, e: {SV.eq(y, h) == b : Bool}, hy: {SV.mem(y, Con{h, t}) == True{} : Bool}, ih: {L.subl(r, t) == True{} : Bool}) -> {L.subl(L.rem.go(b, y, r), t) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      L.subl_con(y, r, t, L.mem_tl_inv(y, h, t, hy, e), ih)

# ys within h :: t: ys without h is within t
def rem_t(ys: List<&2, Nat>, +h: Nat, +t: List<&2, Nat>, +hs: {L.subl(ys, Con{h, t}) == True{} : Bool}) -> {L.subl(L.rem(h, ys), t) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +u}:
      rem_t.go(SV.eq(y, h), h, y, t, L.rem(h, u), {==}, L.subl_hd(y, u, Con{h, t}, hs), rem_t(u, h, t, L.subl_tl(y, u, Con{h, t}, hs)))

def rem_dist.go(b: Bool, +x: Nat, +y: Nat, +t: List<&2, Nat>, hn: {SV.mem(y, t) == False{} : Bool}, ih: {SV.distinct(L.rem(x, t)) == True{} : Bool}) -> {SV.distinct(L.rem.go(b, y, L.rem(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      L.dist_con(y, L.rem(x, t), L.notin_subl(y, L.rem(x, t), t, hn, rem_sub(x, t)), ih)

def rem_dist(+x: Nat, ys: List<&2, Nat>, +d: {SV.distinct(ys) == True{} : Bool}) -> {SV.distinct(L.rem(x, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      rem_dist.go(SV.eq(y, x), x, y, t, L.dist_hd(y, t, d), rem_dist(x, t, L.dist_tl(y, t, d)))

# x not in ys: removing x changes nothing
def rem_notin(+x: Nat, ys: List<&2, Nat>, +h: {SV.mem(x, ys) == False{} : Bool}) -> {L.rem(x, ys) == ys : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %Equal.sym(Bool, SV.eq(y, x), False{}, TJ.ne_of_notin(y, x, t, h)) : {L.rem.go(_, y, L.rem(x, t)) == Con{y, t} : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, L.rem(x, t), t, rem_notin(x, t, L.bor_fr(SV.eq(x, y), SV.mem(x, t), h))) : {Con{y, _} == Con{y, t} : List<&2, Nat>}
      {==}

def nil_of_subl(xs: List<&2, Nat>, h: {L.subl(xs, Nil{}) == True{} : Bool}) -> {xs == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      absurd({Con{y, t} == Nil{} : List<&2, Nat>}, KA.ft(L.subl_hd(y, t, Nil{}, h)))

def notin_rw(+y: Nat, +h: Nat, +t: List<&2, Nat>, eh: {y == h : Nat}, hn: {SV.mem(y, t) == False{} : Bool}) -> {SV.mem(h, t) == False{} : Bool}:
  %eh : {SV.mem(_, t) == False{} : Bool}
  hn

# Sums over the free variables
# ----------------------------

# w read at each u's position in v
def reix(~F: O.OField, +w: M.Vec(~F), +v: List<&2, Nat>, us: List<&2, Nat>) -> M.Vec(~F):
  match us:
    case Nil{}:
      Nil{}
    case Con{+u, t}:
      Con{O.lookup(~F, w, ST.pos(u, v)), reix(~F, w, v, t)}

# d e / d x_u at x, times w at u's position in v
def dt(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, +u: Nat) -> O.C(F):
  O.mul(F, O.eval(~F, x, DV.deriv(e, u)), O.lookup(~F, w, ST.pos(u, v)))

def dsum(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, us: List<&2, Nat>) -> O.C(F):
  match us:
    case Nil{}:
      O.zero(F)
    case Con{+u, t}:
      O.add(F, dt(~F, x, e, w, v, u), dsum(~F, x, e, w, v, t))

# a row of the Jacobian in us times w read through v
def dot_reix(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, us: List<&2, Nat>) -> {M.dot(~F, DV.jrow(~F, x, e, us), reix(~F, w, v, us)) == dsum(~F, x, e, w, v, us) : O.C(F)}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      %Equal.sym(O.C(F), M.dot(~F, DV.jrow(~F, x, e, t), reix(~F, w, v, t)), dsum(~F, x, e, w, v, t), dot_reix(~F, x, e, w, v, t)) : {O.add(F, dt(~F, x, e, w, v, u), _) == O.add(F, dt(~F, x, e, w, v, u), dsum(~F, x, e, w, v, t)) : O.C(F)}
      {==}

# each picked equation's sum
def rowsum(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +w: M.Vec(~F), +v: List<&2, Nat>, +us: List<&2, Nat>, xs: List<&2, Nat>) -> M.Vec(~F):
  match xs:
    case Nil{}:
      Nil{}
    case Con{+j, t}:
      Con{dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t)}

def mv_rows(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +w: M.Vec(~F), +v: List<&2, Nat>, +us: List<&2, Nat>, xs: List<&2, Nat>) -> {M.matvec(~F, DV.jac(~F, x, KP.pickk(full, 0n, xs), us), reix(~F, w, v, us)) == rowsum(~F, x, full, w, v, us, xs) : M.Vec(~F)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(O.C(F), M.dot(~F, DV.jrow(~F, x, PL.eqget(full, j), us), reix(~F, w, v, us)), dsum(~F, x, PL.eqget(full, j), w, v, us), dot_reix(~F, x, PL.eqget(full, j), w, v, us)) : {Con{_, M.matvec(~F, DV.jac(~F, x, KP.pickk(full, 0n, t), us), reix(~F, w, v, us))} == Con{dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), M.matvec(~F, DV.jac(~F, x, KP.pickk(full, 0n, t), us), reix(~F, w, v, us)), rowsum(~F, x, full, w, v, us, t), mv_rows(~F, x, full, w, v, us, t)) : {Con{dsum(~F, x, PL.eqget(full, j), w, v, us), _} == Con{dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t)} : M.Vec(~F)}
      {==}

def dsum_rem.go(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, +y: Nat, +t: List<&2, Nat>, +h: Nat, c: Bool, ec: {SV.eq(y, h) == c : Bool}, hm: {SV.mem(h, Con{y, t}) == True{} : Bool}, hn: {SV.mem(y, t) == False{} : Bool}, ih: {SV.mem(h, t) == True{} : Bool} -> {dsum(~F, x, e, w, v, t) == O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, L.rem(h, t))) : O.C(F)}) -> {O.add(F, dt(~F, x, e, w, v, y), dsum(~F, x, e, w, v, t)) == O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, L.rem.go(c, y, L.rem(h, t)))) : O.C(F)}:
  match c:
    case True{}:
      +eh = L.eq_ok(y, h, ec)
      %Equal.sym(List<&2, Nat>, L.rem(h, t), t, rem_notin(h, t, notin_rw(y, h, t, eh, hn))) : {O.add(F, dt(~F, x, e, w, v, y), dsum(~F, x, e, w, v, t)) == O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, _)) : O.C(F)}
      %eh : {O.add(F, dt(~F, x, e, w, v, y), dsum(~F, x, e, w, v, t)) == O.add(F, dt(~F, x, e, w, v, _), dsum(~F, x, e, w, v, t)) : O.C(F)}
      {==}
    case False{}:
      +r = dsum(~F, x, e, w, v, L.rem(h, t))
      %Equal.sym(O.C(F), dsum(~F, x, e, w, v, t), O.add(F, dt(~F, x, e, w, v, h), r), ih(L.mem_tl_inv(h, y, t, hm, (%L.eq_sym(y, h) : {_ == False{} : Bool}
        ec)))) : {O.add(F, dt(~F, x, e, w, v, y), _) == O.add(F, dt(~F, x, e, w, v, h), O.add(F, dt(~F, x, e, w, v, y), r)) : O.C(F)}
      FL.add_swap(~F, dt(~F, x, e, w, v, y), dt(~F, x, e, w, v, h), r)

# h in b (distinct): the sum over b is h's term plus the sum without h
def dsum_rem(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, b: List<&2, Nat>, +h: Nat, hm: {SV.mem(h, b) == True{} : Bool}, +hd: {SV.distinct(b) == True{} : Bool}) -> {dsum(~F, x, e, w, v, b) == O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, L.rem(h, b))) : O.C(F)}:
  match b:
    case Nil{}:
      absurd({O.zero(F) == O.add(F, dt(~F, x, e, w, v, h), O.zero(F)) : O.C(F)}, KA.ft(hm))
    case Con{+y, +t}:
      dsum_rem.go(~F, x, e, w, v, y, t, h, SV.eq(y, h), {==}, hm, L.dist_hd(y, t, hd), p => dsum_rem(~F, x, e, w, v, t, h, p, L.dist_tl(y, t, hd)))

# the sum over a permutation is the same sum
def dsum_perm(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +w: M.Vec(~F), +v: List<&2, Nat>, a: List<&2, Nat>, +b: List<&2, Nat>, +hda: {SV.distinct(a) == True{} : Bool}, +hdb: {SV.distinct(b) == True{} : Bool}, +h1: {L.subl(a, b) == True{} : Bool}, +h2: {L.subl(b, a) == True{} : Bool}) -> {dsum(~F, x, e, w, v, a) == dsum(~F, x, e, w, v, b) : O.C(F)}:
  match a:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, b, Nil{}, nil_of_subl(b, h2)) : {O.zero(F) == dsum(~F, x, e, w, v, _) : O.C(F)}
      {==}
    case Con{+h, +t}:
      %Equal.sym(O.C(F), dsum(~F, x, e, w, v, b), O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, L.rem(h, b))), dsum_rem(~F, x, e, w, v, b, h, L.subl_hd(h, t, b, h1), hdb)) : {O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, t)) == _ : O.C(F)}
      %Equal.sym(O.C(F), dsum(~F, x, e, w, v, t), dsum(~F, x, e, w, v, L.rem(h, b)), dsum_perm(~F, x, e, w, v, t, L.rem(h, b), L.dist_tl(h, t, hda), rem_dist(h, b, hdb), L.subl_rem(t, h, b, L.subl_tl(h, t, b, h1), L.dist_hd(h, t, hda)), rem_t(b, h, t, h2))) : {O.add(F, dt(~F, x, e, w, v, h), _) == O.add(F, dt(~F, x, e, w, v, h), dsum(~F, x, e, w, v, L.rem(h, b))) : O.C(F)}
      {==}

# Reading through positions
# -------------------------

# v0 not among us: reading (a :: ws) through v0 :: t is reading ws through t
def reix_cons(~F: O.OField, +a: O.C(F), +ws: M.Vec(~F), +v0: Nat, +t: List<&2, Nat>, us: List<&2, Nat>, +h: {SV.mem(v0, us) == False{} : Bool}) -> {reix(~F, Con{a, ws}, Con{v0, t}, us) == reix(~F, ws, t, us) : M.Vec(~F)}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +ut}:
      %Equal.sym(Bool, KA.nateq(u, v0), False{}, TJ.ne_nateq(v0, u, L.bor_fl(SV.eq(v0, u), SV.mem(v0, ut), h))) : {Con{O.lookup(~F, Con{a, ws}, ST.pos.go(_, ST.pos(u, t))), reix(~F, Con{a, ws}, Con{v0, t}, ut)} == Con{O.lookup(~F, ws, ST.pos(u, t)), reix(~F, ws, t, ut)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), reix(~F, Con{a, ws}, Con{v0, t}, ut), reix(~F, ws, t, ut), reix_cons(~F, a, ws, v0, t, ut, L.bor_fr(SV.eq(v0, u), SV.mem(v0, ut), h))) : {Con{O.lookup(~F, ws, ST.pos(u, t)), _} == Con{O.lookup(~F, ws, ST.pos(u, t)), reix(~F, ws, t, ut)} : M.Vec(~F)}
      {==}

def len_zero(~F: O.OField, +a: O.C(F), +ws: M.Vec(~F), h: {1n+M.len(~F, ws) == 0n : Nat}) -> Empty:
  KA.ft(D.eq_of(1n+M.len(~F, ws), 0n, h))

# v distinct, w as long: reading w through v at v is w
def reix_self(~F: O.OField, w: M.Vec(~F), v: List<&2, Nat>, +hd: {SV.distinct(v) == True{} : Bool}, hl: {M.len(~F, w) == SV.len(v) : Nat}) -> {reix(~F, w, v, v) == w : M.Vec(~F)}:
  match w v:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+v0, +t}:
      absurd({reix(~F, Nil{}, Con{v0, t}, Con{v0, t}) == Nil{} : M.Vec(~F)}, KA.ft(D.eq_of(0n, 1n+SV.len(t), hl)))
    case Con{+a, +ws} Nil{}:
      absurd({Nil{} == Con{a, ws} : M.Vec(~F)}, len_zero(~F, a, ws, hl))
    case Con{+a, +ws} Con{+v0, +t}:
      %Equal.sym(Bool, KA.nateq(v0, v0), True{}, KA.nateq_refl(v0)) : {Con{O.lookup(~F, Con{a, ws}, ST.pos.go(_, ST.pos(v0, t))), reix(~F, Con{a, ws}, Con{v0, t}, t)} == Con{a, ws} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), reix(~F, Con{a, ws}, Con{v0, t}, t), reix(~F, ws, t, t), reix_cons(~F, a, ws, v0, t, t, L.dist_hd(v0, t, hd))) : {Con{a, _} == Con{a, ws} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), reix(~F, ws, t, t), ws, reix_self(~F, ws, t, L.dist_tl(v0, t, hd), LN.succ_inj(M.len(~F, ws), SV.len(t), hl))) : {Con{a, _} == Con{a, ws} : M.Vec(~F)}
      {==}

# Zero vectors
# ------------

def zs_head(~F: O.OField, +d: O.C(F), +r: M.Vec(~F), +n: Nat, e: {Con{d, r} == GJ.zeros(~F, 1n+n) : M.Vec(~F)}) -> {d == O.zero(F) : O.C(F)}:
  Equal.cong(M.Vec(~F), O.C(F), u => GJ.vhd(~F, u), Con{d, r}, GJ.zeros(~F, 1n+n), e)

def zs_tail(~F: O.OField, +d: O.C(F), +r: M.Vec(~F), +n: Nat, e: {Con{d, r} == GJ.zeros(~F, 1n+n) : M.Vec(~F)}) -> {r == GJ.zeros(~F, n) : M.Vec(~F)}:
  Equal.cong(M.Vec(~F), M.Vec(~F), u => GJ.vtl(~F, u), Con{d, r}, GJ.zeros(~F, 1n+n), e)

def rows_zero.go(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +w: M.Vec(~F), +v: List<&2, Nat>, +us: List<&2, Nat>, +j: Nat, +t: List<&2, Nat>, +y: Nat, b: Bool, eb: {SV.eq(y, j) == b : Bool}, hm: {SV.bor(b, SV.mem(y, t)) == True{} : Bool}, +h: {Con{dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t)} == GJ.zeros(~F, 1n+SV.len(t)) : M.Vec(~F)}, ih: {SV.mem(y, t) == True{} : Bool} -> {rowsum(~F, x, full, w, v, us, t) == GJ.zeros(~F, SV.len(t)) : M.Vec(~F)} -> {dsum(~F, x, PL.eqget(full, y), w, v, us) == O.zero(F) : O.C(F)}) -> {dsum(~F, x, PL.eqget(full, y), w, v, us) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, y, j, L.eq_ok(y, j, eb)) : {dsum(~F, x, PL.eqget(full, _), w, v, us) == O.zero(F) : O.C(F)}
      zs_head(~F, dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t), SV.len(t), h)
    case False{}:
      ih(hm, zs_tail(~F, dsum(~F, x, PL.eqget(full, j), w, v, us), rowsum(~F, x, full, w, v, us, t), SV.len(t), h))

# the sums of xs all 0: the sum of each y in xs is 0
def rows_zero(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +w: M.Vec(~F), +v: List<&2, Nat>, +us: List<&2, Nat>, xs: List<&2, Nat>, h: {rowsum(~F, x, full, w, v, us, xs) == GJ.zeros(~F, SV.len(xs)) : M.Vec(~F)}, +y: Nat, hm: {SV.mem(y, xs) == True{} : Bool}) -> {dsum(~F, x, PL.eqget(full, y), w, v, us) == O.zero(F) : O.C(F)}:
  match xs:
    case Nil{}:
      absurd({dsum(~F, x, PL.eqget(full, y), w, v, us) == O.zero(F) : O.C(F)}, KA.ft(hm))
    case Con{+j, +t}:
      rows_zero.go(~F, x, full, w, v, us, j, t, y, SV.eq(y, j), {==}, hm, h, p => q => rows_zero(~F, x, full, w, v, us, t, q, y, p))

def reix_zero.go(~F: O.OField, +w: M.Vec(~F), +v: List<&2, Nat>, +u: Nat, +t: List<&2, Nat>, +y: Nat, b: Bool, eb: {SV.eq(y, u) == b : Bool}, hm: {SV.bor(b, SV.mem(y, t)) == True{} : Bool}, +h: {Con{O.lookup(~F, w, ST.pos(u, v)), reix(~F, w, v, t)} == GJ.zeros(~F, 1n+SV.len(t)) : M.Vec(~F)}, ih: {SV.mem(y, t) == True{} : Bool} -> {reix(~F, w, v, t) == GJ.zeros(~F, SV.len(t)) : M.Vec(~F)} -> {O.lookup(~F, w, ST.pos(y, v)) == O.zero(F) : O.C(F)}) -> {O.lookup(~F, w, ST.pos(y, v)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, y, u, L.eq_ok(y, u, eb)) : {O.lookup(~F, w, ST.pos(_, v)) == O.zero(F) : O.C(F)}
      zs_head(~F, O.lookup(~F, w, ST.pos(u, v)), reix(~F, w, v, t), SV.len(t), h)
    case False{}:
      ih(hm, zs_tail(~F, O.lookup(~F, w, ST.pos(u, v)), reix(~F, w, v, t), SV.len(t), h))

# w read through v at us all 0: at each y in us, 0
def reix_zero(~F: O.OField, +w: M.Vec(~F), +v: List<&2, Nat>, us: List<&2, Nat>, h: {reix(~F, w, v, us) == GJ.zeros(~F, SV.len(us)) : M.Vec(~F)}, +y: Nat, hm: {SV.mem(y, us) == True{} : Bool}) -> {O.lookup(~F, w, ST.pos(y, v)) == O.zero(F) : O.C(F)}:
  match us:
    case Nil{}:
      absurd({O.lookup(~F, w, ST.pos(y, v)) == O.zero(F) : O.C(F)}, KA.ft(hm))
    case Con{+u, +t}:
      reix_zero.go(~F, w, v, u, t, y, SV.eq(y, u), {==}, hm, h, p => q => reix_zero(~F, w, v, t, q, y, p))

# the kept rows (over us) are 0 when the block rows (over v) are
def build_rows(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +w: M.Vec(~F), +vv: List<&2, Nat>, +us: List<&2, Nat>, gs: List<&2, Nat>, +a: List<&2, Nat>, +hga: {L.subl(gs, a) == True{} : Bool}, +ha: {rowsum(~F, x, full, w, vv, vv, a) == GJ.zeros(~F, SV.len(a)) : M.Vec(~F)}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}) -> {rowsum(~F, x, full, w, vv, us, gs) == GJ.zeros(~F, SV.len(gs)) : M.Vec(~F)}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +eg = PL.eqget(full, g)
      %Equal.sym(O.C(F), dsum(~F, x, eg, w, vv, us), dsum(~F, x, eg, w, vv, vv), dsum_perm(~F, x, eg, w, vv, us, vv, hdu, hdv, huv, hvu)) : {Con{_, rowsum(~F, x, full, w, vv, us, t)} == Con{O.zero(F), GJ.zeros(~F, SV.len(t))} : M.Vec(~F)}
      %Equal.sym(O.C(F), dsum(~F, x, eg, w, vv, vv), O.zero(F), rows_zero(~F, x, full, w, vv, vv, a, ha, g, L.subl_hd(g, t, a, hga))) : {Con{_, rowsum(~F, x, full, w, vv, us, t)} == Con{O.zero(F), GJ.zeros(~F, SV.len(t))} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), rowsum(~F, x, full, w, vv, us, t), GJ.zeros(~F, SV.len(t)), build_rows(~F, x, full, w, vv, us, t, a, L.subl_tl(g, t, a, hga), ha, hdu, hdv, huv, hvu)) : {Con{O.zero(F), _} == Con{O.zero(F), GJ.zeros(~F, SV.len(t))} : M.Vec(~F)}
      {==}

# w read through v at us all 0, ws within us: w read at ws all 0
def build_reix(~F: O.OField, +w: M.Vec(~F), +vv: List<&2, Nat>, +us: List<&2, Nat>, ws: List<&2, Nat>, +hws: {L.subl(ws, us) == True{} : Bool}, +h: {reix(~F, w, vv, us) == GJ.zeros(~F, SV.len(us)) : M.Vec(~F)}) -> {reix(~F, w, vv, ws) == GJ.zeros(~F, SV.len(ws)) : M.Vec(~F)}:
  match ws:
    case Nil{}:
      {==}
    case Con{+v0, +t}:
      %Equal.sym(O.C(F), O.lookup(~F, w, ST.pos(v0, vv)), O.zero(F), reix_zero(~F, w, vv, us, h, v0, L.subl_hd(v0, t, us, hws))) : {Con{_, reix(~F, w, vv, t)} == Con{O.zero(F), GJ.zeros(~F, SV.len(t))} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), reix(~F, w, vv, t), GJ.zeros(~F, SV.len(t)), build_reix(~F, w, vv, us, t, L.subl_tl(v0, t, us, hws), h)) : {Con{O.zero(F), _} == Con{O.zero(F), GJ.zeros(~F, SV.len(t))} : M.Vec(~F)}
      {==}

# Lengths
# -------

def jrow_len(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, us: List<&2, Nat>) -> {M.len(~F, DV.jrow(~F, x, e, us)) == SV.len(us) : Nat}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      %Equal.sym(Nat, M.len(~F, DV.jrow(~F, x, e, t)), SV.len(t), jrow_len(~F, x, e, t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def rl_jac(~F: O.OField, +x: M.Vec(~F), es: List<&2, E.QExpr>, +us: List<&2, Nat>) -> GJ.rl(~F, DV.jac(~F, x, es, us), SV.len(us)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (jrow_len(~F, x, e, us), rl_jac(~F, x, t, us))

def nrows_pick(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, xs: List<&2, Nat>, +us: List<&2, Nat>) -> {GJ.nrows(~F, DV.jac(~F, x, KP.pickk(full, 0n, xs), us)) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Nat, GJ.nrows(~F, DV.jac(~F, x, KP.pickk(full, 0n, t), us)), SV.len(t), nrows_pick(~F, x, full, t, us)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def elen_pick(+full: List<&2, E.QExpr>, xs: List<&2, Nat>) -> {DV.elen(KP.pickk(full, 0n, xs)) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(Nat, DV.elen(KP.pickk(full, 0n, t)), SV.len(t), elen_pick(full, t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def nlen_sv(xs: List<&2, Nat>) -> {DV.nlen(xs) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, DV.nlen(t), SV.len(t), nlen_sv(t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def len_reix(~F: O.OField, +w: M.Vec(~F), +v: List<&2, Nat>, us: List<&2, Nat>) -> {M.len(~F, reix(~F, w, v, us)) == SV.len(us) : Nat}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      %Equal.sym(Nat, M.len(~F, reix(~F, w, v, t)), SV.len(t), len_reix(~F, w, v, t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

def zs_rw(~F: O.OField, +v: M.Vec(~F), +n1: Nat, +n2: Nat, en: {n1 == n2 : Nat}, h: {v == GJ.zeros(~F, n1) : M.Vec(~F)}) -> {v == GJ.zeros(~F, n2) : M.Vec(~F)}:
  %en : {v == GJ.zeros(~F, _) : M.Vec(~F)}
  h

# The block order
# ---------------

def e2_of(~F: O.OField, +m: M.Mat(~F), +w: M.Vec(~F), +r: M.Vec(~F), +z: M.Vec(~F), hr: {r == w : M.Vec(~F)}, e: {M.matvec(~F, m, w) == z : M.Vec(~F)}) -> {M.matvec(~F, m, r) == z : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), r, w, hr) : {M.matvec(~F, m, _) == z : M.Vec(~F)}
  e

# a kernel vector of the block-order Jacobian is 0
def perm_inj(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +a: List<&2, Nat>, +us: List<&2, Nat>, +vv: List<&2, Nat>, +hga: {L.subl(good, a) == True{} : Bool}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}, +hn: {SV.len(a) == SV.len(vv) : Nat}, +y: M.Mat(~F), +hy: DV.MEq(~F, M.matmul(~F, y, DV.jac(~F, x, KP.pickk(full, 0n, good), us)), M.ident(~F, DV.nlen(us)), DV.nlen(us), 0n, DV.nlen(us)), +hrn: {DV.nlen(us) == DV.elen(KP.pickk(full, 0n, good)) : Nat}, +w: M.Vec(~F), lw: {M.len(~F, w) == SV.len(vv) : Nat}, e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(full, 0n, a), vv), w) == GJ.zeros(~F, SV.len(vv)) : M.Vec(~F)}) -> {w == GJ.zeros(~F, SV.len(vv)) : M.Vec(~F)}:
  +jp = DV.jac(~F, x, KP.pickk(full, 0n, a), vv)
  +j0 = DV.jac(~F, x, KP.pickk(full, 0n, good), us)
  +rv = reix(~F, w, vv, vv)
  +ru = reix(~F, w, vv, us)
  +nu = DV.nlen(us)
  +hself = reix_self(~F, w, vv, hdv, lw)
  +e2 = e2_of(~F, jp, w, rv, GJ.zeros(~F, SV.len(vv)), hself, e)
  +e3 = Equal.trans(M.Vec(~F), rowsum(~F, x, full, w, vv, vv, a), M.matvec(~F, jp, rv), GJ.zeros(~F, SV.len(vv)), Equal.sym(M.Vec(~F), M.matvec(~F, jp, rv), rowsum(~F, x, full, w, vv, vv, a), mv_rows(~F, x, full, w, vv, vv, a)), e2)
  +e4 = zs_rw(~F, rowsum(~F, x, full, w, vv, vv, a), SV.len(vv), SV.len(a), Equal.sym(Nat, SV.len(a), SV.len(vv), hn), e3)
  +e5 = build_rows(~F, x, full, w, vv, us, good, a, hga, e4, hdu, hdv, huv, hvu)
  +e6 = Equal.trans(M.Vec(~F), M.matvec(~F, j0, ru), rowsum(~F, x, full, w, vv, us, good), GJ.zeros(~F, SV.len(good)), mv_rows(~F, x, full, w, vv, us, good), e5)
  +lgn = Equal.trans(Nat, SV.len(good), DV.elen(KP.pickk(full, 0n, good)), nu, Equal.sym(Nat, DV.elen(KP.pickk(full, 0n, good)), SV.len(good), elen_pick(full, good)), Equal.sym(Nat, nu, DV.elen(KP.pickk(full, 0n, good)), hrn))
  +lru = Equal.trans(Nat, M.len(~F, ru), SV.len(us), nu, len_reix(~F, w, vv, us), Equal.sym(Nat, nu, SV.len(us), nlen_sv(us)))
  +e7 = GJ.inj_of_left(~F, j0, y, nu, hy, ru, lru, zs_rw(~F, M.matvec(~F, j0, ru), SV.len(good), nu, lgn, e6))
  +e8 = zs_rw(~F, ru, nu, SV.len(us), nlen_sv(us), e7)
  Equal.trans(M.Vec(~F), w, rv, GJ.zeros(~F, SV.len(vv)), Equal.sym(M.Vec(~F), rv, w, hself), build_reix(~F, w, vv, us, vv, hvu, e8))

def perm_inv.fin(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +a: List<&2, Nat>, +us: List<&2, Nat>, +vv: List<&2, Nat>, +hga: {L.subl(good, a) == True{} : Bool}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}, +hn: {SV.len(a) == SV.len(vv) : Nat}, +hrn: {DV.nlen(us) == DV.elen(KP.pickk(full, 0n, good)) : Nat}, +y: M.Mat(~F), +hy: DV.MEq(~F, M.matmul(~F, y, DV.jac(~F, x, KP.pickk(full, 0n, good), us)), M.ident(~F, DV.nlen(us)), DV.nlen(us), 0n, DV.nlen(us))) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, a), vv), SV.len(vv)):
  +jp = DV.jac(~F, x, KP.pickk(full, 0n, a), vv)
  +ha = Equal.trans(Nat, GJ.nrows(~F, jp), SV.len(a), SV.len(vv), nrows_pick(~F, x, full, a, vv), hn)
  GJ.inv_of_inj(~F, jp, SV.len(vv), ha, GJ.rl_all(~F, jp, SV.len(vv), ha, rl_jac(~F, x, KP.pickk(full, 0n, a), vv)), w => lw => e => perm_inj(~F, x, full, good, a, us, vv, hga, hdu, hdv, huv, hvu, hn, y, hy, hrn, w, lw, e))

def perm_inv.y(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +a: List<&2, Nat>, +us: List<&2, Nat>, +vv: List<&2, Nat>, +hga: {L.subl(good, a) == True{} : Bool}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}, +hn: {SV.len(a) == SV.len(vv) : Nat}, +hrn: {DV.nlen(us) == DV.elen(KP.pickk(full, 0n, good)) : Nat}, +y: M.Mat(~F), hinv: DV.Inverse(~F, DV.jac(~F, x, KP.pickk(full, 0n, good), us), y, DV.nlen(us))) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, a), vv), SV.len(vv)):
  match hinv:
    case (h1, h2):
      perm_inv.fin(~F, x, full, good, a, us, vv, hga, hdu, hdv, huv, hvu, hn, hrn, y, h2)

def perm_inv.s(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +a: List<&2, Nat>, +us: List<&2, Nat>, +vv: List<&2, Nat>, +hga: {L.subl(good, a) == True{} : Bool}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}, +hn: {SV.len(a) == SV.len(vv) : Nat}, +hrn: {DV.nlen(us) == DV.elen(KP.pickk(full, 0n, good)) : Nat}, sy: Sigma<&2, &2, M.Mat(~F), y => DV.Inverse(~F, DV.jac(~F, x, KP.pickk(full, 0n, good), us), y, DV.nlen(us))>) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, a), vv), SV.len(vv)):
  match sy:
    case (y, hinv):
      perm_inv.y(~F, x, full, good, a, us, vv, hga, hdu, hdv, huv, hvu, hn, hrn, y, hinv)

# Regular at the kept equations (picked at good) in the free variables us
# gives the Jacobian with rows picked at a (good within it) and columns v
# (the same set as us) an inverse with |v| rows
def perm_inv(~F: O.OField, +x: M.Vec(~F), +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +a: List<&2, Nat>, +us: List<&2, Nat>, +vv: List<&2, Nat>, +hga: {L.subl(good, a) == True{} : Bool}, +hdu: {SV.distinct(us) == True{} : Bool}, +hdv: {SV.distinct(vv) == True{} : Bool}, +huv: {L.subl(us, vv) == True{} : Bool}, +hvu: {L.subl(vv, us) == True{} : Bool}, +hn: {SV.len(a) == SV.len(vv) : Nat}, hreg: DV.Regular(~F, x, KP.pickk(full, 0n, good), us)) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, a), vv), SV.len(vv)):
  match hreg:
    case (hrn, sy):
      perm_inv.s(~F, x, full, good, a, us, vv, hga, hdu, hdv, huv, hvu, hn, hrn, sy)

# The free variables
# ------------------
# SV.free(n, k, pins): k .. k + n - 1 less pins, ascending

def fgo_mem(b: Bool, +k: Nat, +r: List<&2, Nat>, +u: Nat, h: {SV.mem(u, r) == True{} : Bool}) -> {SV.mem(u, SV.free.go(b, k, r)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.mem_tl(u, k, r, h)

def fge_k(c: Bool, +k: Nat, +u: Nat, +r: List<&2, Nat>, e: {SV.eq(u, k) == c : Bool}, h: {SV.bor(c, SV.mem(u, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {KA.natle(1n+k, u) == True{} : Bool}) -> {KA.natle(k, u) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, u, k, L.eq_ok(u, k, e)) : {KA.natle(k, _) == True{} : Bool}
      KA.natle_refl(k)
    case False{}:
      KA.natle_pred(k, u, ih(h))

def fge_b(b: Bool, +k: Nat, +u: Nat, +r: List<&2, Nat>, h: {SV.mem(u, SV.free.go(b, k, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {KA.natle(1n+k, u) == True{} : Bool}) -> {KA.natle(k, u) == True{} : Bool}:
  match b:
    case True{}:
      KA.natle_pred(k, u, ih(h))
    case False{}:
      fge_k(SV.eq(u, k), k, u, r, {==}, h, ih)

# entries of free(n, k, pins) are at least k
def free_ge(n: Nat, +k: Nat, +pins: List<&2, Nat>, +u: Nat, h: {SV.mem(u, SV.free(n, k, pins)) == True{} : Bool}) -> {KA.natle(k, u) == True{} : Bool}:
  match n:
    case 0n:
      absurd({KA.natle(k, u) == True{} : Bool}, KA.ft(h))
    case 1n++m:
      fge_b(SV.mem(k, pins), k, u, SV.free(m, 1n+k, pins), h, p => free_ge(m, 1n+k, pins, u, p))

def flt_k(c: Bool, +k: Nat, +m: Nat, +u: Nat, +r: List<&2, Nat>, e: {SV.eq(u, k) == c : Bool}, h: {SV.bor(c, SV.mem(u, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {KA.natle(1n+u, 1n+Nat.add(k, m)) == True{} : Bool}) -> {KA.natle(1n+u, 1n+Nat.add(k, m)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, u, k, L.eq_ok(u, k, e)) : {KA.natle(1n+_, 1n+Nat.add(k, m)) == True{} : Bool}
      KA.natle_add_r(k, m)
    case False{}:
      ih(h)

def flt_b(b: Bool, +k: Nat, +m: Nat, +u: Nat, +r: List<&2, Nat>, h: {SV.mem(u, SV.free.go(b, k, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {KA.natle(1n+u, 1n+Nat.add(k, m)) == True{} : Bool}) -> {KA.natle(1n+u, 1n+Nat.add(k, m)) == True{} : Bool}:
  match b:
    case True{}:
      ih(h)
    case False{}:
      flt_k(SV.eq(u, k), k, m, u, r, {==}, h, ih)

# entries of free(n, k, pins) are below k + n
def free_lt(n: Nat, +k: Nat, +pins: List<&2, Nat>, +u: Nat, h: {SV.mem(u, SV.free(n, k, pins)) == True{} : Bool}) -> {KA.natle(1n+u, Nat.add(k, n)) == True{} : Bool}:
  match n:
    case 0n:
      absurd({KA.natle(1n+u, Nat.add(k, 0n)) == True{} : Bool}, KA.ft(h))
    case 1n++m:
      %LN.add_succ(k, m) : {KA.natle(1n+u, _) == True{} : Bool}
      flt_b(SV.mem(k, pins), k, m, u, SV.free(m, 1n+k, pins), h, p => free_lt(m, 1n+k, pins, u, p))

def fnp_k(c: Bool, +k: Nat, +u: Nat, +r: List<&2, Nat>, +pins: List<&2, Nat>, e: {SV.eq(u, k) == c : Bool}, hk: {SV.mem(k, pins) == False{} : Bool}, h: {SV.bor(c, SV.mem(u, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {SV.mem(u, pins) == False{} : Bool}) -> {SV.mem(u, pins) == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, u, k, L.eq_ok(u, k, e)) : {SV.mem(_, pins) == False{} : Bool}
      hk
    case False{}:
      ih(h)

def fnp_b(b: Bool, +k: Nat, +u: Nat, +r: List<&2, Nat>, +pins: List<&2, Nat>, eb: {SV.mem(k, pins) == b : Bool}, h: {SV.mem(u, SV.free.go(b, k, r)) == True{} : Bool}, ih: {SV.mem(u, r) == True{} : Bool} -> {SV.mem(u, pins) == False{} : Bool}) -> {SV.mem(u, pins) == False{} : Bool}:
  match b:
    case True{}:
      ih(h)
    case False{}:
      fnp_k(SV.eq(u, k), k, u, r, pins, {==}, eb, h, ih)

# entries of free(n, k, pins) are not pins
def free_np(n: Nat, +k: Nat, +pins: List<&2, Nat>, +u: Nat, h: {SV.mem(u, SV.free(n, k, pins)) == True{} : Bool}) -> {SV.mem(u, pins) == False{} : Bool}:
  match n:
    case 0n:
      absurd({SV.mem(u, pins) == False{} : Bool}, KA.ft(h))
    case 1n++m:
      fnp_b(SV.mem(k, pins), k, u, SV.free(m, 1n+k, pins), pins, {==}, h, p => free_np(m, 1n+k, pins, u, p))

def free_new(m: Nat, +k: Nat, +pins: List<&2, Nat>, c: Bool, e: {SV.mem(k, SV.free(m, 1n+k, pins)) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.natlt_irr(k, free_ge(m, 1n+k, pins, k, e)))
    case False{}:
      {==}

def fdist_b(b: Bool, +k: Nat, +r: List<&2, Nat>, hn: {SV.mem(k, r) == False{} : Bool}, h: {SV.distinct(r) == True{} : Bool}) -> {SV.distinct(SV.free.go(b, k, r)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.dist_con(k, r, hn, h)

def free_dist(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {SV.distinct(SV.free(n, k, pins)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      fdist_b(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), free_new(m, k, pins, SV.mem(k, SV.free(m, 1n+k, pins)), {==}), free_dist(m, 1n+k, pins))

def fmem_k(c: Bool, +k: Nat, +u: Nat, +r: List<&2, Nat>, +pins: List<&2, Nat>, e: {SV.eq(u, k) == c : Bool}, hn: {SV.mem(u, pins) == False{} : Bool}, ih: {SV.eq(u, k) == False{} : Bool} -> {SV.mem(u, r) == True{} : Bool}) -> {SV.mem(u, SV.free.go(SV.mem(k, pins), k, r)) == True{} : Bool}:
  match c:
    case True{}:
      +ek = L.eq_ok(u, k, e)
      %Equal.sym(Bool, SV.mem(k, pins), False{}, (%ek : {SV.mem(_, pins) == False{} : Bool}
        hn)) : {SV.mem(u, SV.free.go(_, k, r)) == True{} : Bool}
      %Equal.sym(Nat, u, k, ek) : {SV.mem(_, Con{k, r}) == True{} : Bool}
      L.mem_hd(k, r)
    case False{}:
      fgo_mem(SV.mem(k, pins), k, r, u, ih(e))

def fmem_add(+k: Nat, +m: Nat, +u: Nat, h: {KA.natle(1n+u, Nat.add(k, 1n+m)) == True{} : Bool}) -> {KA.natle(1n+u, Nat.add(1n+k, m)) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(k, m), Nat.add(k, 1n+m), LN.add_succ(k, m)) : {KA.natle(1n+u, _) == True{} : Bool}
  h

def fmem_zero(+k: Nat, +u: Nat, h1: {KA.natle(k, u) == True{} : Bool}, h2: {KA.natle(1n+u, Nat.add(k, 0n)) == True{} : Bool}) -> Empty:
  KA.natlt_irr(u, KA.natle_trans(1n+u, k, u, (%Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : {KA.natle(1n+u, _) == True{} : Bool}
    h2), h1))

# k <= u < k + n, u not a pin: u is free
def free_mem(n: Nat, +k: Nat, +pins: List<&2, Nat>, +u: Nat, +h1: {KA.natle(k, u) == True{} : Bool}, +h2: {KA.natle(1n+u, Nat.add(k, n)) == True{} : Bool}, +hn: {SV.mem(u, pins) == False{} : Bool}) -> {SV.mem(u, SV.free(n, k, pins)) == True{} : Bool}:
  match n:
    case 0n:
      absurd({SV.mem(u, Nil{}) == True{} : Bool}, fmem_zero(k, u, h1, h2))
    case 1n++m:
      fmem_k(SV.eq(u, k), k, u, SV.free(m, 1n+k, pins), pins, {==}, hn, q => free_mem(m, 1n+k, pins, u, TJ.lt_of_ne(k, u, h1, (%L.eq_sym(u, k) : {_ == False{} : Bool}
        q)), fmem_add(k, m, u, h2), hn))

# The solver's blocks
# -------------------

def dist_app_r(a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.distinct(ST.app(a, b)) == True{} : Bool}) -> {SV.distinct(b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      dist_app_r(t, b, L.dist_tl(x, ST.app(t, b), h))

# xs and ys disjoint, v in ys: v not in xs
def disj_flip(xs: List<&2, Nat>, +ys: List<&2, Nat>, +v: Nat, +hd: {MX.disj(xs, ys) == True{} : Bool}, +hm: {SV.mem(v, ys) == True{} : Bool}) -> {SV.mem(v, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.bor_f(SV.eq(v, x), SV.mem(v, t), L.mem_ne(v, x, ys, hm, MX.disj_hd(x, t, ys, hd)), disj_flip(t, ys, v, MX.disj_tl(x, t, ys, hd), hm))

def len_vars(+vm: List<&2, Maybe<&2, Nat>>, +bs: List<&2, ST.SB>, h: {SP.lkb(vm, bs) == True{} : Bool}) -> {SV.len(ST.alleqs(bs)) == SV.len(ST.allvars(bs)) : Nat}:
  %Equal.sym(List<&2, Nat>, ST.allvars(bs), ST.look(vm, ST.alleqs(bs)), SP.lkb_vars(vm, bs, h)) : {SV.len(ST.alleqs(bs)) == SV.len(_) : Nat}
  Equal.sym(Nat, SV.len(ST.look(vm, ST.alleqs(bs))), SV.len(ST.alleqs(bs)), L.look_len(vm, ST.alleqs(bs)))

def mem_vars(+vm: List<&2, Maybe<&2, Nat>>, +bs: List<&2, ST.SB>, +u: Nat, h: {SP.lkb(vm, bs) == True{} : Bool}, hm: {SV.mem(u, ST.look(vm, ST.alleqs(bs))) == True{} : Bool}) -> {SV.mem(u, ST.allvars(bs)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, ST.allvars(bs), ST.look(vm, ST.alleqs(bs)), SP.lkb_vars(vm, bs, h)) : {SV.mem(u, _) == True{} : Bool}
  hm

def vars_mem(+vm: List<&2, Maybe<&2, Nat>>, +bs: List<&2, ST.SB>, +u: Nat, h: {SP.lkb(vm, bs) == True{} : Bool}, hm: {SV.mem(u, ST.allvars(bs)) == True{} : Bool}) -> {SV.mem(u, ST.look(vm, ST.alleqs(bs))) == True{} : Bool}:
  %SP.lkb_vars(vm, bs, h) : {SV.mem(u, _) == True{} : Bool}
  hm

# each free variable is a block unknown
def huv_go(ws: List<&2, Nat>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, +hws: {L.subl(ws, SV.free(nv, 0n, fs)) == True{} : Bool}, +hv: {SP.vside(nq, nv, good, vm, fs) == True{} : Bool}, +hga: {L.subl(good, ST.alleqs(bs)) == True{} : Bool}, +hlk: {SP.lkb(vm, bs) == True{} : Bool}) -> {L.subl(ws, ST.allvars(bs)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +hu = L.subl_hd(u, t, SV.free(nv, 0n, fs), hws)
      +hin = L.subl_mem(u, ST.down(nv), ST.app(fs, ST.somes(vm)), SP.mem_down(u, nv, free_lt(nv, 0n, fs, u, hu)), SP.vside_all(nq, nv, good, vm, fs, hv))
      +hs = SP.app_r_of(u, fs, ST.somes(vm), hin, free_np(nv, 0n, fs, u, hu))
      +hl = L.subl_mem(u, ST.look(vm, good), ST.look(vm, ST.alleqs(bs)), L.subl_mem(u, ST.somes(vm), ST.look(vm, good), hs, SP.vs_look(nq, nv, good, vm, fs, hv)), SP.look_mono(vm, good, ST.alleqs(bs), hga))
      L.subl_con(u, t, ST.allvars(bs), mem_vars(vm, bs, u, hlk, hl), huv_go(t, nq, nv, good, vm, fs, bs, L.subl_tl(u, t, SV.free(nv, 0n, fs), hws), hv, hga, hlk))

# each block unknown is a free variable
def hvu_go(ws: List<&2, Nat>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +bs: List<&2, ST.SB>, +hws: {L.subl(ws, ST.allvars(bs)) == True{} : Bool}, +hv: {SP.vside(nq, nv, good, vm, fs) == True{} : Bool}, +hag: {L.subl(ST.alleqs(bs), good) == True{} : Bool}, +hlk: {SP.lkb(vm, bs) == True{} : Bool}) -> {L.subl(ws, SV.free(nv, 0n, fs)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +hs = L.subl_mem(u, ST.look(vm, ST.alleqs(bs)), ST.somes(vm), vars_mem(vm, bs, u, hlk, L.subl_hd(u, t, ST.allvars(bs), hws)), L.look_subl(vm, ST.alleqs(bs), SP.allm_subl(ST.alleqs(bs), good, vm, hag, SP.vs_sat(nq, nv, good, vm, fs, hv))))
      +hb = D.below_mem(u, ST.down(nv), nv, L.subl_mem(u, ST.somes(vm), ST.down(nv), hs, SP.vside_mb(nq, nv, good, vm, fs, hv)), MX.down_below(nv))
      L.subl_con(u, t, SV.free(nv, 0n, fs), free_mem(nv, 0n, fs, u, {==}, MX.lt_nat(u, nv, hb), disj_flip(fs, ST.somes(vm), u, SP.vside_ff(nq, nv, good, vm, fs, hv), hs)), hvu_go(t, nq, nv, good, vm, fs, bs, L.subl_tl(u, t, ST.allvars(bs), hws), hv, hag, hlk))

def reg_go(~F: O.OField, +full: List<&2, E.QExpr>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, +x: M.Vec(~F), +hv: {SP.vside(nq, nv, good, vm, fs) == True{} : Bool}, +hs: {SP.skok(full, nv, good, vm, fs, SP.kblocks(ST.adj(full), nq, nv, good, vm, fs)) == True{} : Bool}, hr: DV.Regular(~F, x, KP.pickk(full, 0n, good), SV.free(nv, 0n, fs))) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, ST.alleqs(SP.kblocks(ST.adj(full), nq, nv, good, vm, fs))), ST.allvars(SP.kblocks(ST.adj(full), nq, nv, good, vm, fs))), SV.len(ST.allvars(SP.kblocks(ST.adj(full), nq, nv, good, vm, fs)))):
  +adj = ST.adj(full)
  +bs = SP.kblocks(adj, nq, nv, good, vm, fs)
  +sf = SP.skok_sf(full, nv, good, vm, fs, bs, hs)
  +hga = SP.sfacts_cg(adj, nv, good, vm, fs, bs, sf)
  +hag = SP.sfacts_gc(adj, nv, good, vm, fs, bs, sf)
  +hlk = SP.sfacts_lk(adj, nv, good, vm, fs, bs, sf)
  +us = SV.free(nv, 0n, fs)
  perm_inv(~F, x, full, good, ST.alleqs(bs), us, ST.allvars(bs), hga, free_dist(nv, 0n, fs), dist_app_r(fs, ST.allvars(bs), SP.sfacts_vpd(adj, nv, good, vm, fs, bs, sf)), huv_go(us, nq, nv, good, vm, fs, bs, L.subl_refl(us), hv, hga, hlk), hvu_go(ST.allvars(bs), nq, nv, good, vm, fs, bs, L.subl_refl(ST.allvars(bs)), hv, hag, hlk), len_vars(vm, bs, hlk), hr)

def reg_kd(~F: O.OField, kd: ST.KD, +full: List<&2, E.QExpr>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +x: M.Vec(~F), hv: {SP.vsides(nq, nv, good, kd) == True{} : Bool}, hs: {SP.skok(full, nv, good, ST.KD.vm(kd), ST.KD.red(kd), SP.kblocks(ST.adj(full), nq, nv, good, ST.KD.vm(kd), ST.KD.red(kd))) == True{} : Bool}, hr: DV.Regular(~F, x, KP.pickk(full, 0n, good), SV.free(nv, 0n, ST.KD.red(kd)))) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, ST.alleqs(SP.kblocks(ST.adj(full), nq, nv, good, ST.KD.vm(kd), ST.KD.red(kd)))), ST.allvars(SP.kblocks(ST.adj(full), nq, nv, good, ST.KD.vm(kd), ST.KD.red(kd)))), SV.len(ST.allvars(SP.kblocks(ST.adj(full), nq, nv, good, ST.KD.vm(kd), ST.KD.red(kd))))):
  match kd:
    case ST.KD{+vm, +fs, dd}:
      reg_go(~F, full, nq, nv, good, vm, fs, x, hv, hs, hr)

# a regular point of the kept system (in the free variables the solver
# chose) has the Jacobian in the solver's block order invertible: rows the
# kept equations block by block, columns the blocks' unknowns
def regular_blocks(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SO.kept(sk), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(SK.Sketch.eqs(sk), 0n, ST.alleqs(SP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk)))))), ST.allvars(SP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk)))))), SV.len(ST.allvars(SP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))))))):
  +full = SK.Sketch.eqs(sk)
  +nq = ST.len.q(full)
  +nv = SO.nvars(sk)
  +good = SO.good_of(sk)
  +kdv = MX.kvs(ST.adj(full), nq, nv, good)
  reg_kd(~F, kdv, full, nq, nv, good, x, SP.vend(sk, ha), SP.struct_ok(sk, ha), (%KP.kept_good(sk, ha) : DV.Regular(~F, x, _, SV.free(nv, 0n, ST.KD.red(kdv)))
    (%MX.pins_red(sk) : DV.Regular(~F, x, SO.kept(sk), SV.free(nv, 0n, _))
      hr)))
