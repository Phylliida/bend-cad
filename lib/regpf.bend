# bend-cad: law 2, solve_regular (PLAN-sk13a S5): the certified geometry
# is a regular point of the system solved, in the free variables. Proofs
# only.
# Generated: python3 tools/expand.py tools/drafts/regpf.draft lib/regpf.bend
#
# Each block's certificate makes the block's Jacobian injective anywhere
# in its box (lib/certpf.bend: cert_jinj, the inclusion theorem; locally
# by lib/locpf.bend's jac_loc). A block's equations read only the pins,
# earlier unknowns and its own, so from each block on the Jacobian of the
# rest of the system in block order is [[A, 0], [C, D]] (lib/binvpf.bend)
# and injective by forward substitution (bm_inj). The plan's orders are
# exactly the solved equations and the free variables (the verdict checks
# it), so the Jacobian in the sketch's order has an inverse too
# (lib/permpf.bend: perm_inv). The law reads the plan and its shape off
# a True verdict (lib/solvepf.bend: hD, hS).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/box.bend as BX
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ./karith.bend as KA
import ./kball.bend as KB
import ./kinst.bend as KI
import ./certdef.bend as C
import ./cert.bend as CK
import ./certpf.bend as CP
import ./struct.bend as ST
import ./plan.bend as PL
import ./planpf.bend as PP
import ./locpf.bend as LC
import ./apxpf.bend as AP
import ./gjpf.bend as GJ
import ./binvpf.bend as BI
import ./permpf.bend as PM
import ./keptpf.bend as KP
import ./listpf.bend as L
import ./nat.bend as LN
import ./fring.bend as FR
import ./ford.bend as FO
import ./fvec.bend as FV
import ./slope.bend as SL
import ./solve.bend as SO
import ./ownpf.bend as OW
import ./pblkpf.bend as PB
import ./maxpf.bend as MX
import ./tarjanpf.bend as TJ
import ./perfpf.bend as PF
import ./solvepf.bend as SPF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Vectors
# -------

def vtd(~F: O.OField, k: Nat, y: M.Vec(~F)) -> {GJ.vapp(~F, GJ.vtake(~F, k, y), GJ.vdrop(~F, k, y)) == y : M.Vec(~F)}:
  match k y:
    case 0n y:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{+a, +t}:
      %Equal.sym(M.Vec(~F), GJ.vapp(~F, GJ.vtake(~F, j, t), GJ.vdrop(~F, j, t)), t, vtd(~F, j, t)) : {Con{a, _} == Con{a, t} : M.Vec(~F)}
      {==}

def len_vdrop(~F: O.OField, k: Nat, y: M.Vec(~F), +n: Nat, h: {M.len(~F, y) == Nat.add(k, n) : Nat}) -> {M.len(~F, GJ.vdrop(~F, k, y)) == n : Nat}:
  match k y:
    case 0n y:
      h
    case 1n+j Nil{}:
      absurd({M.len(~F, GJ.vdrop(~F, 1n+j, Nil{})) == n : Nat}, FV.zero_ne(Nat.add(j, n), h))
    case 1n++j Con{a, +t}:
      len_vdrop(~F, j, t, n, LN.succ_inj(M.len(~F, t), Nat.add(j, n), h))

def natle_addr(+a: Nat, +b: Nat) -> {KA.natle(a, Nat.add(a, b)) == True{} : Bool}:
  KA.natle_add_r(a, b)

# 0 + u = u
def vadd_zl(~F: O.OField, u: M.Vec(~F), +n: Nat, h: {M.len(~F, u) == n : Nat}) -> {M.vadd(~F, GJ.zeros(~F, n), u) == u : M.Vec(~F)}:
  match u n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      absurd({M.vadd(~F, GJ.zeros(~F, 1n+k), Nil{}) == Nil{} : M.Vec(~F)}, FV.zero_ne(k, h))
    case Con{+a, +t} 0n:
      absurd({M.vadd(~F, GJ.zeros(~F, 0n), Con{a, t}) == Con{a, t} : M.Vec(~F)}, FV.succ_ne(M.len(~F, t), h))
    case Con{+a, +t} 1n+k:
      %Equal.sym(M.Vec(~F), M.vadd(~F, GJ.zeros(~F, k), t), t, vadd_zl(~F, t, k, LN.succ_inj(M.len(~F, t), k, h))) : {Con{O.add(F, O.zero(F), a), _} == Con{a, t} : M.Vec(~F)}
      %FR.fring_eq(~F, [a], E.ZVar{0n}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, {==}) : {Con{_, t} == Con{a, t} : M.Vec(~F)}
      {==}

# Block matrices, forward
# -----------------------


# the block matrix times v, split at n1
def bm_split(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, +v1: M.Vec(~F), +v2: M.Vec(~F), +l1: {M.len(~F, v1) == n1 : Nat}, +e: {M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), GJ.vapp(~F, v1, v2)) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}) -> {GJ.vapp(~F, M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)), M.vadd(~F, M.matvec(~F, c, v1), M.matvec(~F, d, v2))) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), GJ.vapp(~F, M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)), M.vadd(~F, M.matvec(~F, c, v1), M.matvec(~F, d, v2))), M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), GJ.vapp(~F, v1, v2)), GJ.mv_block(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, v1, v2, l1)) : {_ == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}
  e

# A v1 = 0
def bm_top(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, +v1: M.Vec(~F), +v2: M.Vec(~F), +h: {M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)) == GJ.zeros(~F, n1) : M.Vec(~F)}) -> {M.matvec(~F, a, v1) == GJ.zeros(~F, n1) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), M.matvec(~F, a, v1), M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)), GJ.vadd_zeros(~F, M.matvec(~F, a, v1), n1, GJ.len_mv(~F, a, n1, v1, sa))) : {_ == GJ.zeros(~F, n1) : M.Vec(~F)}
  h

# D v2 = 0, given v1 = 0
def bm_bot(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, +v1: M.Vec(~F), +v2: M.Vec(~F), +z1: {v1 == GJ.zeros(~F, n1) : M.Vec(~F)}, +h: {M.vadd(~F, M.matvec(~F, c, v1), M.matvec(~F, d, v2)) == GJ.zeros(~F, n2) : M.Vec(~F)}) -> {M.matvec(~F, d, v2) == GJ.zeros(~F, n2) : M.Vec(~F)}:
  %vadd_zl(~F, M.matvec(~F, d, v2), n2, GJ.len_mv(~F, d, n2, v2, sd)) : {_ == GJ.zeros(~F, n2) : M.Vec(~F)}
  %sc : {M.vadd(~F, GJ.zeros(~F, _), M.matvec(~F, d, v2)) == GJ.zeros(~F, n2) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), GJ.zeros(~F, GJ.nrows(~F, c)), M.matvec(~F, c, GJ.zeros(~F, n1)), GJ.matvec_zeros(~F, c, n1)) : {M.vadd(~F, _, M.matvec(~F, d, v2)) == GJ.zeros(~F, n2) : M.Vec(~F)}
  (%z1 : {M.vadd(~F, M.matvec(~F, c, _), M.matvec(~F, d, v2)) == GJ.zeros(~F, n2) : M.Vec(~F)}
    h)

def vz_join(~F: O.OField, +v: M.Vec(~F), +n1: Nat, +n2: Nat, +z1: {GJ.vtake(~F, n1, v) == GJ.zeros(~F, n1) : M.Vec(~F)}, +z2: {GJ.vdrop(~F, n1, v) == GJ.zeros(~F, n2) : M.Vec(~F)}) -> {v == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}:
  %vtd(~F, n1, v) : {_ == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), GJ.vtake(~F, n1, v), GJ.zeros(~F, n1), z1) : {GJ.vapp(~F, _, GJ.vdrop(~F, n1, v)) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), GJ.vdrop(~F, n1, v), GJ.zeros(~F, n2), z2) : {GJ.vapp(~F, GJ.zeros(~F, n1), _) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}
  Equal.sym(M.Vec(~F), GJ.zeros(~F, Nat.add(n1, n2)), GJ.vapp(~F, GJ.zeros(~F, n1), GJ.zeros(~F, n2)), GJ.vapp_zz(~F, n1, n2))

def bm_e(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, +v: M.Vec(~F), +e: {M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), v) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}) -> {M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), GJ.vapp(~F, GJ.vtake(~F, n1, v), GJ.vdrop(~F, n1, v))) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), GJ.vapp(~F, GJ.vtake(~F, n1, v), GJ.vdrop(~F, n1, v)), v, vtd(~F, n1, v)) : {M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), _) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}
  e

# [[A, 0], [C, D]] v = 0, with A and D injective, gives v = 0
def bm_inj(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, ia: @u: M.Vec(~F) -> {M.len(~F, u) == n1 : Nat} -> {M.matvec(~F, a, u) == GJ.zeros(~F, n1) : M.Vec(~F)} -> {u == GJ.zeros(~F, n1) : M.Vec(~F)}, id: @u: M.Vec(~F) -> {M.len(~F, u) == n2 : Nat} -> {M.matvec(~F, d, u) == GJ.zeros(~F, n2) : M.Vec(~F)} -> {u == GJ.zeros(~F, n2) : M.Vec(~F)}, +v: M.Vec(~F), +lv: {M.len(~F, v) == Nat.add(n1, n2) : Nat}, +e: {M.matvec(~F, GJ.bm(~F, a, c, d, n1, n2), v) == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}) -> {v == GJ.zeros(~F, Nat.add(n1, n2)) : M.Vec(~F)}:
  +v1 = GJ.vtake(~F, n1, v)
  +v2 = GJ.vdrop(~F, n1, v)
  +l1 = Equal.sym(Nat, n1, M.len(~F, v1), GJ.len_vtake(~F, n1, v, KA.natle_rw(n1, Nat.add(n1, n2), M.len(~F, v), Equal.sym(Nat, M.len(~F, v), Nat.add(n1, n2), lv), natle_addr(n1, n2))))
  +l2 = len_vdrop(~F, n1, v, n2, lv)
  +e2 = bm_split(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, v1, v2, l1, bm_e(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, v, e))
  +lt = GJ.len_vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1), n1, GJ.len_mv(~F, a, n1, v1, sa), GJ.len_zeros_eq(~F, n1))
  +z1 = ia(v1, l1, bm_top(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, v1, v2, GJ.vapp_z1(~F, M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)), M.vadd(~F, M.matvec(~F, c, v1), M.matvec(~F, d, v2)), n1, n2, lt, e2)))
  +z2 = id(v2, l2, bm_bot(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, v1, v2, z1, GJ.vapp_z2(~F, M.vadd(~F, M.matvec(~F, a, v1), GJ.zeros(~F, n1)), M.vadd(~F, M.matvec(~F, c, v1), M.matvec(~F, d, v2)), n1, n2, lt, e2)))
  vz_join(~F, v, n1, n2, z1, z2)

# Lists of numbers
# ----------------

def tk_dp(n: Nat, xs: List<&2, Nat>) -> {ST.app(SO.ntake(n, xs), OW.ndrop(n, xs)) == xs : List<&2, Nat>}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, ST.app(SO.ntake(m, t), OW.ndrop(m, t)), t, tk_dp(m, t)) : {Con{h, _} == Con{h, t} : List<&2, Nat>}
      {==}

def dp_nil(n: Nat) -> {OW.ndrop(n, Nil{}) == Nil{} : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def dp_dp(o: Nat, +n: Nat, xs: List<&2, Nat>) -> {OW.ndrop(n, OW.ndrop(o, xs)) == OW.ndrop(Nat.add(o, n), xs) : List<&2, Nat>}:
  match o xs:
    case 0n xs:
      {==}
    case 1n+j Nil{}:
      dp_nil(n)
    case 1n+j Con{h, t}:
      dp_dp(j, n, t)

def len_tk(n: Nat, xs: List<&2, Nat>, h: {KA.natle(n, SV.len(xs)) == True{} : Bool}) -> {SV.len(SO.ntake(n, xs)) == n : Nat}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      absurd({SV.len(SO.ntake(1n+m, Nil{})) == 1n+m : Nat}, KA.ft(h))
    case 1n++m Con{h2, +t}:
      %Equal.sym(Nat, SV.len(SO.ntake(m, t)), m, len_tk(m, t, h)) : {1n+_ == 1n+m : Nat}
      {==}

def len_dp(n: Nat, xs: List<&2, Nat>, +k: Nat, h: {SV.len(xs) == Nat.add(n, k) : Nat}) -> {SV.len(OW.ndrop(n, xs)) == k : Nat}:
  match n xs:
    case 0n xs:
      h
    case 1n+m Nil{}:
      absurd({SV.len(OW.ndrop(1n+m, Nil{})) == k : Nat}, FV.zero_ne(Nat.add(m, k), h))
    case 1n++m Con{h2, +t}:
      len_dp(m, t, k, LN.succ_inj(SV.len(t), Nat.add(m, k), h))

def le_dp(o: Nat, +n: Nat, xs: List<&2, Nat>, h: {KA.natle(Nat.add(o, n), SV.len(xs)) == True{} : Bool}) -> {KA.natle(n, SV.len(OW.ndrop(o, xs))) == True{} : Bool}:
  match o xs:
    case 0n xs:
      h
    case 1n+j Nil{}:
      absurd({KA.natle(n, SV.len(OW.ndrop(1n+j, Nil{}))) == True{} : Bool}, KA.ft(h))
    case 1n+j Con{h2, t}:
      le_dp(j, n, t, h)

def subl_tk(+n: Nat, +xs: List<&2, Nat>) -> {L.subl(SO.ntake(n, xs), xs) == True{} : Bool}:
  PB.subl_app_l(SO.ntake(n, xs), OW.ndrop(n, xs), xs, (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, xs), OW.ndrop(n, xs)), xs, tk_dp(n, xs)) : {L.subl(_, xs) == True{} : Bool}
    L.subl_refl(xs)))

def subl_dp(+n: Nat, +xs: List<&2, Nat>) -> {L.subl(OW.ndrop(n, xs), xs) == True{} : Bool}:
  PB.subl_app_r(SO.ntake(n, xs), OW.ndrop(n, xs), xs, (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, xs), OW.ndrop(n, xs)), xs, tk_dp(n, xs)) : {L.subl(_, xs) == True{} : Bool}
    L.subl_refl(xs)))

def mop.go(+v: Nat, +t: List<&2, Nat>, b: Bool, hl: {KA.natle(1n+PL.pos.go(b, PL.pos(v, t)), 1n+PL.nlen(t)) == True{} : Bool}, ih: {KA.natle(1n+PL.pos(v, t), PL.nlen(t)) == True{} : Bool} -> {SV.mem(v, t) == True{} : Bool}) -> {SV.bor(b, SV.mem(v, t)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(hl)

# a position inside the list is a member's
def mem_of_pos(+v: Nat, xs: List<&2, Nat>, h: {KA.natle(1n+PL.pos(v, xs), PL.nlen(xs)) == True{} : Bool}) -> {SV.mem(v, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(v, Nil{}) == True{} : Bool}, KA.ft(h))
    case Con{+h2, +t}:
      %Equal.sym(Bool, SV.eq(v, h2), KA.nateq(v, h2), L.eq_sv(v, h2)) : {SV.bor(_, SV.mem(v, t)) == True{} : Bool}
      mop.go(v, t, KA.nateq(v, h2), h, hm => mem_of_pos(v, t, hm))

# Equations of the plan
# ---------------------

def eb_get(+m: Nat, es: List<&2, E.QExpr>, j: Nat, +h: {PL.eqs_below(m, es) == True{} : Bool}) -> {SL.below(m, PL.eqget(es, j)) == True{} : Bool}:
  match es j:
    case Nil{} j:
      {==}
    case Con{+e, +t} 0n:
      KA.band_l(SL.below(m, e), PL.eqs_below(m, t), h)
    case Con{+e, +t} 1n+k:
      eb_get(m, t, k, KA.band_r(SL.below(m, e), PL.eqs_below(m, t), h))

# below cnt, with every variable below cnt in xs: inside xs
def inb(e: E.QExpr, +xs: List<&2, Nat>, +cnt: Nat, +hp: {PL.present(xs, cnt, 0n) == True{} : Bool}, +hb: {SL.below(cnt, e) == True{} : Bool}) -> {SV.inside(e, xs) == True{} : Bool}:
  match e:
    case E.QVar{+v}:
      mem_of_pos(v, xs, PP.present0(xs, cnt, v, hp, hb))
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      L.band_i(SV.inside(a, xs), SV.inside(b, xs), inb(a, xs, cnt, hp, KA.band_l(SL.below(cnt, a), SL.below(cnt, b), hb)), inb(b, xs, cnt, hp, KA.band_r(SL.below(cnt, a), SL.below(cnt, b), hb)))
    case E.QSub{+a, +b}:
      L.band_i(SV.inside(a, xs), SV.inside(b, xs), inb(a, xs, cnt, hp, KA.band_l(SL.below(cnt, a), SL.below(cnt, b), hb)), inb(b, xs, cnt, hp, KA.band_r(SL.below(cnt, a), SL.below(cnt, b), hb)))
    case E.QMul{+a, +b}:
      L.band_i(SV.inside(a, xs), SV.inside(b, xs), inb(a, xs, cnt, hp, KA.band_l(SL.below(cnt, a), SL.below(cnt, b), hb)), inb(b, xs, cnt, hp, KA.band_r(SL.below(cnt, a), SL.below(cnt, b), hb)))
    case E.QNeg{+a}:
      inb(a, xs, cnt, hp, hb)

# every equation uses only variables of vp
def allin_all(+eqs: List<&2, E.QExpr>, js: List<&2, Nat>, +vp: List<&2, Nat>, +cnt: Nat, +hp: {PL.present(vp, cnt, 0n) == True{} : Bool}, +hb: {PL.eqs_below(cnt, eqs) == True{} : Bool}) -> {BI.allin(eqs, js, vp) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.band_i(SV.inside(PL.eqget(eqs, j), vp), BI.allin(eqs, t, vp), inb(PL.eqget(eqs, j), vp, cnt, hp, eb_get(cnt, eqs, j, hb)), allin_all(eqs, t, vp, cnt, hp, hb))

def allin_app_l(+full: List<&2, E.QExpr>, a: List<&2, Nat>, +b: List<&2, Nat>, +w: List<&2, Nat>, +h: {BI.allin(full, ST.app(a, b), w) == True{} : Bool}) -> {BI.allin(full, a, w) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.band_i(SV.inside(PL.eqget(full, j), w), BI.allin(full, t, w), L.band_l(SV.inside(PL.eqget(full, j), w), BI.allin(full, ST.app(t, b), w), h), allin_app_l(full, t, b, w, L.band_r(SV.inside(PL.eqget(full, j), w), BI.allin(full, ST.app(t, b), w), h)))

def allin_app_r(+full: List<&2, E.QExpr>, a: List<&2, Nat>, +b: List<&2, Nat>, +w: List<&2, Nat>, +h: {BI.allin(full, ST.app(a, b), w) == True{} : Bool}) -> {BI.allin(full, b, w) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+j, +t}:
      allin_app_r(full, t, b, w, L.band_r(SV.inside(PL.eqget(full, j), w), BI.allin(full, ST.app(t, b), w), h))

def allin_tk(+full: List<&2, E.QExpr>, +n: Nat, +es: List<&2, Nat>, +w: List<&2, Nat>, +h: {BI.allin(full, es, w) == True{} : Bool}) -> {BI.allin(full, SO.ntake(n, es), w) == True{} : Bool}:
  allin_app_l(full, SO.ntake(n, es), OW.ndrop(n, es), w, (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, es), OW.ndrop(n, es)), es, tk_dp(n, es)) : {BI.allin(full, _, w) == True{} : Bool}
    h))

def allin_dp(+full: List<&2, E.QExpr>, +n: Nat, +es: List<&2, Nat>, +w: List<&2, Nat>, +h: {BI.allin(full, es, w) == True{} : Bool}) -> {BI.allin(full, OW.ndrop(n, es), w) == True{} : Bool}:
  allin_app_r(full, SO.ntake(n, es), OW.ndrop(n, es), w, (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, es), OW.ndrop(n, es)), es, tk_dp(n, es)) : {BI.allin(full, _, w) == True{} : Bool}
    h))

def tq_ro(+vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, n: Nat, es: List<&2, Nat>) -> {PL.takeq(n, PL.reorder(vp, eqs, es)) == PL.reorder(vp, eqs, SO.ntake(n, es)) : List<&2, E.QExpr>}:
  match n es:
    case 0n es:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+j, +t}:
      %Equal.sym(List<&2, E.QExpr>, PL.takeq(k, PL.reorder(vp, eqs, t)), PL.reorder(vp, eqs, SO.ntake(k, t)), tq_ro(vp, eqs, k, t)) : {Con{PL.rnv(vp, PL.eqget(eqs, j)), _} == Con{PL.rnv(vp, PL.eqget(eqs, j)), PL.reorder(vp, eqs, SO.ntake(k, t))} : List<&2, E.QExpr>}
      {==}

def dq_ro(+vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, n: Nat, es: List<&2, Nat>) -> {PL.dropq(n, PL.reorder(vp, eqs, es)) == PL.reorder(vp, eqs, OW.ndrop(n, es)) : List<&2, E.QExpr>}:
  match n es:
    case 0n es:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+j, +t}:
      dq_ro(vp, eqs, k, t)

# the plan's block reads each of its equations within vp, below o + n in
# block order and below n + m locally
def rowsok_of(+eqs: List<&2, E.QExpr>, +vp: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, es: List<&2, Nat>, +hin: {BI.allin(eqs, es, vp) == True{} : Bool}, +hb: {PL.eqs_below(Nat.add(o, n), PL.reorder(vp, eqs, es)) == True{} : Bool}, +hl: {CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, es))) == True{} : Bool}) -> {LC.rowsok(eqs, vp, o, n, pars, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      +rj = PL.rnv(vp, PL.eqget(eqs, j))
      L.band_i(SV.inside(PL.eqget(eqs, j), vp), SV.band(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(eqs, vp, o, n, pars, t))),
        L.band_l(SV.inside(PL.eqget(eqs, j), vp), BI.allin(eqs, t, vp), hin),
        L.band_i(SL.below(Nat.add(o, n), rj), SV.band(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(eqs, vp, o, n, pars, t)),
          KA.band_l(SL.below(Nat.add(o, n), rj), PL.eqs_below(Nat.add(o, n), PL.reorder(vp, eqs, t)), hb),
          L.band_i(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), LC.rowsok(eqs, vp, o, n, pars, t),
            KA.band_l(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, t))), hl),
            rowsok_of(eqs, vp, o, n, pars, t, L.band_r(SV.inside(PL.eqget(eqs, j), vp), BI.allin(eqs, t, vp), hin), KA.band_r(SL.below(Nat.add(o, n), rj), PL.eqs_below(Nat.add(o, n), PL.reorder(vp, eqs, t)), hb), KA.band_r(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, rj)), CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, t))), hl)))))

# A block, locally
# ----------------


def ok_of(+vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<KI.dnum()>, +h: {CK.check(~KI.dnum(), C.Block{PL.renames(o, n, pars, PL.takeq(n, PL.reorder(vp, eqs, epr))), n}, c) == True{} : Bool}) -> {CK.check(~KI.dnum(), C.Block{PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n}, c) == True{} : Bool}:
  %tq_ro(vp, eqs, n, epr) : {CK.check(~KI.dnum(), C.Block{PL.renames(o, n, pars, _), n}, c) == True{} : Bool}
  h

def below_of(+vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +h: {PL.eqs_below(Nat.add(o, n), PL.takeq(n, PL.reorder(vp, eqs, epr))) == True{} : Bool}) -> {PL.eqs_below(Nat.add(o, n), PL.reorder(vp, eqs, SO.ntake(n, epr))) == True{} : Bool}:
  %tq_ro(vp, eqs, n, epr) : {PL.eqs_below(Nat.add(o, n), _) == True{} : Bool}
  h

def vp3(+o: Nat, +n: Nat, +vp: List<&2, Nat>) -> {vp == ST.app(SO.ntake(o, vp), ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp)))) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp))), OW.ndrop(o, vp), tk_dp(n, OW.ndrop(o, vp))) : {vp == ST.app(SO.ntake(o, vp), _) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, ST.app(SO.ntake(o, vp), OW.ndrop(o, vp)), vp, tk_dp(o, vp))

def xsplit2(~F: O.OField, +o: Nat, +n: Nat, +y: M.Vec(~F)) -> {y == C.app(~F, C.app(~F, PP.ftake(~F, o, y), PP.ftake(~F, n, PP.fdrop(~F, o, y))), PP.fdrop(~F, Nat.add(o, n), y)) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), C.app(~F, PP.ftake(~F, o, y), PP.ftake(~F, n, PP.fdrop(~F, o, y))), PP.ftake(~F, Nat.add(o, n), y), LC.app_take(~F, o, n, y)) : {y == C.app(~F, _, PP.fdrop(~F, Nat.add(o, n), y)) : M.Vec(~F)}
  Equal.sym(M.Vec(~F), C.app(~F, PP.ftake(~F, Nat.add(o, n), y), PP.fdrop(~F, Nat.add(o, n), y)), y, PP.app_td(~F, Nat.add(o, n), y))

# the local slopes at (y ++ z) are the block's Jacobian at x
def ev_of(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +hly: {M.len(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))) == n : Nat}, +hjl: {DV.jac(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), ST.iota(n, 0n)) == DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))) : M.Mat(~F)}, +d: M.Vec(~F), +e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), d) == GJ.zeros(~F, n) : M.Vec(~F)}) -> {M.matvec(~F, CP.smat(~F, C.app(~F, C.fit(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), C.app(~F, C.fit(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, 0n), d) == GJ.zeros(~F, n) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), C.fit(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), FV.fit_len(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), hly)) : {M.matvec(~F, CP.smat(~F, C.app(~F, _, PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), C.app(~F, C.fit(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, 0n), d) == GJ.zeros(~F, n) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), C.fit(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), FV.fit_len(~F, n, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), hly)) : {M.matvec(~F, CP.smat(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), C.app(~F, _, PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, 0n), d) == GJ.zeros(~F, n) : M.Vec(~F)}
  %AP.jac_smat(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, 0n) : {M.matvec(~F, _, d) == GJ.zeros(~F, n) : M.Vec(~F)}
  %Equal.sym(M.Mat(~F), DV.jac(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), ST.iota(n, 0n)), DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), hjl) : {M.matvec(~F, _, d) == GJ.zeros(~F, n) : M.Vec(~F)}
  e

# the block's own Jacobian is injective: locally it is the certificate's
# slopes at a point of its box (lib/certpf.bend: cert_jinj)
def blk_inj(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +hX: BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp)), +hgr: {KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gr, vp)) == KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)) : Nat}, +hvd: {SV.distinct(vp) == True{} : Bool}, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<KI.dnum()>, +hbo: {PL.block_ok(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c) == True{} : Bool}, +hin: {BI.allin(eqs, epr, vp) == True{} : Bool}, +d: M.Vec(~F), +hdl: {M.len(~F, d) == n : Nat}, +e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), d) == GJ.zeros(~F, n) : M.Vec(~F)}) -> {d == GJ.zeros(~F, n) : M.Vec(~F)}:
  +hgc = PP.bo_in_box(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo)
  +hgo = PP.natle_addl(o, n, KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), hgc)
  +hlx = Equal.trans(Nat, M.len(~F, LC.xperm(~F, x, vp)), M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp))), KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), PP.inbox_len(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp), hX), CP.len_ofkv(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp)))
  +hXn = KA.natle_rw(Nat.add(o, n), KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), M.len(~F, LC.xperm(~F, x, vp)), Equal.sym(Nat, M.len(~F, LC.xperm(~F, x, vp)), KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), hlx), hgc)
  +hXo = KA.natle_rw(o, KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), M.len(~F, LC.xperm(~F, x, vp)), Equal.sym(Nat, M.len(~F, LC.xperm(~F, x, vp)), KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), hlx), hgo)
  +hlv = Equal.trans(Nat, KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), PL.nlen(vp), SV.len(vp), PP.klen_kperm(~KI.dnum(), gc, vp), PB.nlen_sv(vp))
  +hvo = KA.natle_rw(o, KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), SV.len(vp), hlv, hgo)
  +hvn = KA.natle_rw(Nat.add(o, n), KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)), SV.len(vp), hlv, hgc)
  +okc = ok_of(vp, eqs, epr, o, n, pars, c, PP.bo_cert(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))
  +hlp = PP.len_ftake(~F, o, LC.xperm(~F, x, vp), hXo)
  +hly = PP.len_ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)), LC.ld_le(~F, o, n, LC.xperm(~F, x, vp), hXn))
  +hpb0 = PP.pbox_of_inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), o, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.fdrop(~F, o, LC.xperm(~F, x, vp)), PP.inbox_rw(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp), C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.fdrop(~F, o, LC.xperm(~F, x, vp))), Equal.sym(M.Vec(~F), C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.fdrop(~F, o, LC.xperm(~F, x, vp))), LC.xperm(~F, x, vp), PP.app_td(~F, o, LC.xperm(~F, x, vp))), hX), hlp, hgo, hgr)
  +hlpy = Equal.trans(Nat, M.len(~F, C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))))), Nat.add(M.len(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp))), M.len(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))))), Nat.add(o, n), PP.len_app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.add2(M.len(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp))), o, M.len(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), n, hlp, hly))
  +hpb1 = PP.pbox_of_inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), Nat.add(o, n), C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.fdrop(~F, Nat.add(o, n), LC.xperm(~F, x, vp)), PP.inbox_rw(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp), C.app(~F, C.app(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp)))), PP.fdrop(~F, Nat.add(o, n), LC.xperm(~F, x, vp))), xsplit2(~F, o, n, LC.xperm(~F, x, vp)), hX), hlpy, hgc, hgr)
  +hball = PP.ball_of_seg(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), o, n, c, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.seg_of_pbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), o, n, PP.ftake(~F, o, LC.xperm(~F, x, vp)), PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), hpb1, hlp, hgo, hgr), hly, PP.cert_lyc(~KI.dnum(), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, c, okc), PP.bo_yc(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo), PP.bo_yr(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))
  +hpin = PP.pin_pc(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), o, PP.ftake(~F, o, LC.xperm(~F, x, vp)), hpb0, hgo, pars, C.Cert.pc(KI.dnum(), c), C.Cert.pr(KI.dnum(), c), PP.bo_pars(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo), PP.bo_pcont(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))
  +hbel = PP.allb_rw(Nat.add(n, KA.klen(~KI.dnum(), C.Cert.pc(KI.dnum(), c))), Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), PP.add2(n, n, KA.klen(~KI.dnum(), C.Cert.pc(KI.dnum(), c)), PL.nlen(pars), {==}, PP.pcont_len(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), pars, C.Cert.pc(KI.dnum(), c), C.Cert.pr(KI.dnum(), c), PP.bo_pcont(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))), PP.cert_bel(~KI.dnum(), PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, c, okc))
  +hrow = rowsok_of(eqs, vp, o, n, pars, SO.ntake(n, epr), allin_tk(eqs, n, epr, vp, hin), below_of(vp, eqs, epr, o, n, PP.bo_below(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo)), hbel)
  +hrun = PB.posrun_of(vp, SO.ntake(n, OW.ndrop(o, vp)), SO.ntake(o, vp), OW.ndrop(n, OW.ndrop(o, vp)), o, 0n, vp3(o, n, vp), Equal.trans(Nat, SV.len(SO.ntake(o, vp)), o, Nat.add(o, 0n), len_tk(o, vp, hvo), LN.add_zero(o)), hvd)
  +hvs = L.subl_trans(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(o, vp), vp, subl_tk(n, OW.ndrop(o, vp)), subl_dp(o, vp))
  +hn = len_tk(n, OW.ndrop(o, vp), le_dp(o, n, vp, hvn))
  +hjl = LC.jac_loc(~F, x, vp, o, n, pars, eqs, SO.ntake(n, epr), SO.ntake(n, OW.ndrop(o, vp)), hrun, hvs, hn, hrow, hXn)
  CP.cert_jinj(~KI.dnum(), ~F, ~H, PL.renames(o, n, pars, PL.reorder(vp, eqs, SO.ntake(n, epr))), n, c, okc, PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars), hpin, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), hball, d, hdl, ev_of(~F, x, vp, eqs, epr, o, n, pars, hly, hjl, d, e))

# The walk's lengths
# ------------------

def isnil_ok(es: List<&2, E.QExpr>, h: {PL.isnil(es) == True{} : Bool}) -> {CK.eqlen(es) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      absurd({CK.eqlen(Con{e, t}) == 0n : Nat}, KA.ft(h))

def eq_dq(n: Nat, es: List<&2, E.QExpr>, h: {KA.natle(n, CK.eqlen(es)) == True{} : Bool}) -> {CK.eqlen(es) == Nat.add(n, CK.eqlen(PL.dropq(n, es))) : Nat}:
  match n es:
    case 0n es:
      {==}
    case 1n+k Nil{}:
      absurd({CK.eqlen(Nil{}) == Nat.add(1n+k, CK.eqlen(PL.dropq(1n+k, Nil{}))) : Nat}, KA.ft(h))
    case 1n++k Con{e, +t}:
      %Equal.sym(Nat, CK.eqlen(t), Nat.add(k, CK.eqlen(PL.dropq(k, t))), eq_dq(k, t, h)) : {1n+_ == 1n+Nat.add(k, CK.eqlen(PL.dropq(k, t))) : Nat}
      {==}

# the walk ends with as many equations as variables
def wl(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), bs: List<&2, PL.PBlock<K>>, +es: List<&2, E.QExpr>, +o: Nat, +hw: {PL.walk(~K, gc, gr, bs, es, o) == True{} : Bool}) -> {Nat.add(o, CK.eqlen(es)) == KA.klen(~K, gc) : Nat}:
  match bs:
    case Nil{}:
      +ho = KA.nateq_ok(o, KA.klen(~K, gc), KA.band_l(KA.nateq(o, KA.klen(~K, gc)), PL.isnil(es), hw))
      %Equal.sym(Nat, CK.eqlen(es), 0n, isnil_ok(es, KA.band_r(KA.nateq(o, KA.klen(~K, gc)), PL.isnil(es), hw))) : {Nat.add(o, _) == KA.klen(~K, gc) : Nat}
      %LN.add_zero(o) : {_ == KA.klen(~K, gc) : Nat}
      ho
    case Con{PL.PBlock{+n, +pars, +c}, +t}:
      +hbo = KA.band_l(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      +hrest = KA.band_r(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      %Equal.sym(Nat, CK.eqlen(es), Nat.add(n, CK.eqlen(PL.dropq(n, es))), eq_dq(n, es, PP.bo_n_eqs(~K, gc, gr, es, o, n, pars, c, hbo))) : {Nat.add(o, _) == KA.klen(~K, gc) : Nat}
      %Equal.sym(Nat, Nat.add(o, Nat.add(n, CK.eqlen(PL.dropq(n, es)))), Nat.add(Nat.add(o, n), CK.eqlen(PL.dropq(n, es))), LN.add_assoc(o, n, CK.eqlen(PL.dropq(n, es)))) : {_ == KA.klen(~K, gc) : Nat}
      wl(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n), hrest)

def hwl(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +hX: BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp)), +hgr: {KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gr, vp)) == KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)) : Nat}, +hvd: {SV.distinct(vp) == True{} : Bool}, bs: List<&2, PL.PBlock<KI.dnum()>>, +epr: List<&2, Nat>, +o: Nat, +hw: {PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, PL.reorder(vp, eqs, epr), o) == True{} : Bool}) -> {Nat.add(o, SV.len(epr)) == SV.len(vp) : Nat}:
  +h = wl(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, PL.reorder(vp, eqs, epr), o, hw)
  %PB.nlen_sv(epr) : {Nat.add(o, _) == SV.len(vp) : Nat}
  %PP.len_reorder(vp, eqs, epr) : {Nat.add(o, _) == SV.len(vp) : Nat}
  %PB.nlen_sv(vp) : {Nat.add(o, CK.eqlen(PL.reorder(vp, eqs, epr))) == _ : Nat}
  %PP.klen_kperm(~KI.dnum(), gc, vp) : {Nat.add(o, CK.eqlen(PL.reorder(vp, eqs, epr))) == _ : Nat}
  h

# Variables before o + n
# ----------------------

def mem_tk.go(+v: Nat, +t: List<&2, Nat>, +m: Nat, b: Bool, hp: {KA.natle(1n+PL.pos.go(b, PL.pos(v, t)), 1n+m) == True{} : Bool}, hm: {SV.bor(b, SV.mem(v, t)) == True{} : Bool}, ih: {SV.mem(v, t) == True{} : Bool} -> {KA.natle(1n+PL.pos(v, t), m) == True{} : Bool} -> {SV.mem(v, SO.ntake(m, t)) == True{} : Bool}) -> {SV.bor(b, SV.mem(v, SO.ntake(m, t))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(hm, hp)

# v in vp at a position below m: v among vp's first m
def mem_tk(+v: Nat, vp: List<&2, Nat>, m: Nat, hm: {SV.mem(v, vp) == True{} : Bool}, hp: {KA.natle(1n+PL.pos(v, vp), m) == True{} : Bool}) -> {SV.mem(v, SO.ntake(m, vp)) == True{} : Bool}:
  match vp m:
    case Nil{} m:
      absurd({SV.mem(v, SO.ntake(m, Nil{})) == True{} : Bool}, L.mem_nil(v, hm))
    case Con{+h, +t} 0n:
      absurd({SV.mem(v, SO.ntake(0n, Con{h, t})) == True{} : Bool}, KA.ft(hp))
    case Con{+h, +t} 1n++k:
      %Equal.sym(Bool, SV.eq(v, h), KA.nateq(v, h), L.eq_sv(v, h)) : {SV.bor(_, SV.mem(v, SO.ntake(k, t))) == True{} : Bool}
      mem_tk.go(v, t, k, KA.nateq(v, h), hp, (%L.eq_sv(v, h) : {SV.bor(_, SV.mem(v, t)) == True{} : Bool}
        hm), hm2 => hp2 => mem_tk(v, t, k, hm2, hp2))

# inside vp and below m in block order: inside vp's first m
def ins_tk(e: E.QExpr, +vp: List<&2, Nat>, +m: Nat, +hin: {SV.inside(e, vp) == True{} : Bool}, +hb: {SL.below(m, PL.rnv(vp, e)) == True{} : Bool}) -> {SV.inside(e, SO.ntake(m, vp)) == True{} : Bool}:
  match e:
    case E.QVar{+v}:
      mem_tk(v, vp, m, hin, hb)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      L.band_i(SV.inside(a, SO.ntake(m, vp)), SV.inside(b, SO.ntake(m, vp)), ins_tk(a, vp, m, L.band_l(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_l(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)), ins_tk(b, vp, m, L.band_r(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_r(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)))
    case E.QSub{+a, +b}:
      L.band_i(SV.inside(a, SO.ntake(m, vp)), SV.inside(b, SO.ntake(m, vp)), ins_tk(a, vp, m, L.band_l(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_l(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)), ins_tk(b, vp, m, L.band_r(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_r(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)))
    case E.QMul{+a, +b}:
      L.band_i(SV.inside(a, SO.ntake(m, vp)), SV.inside(b, SO.ntake(m, vp)), ins_tk(a, vp, m, L.band_l(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_l(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)), ins_tk(b, vp, m, L.band_r(SV.inside(a, vp), SV.inside(b, vp), hin), KA.band_r(SL.below(m, PL.rnv(vp, a)), SL.below(m, PL.rnv(vp, b)), hb)))
    case E.QNeg{+a}:
      ins_tk(a, vp, m, hin, hb)

# the block's equations use only vp's first o + n
def allin_tkw(+eqs: List<&2, E.QExpr>, +vp: List<&2, Nat>, +m: Nat, es: List<&2, Nat>, +hin: {BI.allin(eqs, es, vp) == True{} : Bool}, +hb: {PL.eqs_below(m, PL.reorder(vp, eqs, es)) == True{} : Bool}) -> {BI.allin(eqs, es, SO.ntake(m, vp)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.band_i(SV.inside(PL.eqget(eqs, j), SO.ntake(m, vp)), BI.allin(eqs, t, SO.ntake(m, vp)), ins_tk(PL.eqget(eqs, j), vp, m, L.band_l(SV.inside(PL.eqget(eqs, j), vp), BI.allin(eqs, t, vp), hin), KA.band_l(SL.below(m, PL.rnv(vp, PL.eqget(eqs, j))), PL.eqs_below(m, PL.reorder(vp, eqs, t)), hb)), allin_tkw(eqs, vp, m, t, L.band_r(SV.inside(PL.eqget(eqs, j), vp), BI.allin(eqs, t, vp), hin), KA.band_r(SL.below(m, PL.rnv(vp, PL.eqget(eqs, j))), PL.eqs_below(m, PL.reorder(vp, eqs, t)), hb)))

# Forward substitution
# --------------------


def rl_rw(~F: O.OField, +a: M.Mat(~F), +m: Nat, +m2: Nat, +e: {m == m2 : Nat}, +h: GJ.rl(~F, a, m)) -> GJ.rl(~F, a, m2):
  %e : GJ.rl(~F, a, _)
  h

def len_cong(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +e: {xs == ys : List<&2, Nat>}) -> {SV.len(xs) == SV.len(ys) : Nat}:
  %e : {SV.len(xs) == SV.len(_) : Nat}
  {==}

def walk_rw(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +hX: BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp)), +hgr: {KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gr, vp)) == KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)) : Nat}, +hvd: {SV.distinct(vp) == True{} : Bool}, bs: List<&2, PL.PBlock<KI.dnum()>>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +h: {PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, PL.dropq(n, PL.reorder(vp, eqs, epr)), Nat.add(o, n)) == True{} : Bool}) -> {PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, PL.reorder(vp, eqs, OW.ndrop(n, epr)), Nat.add(o, n)) == True{} : Bool}:
  %dq_ro(vp, eqs, n, epr) : {PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, _, Nat.add(o, n)) == True{} : Bool}
  h

def ne_of(+vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +n: Nat, +h: {KA.natle(n, CK.eqlen(PL.reorder(vp, eqs, epr))) == True{} : Bool}) -> {KA.natle(n, SV.len(epr)) == True{} : Bool}:
  %PB.nlen_sv(epr) : {KA.natle(n, _) == True{} : Bool}
  %PP.len_reorder(vp, eqs, epr) : {KA.natle(n, _) == True{} : Bool}
  h

def lc2_of(+o: Nat, +n: Nat, +vp: List<&2, Nat>, +k: Nat, +h: {Nat.add(Nat.add(o, n), k) == SV.len(vp) : Nat}) -> {SV.len(OW.ndrop(n, OW.ndrop(o, vp))) == k : Nat}:
  %Equal.sym(List<&2, Nat>, OW.ndrop(n, OW.ndrop(o, vp)), OW.ndrop(Nat.add(o, n), vp), dp_dp(o, n, vp)) : {SV.len(_) == k : Nat}
  len_dp(Nat.add(o, n), vp, k, Equal.sym(Nat, Nat.add(Nat.add(o, n), k), SV.len(vp), h))

# the later unknowns are none of vp's first o + n
def hd_of(+o: Nat, +n: Nat, +vp: List<&2, Nat>, +hvd: {SV.distinct(vp) == True{} : Bool}) -> {MX.disj(OW.ndrop(n, OW.ndrop(o, vp)), SO.ntake(Nat.add(o, n), vp)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, OW.ndrop(n, OW.ndrop(o, vp)), OW.ndrop(Nat.add(o, n), vp), dp_dp(o, n, vp)) : {MX.disj(_, SO.ntake(Nat.add(o, n), vp)) == True{} : Bool}
  BI.disj_swap(SO.ntake(Nat.add(o, n), vp), OW.ndrop(Nat.add(o, n), vp), BI.dist_disj(SO.ntake(Nat.add(o, n), vp), OW.ndrop(Nat.add(o, n), vp), (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(Nat.add(o, n), vp), OW.ndrop(Nat.add(o, n), vp)), vp, tk_dp(Nat.add(o, n), vp)) : {SV.distinct(_) == True{} : Bool}
    hvd)))

def jd_rw(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +u: M.Vec(~F), +eu: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))), u) == GJ.zeros(~F, SV.len(OW.ndrop(n, epr))) : M.Vec(~F)}) -> {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(Nat.add(o, n), vp)), u) == GJ.zeros(~F, SV.len(OW.ndrop(n, epr))) : M.Vec(~F)}:
  %dp_dp(o, n, vp) : {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), _), u) == GJ.zeros(~F, SV.len(OW.ndrop(n, epr))) : M.Vec(~F)}
  eu

# the rest of the system's Jacobian is [[A, 0], [C, D]]
def e_bm(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +n: Nat, +hl1: {SV.len(SO.ntake(n, epr)) == n : Nat}, +hlc2: {SV.len(OW.ndrop(n, OW.ndrop(o, vp))) == SV.len(OW.ndrop(n, epr)) : Nat}, +hle: {SV.len(epr) == Nat.add(n, SV.len(OW.ndrop(n, epr))) : Nat}, +hz: {DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))) == GJ.zmat(~F, SV.len(SO.ntake(n, epr)), SV.len(OW.ndrop(n, OW.ndrop(o, vp)))) : M.Mat(~F)}, +w: M.Vec(~F), +e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), OW.ndrop(o, vp)), w) == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}) -> {M.matvec(~F, GJ.bm(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))), n, SV.len(OW.ndrop(n, epr))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}:
  %hl1 : {M.matvec(~F, GJ.vcat(~F, GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), GJ.zmat(~F, _, SV.len(OW.ndrop(n, epr)))), GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %hlc2 : {M.matvec(~F, GJ.vcat(~F, GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), GJ.zmat(~F, SV.len(SO.ntake(n, epr)), _)), GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %hz : {M.matvec(~F, GJ.vcat(~F, GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), _), GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %BI.jac_cols(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp))) : {M.matvec(~F, GJ.vcat(~F, _, GJ.hcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %BI.jac_cols(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp))) : {M.matvec(~F, GJ.vcat(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp)))), _), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %BI.jac_rows(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), KP.pickk(eqs, 0n, OW.ndrop(n, epr)), ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp)))) : {M.matvec(~F, _, w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %BI.pickk_app(eqs, 0n, SO.ntake(n, epr), OW.ndrop(n, epr)) : {M.matvec(~F, DV.jac(~F, x, _, ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp)))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, epr), OW.ndrop(n, epr)), epr, tk_dp(n, epr)) : {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, _), ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp)))), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, OW.ndrop(o, vp)), OW.ndrop(n, OW.ndrop(o, vp))), OW.ndrop(o, vp), tk_dp(n, OW.ndrop(o, vp))) : {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), _), w) == GJ.zeros(~F, Nat.add(n, SV.len(OW.ndrop(n, epr)))) : M.Vec(~F)}
  %hle : {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), OW.ndrop(o, vp)), w) == GJ.zeros(~F, _) : M.Vec(~F)}
  e

# from offset o on, the rest of the system's Jacobian in the rest of the
# unknowns (both in block order, the sketch's numbering) is injective
def e_vr(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +epr: List<&2, Nat>, +o: Nat, +vr: List<&2, Nat>, +hvr: {vr == OW.ndrop(o, vp) : List<&2, Nat>}, +w: M.Vec(~F), +e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), vr), w) == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}) -> {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), OW.ndrop(o, vp)), w) == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}:
  %hvr : {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), _), w) == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}
  e

def rinj(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +x: M.Vec(~F), +vp: List<&2, Nat>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +hX: BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp)), +hgr: {KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gr, vp)) == KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp)) : Nat}, +hvd: {SV.distinct(vp) == True{} : Bool}, bs: List<&2, PL.PBlock<KI.dnum()>>, +epr: List<&2, Nat>, +o: Nat, +vr: List<&2, Nat>, +hvr: {vr == OW.ndrop(o, vp) : List<&2, Nat>}, +hw: {PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), bs, PL.reorder(vp, eqs, epr), o) == True{} : Bool}, +hin: {BI.allin(eqs, epr, vp) == True{} : Bool}, +w: M.Vec(~F), +lw: {M.len(~F, w) == SV.len(epr) : Nat}, +e: {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, epr), vr), w) == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}) -> {w == GJ.zeros(~F, SV.len(epr)) : M.Vec(~F)}:
  match bs:
    case Nil{}:
      +hnil = KA.band_r(KA.nateq(o, KA.klen(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp))), PL.isnil(PL.reorder(vp, eqs, epr)), hw)
      +hl0 = Equal.trans(Nat, SV.len(epr), PL.nlen(epr), 0n, Equal.sym(Nat, PL.nlen(epr), SV.len(epr), PB.nlen_sv(epr)), Equal.trans(Nat, PL.nlen(epr), CK.eqlen(PL.reorder(vp, eqs, epr)), 0n, Equal.sym(Nat, CK.eqlen(PL.reorder(vp, eqs, epr)), PL.nlen(epr), PP.len_reorder(vp, eqs, epr)), isnil_ok(PL.reorder(vp, eqs, epr), hnil)))
      %Equal.sym(Nat, SV.len(epr), 0n, hl0) : {w == GJ.zeros(~F, _) : M.Vec(~F)}
      PP.rnil.r(~F, w, Equal.trans(Nat, M.len(~F, w), SV.len(epr), 0n, lw, hl0))
    case Con{PL.PBlock{+n, +pars, +c}, +t}:
      +hbo = KA.band_l(PL.block_ok(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c), PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), t, PL.dropq(n, PL.reorder(vp, eqs, epr)), Nat.add(o, n)), hw)
      +hrest = KA.band_r(PL.block_ok(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c), PL.walk(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), t, PL.dropq(n, PL.reorder(vp, eqs, epr)), Nat.add(o, n)), hw)
      +hw2 = walk_rw(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, t, epr, o, n, hrest)
      +hwl0 = hwl(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, Con{PL.PBlock{n, pars, c}, t}, epr, o, hw)
      +hne = ne_of(vp, eqs, epr, n, PP.bo_n_eqs(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))
      +hl1 = len_tk(n, epr, hne)
      +hle = Equal.trans(Nat, SV.len(epr), Nat.add(SV.len(SO.ntake(n, epr)), SV.len(OW.ndrop(n, epr))), Nat.add(n, SV.len(OW.ndrop(n, epr))), Equal.trans(Nat, SV.len(epr), SV.len(ST.app(SO.ntake(n, epr), OW.ndrop(n, epr))), Nat.add(SV.len(SO.ntake(n, epr)), SV.len(OW.ndrop(n, epr))), len_cong(epr, ST.app(SO.ntake(n, epr), OW.ndrop(n, epr)), Equal.sym(List<&2, Nat>, ST.app(SO.ntake(n, epr), OW.ndrop(n, epr)), epr, tk_dp(n, epr))), MX.len_app(SO.ntake(n, epr), OW.ndrop(n, epr))), PP.add2(SV.len(SO.ntake(n, epr)), n, SV.len(OW.ndrop(n, epr)), SV.len(OW.ndrop(n, epr)), hl1, {==}))
      +hwl2 = hwl(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, t, OW.ndrop(n, epr), Nat.add(o, n), hw2)
      +hlc2 = lc2_of(o, n, vp, SV.len(OW.ndrop(n, epr)), hwl2)
      +hlw = len_dp(o, vp, SV.len(epr), Equal.sym(Nat, Nat.add(o, SV.len(epr)), SV.len(vp), hwl0))
      +hlc1 = len_tk(n, OW.ndrop(o, vp), KA.natle_rw(n, SV.len(epr), SV.len(OW.ndrop(o, vp)), Equal.sym(Nat, SV.len(OW.ndrop(o, vp)), SV.len(epr), hlw), hne))
      +hz = BI.jac_z(~F, x, eqs, SO.ntake(n, epr), SO.ntake(Nat.add(o, n), vp), allin_tkw(eqs, vp, Nat.add(o, n), SO.ntake(n, epr), allin_tk(eqs, n, epr, vp, hin), below_of(vp, eqs, epr, o, n, PP.bo_below(~KI.dnum(), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), PL.reorder(vp, eqs, epr), o, n, pars, c, hbo))), OW.ndrop(n, OW.ndrop(o, vp)), hd_of(o, n, vp, hvd))
      +sa = Equal.trans(Nat, GJ.nrows(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp)))), SV.len(SO.ntake(n, epr)), n, PM.nrows_pick(~F, x, eqs, SO.ntake(n, epr), SO.ntake(n, OW.ndrop(o, vp))), hl1)
      +ra = rl_rw(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), SV.len(SO.ntake(n, OW.ndrop(o, vp))), n, hlc1, PM.rl_jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))))
      +sc = PM.nrows_pick(~F, x, eqs, OW.ndrop(n, epr), SO.ntake(n, OW.ndrop(o, vp)))
      +rc = rl_rw(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), SV.len(SO.ntake(n, OW.ndrop(o, vp))), n, hlc1, PM.rl_jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))))
      +sd = PM.nrows_pick(~F, x, eqs, OW.ndrop(n, epr), OW.ndrop(n, OW.ndrop(o, vp)))
      %Equal.sym(Nat, SV.len(epr), Nat.add(n, SV.len(OW.ndrop(n, epr))), hle) : {w == GJ.zeros(~F, _) : M.Vec(~F)}
      bm_inj(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, SO.ntake(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), SO.ntake(n, OW.ndrop(o, vp))), DV.jac(~F, x, KP.pickk(eqs, 0n, OW.ndrop(n, epr)), OW.ndrop(n, OW.ndrop(o, vp))), n, SV.len(OW.ndrop(n, epr)), sa, ra, sc, rc, sd, u => lu => eu => blk_inj(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, epr, o, n, pars, c, hbo, hin, u, lu, eu), u => lu => eu => rinj(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, t, OW.ndrop(n, epr), Nat.add(o, n), OW.ndrop(n, OW.ndrop(o, vp)), dp_dp(o, n, vp), hw2, allin_dp(eqs, n, epr, vp, hin), u, lu, eu), w, Equal.trans(Nat, M.len(~F, w), SV.len(epr), Nat.add(n, SV.len(OW.ndrop(n, epr))), lw, hle), e_bm(~F, x, vp, eqs, epr, o, n, hl1, hlc2, hle, hz, w, e_vr(~F, x, vp, eqs, epr, o, vr, hvr, w, e)))

# Back to the sketch's order
# --------------------------

def xz_eq(~F: O.OField, +x: M.Vec(~F), vp: List<&2, Nat>) -> {LC.xperm(~F, x, vp) == PP.zmap(~F, x, vp) : M.Vec(~F)}:
  match vp:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      %Equal.sym(M.Vec(~F), LC.xperm(~F, x, t), PP.zmap(~F, x, t), xz_eq(~F, x, t)) : {Con{O.lookup(~F, x, v), _} == Con{O.lookup(~F, x, v), PP.zmap(~F, x, t)} : M.Vec(~F)}
      {==}

def below_of_pars(+o: Nat, xs: List<&2, Nat>, +h: {PL.pars_ok(o, xs) == True{} : Bool}) -> {SV.below(xs, o) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      L.band_i(SV.lt(v, o), SV.below(t, o), (%Equal.sym(Bool, SV.lt(v, o), KA.natle(1n+v, o), L.lt_sv(v, o)) : {_ == True{} : Bool}
        KA.band_l(KA.natle(1n+v, o), PL.pars_ok(o, t), h)), below_of_pars(o, t, KA.band_r(KA.natle(1n+v, o), PL.pars_ok(o, t), h)))

def pars_tk(+o: Nat, n: Nat, xs: List<&2, Nat>, +h: {PL.pars_ok(o, xs) == True{} : Bool}) -> {PL.pars_ok(o, SO.ntake(n, xs)) == True{} : Bool}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n++m Con{+v, +t}:
      KA.band_i(KA.natle(1n+v, o), PL.pars_ok(o, SO.ntake(m, t)), KA.band_l(KA.natle(1n+v, o), PL.pars_ok(o, t), h), pars_tk(o, m, t, KA.band_r(KA.natle(1n+v, o), PL.pars_ok(o, t), h)))

def lom.go(+o: Nat, +v: Nat, +u: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(v, u) == b : Bool}, hm: {SV.bor(b, SV.mem(v, t)) == True{} : Bool}, hu: {KA.natle(1n+u, o) == True{} : Bool}, ih: {SV.mem(v, t) == True{} : Bool} -> {KA.natle(1n+v, o) == True{} : Bool}) -> {KA.natle(1n+v, o) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, v, u, L.eq_ok(v, u, e)) : {KA.natle(1n+_, o) == True{} : Bool}
      hu
    case False{}:
      ih(hm)

# a member of a list of numbers below o is below o
def lt_of_mem(+o: Nat, xs: List<&2, Nat>, +v: Nat, +h: {PL.pars_ok(o, xs) == True{} : Bool}, hm: {SV.mem(v, xs) == True{} : Bool}) -> {KA.natle(1n+v, o) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({KA.natle(1n+v, o) == True{} : Bool}, L.mem_nil(v, hm))
    case Con{+u, +t}:
      lom.go(o, v, u, t, SV.eq(v, u), {==}, hm, KA.band_l(KA.natle(1n+u, o), PL.pars_ok(o, t), h), hm2 => lt_of_mem(o, t, v, KA.band_r(KA.natle(1n+u, o), PL.pars_ok(o, t), h), hm2))

def maf.go(+u: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, c: Bool, h: {SV.bor(c, SV.mem(u, ST.app(t, b))) == True{} : Bool}, hn: {SV.bor(c, SV.mem(u, t)) == False{} : Bool}, ih: {SV.mem(u, ST.app(t, b)) == True{} : Bool} -> {SV.mem(u, t) == False{} : Bool} -> {SV.mem(u, b) == True{} : Bool}) -> {SV.mem(u, b) == True{} : Bool}:
  match c:
    case True{}:
      absurd({SV.mem(u, b) == True{} : Bool}, KA.tf(hn))
    case False{}:
      ih(h, hn)

# in a ++ b and not in a: in b
def mem_app_rf(+u: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, ST.app(a, b)) == True{} : Bool}, hn: {SV.mem(u, a) == False{} : Bool}) -> {SV.mem(u, b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      maf.go(u, t, b, SV.eq(u, x), h, hn, h2 => hn2 => mem_app_rf(u, t, b, h2, hn2))

def dl.go(+x: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, c: Bool, e: {SV.mem(x, t) == c : Bool}, h: {SV.bnot(SV.mem(x, ST.app(t, b))) == True{} : Bool}) -> {SV.bnot(c) == True{} : Bool}:
  match c:
    case True{}:
      absurd({SV.bnot(True{}) == True{} : Bool}, KA.ft((%TJ.mem_app_l(x, t, b, e) : {SV.bnot(_) == True{} : Bool}
        h)))
    case False{}:
      {==}

def dist_l(a: List<&2, Nat>, +b: List<&2, Nat>, +d: {SV.distinct(ST.app(a, b)) == True{} : Bool}) -> {SV.distinct(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.bnot(SV.mem(x, t)), SV.distinct(t), dl.go(x, t, b, SV.mem(x, t), {==}, L.band_l(SV.bnot(SV.mem(x, ST.app(t, b))), SV.distinct(ST.app(t, b)), d)), dist_l(t, b, L.band_r(SV.bnot(SV.mem(x, ST.app(t, b))), SV.distinct(ST.app(t, b)), d)))

def dist_app(+m: Nat, +vp: List<&2, Nat>, +hvd: {SV.distinct(vp) == True{} : Bool}) -> {SV.distinct(ST.app(SO.ntake(m, vp), OW.ndrop(m, vp))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(m, vp), OW.ndrop(m, vp)), vp, tk_dp(m, vp)) : {SV.distinct(_) == True{} : Bool}
    hvd)


def vv_np(+nv: Nat, +vp: List<&2, Nat>, +np: Nat, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +hvd: {SV.distinct(vp) == True{} : Bool}, +v: Nat, +hv: {SV.mem(v, OW.ndrop(np, vp)) == True{} : Bool}) -> {SV.mem(v, pins) == False{} : Bool}:
  (%hpn : {SV.mem(v, _) == False{} : Bool}
    BI.disj_mem(OW.ndrop(np, vp), SO.ntake(np, vp), BI.disj_swap(SO.ntake(np, vp), OW.ndrop(np, vp), BI.dist_disj(SO.ntake(np, vp), OW.ndrop(np, vp), dist_app(np, vp, hvd))), v, hv))

# the plan's unknowns are free variables
def sub_free(+nv: Nat, +vp: List<&2, Nat>, +np: Nat, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +hvd: {SV.distinct(vp) == True{} : Bool}, +hpo: {PL.pars_ok(nv, vp) == True{} : Bool}, ws: List<&2, Nat>, +hws: {L.subl(ws, OW.ndrop(np, vp)) == True{} : Bool}) -> {L.subl(ws, SV.free(nv, 0n, pins)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      +hv = L.subl_hd(v, t, OW.ndrop(np, vp), hws)
      L.band_i(SV.mem(v, SV.free(nv, 0n, pins)), L.subl(t, SV.free(nv, 0n, pins)), PM.free_mem(nv, 0n, pins, v, {==}, lt_of_mem(nv, vp, v, hpo, L.subl_mem(v, OW.ndrop(np, vp), vp, hv, subl_dp(np, vp))), vv_np(nv, vp, np, pins, hpn, hvd, v, hv)), sub_free(nv, vp, np, pins, hpn, hvd, hpo, t, L.subl_tl(v, t, OW.ndrop(np, vp), hws)))

def mem_tkdp(+u: Nat, +np: Nat, +vp: List<&2, Nat>, +h: {SV.mem(u, vp) == True{} : Bool}) -> {SV.mem(u, ST.app(SO.ntake(np, vp), OW.ndrop(np, vp))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, ST.app(SO.ntake(np, vp), OW.ndrop(np, vp)), vp, tk_dp(np, vp)) : {SV.mem(u, _) == True{} : Bool}
    h)

def nt_pins(+u: Nat, +np: Nat, +vp: List<&2, Nat>, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +h: {SV.mem(u, pins) == False{} : Bool}) -> {SV.mem(u, SO.ntake(np, vp)) == False{} : Bool}:
  (%Equal.sym(List<&2, Nat>, SO.ntake(np, vp), pins, hpn) : {SV.mem(u, _) == False{} : Bool}
    h)

# and every free variable is one of them
def sub_vv(+nv: Nat, +vp: List<&2, Nat>, +np: Nat, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +hvd: {SV.distinct(vp) == True{} : Bool}, +hp: {PL.present(vp, nv, 0n) == True{} : Bool}, ws: List<&2, Nat>, +hws: {L.subl(ws, SV.free(nv, 0n, pins)) == True{} : Bool}) -> {L.subl(ws, OW.ndrop(np, vp)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      +hu = L.subl_hd(u, t, SV.free(nv, 0n, pins), hws)
      +hmv = mem_of_pos(u, vp, PP.present0(vp, nv, u, hp, PM.free_lt(nv, 0n, pins, u, hu)))
      L.band_i(SV.mem(u, OW.ndrop(np, vp)), L.subl(t, OW.ndrop(np, vp)), mem_app_rf(u, SO.ntake(np, vp), OW.ndrop(np, vp), mem_tkdp(u, np, vp, hmv), nt_pins(u, np, vp, pins, hpn, PM.free_np(nv, 0n, pins, u, hu))), sub_vv(nv, vp, np, pins, hpn, hvd, hp, t, L.subl_tl(u, t, SV.free(nv, 0n, pins), hws)))

# The system in the sketch's order
# --------------------------------

# eqget reads the head of the list from k on
def eg_qd(xs: List<&2, E.QExpr>, k: Nat) -> {PL.eqget(xs, k) == OW.qhd(OW.qdrop(k, xs)) : E.QExpr}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+j:
      eg_qd(t, j)

def pk_iota.go(+full: List<&2, E.QExpr>, es: List<&2, E.QExpr>, +d: Nat, +h: {OW.qdrop(d, full) == es : List<&2, E.QExpr>}) -> {KP.pickk(full, 0n, ST.iota(CK.eqlen(es), d)) == es : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +he = Equal.trans(E.QExpr, PL.eqget(full, d), OW.qhd(OW.qdrop(d, full)), e, eg_qd(full, d), Equal.cong(List<&2, E.QExpr>, E.QExpr, y => OW.qhd(y), OW.qdrop(d, full), Con{e, t}, h))
      %Equal.sym(E.QExpr, PL.eqget(full, d), e, he) : {Con{_, KP.pickk(full, 0n, ST.iota(CK.eqlen(t), 1n+d))} == Con{e, t} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, KP.pickk(full, 0n, ST.iota(CK.eqlen(t), 1n+d)), t, pk_iota.go(full, t, 1n+d, OW.qdrop_step(d, full, e, t, h))) : {Con{e, _} == Con{e, t} : List<&2, E.QExpr>}
      {==}

# picking every equation in order gives the system back
def pk_iota(+full: List<&2, E.QExpr>) -> {KP.pickk(full, 0n, ST.iota(CK.eqlen(full), 0n)) == full : List<&2, E.QExpr>}:
  pk_iota.go(full, full, 0n, {==})

def elen_eq(es: List<&2, E.QExpr>) -> {DV.elen(es) == CK.eqlen(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      %Equal.sym(Nat, DV.elen(t), CK.eqlen(t), elen_eq(t)) : {1n+_ == 1n+CK.eqlen(t) : Nat}
      {==}

# lf + lp = nv, lp = np and np + le = nv: lf = le
def len_fr(+lf: Nat, +lp: Nat, +np: Nat, +le: Nat, +nv: Nat, +h1: {Nat.add(lf, lp) == nv : Nat}, +h2: {lp == np : Nat}, +h3: {Nat.add(np, le) == nv : Nat}) -> {lf == le : Nat}:
  PF.cancel_r(lf, lp, le, nv, h1, Equal.trans(Nat, Nat.add(le, lp), Nat.add(lp, le), nv, LN.add_comm(le, lp), (%Equal.sym(Nat, lp, np, h2) : {Nat.add(_, le) == nv : Nat}
    h3)))

def po_nv(+a: Nat, +b: Nat, +vp: List<&2, Nat>, +e: {a == b : Nat}, +h: {PL.pars_ok(a, vp) == True{} : Bool}) -> {PL.pars_ok(b, vp) == True{} : Bool}:
  %e : {PL.pars_ok(_, vp) == True{} : Bool}
  h

def pr_nv(+a: Nat, +b: Nat, +vp: List<&2, Nat>, +e: {a == b : Nat}, +h: {PL.present(vp, a, 0n) == True{} : Bool}) -> {PL.present(vp, b, 0n) == True{} : Bool}:
  %e : {PL.present(vp, _, 0n) == True{} : Bool}
  h

def dist_pins(+np: Nat, +vp: List<&2, Nat>, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +hvd: {SV.distinct(vp) == True{} : Bool}) -> {SV.distinct(pins) == True{} : Bool}:
  %hpn : {SV.distinct(_) == True{} : Bool}
  dist_l(SO.ntake(np, vp), OW.ndrop(np, vp), dist_app(np, vp, hvd))

def below_pins(+nv: Nat, +np: Nat, +vp: List<&2, Nat>, +pins: List<&2, Nat>, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +hpo: {PL.pars_ok(nv, vp) == True{} : Bool}) -> {SV.below(pins, nv) == True{} : Bool}:
  %hpn : {SV.below(_, nv) == True{} : Bool}
  below_of_pars(nv, SO.ntake(np, vp), pars_tk(nv, np, vp, hpo))

# an inverse with n rows, n the number of variables and of equations
def reg_of(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +us: List<&2, Nat>, +n: Nat, +h1: {DV.nlen(us) == n : Nat}, +h2: {DV.elen(es) == n : Nat}, inv: GJ.InvN(~F, DV.jac(~F, x, es, us), n)) -> DV.Regular(~F, x, es, us):
  match inv:
    case (+y, b):
      match b:
        case (iv, hr):
          (Equal.trans(Nat, DV.nlen(us), n, DV.elen(es), h1, Equal.sym(Nat, DV.elen(es), n, h2)), (y, (%Equal.sym(Nat, DV.nlen(us), n, h1) : DV.Inverse(~F, DV.jac(~F, x, es, us), y, _)
            iv)))

# an injective Jacobian with as many columns as rows is regular
def reg_blk(~F: O.OField, +x: M.Vec(~F), +eqs: List<&2, E.QExpr>, +ep: List<&2, Nat>, +vv: List<&2, Nat>, +hl: {SV.len(vv) == SV.len(ep) : Nat}, inj: @w: M.Vec(~F) -> {M.len(~F, w) == SV.len(ep) : Nat} -> {M.matvec(~F, DV.jac(~F, x, KP.pickk(eqs, 0n, ep), vv), w) == GJ.zeros(~F, SV.len(ep)) : M.Vec(~F)} -> {w == GJ.zeros(~F, SV.len(ep)) : M.Vec(~F)}) -> DV.Regular(~F, x, KP.pickk(eqs, 0n, ep), vv):
  +jp = DV.jac(~F, x, KP.pickk(eqs, 0n, ep), vv)
  +ha = PM.nrows_pick(~F, x, eqs, ep, vv)
  reg_of(~F, x, KP.pickk(eqs, 0n, ep), vv, SV.len(ep), Equal.trans(Nat, DV.nlen(vv), SV.len(vv), SV.len(ep), PM.nlen_sv(vv), hl), PM.elen_pick(eqs, ep), GJ.inv_of_inj(~F, jp, SV.len(ep), ha, GJ.rl_all(~F, jp, SV.len(ep), ha, rl_rw(~F, jp, SV.len(vv), SV.len(ep), hl, PM.rl_jac(~F, x, KP.pickk(eqs, 0n, ep), vv))), inj))


# the plan's box, read in block order
def hx_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<KI.dnum()>>, +ok: {PL.check.r(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +hb: BX.inbox(~KI.dnum(), ~F, ~H, gc, gr, x)) -> BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), LC.xperm(~F, x, vp)):
  (%Equal.sym(M.Vec(~F), LC.xperm(~F, x, vp), PP.zmap(~F, x, vp), xz_eq(~F, x, vp)) : BX.inbox(~KI.dnum(), ~F, ~H, PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), _)
    PP.un_in(~KI.dnum(), ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x, hb))

# a plan that checks, whose orders are the variables (the pins first) and
# the equations, makes every point of its box a regular point of the
# system in the free variables
def plan_regular(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<KI.dnum()>>, +ok: {PL.check.r(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +nv: Nat, +pins: List<&2, Nat>, +hgc: {KA.klen(~KI.dnum(), gc) == nv : Nat}, +hvl: {PL.nlen(vp) == nv : Nat}, +hvd: {SV.distinct(vp) == True{} : Bool}, +hel: {PL.nlen(ep) == CK.eqlen(eqs) : Nat}, +hpn: {SO.ntake(np, vp) == pins : List<&2, Nat>}, +x: M.Vec(~F), +hb: BX.inbox(~KI.dnum(), ~F, ~H, gc, gr, x)) -> DV.Regular(~F, x, eqs, SV.free(nv, 0n, pins)):
  +hcp = PP.cr_inner(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok)
  +hX = hx_of(~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x, hb)
  +hgr = PP.cp_len(~KI.dnum(), PL.reorder(vp, eqs, ep), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), np, bs, hcp)
  +hw = PP.cp_walk(~KI.dnum(), PL.reorder(vp, eqs, ep), PL.kperm(~KI.dnum(), gc, vp), PL.kperm(~KI.dnum(), gr, vp), np, bs, hcp)
  +hpo = po_nv(KA.klen(~KI.dnum(), gc), nv, vp, hgc, PP.cr_vp_lt(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok))
  +hpr = pr_nv(KA.klen(~KI.dnum(), gc), nv, vp, hgc, PP.cr_vp_has(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok))
  +hin = allin_all(eqs, ep, vp, KA.klen(~KI.dnum(), gc), PP.cr_vp_has(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok), PP.cr_below(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok))
  +hwl0 = hwl(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, bs, ep, np, hw)
  +hlv = Equal.trans(Nat, SV.len(vp), PL.nlen(vp), nv, Equal.sym(Nat, PL.nlen(vp), SV.len(vp), PB.nlen_sv(vp)), hvl)
  +hnv = Equal.trans(Nat, Nat.add(np, SV.len(ep)), SV.len(vp), nv, hwl0, hlv)
  +hle = Equal.trans(Nat, SV.len(ep), PL.nlen(ep), CK.eqlen(eqs), Equal.sym(Nat, PL.nlen(ep), SV.len(ep), PB.nlen_sv(ep)), hel)
  +hnl = KA.natle_rw(np, Nat.add(np, SV.len(ep)), SV.len(vp), hwl0, natle_addr(np, SV.len(ep)))
  +hlp = Equal.trans(Nat, SV.len(pins), SV.len(SO.ntake(np, vp)), np, len_cong(pins, SO.ntake(np, vp), Equal.sym(List<&2, Nat>, SO.ntake(np, vp), pins, hpn)), len_tk(np, vp, hnl))
  +hfl = PF.free_len(nv, pins, dist_pins(np, vp, pins, hpn, hvd), below_pins(nv, np, vp, pins, hpn, hpo))
  +hlf = len_fr(SV.len(SV.free(nv, 0n, pins)), SV.len(pins), np, SV.len(ep), nv, hfl, hlp, hnv)
  +hlvv = len_dp(np, vp, SV.len(ep), Equal.sym(Nat, Nat.add(np, SV.len(ep)), SV.len(vp), hwl0))
  +hreg = reg_blk(~F, x, eqs, ep, OW.ndrop(np, vp), hlvv, w => lw => e => rinj(~F, ~H, x, vp, eqs, gc, gr, hX, hgr, hvd, bs, ep, np, OW.ndrop(np, vp), {==}, hw, hin, w, lw, e))
  +hga = PF.below_iota(ep, CK.eqlen(eqs), below_of_pars(CK.eqlen(eqs), ep, PP.cr_ep_lt(~KI.dnum(), eqs, gc, gr, vp, ep, np, bs, ok)))
  +huv = sub_free(nv, vp, np, pins, hpn, hvd, hpo, OW.ndrop(np, vp), L.subl_refl(OW.ndrop(np, vp)))
  +hvu = sub_vv(nv, vp, np, pins, hpn, hvd, hpr, SV.free(nv, 0n, pins), L.subl_refl(SV.free(nv, 0n, pins)))
  +hn = Equal.trans(Nat, SV.len(ST.iota(CK.eqlen(eqs), 0n)), CK.eqlen(eqs), SV.len(SV.free(nv, 0n, pins)), PF.iota_len(CK.eqlen(eqs), 0n), Equal.sym(Nat, SV.len(SV.free(nv, 0n, pins)), CK.eqlen(eqs), Equal.trans(Nat, SV.len(SV.free(nv, 0n, pins)), SV.len(ep), CK.eqlen(eqs), hlf, hle)))
  +hfe = Equal.trans(Nat, DV.elen(eqs), CK.eqlen(eqs), SV.len(SV.free(nv, 0n, pins)), elen_eq(eqs), Equal.sym(Nat, SV.len(SV.free(nv, 0n, pins)), CK.eqlen(eqs), Equal.trans(Nat, SV.len(SV.free(nv, 0n, pins)), SV.len(ep), CK.eqlen(eqs), hlf, hle)))
  reg_of(~F, x, eqs, SV.free(nv, 0n, pins), SV.len(SV.free(nv, 0n, pins)), PM.nlen_sv(SV.free(nv, 0n, pins)), hfe, (%pk_iota(eqs) : GJ.InvN(~F, DV.jac(~F, x, _, SV.free(nv, 0n, pins)), SV.len(SV.free(nv, 0n, pins)))
    PM.perm_inv(~F, x, eqs, ep, ST.iota(CK.eqlen(eqs), 0n), OW.ndrop(np, vp), SV.free(nv, 0n, pins), hga, BI.dist_r(SO.ntake(np, vp), OW.ndrop(np, vp), dist_app(np, vp, hvd)), PM.free_dist(nv, 0n, pins), huv, hvu, hn, hreg)))

# The verdict's shape check
# -------------------------

def nl_eq_ok(xs: List<&2, Nat>, ys: List<&2, Nat>, +h: {SO.nl_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +t}:
      absurd({Nil{} == Con{b, t} : List<&2, Nat>}, KA.ft(h))
    case Con{+a, +s} Nil{}:
      absurd({Con{a, s} == Nil{} : List<&2, Nat>}, KA.ft(h))
    case Con{+a, +s} Con{+b, +t}:
      %L.eq_ok(a, b, L.band_l(SV.eq(a, b), SO.nl_eq(s, t), h)) : {Con{a, s} == Con{_, t} : List<&2, Nat>}
      %nl_eq_ok(s, t, L.band_r(SV.eq(a, b), SO.nl_eq(s, t), h)) : {Con{a, s} == Con{a, _} : List<&2, Nat>}
      {==}


# a plan that checks and passes the shape check makes every point of the
# box a regular point of the system in the free variables
def reg_plan(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +eqs: List<&2, E.QExpr>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +nv: Nat, +pins: List<&2, Nat>, p: PL.Plan<KI.dnum()>, +hc: {PL.check(~KI.dnum(), eqs, gc, gr, p) == True{} : Bool}, +hs: {SO.shape(nv, CK.eqlen(eqs), gc, pins, p) == True{} : Bool}, +x: M.Vec(~F), +hb: BX.inbox(~KI.dnum(), ~F, ~H, gc, gr, x)) -> DV.Regular(~F, x, eqs, SV.free(nv, 0n, pins)):
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      +hgc = KA.nateq_ok(KA.klen(~KI.dnum(), gc), nv, KA.band_l(KA.nateq(KA.klen(~KI.dnum(), gc), nv), KA.band(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins)))), hs))
      +s1 = KA.band_r(KA.nateq(KA.klen(~KI.dnum(), gc), nv), KA.band(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins)))), hs)
      +hvl = KA.nateq_ok(PL.nlen(vp), nv, KA.band_l(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins))), s1))
      +s2 = KA.band_r(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins))), s1)
      +hvd = KA.band_l(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins)), s2)
      +s3 = KA.band_r(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins)), s2)
      +hel = KA.nateq_ok(PL.nlen(ep), CK.eqlen(eqs), KA.band_l(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins), s3))
      +hpn = nl_eq_ok(SO.ntake(np, vp), pins, KA.band_r(KA.nateq(PL.nlen(ep), CK.eqlen(eqs)), SO.nl_eq(SO.ntake(np, vp), pins), s3))
      plan_regular(~F, ~H, eqs, gc, gr, vp, ep, np, bs, hc, nv, pins, hgc, hvl, hvd, hel, hpn, x, hb)

# The law
# -------

# a True verdict: every point of the box is a regular point of the system
# solved in the free variables
def regular_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}, +y: M.Vec(~F), +hb: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y)) -> DV.Regular(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(x))):
  reg_plan(~F, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.nvars(sk), SO.Out.pins(x), SO.Out.plan(x), SPF.hD(sk, g0, x, h), SPF.hS(sk, g0, x, h), y, hb)

def solve_regular(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x: M.Vec(~F), +h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x), m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(SO.solve_l(sk, g0, l)))):
  regular_of(~F, ~H, sk, g0, SO.search_lw(sk, g0, l, 7n), ok, x, h)
