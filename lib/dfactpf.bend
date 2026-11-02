# bend-cad: the facts of an honest classification hold (PLAN-sk13b B6).
# Proofs only.
#
# In any ordered field, at a geometry x where the system solved holds,
# every equation of a constraint that is not red holds as a fact: some
# segment of its drop's nd has length 0, or the equation holds with its
# constraint's direction statement. By induction along the constraints
# (KF(c): the facts of the kept constraints before c, spec/solve.bend's
# first half of dfacts, all hold), each step reading one Fate of the
# extended Honest (spec/_draft13b.bend):
# - an equation the solver solves holds at x;
# - a degree-0 drop's reason names only equations of the system solved,
#   so its combination is 0 at x, and the reason's identity holds in every
#   ordered field (lib/identpf.bend: ident_all);
# - a direction drop's facts are KF(c)'s and c's own earlier solved
#   equations, so its derivation's conclusion holds wherever its nd
#   segments have nonzero length (lib/dirpf.bend: sound), and proves the
#   equation (Proves: the same polynomial, or c's direction statement,
#   which is the equation up to sign).
# A constraint's direction statement holds exactly where its one equation
# does (dstat_ok and its converse, eq_r, below).
#
# Generated from tools/drafts/dfactpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./dirpf.bend as DP
import ./hreadpf.bend as HR
import ./clslpf.bend as CL
import ./identpf.bend as ID
import ./dropok.bend as DK
import ./vrdpf.bend as VR
import ./dpassmpf.bend as DPM
import ./conflict.bend as CO
import ./dmemopf.bend as DMO


def absurd(-A: Type, x: Empty) -> A:
  match x:

# Which constraint an equation is from
# ------------------------------------

# position m of the equations qs (owners own) is equation r of the
# constraint k of rs that owns it
def At(+es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +own: List<&2, Nat>, +qs: List<&2, E.QExpr>, +m: Nat) -> Data:
  Sigma<&2, &2, SK.Constraint, k => Sigma<&2, &2, Nat, r => SK.Both({SV.rec_at(rs, SV.nth(own, m)) == Some{k} : Maybe<&2, SK.Constraint>}, SK.Both({SV.lt(r, SV.neqs(SK.Constraint.eqs(es, k))) == True{} : Bool}, {SV.eqat(qs, m) == SV.eqat(SK.Constraint.eqs(es, k), r) : E.QExpr}))>>

def rd_con(rs: List<&2, SK.Rec>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, t}:
      True{}

def rd_at(i: Nat, rs: List<&2, SK.Rec>, +r: SK.Rec, +t: List<&2, SK.Rec>, h: {KB.rdrop(i, rs) == Con{r, t} : List<&2, SK.Rec>}) -> {SV.rec_at(rs, i) == Some{SV.rec.k(r)} : Maybe<&2, SK.Constraint>}:
  match i rs:
    case 0n Nil{}:
      absurd({SV.rec_at(Nil{}, 0n) == Some{SV.rec.k(r)} : Maybe<&2, SK.Constraint>}, KA.ft(Equal.cong(List<&2, SK.Rec>, Bool, x => rd_con(x), Nil{}, Con{r, t}, h)))
    case 0n Con{x, xt}:
      Equal.cong(List<&2, SK.Rec>, Maybe<&2, SK.Constraint>, y => SV.rec_at(y, 0n), Con{x, xt}, Con{r, t}, h)
    case 1n+j Nil{}:
      absurd({SV.rec_at(Nil{}, 1n+j) == Some{SV.rec.k(r)} : Maybe<&2, SK.Constraint>}, KA.ft(Equal.cong(List<&2, SK.Rec>, Bool, x => rd_con(x), Nil{}, Con{r, t}, h)))
    case 1n+j Con{x, xt}:
      rd_at(j, xt, r, t, h)

# within the block of record i's equations (xs, from its r-th); past it,
# the rest (ih)
def at.b(xs: List<&2, E.QExpr>, +es: List<&2, SK.Ent>, +k: SK.Constraint, +r: Nat, +hq: {OW.qdrop(r, SK.Constraint.eqs(es, k)) == xs : List<&2, E.QExpr>}, +i: Nat, +t: List<&2, SK.Rec>, +rs: List<&2, SK.Rec>, +hk: {SV.rec_at(rs, i) == Some{k} : Maybe<&2, SK.Constraint>},
  m: Nat, hm: {SV.lt(m, SV.neqs(SK.cat(xs, SK.Sketch.eqs.go(es, t)))) == True{} : Bool},
  ih: @m2: Nat -> {SV.lt(m2, SV.neqs(SK.Sketch.eqs.go(es, t))) == True{} : Bool} -> At(es, rs, SV.owners.go(es, t, 1n+i), SK.Sketch.eqs.go(es, t), m2)) -> At(es, rs, SV.cat(SV.reps(SV.neqs(xs), i), SV.owners.go(es, t, 1n+i)), SK.cat(xs, SK.Sketch.eqs.go(es, t)), m):
  match xs m:
    case Nil{} m:
      ih(m, hm)
    case Con{+e, +xt} 0n:
      (k, (r, (hk, (SP.lt_qdrop(SK.Constraint.eqs(es, k), r, e, xt, hq), Equal.sym(E.QExpr, SV.eqat(SK.Constraint.eqs(es, k), r), e, OW.eqat_of(SK.Constraint.eqs(es, k), r, e, xt, hq))))))
    case Con{+e, +xt} 1n+q:
      at.b(xt, es, k, 1n+r, OW.qdrop_step(r, SK.Constraint.eqs(es, k), e, xt, hq), i, t, rs, hk, q, hm, ih)

def at.go(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +rs: List<&2, SK.Rec>, +hd: {KB.rdrop(i, rs) == cs : List<&2, SK.Rec>}, m: Nat, hm: {SV.lt(m, SV.neqs(SK.Sketch.eqs.go(es, cs))) == True{} : Bool}) -> At(es, rs, SV.owners.go(es, cs, i), SK.Sketch.eqs.go(es, cs), m):
  match cs:
    case Nil{}:
      absurd(At(es, rs, Nil{}, Nil{}, m), KA.ft(KB.lt_zero(m, hm)))
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      at.go(es, t, 1n+i, rs, KB.rdrop_step(i, rs, SK.Rec{id, True{}, k}, t, hd), m, hm)
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      +hd2 = KB.rdrop_step(i, rs, SK.Rec{id, False{}, k}, t, hd)
      at.b(SK.Constraint.eqs(es, k), es, k, 0n, {==}, i, t, rs, rd_at(i, rs, SK.Rec{id, False{}, k}, t, hd), m, hm, m2 => h2 => at.go(es, t, 1n+i, rs, hd2, m2, h2))

# the sketch's equation m is equation r of k, its owner's constraint
def AtK(+sk: SK.Sketch, +m: Nat) -> Data:
  Sigma<&2, &2, SK.Constraint, k => Sigma<&2, &2, Nat, r => SK.Both({SV.kind_at(sk, SV.nth(SV.owners(sk), m)) == Some{k} : Maybe<&2, SK.Constraint>}, SK.Both({SV.lt(r, SV.neqs(SK.Constraint.eqs(SV.ents(sk), k))) == True{} : Bool}, {SV.eqat(SK.Sketch.eqs(sk), m) == SV.eqat(SK.Constraint.eqs(SV.ents(sk), k), r) : E.QExpr}))>>

def at(sk: SK.Sketch, +m: Nat, hm: {SV.lt(m, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> AtK(sk, m):
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      at.go(es, cs, 0n, cs, {==}, m, hm)

# A direction statement and its constraint's equation
# ---------------------------------------------------


def dsome(m: Maybe<&2, DR.DStat>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

# where equation r of k vanishes, k's direction statement holds (k has one
# equation when it has a statement)
def stat_r(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, r: Nat, hr: {SV.lt(r, SV.neqs(SK.Constraint.eqs(es, k))) == True{} : Bool}, he: {O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, k), r)) == O.zero(F) : O.C(F)}) -> DP.StatHolds(~F, env, es, DR.dstat(es, k)):
  match k:
    case SK.Parallel{+a, +b}:
      match r:
        case 0n:
          DP.dstat_ok(~F, env, es, SK.Parallel{a, b}, (he, Unit{}))
        case 1n+q:
          absurd(DP.StatHolds(~F, env, es, DR.dstat(es, SK.Parallel{a, b})), KA.ft(KB.lt_zero(q, hr)))
    case SK.Perpendicular{+a, +b}:
      match r:
        case 0n:
          DP.dstat_ok(~F, env, es, SK.Perpendicular{a, b}, (he, Unit{}))
        case 1n+q:
          absurd(DP.StatHolds(~F, env, es, DR.dstat(es, SK.Perpendicular{a, b})), KA.ft(KB.lt_zero(q, hr)))
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      match r:
        case 0n:
          DP.dstat_ok(~F, env, es, SK.Angle{a, ra, b, rb, c, s}, (he, Unit{}))
        case 1n+q:
          absurd(DP.StatHolds(~F, env, es, DR.dstat(es, SK.Angle{a, ra, b, rb, c, s})), KA.ft(KB.lt_zero(q, hr)))
    case SK.OnLine{+p, +a}:
      match r:
        case 0n:
          DP.dstat_ok(~F, env, es, SK.OnLine{p, a}, (he, Unit{}))
        case 1n+q:
          absurd(DP.StatHolds(~F, env, es, DR.dstat(es, SK.OnLine{p, a})), KA.ft(KB.lt_zero(q, hr)))
    case SK.Coincident{x1, x2}:
      Unit{}
    case SK.Horizontal{x1, x2}:
      Unit{}
    case SK.Vertical{x1, x2}:
      Unit{}
    case SK.Concentric{x1, x2}:
      Unit{}
    case SK.EqualRadius{x1, x2}:
      Unit{}
    case SK.Fix{x1, x2}:
      Unit{}
    case SK.Distance{x1, x2, x3}:
      Unit{}
    case SK.HDistance{x1, x2, x3}:
      Unit{}
    case SK.VDistance{x1, x2, x3}:
      Unit{}
    case SK.Radius{x1, x2}:
      Unit{}
    case SK.Diameter{x1, x2}:
      Unit{}
    case SK.LineDistance{x1, x2, x3, x4, x5}:
      Unit{}
    case SK.EqualLength{x1, x2}:
      Unit{}
    case SK.OnCircle{x1, x2}:
      Unit{}
    case SK.Midpoint{x1, x2}:
      Unit{}
    case SK.Symmetric{x1, x2, x3}:
      Unit{}

# dot(a, b) is cross(a, i b)
def perp_eq(~F: O.OField, +env: List<&2, O.C(F)>, +a: SK.VE, +b: SK.VE, h: {DP.evc(~F, env, a, DR.imul(b)) == O.zero(F) : O.C(F)}) -> {DP.ev(~F, env, SK.VE.dot(a, b)) == O.zero(F) : O.C(F)}:
  FO.cert1(~F, DP.ev(~F, env, SK.VE.dot(a, b)), O.one(F), DP.evc(~F, env, a, DR.imul(b)), FR.fring_eq(~F, [DP.ev(~F, env, SK.VE.x(a)), DP.ev(~F, env, SK.VE.y(a)), DP.ev(~F, env, SK.VE.x(b)), DP.ev(~F, env, SK.VE.y(b))],
    E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZNeg{E.ZVar{3n}}}}}, {==}), h)

# an Angle's statement cross(a, conj(c + is) w) = 0 gives its equation
# cross(rot(c, s) a', w) = 0, a' = sign a: the equation is sign times the
# statement, less sign dot(a, w) (s + (-s))
def eq_angle.go(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +w1: O.C(F), +w2: O.C(F), +qc: S.Q, +qs: S.Q, +sg: O.C(F),
  h: {O.sub(~F, O.mul(F, a1, O.add(F, O.mul(F, O.ofq(~F, S.Q.neg(qs)), w1), O.mul(F, O.ofq(~F, qc), w2))), O.mul(F, a2, O.sub(~F, O.mul(F, O.ofq(~F, qc), w1), O.mul(F, O.ofq(~F, S.Q.neg(qs)), w2)))) == O.zero(F) : O.C(F)})
  -> {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)) == O.zero(F) : O.C(F)}:
  FO.cert2(~F, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a2))), w2), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, sg, a1)), O.mul(F, O.ofq(~F, qc), O.mul(F, sg, a2))), w1)),
    sg, O.sub(~F, O.mul(F, a1, O.add(F, O.mul(F, O.ofq(~F, S.Q.neg(qs)), w1), O.mul(F, O.ofq(~F, qc), w2))), O.mul(F, a2, O.sub(~F, O.mul(F, O.ofq(~F, qc), w1), O.mul(F, O.ofq(~F, S.Q.neg(qs)), w2)))),
    O.neg(F, O.mul(F, sg, O.add(F, O.mul(F, a1, w1), O.mul(F, a2, w2)))), O.add(F, O.ofq(~F, S.Q.neg(qs)), O.ofq(~F, qs)),
    FR.fring_eq(~F, [a1, a2, w1, w2, O.ofq(~F, qc), O.ofq(~F, qs), O.ofq(~F, S.Q.neg(qs)), sg],
      E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{7n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{7n}, E.ZVar{1n}}}}, E.ZVar{3n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{7n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{7n}, E.ZVar{1n}}}}, E.ZVar{2n}}},
      E.ZAdd{E.ZMul{E.ZVar{7n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZVar{6n}, E.ZVar{3n}}}}}},
        E.ZMul{E.ZNeg{E.ZMul{E.ZVar{7n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}}, E.ZAdd{E.ZVar{6n}, E.ZVar{5n}}}}, {==}),
    h, DP.negs0(~F, qs))


def eq_angle.s(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +qc: S.Q, s: E.QExpr, hs: DP.StatHolds(~F, env, es, DR.dstat.angle(es, a, ra, b, rb, E.QCst{qc}, s)), hd: {dsome(DR.dstat.angle(es, a, ra, b, rb, E.QCst{qc}, s)) == True{} : Bool})
  -> {DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}:
  match s:
    case E.QCst{+qs}:
      %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra)))), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a)))), DP.rev_x(~F, env, SK.seg(es, a), ra)) : {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), _), O.mul(F, O.ofq(~F, qs), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), _), O.mul(F, O.ofq(~F, qc), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))))) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a)))), DP.rev_y(~F, env, SK.seg(es, a), ra)) : {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofq(~F, qc), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, O.ofq(~F, qs), _)), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, O.add(F, O.mul(F, O.ofq(~F, qs), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, O.ofq(~F, qc), _)), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))))) == O.zero(F) : O.C(F)}
      eq_angle.go(~F, DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))), qc, qs, DP.rsign(~F, ra), hs)
    case E.QVar{i}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, E.QVar{i}, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QAdd{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, E.QAdd{x, y}, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QSub{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, E.QSub{x, y}, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QMul{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, E.QMul{x, y}, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QNeg{x}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QCst{qc}, E.QNeg{x}, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))

def eq_angle.cs(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, c: E.QExpr, +s: E.QExpr, hs: DP.StatHolds(~F, env, es, DR.dstat.angle(es, a, ra, b, rb, c, s)), hd: {dsome(DR.dstat.angle(es, a, ra, b, rb, c, s)) == True{} : Bool})
  -> {DP.ev(~F, env, SK.VE.cross(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}:
  match c:
    case E.QCst{+qc}:
      eq_angle.s(~F, env, es, a, ra, b, rb, qc, s, hs, hd)
    case E.QVar{i}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QVar{i}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QAdd{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QAdd{x, y}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QSub{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QSub{x, y}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QMul{x, y}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QMul{x, y}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case E.QNeg{x}:
      absurd({DP.ev(~F, env, SK.VE.cross(SK.VE.rot(E.QNeg{x}, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}, KA.ft(hd))


# where k's direction statement holds, its equation does (the converse of
# stat_r)
def eq_r(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, r: Nat, hr: {SV.lt(r, SV.neqs(SK.Constraint.eqs(es, k))) == True{} : Bool}, hs: DP.StatHolds(~F, env, es, DR.dstat(es, k)), hd: {dsome(DR.dstat(es, k)) == True{} : Bool}) -> {O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, k), r)) == O.zero(F) : O.C(F)}:
  match k:
    case SK.Parallel{+a, +b}:
      match r:
        case 0n:
          hs
        case 1n+q:
          absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Parallel{a, b}), 1n+q)) == O.zero(F) : O.C(F)}, KA.ft(KB.lt_zero(q, hr)))
    case SK.Perpendicular{+a, +b}:
      match r:
        case 0n:
          perp_eq(~F, env, DR.zseg(es, a), DR.zseg(es, b), hs)
        case 1n+q:
          absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Perpendicular{a, b}), 1n+q)) == O.zero(F) : O.C(F)}, KA.ft(KB.lt_zero(q, hr)))
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      match r:
        case 0n:
          eq_angle.cs(~F, env, es, a, ra, b, rb, c, s, hs, hd)
        case 1n+q:
          absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Angle{a, ra, b, rb, c, s}), 1n+q)) == O.zero(F) : O.C(F)}, KA.ft(KB.lt_zero(q, hr)))
    case SK.OnLine{+p, +a}:
      match r:
        case 0n:
          hs
        case 1n+q:
          absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.OnLine{p, a}), 1n+q)) == O.zero(F) : O.C(F)}, KA.ft(KB.lt_zero(q, hr)))
    case SK.Coincident{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Coincident{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Horizontal{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Horizontal{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Vertical{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Vertical{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Concentric{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Concentric{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.EqualRadius{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.EqualRadius{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Fix{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Fix{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Distance{+x1, +x2, +x3}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Distance{x1, x2, x3}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.HDistance{+x1, +x2, +x3}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.HDistance{x1, x2, x3}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.VDistance{+x1, +x2, +x3}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.VDistance{x1, x2, x3}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Radius{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Radius{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Diameter{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Diameter{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.LineDistance{+x1, +x2, +x3, +x4, +x5}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.LineDistance{x1, x2, x3, x4, x5}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.EqualLength{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.EqualLength{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.OnCircle{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.OnCircle{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Midpoint{+x1, +x2}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Midpoint{x1, x2}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))
    case SK.Symmetric{+x1, +x2, +x3}:
      absurd({O.eval(~F, env, SV.eqat(SK.Constraint.eqs(es, SK.Symmetric{x1, x2, x3}), r)) == O.zero(F) : O.C(F)}, KA.ft(hd))

# Lengths
# -------

# a segment has positive squared length, or 0
def ls_seg.c(~F: O.OField, +v: O.C(F), h: O.le(~F, O.zero(F), v)) -> DP.DOr(O.lt(F, O.zero(F), v), {v == O.zero(F) : O.C(F)}):
  match h:
    case Inl{l}:
      Inl{l}
    case Inr{e}:
      Inr{Equal.sym(O.C(F), O.zero(F), v, e)}

def ls_seg(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat) -> DP.DOr(DR.Long(~F, env, es, s), {DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))) == O.zero(F) : O.C(F)}):
  +x = DP.ev(~F, env, SK.VE.x(DR.zseg(es, s)))
  +y = DP.ev(~F, env, SK.VE.y(DR.zseg(es, s)))
  ls_seg.c(~F, DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))), FO.nonneg_add(~F, O.mul(F, x, x), O.mul(F, y, y), FO.sq_nonneg(~F, x), FO.sq_nonneg(~F, y)))

def ls_dec.c(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat, +t: List<&2, Nat>, a: DP.DOr(DR.Long(~F, env, es, s), {DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))) == O.zero(F) : O.C(F)}), b: DP.DOr(DR.Longs(~F, env, es, t), DP.Short(~F, env, es, t)))
  -> DP.DOr(DR.Longs(~F, env, es, Con{s, t}), DP.Short(~F, env, es, Con{s, t})):
  match a:
    case Inl{l}:
      match b:
        case Inl{lt}:
          Inl{(l, lt)}
        case Inr{st}:
          Inr{Inr{st}}
    case Inr{z}:
      Inr{Inl{z}}

# every segment of nd has positive squared length, or some has length 0
def ls_dec(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>) -> DP.DOr(DR.Longs(~F, env, es, nd), DP.Short(~F, env, es, nd)):
  match nd:
    case Nil{}:
      Inl{Unit{}}
    case Con{+s, +t}:
      ls_dec.c(~F, env, es, s, t, ls_seg(~F, env, es, s), ls_dec(~F, env, es, t))

def longs_mem.c(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +x: Nat, +t: List<&2, Nat>, +s: Nat, b: Bool, eb: {SV.eq(s, x) == b : Bool}, hm: {SV.bor(b, SV.mem(s, t)) == True{} : Bool}, +hl: DR.Longs(~F, env, es, Con{x, t}),
  ih: {SV.mem(s, t) == True{} : Bool} -> DR.Long(~F, env, es, s)) -> DR.Long(~F, env, es, s):
  match b:
    case True{}:
      (+lx, lt) = hl
      %Equal.sym(Nat, s, x, LI.eq_ok(s, x, eb)) : DR.Long(~F, env, es, _)
      lx
    case False{}:
      ih(hm)

def longs_mem(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>, +s: Nat, hm: {SV.mem(s, nd) == True{} : Bool}, +hl: DR.Longs(~F, env, es, nd)) -> DR.Long(~F, env, es, s):
  match nd:
    case Nil{}:
      absurd(DR.Long(~F, env, es, s), KA.ft(hm))
    case Con{+x, +t}:
      longs_mem.c(~F, env, es, x, t, s, SV.eq(s, x), {==}, hm, hl, h => longs_mem(~F, env, es, t, s, h, DP.snd(DR.Long(~F, env, es, x), DR.Longs(~F, env, es, t), hl)))

# nd within nd2: where nd2's segments are long, so are nd's
def longs_sub(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hs: {SV.sub(xs, ys) == True{} : Bool}, +hl: DR.Longs(~F, env, es, ys)) -> DR.Longs(~F, env, es, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (longs_mem(~F, env, es, ys, x, LI.band_l(SV.mem(x, ys), SV.sub(t, ys), hs), hl), longs_sub(~F, env, es, t, ys, LI.band_r(SV.mem(x, ys), SV.sub(t, ys), hs), hl))

# The honest classification read once
# -----------------------------------
# As lib/hreadpf.bend reads sk-13a's Honest: every class drops only its own
# constraint's equations, each below the number of equations (HR.hfacts),
# read out of each Fate as Bool facts and the Fate put back.


def at_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, b: Bool, +k: Nat, h: DH.drops_ok.at(sk, cls, R, D, c, d, b, k)) -> ({SV.bor(b, SV.bnot(SV.mem(k, d))) == True{} : Bool} & DH.drops_ok.at(sk, cls, R, D, c, d, b, k)):
  match b:
    case True{}:
      ({==}, h)
    case False{}:
      HR.at_f(k, d, h)

def dg_cmb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +o: Nat, +t: List<&2, Nat>, +k: Nat,
  p: ({SV.bor(SV.eq(o, c), SV.bnot(SV.mem(k, d))) == True{} : Bool} & DH.drops_ok.at(sk, cls, R, D, c, d, SV.eq(o, c), k)), q: ({HR.dn(t, d, c, 1n+k) == True{} : Bool} & DH.drops_ok.go(sk, cls, R, D, c, d, t, 1n+k)))
  -> ({HR.dn(Con{o, t}, d, c, k) == True{} : Bool} & DH.drops_ok.go(sk, cls, R, D, c, d, Con{o, t}, k)):
  match p:
    case (+ha, a2):
      match q:
        case (+hr, r2):
          (LI.band_i(SV.bor(SV.eq(o, c), SV.bnot(SV.mem(k, d))), HR.dn(t, d, c, 1n+k), ha, hr), (a2, r2))

def dg_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, own_s: List<&2, Nat>, +k: Nat, h: DH.drops_ok.go(sk, cls, R, D, c, d, own_s, k)) -> ({HR.dn(own_s, d, c, k) == True{} : Bool} & DH.drops_ok.go(sk, cls, R, D, c, d, own_s, k)):
  match own_s:
    case Nil{}:
      ({==}, h)
    case Con{+o, +t}:
      match h:
        case (a, r):
          dg_cmb(sk, cls, R, D, c, d, o, t, k, at_rb(sk, cls, R, D, c, d, SV.eq(o, c), k, a), dg_rb(sk, cls, R, D, c, d, t, 1n+k, r))

def dok_cmb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +hb: {SV.band(SV.distinct(d), SV.below(d, SV.neqs(SK.Sketch.eqs(sk)))) == True{} : Bool}, q: ({HR.dn(SV.owners(sk), d, c, 0n) == True{} : Bool} & DH.drops_ok.go(sk, cls, R, D, c, d, SV.owners(sk), 0n)))
  -> ({HR.pk_d(sk, c, d) == True{} : Bool} & DH.DropsOk(sk, cls, R, D, c, d)):
  match q:
    case (+hdn, g2):
      +hbl = LI.band_r(SV.distinct(d), SV.below(d, SV.neqs(SK.Sketch.eqs(sk))), hb)
      (LI.band_i(KB.allo(SV.owners(sk), d, c), SV.below(d, SV.neqs(SK.Sketch.eqs(sk))), HR.allo_of(SV.owners(sk), SV.neqs(SK.Sketch.eqs(sk)), d, c, d, OW.len_owners(sk), hdn, hbl, LI.subl_refl(d)), hbl), (hb, g2))

def dok_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, h: DH.DropsOk(sk, cls, R, D, c, d)) -> ({HR.pk_d(sk, c, d) == True{} : Bool} & DH.DropsOk(sk, cls, R, D, c, d)):
  match h:
    case (+hb, g):
      dok_cmb(sk, cls, R, D, c, d, hb, dg_rb(sk, cls, R, D, c, d, SV.owners(sk), 0n, g))

def ka_cmb(-A: Type, -B: Type, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, nr: A, q: ({HR.pk_d(sk, c, d) == True{} : Bool} & DH.DropsOk(sk, cls, R, D, c, d)), r2: B)
  -> ({HR.pk_d(sk, c, d) == True{} : Bool} & (A & (DH.DropsOk(sk, cls, R, D, c, d) & B))):
  match q:
    case (+hp, dk2):
      (hp, (nr, (dk2, r2)))

def kok_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, h: DH.KeptOk(sk, cls, R, D, c, dd)) -> ({HR.pk_d(sk, c, SV.drops(dd)) == True{} : Bool} & DH.KeptOk(sk, cls, R, D, c, dd)):
  match h:
    case (nr, r1):
      match r1:
        case (dk, r2):
          ka_cmb(SV.NoRefute2(sk, R, c), (DH.DropsNd(sk, cls, R, D, c, dd) & (SV.Matchable(SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))) & ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} -> &i: Nat -> ({SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool} & SV.NotImplied(sk, R, c, i))))),
            sk, cls, R, D, c, SV.drops(dd), nr, dok_rb(sk, cls, R, D, c, SV.drops(dd), dk), r2)

def aok_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, h: DH.AmberOk(sk, cls, R, D, c, dd)) -> ({HR.pk_d(sk, c, SV.drops(dd)) == True{} : Bool} & DH.AmberOk(sk, cls, R, D, c, dd)):
  match h:
    case (nr, r1):
      match r1:
        case (dk, r2):
          ka_cmb(SV.NoRefute2(sk, R, c), (DH.DropsNd(sk, cls, R, D, c, dd) & ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} & DH.AllImplied(sk, R, c))),
            sk, cls, R, D, c, SV.drops(dd), nr, dok_rb(sk, cls, R, D, c, SV.drops(dd), dk), r2)

def fdr_rb(+sk: SK.Sketch, +c: Nat, k: SV.Class, h: DH.Fate.driven(k)) -> ({HR.pk_d(sk, c, SV.kdrops(k)) == True{} : Bool} & DH.Fate.driven(k)):
  match k:
    case SV.Kept{+dc}:
      HR.kd_nil(sk, c, dc, h)
    case SV.Amber{dc, rs}:
      absurd(({HR.pk_d(sk, c, SV.drops(dc)) == True{} : Bool} & Empty), h)
    case SV.Over{j, s, w}:
      absurd(({HR.pk_d(sk, c, Nil{}) == True{} : Bool} & Empty), h)
    case SV.Conflict{s, cns}:
      absurd(({HR.pk_d(sk, c, Nil{}) == True{} : Bool} & Empty), h)

def fdv_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, k: SV.Class, h: DH.Fate.driving(sk, cls, R, D, c, k)) -> ({HR.pk_d(sk, c, SV.kdrops(k)) == True{} : Bool} & DH.Fate.driving(sk, cls, R, D, c, k)):
  match k:
    case SV.Kept{+dc}:
      kok_rb(sk, cls, R, D, c, dc, h)
    case SV.Amber{+dc, +rs}:
      aok_rb(sk, cls, R, D, c, dc, h)
    case SV.Over{+j, +s, +w}:
      ({==}, h)
    case SV.Conflict{+s, +cns}:
      ({==}, h)

def fpk_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, b: Bool, +k: SV.Class, h: DH.Fate.pick(sk, cls, R, D, c, b, k)) -> ({HR.pk_d(sk, c, SV.kdrops(k)) == True{} : Bool} & DH.Fate.pick(sk, cls, R, D, c, b, k)):
  match b:
    case True{}:
      fdr_rb(sk, c, k, h)
    case False{}:
      fdv_rb(sk, cls, R, D, c, k, h)

def hg_cmb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +m: Nat, +c: Nat, p: ({HR.pp(sk, cls, c) == True{} : Bool} & DH.Fate(sk, cls, c)), q: ({HR.PP(sk, cls, m, 1n+c) == True{} : Bool} & DH.Honest.go(sk, cls, m, 1n+c)))
  -> ({HR.PP(sk, cls, 1n+m, c) == True{} : Bool} & DH.Honest.go(sk, cls, 1n+m, c)):
  match p:
    case (+hp, f2):
      match q:
        case (+hP, r2):
          (LI.band_i(HR.pp(sk, cls, c), HR.PP(sk, cls, m, 1n+c), hp, hP), (f2, r2))

def hg_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c: Nat, h: DH.Honest.go(sk, cls, n, c)) -> ({HR.PP(sk, cls, n, c) == True{} : Bool} & DH.Honest.go(sk, cls, n, c)):
  match n:
    case 0n:
      ({==}, h)
    case 1n++m:
      match h:
        case (f, r):
          hg_cmb(sk, cls, m, c, fpk_rb(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.driven(sk, c), SV.class_at(cls, c), f), hg_rb(sk, cls, m, 1n+c, r))

def hon_cmb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +hn: {SV.clsn(cls) == SV.ncons(sk) : Nat}, q: ({HR.PP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool} & DH.Honest.go(sk, cls, SV.ncons(sk), 0n)))
  -> ({HR.hfacts(sk, cls) == True{} : Bool} & DH.Honest(sk, cls)):
  match q:
    case (+hP, g2):
      (HR.hfacts_of(sk, cls, hn, hP), (hn, g2))

# read the facts out of an honest classification, and give it back
def hon_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: DH.Honest(sk, cls)) -> ({HR.hfacts(sk, cls) == True{} : Bool} & DH.Honest(sk, cls)):
  match h:
    case (+hn, g):
      hon_cmb(sk, cls, hn, hg_rb(sk, cls, SV.ncons(sk), 0n, g))

# The nd a dropped equation's fact carries
# ----------------------------------------
# dnd_at finds the first drop of j among every class's; the classes before
# j's owner's drop none of its equations (HR.hfacts), so it is the first in
# that class's own list.

def kd_kdd(k: SV.Class) -> {SV.kdrops(k) == SV.drops(SV.kdd(k)) : List<&2, Nat>}:
  match k:
    case SV.Kept{dc}:
      {==}
    case SV.Amber{dc, rs}:
      {==}
    case SV.Over{j, s, w}:
      {==}
    case SV.Conflict{s, nd}:
      {==}

def dnd_skip.c(b: Bool, +i: Nat, +nd: List<&2, Nat>, +t: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +j: Nat, eb: {SV.eq(j, i) == b : Bool}, h: {SV.bor(b, SV.mem(j, SV.drops(t))) == False{} : Bool},
  ih: {SV.mem(j, SV.drops(t)) == False{} : Bool} -> {SV.dnd.go(SV.dcat(t, ys), j) == SV.dnd.go(ys, j) : List<&2, Nat>}) -> {SV.dnd.pick(SV.eq(i, j), nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.go(ys, j) : List<&2, Nat>}:
  match b:
    case True{}:
      absurd({SV.dnd.pick(SV.eq(i, j), nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.go(ys, j) : List<&2, Nat>}, KA.tf(h))
    case False{}:
      %Equal.sym(Bool, SV.eq(i, j), False{}, Equal.trans(Bool, SV.eq(i, j), SV.eq(j, i), False{}, LI.eq_sym(i, j), eb)) : {SV.dnd.pick(_, nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.go(ys, j) : List<&2, Nat>}
      ih(h)

# j not dropped in xs: xs is passed over
def dnd_skip(xs: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +j: Nat, h: {SV.mem(j, SV.drops(xs)) == False{} : Bool}) -> {SV.dnd.go(SV.dcat(xs, ys), j) == SV.dnd.go(ys, j) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{SV.Drop{+i, +nd, w}, +t}:
      dnd_skip.c(SV.eq(j, i), i, nd, t, ys, j, {==}, h, hh => dnd_skip(t, ys, j, hh))

def dnd_hit.c(b: Bool, +i: Nat, +nd: List<&2, Nat>, +t: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +j: Nat, eb: {SV.eq(j, i) == b : Bool}, h: {SV.bor(b, SV.mem(j, SV.drops(t))) == True{} : Bool},
  ih: {SV.mem(j, SV.drops(t)) == True{} : Bool} -> {SV.dnd.go(SV.dcat(t, ys), j) == SV.dnd.go(t, j) : List<&2, Nat>}) -> {SV.dnd.pick(SV.eq(i, j), nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.pick(SV.eq(i, j), nd, SV.dnd.go(t, j)) : List<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.eq(i, j), True{}, Equal.trans(Bool, SV.eq(i, j), SV.eq(j, i), True{}, LI.eq_sym(i, j), eb)) : {SV.dnd.pick(_, nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.pick(_, nd, SV.dnd.go(t, j)) : List<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, SV.eq(i, j), False{}, Equal.trans(Bool, SV.eq(i, j), SV.eq(j, i), False{}, LI.eq_sym(i, j), eb)) : {SV.dnd.pick(_, nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.pick(_, nd, SV.dnd.go(t, j)) : List<&2, Nat>}
      ih(h)

# j dropped in xs: its first drop is there
def dnd_hit(xs: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +j: Nat, h: {SV.mem(j, SV.drops(xs)) == True{} : Bool}) -> {SV.dnd.go(SV.dcat(xs, ys), j) == SV.dnd.go(xs, j) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      absurd({SV.dnd.go(SV.dcat(Nil{}, ys), j) == SV.dnd.go(Nil{}, j) : List<&2, Nat>}, KA.ft(h))
    case Con{SV.Drop{+i, +nd, w}, +t}:
      dnd_hit.c(SV.eq(j, i), i, nd, t, ys, j, {==}, h, hh => dnd_hit(t, ys, j, hh))

def dd.pick(b: Bool, x: List<&2, SV.Drop>, y: List<&2, SV.Drop>) -> List<&2, SV.Drop>:
  match b:
    case True{}:
      x
    case False{}:
      y

# the drops of the class at absolute position o, cls starting at i
def dd_abs(cls: List<&2, SV.Class>, +i: Nat, +o: Nat) -> List<&2, SV.Drop>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      dd.pick(SV.eq(o, i), SV.kdd(h), dd_abs(t, 1n+i, o))

def dd_at(cls: List<&2, SV.Class>, +i: Nat, m: Nat) -> {dd_abs(cls, i, Nat.add(m, i)) == SV.kdd(SV.class_at(cls, m)) : List<&2, SV.Drop>}:
  match cls m:
    case Nil{} m:
      {==}
    case Con{+h, +t} 0n:
      %Equal.sym(Bool, SV.eq(i, i), True{}, LI.eq_refl(i)) : {dd.pick(_, SV.kdd(h), dd_abs(t, 1n+i, i)) == SV.kdd(h) : List<&2, SV.Drop>}
      {==}
    case Con{+h, +t} 1n++k:
      %Equal.sym(Bool, SV.eq(1n+Nat.add(k, i), i), False{}, CL.ne_add(k, i)) : {dd.pick(_, SV.kdd(h), dd_abs(t, 1n+i, 1n+Nat.add(k, i))) == SV.kdd(SV.class_at(t, k)) : List<&2, SV.Drop>}
      %Equal.sym(Nat, 1n+Nat.add(k, i), Nat.add(k, 1n+i), LN.add_succ(k, i)) : {dd_abs(t, 1n+i, _) == SV.kdd(SV.class_at(t, k)) : List<&2, SV.Drop>}
      dd_at(t, 1n+i, k)

def dd_absz(cls: List<&2, SV.Class>, +o: Nat) -> {dd_abs(cls, 0n, o) == SV.kdd(SV.class_at(cls, o)) : List<&2, SV.Drop>}:
  %Equal.sym(Nat, o, Nat.add(o, 0n), LN.add_zero(o)) : {dd_abs(cls, 0n, _) == SV.kdd(SV.class_at(cls, o)) : List<&2, SV.Drop>}
  dd_at(cls, 0n, o)

# a = b, b is not i: a is not i
def ne_tr(+a: Nat, +b: Nat, +i: Nat, e: {SV.eq(a, b) == True{} : Bool}, h: {SV.eq(b, i) == False{} : Bool}) -> {SV.eq(a, i) == False{} : Bool}:
  %Equal.sym(Nat, a, b, LI.eq_ok(a, b, e)) : {SV.eq(_, i) == False{} : Bool}
  h

def dnd_own.c(b: Bool, +own: List<&2, Nat>, +h: SV.Class, +t: List<&2, SV.Class>, +i: Nat, +o: Nat, +k: Nat, eb: {SV.eq(o, i) == b : Bool}, +ho: {SV.eq(SV.nth(own, k), o) == True{} : Bool}, +ha: {KB.allo(own, SV.kdrops(h), i) == True{} : Bool},
  hm: {SV.mem(k, SV.drops(dd.pick(b, SV.kdd(h), dd_abs(t, 1n+i, o)))) == True{} : Bool},
  ih: {SV.mem(k, SV.drops(dd_abs(t, 1n+i, o))) == True{} : Bool} -> {SV.dnd.go(SV.cdrops(t), k) == SV.dnd.go(dd_abs(t, 1n+i, o), k) : List<&2, Nat>})
  -> {SV.dnd.go(SV.dcat(SV.kdd(h), SV.cdrops(t)), k) == SV.dnd.go(dd.pick(b, SV.kdd(h), dd_abs(t, 1n+i, o)), k) : List<&2, Nat>}:
  match b:
    case True{}:
      dnd_hit(SV.kdd(h), SV.cdrops(t), k, hm)
    case False{}:
      +hk = ne_tr(SV.nth(own, k), o, i, ho, eb)
      Equal.trans(List<&2, Nat>, SV.dnd.go(SV.dcat(SV.kdd(h), SV.cdrops(t)), k), SV.dnd.go(SV.cdrops(t), k), SV.dnd.go(dd_abs(t, 1n+i, o), k),
        dnd_skip(SV.kdd(h), SV.cdrops(t), k, (%kd_kdd(h) : {SV.mem(k, _) == False{} : Bool}
          CL.allo_nm(own, SV.kdrops(h), i, k, ha, hk))), ih(hm))

def dnd_own.go(+own: List<&2, Nat>, cls: List<&2, SV.Class>, +i: Nat, +o: Nat, +k: Nat, +hd: {CL.downs(own, cls, i) == True{} : Bool}, +ho: {SV.eq(SV.nth(own, k), o) == True{} : Bool}, hm: {SV.mem(k, SV.drops(dd_abs(cls, i, o))) == True{} : Bool})
  -> {SV.dnd.go(SV.cdrops(cls), k) == SV.dnd.go(dd_abs(cls, i, o), k) : List<&2, Nat>}:
  match cls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      dnd_own.c(SV.eq(o, i), own, h, t, i, o, k, {==}, ho, LI.band_l(KB.allo(own, SV.kdrops(h), i), CL.downs(own, t, 1n+i), hd), hm,
        hh => dnd_own.go(own, t, 1n+i, o, k, LI.band_r(KB.allo(own, SV.kdrops(h), i), CL.downs(own, t, 1n+i), hd), ho, hh))

# a dropped equation's fact carries its drop's nd in its owner's class
def dnd_own(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +k: Nat, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, hm: {SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool})
  -> {SV.dnd_at(cls, k) == SV.dnd.go(SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k) : List<&2, Nat>}:
  +o = SV.nth(SV.owners(sk), k)
  +ez = dd_absz(cls, o)
  Equal.trans(List<&2, Nat>, SV.dnd_at(cls, k), SV.dnd.go(dd_abs(cls, 0n, o), k), SV.dnd.go(SV.kdd(SV.class_at(cls, o)), k),
    dnd_own.go(SV.owners(sk), cls, 0n, o, k, LI.band_l(CL.downs(SV.owners(sk), cls, 0n), SV.below(SV.dropped(cls), SV.neqs(SK.Sketch.eqs(sk))), hf), LI.eq_refl(o),
      (%Equal.sym(List<&2, SV.Drop>, dd_abs(cls, 0n, o), SV.kdd(SV.class_at(cls, o)), ez) : {SV.mem(k, SV.drops(_)) == True{} : Bool}
        (%kd_kdd(SV.class_at(cls, o)) : {SV.mem(k, _) == True{} : Bool}
          hm))),
    Equal.cong(List<&2, SV.Drop>, List<&2, Nat>, z => SV.dnd.go(z, k), dd_abs(cls, 0n, o), SV.kdd(SV.class_at(cls, o)), ez))

# Facts at a position
# -------------------


def allfacts_cat(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, xs: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, h1: DP.AllFacts(~F, env, es, xs), h2: DP.AllFacts(~F, env, es, ys)) -> DP.AllFacts(~F, env, es, SV.fcat(xs, ys)):
  match xs:
    case Nil{}:
      h2
    case Con{+f, +t}:
      (a, b) = h1
      (a, allfacts_cat(~F, env, es, t, ys, b, h2))

def stat_at.h(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +j: Nat, a: AtK(sk, j), he: {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}) -> DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))):
  (+k, q1) = a
  (+r, q2) = q1
  (hk, q3) = q2
  (hr, heq) = q3
  %Equal.sym(Maybe<&2, SK.Constraint>, SV.kind_at(sk, SV.nth(SV.owners(sk), j)), Some{k}, hk) : DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), _))
  stat_r(~F, x, SV.ents(sk), k, r, hr, (%heq : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
    he))

# where the sketch's equation j vanishes, its constraint's statement holds
def stat_at(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +j: Nat, hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, he: {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}) -> DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))):
  stat_at.h(~F, x, sk, j, at(sk, j, hj), he)

def eq_at.h(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +j: Nat, a: AtK(sk, j), hs: DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))), hd: {dsome(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}:
  (+k, q1) = a
  (+r, q2) = q1
  (+hk, q3) = q2
  (hr, heq) = q3
  %Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), j), SV.eqat(SK.Constraint.eqs(SV.ents(sk), k), r), heq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
  eq_r(~F, x, SV.ents(sk), k, r, hr, (%hk : DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), _))
    hs), (%hk : {dsome(SV.dstat_of(SV.ents(sk), _)) == True{} : Bool}
    hd))

# where the sketch's equation j's constraint's statement holds, j does
def eq_at(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +j: Nat, hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, hs: DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))), hd: {dsome(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}:
  eq_at.h(~F, x, sk, j, at(sk, j, hj), hs, hd)


# the same for an equation of c
def stat_c(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}, he: {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}) -> DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))):
  %ho : DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, _)))
  stat_at(~F, x, sk, j, hj, he)

def eq_c(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}, hs: DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))), hd: {dsome(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}:
  eq_at(~F, x, sk, j, hj, (%Equal.sym(Nat, SV.nth(SV.owners(sk), j), c, ho) : DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, _)))
    hs), (%Equal.sym(Nat, SV.nth(SV.owners(sk), j), c, ho) : {dsome(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, _))) == True{} : Bool}
    hd))

# the equation holds, so its statement does
def ec_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}, +he: {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}) -> SK.Both({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)))):
  (he, stat_c(~F, x, sk, c, j, hj, ho, he))

def pr_s(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +b: Nat, +yy: SK.VE, +l: S.Q, +em: {SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)) == Some{DR.DStat{b, yy, l}} : Maybe<&2, DR.DStat>}, +a: DR.Node, +y: SK.VE,
  ha: {a == DR.NSeg{b} : DR.Node}, hsv: DR.SameV(y, yy), hh: {DP.evc(~F, x, DR.zdir(SV.ents(sk), a), y) == O.zero(F) : O.C(F)}) -> DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))):
  %Equal.sym(Maybe<&2, DR.DStat>, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), Some{DR.DStat{b, yy, l}}, em) : DP.StatHolds(~F, x, SV.ents(sk), _)
  DP.same_tr(~F, x, DR.zseg(SV.ents(sk), b), y, yy, hsv, (%ha : {DP.evc(~F, x, DR.zdir(SV.ents(sk), _), y) == O.zero(F) : O.C(F)}
    hh))

def pr_p(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}, m: Maybe<&2, DR.DStat>, +em: {SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)) == m : Maybe<&2, DR.DStat>}, +a: DR.Node, +y: SK.VE, hp: SV.Proves.p(SV.ents(sk), m, a, y), hh: {DP.evc(~F, x, DR.zdir(SV.ents(sk), a), y) == O.zero(F) : O.C(F)}) -> SK.Both({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)))):
  match m:
    case Some{DR.DStat{+b, +yy, l}}:
      (ha, hsv) = hp
      +hs = pr_s(~F, x, sk, c, b, yy, l, em, a, y, ha, hsv, hh)
      (eq_c(~F, x, sk, c, j, hj, ho, hs, (%Equal.sym(Maybe<&2, DR.DStat>, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), Some{DR.DStat{b, yy, l}}, em) : {dsome(_) == True{} : Bool}
        {==})), hs)
    case None{}:
      absurd(SK.Both({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)))), hp)

# a conclusion that proves c's equation j, holding at x: j holds, and so
# does c's statement
def pr_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}, jd: DR.Jd, hp: SV.Proves(SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.eqat(SK.Sketch.eqs(sk), j), jd), hh: DP.Holds(~F, x, SV.ents(sk), jd)) -> SK.Both({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)))):
  match jd:
    case DR.JK{+f}:
      ec_of(~F, x, sk, c, j, hj, ho, DP.k_tr(~F, x, f, SV.eqat(SK.Sketch.eqs(sk), j), hp, hh))
    case DR.JP{+a, +y}:
      pr_p(~F, x, sk, c, j, hj, ho, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), {==}, a, y, hp, hh)

# A kept constraint's drops, at x
# -------------------------------
# c is kept (not red) and drops d; KF(c), the facts of the kept constraints
# before it, hold at x.


# an equation of c that c does not drop is not dropped
def nd_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +p: Nat, +ho: {SV.nth(SV.owners(sk), p) == c : Nat}, hn: {SV.mem(p, d) == False{} : Bool}) -> {SV.mem(p, SV.dropped(cls)) == False{} : Bool}:
  Equal.trans(Bool, SV.mem(p, SV.dropped(cls)), SV.mem(p, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), p)))), False{}, HR.mem_dropped(sk, cls, p, hf),
    (%Equal.sym(Nat, SV.nth(SV.owners(sk), p), c, ho) : {SV.mem(p, SV.kdrops(SV.class_at(cls, _))) == False{} : Bool}
      (%Equal.sym(List<&2, Nat>, SV.kdrops(SV.class_at(cls, c)), d, hkd) : {SV.mem(p, _) == False{} : Bool}
        hn)))

# so it is solved, and holds at x
def z_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +p: Nat, +ho: {SV.nth(SV.owners(sk), p) == c : Nat}, hn: {SV.mem(p, d) == False{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), p)) == O.zero(F) : O.C(F)}:
  VR.zat(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), hz, p, VR.sa_of(SV.owners(sk), SV.reds(cls), SV.dropped(cls), p, (%Equal.sym(Nat, SV.nth(SV.owners(sk), p), c, ho) : {SV.mem(_, SV.reds(cls)) == False{} : Bool}
    hnr), nd_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, p, ho, hn)))

def ib_sa.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, +p: Nat, +eb: {SV.band(SV.lt(SV.nth(SV.owners(sk), p), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), p), SV.reds(cls))), SV.bnot(SV.mem(p, SV.dropped(cls))))) == b : Bool}, h: {SV.bor(b, SV.band(SV.lt(p, j), SV.band(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d))))) == True{} : Bool}) -> {DK.solved_at(SV.owners(sk), SV.reds(cls), SV.dropped(cls), p) == True{} : Bool}:
  match b:
    case True{}:
      LI.band_r(SV.lt(SV.nth(SV.owners(sk), p), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), p), SV.reds(cls))), SV.bnot(SV.mem(p, SV.dropped(cls)))), eb)
    case False{}:
      +h2 = LI.band_r(SV.lt(p, j), SV.band(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d))), h)
      +ho = LI.eq_ok(SV.nth(SV.owners(sk), p), c, LI.band_l(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d)), h2))
      VR.sa_of(SV.owners(sk), SV.reds(cls), SV.dropped(cls), p, (%Equal.sym(Nat, SV.nth(SV.owners(sk), p), c, ho) : {SV.mem(_, SV.reds(cls)) == False{} : Bool}
        hnr), nd_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, p, ho, KB.bnot_t(SV.mem(p, d), LI.band_r(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d)), h2))))

# a degree-0 reason names only equations of the system solved
def cs_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, ms: List<&2, SV.Mul>, +h: {DH.in_basis.all(sk, SV.reds(cls), SV.dropped(cls), c, d, j, ms) == True{} : Bool}) -> {DK.comb.solved(SV.owners(sk), SV.reds(cls), SV.dropped(cls), ms) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{SV.Mul{+p, +q}, +t}:
      +hi = LI.band_l(DH.in_basis(sk, SV.reds(cls), SV.dropped(cls), c, d, j, p), DH.in_basis.all(sk, SV.reds(cls), SV.dropped(cls), c, d, j, t), h)
      LI.band_i(DK.solved_at(SV.owners(sk), SV.reds(cls), SV.dropped(cls), p), DK.comb.solved(SV.owners(sk), SV.reds(cls), SV.dropped(cls), t), ib_sa.c(~F, SV.band(SV.lt(SV.nth(SV.owners(sk), p), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), p), SV.reds(cls))), SV.bnot(SV.mem(p, SV.dropped(cls))))), x, sk, cls, hz, hf, c, d, hkd, hnr, j, p, {==}, LI.band_r(SV.lt(p, SV.neqs(SK.Sketch.eqs(sk))), SV.bor(SV.band(SV.lt(SV.nth(SV.owners(sk), p), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), p), SV.reds(cls))), SV.bnot(SV.mem(p, SV.dropped(cls))))), SV.band(SV.lt(p, j), SV.band(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d))))), hi)),
        cs_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, t, LI.band_r(DH.in_basis(sk, SV.reds(cls), SV.dropped(cls), c, d, j, p), DH.in_basis.all(sk, SV.reds(cls), SV.dropped(cls), c, d, j, t), h)))

def of_ok.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +k: Nat, +eb: {SV.band(SV.lt(k, j), SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d)))) == b : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, ih: DP.AllFacts(~F, x, SV.ents(sk), SV.ofacts.go(t, SV.owners(sk), sk, c, d, j, 1n+k)))
  -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.pick(b, DR.Fact{e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}, SV.ofacts.go(t, SV.owners(sk), sk, c, d, j, 1n+k))):
  match b:
    case True{}:
      +h2 = LI.band_r(SV.lt(k, j), SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d))), eb)
      +ho = LI.eq_ok(SV.nth(SV.owners(sk), k), c, LI.band_l(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d)), h2))
      +ez = z_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, k, ho, KB.bnot_t(SV.mem(k, d), LI.band_r(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d)), h2)))
      (Inr{((%OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        ez), stat_c(~F, x, sk, c, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), ho, ez))}, ih)
    case False{}:
      ih

# c's own earlier equations that it does not drop hold at x, as facts
def of_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, es: List<&2, E.QExpr>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}) -> DP.AllFacts(~F, x, SV.ents(sk), SV.ofacts.go(es, SV.owners(sk), sk, c, d, j, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      of_ok.c(~F, SV.band(SV.lt(k, j), SV.band(SV.eq(SV.nth(SV.owners(sk), k), c), SV.bnot(SV.mem(k, d)))), x, sk, cls, hz, hf, c, d, hkd, hnr, j, e, t, k, {==}, hq, of_ok(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, t, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq)))


# a drop of c whose nd segments are long: its equation and c's statement
# hold at x
def fh_drop.w(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, +nd: List<&2, Nat>, w: SV.Why, wk: DH.why_ok(sk, cls, SV.reds(cls), SV.dropped(cls), c, d, j, nd, w), hl: DR.Longs(~F, x, SV.ents(sk), nd), +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat}) -> SK.Both({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)))):
  match w:
    case SV.WLin{+ms}:
      (+hib, q) = wk
      (hid, hn) = q
      ec_of(~F, x, sk, c, j, hj, ho, Equal.trans(O.C(F), O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)), O.eval(~F, x, SV.mlin(SK.Sketch.eqs(sk), ms)), O.zero(F), ID.ident_all(~F, SV.eqat(SK.Sketch.eqs(sk), j), SV.mlin(SK.Sketch.eqs(sk), ms), hid, x), VR.comb_zero(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), hz, ms, cs_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, ms, hib))))
    case SV.WDer{+dv}:
      (hv, q) = wk
      (hp, hs) = q
      pr_ok(~F, x, sk, c, j, hj, ho, DR.concl(SV.ents(sk), SV.dfacts(sk, cls, SV.reds(cls), c, d, j), dv), hp, DP.sound(~F, x, SV.ents(sk), SV.dfacts(sk, cls, SV.reds(cls), c, d, j), SV.ctx(sk, SV.reds(cls), c), allfacts_cat(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n), kf, of_ok(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, SK.Sketch.eqs(sk), 0n, {==})), dv, hv, (%hs : DR.Longs(~F, x, SV.ents(sk), _) hl)))

def fh_drop.l(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +j: Nat, +nd: List<&2, Nat>, w: SV.Why, wk: DH.why_ok(sk, cls, SV.reds(cls), SV.dropped(cls), c, d, j, nd, w), dec: DP.DOr(DR.Longs(~F, x, SV.ents(sk), nd), DP.Short(~F, x, SV.ents(sk), nd)), +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), +hj: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), j) == c : Nat})
  -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}):
  match dec:
    case Inl{hl}:
      Inr{fh_drop.w(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, nd, w, wk, hl, kf, hj, ho)}
    case Inr{sh}:
      Inl{sh}

# each drop's fact (with the drop's nd and c's statement) at x
def DW(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, dd: List<&2, SV.Drop>) -> Data:
  match dd:
    case Nil{}:
      Unit
    case Con{SV.Drop{+j, +nd, w}, t}:
      SK.Both(DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}), DW(~F, x, sk, c, t))

def dw_mk(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), dd: List<&2, SV.Drop>, hnd: DH.drops_nd(sk, cls, SV.reds(cls), SV.dropped(cls), c, d, dd), +ha: {KB.allo(SV.owners(sk), SV.drops(dd), c) == True{} : Bool}, +hb: {SV.below(SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> DW(~F, x, sk, c, dd):
  match dd:
    case Nil{}:
      Unit{}
    case Con{SV.Drop{+j, +nd, w}, +t}:
      (wk, rest) = hnd
      +hj = LI.band_l(SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))), SV.below(SV.drops(t), SV.neqs(SK.Sketch.eqs(sk))), hb)
      +ho = LI.eq_ok(SV.nth(SV.owners(sk), j), c, LI.band_l(SV.eq(SV.nth(SV.owners(sk), j), c), KB.allo(SV.owners(sk), SV.drops(t), c), ha))
      (fh_drop.l(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, j, nd, w, wk, ls_dec(~F, x, SV.ents(sk), nd), kf, hj, ho),
        dw_mk(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, kf, t, rest, LI.band_r(SV.eq(SV.nth(SV.owners(sk), j), c), KB.allo(SV.owners(sk), SV.drops(t), c), ha), LI.band_r(SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))), SV.below(SV.drops(t), SV.neqs(SK.Sketch.eqs(sk))), hb)))

# A fact by its position
# ----------------------


def af_hd(~F: O.OField, b: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +f: DR.Fact, +rest: List<&2, DR.Fact>, eb: {b == True{} : Bool}, h: DP.AllFacts(~F, env, es, SV.facts.pick(b, f, rest))) -> DP.FactHolds(~F, env, es, f):
  match b:
    case True{}:
      DP.fst(DP.FactHolds(~F, env, es, f), DP.AllFacts(~F, env, es, rest), h)
    case False{}:
      absurd(DP.FactHolds(~F, env, es, f), KA.ft(eb))

def af_tl(~F: O.OField, b: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +f: DR.Fact, +rest: List<&2, DR.Fact>, h: DP.AllFacts(~F, env, es, SV.facts.pick(b, f, rest))) -> DP.AllFacts(~F, env, es, rest):
  match b:
    case True{}:
      DP.snd(DP.FactHolds(~F, env, es, f), DP.AllFacts(~F, env, es, rest), h)
    case False{}:
      h


# the fact at position m + k of a list from k, its owner in cs
def af_at(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +cs: List<&2, Nat>, es: List<&2, E.QExpr>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}, m: Nat, hm: {SV.mem(SV.nth(SV.owners(sk), Nat.add(m, k)), cs) == True{} : Bool}, hlt: {SV.lt(m, SV.neqs(es)) == True{} : Bool},
  h: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(es, SV.owners(sk), cs, sk, cls, True{}, k))) -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), Nat.add(m, k)), SV.dnd_at(cls, Nat.add(m, k)), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), Nat.add(m, k))))}):
  match es m:
    case Nil{} m:
      absurd(DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), Nat.add(m, k)), SV.dnd_at(cls, Nat.add(m, k)), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), Nat.add(m, k))))}), KA.ft(KB.lt_zero(m, hlt)))
    case Con{+e, +t} 0n:
      %Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{_, SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))})
      af_hd(~F, SV.mem(SV.nth(SV.owners(sk), k), cs), x, SV.ents(sk), DR.Fact{e, SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))}, SV.facts.go(t, SV.owners(sk), cs, sk, cls, True{}, 1n+k), hm, h)
    case Con{+e, +t} 1n++q:
      %Equal.sym(Nat, 1n+Nat.add(q, k), Nat.add(q, 1n+k), LN.add_succ(q, k)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), _), SV.dnd_at(cls, _), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), _)))})
      af_at(~F, x, sk, cls, cs, t, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), q, (%LN.add_succ(q, k) : {SV.mem(SV.nth(SV.owners(sk), _), cs) == True{} : Bool}
        hm), hlt, af_tl(~F, SV.mem(SV.nth(SV.owners(sk), k), cs), x, SV.ents(sk), DR.Fact{e, SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))}, SV.facts.go(t, SV.owners(sk), cs, sk, cls, True{}, 1n+k), h))

# c is driving and not red: dcond
def dc_t(+sk: SK.Sketch, +R: List<&2, Nat>, +o: Nat, +hd: {SV.driving(sk, o) == True{} : Bool}, +hr: {SV.mem(o, R) == False{} : Bool}) -> {KB.dcond(sk, R, o) == True{} : Bool}:
  %Equal.sym(Bool, SV.driving(sk, o), True{}, hd) : {SV.band(_, SV.bnot(SV.mem(o, R))) == True{} : Bool}
  %Equal.sym(Bool, SV.mem(o, R), False{}, hr) : {SV.band(True{}, SV.bnot(_)) == True{} : Bool}
  {==}

def kpk_mem(b: Bool, +kb: List<&2, Nat>, +c: Nat, +o: Nat, h: {SV.mem(o, kb) == True{} : Bool}) -> {SV.mem(o, KB.kpk(b, kb, c)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.mem(o, CO.lsnoc(kb, c)), SV.bor(SV.mem(o, kb), SV.eq(o, c)), KB.mem_snoc(o, kb, c)) : {_ == True{} : Bool}
      LI.bor_l(SV.mem(o, kb), SV.eq(o, c), h)
    case False{}:
      h

def kb_mem.c(b: Bool, +sk: SK.Sketch, +R: List<&2, Nat>, +o: Nat, +c2: Nat, eb: {SV.eq(o, c2) == b : Bool}, +hd: {SV.driving(sk, o) == True{} : Bool}, +hr: {SV.mem(o, R) == False{} : Bool}, +hlt: {SV.lt(o, 1n+c2) == True{} : Bool},
  ih: {SV.lt(o, c2) == True{} : Bool} -> {SV.mem(o, SV.kept_before(sk, R, c2)) == True{} : Bool}) -> {SV.mem(o, KB.kpk(KB.dcond(sk, R, c2), SV.kept_before(sk, R, c2), c2)) == True{} : Bool}:
  match b:
    case True{}:
      %LI.eq_ok(o, c2, eb) : {SV.mem(o, KB.kpk(KB.dcond(sk, R, _), SV.kept_before(sk, R, _), _)) == True{} : Bool}
      %Equal.sym(Bool, KB.dcond(sk, R, o), True{}, dc_t(sk, R, o, hd, hr)) : {SV.mem(o, KB.kpk(_, SV.kept_before(sk, R, o), o)) == True{} : Bool}
      %Equal.sym(Bool, SV.mem(o, CO.lsnoc(SV.kept_before(sk, R, o), o)), SV.bor(SV.mem(o, SV.kept_before(sk, R, o)), SV.eq(o, o)), KB.mem_snoc(o, SV.kept_before(sk, R, o), o)) : {_ == True{} : Bool}
      LI.bor_r(SV.mem(o, SV.kept_before(sk, R, o)), SV.eq(o, o), LI.eq_refl(o))
    case False{}:
      kpk_mem(KB.dcond(sk, R, c2), SV.kept_before(sk, R, c2), c2, o, ih(KB.lt_down(o, c2, hlt, eb)))

# a driving constraint before c that is not red is kept before c
def kb_mem(+sk: SK.Sketch, +R: List<&2, Nat>, +o: Nat, c: Nat, +hd: {SV.driving(sk, o) == True{} : Bool}, +hr: {SV.mem(o, R) == False{} : Bool}, hlt: {SV.lt(o, c) == True{} : Bool}) -> {SV.mem(o, SV.kept_before(sk, R, c)) == True{} : Bool}:
  match c:
    case 0n:
      absurd({SV.mem(o, SV.kept_before(sk, R, 0n)) == True{} : Bool}, KA.ft(KB.lt_zero(o, hlt)))
    case 1n++c2:
      %Equal.sym(List<&2, Nat>, SV.kept_before(sk, R, 1n+c2), KB.kpk(KB.dcond(sk, R, c2), SV.kept_before(sk, R, c2), c2), KB.kb_next(sk, R, c2)) : {SV.mem(o, _) == True{} : Bool}
      kb_mem.c(SV.eq(o, c2), sk, R, o, c2, {==}, hd, hr, hlt, h => kb_mem(sk, R, o, c2, hd, hr, h))

def dw_at.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +j: Nat, +nd: List<&2, Nat>, +t: List<&2, SV.Drop>, +p: Nat, +eb: {SV.eq(p, j) == b : Bool}, hm: {SV.bor(b, SV.mem(p, SV.drops(t))) == True{} : Bool},
  hd: DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}), ih: {SV.mem(p, SV.drops(t)) == True{} : Bool} -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), SV.dnd.go(t, p), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}))
  -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), SV.dnd.pick(SV.eq(j, p), nd, SV.dnd.go(t, p)), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}):
  match b:
    case True{}:
      %Equal.sym(Bool, SV.eq(j, p), True{}, Equal.trans(Bool, SV.eq(j, p), SV.eq(p, j), True{}, LI.eq_sym(j, p), eb)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), SV.dnd.pick(_, nd, SV.dnd.go(t, p)), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      %Equal.sym(Nat, p, j, LI.eq_ok(p, j, eb)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), _), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      hd
    case False{}:
      %Equal.sym(Bool, SV.eq(j, p), False{}, Equal.trans(Bool, SV.eq(j, p), SV.eq(p, j), False{}, LI.eq_sym(j, p), eb)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), SV.dnd.pick(_, nd, SV.dnd.go(t, p)), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      ih(hm)

# the fact of p's first drop
def dw_at(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, dd: List<&2, SV.Drop>, +p: Nat, hm: {SV.mem(p, SV.drops(dd)) == True{} : Bool}, +h: DW(~F, x, sk, c, dd)) -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), SV.dnd.go(dd, p), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}):
  match dd:
    case Nil{}:
      absurd(DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), p), Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}), KA.ft(hm))
    case Con{SV.Drop{+j, +nd, w}, +t}:
      dw_at.c(~F, SV.eq(p, j), x, sk, c, j, nd, t, p, {==}, hm, DP.fst(DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}), DW(~F, x, sk, c, t), h),
        hh => dw_at(~F, x, sk, c, t, p, hh, DP.snd(DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), nd, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}), DW(~F, x, sk, c, t), h)))

# c's own facts
# -------------


# k, an equation of c, is among c's drops
def km_of(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +d: List<&2, Nat>, +k: Nat, +ho: {SV.nth(SV.owners(sk), k) == c : Nat}, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, eb: {SV.mem(k, d) == True{} : Bool}) -> {SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool}:
  %Equal.sym(Nat, SV.nth(SV.owners(sk), k), c, ho) : {SV.mem(k, SV.kdrops(SV.class_at(cls, _))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, SV.kdrops(SV.class_at(cls, c)), d, hkd) : {SV.mem(k, _) == True{} : Bool}
  eb

def fh_k.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +dd: List<&2, SV.Drop>, +hkdd: {SV.kdd(SV.class_at(cls, c)) == dd : List<&2, SV.Drop>}, +hdd: {SV.drops(dd) == d : List<&2, Nat>}, +dw: DW(~F, x, sk, c, dd), +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ho: {SV.nth(SV.owners(sk), k) == c : Nat}, +eb: {SV.mem(k, d) == b : Bool})
  -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}):
  match b:
    case True{}:
      +hm = km_of(sk, cls, c, d, k, ho, hkd, eb)
      %Equal.sym(List<&2, Nat>, SV.dnd_at(cls, k), SV.dnd.go(SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k), dnd_own(sk, cls, k, hf, hm)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), k), _, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      %Equal.sym(Nat, SV.nth(SV.owners(sk), k), c, ho) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd.go(SV.kdd(SV.class_at(cls, _)), k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      %Equal.sym(List<&2, SV.Drop>, SV.kdd(SV.class_at(cls, c)), dd, hkdd) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd.go(_, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))})
      dw_at(~F, x, sk, c, dd, k, (%Equal.sym(List<&2, Nat>, SV.drops(dd), d, hdd) : {SV.mem(k, _) == True{} : Bool}
        eb), dw)
    case False{}:
      Inr{ec_of(~F, x, sk, c, k, hk, ho, z_of(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, k, ho, eb))}

def cf_ok.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +dd: List<&2, SV.Drop>, +hkdd: {SV.kdd(SV.class_at(cls, c)) == dd : List<&2, SV.Drop>}, +hdd: {SV.drops(dd) == d : List<&2, Nat>}, +dw: DW(~F, x, sk, c, dd), +e: E.QExpr, +t: List<&2, E.QExpr>, +k: Nat, +eb: {SV.eq(SV.nth(SV.owners(sk), k), c) == b : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, ih: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(t, SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, 1n+k)))
  -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.pick(SV.bor(b, False{}), DR.Fact{e, SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))}, SV.facts.go(t, SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, 1n+k))):
  match b:
    case True{}:
      +ho = LI.eq_ok(SV.nth(SV.owners(sk), k), c, eb)
      ((%OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{_, SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))})
        (%Equal.sym(Nat, SV.nth(SV.owners(sk), k), c, ho) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, _))})
          fh_k.c(~F, SV.mem(k, d), x, sk, cls, hz, hf, c, d, hkd, hnr, dd, hkdd, hdd, dw, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), ho, {==}))), ih)
    case False{}:
      ih

# c's own equations hold at x as facts
def cf_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +d: List<&2, Nat>, +hkd: {SV.kdrops(SV.class_at(cls, c)) == d : List<&2, Nat>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +dd: List<&2, SV.Drop>, +hkdd: {SV.kdd(SV.class_at(cls, c)) == dd : List<&2, SV.Drop>}, +hdd: {SV.drops(dd) == d : List<&2, Nat>}, +dw: DW(~F, x, sk, c, dd), es: List<&2, E.QExpr>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(es, SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      cf_ok.c(~F, SV.eq(SV.nth(SV.owners(sk), k), c), x, sk, cls, hz, hf, c, d, hkd, hnr, dd, hkdd, hdd, dw, e, t, k, {==}, hq, cf_ok(~F, x, sk, cls, hz, hf, c, d, hkd, hnr, dd, hkdd, hdd, dw, t, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq)))

# One constraint
# --------------


# c joins the kept constraints: its facts after KF(c)'s
def kf_keep(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +edc: {KB.dcond(sk, SV.reds(cls), c) == True{} : Bool}, +hb: {SV.below(SV.kept_before(sk, SV.reds(cls), c), c) == True{} : Bool}, +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), cf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, 0n))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)):
  %Equal.sym(Bool, KB.dcond(sk, SV.reds(cls), c), True{}, edc) : DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(_, SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n))
  %Equal.sym(List<&2, DR.Fact>, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), CO.lsnoc(SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, SV.kept_before(sk, SV.reds(cls), c)}, sk, cls, True{}, 0n), DPM.facts_snoc(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), c, sk, cls, True{}, 0n)) : DP.AllFacts(~F, x, SV.ents(sk), _)
  %Equal.sym(List<&2, DR.Fact>, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, SV.kept_before(sk, SV.reds(cls), c)}, sk, cls, True{}, 0n), SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, 0n)), DPM.split(SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, c, 0n, {==}, OW.len_owners(sk), OW.sorted_owners(sk), hb)) : DP.AllFacts(~F, x, SV.ents(sk), _)
  allfacts_cat(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, Nil{}}, sk, cls, True{}, 0n), kf, cf)

# c does not join them
def kf_same(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +edc: {KB.dcond(sk, SV.reds(cls), c) == False{} : Bool}, kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)):
  %Equal.sym(Bool, KB.dcond(sk, SV.reds(cls), c), False{}, edc) : DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(_, SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n))
  kf

def kd_of(+cls: List<&2, SV.Class>, +c: Nat, +dd: List<&2, SV.Drop>, +ekd: {SV.kdd(SV.class_at(cls, c)) == dd : List<&2, SV.Drop>}) -> {SV.kdrops(SV.class_at(cls, c)) == SV.drops(dd) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, SV.kdrops(SV.class_at(cls, c)), SV.drops(SV.kdd(SV.class_at(cls, c))), SV.drops(dd), kd_kdd(SV.class_at(cls, c)), Equal.cong(List<&2, SV.Drop>, List<&2, Nat>, z => SV.drops(z), SV.kdd(SV.class_at(cls, c)), dd, ekd))

# a kept or amber c, with drops dd
def st_dd(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +dd: List<&2, SV.Drop>, +ekd: {SV.kdd(SV.class_at(cls, c)) == dd : List<&2, SV.Drop>}, +hnr: {SV.mem(c, SV.reds(cls)) == False{} : Bool}, +edc: {KB.dcond(sk, SV.reds(cls), c) == True{} : Bool}, +hb: {SV.below(SV.kept_before(sk, SV.reds(cls), c), c) == True{} : Bool}, +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)),
  hnd: DH.DropsNd(sk, cls, SV.reds(cls), SV.dropped(cls), c, dd), +hpk: {HR.pk_d(sk, c, SV.drops(dd)) == True{} : Bool}) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)):
  +hkd = kd_of(cls, c, dd, ekd)
  +ha = LI.band_l(KB.allo(SV.owners(sk), SV.drops(dd), c), SV.below(SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))), hpk)
  +hbl = LI.band_r(KB.allo(SV.owners(sk), SV.drops(dd), c), SV.below(SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))), hpk)
  kf_keep(~F, x, sk, cls, c, edc, hb, kf, cf_ok(~F, x, sk, cls, hz, hf, c, SV.drops(dd), hkd, hnr, dd, ekd, {==}, dw_mk(~F, x, sk, cls, hz, hf, c, SV.drops(dd), hkd, hnr, kf, dd, hnd, ha, hbl), SK.Sketch.eqs(sk), 0n, {==}))

# what an amber constraint's Fate says of its sides, kept for after the
# walk (each Fate is read once)
def AmbS.k(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, k: SV.Class) -> Type:
  match k:
    case SV.Kept{dd}:
      Unit
    case SV.Amber{dd, rs}:
      DH.AllImplied(sk, R, c)
    case SV.Over{j, s, w}:
      Unit
    case SV.Conflict{s, nd}:
      Unit

def AmbS.pick(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, b: Bool, +k: SV.Class) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      AmbS.k(sk, R, c, k)

def AmbS(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat) -> Type:
  AmbS.pick(sk, SV.reds(cls), c, SV.driven(sk, c), SV.class_at(cls, c))

def Amb.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      AmbS(sk, cls, c) & Amb.go(sk, cls, m, 1n+c)

def st_k(~F: O.OField, k: SV.Class, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +ek: {SV.class_at(cls, c) == k : SV.Class}, +er: {SV.mem(c, SV.reds(cls)) == SV.is_red(k) : Bool}, +edc0: {KB.dcond(sk, SV.reds(cls), c) == SV.bnot(SV.mem(c, SV.reds(cls))) : Bool},
  p: ({HR.pk_d(sk, c, SV.kdrops(k)) == True{} : Bool} & DH.Fate.driving(sk, cls, SV.reds(cls), SV.dropped(cls), c, k)), +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), +hb: {SV.below(SV.kept_before(sk, SV.reds(cls), c), c) == True{} : Bool}) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)) & AmbS.k(sk, SV.reds(cls), c, k):
  match k:
    case SV.Kept{+dd}:
      (+hpk, f) = p
      (nr, q1) = f
      (dok, q2) = q1
      (hnd, rest) = q2
      (st_dd(~F, x, sk, cls, hz, hf, c, dd, Equal.cong(SV.Class, List<&2, SV.Drop>, z => SV.kdd(z), SV.class_at(cls, c), SV.Kept{dd}, ek), er, Equal.trans(Bool, KB.dcond(sk, SV.reds(cls), c), SV.bnot(SV.mem(c, SV.reds(cls))), True{}, edc0, KB.bnot_f(SV.mem(c, SV.reds(cls)), er)), hb, kf, hnd, hpk), Unit{})
    case SV.Amber{+dd, +rs}:
      (+hpk, f) = p
      (nr, q1) = f
      (dok, q2) = q1
      (hnd, q3) = q2
      (ham, hall) = q3
      (st_dd(~F, x, sk, cls, hz, hf, c, dd, Equal.cong(SV.Class, List<&2, SV.Drop>, z => SV.kdd(z), SV.class_at(cls, c), SV.Amber{dd, rs}, ek), er, Equal.trans(Bool, KB.dcond(sk, SV.reds(cls), c), SV.bnot(SV.mem(c, SV.reds(cls))), True{}, edc0, KB.bnot_f(SV.mem(c, SV.reds(cls)), er)), hb, kf, hnd, hpk), hall)
    case SV.Over{+j, +s, +w}:
      (kf_same(~F, x, sk, cls, c, Equal.trans(Bool, KB.dcond(sk, SV.reds(cls), c), SV.bnot(SV.mem(c, SV.reds(cls))), False{}, edc0, (%Equal.sym(Bool, SV.mem(c, SV.reds(cls)), True{}, er) : {SV.bnot(_) == False{} : Bool}
        {==})), kf), Unit{})
    case SV.Conflict{+s, +nd}:
      (kf_same(~F, x, sk, cls, c, Equal.trans(Bool, KB.dcond(sk, SV.reds(cls), c), SV.bnot(SV.mem(c, SV.reds(cls))), False{}, edc0, (%Equal.sym(Bool, SV.mem(c, SV.reds(cls)), True{}, er) : {SV.bnot(_) == False{} : Bool}
        {==})), kf), Unit{})

# driven: not kept
def dcf(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +eb: {SV.driven(sk, c) == True{} : Bool}, +hc: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}) -> {KB.dcond(sk, R, c) == False{} : Bool}:
  %Equal.sym(Bool, SV.driven(sk, c), True{}, eb) : {SV.band(SV.band(SV.lt(c, SV.ncons(sk)), SV.bnot(_)), SV.bnot(SV.mem(c, R))) == False{} : Bool}
  %Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), True{}, hc) : {SV.band(SV.band(_, False{}), SV.bnot(SV.mem(c, R))) == False{} : Bool}
  {==}

# driving: kept iff not red
def dcv(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +eb: {SV.driven(sk, c) == False{} : Bool}, +hc: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}) -> {KB.dcond(sk, R, c) == SV.bnot(SV.mem(c, R)) : Bool}:
  %Equal.sym(Bool, SV.driven(sk, c), False{}, eb) : {SV.band(SV.band(SV.lt(c, SV.ncons(sk)), SV.bnot(_)), SV.bnot(SV.mem(c, R))) == SV.bnot(SV.mem(c, R)) : Bool}
  %Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), True{}, hc) : {SV.band(SV.band(_, True{}), SV.bnot(SV.mem(c, R))) == SV.bnot(SV.mem(c, R)) : Bool}
  {==}

def st_b(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +eb: {SV.driven(sk, c) == b : Bool}, +hc: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}, f: DH.Fate.pick(sk, cls, SV.reds(cls), SV.dropped(cls), c, b, SV.class_at(cls, c)), +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), +hb: {SV.below(SV.kept_before(sk, SV.reds(cls), c), c) == True{} : Bool})
  -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)) & AmbS.pick(sk, SV.reds(cls), c, b, SV.class_at(cls, c)):
  match b:
    case True{}:
      (kf_same(~F, x, sk, cls, c, dcf(sk, SV.reds(cls), c, eb, hc), kf), Unit{})
    case False{}:
      st_k(~F, SV.class_at(cls, c), x, sk, cls, hz, hf, c, {==}, CL.mem_reds(cls, c), dcv(sk, SV.reds(cls), c, eb, hc), fdv_rb(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.class_at(cls, c), f), kf, hb)

# The constraints in order
# ------------------------


def kf_next(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, h: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), 1n+c), sk, cls, True{}, 0n)):
  %Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls), 1n+c), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), KB.kb_next(sk, SV.reds(cls), c)) : DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), _, sk, cls, True{}, 0n))
  h

def kbp_n(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, h: KB.KBP(sk, R, SV.kept_before(sk, R, c), c)) -> KB.KBP(sk, R, SV.kept_before(sk, R, 1n+c), 1n+c):
  %Equal.sym(List<&2, Nat>, SV.kept_before(sk, R, 1n+c), KB.kpk(KB.dcond(sk, R, c), SV.kept_before(sk, R, c), c), KB.kb_next(sk, R, c)) : KB.KBP(sk, R, _, 1n+c)
  KB.kbp_next(sk, R, SV.kept_before(sk, R, c), c, h)

def kb_b(+sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, +hk: KB.KBP(sk, R, kb, c)) -> {SV.below(kb, c) == True{} : Bool}:
  +h = KB.kbp_bool(sk, R, kb, c, hk)
  LI.band_l(SV.below(kb, c), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, R)), LI.band_r(SV.distinct(kb), SV.band(SV.below(kb, c), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, R))), h))

def lt_c(+c: Nat, +m: Nat, +n: Nat, hcn: {Nat.add(c, 1n+m) == n : Nat}) -> {SV.lt(c, n) == True{} : Bool}:
  %hcn : {SV.lt(c, _) == True{} : Bool}
  DMO.lt_add(c, m)

def kf_end(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +hcn: {Nat.add(c, 0n) == SV.ncons(sk) : Nat}, kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)):
  %Equal.trans(Nat, c, Nat.add(c, 0n), SV.ncons(sk), LN.add_zero(c), hcn) : DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), _), sk, cls, True{}, 0n))
  kf

def wcmb(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +m: Nat, +c: Nat, a: AmbS(sk, cls, c), r: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, m, 1n+c)) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, 1n+m, c):
  (k, rest) = r
  (k, (a, rest))

def walk.c(~F: O.OField, +m: Nat, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, p: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), KB.kpk(KB.dcond(sk, SV.reds(cls), c), SV.kept_before(sk, SV.reds(cls), c), c), sk, cls, True{}, 0n)) & AmbS(sk, cls, c), ih: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), 1n+c), sk, cls, True{}, 0n)) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, m, 1n+c)) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, 1n+m, c):
  (kfn, a) = p
  wcmb(~F, x, sk, cls, m, c, a, ih(kf_next(~F, x, sk, cls, c, kfn)))

def walk(~F: O.OField, n: Nat, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +c: Nat, +hcn: {Nat.add(c, n) == SV.ncons(sk) : Nat}, H: DH.Honest.go(sk, cls, n, c), +kf: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), c), sk, cls, True{}, 0n)), +kbp: KB.KBP(sk, SV.reds(cls), SV.kept_before(sk, SV.reds(cls), c), c)) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, n, c):
  match n:
    case 0n:
      (kf_end(~F, x, sk, cls, c, hcn, kf), Unit{})
    case 1n++m:
      (f, H2) = H
      +hc = lt_c(c, m, SV.ncons(sk), hcn)
      walk.c(~F, m, x, sk, cls, c, st_b(~F, SV.driven(sk, c), x, sk, cls, hz, hf, c, {==}, hc, f, kf, kb_b(sk, SV.reds(cls), SV.kept_before(sk, SV.reds(cls), c), c, kbp)),
        kf1 => walk(~F, m, x, sk, cls, hz, hf, 1n+c, Equal.trans(Nat, 1n+Nat.add(c, m), Nat.add(c, 1n+m), SV.ncons(sk), LN.add_succ(c, m), hcn), H2, kf1, kbp_n(sk, SV.reds(cls), c, kbp)))

def fg_nil(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +w: Bool, +k: Nat) -> {SV.facts.go(es, own, Nil{}, sk, cls, w, k) == Nil{} : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      fg_nil(t, own, sk, cls, w, 1n+k)

def kf0(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), 0n), sk, cls, True{}, 0n)):
  %Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls), 0n), Nil{}, KB.kb_zero(sk, SV.reds(cls))) : DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), _, sk, cls, True{}, 0n))
  %Equal.sym(List<&2, DR.Fact>, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), Nil{}, sk, cls, True{}, 0n), Nil{}, fg_nil(SK.Sketch.eqs(sk), SV.owners(sk), sk, cls, True{}, 0n)) : DP.AllFacts(~F, x, SV.ents(sk), _)
  Unit{}

def kbp0(+sk: SK.Sketch, +R: List<&2, Nat>) -> KB.KBP(sk, R, SV.kept_before(sk, R, 0n), 0n):
  %Equal.sym(List<&2, Nat>, SV.kept_before(sk, R, 0n), Nil{}, KB.kb_zero(sk, R)) : KB.KBP(sk, R, _, 0n)
  KB.kbp_zero(sk, R)

def fh_go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), p: ({HR.hfacts(sk, cls) == True{} : Bool} & DH.Honest(sk, cls))) -> ({HR.hfacts(sk, cls) == True{} : Bool} & (DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, SV.ncons(sk), 0n))):
  (+hf, h) = p
  (hn, g) = h
  (hf, walk(~F, SV.ncons(sk), x, sk, cls, hz, hf, 0n, {==}, g, kf0(~F, x, sk, cls), kbp0(sk, SV.reds(cls))))

# at a geometry where the system solved holds, every fact of the kept
# constraints holds (and what each amber constraint's Fate says of its
# sides is handed on)
def facts_hold(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, h: DH.Honest(sk, cls), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls)))) -> ({HR.hfacts(sk, cls) == True{} : Bool} & (DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, SV.ncons(sk), 0n))):
  fh_go(~F, x, sk, cls, hz, hon_rb(sk, cls, h))

# The dropped equations (draft solve_drop)
# ----------------------------------------

def nth_lt(xs: List<&2, Nat>, j: Nat, +n: Nat, +hb: {SV.below(xs, n) == True{} : Bool}, hj: {SV.lt(j, SV.len(xs)) == True{} : Bool}) -> {SV.lt(SV.nth(xs, j), n) == True{} : Bool}:
  match xs j:
    case Nil{} j:
      absurd({SV.lt(SV.nth(Nil{}, j), n) == True{} : Bool}, KA.ft(KB.lt_zero(j, hj)))
    case Con{+h, +t} 0n:
      LI.band_l(SV.lt(h, n), SV.below(t, n), hb)
    case Con{+h, +t} 1n+q:
      nth_lt(t, q, n, LI.band_r(SV.lt(h, n), SV.below(t, n), hb), hj)

def ltd.c(b: Bool, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +j: Nat, +eb: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == b : Bool}, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}) -> {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      absurd({SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, KA.ft(Equal.trans(Bool, False{}, SV.mem(j, SV.dropped(cls)), True{}, Equal.sym(Bool, SV.mem(j, SV.dropped(cls)), False{}, HR.nd_past(sk, cls, j, hf, eb)), hj)))

def red_nd(k: SV.Class, +j: Nat, hm: {SV.mem(j, SV.kdrops(k)) == True{} : Bool}) -> {SV.is_red(k) == False{} : Bool}:
  match k:
    case SV.Kept{dc}:
      {==}
    case SV.Amber{dc, rs}:
      {==}
    case SV.Over{x1, x2, x3}:
      absurd({True{} == False{} : Bool}, KA.ft(hm))
    case SV.Conflict{x1, x2}:
      absurd({True{} == False{} : Bool}, KA.ft(hm))

def ndr.c(b: Bool, +sk: SK.Sketch, +j: Nat, +eb: {SV.driven(sk, SV.nth(SV.owners(sk), j)) == b : Bool}, +hjl: {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool}) -> {SV.driven(sk, SV.nth(SV.owners(sk), j)) == False{} : Bool}:
  match b:
    case True{}:
      absurd({SV.driven(sk, SV.nth(SV.owners(sk), j)) == False{} : Bool}, KA.ft(Equal.trans(Bool, False{}, SV.eq(SV.nth(SV.owners(sk), j), SV.nth(SV.owners(sk), j)), True{}, Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), j), SV.nth(SV.owners(sk), j)), False{}, OW.driven_noown(sk, SV.nth(SV.owners(sk), j), eb, j, hjl)), LI.eq_refl(SV.nth(SV.owners(sk), j)))))
    case False{}:
      eb

def jl_of(+sk: SK.Sketch, +j: Nat, hjn: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool}:
  %Equal.sym(Nat, SV.len(SV.owners(sk)), SV.neqs(SK.Sketch.eqs(sk)), OW.len_owners(sk)) : {SV.lt(j, _) == True{} : Bool}
  hjn

# the fact of the sketch's equation j, its owner kept
def fh_at(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +j: Nat, +hjn: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, hm: {SV.mem(SV.nth(SV.owners(sk), j), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk))) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)))
  -> DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), j), SV.dnd_at(cls, j), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))}):
  %Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : DP.FactHolds(~F, x, SV.ents(sk), DR.Fact{SV.eqat(SK.Sketch.eqs(sk), _), SV.dnd_at(cls, _), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), _)))})
  af_at(~F, x, sk, cls, SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), SK.Sketch.eqs(sk), 0n, {==}, j, (%LN.add_zero(j) : {SV.mem(SV.nth(SV.owners(sk), _), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk))) == True{} : Bool}
    hm), hjn, af)

# a dropped equation's constraint is driving, not red, and so kept before
# the end
def dkb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +j: Nat, +hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}, +hjn: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.mem(SV.nth(SV.owners(sk), j), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk))) == True{} : Bool}:
  +o = SV.nth(SV.owners(sk), j)
  +hjl = jl_of(sk, j, hjn)
  kb_mem(sk, SV.reds(cls), o, SV.ncons(sk), LI.band_i(SV.lt(o, SV.ncons(sk)), SV.bnot(SV.driven(sk, o)), nth_lt(SV.owners(sk), j, SV.ncons(sk), OW.below_ncons(sk), hjl), KB.bnot_f(SV.driven(sk, o), ndr.c(SV.driven(sk, o), sk, j, {==}, hjl))),
    Equal.trans(Bool, SV.mem(o, SV.reds(cls)), SV.is_red(SV.class_at(cls, o)), False{}, CL.mem_reds(cls, o), red_nd(SV.class_at(cls, o), j, Equal.trans(Bool, SV.mem(j, SV.kdrops(SV.class_at(cls, o))), SV.mem(j, SV.dropped(cls)), True{}, Equal.sym(Bool, SV.mem(j, SV.dropped(cls)), SV.mem(j, SV.kdrops(SV.class_at(cls, o))), HR.mem_dropped(sk, cls, j, hf)), hj))),
    nth_lt(SV.owners(sk), j, SV.ncons(sk), OW.below_ncons(sk), hjl))

def dl_go2(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +j: Nat, +hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, j)), +hf: {HR.hfacts(sk, cls) == True{} : Bool}, q: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, SV.ncons(sk), 0n)) -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  (af, amb) = q
  +hjn = ltd.c(SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))), sk, cls, j, {==}, hf, hj)
  +fh = fh_at(~F, x, sk, cls, j, hjn, dkb(sk, cls, hf, j, hj, hjn), af)
  (DP.fst({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), j)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j)))), DP.fact_ok(~F, x, SV.ents(sk), SV.eqat(SK.Sketch.eqs(sk), j), SV.dnd_at(cls, j), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), j))), fh, hl)), Unit{})

# DRAFT LAW (PLAN-sk13b B6, solve_drop): for an honest classification, in
# every ordered field, wherever the system solved holds and a dropped
# equation's nd segments have nonzero length, it holds
def dl_go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +j: Nat, +hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, j)), p: ({HR.hfacts(sk, cls) == True{} : Bool} & (DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & Amb.go(sk, cls, SV.ncons(sk), 0n)))) -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  (+hf, q) = p
  dl_go2(~F, x, sk, cls, j, hj, hl, hf, q)

def drop_law(~F: O.OField, +sk: SK.Sketch, +cls: List<&2, SV.Class>, h: DH.Honest(sk, cls), +x: M.Vec(~F), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +j: Nat, +hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, j)))
  -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  dl_go(~F, x, sk, cls, j, hj, hl, facts_hold(~F, x, sk, cls, h, hz))
