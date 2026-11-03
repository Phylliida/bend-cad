# bend-cad: two classifications side by side, with the direction layer
# (PLAN-sk13b B6, for honest_unique). Proofs only.
#
# Two DropsOk of the draft Honest at c, over the same kept constraints and
# the same solved equations before c, drop the same of c's equations
# (drops_ag2). As lib/agreepf.bend's drops_ag: walk c's equations in
# order, c's own equations not dropped agreeing so far. An equation
# dropped in one and kept in the other is derivable in one way in the
# first and in neither in the second:
# - by degree 0, over equal bases (agreepf's dnd);
# - by directions (ddn): the facts it may read are the same in both once
#   their nd is erased (the kept constraints' facts differ only in their
#   drops' nd; c's own are its undropped equations with its statement,
#   of_or), and a derivation reads no nd (lib/dstrippf.bend), so a
#   derivation for the first is one for the second.
#
# Generated from tools/drafts/dagreepf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./listpf.bend as L
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./agreepf.bend as AG
import ./dstrippf.bend as ST


def absurd(-A: Type, x: Empty) -> A:
  match x:

# The facts a direction drop may read, without their nd
# -----------------------------------------------------

def fs_pick(b: Bool, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>, +r1: List<&2, DR.Fact>, +r2: List<&2, DR.Fact>, +ih: {ST.fstrip(r1) == r2 : List<&2, DR.Fact>}) -> {ST.fstrip(SV.facts.pick(b, DR.Fact{e, nd, ds}, r1)) == SV.facts.pick(b, DR.Fact{e, Nil{}, ds}, r2) : List<&2, DR.Fact>}:
  match b:
    case True{}:
      %ih : {Con{DR.Fact{e, Nil{}, ds}, ST.fstrip(r1)} == Con{DR.Fact{e, Nil{}, ds}, _} : List<&2, DR.Fact>}
      {==}
    case False{}:
      ih

# the facts of some constraints, nd erased: the same with no nd
def fs_go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +w: Bool, +k: Nat) -> {ST.fstrip(SV.facts.go(es, own, cs, sk, cls, w, k)) == SV.facts.go(es, own, cs, sk, Nil{}, False{}, k) : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fs_pick(SV.mem(SV.nth(own, k), cs), e, SV.fnd.pick(w, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k))), SV.facts.go(t, own, cs, sk, cls, w, 1n+k), SV.facts.go(t, own, cs, sk, Nil{}, False{}, 1n+k), fs_go(t, own, cs, sk, cls, w, 1n+k))

# equations as facts with no nd and the statement ds
def fmk(+ds: Maybe<&2, DR.DStat>, xs: List<&2, E.QExpr>) -> List<&2, DR.Fact>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{DR.Fact{e, Nil{}, ds}, fmk(ds, t)}

def of_pick(b: Bool, +e: E.QExpr, +ds: Maybe<&2, DR.DStat>, +r: List<&2, DR.Fact>, +xs: List<&2, E.QExpr>, +ih: {r == fmk(ds, xs) : List<&2, DR.Fact>}) -> {SV.facts.pick(b, DR.Fact{e, Nil{}, ds}, r) == fmk(ds, SV.solved.pick(b, e, xs)) : List<&2, DR.Fact>}:
  match b:
    case True{}:
      %ih : {Con{DR.Fact{e, Nil{}, ds}, r} == Con{DR.Fact{e, Nil{}, ds}, _} : List<&2, DR.Fact>}
      {==}
    case False{}:
      ih

# c's own facts a drop may read are its own equations it may read, with
# its statement
def of_or(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>, +i: Nat, +k: Nat) -> {SV.ofacts.go(es, own, sk, c, d, i, k) == fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest.go(es, own, c, d, i, k)) : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      of_pick(SV.band(SV.lt(k, i), SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d)))), e, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.ofacts.go(t, own, sk, c, d, i, 1n+k), SV.own_rest.go(t, own, c, d, i, 1n+k), of_or(t, own, sk, c, d, i, 1n+k))

def fs_cat(xs: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>) -> {ST.fstrip(SV.fcat(xs, ys)) == SV.fcat(ST.fstrip(xs), ST.fstrip(ys)) : List<&2, DR.Fact>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %fs_cat(t, ys) : {Con{ST.fsx(f), ST.fstrip(SV.fcat(t, ys))} == Con{ST.fsx(f), _} : List<&2, DR.Fact>}
      {==}


# the facts drop j of c may read, nd erased
def df_n(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +j: Nat) -> {ST.fstrip(SV.dfacts(sk, cls, R, c, d, j)) == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d, j)))) : List<&2, DR.Fact>}:
  %Equal.sym(List<&2, DR.Fact>, ST.fstrip(SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n))), SV.fcat(ST.fstrip(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n)), ST.fstrip(SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n))), fs_cat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n))) : {_ == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d, j)))) : List<&2, DR.Fact>}
  %Equal.sym(List<&2, DR.Fact>, ST.fstrip(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n)), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), fs_go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n)) : {SV.fcat(_, ST.fstrip(SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n))) == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d, j)))) : List<&2, DR.Fact>}
  %Equal.sym(List<&2, DR.Fact>, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n), fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d, j)), of_or(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, j, 0n)) : {SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), ST.fstrip(_)) == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d, j)))) : List<&2, DR.Fact>}
  {==}


# over the same kept constraints, with c's own readable equations the
# same, the facts are the same once nd is erased
def df_ag(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +j: Nat, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hor: {SV.own_rest(sk, c, d1, j) == SV.own_rest(sk, c, d2, j) : List<&2, E.QExpr>}) -> {ST.fstrip(SV.dfacts(sk, cls1, R1, c, d1, j)) == ST.fstrip(SV.dfacts(sk, cls2, R2, c, d2, j)) : List<&2, DR.Fact>}:
  %Equal.sym(List<&2, DR.Fact>, ST.fstrip(SV.dfacts(sk, cls1, R1, c, d1, j)), SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R1, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d1, j)))), df_n(sk, cls1, R1, c, d1, j)) : {_ == ST.fstrip(SV.dfacts(sk, cls2, R2, c, d2, j)) : List<&2, DR.Fact>}
  %Equal.sym(List<&2, DR.Fact>, ST.fstrip(SV.dfacts(sk, cls2, R2, c, d2, j)), SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R2, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d2, j)))), df_n(sk, cls2, R2, c, d2, j)) : {SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R1, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d1, j)))) == _ : List<&2, DR.Fact>}
  %hkb : {SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R1, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d1, j)))) == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), _, sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d2, j)))) : List<&2, DR.Fact>}
  %hor : {SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R1, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.own_rest(sk, c, d1, j)))) == SV.fcat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R1, c), sk, Nil{}, False{}, 0n), ST.fstrip(fmk(SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), _))) : List<&2, DR.Fact>}
  {==}

def cx_ag(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}) -> {SV.ctx(sk, R1, c) == SV.ctx(sk, R2, c) : List<&2, E.QExpr>}:
  {==}

def ddn.v(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +j: Nat, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hor: {SV.own_rest(sk, c, d1, j) == SV.own_rest(sk, c, d2, j) : List<&2, E.QExpr>}, +nd: List<&2, Nat>, +dv: DR.Der, r: DR.Valid(SV.ents(sk), SV.dfacts(sk, cls1, R1, c, d1, j), SV.ctx(sk, R1, c), dv) & (SV.Proves(SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.eqat(SK.Sketch.eqs(sk), j), DR.concl(SV.ents(sk), SV.dfacts(sk, cls1, R1, c, d1, j), dv)) & {SV.sub(DR.nd(SV.ents(sk), SV.dfacts(sk, cls1, R1, c, d1, j), dv), nd) == True{} : Bool}),
  hn: SV.NotDirDerivable(sk, cls2, R2, c, d2, j)) -> Empty:
  (v, q) = r
  (p, s) = q
  hn(dv, (%cx_ag(sk, R1, R2, c, hkb) : DR.Valid(SV.ents(sk), SV.dfacts(sk, cls2, R2, c, d2, j), _, dv)
    ST.vtr(dv, SV.ents(sk), SV.ctx(sk, R1, c), SV.dfacts(sk, cls1, R1, c, d1, j), SV.dfacts(sk, cls2, R2, c, d2, j), df_ag(sk, cls1, R1, cls2, R2, c, d1, d2, j, hkb, hor), v)), ST.pr_tr(dv, SV.ents(sk), SV.dfacts(sk, cls1, R1, c, d1, j), SV.dfacts(sk, cls2, R2, c, d2, j), df_ag(sk, cls1, R1, cls2, R2, c, d1, d2, j, hkb, hor), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.eqat(SK.Sketch.eqs(sk), j), p))

def ddn.q(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +j: Nat, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hor: {SV.own_rest(sk, c, d1, j) == SV.own_rest(sk, c, d2, j) : List<&2, E.QExpr>}, +nd: List<&2, Nat>, q: SV.DirDerivable(sk, cls1, R1, c, d1, j, nd), hn: SV.NotDirDerivable(sk, cls2, R2, c, d2, j)) -> Empty:
  match q:
    case (+dv, r):
      ddn.v(sk, cls1, R1, cls2, R2, c, d1, d2, j, hkb, hor, nd, dv, r, hn)

# a direction derivation in the first, none in the second
def ddn(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +j: Nat, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hor: {SV.own_rest(sk, c, d1, j) == SV.own_rest(sk, c, d2, j) : List<&2, E.QExpr>}, hd: &nd: List<&2, Nat> -> SV.DirDerivable(sk, cls1, R1, c, d1, j, nd), hn: SV.NotDirDerivable(sk, cls2, R2, c, d2, j)) -> Empty:
  match hd:
    case (+nd, q):
      ddn.q(sk, cls1, R1, cls2, R2, c, d1, d2, j, hkb, hor, nd, q, hn)

# The drops at c
# --------------


# derivable in the first, in neither way in the second
def mm_tf(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +k: Nat, x1: Or(SV.Derivable(sk, R1, D1, c, d1, k), &nd: List<&2, Nat> -> SV.DirDerivable(sk, cls1, R1, c, d1, k, nd)), x2: SV.NotDerivable(sk, R2, D2, c, d2, k) & SV.NotDirDerivable(sk, cls2, R2, c, d2, k),
  +hb: {SV.basis(sk, R1, D1, c, d1, k) == SV.basis(sk, R2, D2, c, d2, k) : List<&2, E.QExpr>}, +hor: {SV.own_rest(sk, c, d1, k) == SV.own_rest(sk, c, d2, k) : List<&2, E.QExpr>}) -> Empty:
  match x1:
    case Inl{h0}:
      (n0, nd) = x2
      AG.dnd(sk, R1, D1, R2, D2, c, d1, d2, k, hb, h0, n0)
    case Inr{hd}:
      (n0, nd) = x2
      ddn(sk, cls1, R1, cls2, R2, c, d1, d2, k, hkb, hor, hd, nd)

# dropped in one exactly when in the other
def mm_ag2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, m1: Bool, m2: Bool, +k: Nat, x1: SV.drops_ok.mem(sk, cls1, R1, D1, c, d1, m1, k), x2: SV.drops_ok.mem(sk, cls2, R2, D2, c, d2, m2, k), +hb: {SV.basis(sk, R1, D1, c, d1, k) == SV.basis(sk, R2, D2, c, d2, k) : List<&2, E.QExpr>}, +hor: {SV.own_rest(sk, c, d1, k) == SV.own_rest(sk, c, d2, k) : List<&2, E.QExpr>}) -> {m1 == m2 : Bool}:
  match m1 m2:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, mm_tf(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, k, x1, x2, hb, hor))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, mm_tf(sk, cls2, R2, D2, cls1, R1, D1, c, d2, d1, Equal.sym(List<&2, Nat>, SV.kept_before(sk, R1, c), SV.kept_before(sk, R2, c), hkb), k, x2, x1, Equal.sym(List<&2, E.QExpr>, SV.basis(sk, R1, D1, c, d1, k), SV.basis(sk, R2, D2, c, d2, k), hb), Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, d1, k), SV.own_rest(sk, c, d2, k), hor)))

def at_ag2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, b: Bool, +k: Nat, a1: SV.drops_ok.at(sk, cls1, R1, D1, c, d1, b, k), a2: SV.drops_ok.at(sk, cls2, R2, D2, c, d2, b, k), +hb: {SV.basis(sk, R1, D1, c, d1, k) == SV.basis(sk, R2, D2, c, d2, k) : List<&2, E.QExpr>}, +hor: {SV.own_rest(sk, c, d1, k) == SV.own_rest(sk, c, d2, k) : List<&2, E.QExpr>}) -> {SV.mem(k, d1) == SV.mem(k, d2) : Bool}:
  match b:
    case True{}:
      mm_ag2(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, SV.mem(k, d1), SV.mem(k, d2), k, a1, a2, hb, hor)
    case False{}:
      Equal.trans(Bool, SV.mem(k, d1), False{}, SV.mem(k, d2), a1, Equal.sym(Bool, SV.mem(k, d2), False{}, a2))

def da.c(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +o: Nat, +t: List<&2, Nat>, +k: Nat, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, t} : List<&2, Nat>}, +hps: {SV.presolved(sk, R1, D1, c) == SV.presolved(sk, R2, D2, c) : List<&2, E.QExpr>}, +hor: {SV.own_rest(sk, c, d1, k) == SV.own_rest(sk, c, d2, k) : List<&2, E.QExpr>},
  g1: SV.drops_ok.at(sk, cls1, R1, D1, c, d1, SV.eq(o, c), k) & SV.drops_ok.go(sk, cls1, R1, D1, c, d1, t, 1n+k), g2: SV.drops_ok.at(sk, cls2, R2, D2, c, d2, SV.eq(o, c), k) & SV.drops_ok.go(sk, cls2, R2, D2, c, d2, t, 1n+k),
  ih: {SV.own_rest(sk, c, d1, 1n+k) == SV.own_rest(sk, c, d2, 1n+k) : List<&2, E.QExpr>} -> SV.drops_ok.go(sk, cls1, R1, D1, c, d1, t, 1n+k) -> SV.drops_ok.go(sk, cls2, R2, D2, c, d2, t, 1n+k) -> {SP.agree(t, d1, d2, c, 1n+k) == True{} : Bool})
  -> {SP.agree(Con{o, t}, d1, d2, c, k) == True{} : Bool}:
  (a1, r1) = g1
  (a2, r2) = g2
  +ek = at_ag2(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, SV.eq(o, c), k, a1, a2, AG.basis_ag(sk, R1, D1, R2, D2, c, d1, d2, k, hps, hor), hor)
  L.band_i(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, d1), SV.mem(k, d2))), SP.agree(t, d1, d2, c, 1n+k), L.bor_r(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, d1), SV.mem(k, d2)), AG.beq_of(SV.mem(k, d1), SV.mem(k, d2), ek)),
    ih(AG.or_next(sk, c, d1, d2, k, (%OW.len_owners(sk) : {SV.lt(k, _) == True{} : Bool}
      AG.lt_ndrop(SV.owners(sk), k, o, t, ho)), ek, hor), r1, r2))

def da.go2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, own_s: List<&2, Nat>, +k: Nat, +ho: {OW.ndrop(k, SV.owners(sk)) == own_s : List<&2, Nat>}, +hps: {SV.presolved(sk, R1, D1, c) == SV.presolved(sk, R2, D2, c) : List<&2, E.QExpr>}, +hor: {SV.own_rest(sk, c, d1, k) == SV.own_rest(sk, c, d2, k) : List<&2, E.QExpr>},
  g1: SV.drops_ok.go(sk, cls1, R1, D1, c, d1, own_s, k), g2: SV.drops_ok.go(sk, cls2, R2, D2, c, d2, own_s, k)) -> {SP.agree(own_s, d1, d2, c, k) == True{} : Bool}:
  match own_s:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      da.c(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, o, t, k, ho, hps, hor, g1, g2, h => r1 => r2 => da.go2(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, t, 1n+k, OW.ndrop_step(k, SV.owners(sk), o, t, ho), hps, h, r1, r2))

# two DropsOk of the draft Honest at c, over the same kept constraints and
# solved equations before c, drop the same of c's equations
def drops_ag2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +cls2: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hps: {SV.presolved(sk, R1, D1, c) == SV.presolved(sk, R2, D2, c) : List<&2, E.QExpr>}, h1: SV.DropsOk(sk, cls1, R1, D1, c, d1), h2: SV.DropsOk(sk, cls2, R2, D2, c, d2)) -> {SP.agree(SV.owners(sk), d1, d2, c, 0n) == True{} : Bool}:
  (hb1, g1) = h1
  (hb2, g2) = h2
  da.go2(sk, cls1, R1, D1, cls2, R2, D2, c, d1, d2, hkb, SV.owners(sk), 0n, {==}, hps, Equal.trans(List<&2, E.QExpr>, SV.own_rest(sk, c, d1, 0n), Nil{}, SV.own_rest(sk, c, d2, 0n), SP.or_nil(SK.Sketch.eqs(sk), SV.owners(sk), c, d1, 0n, 0n, {==}), Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, d2, 0n), Nil{}, SP.or_nil(SK.Sketch.eqs(sk), SV.owners(sk), c, d2, 0n, 0n, {==}))), g1, g2)
