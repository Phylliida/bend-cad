# bend-cad: the single pass (PLAN-sk13a S4). The constraints are walked
# once, in order; each driving constraint c gets exactly one class
# (spec/solve.bend: Class), the honest one given the classes before it:
# - Conflict, if c with the kept constraints before it has a degree-0
#   refutation (lib/refute.bend), with the deletion filter's support
#   (lib/conflict.bend);
# - otherwise c's equations are reduced in order against the solved
#   equations before c and c's own earlier ones kept (lib/elim.bend): each
#   is dropped (a combination of them, with its certificate) or joins the
#   basis;
# - then c's equations left are matched as a unit, by augmenting paths over
#   what each equation depends on (lib/deppf.bend: dadj; lib/struct.bend:
#   search); if one fails, the matching goes back to what it was, and c is
#   Over with that search's witness;
# - otherwise c is kept, and amber when all its equations are dropped and
#   every side condition of it is implied by the premises before it (each
#   side's negation refuted with them).
# A driven constraint is kept with nothing dropped.
#
# The state: the kept constraints so far, the basis's echelon rows, the
# basis (the solved equations before c, in sketch order) and its
# positions, and the matching (each variable's equation).
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/passpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DR
import ./refute.bend as RF
import ./conflict.bend as CO
import ./struct.bend as ST
import ./deppf.bend as DP

# The sketch's parts
# ------------------

def recs(sk: SK.Sketch) -> List<&2, SK.Rec>:
  match sk:
    case SK.Sketch{vs, es, cs}:
      cs

def vlen(vs: List<&2, SK.VKind>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case Con{v, t}:
      1n+vlen(t)

def nvars(sk: SK.Sketch) -> Nat:
  match sk:
    case SK.Sketch{vs, es, cs}:
      vlen(vs)

# what each equation depends on
def dadjs(es: List<&2, E.QExpr>) -> List<&2, List<&2, Nat>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{DP.dadj(e), dadjs(t)}

# Drop certificates
# -----------------
# A dropped equation e = l . B (the spec's Derivable): h = 1 and l_i times
# the basis equation at position bp_i.

def muls(bp: List<&2, Nat>, ls: List<&2, S.Q>) -> List<&2, SV.Mul>:
  match bp ls:
    case Nil{} ls:
      Nil{}
    case Con{i, it} Nil{}:
      Nil{}
    case Con{i, it} Con{l, lt}:
      Con{SV.Mul{i, E.QCst{l}}, muls(it, lt)}

def qone() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

def drop_of(+j: Nat, +r: EL.Res, +e: E.QExpr, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>) -> SV.Drop:
  SV.Drop{j, SV.Comb{E.QCst{qone()}, muls(bp, DR.dropls(DR.rescb(r), DR.resbt(r), e, B))}}

# A constraint's equations
# ------------------------
# All positions are walked; those c owns are reduced in turn. rows are the
# basis B's (EP.rinv), bp its positions; ds the drops so far (newest first)
# and us c's equations that joined the basis (in order).

type CW is Data:
  CW{rows: List<&2, EL.Row>, B: List<&2, E.QExpr>, bp: List<&2, Nat>, ds: List<&2, SV.Drop>, us: List<&2, Nat>}

def cw.pick(b: Bool, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>, us: List<&2, Nat>) -> CW:
  match b:
    case True{}:
      CW{rows, B, bp, Con{drop_of(k, r, e, B, bp), ds}, us}
    case False{}:
      CW{EL.rsnoc(rows, EL.row_of(r)), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}

def cw.res(+k: Nat, +e: E.QExpr, st: CW) -> CW:
  match st:
    case CW{+rows, +B, +bp, ds, us}:
      +r = EL.resid(rows, e)
      cw.pick(EP.isnil(EP.resp(r)), k, e, r, rows, B, bp, ds, us)

def cw.at(o: Bool, +k: Nat, +e: E.QExpr, st: CW) -> CW:
  match o:
    case True{}:
      cw.res(k, e, st)
    case False{}:
      st

# the equations es from position k (own the owners)
def cwalk(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, st: CW) -> CW:
  match es:
    case Nil{}:
      st
    case Con{e, t}:
      cwalk(t, own, c, 1n+k, cw.at(SV.eq(SV.nth(own, k), c), k, e, st))

# Matching a constraint's equations as a unit
# --------------------------------------------

# the equations us, in turn
def grpl(us: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, st: ST.GS) -> ST.GS:
  match us st:
    case Nil{} st:
      st
    case Con{+u, t} ST.GOk{+vm}:
      grpl(t, adj, f, ST.gstep(u, ST.search(f, adj, vm, u), vm))
    case Con{u, t} ST.GFail{r}:
      ST.GFail{r}

# Side conditions implied
# -----------------------

def srefs.c(m: Maybe<&2, RF.Cert>, r: Maybe<&2, List<&2, SV.Ref>>) -> Maybe<&2, List<&2, SV.Ref>>:
  match m r:
    case None{} r:
      None{}
    case Some{RF.Cert{ls, ms, k}} None{}:
      None{}
    case Some{RF.Cert{ls, ms, k}} Some{rs}:
      Some{Con{SV.Ref{ls, ms, k}, rs}}

# the premises kb before c (with the entities' sides) and the negation of
# c's i-th side condition (the spec's neg_pre, kb being kept_before)
def neg_kb(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat) -> List<&2, SK.Side>:
  SK.cats(SK.cats(SV.csides(sk, kb), SV.esides(sk)), [SV.negate(SV.side_at(SV.csides(sk, [c]), i))])

# each of c's side conditions ss (from the i-th) refuted with the premises
# kb before c, or None if one is not
def srefs(ss: List<&2, SK.Side>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat) -> Maybe<&2, List<&2, SV.Ref>>:
  match ss:
    case Nil{}:
      Some{Nil{}}
    case Con{s, t}:
      srefs.c(RF.refute(SV.eqs_of(sk, kb), neg_kb(sk, kb, c, i)), srefs(t, sk, kb, c, 1n+i))

# One constraint
# --------------
# The state: kb, the kept (not red) driving constraints so far; rows, the
# basis B's echelon rows; B, the solved equations so far, in sketch order,
# and bp their positions; vm, the matching (each variable's equation).

type PS is Data:
  PS{kb: List<&2, Nat>, rows: List<&2, EL.Row>, B: List<&2, E.QExpr>, bp: List<&2, Nat>, vm: List<&2, Maybe<&2, Nat>>}

type PO is Data:
  PO{k: SV.Class, st: PS}

def PO.k(o: PO) -> SV.Class:
  match o:
    case PO{k, st}:
      k

def PO.st(o: PO) -> PS:
  match o:
    case PO{k, st}:
      st

def one.a(m: Maybe<&2, List<&2, SV.Ref>>, +dd: List<&2, SV.Drop>) -> SV.Class:
  match m:
    case None{}:
      SV.Kept{dd}
    case Some{rs}:
      SV.Amber{dd, rs}

def one.k(a: Bool, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> SV.Class:
  match a:
    case True{}:
      one.a(srefs(SV.csides(sk, [c]), sk, kb, c, 0n), dd)
    case False{}:
      SV.Kept{dd}

def one.g(g: ST.GS, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, w: CW) -> PO:
  match g w:
    case ST.GFail{ST.Red{j, s, x}} w:
      PO{SV.Over{j, s, x}, PS{kb, rows, B, bp, vm}}
    case ST.GOk{vm2} CW{rows2, B2, bp2, +dd, us}:
      PO{one.k(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd), PS{CO.lsnoc(kb, c), rows2, B2, bp2, vm2}}

def cw.us(w: CW) -> List<&2, Nat>:
  match w:
    case CW{rows, B, bp, ds, us}:
      us

def one.w(+w: CW, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>) -> PO:
  one.g(grpl(cw.us(w), adj, f, ST.GOk{vm}), sk, c, kb, rows, B, bp, vm, w)

def one.c(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>) -> PO:
  match b:
    case True{}:
      PO{SV.Conflict{CO.support(sk, c, kb)}, PS{kb, rows, B, bp, vm}}
    case False{}:
      one.w(cwalk(es, own, c, 0n, CW{rows, B, bp, Nil{}, Nil{}}), sk, adj, f, c, kb, rows, B, bp, vm)

# the driving constraint at position c
def one(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PS) -> PO:
  match st:
    case PS{+kb, +rows, +B, +bp, +vm}:
      one.c(CO.refutable(sk, c, kb), es, own, sk, adj, f, c, kb, rows, B, bp, vm)

# The pass
# --------

# the constraints rs from position i
def pass(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PS) -> List<&2, SV.Class>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      Con{SV.Kept{Nil{}}, pass(t, es, own, sk, adj, f, 1n+i, st)}
    case Con{SK.Rec{id, False{}, k}, t}:
      +o = one(es, own, sk, adj, f, i, st)
      Con{PO.k(o), pass(t, es, own, sk, adj, f, 1n+i, PO.st(o))}

def start(+nv: Nat) -> PS:
  PS{Nil{}, Nil{}, Nil{}, Nil{}, ST.nones(nv)}

# every constraint's class
def classes(+sk: SK.Sketch) -> List<&2, SV.Class>:
  pass(recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, dadjs(SK.Sketch.eqs(sk)), 1n+nvars(sk), 0n, start(nvars(sk)))
