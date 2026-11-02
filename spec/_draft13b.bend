# bend-cad spec (DRAFT for sk-13b, PLAN-sk13b B4.0): Honest, extended by
# the direction layer (PLAN-sk13b.md v2). Everything else it reads is
# spec/solve.bend's, where the direction layer's facts, derivations and
# refutations are defined (spec/dir.bend's calculus). At the switch these
# definitions replace spec/solve.bend's Honest and its parts, and this
# file goes. Trusted once it does.
#
# What changes from spec/solve.bend's Honest:
# - a conflict is a refutation of degree 0 or by directions, irreducible
#   for both, with the segments a direction refutation needs (nd);
# - an equation is dropped iff it has a degree-0 derivation or a
#   direction-layer one, and each drop records its reason, which is one
#   (with the nd the derivation needs);
# - Kept, Amber and Over need no refutation of either kind.

import Base
import ./sketch.bend as SK
import ./solve.bend as SV
import ./dir.bend as DR

# Honest classifications (sk-13a, extended by sk-13b), constraint by
# constraint
# -------------------------------------------------------------------
# What the answer must be, stated for each constraint c given the classes
# of the constraints before it, as exclusive cases, so the sketch decides
# every class (honest_unique, by induction along the order):
# - Conflict iff c with the premises before it has a refutation, of degree
#   0 or by directions (then with an irreducible support among them, and
#   the nd a direction refutation needs);
# - otherwise each equation of c is dropped iff it is a constant
#   combination of the solved equations before c and c's own earlier
#   equations not dropped, or has a direction-layer derivation from every
#   equation of the kept constraints before c and those (each drop
#   recording its reason: the combination, or the derivation with the nd
#   it needs);
# - otherwise Over iff c's remaining equations with the solved ones before
#   it contain a structurally over-determined set (by what the equations
#   depend on);
# - otherwise kept, and amber iff all of its equations are dropped and
#   every side condition of it is implied.
# The global facts (the kept system has no refutation; the solved
# equations are independent modulo constants; they have a matching)
# follow as theorems.

# Drops, with both layers
# ----------------------

def drops_ok.mem(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, m: Bool, +k: Nat) -> Type:
  match m:
    case True{}:
      Or(SV.Derivable(sk, red, ds, c, d, k), &nd: List<&2, Nat> -> SV.DirDerivable(sk, cls, red, c, d, k, nd))
    case False{}:
      SV.NotDerivable(sk, red, ds, c, d, k) & SV.NotDirDerivable(sk, cls, red, c, d, k)

def drops_ok.at(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, b: Bool, +k: Nat) -> Type:
  match b:
    case True{}:
      drops_ok.mem(sk, cls, red, ds, c, d, SV.mem(k, d), k)
    case False{}:
      {SV.mem(k, d) == False{} : Bool}

def drops_ok.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, own: List<&2, Nat>, +k: Nat) -> Type:
  match own:
    case Nil{}:
      Unit
    case Con{o, t}:
      drops_ok.at(sk, cls, red, ds, c, d, SV.eq(o, c), k) & drops_ok.go(sk, cls, red, ds, c, d, t, 1n+k)

# d is exactly c's derivable equations: each equation of c is in d iff it
# is a constant combination of the solved equations before c and c's own
# earlier equations not in d, or has a direction-layer derivation from
# the equations of the kept constraints before c and those; nothing else
# is in d
def DropsOk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>) -> Type:
  {SV.band(SV.distinct(d), SV.below(d, SV.neqs(SK.Sketch.eqs(sk)))) == True{} : Bool} & drops_ok.go(sk, cls, red, ds, c, d, SV.owners(sk), 0n)

# position p is an equation that equation i of c may be combined from (in
# basis): a solved equation of a constraint before c, or one of c's own
# before i not in d
def in_basis(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +p: Nat) -> Bool:
  SV.band(SV.lt(p, SV.neqs(SK.Sketch.eqs(sk))), SV.bor(SV.band(SV.lt(SV.nth(SV.owners(sk), p), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), p), red)), SV.bnot(SV.mem(p, ds)))), SV.band(SV.lt(p, i), SV.band(SV.eq(SV.nth(SV.owners(sk), p), c), SV.bnot(SV.mem(p, d))))))

def in_basis.all(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, ms: List<&2, SV.Mul>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{SV.Mul{+p, q}, t}:
      SV.band(in_basis(sk, red, ds, c, d, i, p), in_basis.all(sk, red, ds, c, d, i, t))

# a drop's reason is its witness: for equation j, a constant combination
# of equations it may be combined from that is the same polynomial as j,
# or a derivation from the facts it may read that is valid, proves j and
# needs at most the drop's nd
def why_ok(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +j: Nat, +nd: List<&2, Nat>, w: SV.Why) -> Type:
  match w:
    case SV.WLin{+ms}:
      {in_basis.all(sk, red, ds, c, d, j, ms) == True{} : Bool} & SV.Ident(SV.eqat(SK.Sketch.eqs(sk), j), SV.mlin(SK.Sketch.eqs(sk), ms))
    case SV.WDer{+dv}:
      DR.Valid(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, j), SV.ctx(sk, red, c), dv) & (SV.Proves(SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.eqat(SK.Sketch.eqs(sk), j), DR.concl(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, j), dv)) & {SV.sub(DR.nd(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, j), dv), nd) == True{} : Bool})

# each recorded drop's reason is its witness
def drops_nd(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, dd: List<&2, SV.Drop>) -> Type:
  match dd:
    case Nil{}:
      Unit
    case Con{SV.Drop{+j, +nd, w}, t}:
      why_ok(sk, cls, red, ds, c, d, j, nd, w) & drops_nd(sk, cls, red, ds, c, d, t)

def DropsNd(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> Type:
  drops_nd(sk, cls, red, ds, c, SV.drops(dd), dd)

# kept with the drops dd: no refutation of either kind, dd exactly the
# derivable equations, each with its reason, no over-determined
# set, and not amber (if every equation is dropped, some side condition
# is not implied)
def KeptOk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> Type:
  SV.NoRefute2(sk, red, c) & (DropsOk(sk, cls, red, ds, c, SV.drops(dd)) & (DropsNd(sk, cls, red, ds, c, dd) & (SV.Matchable(SK.cat(SV.presolved(sk, red, ds, c), SV.own_rest(sk, c, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))) & ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} -> &i: Nat -> ({SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool} & SV.NotImplied(sk, red, c, i))))))

# each side condition of c from position i on (ss, the rest of c's
# sides) is implied: one Implied per side, so that each can be used
def implied.go(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, ss: List<&2, SK.Side>, +i: Nat) -> Type:
  match ss:
    case Nil{}:
      Unit
    case Con{s, t}:
      SV.Implied(sk, red, c, i) & implied.go(sk, red, c, t, 1n+i)

def AllImplied(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> Type:
  implied.go(sk, red, c, SV.csides(sk, [c]), 0n)

# amber with the drops dd: no refutation, dd exactly the derivable
# equations with their reasons, all of c's equations, every side implied
def AmberOk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> Type:
  SV.NoRefute2(sk, red, c) & (DropsOk(sk, cls, red, ds, c, SV.drops(dd)) & (DropsNd(sk, cls, red, ds, c, dd) & ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} & AllImplied(sk, red, c))))

# Over with equation j in the over-determined set s over w: no
# refutation, and with c's derivable equations d set aside, s is made of
# c's other equations and earlier solved ones
def OverOk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Type:
  SV.NoRefute2(sk, red, c) & (&d: List<&2, Nat> -> (DropsOk(sk, cls, red, ds, c, d) & {SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), red, ds, d, c, s))) == True{} : Bool} & SV.Overdet(SK.Sketch.eqs(sk), s, w)))

# Conflict with support s and nd: kept, driving constraints before c; c
# and s have a refutation, of degree 0 or by directions needing at most
# nd; without any one member of s they have none of either kind (in c's
# own context, which fixes the collapsed segments, so that refutability
# grows with the constraints)
def ConflictOk(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>) -> Type:
  {SV.band(SV.distinct(s), SV.band(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red)))) == True{} : Bool} & (Or(SV.Ref0(sk, c, s), SV.DirRefutes(sk, c, s, SV.ctx(sk, red, c), nd)) & (@m: Nat -> {SV.mem(m, s) == True{} : Bool} -> (SV.NoRef0(sk, c, SV.unmark(m, s)) & SV.NoDirRef(sk, c, SV.unmark(m, s), SV.ctx(sk, red, c)))))

def Fate.driving(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, k: SV.Class) -> Type:
  match k:
    case SV.Kept{+dc}:
      KeptOk(sk, cls, red, ds, c, dc)
    case SV.Amber{+dc, rs}:
      AmberOk(sk, cls, red, ds, c, dc)
    case SV.Over{+j, +s, +w}:
      OverOk(sk, cls, red, ds, c, j, s, w)
    case SV.Conflict{+s, +nd}:
      ConflictOk(sk, red, c, s, nd)

# a driven constraint means nothing: kept, nothing dropped
def Fate.driven(k: SV.Class) -> Type:
  match k:
    case SV.Kept{dc}:
      {SV.drops(dc) == Nil{} : List<&2, Nat>}
    case SV.Amber{dc, rs}:
      Empty
    case SV.Over{j, s, w}:
      Empty
    case SV.Conflict{s, nd}:
      Empty

def Fate.pick(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, b: Bool, +k: SV.Class) -> Type:
  match b:
    case True{}:
      Fate.driven(k)
    case False{}:
      Fate.driving(sk, cls, red, ds, c, k)

# the constraint at position c has its honest class, given the others'
def Fate(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat) -> Type:
  Fate.pick(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.driven(sk, c), SV.class_at(cls, c))

def Honest.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      Fate(sk, cls, c) & Honest.go(sk, cls, m, 1n+c)

# an honest classification of the sketch: one class per constraint, each
# the honest one given the classes before it
def Honest(+sk: SK.Sketch, +cls: List<&2, SV.Class>) -> Type:
  {SV.clsn(cls) == SV.ncons(sk) : Nat} & Honest.go(sk, cls, SV.ncons(sk), 0n)
