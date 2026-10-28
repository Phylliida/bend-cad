# bend-cad: the direction layer's closure (PLAN-sk13b B3, "Closure, as
# designed 2026-10-27", audited in AUDIT-sk13b-closure.md). Given the facts
# fs, the context ctx and a tag variable t past every variable, it finds
# every derivable judgment of spec/dir.bend's calculus, as a finite state:
# - K: the span of K facts (lib/kspace.bend);
# - the open nodes (F and the segments not collapsed in ctx) in a forest,
#   F always a root: each has a root r and a label w with a derivation of
#   par(r, x), x the same form as w z_a, so par(a, y) iff w y is in r's set;
#   F's set is {y : Im y in K}, another root's is the span of its
#   generators (a hull, lib/hspace.bend);
# - links from collapsed segments c: derivations of par(c, x), x the same
#   as w z_b, at most two independent w per pair.
# The skeleton (K, the forest, the links) grows by one item per round, at
# the first failing check; the sets are rebuilt from it each round. A
# fixpoint is closed under every rule (proven in lib/dclosepf.bend), and
# an explosion (1 in K, or an open direction in K squared) makes every
# judgment derivable.
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./pair.bend as PT
import ./lab.bend as LB
import ./indset.bend as IS
import ./seppf.bend as SP

# Nodes
# -----

def node_eq(a: DR.Node, +b: DR.Node) -> Bool:
  match a:
    case DR.NFrame{}:
      match b:
        case DR.NFrame{}:
          True{}
        case DR.NSeg{t}:
          False{}
    case DR.NSeg{s}:
      match b:
        case DR.NFrame{}:
          False{}
        case DR.NSeg{t}:
          SV.eq(s, t)

def segids.of(+id: Nat, g: SK.Geo, rest: List<&2, Nat>) -> List<&2, Nat>:
  match g:
    case SK.GPoint{x, y}:
      rest
    case SK.GSeg{p, q}:
      Con{id, rest}
    case SK.GCirc{c, r}:
      rest
    case SK.GArc{s, e, b}:
      rest

# the sketch's segment ids
def segids(es: List<&2, SK.Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case Con{SK.Ent{id, cons, g}, t}:
      segids.of(id, g, segids(t))

def snodes(ids: List<&2, Nat>) -> List<&2, DR.Node>:
  match ids:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{DR.NSeg{s}, snodes(t)}

# The context's span
# ------------------

type SP is Data:
  SP{rows: List<&2, EL.Row>, bs: List<&2, E.QExpr>}

def sp.rows(s: SP) -> List<&2, EL.Row>:
  match s:
    case SP{rows, bs}:
      rows

def sp.pick(b: Bool, +rows: List<&2, EL.Row>, +bs: List<&2, E.QExpr>, +r: EL.Res, +e: E.QExpr) -> SP:
  match b:
    case True{}:
      SP{rows, bs}
    case False{}:
      SP{EL.rsnoc(rows, EL.row_of(r)), EP.qsnoc(bs, e)}

def sp.add(s: SP, +e: E.QExpr) -> SP:
  match s:
    case SP{+rows, +bs}:
      +r = EL.resid(rows, e)
      sp.pick(EP.isnil(EP.resp(r)), rows, bs, r, e)

def sp.of(es: List<&2, E.QExpr>, s: SP) -> SP:
  match es:
    case Nil{}:
      s
    case Con{e, t}:
      sp.of(t, sp.add(s, e))

def sp.inb(+s: SP, +e: E.QExpr) -> Bool:
  EP.isnil(EP.resp(EL.resid(sp.rows(s), e)))

# segment s is collapsed in the context
def coll(+es: List<&2, SK.Ent>, +cs: SP, +s: Nat) -> Bool:
  SV.band(sp.inb(cs, SK.VE.x(DR.zseg(es, s))), sp.inb(cs, SK.VE.y(DR.zseg(es, s))))

def isopen(+es: List<&2, SK.Ent>, +cs: SP, n: DR.Node) -> Bool:
  match n:
    case DR.NFrame{}:
      True{}
    case DR.NSeg{s}:
      SV.bnot(coll(es, cs, s))

# Lists
# -----

def dcat(xs: List<&2, DR.Der>, ys: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match xs:
    case Nil{}:
      ys
    case Con{x, t}:
      Con{x, dcat(t, ys)}

def dpick(b: Bool, +x: DR.Der, rest: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match b:
    case True{}:
      Con{x, rest}
    case False{}:
      rest

def dcatif(b: Bool, xs: List<&2, DR.Der>, ys: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match b:
    case True{}:
      dcat(xs, ys)
    case False{}:
      ys

def ddrop(n: Nat, ds: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match n ds:
    case 0n ds:
      ds
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{d, t}:
      ddrop(m, t)

def dlen(ds: List<&2, DR.Der>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      1n+dlen(t)

# Labels
# ------

def lone() -> DR.Lab:
  DR.Lab{DR.qo(), DR.qz()}

def li() -> DR.Lab:
  DR.Lab{DR.qz(), DR.qo()}

# the rotation by g as a form: g times (1, 0)
def lform(g: DR.Lab) -> SK.VE:
  DR.gmul(g, SK.VE{DR.cst(DR.qo()), DR.cst(DR.qz())})

def lpar.go(+c1: S.Q, +s1: S.Q, w2: DR.Lab) -> Bool:
  match w2:
    case DR.Lab{c2, s2}:
      SV.bnot(DR.qnz(S.Q.sub(S.Q.mul(c1, s2), S.Q.mul(s1, c2))))

# w1 and w2 are real multiples of each other (as vectors of Q^2)
def lpar(w1: DR.Lab, +w2: DR.Lab) -> Bool:
  match w1:
    case DR.Lab{c1, s1}:
      lpar.go(c1, s1, w2)

# w lies in the span of ws, as the links store them: none, one, or two
# independent
def qspan(ws: List<&2, DR.Lab>, +w: DR.Lab) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w0, Nil{}}:
      lpar(w0, w)
    case Con{w0, Con{w1, t}}:
      True{}

# K squared, as a hull's generators
# ---------------------------------

def kgens(+r: DR.Node, ds: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, t}:
      Con{HS.kre(r, d), Con{HS.kim(r, d), kgens(r, t)}}

# Statements
# ----------

def stat_ok(ds: Maybe<&2, DR.DStat>, +s: Nat) -> Bool:
  match ds:
    case Some{DR.DStat{a, x, l}}:
      SV.band(SV.eq(a, s), DR.qnz(l))
    case None{}:
      False{}

def stats.pick(b: Bool, +i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{i, rest}
    case False{}:
      rest

# the positions of the facts with a statement at segment s
def stats(fs: List<&2, DR.Fact>, +s: Nat, +i: Nat) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{DR.Fact{e, nd, ds}, t}:
      stats.pick(stat_ok(ds, s), i, stats(t, s, 1n+i))

def nstats(+fs: List<&2, DR.Fact>, n: DR.Node) -> List<&2, Nat>:
  match n:
    case DR.NFrame{}:
      Nil{}
    case DR.NSeg{s}:
      stats(fs, s, 0n)

def pprems(ix: List<&2, Nat>) -> List<&2, DR.Der>:
  match ix:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Con{DR.DPPrem{i}, pprems(t)}

# The skeleton
# ------------

# an open node a: d proves par(r, x), x the same as w z_a
type Mem is Data:
  Mem{a: DR.Node, r: DR.Node, w: DR.Lab, d: DR.Der}

# a link from the collapsed segment c: d proves par(c, x), x the same as
# w z_b
type Link is Data:
  Link{c: Nat, b: DR.Node, w: DR.Lab, d: DR.Der}

type Sk is Data:
  Sk{k: KS.KS, ms: List<&2, Mem>, ls: List<&2, Link>}

def Mem.r(m: Mem) -> DR.Node:
  match m:
    case Mem{a, r, w, d}:
      r

def Sk.k(s: Sk) -> KS.KS:
  match s:
    case Sk{k, ms, ls}:
      k

def Sk.ms(s: Sk) -> List<&2, Mem>:
  match s:
    case Sk{k, ms, ls}:
      ms

def Sk.ls(s: Sk) -> List<&2, Link>:
  match s:
    case Sk{k, ms, ls}:
      ls

# K from the facts at positions i, i+1, ...
def kinit(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, rest: List<&2, DR.Fact>, +i: Nat, k: KS.KS) -> KS.KS:
  match rest:
    case Nil{}:
      k
    case Con{f, t}:
      kinit(es, fs, t, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}))

def mpick(b: Bool, +n: DR.Node, rest: List<&2, Mem>) -> List<&2, Mem>:
  match b:
    case True{}:
      Con{Mem{n, n, lone(), DR.DSelf{n}}, rest}
    case False{}:
      rest

# every open node its own root
def minit(ns: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +cs: SP) -> List<&2, Mem>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      mpick(isopen(es, cs, n), n, minit(t, es, cs))

def sk0(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: SP) -> Sk:
  Sk{kinit(es, fs, fs, 0n, KS.ks0()), minit(Con{DR.NFrame{}, snodes(segids(es))}, es, cs), Nil{}}

def mem_or(b: Bool, +m: Mem, rest: Maybe<&2, Mem>) -> Maybe<&2, Mem>:
  match b:
    case True{}:
      Some{m}
    case False{}:
      rest

def Mem.a(m: Mem) -> DR.Node:
  match m:
    case Mem{a, r, w, d}:
      a

# the member record of node a
def mem_of(ms: List<&2, Mem>, +a: DR.Node) -> Maybe<&2, Mem>:
  match ms:
    case Nil{}:
      None{}
    case Con{+m, t}:
      mem_or(node_eq(Mem.a(m), a), m, mem_of(t, a))

# Generators
# ----------

# through at a, from d proving par(r, w z_a)
def thr(+d: DR.Der, +w: DR.Lab, +a: DR.Node, +d2: DR.Der) -> DR.Der:
  DR.DThrough{d, d2, DR.Lab.conj(w), a}

def lstats(ps: List<&2, DR.Der>, +a: DR.Node, +w: DR.Lab, +d: DR.Der) -> List<&2, DR.Der>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{thr(d, w, a, p), lstats(t, a, w, d)}

# a link from c to a member a, turned at a and passed through it
def llinks(ls: List<&2, Link>, +a: DR.Node, +w: DR.Lab, +d: DR.Der) -> List<&2, DR.Der>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{c, b, wl, dl}, t}:
      dpick(node_eq(b, a), thr(d, w, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), llinks(t, a, w, d))

def mgens(+fs: List<&2, DR.Fact>, +ls: List<&2, Link>, m: Mem) -> List<&2, DR.Der>:
  match m:
    case Mem{+a, r, +w, +d}:
      Con{d, dcat(lstats(pprems(nstats(fs, a)), a, w, d), llinks(ls, a, w, d))}

# the generators of root r: what its members give
def rgens(+fs: List<&2, DR.Fact>, +r: DR.Node, ms: List<&2, Mem>, +ls: List<&2, Link>) -> List<&2, DR.Der>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+m, t}:
      dcatif(node_eq(Mem.r(m), r), mgens(fs, ls, m), rgens(fs, r, t, ls))

def hfold(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS) -> HS.HS:
  match ds:
    case Nil{}:
      h
    case Con{+d, tl}:
      hfold(tl, es, fs, t, HS.hs.add(es, fs, t, h, d))

# K squared's part of a hull at r
def khull(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +r: DR.Node) -> HS.HS:
  hfold(kgens(r, KS.ks.ds(k)), es, fs, t, HS.hs0())

# a root's hull: K squared's generators first, then its own
def rhull(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node) -> HS.HS:
  hfold(rgens(fs, r, Sk.ms(s), Sk.ls(s)), es, fs, t, khull(es, fs, t, Sk.k(s), r))

# Collapsed nodes
# ---------------

# a tied set's span: cross(u, x) over the generators, u the tie's form
type TS is Data:
  TS{rows: List<&2, EL.Row>, ds: List<&2, DR.Der>}

def ts.rows(s: TS) -> List<&2, EL.Row>:
  match s:
    case TS{rows, ds}:
      rows

def ts.ds(s: TS) -> List<&2, DR.Der>:
  match s:
    case TS{rows, ds}:
      ds

def ts.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der) -> TS:
  match b:
    case True{}:
      TS{rows, ds}
    case False{}:
      TS{EL.rsnoc(rows, EL.row_of(r)), KS.dsnoc(ds, d)}

def ts.add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, s: TS, +d: DR.Der) -> TS:
  match s:
    case TS{+rows, +ds}:
      +r = EL.resid(rows, SK.VE.cross(lform(u), DR.Jd.x(DR.concl(es, fs, d))))
      ts.pick(EP.isnil(EP.resp(r)), rows, ds, r, d)

def tfold(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, s: TS) -> TS:
  match ds:
    case Nil{}:
      s
    case Con{+d, tl}:
      tfold(tl, es, fs, u, ts.add(es, fs, u, s, d))

def ts.inb(+s: TS, +u: DR.Lab, +y: SK.VE) -> Bool:
  EP.isnil(EP.resp(EL.resid(ts.rows(s), SK.VE.cross(lform(u), y))))

def crosses(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, ds: List<&2, DR.Der>) -> List<&2, E.QExpr>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{SK.VE.cross(lform(u), DR.Jd.x(DR.concl(es, fs, d))), crosses(es, fs, u, t)}

# a collapsed segment's set
type Rep is Data:
  # z_c in K squared: every form
  RFull{}
  # the span of its generators
  RFree{h: HS.HS}
  # tied to the constant u by du (par(c, x), x the same as u (1, 0)):
  # {y : cross(u, y) in the span of cross(u, its generators)}
  RTied{u: DR.Lab, du: DR.Der, ts: TS}

def lstored.pick(f: Bool, +w: DR.Lab, rest: List<&2, DR.Lab>) -> List<&2, DR.Lab>:
  match f:
    case True{}:
      Con{w, rest}
    case False{}:
      rest

# the links' labels from c to b
def lstored(ls: List<&2, Link>, +c: Nat, +b: DR.Node) -> List<&2, DR.Lab>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{c2, bl, w, d}, t}:
      lstored.pick(SV.band(SV.eq(c2, c), node_eq(bl, b)), w, lstored(t, c, b))

def lout.gens(hs: List<&2, DR.Der>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der) -> List<&2, DR.Der>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{DR.DThrough{dl, DR.DThrough{DR.DTurn{db, DR.Lab.conj(wb), b}, h, wb, rb}, DR.Lab.conj(wl), b}, lout.gens(t, b, wl, dl, rb, wb, db)}

def lout.root(f: Bool, +fs: List<&2, DR.Fact>, +ms: List<&2, Mem>, +ls: List<&2, Link>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der) -> List<&2, DR.Der>:
  match f:
    case True{}:
      Con{DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}, Nil{}}
    case False{}:
      lout.gens(rgens(fs, rb, ms, ls), b, wl, dl, rb, wb, db)

# what a link from c to b gives c: itself, and through b: a tie when b is
# in F's component, else the root's generators turned to b
def lout.mem(m: Maybe<&2, Mem>, +fs: List<&2, DR.Fact>, +ms: List<&2, Mem>, +ls: List<&2, Link>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der) -> List<&2, DR.Der>:
  match m:
    case None{}:
      Nil{}
    case Some{Mem{a, +rb, wb, db}}:
      lout.root(node_eq(rb, DR.NFrame{}), fs, ms, ls, b, wl, dl, rb, wb, db)

def louts(ls: List<&2, Link>, +c: Nat, +fs: List<&2, DR.Fact>, +ms: List<&2, Mem>, +all: List<&2, Link>) -> List<&2, DR.Der>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{c2, +b, +wl, +dl}, t}:
      dcatif(SV.eq(c2, c), Con{dl, lout.mem(mem_of(ms, b), fs, ms, all, b, wl, dl)}, louts(t, c, fs, ms, all))

# what a link from another collapsed c2 to c gives c: the turn
def lins(ls: List<&2, Link>, +c: Nat) -> List<&2, DR.Der>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Link{c2, b, wl, dl}, t}:
      dpick(node_eq(b, DR.NSeg{c}), DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, lins(t, c))

# c's generators
def cgens(+fs: List<&2, DR.Fact>, +s: Sk, +c: Nat) -> List<&2, DR.Der>:
  Con{DR.DSelf{DR.NSeg{c}}, dcat(pprems(stats(fs, c, 0n)), dcat(louts(Sk.ls(s), c, fs, Sk.ms(s), Sk.ls(s)), lins(Sk.ls(s), c)))}

# a label with a derivation
type LD is Data:
  LD{u: DR.Lab, d: DR.Der}

def ctie.pick(b: Bool, +x: LD, rest: Maybe<&2, LD>) -> Maybe<&2, LD>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def ctie.mem(m: Maybe<&2, Mem>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, rest: Maybe<&2, LD>) -> Maybe<&2, LD>:
  match m:
    case None{}:
      rest
    case Some{Mem{a, rb, +wb, +db}}:
      ctie.pick(node_eq(rb, DR.NFrame{}), LD{LB.lmul(wl, DR.Lab.conj(wb)), DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}}, rest)

def ctie.if(f: Bool, m: Maybe<&2, Mem>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, rest: Maybe<&2, LD>) -> Maybe<&2, LD>:
  match f:
    case True{}:
      ctie.mem(m, b, wl, dl, rest)
    case False{}:
      rest

# c's first tie: a link into F's component, through its node; the tie is
# u (1, 0), u the link's label times the conjugate of the node's
def cties(ls: List<&2, Link>, +c: Nat, +ms: List<&2, Mem>) -> Maybe<&2, LD>:
  match ls:
    case Nil{}:
      None{}
    case Con{Link{c2, +b, +wl, +dl}, t}:
      ctie.if(SV.eq(c2, c), mem_of(ms, b), b, wl, dl, cties(t, c, ms))

# c's direction is in K squared
def fullc(+es: List<&2, SK.Ent>, +k: KS.KS, +c: Nat) -> Bool:
  SV.band(KS.ks.inb(k, SK.VE.x(DR.zseg(es, c))), KS.ks.inb(k, SK.VE.y(DR.zseg(es, c))))

def crep.t(m: Maybe<&2, LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +gens: List<&2, DR.Der>) -> Rep:
  match m:
    case None{}:
      RFree{hfold(gens, es, fs, t, HS.hs0())}
    case Some{LD{+u, du}}:
      RTied{u, du, tfold(gens, es, fs, u, TS{Nil{}, Nil{}})}

def crep.f(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat) -> Rep:
  match b:
    case True{}:
      RFull{}
    case False{}:
      crep.t(cties(Sk.ls(s), c, Sk.ms(s)), es, fs, t, dcat(kgens(DR.NSeg{c}, KS.ks.ds(Sk.k(s))), cgens(fs, s, c)))

# a collapsed segment's set
def crep(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat) -> Rep:
  crep.f(fullc(es, Sk.k(s), c), es, fs, t, s, c)

def rep.inb(r: Rep, +t: Nat, +y: SK.VE) -> Bool:
  match r:
    case RFull{}:
      True{}
    case RFree{h}:
      HS.hs.inb(h, y, t)
    case RTied{u, du, ts}:
      ts.inb(ts, u, y)

def ts.lab(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +s: TS, +z: SK.VE) -> Maybe<&2, DR.Lab>:
  LB.lab_map(PT.ptest(ts.rows(s), crosses(es, fs, u, ts.ds(s)), SK.VE.cross(lform(u), z), SK.VE.cross(lform(u), DR.imul(z))))

def bpair(b: Bool, +w: DR.Lab) -> List<&2, DR.Lab>:
  match b:
    case True{}:
      Con{w, Con{LB.lmul(li(), w), Nil{}}}
    case False{}:
      Con{w, Nil{}}

def basis.free(m: Maybe<&2, DR.Lab>, +t: Nat, +h: HS.HS, +z: SK.VE) -> List<&2, DR.Lab>:
  match m:
    case None{}:
      Nil{}
    case Some{+w}:
      bpair(HS.hs.inb(h, DR.gmul(LB.lmul(li(), w), z), t), w)

def basis.tied(m: Maybe<&2, DR.Lab>, +u: DR.Lab, +s: TS, +z: SK.VE) -> List<&2, DR.Lab>:
  match m:
    case None{}:
      Nil{}
    case Some{+w}:
      bpair(ts.inb(s, u, DR.gmul(LB.lmul(li(), w), z)), w)

def basis.k(m: Maybe<&2, DR.Lab>, +k: KS.KS, +z: SK.VE) -> List<&2, DR.Lab>:
  match m:
    case None{}:
      Nil{}
    case Some{+w}:
      bpair(KS.ks.inb(k, SK.VE.y(DR.gmul(LB.lmul(li(), w), z))), w)

# a basis of {w : w z in the set}
def rep.basis(r: Rep, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +z: SK.VE) -> List<&2, DR.Lab>:
  match r:
    case RFull{}:
      Con{lone(), Con{li(), Nil{}}}
    case RFree{+h}:
      basis.free(LB.hs.lab(es, fs, t, h, z), t, h, z)
    case RTied{+u, du, +s}:
      basis.tied(ts.lab(es, fs, u, s, z), u, s, z)

def lnorm(g: DR.Lab) -> S.Q:
  match g:
    case DR.Lab{+c, +s}:
      S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))

# y in a tied set: y = (the generators' combination) + p u, p =
# dot(u, the rest) / |u|^2, the second part through F
def tied.der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +u: DR.Lab, +du: DR.Der, +s: TS, +y: SK.VE) -> DR.Der:
  +e = SK.VE.cross(lform(u), y)
  +res = EL.resid(ts.rows(s), e)
  +ch = HS.pchain(DR.NSeg{c}, DV.dropls(DV.rescb(res), DV.resbt(res), e, crosses(es, fs, u, ts.ds(s))), ts.ds(s))
  +p = {E.QMul{E.QCst{S.Q.inv(lnorm(u))}, SK.VE.dot(lform(u), SK.VE.sub(y, DR.Jd.x(DR.concl(es, fs, ch))))} : E.QExpr}
  DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{p, DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}}

# a derivation of par(c, y), y in c's set
def rep.der(r: Rep, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +c: Nat, +y: SK.VE) -> DR.Der:
  match r:
    case RFull{}:
      DR.DVoid{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, c))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, c))), DR.NSeg{c}, y}
    case RFree{h}:
      HS.hs.der(es, fs, t, DR.NSeg{c}, h, y)
    case RTied{u, du, s}:
      tied.der(es, fs, c, u, du, s, y)

# Merges
# ------

def reroot.one(b: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +old: DR.Node) -> Mem:
  match b:
    case True{}:
      Mem{a, new, LB.lmul(ww, w), DR.DThrough{dR, d, DR.Lab.conj(ww), old}}
    case False{}:
      Mem{a, r, w, d}

# move old's members under new: dR proves par(new, x), x the same as W z_old
def reroot(ms: List<&2, Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab) -> List<&2, Mem>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Mem{+a, +r, +w, +d}, t}:
      Con{reroot.one(node_eq(r, old), a, r, w, d, new, dR, ww, old), reroot(t, old, new, dR, ww)}

def merge.go(f: Bool, +ms: List<&2, Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der) -> List<&2, Mem>:
  match f:
    case True{}:
      reroot(ms, rr, DR.NFrame{}, DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}, LB.lmul(wb, DR.Lab.conj(w)))
    case False{}:
      reroot(ms, rb, rr, DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}, LB.lmul(w, DR.Lab.conj(wb)))

# d1 proves par(rr, x), x the same as w z_b, b outside rr's component:
# the two components become one, F staying a root
def merge(+ms: List<&2, Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, m: Mem) -> List<&2, Mem>:
  match m:
    case Mem{+b, +rb, +wb, +db}:
      merge.go(SV.band(node_eq(rb, DR.NFrame{}), SV.bnot(node_eq(rr, DR.NFrame{}))), ms, rr, d1, w, b, rb, wb, db)

# F's set holds w z_b for an open b outside F's component (Im(w z_b) in K)
def mgF.pick(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, Mem>, +mb: Mem, +b: DR.Node, rest: Maybe<&2, List<&2, Mem>>) -> Maybe<&2, List<&2, Mem>>:
  match m:
    case None{}:
      rest
    case Some{+w}:
      Some{merge(ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, mb)}

def mgF.if(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, Mem>, +mb: Mem, +b: DR.Node, rest: Maybe<&2, List<&2, Mem>>) -> Maybe<&2, List<&2, Mem>>:
  match f:
    case True{}:
      mgF.pick(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, mb, b, rest)
    case False{}:
      rest

def mgF(sc: List<&2, Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, Mem>) -> Maybe<&2, List<&2, Mem>>:
  match sc:
    case Nil{}:
      None{}
    case Con{Mem{+b, +rb, +wb, +db}, t}:
      mgF.if(SV.bnot(node_eq(rb, DR.NFrame{})), es, fs, k, ms, Mem{b, rb, wb, db}, b, mgF(t, es, fs, k, ms))

# a free root r's hull holds w z_b for an open b outside r's component
def mgR.pick(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, Mem>, +mb: Mem, +b: DR.Node, rest: Maybe<&2, List<&2, Mem>>) -> Maybe<&2, List<&2, Mem>>:
  match m:
    case None{}:
      rest
    case Some{+w}:
      Some{merge(ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, mb)}

def mgR.if(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, Mem>, +mb: Mem, +b: DR.Node, rest: Maybe<&2, List<&2, Mem>>) -> Maybe<&2, List<&2, Mem>>:
  match f:
    case True{}:
      mgR.pick(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, t, h, r, ms, mb, b, rest)
    case False{}:
      rest

def mgR(sc: List<&2, Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, Mem>) -> Maybe<&2, List<&2, Mem>>:
  match sc:
    case Nil{}:
      None{}
    case Con{Mem{+b, +rb, +wb, +db}, tl}:
      mgR.if(SV.bnot(node_eq(rb, r)), es, fs, t, h, r, ms, Mem{b, rb, wb, db}, b, mgR(tl, es, fs, t, h, r, ms))

def roots.pick(f: Bool, +a: DR.Node, rest: List<&2, DR.Node>) -> List<&2, DR.Node>:
  match f:
    case True{}:
      Con{a, rest}
    case False{}:
      rest
# the roots
def roots(ms: List<&2, Mem>) -> List<&2, DR.Node>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Mem{+a, r, w, d}, t}:
      roots.pick(node_eq(a, r), a, roots(t))


# The checks
# ----------

def mpick2(b: Bool, +x: DR.Der, rest: Maybe<&2, DR.Der>) -> Maybe<&2, DR.Der>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

# frame-back: a generator of F whose imaginary part is not in K
def fback(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> Maybe<&2, DR.Der>:
  match gs:
    case Nil{}:
      None{}
    case Con{+g, t}:
      mpick2(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), DR.DBack{g}, fback(t, es, fs, k))

def cl.k(b: Bool, +px: DR.Der, +d2: DR.Der) -> DR.Der:
  match b:
    case True{}:
      DR.DLine{px, d2, False{}}
    case False{}:
      DR.DLine{px, d2, True{}}

# x = x_j - (the inserted ones' combination) has x and i x in the hull h:
# a complex line, giving K the part of x not yet in it
def cl.found(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +d: DR.Der, +res: EL.Res, +e: E.QExpr, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>) -> DR.Der:
  +px = {DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)), DV.dropls(DV.rescb(res), DV.resbt(res), e, bb)), prev)} : DR.Der}
  cl.k(KS.ks.inb(k, SK.VE.x(DR.Jd.x(DR.concl(es, fs, px)))), px, HS.hs.der(es, fs, t, r, h, DR.imul(DR.Jd.x(DR.concl(es, fs, px)))))

def cl.pick(b: Bool, +found: DR.Der, rest: Maybe<&2, DR.Der>) -> Maybe<&2, DR.Der>:
  match b:
    case True{}:
      Some{found}
    case False{}:
      rest

# the kept non-K generators ds, i times each inserted in turn after the
# hull's rows (rows2 over bb, prev the ones inserted so far)
def cl.go(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>) -> Maybe<&2, DR.Der>:
  match ds:
    case Nil{}:
      None{}
    case Con{+d, tl}:
      +e = HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)
      +res = EL.resid(rows2, e)
      cl.pick(EP.isnil(EP.resp(res)), cl.found(es, fs, t, r, h, k, d, res, e, bb, prev),
        cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d)))

# a complex line at the free root r outside K squared, as a new K fact
def clx(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node) -> Maybe<&2, DR.Der>:
  +hk = khull(es, fs, t, Sk.k(s), r)
  +h = hfold(rgens(fs, r, Sk.ms(s), Sk.ls(s)), es, fs, t, hk)
  cl.go(ddrop(dlen(HS.hs.ds(hk)), HS.hs.ds(h)), es, fs, t, r, h, Sk.k(s), HS.hs.rows(h), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{})

def clxs.pick(m: Maybe<&2, DR.Der>, rest: Maybe<&2, DR.Der>) -> Maybe<&2, DR.Der>:
  match m:
    case None{}:
      rest
    case Some{+d}:
      Some{d}

def clxs.if(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node, rest: Maybe<&2, DR.Der>) -> Maybe<&2, DR.Der>:
  match f:
    case True{}:
      clxs.pick(clx(es, fs, t, s, r), rest)
    case False{}:
      rest

def clxs(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk) -> Maybe<&2, DR.Der>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, tl}:
      clxs.if(SV.bnot(node_eq(r, DR.NFrame{})), es, fs, t, s, r, clxs(tl, es, fs, t, s))

def mgs.pick(m: Maybe<&2, List<&2, Mem>>, rest: Maybe<&2, List<&2, Mem>>) -> Maybe<&2, List<&2, Mem>>:
  match m:
    case None{}:
      rest
    case Some{+x}:
      Some{x}

def mgs.root(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node) -> Maybe<&2, List<&2, Mem>>:
  match f:
    case True{}:
      mgF(Sk.ms(s), es, fs, Sk.k(s), Sk.ms(s))
    case False{}:
      mgR(Sk.ms(s), es, fs, t, rhull(es, fs, t, s, r), r, Sk.ms(s))

# the first merge
def mgs(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk) -> Maybe<&2, List<&2, Mem>>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, tl}:
      mgs.pick(mgs.root(node_eq(r, DR.NFrame{}), es, fs, t, s, r), mgs(tl, es, fs, t, s))

def lk.pick(f: Bool, +w: DR.Lab, rest: Maybe<&2, DR.Lab>) -> Maybe<&2, DR.Lab>:
  match f:
    case True{}:
      rest
    case False{}:
      Some{w}

# links from collapsed c: the first basis label not yet in the stored span
def lk.first(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>) -> Maybe<&2, DR.Lab>:
  match ws:
    case Nil{}:
      None{}
    case Con{+w, t}:
      lk.pick(qspan(stored, w), w, lk.first(t, stored))

def lfirst(m: Maybe<&2, Link>, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match m:
    case None{}:
      rest
    case Some{+x}:
      Some{x}

def lk.mk(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +c: Nat, +rep: Rep, +b: DR.Node, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match m:
    case None{}:
      rest
    case Some{+w}:
      Some{Link{c, b, w, rep.der(rep, es, fs, t, k, c, DR.gmul(w, DR.zdir(es, b)))}}

def lk.c.if(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat, +rep: Rep, +b: DR.Node, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match f:
    case True{}:
      rest
    case False{}:
      lk.mk(lk.first(rep.basis(rep, es, fs, t, DR.zdir(es, b)), lstored(Sk.ls(s), c, b)), es, fs, t, Sk.k(s), c, rep, b, rest)

# collapsed c and the nodes bs: G_cb in the stored links' span
def lk.c(bs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat, +rep: Rep) -> Maybe<&2, Link>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, tl}:
      lk.c.if(node_eq(b, DR.NSeg{c}), es, fs, t, s, c, rep, b, lk.c(tl, es, fs, t, s, c, rep))

def lk.r.basis(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node, +z: SK.VE) -> List<&2, DR.Lab>:
  match f:
    case True{}:
      basis.k(LB.ks.lab(es, fs, Sk.k(s), z), Sk.k(s), z)
    case False{}:
      basis.free(LB.hs.lab(es, fs, t, rhull(es, fs, t, s, r), z), t, rhull(es, fs, t, s, r), z)

def lk.r.der(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node, +y: SK.VE) -> DR.Der:
  match f:
    case True{}:
      DR.DFrame{KS.ks.der(es, fs, Sk.k(s), SK.VE.y(y)), y}
    case False{}:
      HS.hs.der(es, fs, t, r, rhull(es, fs, t, s, r), y)

def lk.r.first(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>) -> Maybe<&2, DR.Lab>:
  match ws:
    case Nil{}:
      None{}
    case Con{+w, t}:
      lk.pick(qspan(stored, DR.Lab.conj(w)), w, lk.r.first(t, stored))

def lk.r.mk(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat, +r: DR.Node, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match m:
    case None{}:
      rest
    case Some{+w}:
      Some{Link{c, r, DR.Lab.conj(w), DR.DTurn{lk.r.der(node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}}

# the open roots rs and collapsed c: conj(G_rc) in the stored links' span
def lk.r(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat) -> Maybe<&2, Link>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, tl}:
      lk.r.mk(lk.r.first(lk.r.basis(node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), lstored(Sk.ls(s), c, r)), es, fs, t, s, c, r, lk.r(tl, es, fs, t, s, c))

def lks.go(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +c: Nat, +rep: Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>, rest: Maybe<&2, Link>) -> Maybe<&2, Link>:
  match f:
    case True{}:
      rest
    case False{}:
      lfirst(lk.c(bs, es, fs, t, s, c, rep), lfirst(lk.r(rs, es, fs, t, s, c), rest))

# the first new link, over the collapsed segments cids
def lks(cids: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>) -> Maybe<&2, Link>:
  match cids:
    case Nil{}:
      None{}
    case Con{+c, tl}:
      lks.go(fullc(es, Sk.k(s), c), es, fs, t, s, c, crep(es, fs, t, s, c), bs, rs, lks(tl, es, fs, t, s, bs, rs))

# The rounds
# ----------

type Out is Data:
  # one more skeleton item
  OStep{s: Sk}
  # closed
  OFix{s: Sk}
  # 1 in K
  OOne{d: DR.Der}
  # an open segment's direction in K squared
  OVoid{sg: Nat, dr: DR.Der, di: DR.Der}

def lsnoc(ls: List<&2, Link>, +x: Link) -> List<&2, Link>:
  match ls:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, lsnoc(t, x)}

def ids.pick(f: Bool, +i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match f:
    case True{}:
      Con{i, rest}
    case False{}:
      rest

# the collapsed segments
def cids(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: SP) -> List<&2, Nat>:
  match ids:
    case Nil{}:
      Nil{}
    case Con{+i, t}:
      ids.pick(coll(es, cs, i), i, cids(t, es, cs))

def vpick(f: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match f:
    case True{}:
      Some{i}
    case False{}:
      rest

# an open segment whose direction is in K squared
def voidseg(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: SP, +k: KS.KS) -> Maybe<&2, Nat>:
  match ids:
    case Nil{}:
      None{}
    case Con{+i, t}:
      vpick(SV.band(SV.bnot(coll(es, cs, i)), fullc(es, k, i)), i, voidseg(t, es, cs, k))

def r.c4(m: Maybe<&2, Link>, +s: Sk) -> Out:
  match m:
    case None{}:
      OFix{s}
    case Some{+l}:
      OStep{Sk{Sk.k(s), Sk.ms(s), lsnoc(Sk.ls(s), l)}}

def r.c3(m: Maybe<&2, List<&2, Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  match m:
    case None{}:
      r.c4(lks(cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, snodes(ids)}, roots(Sk.ms(s))), s)
    case Some{+ms}:
      OStep{Sk{Sk.k(s), ms, Sk.ls(s)}}

def r.c2(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  match m:
    case None{}:
      r.c3(mgs(roots(Sk.ms(s)), es, fs, t, s), es, fs, t, cs, ids, s)
    case Some{+d}:
      OStep{Sk{KS.ks.add(es, fs, Sk.k(s), d), Sk.ms(s), Sk.ls(s)}}

def r.c1(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  match m:
    case None{}:
      r.c2(clxs(roots(Sk.ms(s)), es, fs, t, s), es, fs, t, cs, ids, s)
    case Some{+d}:
      OStep{Sk{KS.ks.add(es, fs, Sk.k(s), d), Sk.ms(s), Sk.ls(s)}}

def r.e2(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  match m:
    case None{}:
      r.c1(fback(rgens(fs, DR.NFrame{}, Sk.ms(s), Sk.ls(s)), es, fs, Sk.k(s)), es, fs, t, cs, ids, s)
    case Some{+g}:
      OVoid{g, KS.ks.der(es, fs, Sk.k(s), SK.VE.x(DR.zseg(es, g))), KS.ks.der(es, fs, Sk.k(s), SK.VE.y(DR.zseg(es, g)))}

def r.e1(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  match f:
    case True{}:
      OOne{KS.ks.der(es, fs, Sk.k(s), DR.cst(DR.qo()))}
    case False{}:
      r.e2(voidseg(ids, es, cs, Sk.k(s)), es, fs, t, cs, ids, s)

# one round: explosion, else the first failing check's item, else closed
def round(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>, +s: Sk) -> Out:
  r.e1(KS.ks.inb(Sk.k(s), DR.cst(DR.qo())), es, fs, t, cs, ids, s)

def run(fuel: Nat, o: Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: SP, +ids: List<&2, Nat>) -> Out:
  match fuel o:
    case 0n o:
      o
    case 1n+f OStep{s}:
      run(f, round(es, fs, t, cs, ids, s), es, fs, t, cs, ids)
    case 1n+f OFix{s}:
      OFix{s}
    case 1n+f OOne{d}:
      OOne{d}
    case 1n+f OVoid{sg, dr, di}:
      OVoid{sg, dr, di}

# the closure of the facts fs in the context ctx, t past every variable
def dclose(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat) -> Out:
  +cs = sp.of(ctx, SP{Nil{}, Nil{}})
  run(fuel, OStep{sk0(es, fs, cs)}, es, fs, t, cs, segids(es))

# The closure's hypotheses
# ------------------------

def ptsb.g(g: SK.Geo, +t: Nat) -> Bool:
  match g:
    case SK.GPoint{x, y}:
      SV.band(SV.lt(x, t), SV.lt(y, t))
    case SK.GSeg{p, q}:
      True{}
    case SK.GCirc{c, r}:
      True{}
    case SK.GArc{s, e, b}:
      True{}

# every point's coordinates are below t
def ptsb(es: List<&2, SK.Ent>, +t: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{SK.Ent{id, cons, g}, tl}:
      SV.band(ptsb.g(g, t), ptsb(tl, t))

# t is past every point's coordinates (and so every direction's variables)
def zb(+es: List<&2, SK.Ent>, +t: Nat) -> Bool:
  SV.band(SV.lt(0n, t), ptsb(es, t))

def fb.ds(ds: Maybe<&2, DR.DStat>, +t: Nat) -> Bool:
  match ds:
    case Some{DR.DStat{a, +x, l}}:
      SV.band(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t))
    case None{}:
      True{}

# every fact's equation and statement are below t
def fb(fs: List<&2, DR.Fact>, +t: Nat) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{DR.Fact{e, nd, ds}, tl}:
      SV.band(SP.vbelow(e, t), SV.band(fb.ds(ds, t), fb(tl, t)))

# Queries
# -------
# What a fixpoint holds, read off its sets: a K equation, or a direction
# statement par(b, y) by b's set (its root's when it has a record, its
# collapsed set when not).

def rset.inb(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node, +y: SK.VE) -> Bool:
  match f:
    case True{}:
      KS.ks.inb(Sk.k(s), SK.VE.y(y))
    case False{}:
      HS.hs.inb(rhull(es, fs, t, s, r), y, t)

def par.n(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +y: SK.VE) -> Bool:
  match a:
    case DR.NFrame{}:
      KS.ks.inb(Sk.k(s), SK.VE.y(y))
    case DR.NSeg{c}:
      rep.inb(crep(es, fs, t, s, c), t, y)

def par.m(m: Maybe<&2, Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +a: DR.Node, +y: SK.VE) -> Bool:
  match m:
    case Some{Mem{a2, +r, +w, d}}:
      rset.inb(node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, y))
    case None{}:
      par.n(a, es, fs, t, s, y)

# the state holds par(a, y)
def par.inb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +a: DR.Node, +y: SK.VE) -> Bool:
  par.m(mem_of(Sk.ms(s), a), es, fs, t, s, a, y)

def stat.inb(m: Maybe<&2, DR.DStat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk) -> Bool:
  match m:
    case Some{DR.DStat{+b, +y, l}}:
      par.inb(es, fs, t, s, DR.NSeg{b}, y)
    case None{}:
      False{}

# the state holds the equation e, or the direction statement m
def holds(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> Bool:
  SV.bor(KS.ks.inb(Sk.k(s), e), stat.inb(m, es, fs, t, s))

# Derivations of what a fixpoint holds
# ------------------------------------

def rset.der(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +r: DR.Node, +y: SK.VE) -> DR.Der:
  match f:
    case True{}:
      DR.DFrame{KS.ks.der(es, fs, Sk.k(s), SK.VE.y(y)), y}
    case False{}:
      HS.hs.der(es, fs, t, r, rhull(es, fs, t, s, r), y)

# b's record (r, w, d) and dx proving par(r, w y) give par(b, y): d turned
# to b, passed through r with dx, scaled by 1/|w|²
def mem.back(+d: DR.Der, +w: DR.Lab, +b: DR.Node, +r: DR.Node, +dx: DR.Der) -> DR.Der:
  DR.DPLin{S.Q.inv(lnorm(w)), DR.DThrough{DR.DTurn{d, DR.Lab.conj(w), b}, dx, w, r}, DR.qz(), DR.DThrough{DR.DTurn{d, DR.Lab.conj(w), b}, dx, w, r}}

def par.dn(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +y: SK.VE) -> DR.Der:
  match a:
    case DR.NFrame{}:
      DR.DFrame{KS.ks.der(es, fs, Sk.k(s), SK.VE.y(y)), y}
    case DR.NSeg{+c}:
      rep.der(crep(es, fs, t, s, c), es, fs, t, Sk.k(s), c, y)

def par.dm(m: Maybe<&2, Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +a: DR.Node, +y: SK.VE) -> DR.Der:
  match m:
    case Some{Mem{a2, +r, +w, +d}}:
      mem.back(d, w, a, r, rset.der(node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, y)))
    case None{}:
      par.dn(a, es, fs, t, s, y)

# a derivation of par(a, y) when the state holds it
def par.der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +a: DR.Node, +y: SK.VE) -> DR.Der:
  par.dm(mem_of(Sk.ms(s), a), es, fs, t, s, a, y)

def stat.der(m: Maybe<&2, DR.DStat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk) -> DR.Der:
  match m:
    case Some{DR.DStat{+b, +y, l}}:
      par.der(es, fs, t, s, DR.NSeg{b}, y)
    case None{}:
      DR.DZero{}

def hold.pick(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> DR.Der:
  match f:
    case True{}:
      KS.ks.der(es, fs, Sk.k(s), e)
    case False{}:
      stat.der(m, es, fs, t, s)

# a derivation of what the state holds: e by K, or else its statement
def hold.der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: Sk, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> DR.Der:
  hold.pick(KS.ks.inb(Sk.k(s), e), es, fs, t, s, e, m)
