# bend-cad: the structure of a system (DESIGN §10.1, stage 2). Part of the
# verified proposer: nothing here is believed without proof. What a
# structure claims is checked (lib/solve.bend: the plan by lib/plan.bend's
# checker, each red equation's witness by spec/solve.bend), and that the
# checks always pass is the totality law (ROADMAP: solve_total).
#
# A system is a list of equations over variables 0 .. nv - 1. Equation j
# uses variable v when v occurs in it. The matching pairs equations with
# distinct variables they use; it grows by augmenting paths (Kuhn),
# searched depth first with the fuel bounding only the depth. A failed
# search from an equation j visits variables W, all matched, and the
# equations S = j and their mates; every variable of S lies in W and |W| =
# |S| - 1, so S has more equations than unknowns whatever the matching
# becomes later.
#
# Blocks are the strongly connected components (Tarjan, explicit stack)
# of the graph in which an equation needs the equation matched to each
# variable it uses; a component is emitted after every component it needs.
# Each is checked as it is emitted, and what is left after a failed check
# becomes one block, which is always valid.
#
# Bend allows no mutual recursion, so each loop is one recursive def over
# a state, and every step that inspects a computed value is a
# non-recursive helper that returns the next state.

import Base
import ../spec/ring.bend as E
import ./karith.bend as KA

# Lists of numbers
# ----------------

def bor(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

def bnot(a: Bool) -> Bool:
  match a:
    case True{}:
      False{}
    case False{}:
      True{}

def mem(+v: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      bor(KA.nateq(v, h), mem(v, t))

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len(t)

def app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, app(t, ys)}

def rev.go(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev.go(t, Con{h, acc})

def rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  rev.go(xs, Nil{})

def iota(n: Nat, +k: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{k, iota(m, 1n+k)}

# every entry of xs is in ys
def all_in(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      KA.band(mem(h, ys), all_in(t, ys))

# the position of v in xs (its length when absent)
def pos.go(b: Bool, rest: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+rest

def pos(+v: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      pos.go(KA.nateq(v, h), pos(v, t))

# Lists of lists, of options and of flags
# ---------------------------------------

def nthl(xs: List<&2, List<&2, Nat>>, k: Nat) -> List<&2, Nat>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      nthl(t, j)

def cats(xs: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      app(h, cats(t))

def revl.go(xs: List<&2, List<&2, Nat>>, acc: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      revl.go(t, Con{h, acc})

def nones(n: Nat) -> List<&2, Maybe<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{None{}, nones(m)}

def getm(xs: List<&2, Maybe<&2, Nat>>, k: Nat) -> Maybe<&2, Nat>:
  match xs k:
    case Nil{} k:
      None{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      getm(t, j)

def setm(xs: List<&2, Maybe<&2, Nat>>, k: Nat, +x: Maybe<&2, Nat>) -> List<&2, Maybe<&2, Nat>>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      Con{x, t}
    case Con{h, t} 1n+j:
      Con{h, setm(t, j, x)}

# the entries some (in order)
def somes(xs: List<&2, Maybe<&2, Nat>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{None{}, t}:
      somes(t)
    case Con{Some{x}, t}:
      Con{x, somes(t)}

# the indices whose entry is None, from k
def holes(xs: List<&2, Maybe<&2, Nat>>, +k: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{None{}, t}:
      Con{k, holes(t, 1n+k)}
    case Con{Some{x}, t}:
      holes(t, 1n+k)

def look.of(x: Maybe<&2, Nat>) -> Nat:
  match x:
    case None{}:
      0n
    case Some{y}:
      y

# m(x) for each x (0 for None)
def look(+m: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{look.of(getm(m, x)), look(m, t)}


# Incidence
# ---------

def addv.go(b: Bool, v: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      acc
    case False{}:
      Con{v, acc}

def addv(+v: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  addv.go(mem(v, acc), v, acc)

# the variables of e not yet in acc, prepended to acc (each once)
def evars(e: E.QExpr, acc: List<&2, Nat>) -> List<&2, Nat>:
  match e:
    case E.QVar{v}:
      addv(v, acc)
    case E.QCst{q}:
      acc
    case E.QAdd{a, b}:
      evars(b, evars(a, acc))
    case E.QSub{a, b}:
      evars(b, evars(a, acc))
    case E.QMul{a, b}:
      evars(b, evars(a, acc))
    case E.QNeg{a}:
      evars(a, acc)

# each equation's variables, in order of first occurrence
def adj(es: List<&2, E.QExpr>) -> List<&2, List<&2, Nat>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{rev(evars(e, Nil{})), adj(t)}

def total(xs: List<&2, List<&2, Nat>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(len(h), total(t))

def hd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

# n - 1, n - 2, ..., 0
def down(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n++m:
      Con{m, down(m)}

# Augmenting paths (Kuhn)
# -----------------------
# vm maps each variable to its equation. A search from an unmatched
# equation e tries the variables e uses, in order, depth first: a visited
# one is skipped; a free one goes to e, which ends the search (found); one
# matched to e2 is visited and goes to e for the time being, and the search
# goes on from e2, now unmatched; if that fails, v stays e2's (the search
# goes on with the matching it had) and e tries its next variable.
#
# A failed search from e visits variables W, every one of them matched,
# and every variable that e or a mate of W uses lies in W: so e and the
# mates of W are |W| + 1 equations over the |W| variables of W. Each level
# visits a new variable, which is matched, so a fuel of one more than the
# number of variables bounds the depth.

# how the variable being tried stands: visited, free, matched to e, or
# there is none (no variables left, or the search has already succeeded)
type Cls is Data:
  Seen{}
  Free{}
  Mate{e: Nat}
  Done{}

# a search's state: whether it found a path (and then the new matching), and
# the variables visited so far
type DS is Data:
  DS{ok: Bool, vm: List<&2, Maybe<&2, Nat>>, vis: List<&2, Nat>}

def ds.vis(s: DS) -> List<&2, Nat>:
  match s:
    case DS{ok, vm, vis}:
      vis

def cls.m(m: Maybe<&2, Nat>) -> Cls:
  match m:
    case None{}:
      Free{}
    case Some{e}:
      Mate{e}

def cls.of(seen: Bool, m: Maybe<&2, Nat>) -> Cls:
  match seen:
    case True{}:
      Seen{}
    case False{}:
      cls.m(m)

# how the first of vs stands
def cls(+vm: List<&2, Maybe<&2, Nat>>, +vis: List<&2, Nat>, vs: List<&2, Nat>) -> Cls:
  match vs:
    case Nil{}:
      Done{}
    case Con{+v, t}:
      cls.of(mem(v, vis), getm(vm, v))

# how the first of vs stands after the search r
def cnext(r: DS, +vm: List<&2, Maybe<&2, Nat>>, +vs: List<&2, Nat>) -> Cls:
  match r:
    case DS{True{}, m, vis}:
      Done{}
    case DS{False{}, m, +vis}:
      cls(vm, vis, vs)

# try the variables vs for e (c: how the first stands), e being unmatched
# in vm, from the state st
def dfs(f: Nat, vs: List<&2, Nat>, c: Cls, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +st: DS) -> DS:
  match f vs c:
    case 0n Nil{} Seen{}:
      st
    case 0n Nil{} Free{}:
      st
    case 0n Nil{} Mate{e2}:
      st
    case 0n Nil{} Done{}:
      st
    case 1n++g Nil{} Seen{}:
      st
    case 1n++g Nil{} Free{}:
      st
    case 1n++g Nil{} Mate{e2}:
      st
    case 1n++g Nil{} Done{}:
      st
    case 0n Con{v, +rest} Seen{}:
      dfs(0n, rest, cls(vm, ds.vis(st), rest), e, adj, vm, st)
    case 0n Con{+v, rest} Free{}:
      DS{True{}, setm(vm, v, Some{e}), ds.vis(st)}
    case 0n Con{v, rest} Mate{e2}:
      st
    case 0n Con{v, rest} Done{}:
      st
    case 1n++g Con{v, +rest} Seen{}:
      dfs(1n+g, rest, cls(vm, ds.vis(st), rest), e, adj, vm, st)
    case 1n++g Con{+v, rest} Free{}:
      DS{True{}, setm(vm, v, Some{e}), ds.vis(st)}
    case 1n++g Con{+v, +rest} Mate{+e2}:
      +r = dfs(g, nthl(adj, e2), cls(setm(vm, v, Some{e}), Con{v, ds.vis(st)}, nthl(adj, e2)), e2, adj, setm(vm, v, Some{e}), DS{False{}, vm, Con{v, ds.vis(st)}})
      dfs(1n+g, rest, cnext(r, vm, rest), e, adj, vm, r)
    case 1n++g Con{v, rest} Done{}:
      st

# a search from the unmatched equation e
def search(+f: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +e: Nat) -> DS:
  dfs(f, nthl(adj, e), cls(vm, Nil{}, nthl(adj, e)), e, adj, vm, DS{False{}, vm, Nil{}})

# a red equation: the search from eq failed; S is eq and the mates of the
# visited variables W (at that moment)
type Red is Data:
  Red{eq: Nat, s: List<&2, Nat>, w: List<&2, Nat>}

type KS is Data:
  KS{vm: List<&2, Maybe<&2, Nat>>, red: List<&2, Red>}

def KS.vm(st: KS) -> List<&2, Maybe<&2, Nat>>:
  match st:
    case KS{vm, red}:
      vm

def kstep(+j: Nat, a: DS, st: KS) -> KS:
  match a st:
    case DS{True{}, vm2, vis} KS{vm, red}:
      KS{vm2, red}
    case DS{False{}, vm2, +vis} KS{+vm, red}:
      KS{vm, Con{Red{j, Con{j, look(vm, vis)}, vis}, red}}

# search from each equation in turn
def kuhn(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: KS) -> KS:
  match js:
    case Nil{}:
      st
    case Con{+j, t}:
      kuhn(t, adj, f, kstep(j, search(f, adj, KS.vm(st), j), st))

# Dead variables
# --------------
# The variables W a failed search visited are dead: all matched, and what
# the searched equation and the mates of W use is in W. No later search
# finds a path through W (one that enters W stays among the mates of W,
# which use only W, all matched), so a search may begin with W visited: it
# finds what it would have found, sooner, and a path it finds leaves the
# mates of W as they were. The variable side (below) searches so, with the
# roles swapped: from variables, through equations.

# a search from the unmatched equation e, the variables vis visited already
def search.from(+f: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vis: List<&2, Nat>) -> DS:
  dfs(f, nthl(adj, e), cls(vm, vis, nthl(adj, e)), e, adj, vm, DS{False{}, vm, vis})

# the matching, the failed searches (newest first) and the dead variables
type KD is Data:
  KD{vm: List<&2, Maybe<&2, Nat>>, red: List<&2, Nat>, dead: List<&2, Nat>}

def KD.vm(st: KD) -> List<&2, Maybe<&2, Nat>>:
  match st:
    case KD{vm, red, dead}:
      vm

def KD.red(st: KD) -> List<&2, Nat>:
  match st:
    case KD{vm, red, dead}:
      red

def KD.dead(st: KD) -> List<&2, Nat>:
  match st:
    case KD{vm, red, dead}:
      dead

def kdstep(+j: Nat, a: DS, st: KD) -> KD:
  match a st:
    case DS{True{}, vm2, vis} KD{vm, red, dead}:
      KD{vm2, red, dead}
    case DS{False{}, vm2, vis} KD{vm, red, dead}:
      KD{vm, Con{j, red}, vis}

# search from each equation in turn, past the dead variables
def kuhnd(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: KD) -> KD:
  match js:
    case Nil{}:
      st
    case Con{+j, t}:
      kuhnd(t, adj, f, kdstep(j, search.from(f, adj, KD.vm(st), j, KD.dead(st)), st))

# Constraints as units
# --------------------
# A constraint's equations are matched together: if one of them fails,
# the matching goes back to what it was before the constraint, and the
# constraint is red with that equation's witness. A witness then uses only
# equations of constraints accepted earlier and of the red one itself, so
# restoring any one red constraint over-determines the accepted ones.
# (lib/solve.bend walks the sketch's constraints.)

type GS is Data:
  GOk{vm: List<&2, Maybe<&2, Nat>>}
  GFail{r: Red}

def gstep(+j: Nat, a: DS, +vm: List<&2, Maybe<&2, Nat>>) -> GS:
  match a:
    case DS{True{}, vm2, vis}:
      GOk{vm2}
    case DS{False{}, vm2, +vis}:
      GFail{Red{j, Con{j, look(vm, vis)}, vis}}

# the n equations k, k + 1, ... of one constraint, in turn
def grp(n: Nat, +k: Nat, +adj: List<&2, List<&2, Nat>>, +f: Nat, st: GS) -> GS:
  match n st:
    case 0n GOk{vm}:
      GOk{vm}
    case 0n GFail{r}:
      GFail{r}
    case 1n+m GOk{+vm}:
      grp(m, 1n+k, adj, f, gstep(k, search(f, adj, vm, k), vm))
    case 1n+m GFail{r}:
      GFail{r}

# Components (Tarjan)
# -------------------
# idx and low per equation (None: not reached), the component stack st,
# the call stack cs (an equation and the equations it still has to visit),
# and the components found, newest first.

type TF is Data:
  TF{v: Nat, rest: List<&2, Nat>}

type TS is Data:
  TS{c: Nat, idx: List<&2, Maybe<&2, Nat>>, low: List<&2, Maybe<&2, Nat>>, st: List<&2, Nat>, cs: List<&2, TF>, out: List<&2, List<&2, Nat>>}

def nmin.go(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

def nmin(+a: Nat, +b: Nat) -> Nat:
  nmin.go(KA.natle(a, b), a, b)

def needs.ne(b: Bool, j: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{j, rest}

# the equations matched to e's variables, other than e itself
def needs.of(+e: Nat, m: Maybe<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      rest
    case Some{+j}:
      needs.ne(KA.nateq(j, e), j, rest)


def needs.go(+e: Nat, +vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      needs.of(e, getm(vm, x), needs.go(e, vm, t))

def needs(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +e: Nat) -> List<&2, Nat>:
  needs.go(e, vm, nthl(adj, e))

# reach equation w: number it and put it on both stacks
def tpush(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +w: Nat, s: TS) -> TS:
  match s:
    case TS{+c, idx, low, st, cs, out}:
      TS{1n+c, setm(idx, w, Some{c}), setm(low, w, Some{c}), Con{w, st}, Con{TF{w, needs(adj, vm, w)}, cs}, out}

# lower v's low to x
def tlow(+v: Nat, +x: Nat, s: TS) -> TS:
  match s:
    case TS{c, idx, +low, st, cs, out}:
      TS{c, idx, setm(low, v, Some{nmin(look.of(getm(low, v)), x)}), st, cs, out}

# from v, equation w: new (reach it), on the stack (lower v), or done
def tedge.on(on: Bool, +v: Nat, iw: Nat, s: TS) -> TS:
  match on:
    case True{}:
      tlow(v, iw, s)
    case False{}:
      s

def tedge(m: Maybe<&2, Nat>, on: Bool, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +w: Nat, s: TS) -> TS:
  match m:
    case None{}:
      tpush(adj, vm, w, s)
    case Some{iw}:
      tedge.on(on, v, iw, s)

# pop the component stack down to v (b: its top is v)
def tpop(st: List<&2, Nat>, b: Bool, +v: Nat, acc: List<&2, Nat>, c: Nat, idx: List<&2, Maybe<&2, Nat>>, low: List<&2, Maybe<&2, Nat>>, cs: List<&2, TF>, out: List<&2, List<&2, Nat>>) -> TS:
  match st b:
    case Nil{} b:
      TS{c, idx, low, Nil{}, cs, Con{acc, out}}
    case Con{h, t} True{}:
      TS{c, idx, low, t, cs, Con{Con{h, acc}, out}}
    case Con{h, +t} False{}:
      tpop(t, KA.nateq(hd(t), v), v, Con{h, acc}, c, idx, low, cs, out)

# v is finished (its frame popped): a component if low = idx; then the
# caller's low drops to v's
def tfin.root(b: Bool, +v: Nat, s: TS) -> TS:
  match b s:
    case True{} TS{c, idx, low, +st, cs, out}:
      tpop(st, KA.nateq(hd(st), v), v, Nil{}, c, idx, low, cs, out)
    case False{} s:
      s

def tfin.up(cs: List<&2, TF>, +x: Nat, s: TS) -> TS:
  match cs:
    case Nil{}:
      s
    case Con{TF{u, r}, t}:
      tlow(u, x, s)

def ts.low(+v: Nat, s: TS) -> Nat:
  match s:
    case TS{c, idx, low, st, cs, out}:
      look.of(getm(low, v))

def ts.idx(+v: Nat, s: TS) -> Nat:
  match s:
    case TS{c, idx, low, st, cs, out}:
      look.of(getm(idx, v))

def ts.cs(s: TS) -> List<&2, TF>:
  match s:
    case TS{c, idx, low, st, cs, out}:
      cs

def tfin(+v: Nat, +s: TS) -> TS:
  tfin.up(ts.cs(s), ts.low(v, s), tfin.root(KA.nateq(ts.low(v, s), ts.idx(v, s)), v, s))

def troot(m: Maybe<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +r: Nat, s: TS) -> TS:
  match m:
    case None{}:
      tpush(adj, vm, r, s)
    case Some{i}:
      s

def tarjan(f: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, roots: List<&2, Nat>, s: TS) -> TS:
  match f roots s:
    case 0n roots s:
      s
    case 1n+g Nil{} TS{c, idx, low, st, Nil{}, out}:
      TS{c, idx, low, st, Nil{}, out}
    case 1n+g Con{+r, rt} TS{c, +idx, low, st, Nil{}, out}:
      tarjan(g, adj, vm, rt, troot(getm(idx, r), adj, vm, r, TS{c, idx, low, st, Nil{}, out}))
    case 1n+g roots TS{c, +idx, low, +st, Con{TF{+v, Con{+w, rest}}, ct}, out}:
      tarjan(g, adj, vm, roots, tedge(getm(idx, w), mem(w, st), adj, vm, v, w, TS{c, idx, low, st, Con{TF{v, rest}, ct}, out}))
    case 1n+g roots TS{c, idx, low, st, Con{TF{+v, Nil{}}, ct}, out}:
      tarjan(g, adj, vm, roots, tfin(v, TS{c, idx, low, st, ct, out}))

def ts.out(s: TS) -> List<&2, List<&2, Nat>>:
  match s:
    case TS{c, idx, low, st, cs, out}:
      out

# the components of the matched equations es, each after those it needs
def comps(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +es: List<&2, Nat>, +ne: Nat) -> List<&2, List<&2, Nat>>:
  revl.go(ts.out(tarjan(Nat.add(Nat.add(total(adj), ne), Nat.add(ne, Nat.add(ne, 2n))), adj, vm, es, TS{0n, nones(ne), nones(ne), Nil{}, Nil{}, Nil{}})), Nil{})

# Blocks
# ------

# each equation's matched variable (from the variables' map vm)
def invert(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, em: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match vm:
    case Nil{}:
      em
    case Con{None{}, t}:
      invert(t, 1n+k, em)
    case Con{Some{j}, t}:
      invert(t, 1n+k, setm(em, j, Some{k}))

def uses.add(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      uses.add(t, addv(x, acc))

# the variables the equations js use (each once)
def uses.go(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match js:
    case Nil{}:
      acc
    case Con{j, t}:
      uses.go(t, adj, uses.add(nthl(adj, j), acc))


def uses(+js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  rev(uses.go(js, adj, Nil{}))

# a block: its equations and its unknowns (system numbering)
type SB is Data:
  SB{eqs: List<&2, Nat>, vars: List<&2, Nat>}

def revb.go(xs: List<&2, SB>, acc: List<&2, SB>) -> List<&2, SB>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      revb.go(t, Con{h, acc})

# the component is a valid next block: its equations use only known
# variables and its own unknowns
def valid(+comp: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +known: List<&2, Nat>) -> Bool:
  all_in(uses(comp, adj), app(look(em, comp), known))

def hdl(xs: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h

# emit the components in order (ok: the first is valid); after a failed
# check everything left is one block
def blocks(cs: List<&2, List<&2, Nat>>, ok: Bool, +adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +known: List<&2, Nat>, acc: List<&2, SB>) -> List<&2, SB>:
  match cs ok:
    case Nil{} ok:
      revb.go(acc, Nil{})
    case Con{+comp, +rest} True{}:
      blocks(rest, valid(hdl(rest), adj, em, app(known, look(em, comp))), adj, em, app(known, look(em, comp)), Con{SB{comp, look(em, comp)}, acc})
    case Con{+comp, +rest} False{}:
      revb.go(Con{SB{cats(Con{comp, rest}), look(em, cats(Con{comp, rest}))}, acc}, Nil{})

def minus.go(b: Bool, h: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{h, rest}

# the entries of xs that are not in ys
def minus(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      minus.go(mem(h, ys), h, minus(t, ys))

# the entries of xs that are in ys
def inter(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      minus.go(bnot(mem(h, ys)), h, inter(t, ys))

# The skeleton of a plan
# ----------------------
# vp: the variables in block order (pins first), ep: the equations in
# block order, np: the number of pins; per block, its size and its
# parameters as positions in vp (what lib/plan.bend's Plan holds, less the
# certificates).

type SkB is Data:
  SkB{eqs: List<&2, Nat>, vars: List<&2, Nat>, pars: List<&2, Nat>}

type Skel is Data:
  Skel{vp: List<&2, Nat>, ep: List<&2, Nat>, np: Nat, bs: List<&2, SkB>, red: List<&2, Red>}

def sb.vars(b: SB) -> List<&2, Nat>:
  match b:
    case SB{es, vs}:
      vs

def sb.eqs(b: SB) -> List<&2, Nat>:
  match b:
    case SB{es, vs}:
      es

def allvars(bs: List<&2, SB>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      app(sb.vars(b), allvars(t))

def alleqs(bs: List<&2, SB>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      app(sb.eqs(b), alleqs(t))

def positions(xs: List<&2, Nat>, +vp: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{pos(x, vp), positions(t, vp)}

def skbs(bs: List<&2, SB>, +adj: List<&2, List<&2, Nat>>, +vp: List<&2, Nat>) -> List<&2, SkB>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{SB{+es, +vs}, t}:
      Con{SkB{es, vs, positions(minus(uses(es, adj), vs), vp)}, skbs(t, adj, vp)}


def ks.red(st: KS) -> List<&2, Red>:
  match st:
    case KS{vm, red}:
      red

def red.eq(r: Red) -> Nat:
  match r:
    case Red{e, s, w}:
      e

def red.eqs(rs: List<&2, Red>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{red.eq(r), red.eqs(t)}

def len.q(es: List<&2, E.QExpr>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, t}:
      1n+len.q(t)

def blocks.of(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +pins: List<&2, Nat>, +cs: List<&2, List<&2, Nat>>) -> List<&2, SB>:
  blocks(cs, valid(hdl(cs), adj, em, pins), adj, em, pins, Nil{})

def skel.fin(+adj: List<&2, List<&2, Nat>>, red: List<&2, Red>, +pins: List<&2, Nat>, +bs: List<&2, SB>) -> Skel:
  +vp = app(pins, allvars(bs))
  Skel{vp, alleqs(bs), len(pins), skbs(bs, adj, vp), red}

# the equations among js that use v
def users(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +v: Nat) -> List<&2, Nat>:
  match js:
    case Nil{}:
      Nil{}
    case Con{+j, t}:
      minus.go(bnot(mem(v, nthl(adj, j))), j, users(t, adj, v))

# for each variable from k on, the equations among js that use it
def transpose(n: Nat, +k: Nat, +js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{users(js, adj, k), transpose(m, 1n+k, js, adj)}

# the structure, given the variable side's run st (its map sends equations
# to variables; its failed searches are the pins)
def skel.pins(+adj: List<&2, List<&2, Nat>>, +ne: Nat, +nv: Nat, red: List<&2, Red>, +good: List<&2, Nat>, +st: KS) -> Skel:
  skel.fin(adj, red, red.eqs(ks.red(st)), blocks.of(adj, KS.vm(st), red.eqs(ks.red(st)), comps(adj, invert(KS.vm(st), 0n, nones(nv)), good, ne)))

# the variable side: match variables to the good equations, latest
# variables first, so the earliest ones are left over as pins (greedy on
# the transversal matroid: the best pin set for that order of preference)
def skel.vars(+adj: List<&2, List<&2, Nat>>, +ne: Nat, +nv: Nat, red: List<&2, Red>, +good: List<&2, Nat>, +adjt: List<&2, List<&2, Nat>>) -> Skel:
  skel.pins(adj, ne, nv, red, good, kuhn(down(nv), adjt, 1n+ne, KS{nones(ne), Nil{}}))

# the equation side's run st gives the red equations and their witnesses
def skel.go(+adj: List<&2, List<&2, Nat>>, +ne: Nat, +nv: Nat, +st: KS) -> Skel:
  skel.vars(adj, ne, nv, ks.red(st), minus(iota(ne, 0n), red.eqs(ks.red(st))), transpose(nv, 0n, minus(iota(ne, 0n), red.eqs(ks.red(st))), adj))

# The structure of a system: es over variables 0 .. nv - 1
def structure(+es: List<&2, E.QExpr>, +nv: Nat) -> Skel:
  skel.go(adj(es), len.q(es), nv, kuhn(iota(len.q(es), 0n), adj(es), 1n+nv, KS{nones(nv), Nil{}}))

# The structure of part of a system
# ---------------------------------
# The equations good (in order) of a system with adjacency adj, nq
# equations over nv variables, good being matchable (lib/solve.bend: the
# red stage's matched equations): no equation side, the variable side past
# its dead equations, then the blocks, all in the system's numbering; and
# then each equation renumbered to its position in good.

def skel.kd(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>, +st: KD) -> Skel:
  skel.fin(adj, Nil{}, KD.red(st), blocks.of(adj, KD.vm(st), KD.red(st), comps(adj, invert(KD.vm(st), 0n, nones(nv)), good, nq)))

def skel.kept(+adj: List<&2, List<&2, Nat>>, +nq: Nat, +nv: Nat, +good: List<&2, Nat>) -> Skel:
  skel.kd(adj, nq, nv, good, kuhnd(down(nv), transpose(nv, 0n, good, adj), 1n+nq, KD{nones(nq), Nil{}, Nil{}}))

def renum.bs(bs: List<&2, SkB>, +good: List<&2, Nat>) -> List<&2, SkB>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{SkB{es, vs, ps}, t}:
      Con{SkB{positions(es, good), vs, ps}, renum.bs(t, good)}

def renum(s: Skel, +good: List<&2, Nat>) -> Skel:
  match s:
    case Skel{vp, ep, np, bs, red}:
      Skel{vp, positions(ep, good), np, renum.bs(bs, good), red}
