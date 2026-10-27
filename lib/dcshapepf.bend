# bend-cad: the closure state's shape (PLAN-sk13b B3, "Closure of a
# fixpoint"): the facts about the member records, the links and K that the
# closure theorem reads off the final state, kept by every round:
# - every record is the first record of its node (sketch ids may repeat,
#   so a node can have several records; they stay equal);
# - a record whose node is its root is (r, r, 1, DSelf r);
# - every record's root is a root (its record's root is itself);
# - every record's node is F or a sketch segment;
# - F has a record, and each sketch segment is collapsed or has one;
# - every fact is in K;
# - each pair's first two stored labels are independent.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./listpf.bend as LP2
import ./labpf.bend as LP
import ./kspace.bend as KS
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcgenpf.bend as GN
import ./dcsetpf.bend as ST
import ./lspanpf.bend as LS
import ./pairpf.bend as PP

def absurd(-A: Type, x: Empty) -> A:
  match x:

def node_refl(a: DR.Node) -> {DC.node_eq(a, a) == True{} : Bool}:
  match a:
    case DR.NFrame{}:
      {==}
    case DR.NSeg{s}:
      LP2.eq_refl(s)

# DC.Mem lists by position
def mat(xs: List<&2, DC.Mem>, n: Nat) -> Maybe<&2, DC.Mem>:
  match xs n:
    case Nil{} n:
      None{}
    case Con{x, tl} 0n:
      Some{x}
    case Con{x, tl} 1n+k:
      mat(tl, k)

def Inm(+x: DC.Mem, +xs: List<&2, DC.Mem>) -> Data:
  Sigma<&2, &2, Nat, n => {mat(xs, n) == Some{x} : Maybe<&2, DC.Mem>}>

def mis_some(m: Maybe<&2, DC.Mem>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def msome_or(m: Maybe<&2, DC.Mem>, +d: DC.Mem) -> DC.Mem:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def msome_inj(+x: DC.Mem, +y: DC.Mem, h: {Some{x} == Some{y} : Maybe<&2, DC.Mem>}) -> {x == y : DC.Mem}:
  Equal.cong(Maybe<&2, DC.Mem>, DC.Mem, m => msome_or(m, x), Some{x}, Some{y}, h)

def mnone_some(+y: DC.Mem, h: {None{} == Some{y} : Maybe<&2, DC.Mem>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DC.Mem>, Bool, m => mis_some(m), None{}, Some{y}, h)) : PP.none_some.p(_)
  Unit{}

def inm_hd(+x: DC.Mem, +tl: List<&2, DC.Mem>) -> Inm(x, Con{x, tl}):
  (0n, {==})

def inm_tl.go(+x: DC.Mem, +h0: DC.Mem, +tl: List<&2, DC.Mem>, +n: Nat, +e: {mat(tl, n) == Some{x} : Maybe<&2, DC.Mem>}) -> Inm(x, Con{h0, tl}):
  (1n+n, e)

def inm_tl(+x: DC.Mem, +h0: DC.Mem, +tl: List<&2, DC.Mem>, h: Inm(x, tl)) -> Inm(x, Con{h0, tl}):
  (+n, +e) = h
  inm_tl.go(x, h0, tl, n, e)

# DC.Link lists by position
def lat(xs: List<&2, DC.Link>, n: Nat) -> Maybe<&2, DC.Link>:
  match xs n:
    case Nil{} n:
      None{}
    case Con{x, tl} 0n:
      Some{x}
    case Con{x, tl} 1n+k:
      lat(tl, k)

def Inl(+x: DC.Link, +xs: List<&2, DC.Link>) -> Data:
  Sigma<&2, &2, Nat, n => {lat(xs, n) == Some{x} : Maybe<&2, DC.Link>}>

def lis_some(m: Maybe<&2, DC.Link>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def lsome_or(m: Maybe<&2, DC.Link>, +d: DC.Link) -> DC.Link:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def lsome_inj(+x: DC.Link, +y: DC.Link, h: {Some{x} == Some{y} : Maybe<&2, DC.Link>}) -> {x == y : DC.Link}:
  Equal.cong(Maybe<&2, DC.Link>, DC.Link, m => lsome_or(m, x), Some{x}, Some{y}, h)

def lnone_some(+y: DC.Link, h: {None{} == Some{y} : Maybe<&2, DC.Link>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DC.Link>, Bool, m => lis_some(m), None{}, Some{y}, h)) : PP.none_some.p(_)
  Unit{}

def inl_hd(+x: DC.Link, +tl: List<&2, DC.Link>) -> Inl(x, Con{x, tl}):
  (0n, {==})

def inl_tl.go(+x: DC.Link, +h0: DC.Link, +tl: List<&2, DC.Link>, +n: Nat, +e: {lat(tl, n) == Some{x} : Maybe<&2, DC.Link>}) -> Inl(x, Con{h0, tl}):
  (1n+n, e)

def inl_tl(+x: DC.Link, +h0: DC.Link, +tl: List<&2, DC.Link>, h: Inl(x, tl)) -> Inl(x, Con{h0, tl}):
  (+n, +e) = h
  inl_tl.go(x, h0, tl, n, e)

# DR.Node lists by position
def nat(xs: List<&2, DR.Node>, n: Nat) -> Maybe<&2, DR.Node>:
  match xs n:
    case Nil{} n:
      None{}
    case Con{x, tl} 0n:
      Some{x}
    case Con{x, tl} 1n+k:
      nat(tl, k)

def Inn(+x: DR.Node, +xs: List<&2, DR.Node>) -> Data:
  Sigma<&2, &2, Nat, n => {nat(xs, n) == Some{x} : Maybe<&2, DR.Node>}>

def nis_some(m: Maybe<&2, DR.Node>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def nsome_or(m: Maybe<&2, DR.Node>, +d: DR.Node) -> DR.Node:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def nsome_inj(+x: DR.Node, +y: DR.Node, h: {Some{x} == Some{y} : Maybe<&2, DR.Node>}) -> {x == y : DR.Node}:
  Equal.cong(Maybe<&2, DR.Node>, DR.Node, m => nsome_or(m, x), Some{x}, Some{y}, h)

def nnone_some(+y: DR.Node, h: {None{} == Some{y} : Maybe<&2, DR.Node>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DR.Node>, Bool, m => nis_some(m), None{}, Some{y}, h)) : PP.none_some.p(_)
  Unit{}

def inn_hd(+x: DR.Node, +tl: List<&2, DR.Node>) -> Inn(x, Con{x, tl}):
  (0n, {==})

def inn_tl.go(+x: DR.Node, +h0: DR.Node, +tl: List<&2, DR.Node>, +n: Nat, +e: {nat(tl, n) == Some{x} : Maybe<&2, DR.Node>}) -> Inn(x, Con{h0, tl}):
  (1n+n, e)

def inn_tl(+x: DR.Node, +h0: DR.Node, +tl: List<&2, DR.Node>, h: Inn(x, tl)) -> Inn(x, Con{h0, tl}):
  (+n, +e) = h
  inn_tl.go(x, h0, tl, n, e)

# Finding records
# ---------------

# m is in ms, and its node is a
def MemIn(+ms: List<&2, DC.Mem>, +a: DR.Node, +m: DC.Mem) -> Data:
  SK.Both(Inm(m, ms), {DC.node_eq(DC.Mem.a(m), a) == True{} : Bool})

def mem_of_in.tl(+m0: DC.Mem, +tl: List<&2, DC.Mem>, +a: DR.Node, +m: DC.Mem, h: MemIn(tl, a, m)) -> MemIn(Con{m0, tl}, a, m):
  (hi, hn) = h
  (inm_tl(m, m0, tl, hi), hn)

def mem_of_in.pick(f: Bool, +m0: DC.Mem, +tl: List<&2, DC.Mem>, +a: DR.Node, ef: {f == DC.node_eq(DC.Mem.a(m0), a) : Bool}, +m: DC.Mem,
  e: {DC.mem_or(f, m0, DC.mem_of(tl, a)) == Some{m} : Maybe<&2, DC.Mem>}, ih: {DC.mem_of(tl, a) == Some{m} : Maybe<&2, DC.Mem>} -> MemIn(tl, a, m)) -> MemIn(Con{m0, tl}, a, m):
  match f:
    case True{}:
      %msome_inj(m0, m, e) : MemIn(Con{m0, tl}, a, _)
      ((0n, {==}), Equal.sym(Bool, True{}, DC.node_eq(DC.Mem.a(m0), a), ef))
    case False{}:
      mem_of_in.tl(m0, tl, a, m, ih(e))

# the record mem_of finds is in the list, with the node asked for
def mem_of_in(ms: List<&2, DC.Mem>, +a: DR.Node, +m: DC.Mem, e: {DC.mem_of(ms, a) == Some{m} : Maybe<&2, DC.Mem>}) -> MemIn(ms, a, m):
  match ms:
    case Nil{}:
      absurd(MemIn(Nil{}, a, m), mnone_some(m, e))
    case Con{+m0, +tl}:
      mem_of_in.pick(DC.node_eq(DC.Mem.a(m0), a), m0, tl, a, {==}, m, e, h => mem_of_in(tl, a, m, h))

# Rerooting
# ---------

def rone(+old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, m: DC.Mem) -> DC.Mem:
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)

def mmap(+old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, m: Maybe<&2, DC.Mem>) -> Maybe<&2, DC.Mem>:
  match m:
    case Some{x}:
      Some{rone(old, new, dR, ww, x)}
    case None{}:
      None{}

def rone_a.go(f: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +old: DR.Node)
  -> {DC.Mem.a(DC.reroot.one(f, a, r, w, d, new, dR, ww, old)) == a : DR.Node}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# rerooting keeps each record's node
def rone_a(+old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, m: DC.Mem) -> {DC.Mem.a(rone(old, new, dR, ww, m)) == DC.Mem.a(m) : DR.Node}:
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      rone_a.go(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)

def mem_reroot.g(g: Bool, +m0: DC.Mem, +tl: List<&2, DC.Mem>, +a: DR.Node, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  ih: {DC.mem_of(DC.reroot(tl, old, new, dR, ww), a) == mmap(old, new, dR, ww, DC.mem_of(tl, a)) : Maybe<&2, DC.Mem>})
  -> {DC.mem_or(g, rone(old, new, dR, ww, m0), DC.mem_of(DC.reroot(tl, old, new, dR, ww), a)) == mmap(old, new, dR, ww, DC.mem_or(g, m0, DC.mem_of(tl, a))) : Maybe<&2, DC.Mem>}:
  match g:
    case True{}:
      {==}
    case False{}:
      ih

# mem_of commutes with reroot
def mem_reroot(ms: List<&2, DC.Mem>, +a: DR.Node, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab)
  -> {DC.mem_of(DC.reroot(ms, old, new, dR, ww), a) == mmap(old, new, dR, ww, DC.mem_of(ms, a)) : Maybe<&2, DC.Mem>}:
  match ms:
    case Nil{}:
      {==}
    case Con{DC.Mem{+a0, +r0, +w0, +d0}, +tl}:
      %Equal.sym(DR.Node, DC.Mem.a(rone(old, new, dR, ww, DC.Mem{a0, r0, w0, d0})), a0, rone_a(old, new, dR, ww, DC.Mem{a0, r0, w0, d0}))
        : {DC.mem_or(DC.node_eq(_, a), rone(old, new, dR, ww, DC.Mem{a0, r0, w0, d0}), DC.mem_of(DC.reroot(tl, old, new, dR, ww), a)) == mmap(old, new, dR, ww, DC.mem_of(Con{DC.Mem{a0, r0, w0, d0}, tl}, a)) : Maybe<&2, DC.Mem>}
      mem_reroot.g(DC.node_eq(a0, a), DC.Mem{a0, r0, w0, d0}, tl, a, old, new, dR, ww, mem_reroot(tl, a, old, new, dR, ww))

# every record is the first record of its node
def AllFirst(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>) -> Data:
  match sc:
    case Nil{}:
      Unit
    case Con{+m, tl}:
      SK.Both({DC.mem_of(ms, DC.Mem.a(m)) == Some{m} : Maybe<&2, DC.Mem>}, AllFirst(tl, ms))

def af_one(+ms: List<&2, DC.Mem>, +m: DC.Mem, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, e: {DC.mem_of(ms, DC.Mem.a(m)) == Some{m} : Maybe<&2, DC.Mem>})
  -> {DC.mem_of(DC.reroot(ms, old, new, dR, ww), DC.Mem.a(rone(old, new, dR, ww, m))) == Some{rone(old, new, dR, ww, m)} : Maybe<&2, DC.Mem>}:
  %Equal.sym(DR.Node, DC.Mem.a(rone(old, new, dR, ww, m)), DC.Mem.a(m), rone_a(old, new, dR, ww, m)) : {DC.mem_of(DC.reroot(ms, old, new, dR, ww), _) == Some{rone(old, new, dR, ww, m)} : Maybe<&2, DC.Mem>}
  Equal.trans(Maybe<&2, DC.Mem>, DC.mem_of(DC.reroot(ms, old, new, dR, ww), DC.Mem.a(m)), mmap(old, new, dR, ww, DC.mem_of(ms, DC.Mem.a(m))), Some{rone(old, new, dR, ww, m)},
    mem_reroot(ms, DC.Mem.a(m), old, new, dR, ww), Equal.cong(Maybe<&2, DC.Mem>, Maybe<&2, DC.Mem>, x => mmap(old, new, dR, ww, x), DC.mem_of(ms, DC.Mem.a(m)), Some{m}, e))

# rerooting keeps every record the first of its node
def af_reroot(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: AllFirst(sc, ms))
  -> AllFirst(DC.reroot(sc, old, new, dR, ww), DC.reroot(ms, old, new, dR, ww)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a0, +r0, +w0, +d0}, tl}:
      (e0, ht) = h
      (af_one(ms, DC.Mem{a0, r0, w0, d0}, old, new, dR, ww, e0), af_reroot(tl, ms, old, new, dR, ww, ht))
