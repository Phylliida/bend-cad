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
import ./lab.bend as LB
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcgenpf.bend as GN
import ./dcsetpf.bend as ST
import ./lspanpf.bend as LS
import ./indsetpf.bend as IP
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

# Nodes
# -----

def node_sym.go(g: Bool, +a: DR.Node, +b: DR.Node, eg: {g == DC.node_eq(b, a) : Bool}, h: {DC.node_eq(a, b) == False{} : Bool}) -> {g == False{} : Bool}:
  match g:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, LP.tf(Equal.trans(Bool, True{}, DC.node_eq(a, b), False{},
        Equal.trans(Bool, True{}, DC.node_eq(a, a), DC.node_eq(a, b), Equal.sym(Bool, DC.node_eq(a, a), True{}, node_refl(a)),
          Equal.cong(DR.Node, Bool, x => DC.node_eq(a, x), a, b, Equal.sym(DR.Node, b, a, GN.node_eq_ok(b, a, Equal.sym(Bool, True{}, DC.node_eq(b, a), eg))))), h)))

def node_sym(+a: DR.Node, +b: DR.Node, h: {DC.node_eq(a, b) == False{} : Bool}) -> {DC.node_eq(b, a) == False{} : Bool}:
  node_sym.go(DC.node_eq(b, a), a, b, {==}, h)

def node_sym_t(+a: DR.Node, +b: DR.Node, h: {DC.node_eq(a, b) == True{} : Bool}) -> {DC.node_eq(b, a) == True{} : Bool}:
  %GN.node_eq_ok(a, b, h) : {DC.node_eq(_, a) == True{} : Bool}
  node_refl(a)

# Roots
# -----

def isroot.m(m: Maybe<&2, DC.Mem>, +r: DR.Node) -> Bool:
  match m:
    case Some{DC.Mem{a, r2, w, d}}:
      DC.node_eq(r2, r)
    case None{}:
      False{}

# r's record has r as its root
def isroot(+ms: List<&2, DC.Mem>, +r: DR.Node) -> Bool:
  isroot.m(DC.mem_of(ms, r), r)

def iroot_keep.m(m: Maybe<&2, DC.Mem>, +r: DR.Node, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: {isroot.m(m, r) == True{} : Bool}, +hr: {DC.node_eq(r, old) == False{} : Bool})
  -> {isroot.m(mmap(old, new, dR, ww, m), r) == True{} : Bool}:
  match m:
    case None{}:
      absurd({isroot.m(None{}, r) == True{} : Bool}, LP.tf(Equal.sym(Bool, False{}, True{}, h)))
    case Some{DC.Mem{+a2, +r2, +w2, +d2}}:
      %Equal.sym(DR.Node, r2, r, GN.node_eq_ok(r2, r, h)) : {isroot.m(Some{DC.reroot.one(DC.node_eq(_, old), a2, _, w2, d2, new, dR, ww, old)}, r) == True{} : Bool}
      %Equal.sym(Bool, DC.node_eq(r, old), False{}, hr) : {isroot.m(Some{DC.reroot.one(_, a2, r, w2, d2, new, dR, ww, old)}, r) == True{} : Bool}
      node_refl(r)

# a root whose record is not moved stays a root
def iroot_keep(+ms: List<&2, DC.Mem>, +r: DR.Node, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: {isroot(ms, r) == True{} : Bool}, +hr: {DC.node_eq(r, old) == False{} : Bool})
  -> {isroot(DC.reroot(ms, old, new, dR, ww), r) == True{} : Bool}:
  %Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.reroot(ms, old, new, dR, ww), r), mmap(old, new, dR, ww, DC.mem_of(ms, r)), mem_reroot(ms, r, old, new, dR, ww)) : {isroot.m(_, r) == True{} : Bool}
  iroot_keep.m(DC.mem_of(ms, r), r, old, new, dR, ww, h, hr)

# every record's root is a root
def RootsOk(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>) -> Data:
  match sc:
    case Nil{}:
      Unit
    case Con{+m, tl}:
      SK.Both({isroot(ms, DC.Mem.r(m)) == True{} : Bool}, RootsOk(tl, ms))

def rok_one(f: Bool, +ms: List<&2, DC.Mem>, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  ef: {f == DC.node_eq(r0, old) : Bool}, e0: {isroot(ms, r0) == True{} : Bool}, +hn: {isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool})
  -> {isroot(DC.reroot(ms, old, new, dR, ww), DC.Mem.r(DC.reroot.one(f, a0, r0, w0, d0, new, dR, ww, old))) == True{} : Bool}:
  match f:
    case True{}:
      iroot_keep(ms, new, old, new, dR, ww, hn, node_sym(old, new, hon))
    case False{}:
      iroot_keep(ms, r0, old, new, dR, ww, e0, Equal.sym(Bool, False{}, DC.node_eq(r0, old), ef))

# rerooting to a root keeps every record's root a root
def rok_reroot(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: RootsOk(sc, ms),
  +hn: {isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}) -> RootsOk(DC.reroot(sc, old, new, dR, ww), DC.reroot(ms, old, new, dR, ww)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a0, +r0, +w0, +d0}, tl}:
      (e0, ht) = h
      (rok_one(DC.node_eq(r0, old), ms, a0, r0, w0, d0, old, new, dR, ww, {==}, e0, hn, hon), rok_reroot(tl, ms, old, new, dR, ww, ht, hn, hon))

# Root records
# ------------

def rrok.go(f: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der) -> Data:
  match f:
    case True{}:
      {DC.Mem{a, r, w, d} == DC.Mem{r, r, DC.lone(), DR.DSelf{r}} : DC.Mem}
    case False{}:
      Unit

# a record whose node is its root is (r, r, 1, DSelf r)
def rrok(m: DC.Mem) -> Data:
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      rrok.go(DC.node_eq(a, r), a, r, w, d)

def AllRR(sc: List<&2, DC.Mem>) -> Data:
  match sc:
    case Nil{}:
      Unit
    case Con{+m, tl}:
      SK.Both(rrok(m), AllRR(tl))

def rr_one.on(+old: DR.Node, +new: DR.Node, +r0: DR.Node, e1: {old == r0 : DR.Node}, e2: {r0 == new : DR.Node}) -> {True{} == DC.node_eq(old, new) : Bool}:
  %Equal.sym(DR.Node, old, r0, e1) : {True{} == DC.node_eq(_, new) : Bool}
  %Equal.sym(DR.Node, r0, new, e2) : {True{} == DC.node_eq(_, new) : Bool}
  Equal.sym(Bool, DC.node_eq(new, new), True{}, node_refl(new))

def rr_one.no(+ms: List<&2, DC.Mem>, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der, +old: DR.Node, +new: DR.Node, ea: {a0 == new : DR.Node},
  ef: {True{} == DC.node_eq(r0, old) : Bool}, f0: {DC.mem_of(ms, a0) == Some{DC.Mem{a0, r0, w0, d0}} : Maybe<&2, DC.Mem>},
  hn: {isroot(ms, new) == True{} : Bool}, hon: {DC.node_eq(old, new) == False{} : Bool}) -> Empty:
  LP.tf(Equal.trans(Bool, True{}, DC.node_eq(old, new), False{},
    rr_one.on(old, new, r0, Equal.sym(DR.Node, r0, old, GN.node_eq_ok(r0, old, Equal.sym(Bool, True{}, DC.node_eq(r0, old), ef))),
      GN.node_eq_ok(r0, new, Equal.trans(Bool, DC.node_eq(r0, new), isroot(ms, new), True{},
        Equal.sym(Bool, isroot(ms, new), DC.node_eq(r0, new), Equal.cong(Maybe<&2, DC.Mem>, Bool, x => isroot.m(x, new), DC.mem_of(ms, new), Some{DC.Mem{a0, r0, w0, d0}},
          Equal.trans(Maybe<&2, DC.Mem>, DC.mem_of(ms, new), DC.mem_of(ms, a0), Some{DC.Mem{a0, r0, w0, d0}}, Equal.cong(DR.Node, Maybe<&2, DC.Mem>, y => DC.mem_of(ms, y), new, a0, Equal.sym(DR.Node, a0, new, ea)), f0))),
        hn))),
    hon))

def rr_one.t(g: Bool, +ms: List<&2, DC.Mem>, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  eg: {g == DC.node_eq(a0, new) : Bool}, ef: {True{} == DC.node_eq(r0, old) : Bool}, f0: {DC.mem_of(ms, a0) == Some{DC.Mem{a0, r0, w0, d0}} : Maybe<&2, DC.Mem>},
  hn: {isroot(ms, new) == True{} : Bool}, hon: {DC.node_eq(old, new) == False{} : Bool})
  -> rrok.go(g, a0, new, LB.lmul(ww, w0), DR.DThrough{dR, d0, DR.Lab.conj(ww), old}):
  match g:
    case False{}:
      Unit{}
    case True{}:
      absurd(rrok.go(True{}, a0, new, LB.lmul(ww, w0), DR.DThrough{dR, d0, DR.Lab.conj(ww), old}),
        rr_one.no(ms, a0, r0, w0, d0, old, new, GN.node_eq_ok(a0, new, Equal.sym(Bool, True{}, DC.node_eq(a0, new), eg)), ef, f0, hn, hon))

def rr_one(f: Bool, +ms: List<&2, DC.Mem>, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  ef: {f == DC.node_eq(r0, old) : Bool}, rr0: rrok(DC.Mem{a0, r0, w0, d0}), f0: {DC.mem_of(ms, a0) == Some{DC.Mem{a0, r0, w0, d0}} : Maybe<&2, DC.Mem>},
  hn: {isroot(ms, new) == True{} : Bool}, hon: {DC.node_eq(old, new) == False{} : Bool}) -> rrok(DC.reroot.one(f, a0, r0, w0, d0, new, dR, ww, old)):
  match f:
    case False{}:
      rr0
    case True{}:
      rr_one.t(DC.node_eq(a0, new), ms, a0, r0, w0, d0, old, new, dR, ww, {==}, ef, f0, hn, hon)

def rr_reroot.go(+ms: List<&2, DC.Mem>, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der, +tl: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  rr0: rrok(DC.Mem{a0, r0, w0, d0}), rt: AllRR(tl), hf: AllFirst(Con{DC.Mem{a0, r0, w0, d0}, tl}, ms), +hn: {isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool},
  ih: AllRR(tl) -> AllFirst(tl, ms) -> AllRR(DC.reroot(tl, old, new, dR, ww))) -> AllRR(DC.reroot(Con{DC.Mem{a0, r0, w0, d0}, tl}, old, new, dR, ww)):
  (f0, ft) = hf
  (rr_one(DC.node_eq(r0, old), ms, a0, r0, w0, d0, old, new, dR, ww, {==}, rr0, f0, hn, hon), ih(rt, ft))

# rerooting to a root keeps the root records' shape
def rr_reroot(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: AllRR(sc), hf: AllFirst(sc, ms),
  +hn: {isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}) -> AllRR(DC.reroot(sc, old, new, dR, ww)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a0, +r0, +w0, +d0}, +tl}:
      (rr0, rt) = h
      rr_reroot.go(ms, a0, r0, w0, d0, tl, old, new, dR, ww, rr0, rt, hf, hn, hon, x => y => rr_reroot(tl, ms, old, new, dR, ww, x, y, hn, hon))

# Record nodes and collapsed segments
# -----------------------------------

def nmem(+n: DR.Node, ns: List<&2, DR.Node>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{h, t}:
      SV.bor(DC.node_eq(n, h), nmem(n, t))

# every record's node is in ns
def RecN(sc: List<&2, DC.Mem>, +ns: List<&2, DR.Node>) -> Data:
  match sc:
    case Nil{}:
      Unit
    case Con{+m, tl}:
      SK.Both({nmem(DC.Mem.a(m), ns) == True{} : Bool}, RecN(tl, ns))

def recn.one(+ns: List<&2, DR.Node>, +m: DC.Mem, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, e: {nmem(DC.Mem.a(m), ns) == True{} : Bool})
  -> {nmem(DC.Mem.a(rone(old, new, dR, ww, m)), ns) == True{} : Bool}:
  %Equal.sym(DR.Node, DC.Mem.a(rone(old, new, dR, ww, m)), DC.Mem.a(m), rone_a(old, new, dR, ww, m)) : {nmem(_, ns) == True{} : Bool}
  e

def recn_reroot(sc: List<&2, DC.Mem>, +ns: List<&2, DR.Node>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: RecN(sc, ns)) -> RecN(DC.reroot(sc, old, new, dR, ww), ns):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a0, +r0, +w0, +d0}, tl}:
      (e0, ht) = h
      (recn.one(ns, DC.Mem{a0, r0, w0, d0}, old, new, dR, ww, e0), recn_reroot(tl, ns, old, new, dR, ww, ht))

# each sketch segment is collapsed in the context or has a record
def RecS(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +ms: List<&2, DC.Mem>) -> Data:
  match ids:
    case Nil{}:
      Unit
    case Con{+s, tl}:
      SK.Both({SV.bor(DC.coll(es, cs, s), mis_some(DC.mem_of(ms, DR.NSeg{s}))) == True{} : Bool}, RecS(tl, es, cs, ms))

def mis_mmap(+old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, m: Maybe<&2, DC.Mem>) -> {mis_some(mmap(old, new, dR, ww, m)) == mis_some(m) : Bool}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def recs.one(+es: List<&2, SK.Ent>, +cs: DC.SP, +ms: List<&2, DC.Mem>, +s: Nat, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  e: {SV.bor(DC.coll(es, cs, s), mis_some(DC.mem_of(ms, DR.NSeg{s}))) == True{} : Bool})
  -> {SV.bor(DC.coll(es, cs, s), mis_some(DC.mem_of(DC.reroot(ms, old, new, dR, ww), DR.NSeg{s}))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.reroot(ms, old, new, dR, ww), DR.NSeg{s}), mmap(old, new, dR, ww, DC.mem_of(ms, DR.NSeg{s})), mem_reroot(ms, DR.NSeg{s}, old, new, dR, ww))
    : {SV.bor(DC.coll(es, cs, s), mis_some(_)) == True{} : Bool}
  %Equal.sym(Bool, mis_some(mmap(old, new, dR, ww, DC.mem_of(ms, DR.NSeg{s}))), mis_some(DC.mem_of(ms, DR.NSeg{s})), mis_mmap(old, new, dR, ww, DC.mem_of(ms, DR.NSeg{s})))
    : {SV.bor(DC.coll(es, cs, s), _) == True{} : Bool}
  e

def recs_reroot(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, h: RecS(ids, es, cs, ms))
  -> RecS(ids, es, cs, DC.reroot(ms, old, new, dR, ww)):
  match ids:
    case Nil{}:
      Unit{}
    case Con{+s, tl}:
      (e0, ht) = h
      (recs.one(es, cs, ms, s, old, new, dR, ww, e0), recs_reroot(tl, es, cs, ms, old, new, dR, ww, ht))

# The records' shape
# ------------------

def ShM(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>) -> Data:
  SK.Both(AllFirst(ms, ms), SK.Both(AllRR(ms), SK.Both(RootsOk(ms, ms), SK.Both({isroot(ms, DR.NFrame{}) == True{} : Bool},
    SK.Both(RecN(ms, Con{DR.NFrame{}, DC.snodes(ids)}), RecS(ids, es, cs, ms))))))

def sh.af(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> AllFirst(ms, ms):
  (a, r1) = h
  a

def sh.rr(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> AllRR(ms):
  (a, r1) = h
  (b, r2) = r1
  b

def sh.ro(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> RootsOk(ms, ms):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  c

def sh.fr(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> {isroot(ms, DR.NFrame{}) == True{} : Bool}:
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, r4) = r3
  d

def sh.rn(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> RecN(ms, Con{DR.NFrame{}, DC.snodes(ids)}):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, r4) = r3
  (e, f) = r4
  e

def sh.rs(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, h: ShM(es, cs, ids, ms)) -> RecS(ids, es, cs, ms):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, r4) = r3
  (e, f) = r4
  f

# rerooting a root (not F) under another root keeps the shape
def reroot_sh(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +h: ShM(es, cs, ids, ms),
  +hn: {isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}, +hof: {DC.node_eq(old, DR.NFrame{}) == False{} : Bool})
  -> ShM(es, cs, ids, DC.reroot(ms, old, new, dR, ww)):
  (af_reroot(ms, ms, old, new, dR, ww, sh.af(es, cs, ids, ms, h)),
   (rr_reroot(ms, ms, old, new, dR, ww, sh.rr(es, cs, ids, ms, h), sh.af(es, cs, ids, ms, h), hn, hon),
    (rok_reroot(ms, ms, old, new, dR, ww, sh.ro(es, cs, ids, ms, h), hn, hon),
     (iroot_keep(ms, DR.NFrame{}, old, new, dR, ww, sh.fr(es, cs, ids, ms, h), node_sym(old, DR.NFrame{}, hof)),
      (recn_reroot(ms, Con{DR.NFrame{}, DC.snodes(ids)}, old, new, dR, ww, sh.rn(es, cs, ids, ms, h)), recs_reroot(ids, es, cs, ms, old, new, dR, ww, sh.rs(es, cs, ids, ms, h)))))))

def hof.eq(+rb: DR.Node, +rr: DR.Node, e1: {rb == DR.NFrame{} : DR.Node}, e2: {rr == DR.NFrame{} : DR.Node}) -> {True{} == DC.node_eq(rb, rr) : Bool}:
  %Equal.sym(DR.Node, rb, DR.NFrame{}, e1) : {True{} == DC.node_eq(_, rr) : Bool}
  %Equal.sym(DR.Node, rr, DR.NFrame{}, e2) : {True{} == DC.node_eq(DR.NFrame{}, _) : Bool}
  {==}

def hof.go(g: Bool, +rb: DR.Node, +rr: DR.Node, eg: {g == DC.node_eq(rb, DR.NFrame{}) : Bool}, ef: {False{} == SV.band(g, SV.bnot(DC.node_eq(rr, DR.NFrame{}))) : Bool},
  hne: {DC.node_eq(rb, rr) == False{} : Bool}) -> {g == False{} : Bool}:
  match g:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, LP.tf(Equal.trans(Bool, True{}, DC.node_eq(rb, rr), False{},
        hof.eq(rb, rr, GN.node_eq_ok(rb, DR.NFrame{}, Equal.sym(Bool, True{}, DC.node_eq(rb, DR.NFrame{}), eg)),
          GN.node_eq_ok(rr, DR.NFrame{}, LS.bnot_f(DC.node_eq(rr, DR.NFrame{}), Equal.sym(Bool, False{}, SV.bnot(DC.node_eq(rr, DR.NFrame{})), ef)))),
        hne)))

def merge_sh.go(f: Bool, +es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +ef: {f == SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))) : Bool}, +h: ShM(es, cs, ids, ms), +hrr: {isroot(ms, rr) == True{} : Bool},
  +hne: {DC.node_eq(rb, rr) == False{} : Bool}) -> ShM(es, cs, ids, DC.merge.go(f, ms, rr, d1, w, b, rb, wb, db)):
  match f:
    case True{}:
      reroot_sh(es, cs, ids, ms, rr, DR.NFrame{}, DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}, LB.lmul(wb, DR.Lab.conj(w)), h, sh.fr(es, cs, ids, ms, h),
        IP.bnot_t(DC.node_eq(rr, DR.NFrame{}), LP2.band_r(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{})), Equal.sym(Bool, True{}, SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ef))),
        IP.bnot_t(DC.node_eq(rr, DR.NFrame{}), LP2.band_r(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{})), Equal.sym(Bool, True{}, SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ef))))
    case False{}:
      reroot_sh(es, cs, ids, ms, rb, rr, DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}, LB.lmul(w, DR.Lab.conj(wb)), h, hrr, hne,
        hof.go(DC.node_eq(rb, DR.NFrame{}), rb, rr, {==}, ef, hne))

# a merge of b's component into the root rr keeps the shape
def merge_sh(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, m: DC.Mem, +h: ShM(es, cs, ids, ms),
  +hrr: {isroot(ms, rr) == True{} : Bool}, hne: {DC.node_eq(DC.Mem.r(m), rr) == False{} : Bool}) -> ShM(es, cs, ids, DC.merge(ms, rr, d1, w, m)):
  match m:
    case DC.Mem{+b, +rb, +wb, +db}:
      merge_sh.go(SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), es, cs, ids, ms, rr, d1, w, b, rb, wb, db, {==}, h, hrr, hne)
