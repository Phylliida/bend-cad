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
import ./hspace.bend as HS
import ./lab.bend as LB
import ./labnzpf.bend as NZ
import ./dcreppf.bend as RP
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

# The merge search keeps the shape
# --------------------------------

def OptSh(+es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, m: Maybe<&2, List<&2, DC.Mem>>) -> Data:
  match m:
    case Some{+ms}:
      ShM(es, cs, ids, ms)
    case None{}:
      Unit

def mgF.pick_sh(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +k: KS.KS, +ms: List<&2, DC.Mem>,
  +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +h: ShM(es, cs, ids, ms), +hne: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptSh(es, cs, ids, rest)) -> OptSh(es, cs, ids, DC.mgF.pick(m, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      merge_sh(es, cs, ids, ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, DC.Mem{b, rb, wb, db}, h, sh.fr(es, cs, ids, ms, h), hne)

def mgF.if_sh(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +k: KS.KS, +ms: List<&2, DC.Mem>,
  +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, ef: {f == SV.bnot(DC.node_eq(rb, DR.NFrame{})) : Bool}, +h: ShM(es, cs, ids, ms),
  +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptSh(es, cs, ids, rest)) -> OptSh(es, cs, ids, DC.mgF.if(f, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgF.pick_sh(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, cs, ids, k, ms, b, rb, wb, db, h,
        IP.bnot_t(DC.node_eq(rb, DR.NFrame{}), Equal.sym(Bool, True{}, SV.bnot(DC.node_eq(rb, DR.NFrame{})), ef)), rest, hr)
    case False{}:
      hr

def mgF_sh(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +k: KS.KS, +ms: List<&2, DC.Mem>, +h: ShM(es, cs, ids, ms))
  -> OptSh(es, cs, ids, DC.mgF(sc, es, fs, k, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +t}:
      mgF.if_sh(SV.bnot(DC.node_eq(rb, DR.NFrame{})), es, fs, cs, ids, k, ms, b, rb, wb, db, {==}, h, DC.mgF(t, es, fs, k, ms), mgF_sh(t, es, fs, cs, ids, k, ms, h))

def mgR.pick_sh(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +t: Nat, +hh: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>,
  +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +h: ShM(es, cs, ids, ms), +hrr: {isroot(ms, r) == True{} : Bool}, +hne: {DC.node_eq(rb, r) == False{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptSh(es, cs, ids, rest)) -> OptSh(es, cs, ids, DC.mgR.pick(m, es, fs, t, hh, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      merge_sh(es, cs, ids, ms, r, HS.hs.der(es, fs, t, r, hh, DR.gmul(w, DR.zdir(es, b))), w, DC.Mem{b, rb, wb, db}, h, hrr, hne)

def mgR.if_sh(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +t: Nat, +hh: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>,
  +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, ef: {f == SV.bnot(DC.node_eq(rb, r)) : Bool}, +h: ShM(es, cs, ids, ms), +hrr: {isroot(ms, r) == True{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptSh(es, cs, ids, rest)) -> OptSh(es, cs, ids, DC.mgR.if(f, es, fs, t, hh, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgR.pick_sh(LB.hs.lab(es, fs, t, hh, DR.zdir(es, b)), es, fs, cs, ids, t, hh, r, ms, b, rb, wb, db, h, hrr,
        IP.bnot_t(DC.node_eq(rb, r), Equal.sym(Bool, True{}, SV.bnot(DC.node_eq(rb, r)), ef)), rest, hr)
    case False{}:
      hr

def mgR_sh(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +t: Nat, +hh: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>,
  +h: ShM(es, cs, ids, ms), +hrr: {isroot(ms, r) == True{} : Bool}) -> OptSh(es, cs, ids, DC.mgR(sc, es, fs, t, hh, r, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      mgR.if_sh(SV.bnot(DC.node_eq(rb, r)), es, fs, cs, ids, t, hh, r, ms, b, rb, wb, db, {==}, h, hrr, DC.mgR(tl, es, fs, t, hh, r, ms), mgR_sh(tl, es, fs, cs, ids, t, hh, r, ms, h, hrr))

# each of these nodes is a root
def AllRoot(rs: List<&2, DR.Node>, +ms: List<&2, DC.Mem>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{+r, +tl}:
      SK.Both({isroot(ms, r) == True{} : Bool}, AllRoot(tl, ms))

def roots_root.pick(f: Bool, +ms: List<&2, DC.Mem>, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, ef: {f == DC.node_eq(a, r) : Bool},
  e: {DC.mem_of(ms, a) == Some{DC.Mem{a, r, w, d}} : Maybe<&2, DC.Mem>}, +rest: List<&2, DR.Node>, hr: AllRoot(rest, ms)) -> AllRoot(DC.roots.pick(f, a, rest), ms):
  match f:
    case True{}:
      (Equal.trans(Bool, isroot(ms, a), DC.node_eq(r, a), True{}, Equal.cong(Maybe<&2, DC.Mem>, Bool, x => isroot.m(x, a), DC.mem_of(ms, a), Some{DC.Mem{a, r, w, d}}, e),
         node_sym_t(a, r, Equal.sym(Bool, True{}, DC.node_eq(a, r), ef))), hr)
    case False{}:
      hr

# the roots the search goes over are roots
def roots_root(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, h: AllFirst(sc, ms)) -> AllRoot(DC.roots(sc), ms):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a, +r, +w, +d}, +t}:
      (e0, ht) = h
      roots_root.pick(DC.node_eq(a, r), ms, a, r, w, d, {==}, e0, DC.roots(t), roots_root(t, ms, ht))

def mgs.root_sh(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +t: Nat, +s: DC.Sk, +r: DR.Node,
  +h: ShM(es, cs, ids, DC.Sk.ms(s)), +hrr: {isroot(DC.Sk.ms(s), r) == True{} : Bool}) -> OptSh(es, cs, ids, DC.mgs.root(f, es, fs, t, s, r)):
  match f:
    case True{}:
      mgF_sh(DC.Sk.ms(s), es, fs, cs, ids, DC.Sk.k(s), DC.Sk.ms(s), h)
    case False{}:
      mgR_sh(DC.Sk.ms(s), es, fs, cs, ids, t, DC.rhull(es, fs, t, s, r), r, DC.Sk.ms(s), h, hrr)

def mgs.pick_sh(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +cs: DC.SP, +ids: List<&2, Nat>, hm: OptSh(es, cs, ids, m), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptSh(es, cs, ids, rest))
  -> OptSh(es, cs, ids, DC.mgs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

# the first merge keeps the shape
def mgs_sh(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +t: Nat, +s: DC.Sk,
  +h: ShM(es, cs, ids, DC.Sk.ms(s)), hrs: AllRoot(rs, DC.Sk.ms(s))) -> OptSh(es, cs, ids, DC.mgs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (hr0, ht) = hrs
      mgs.pick_sh(DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r), es, cs, ids, mgs.root_sh(DC.node_eq(r, DR.NFrame{}), es, fs, cs, ids, t, s, r, h, hr0),
        DC.mgs(tl, es, fs, t, s), mgs_sh(tl, es, fs, cs, ids, t, s, h, ht))

# K holds every fact
# ------------------

def KR(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> Data:
  ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k))

# each of the facts fs is in K
def KF(+k: KS.KS, fs: List<&2, DR.Fact>) -> Data:
  match fs:
    case Nil{}:
      Unit
    case Con{DR.Fact{+e, nd, ds}, tl}:
      SK.Both({KS.ks.inb(k, e) == True{} : Bool}, KF(k, tl))

# K only grows
def kf_add(fs: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs0: List<&2, DR.Fact>, +k: KS.KS, +d: DR.Der, +hr: KR(es, fs0, k), h: KF(k, fs)) -> KF(KS.ks.add(es, fs0, k, d), fs):
  match fs:
    case Nil{}:
      Unit{}
    case Con{DR.Fact{+e, nd, ds}, tl}:
      (e0, ht) = h
      (ST.ks_add_mono(es, fs0, k, d, e, hr, e0), kf_add(tl, es, fs0, k, d, hr, ht))

# the fact at i is in K
def kf_at(fs: List<&2, DR.Fact>, i: Nat, +k: KS.KS, h: KF(k, fs), hf: DR.HasFact(DR.fact_at(fs, i))) -> {KS.ks.inb(k, DR.fact.e(DR.fact_at(fs, i))) == True{} : Bool}:
  match fs i:
    case Nil{} i:
      absurd({KS.ks.inb(k, DR.fact.e(DR.fact_at(Nil{}, i))) == True{} : Bool}, hf)
    case Con{DR.Fact{+e, nd, ds}, tl} 0n:
      (e0, ht) = h
      e0
    case Con{DR.Fact{+e, nd, ds}, tl} 1n+j:
      (e0, ht) = h
      kf_at(tl, j, k, ht, hf)

def kinit_ri(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +hr: KR(es, fs, k)) -> KR(es, fs, DC.kinit(es, fs, rest, i, k)):
  match rest:
    case Nil{}:
      hr
    case Con{f, t}:
      kinit_ri(t, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), ST.ks_add_ri(es, fs, k, DR.DPrem{i}, hr))

def kinit_mono(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +e: E.QExpr, +hr: KR(es, fs, k), hz: ST.Inb(KS.ks.rows(k), e))
  -> ST.Inb(KS.ks.rows(DC.kinit(es, fs, rest, i, k)), e):
  match rest:
    case Nil{}:
      hz
    case Con{f, t}:
      kinit_mono(t, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), e, ST.ks_add_ri(es, fs, k, DR.DPrem{i}, hr), ST.ks_add_mono(es, fs, k, DR.DPrem{i}, e, hr, hz))

def kinit_kf.hd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>, +t: List<&2, DR.Fact>, +hr: KR(es, fs, k),
  ef: {DR.fact_at(fs, i) == Some{DR.Fact{e, nd, ds}} : Maybe<&2, DR.Fact>}) -> ST.Inb(KS.ks.rows(KS.ks.add(es, fs, k, DR.DPrem{i})), e):
  %ef : ST.Inb(KS.ks.rows(KS.ks.add(es, fs, k, DR.DPrem{i})), DR.fact.e(_))
  ST.ks_add_new(es, fs, k, DR.DPrem{i}, hr)

# kinit puts every fact into K
def kinit_kf(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +hr: KR(es, fs, k), +ed: {GN.fdrop(i, fs) == rest : List<&2, DR.Fact>})
  -> KF(DC.kinit(es, fs, rest, i, k), rest):
  match rest:
    case Nil{}:
      Unit{}
    case Con{DR.Fact{+e, +nd, +ds}, +t}:
      (kinit_mono(t, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), e, ST.ks_add_ri(es, fs, k, DR.DPrem{i}, hr),
         kinit_kf.hd(es, fs, i, k, e, nd, ds, t, hr, GN.fat_drop(i, fs, DR.Fact{e, nd, ds}, t, ed))),
       kinit_kf(t, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), ST.ks_add_ri(es, fs, k, DR.DPrem{i}, hr), GN.fdrop_tl(i, fs, DR.Fact{e, nd, ds}, t, ed)))

# Stored labels
# -------------

def wsnoc(ws: List<&2, DR.Lab>, +w: DR.Lab) -> List<&2, DR.Lab>:
  match ws:
    case Nil{}:
      Con{w, Nil{}}
    case Con{h, t}:
      Con{h, wsnoc(t, w)}

def wsnoc_if(f: Bool, +ws: List<&2, DR.Lab>, +w: DR.Lab) -> List<&2, DR.Lab>:
  match f:
    case True{}:
      wsnoc(ws, w)
    case False{}:
      ws

def lst.g(g: Bool, f: Bool, +w: DR.Lab, +S: List<&2, DR.Lab>, +wx: DR.Lab)
  -> {DC.lstored.pick(g, w, wsnoc_if(f, S, wx)) == wsnoc_if(f, DC.lstored.pick(g, w, S), wx) : List<&2, DR.Lab>}:
  match g f:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} f:
      {==}

def lst.nil(f: Bool, +wx: DR.Lab) -> {DC.lstored.pick(f, wx, Nil{}) == wsnoc_if(f, Nil{}, wx) : List<&2, DR.Lab>}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# the stored labels after a link is appended
def lstored_snoc(ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der)
  -> {DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b) == wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx) : List<&2, DR.Lab>}:
  match ls:
    case Nil{}:
      lst.nil(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), wx)
    case Con{DC.Link{+c2, +bl, +w, +d}, +t}:
      Equal.trans(List<&2, DR.Lab>, DC.lstored.pick(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), w, DC.lstored(DC.lsnoc(t, DC.Link{cx, bx, wx, dx}), c, b)),
        DC.lstored.pick(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), w, wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(t, c, b), wx)),
        wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored.pick(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), w, DC.lstored(t, c, b)), wx),
        Equal.cong(List<&2, DR.Lab>, List<&2, DR.Lab>, x => DC.lstored.pick(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), w, x), DC.lstored(DC.lsnoc(t, DC.Link{cx, bx, wx, dx}), c, b),
          wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(t, c, b), wx), lstored_snoc(t, c, b, cx, bx, wx, dx)),
        lst.g(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), w, DC.lstored(t, c, b), wx))

# a fresh label keeps the first two independent
def pairok_snoc(ws: List<&2, DR.Lab>, +w: DR.Lab, hp: {LS.pairok(ws) == True{} : Bool}, hq: {DC.qspan(ws, w) == False{} : Bool}) -> {LS.pairok(wsnoc(ws, w)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w0, Nil{}}:
      %Equal.sym(Bool, DC.lpar(w0, w), False{}, hq) : {SV.bnot(_) == True{} : Bool}
      {==}
    case Con{+w0, Con{+w1, +t}}:
      hp

def pok_if(f: Bool, +ws: List<&2, DR.Lab>, +w: DR.Lab, hp: {LS.pairok(ws) == True{} : Bool}, hq: {f == True{} : Bool} -> {DC.qspan(ws, w) == False{} : Bool})
  -> {LS.pairok(wsnoc_if(f, ws, w)) == True{} : Bool}:
  match f:
    case True{}:
      pairok_snoc(ws, w, hp, hq({==}))
    case False{}:
      hp

# each link's pair has its first two stored labels independent
def PairL(sc: List<&2, DC.Link>, +ls: List<&2, DC.Link>) -> Data:
  match sc:
    case Nil{}:
      Unit
    case Con{DC.Link{+c, +b, w, d}, tl}:
      SK.Both({LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}, PairL(tl, ls))

def fr_at(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, fr: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool},
  +hf: {SV.band(SV.eq(cx, c), DC.node_eq(bx, b)) == True{} : Bool}) -> {DC.qspan(DC.lstored(ls, c, b), wx) == False{} : Bool}:
  %LP2.eq_ok(cx, c, LP2.band_l(SV.eq(cx, c), DC.node_eq(bx, b), hf)) : {DC.qspan(DC.lstored(ls, _, b), wx) == False{} : Bool}
  %GN.node_eq_ok(bx, b, LP2.band_r(SV.eq(cx, c), DC.node_eq(bx, b), hf)) : {DC.qspan(DC.lstored(ls, cx, _), wx) == False{} : Bool}
  fr

def pl_one(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, e0: {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool},
  +fr: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool}) -> {LS.pairok(DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b)) == True{} : Bool}:
  %Equal.sym(List<&2, DR.Lab>, DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b), wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), lstored_snoc(ls, c, b, cx, bx, wx, dx))
    : {LS.pairok(_) == True{} : Bool}
  pok_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx, e0, hf => fr_at(ls, c, b, cx, bx, wx, fr, hf))

def pl_old(sc: List<&2, DC.Link>, +ls: List<&2, DC.Link>, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, h: PairL(sc, ls), +fr: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool})
  -> PairL(sc, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c, +b, w, d}, tl}:
      (e0, ht) = h
      (pl_one(ls, c, b, cx, bx, wx, dx, e0, fr), pl_old(tl, ls, cx, bx, wx, dx, ht, fr))

def pl_cat(sc: List<&2, DC.Link>, +all: List<&2, DC.Link>, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, h: PairL(sc, all),
  +e: {LS.pairok(DC.lstored(all, cx, bx)) == True{} : Bool}) -> PairL(DC.lsnoc(sc, DC.Link{cx, bx, wx, dx}), all):
  match sc:
    case Nil{}:
      (e, Unit{})
    case Con{DC.Link{+c, +b, +w, +d}, tl}:
      (e0, ht) = h
      (e0, pl_cat(tl, all, cx, bx, wx, dx, ht, e))

def lcons(ws: List<&2, DR.Lab>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, t}:
      True{}

def pok_nil(ws: List<&2, DR.Lab>, h: {lcons(ws) == False{} : Bool}) -> {LS.pairok(ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      absurd({LS.pairok(Con{w, t}) == True{} : Bool}, LP.tf(h))

def pok_find.g(g: Bool, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +c2: Nat, +b2: DR.Node, +w: DR.Lab, +tl: List<&2, DC.Link>,
  +eg: {g == SV.band(SV.eq(c2, c), DC.node_eq(b2, b)) : Bool}, e0: {LS.pairok(DC.lstored(ls, c2, b2)) == True{} : Bool},
  hne: {lcons(DC.lstored.pick(g, w, DC.lstored(tl, c, b))) == True{} : Bool}, ih: {lcons(DC.lstored(tl, c, b)) == True{} : Bool} -> {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool})
  -> {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}:
  match g:
    case True{}:
      %LP2.eq_ok(c2, c, LP2.band_l(SV.eq(c2, c), DC.node_eq(b2, b), Equal.sym(Bool, True{}, SV.band(SV.eq(c2, c), DC.node_eq(b2, b)), eg))) : {LS.pairok(DC.lstored(ls, _, b)) == True{} : Bool}
      %GN.node_eq_ok(b2, b, LP2.band_r(SV.eq(c2, c), DC.node_eq(b2, b), Equal.sym(Bool, True{}, SV.band(SV.eq(c2, c), DC.node_eq(b2, b)), eg))) : {LS.pairok(DC.lstored(ls, c2, _)) == True{} : Bool}
      e0
    case False{}:
      ih(hne)

def pok_find(sc: List<&2, DC.Link>, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, h: PairL(sc, ls), hne: {lcons(DC.lstored(sc, c, b)) == True{} : Bool})
  -> {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}:
  match sc:
    case Nil{}:
      absurd({LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}, LP.tf(Equal.sym(Bool, False{}, True{}, hne)))
    case Con{DC.Link{+c2, +b2, +w, d}, +tl}:
      (e0, ht) = h
      pok_find.g(SV.band(SV.eq(c2, c), DC.node_eq(b2, b)), ls, c, b, c2, b2, w, tl, {==}, e0, hne, x => pok_find(tl, ls, c, b, ht, x))

def pairok_of.go(f: Bool, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, ef: {f == lcons(DC.lstored(ls, c, b)) : Bool}, h: PairL(ls, ls)) -> {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}:
  match f:
    case True{}:
      pok_find(ls, ls, c, b, h, Equal.sym(Bool, True{}, lcons(DC.lstored(ls, c, b)), ef))
    case False{}:
      pok_nil(DC.lstored(ls, c, b), Equal.sym(Bool, False{}, lcons(DC.lstored(ls, c, b)), ef))

# every pair's first two stored labels are independent
def pairok_of(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, h: PairL(ls, ls)) -> {LS.pairok(DC.lstored(ls, c, b)) == True{} : Bool}:
  pairok_of.go(lcons(DC.lstored(ls, c, b)), ls, c, b, {==}, h)

def lnzs.pick(g: Bool, +w: DR.Lab, +rest: List<&2, DR.Lab>, +nw: NZ.Nz(w), hr: LS.LNzs(rest)) -> LS.LNzs(DC.lstored.pick(g, w, rest)):
  match g:
    case True{}:
      (nw, hr)
    case False{}:
      hr

# the stored labels are nonzero
def lnzs_of(ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, h: RP.LsNz(ls)) -> LS.LNzs(DC.lstored(ls, c, b)):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c2, +b2, +w, +d}, +tl}:
      (nw, ht) = h
      lnzs.pick(SV.band(SV.eq(c2, c), DC.node_eq(b2, b)), w, DC.lstored(tl, c, b), nw, lnzs_of(tl, c, b, ht))

# Fresh links
# -----------

# a new link's label is outside its pair's stored span
def Fr(+ls: List<&2, DC.Link>, m: Maybe<&2, DC.Link>) -> Data:
  match m:
    case Some{DC.Link{+c, +b, +w, d}}:
      {DC.qspan(DC.lstored(ls, c, b), w) == False{} : Bool}
    case None{}:
      Unit

def FrW(+stored: List<&2, DR.Lab>, m: Maybe<&2, DR.Lab>) -> Data:
  match m:
    case Some{+w}:
      {DC.qspan(stored, w) == False{} : Bool}
    case None{}:
      Unit

def FrC(+stored: List<&2, DR.Lab>, m: Maybe<&2, DR.Lab>) -> Data:
  match m:
    case Some{+w}:
      {DC.qspan(stored, DR.Lab.conj(w)) == False{} : Bool}
    case None{}:
      Unit

def lkp_fr(f: Bool, +w: DR.Lab, +stored: List<&2, DR.Lab>, ef: {f == DC.qspan(stored, w) : Bool}, +rest: Maybe<&2, DR.Lab>, hr: FrW(stored, rest)) -> FrW(stored, DC.lk.pick(f, w, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      Equal.sym(Bool, False{}, DC.qspan(stored, w), ef)

def lkf_fr(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>) -> FrW(stored, DC.lk.first(ws, stored)):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +t}:
      lkp_fr(DC.qspan(stored, w), w, stored, {==}, DC.lk.first(t, stored), lkf_fr(t, stored))

def lkpc_fr(f: Bool, +w: DR.Lab, +stored: List<&2, DR.Lab>, ef: {f == DC.qspan(stored, DR.Lab.conj(w)) : Bool}, +rest: Maybe<&2, DR.Lab>, hr: FrC(stored, rest)) -> FrC(stored, DC.lk.pick(f, w, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      Equal.sym(Bool, False{}, DC.qspan(stored, DR.Lab.conj(w)), ef)

def lkrf_fr(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>) -> FrC(stored, DC.lk.r.first(ws, stored)):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +t}:
      lkpc_fr(DC.qspan(stored, DR.Lab.conj(w)), w, stored, {==}, DC.lk.r.first(t, stored), lkrf_fr(t, stored))

def lkm_fr(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node, hm: FrW(DC.lstored(DC.Sk.ls(s), c, b), m),
  +rest: Maybe<&2, DC.Link>, hr: Fr(DC.Sk.ls(s), rest)) -> Fr(DC.Sk.ls(s), DC.lk.mk(m, es, fs, t, DC.Sk.k(s), c, rep, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      hm

def lkci_fr(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>, hr: Fr(DC.Sk.ls(s), rest))
  -> Fr(DC.Sk.ls(s), DC.lk.c.if(f, es, fs, t, s, c, rep, b, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      lkm_fr(DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), es, fs, t, s, c, rep, b,
        lkf_fr(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), rest, hr)

def lkc_fr(bs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep) -> Fr(DC.Sk.ls(s), DC.lk.c(bs, es, fs, t, s, c, rep)):
  match bs:
    case Nil{}:
      Unit{}
    case Con{+b, +tl}:
      lkci_fr(DC.node_eq(b, DR.NSeg{c}), es, fs, t, s, c, rep, b, DC.lk.c(tl, es, fs, t, s, c, rep), lkc_fr(tl, es, fs, t, s, c, rep))

def lkrm_fr(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, hm: FrC(DC.lstored(DC.Sk.ls(s), c, r), m),
  +rest: Maybe<&2, DC.Link>, hr: Fr(DC.Sk.ls(s), rest)) -> Fr(DC.Sk.ls(s), DC.lk.r.mk(m, es, fs, t, s, c, r, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      hm

def lkr_fr(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat) -> Fr(DC.Sk.ls(s), DC.lk.r(rs, es, fs, t, s, c)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      lkrm_fr(DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), es, fs, t, s, c, r,
        lkrf_fr(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), DC.lk.r(tl, es, fs, t, s, c), lkr_fr(tl, es, fs, t, s, c))

def lfirst_fr(m: Maybe<&2, DC.Link>, +ls: List<&2, DC.Link>, hm: Fr(ls, m), +rest: Maybe<&2, DC.Link>, hr: Fr(ls, rest)) -> Fr(ls, DC.lfirst(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

def lksg_fr(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>,
  +rest: Maybe<&2, DC.Link>, hr: Fr(DC.Sk.ls(s), rest)) -> Fr(DC.Sk.ls(s), DC.lks.go(f, es, fs, t, s, c, rep, bs, rs, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      lfirst_fr(DC.lk.c(bs, es, fs, t, s, c, rep), DC.Sk.ls(s), lkc_fr(bs, es, fs, t, s, c, rep), DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest),
        lfirst_fr(DC.lk.r(rs, es, fs, t, s, c), DC.Sk.ls(s), lkr_fr(rs, es, fs, t, s, c), rest, hr))

# the link the search finds is fresh for its pair
def lks_fr(cids: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>)
  -> Fr(DC.Sk.ls(s), DC.lks(cids, es, fs, t, s, bs, rs)):
  match cids:
    case Nil{}:
      Unit{}
    case Con{+c, +tl}:
      lksg_fr(DC.fullc(es, DC.Sk.k(s), c), es, fs, t, s, c, DC.crep(es, fs, t, s, c), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs), lks_fr(tl, es, fs, t, s, bs, rs))
