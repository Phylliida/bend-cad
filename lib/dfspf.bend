# bend-cad: what a search for an augmenting path does (lib/struct.bend:
# dfs, search), for the solver's totality (ROADMAP: solve_total). Proofs
# only.
#
# A search from an unmatched equation e (in a matching vm whose matched
# equations are distinct, every variable it may try being below vm's
# length) either finds a path, and then its matching has distinct matched
# equations, one more of them, all among e and those of vm; or it fails
# with visited variables W that are distinct and matched in vm, such that
# every variable used by e or by the mate of a variable of W lies in W.
#
# Each level of the search tries one equation's variables. Its invariant
# (vis_ok) is about the variables visited so far and the base B (those
# visited before the level began): every visited variable outside B has
# had all of its mate's variables visited. The fuel suffices: each level
# visits a new matched variable, and there are at most as many as vm is long
# (the pigeonhole principle).

import Base
import ../spec/solve.bend as SV
import ../spec/ring.bend as E
import ./karith.bend as KA
import ./struct.bend as ST
import ./nat.bend as LN
import ./listpf.bend as L

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The invariants
# --------------

# every variable of each list in adj is below n
def adjb(adj: List<&2, List<&2, Nat>>, +n: Nat) -> Bool:
  match adj:
    case Nil{}:
      True{}
    case Con{h, t}:
      SV.band(SV.below(h, n), adjb(t, n))

# v's mate
def mate(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat) -> Nat:
  ST.look.of(ST.getm(vm, v))

# every variable of xs is in B, or its mate's variables are all in W
def closed(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +w: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+v, t}:
      SV.band(SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)), closed(vm, adj, b, w, t))

# the visited variables vis at fuel f, the level's base being b
def vis_ok(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>) -> Bool:
  SV.band(SV.distinct(vis), SV.band(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))))))

# a found path from e: the new matching vm2
def succ_ok(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))))

# a state of the level from e
def inv(+f: Nat, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, st: ST.DS) -> Bool:
  match st:
    case ST.DS{True{}, vm2, vis}:
      succ_ok(vm, e, vm2)
    case ST.DS{False{}, vm2, vis}:
      vis_ok(vm, adj, b, f, vis)

def ds.ok(st: ST.DS) -> Bool:
  match st:
    case ST.DS{ok, vm, vis}:
      ok

# what trying vs from the state st gives (r): a found path, or the state
# with every variable of vs visited, the state having been a failed one
def res(+f: Nat, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, +st: ST.DS, +vs: List<&2, Nat>, r: ST.DS) -> Bool:
  match r:
    case ST.DS{True{}, vm2, vis}:
      succ_ok(vm, e, vm2)
    case ST.DS{False{}, vm2, +vis}:
      SV.band(vis_ok(vm, adj, b, f, vis), SV.band(L.subl(vs, vis), SV.band(L.subl(ST.ds.vis(st), vis), SV.bnot(ds.ok(st)))))

# Small facts
# -----------

def eq_of(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {SV.eq(a, b) == True{} : Bool}:
  %e : {SV.eq(a, _) == True{} : Bool}
  L.eq_refl(a)

def isseen(c: ST.Cls) -> Bool:
  match c:
    case ST.Seen{}:
      True{}
    case ST.Free{}:
      False{}
    case ST.Mate{e}:
      False{}
    case ST.Done{}:
      False{}

def isfree(c: ST.Cls) -> Bool:
  match c:
    case ST.Seen{}:
      False{}
    case ST.Free{}:
      True{}
    case ST.Mate{e}:
      False{}
    case ST.Done{}:
      False{}

def ismate(c: ST.Cls) -> Bool:
  match c:
    case ST.Seen{}:
      False{}
    case ST.Free{}:
      False{}
    case ST.Mate{e}:
      True{}
    case ST.Done{}:
      False{}

def isdone(c: ST.Cls) -> Bool:
  match c:
    case ST.Seen{}:
      False{}
    case ST.Free{}:
      False{}
    case ST.Mate{e}:
      False{}
    case ST.Done{}:
      True{}

def mate.e(c: ST.Cls) -> Nat:
  match c:
    case ST.Seen{}:
      0n
    case ST.Free{}:
      0n
    case ST.Mate{e}:
      e
    case ST.Done{}:
      0n

# what the class of a variable says
def cls_seen(b: Bool, m: Maybe<&2, Nat>, h: {ST.Seen{} == ST.cls.of(b, m) : ST.Cls}) -> {b == True{} : Bool}:
  match b m:
    case True{} m:
      {==}
    case False{} None{}:
      absurd({False{} == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isseen, ST.Seen{}, ST.Free{}, h)))
    case False{} Some{x}:
      absurd({False{} == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isseen, ST.Seen{}, ST.Mate{x}, h)))

def cls_free_b(b: Bool, m: Maybe<&2, Nat>, h: {ST.Free{} == ST.cls.of(b, m) : ST.Cls}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isfree, ST.Free{}, ST.Seen{}, h)))
    case False{}:
      {==}

def cls_free_m(b: Bool, m: Maybe<&2, Nat>, h: {ST.Free{} == ST.cls.of(b, m) : ST.Cls}) -> {m == None{} : Maybe<&2, Nat>}:
  match b m:
    case True{} m:
      absurd({m == None{} : Maybe<&2, Nat>}, L.tf(Equal.cong(ST.Cls, Bool, isfree, ST.Free{}, ST.Seen{}, h)))
    case False{} None{}:
      {==}
    case False{} Some{x}:
      absurd({Some{x} == None{} : Maybe<&2, Nat>}, L.tf(Equal.cong(ST.Cls, Bool, isfree, ST.Free{}, ST.Mate{x}, h)))

def cls_mate_b(b: Bool, m: Maybe<&2, Nat>, +e: Nat, h: {ST.Mate{e} == ST.cls.of(b, m) : ST.Cls}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, ismate, ST.Mate{e}, ST.Seen{}, h)))
    case False{}:
      {==}

def cls_mate_m(b: Bool, m: Maybe<&2, Nat>, +e: Nat, h: {ST.Mate{e} == ST.cls.of(b, m) : ST.Cls}) -> {m == Some{e} : Maybe<&2, Nat>}:
  match b m:
    case True{} m:
      absurd({m == Some{e} : Maybe<&2, Nat>}, L.tf(Equal.cong(ST.Cls, Bool, ismate, ST.Mate{e}, ST.Seen{}, h)))
    case False{} None{}:
      absurd({None{} == Some{e} : Maybe<&2, Nat>}, L.tf(Equal.cong(ST.Cls, Bool, ismate, ST.Mate{e}, ST.Free{}, h)))
    case False{} Some{+x}:
      %Equal.sym(Nat, e, x, Equal.cong(ST.Cls, Nat, mate.e, ST.Mate{e}, ST.Mate{x}, h)) : {Some{x} == Some{_} : Maybe<&2, Nat>}
      {==}

def cls_done(b: Bool, m: Maybe<&2, Nat>, h: {ST.Done{} == ST.cls.of(b, m) : ST.Cls}) -> Empty:
  match b m:
    case True{} m:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Seen{}, h))
    case False{} None{}:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Free{}, h))
    case False{} Some{x}:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Mate{x}, h))

def done_not(c: ST.Cls, h: {c == ST.Done{} : ST.Cls}, hn: {isdone(c) == False{} : Bool}) -> Empty:
  match c:
    case ST.Seen{}:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Seen{}, Equal.sym(ST.Cls, ST.Seen{}, ST.Done{}, h)))
    case ST.Free{}:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Free{}, Equal.sym(ST.Cls, ST.Free{}, ST.Done{}, h)))
    case ST.Mate{x}:
      L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Mate{x}, Equal.sym(ST.Cls, ST.Mate{x}, ST.Done{}, h)))
    case ST.Done{}:
      L.tf(hn)

# The fuel: at most as many visited variables as vm is long
# ----------------------------------------------------------

# the indices of vm, from k
def ix(vm: List<&2, Maybe<&2, Nat>>, +k: Nat) -> List<&2, Nat>:
  match vm:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{k, ix(t, 1n+k)}

def ix_len(vm: List<&2, Maybe<&2, Nat>>, +k: Nat) -> {SV.len(ix(vm, k)) == L.mlen(vm) : Nat}:
  match vm:
    case Nil{}:
      {==}
    case Con{m, +t}:
      %Equal.sym(Nat, SV.len(ix(t, 1n+k)), L.mlen(t), ix_len(t, 1n+k)) : {1n+_ == 1n+L.mlen(t) : Nat}
      {==}

def ix_mem(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +k: Nat, h: {L.issome(ST.getm(vm, v)) == True{} : Bool}) -> {SV.mem(Nat.add(k, v), ix(vm, k)) == True{} : Bool}:
  match vm v:
    case Nil{} v:
      absurd({SV.mem(Nat.add(k, v), Nil{}) == True{} : Bool}, L.ft(h))
    case Con{m, +t} 0n:
      %LN.add_zero(k) : {SV.mem(_, Con{k, ix(t, 1n+k)}) == True{} : Bool}
      L.mem_hd(k, ix(t, 1n+k))
    case Con{m, +t} 1n++j:
      %LN.add_succ(k, j) : {SV.mem(_, Con{k, ix(t, 1n+k)}) == True{} : Bool}
      L.mem_tl(1n+Nat.add(k, j), k, ix(t, 1n+k), ix_mem(t, j, 1n+k, h))

def allm_ix(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +h: {L.allm(vm, xs) == True{} : Bool}) -> {L.subl(xs, ix(vm, 0n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, ix(vm, 0n), ix_mem(vm, x, 0n, L.band_l(L.issome(ST.getm(vm, x)), L.allm(vm, t), h)), allm_ix(vm, t, L.band_r(L.issome(ST.getm(vm, x)), L.allm(vm, t), h)))

# distinct matched variables: no more than vm's length
def vis_pig(+vm: List<&2, Maybe<&2, Nat>>, +xs: List<&2, Nat>, d: {SV.distinct(xs) == True{} : Bool}, h: {L.allm(vm, xs) == True{} : Bool}) -> {KA.natle(SV.len(xs), L.mlen(vm)) == True{} : Bool}:
  %ix_len(vm, 0n) : {KA.natle(SV.len(xs), _) == True{} : Bool}
  L.pig(xs, ix(vm, 0n), d, allm_ix(vm, xs, h))

# Matched variables across a change of v
# --------------------------------------

def allm_set(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Maybe<&2, Nat>, xs: List<&2, Nat>, +h: {L.allm(vm, xs) == True{} : Bool}, +hn: {SV.mem(v, xs) == False{} : Bool}) -> {L.allm(ST.setm(vm, v, x), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.band_i(L.issome(ST.getm(ST.setm(vm, v, x), w)), L.allm(ST.setm(vm, v, x), t), %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(vm, v, x), w), ST.getm(vm, w), L.getm_set_ne(vm, v, w, x, %L.eq_sym(v, w) : {_ == False{} : Bool}
        L.bor_fl(SV.eq(v, w), SV.mem(v, t), hn))) : {L.issome(_) == True{} : Bool}
        L.band_l(L.issome(ST.getm(vm, w)), L.allm(vm, t), h), allm_set(vm, v, x, t, L.band_r(L.issome(ST.getm(vm, w)), L.allm(vm, t), h), L.bor_fr(SV.eq(v, w), SV.mem(v, t), hn)))

def allm_unset.go(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Maybe<&2, Nat>, +w: Nat, c: Bool, e: {SV.eq(w, v) == c : Bool}, hw: {L.issome(ST.getm(ST.setm(vm, v, x), w)) == True{} : Bool}, hv: {L.issome(ST.getm(vm, v)) == True{} : Bool}) -> {L.issome(ST.getm(vm, w)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, w, v, L.eq_ok(w, v, e)) : {L.issome(ST.getm(vm, _)) == True{} : Bool}
      hv
    case False{}:
      %L.getm_set_ne(vm, v, w, x, e) : {L.issome(_) == True{} : Bool}
      hw

# the variables of xs matched once v is changed, v having been matched
def allm_unset(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +x: Maybe<&2, Nat>, xs: List<&2, Nat>, +h: {L.allm(ST.setm(vm, v, x), xs) == True{} : Bool}, +hv: {L.issome(ST.getm(vm, v)) == True{} : Bool}) -> {L.allm(vm, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      L.band_i(L.issome(ST.getm(vm, w)), L.allm(vm, t), allm_unset.go(vm, v, x, w, SV.eq(w, v), {==}, L.band_l(L.issome(ST.getm(ST.setm(vm, v, x), w)), L.allm(ST.setm(vm, v, x), t), h), hv), allm_unset(vm, v, x, t, L.band_r(L.issome(ST.getm(ST.setm(vm, v, x), w)), L.allm(ST.setm(vm, v, x), t), h), hv))

# Closure
# -------

def closed_base(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +w: List<&2, Nat>, xs: List<&2, Nat>, +h: {L.subl(xs, b) == True{} : Bool}) -> {closed(vm, adj, b, w, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      L.band_i(SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)), closed(vm, adj, b, w, t), L.bor_l(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w), L.subl_hd(v, t, b, h)), closed_base(vm, adj, b, w, t, L.subl_tl(v, t, b, h)))

def closed_mem.go(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +w: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +v: Nat, c: Bool, e: {SV.eq(v, x) == c : Bool}, h: {closed(vm, adj, b, w, Con{x, t}) == True{} : Bool}, hv: {SV.bor(c, SV.mem(v, t)) == True{} : Bool}, ih: {closed(vm, adj, b, w, t) == True{} : Bool} -> {SV.mem(v, t) == True{} : Bool} -> {SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)) == True{} : Bool}) -> {SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, v, x, L.eq_ok(v, x, e)) : {SV.bor(SV.mem(_, b), L.subl(ST.nthl(adj, mate(vm, _)), w)) == True{} : Bool}
      L.band_l(SV.bor(SV.mem(x, b), L.subl(ST.nthl(adj, mate(vm, x)), w)), closed(vm, adj, b, w, t), h)
    case False{}:
      ih(L.band_r(SV.bor(SV.mem(x, b), L.subl(ST.nthl(adj, mate(vm, x)), w)), closed(vm, adj, b, w, t), h), hv)

# the closure at one visited variable
def closed_mem(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +w: List<&2, Nat>, xs: List<&2, Nat>, +v: Nat, h: {closed(vm, adj, b, w, xs) == True{} : Bool}, hv: {SV.mem(v, xs) == True{} : Bool}) -> {SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, mate(vm, v)), w)) == True{} : Bool}, L.ft(hv))
    case Con{+x, +t}:
      closed_mem.go(vm, adj, b, w, x, t, v, SV.eq(v, x), {==}, h, hv, q => r => closed_mem(vm, adj, b, w, t, v, q, r))

def or_subl(a: Bool, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>, h: {SV.bor(a, L.subl(xs, ys)) == True{} : Bool}, hs: {L.subl(ys, zs) == True{} : Bool}) -> {SV.bor(a, L.subl(xs, zs)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.subl_trans(xs, ys, zs, h, hs)

def below_hd(+v: Nat, +t: List<&2, Nat>, +n: Nat, h: {SV.below(Con{v, t}, n) == True{} : Bool}) -> {KA.natle(1n+v, n) == True{} : Bool}:
  %L.lt_sv(v, n) : {_ == True{} : Bool}
  L.band_l(SV.lt(v, n), SV.below(t, n), h)

def below_tl(+v: Nat, +t: List<&2, Nat>, +n: Nat, h: {SV.below(Con{v, t}, n) == True{} : Bool}) -> {SV.below(t, n) == True{} : Bool}:
  L.band_r(SV.lt(v, n), SV.below(t, n), h)

def nthl_below(adj: List<&2, List<&2, Nat>>, k: Nat, +n: Nat, h: {adjb(adj, n) == True{} : Bool}) -> {SV.below(ST.nthl(adj, k), n) == True{} : Bool}:
  match adj k:
    case Nil{} k:
      {==}
    case Con{+l, +t} 0n:
      L.band_l(SV.below(l, n), adjb(t, n), h)
    case Con{+l, +t} 1n+j:
      nthl_below(t, j, n, L.band_r(SV.below(l, n), adjb(t, n), h))

# From a level's closure to its caller's: the level from e2 was entered
# through v (matched to e2 in vm, set to e for the level), the caller had
# visited vis, and the level ended with vis2.

def closed_tr.go2(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +e: Nat, +vis: List<&2, Nat>, +vis2: List<&2, Nat>, +w: Nat, c: Bool, eq2: {SV.mem(w, vis) == c : Bool}, +hne: {SV.eq(w, v) == False{} : Bool}, hin: {SV.bor(SV.mem(w, Con{v, vis}), L.subl(ST.nthl(adj, mate(ST.setm(vm, v, Some{e}), w)), vis2)) == True{} : Bool}, hout: {closed(vm, adj, b, vis, vis) == True{} : Bool}, hsub: {L.subl(vis, vis2) == True{} : Bool}) -> {SV.bor(SV.mem(w, b), L.subl(ST.nthl(adj, mate(vm, w)), vis2)) == True{} : Bool}:
  match c:
    case True{}:
      or_subl(SV.mem(w, b), ST.nthl(adj, mate(vm, w)), vis, vis2, closed_mem(vm, adj, b, vis, vis, w, hout, eq2), hsub)
    case False{}:
      L.bor_r(SV.mem(w, b), L.subl(ST.nthl(adj, mate(vm, w)), vis2), %L.getm_set_ne(vm, v, w, Some{e}, hne) : {L.subl(ST.nthl(adj, ST.look.of(_)), vis2) == True{} : Bool}
        L.bor_rf(SV.mem(w, Con{v, vis}), L.subl(ST.nthl(adj, mate(ST.setm(vm, v, Some{e}), w)), vis2), hin, L.bor_f(SV.eq(w, v), SV.mem(w, vis), hne, eq2)))

def closed_tr.go(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +e: Nat, +e2: Nat, +vis: List<&2, Nat>, +vis2: List<&2, Nat>, +w: Nat, c: Bool, eq1: {SV.eq(w, v) == c : Bool}, hin: {SV.bor(SV.mem(w, Con{v, vis}), L.subl(ST.nthl(adj, mate(ST.setm(vm, v, Some{e}), w)), vis2)) == True{} : Bool}, hout: {closed(vm, adj, b, vis, vis) == True{} : Bool}, he2: {L.subl(ST.nthl(adj, e2), vis2) == True{} : Bool}, hsub: {L.subl(vis, vis2) == True{} : Bool}, hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}) -> {SV.bor(SV.mem(w, b), L.subl(ST.nthl(adj, mate(vm, w)), vis2)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, w, v, L.eq_ok(w, v, eq1)) : {SV.bor(SV.mem(_, b), L.subl(ST.nthl(adj, mate(vm, _)), vis2)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Nat>, ST.getm(vm, v), Some{e2}, hs) : {SV.bor(SV.mem(v, b), L.subl(ST.nthl(adj, ST.look.of(_)), vis2)) == True{} : Bool}
      L.bor_r(SV.mem(v, b), L.subl(ST.nthl(adj, e2), vis2), he2)
    case False{}:
      closed_tr.go2(vm, adj, b, v, e, vis, vis2, w, SV.mem(w, vis), {==}, eq1, hin, hout, hsub)

def closed_tr(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +e: Nat, +e2: Nat, +vis: List<&2, Nat>, +vis2: List<&2, Nat>, xs: List<&2, Nat>, +hin: {closed(ST.setm(vm, v, Some{e}), adj, Con{v, vis}, vis2, xs) == True{} : Bool}, +hout: {closed(vm, adj, b, vis, vis) == True{} : Bool}, +he2: {L.subl(ST.nthl(adj, e2), vis2) == True{} : Bool}, +hsub: {L.subl(vis, vis2) == True{} : Bool}, +hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}) -> {closed(vm, adj, b, vis2, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +vm2 = ST.setm(vm, v, Some{e})
      L.band_i(SV.bor(SV.mem(w, b), L.subl(ST.nthl(adj, mate(vm, w)), vis2)), closed(vm, adj, b, vis2, t), closed_tr.go(vm, adj, b, v, e, e2, vis, vis2, w, SV.eq(w, v), {==}, L.band_l(SV.bor(SV.mem(w, Con{v, vis}), L.subl(ST.nthl(adj, mate(vm2, w)), vis2)), closed(vm2, adj, Con{v, vis}, vis2, t), hin), hout, he2, hsub, hs), closed_tr(vm, adj, b, v, e, e2, vis, vis2, t, L.band_r(SV.bor(SV.mem(w, Con{v, vis}), L.subl(ST.nthl(adj, mate(vm2, w)), vis2)), closed(vm2, adj, Con{v, vis}, vis2, t), hin), hout, he2, hsub, hs))

# The invariants' parts
# ---------------------

def vo_d(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {SV.distinct(vis) == True{} : Bool}:
  L.band_l(SV.distinct(vis), SV.band(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))))), h)

def vo_r1(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {SV.band(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))))) == True{} : Bool}:
  L.band_r(SV.distinct(vis), SV.band(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))))), h)

def vo_a(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {L.allm(vm, vis) == True{} : Bool}:
  L.band_l(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))))), vo_r1(vm, adj, b, f, vis, h))

def vo_r2(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))))) == True{} : Bool}:
  L.band_r(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))))), vo_r1(vm, adj, b, f, vis, h))

def vo_s(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {L.subl(b, vis) == True{} : Bool}:
  L.band_l(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))), vo_r2(vm, adj, b, f, vis, h))

def vo_r3(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))) == True{} : Bool}:
  L.band_r(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))), vo_r2(vm, adj, b, f, vis, h))

def vo_c(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {closed(vm, adj, b, vis, vis) == True{} : Bool}:
  L.band_l(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))), vo_r3(vm, adj, b, f, vis, h))

def vo_f(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, h: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))) == True{} : Bool}:
  L.band_r(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))), vo_r3(vm, adj, b, f, vis, h))

def vo_mk(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +f: Nat, +vis: List<&2, Nat>, hd: {SV.distinct(vis) == True{} : Bool}, ha: {L.allm(vm, vis) == True{} : Bool}, hs: {L.subl(b, vis) == True{} : Bool}, hc: {closed(vm, adj, b, vis, vis) == True{} : Bool}, hf: {KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))) == True{} : Bool}) -> {vis_ok(vm, adj, b, f, vis) == True{} : Bool}:
  L.band_i(SV.distinct(vis), SV.band(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))))), hd, L.band_i(L.allm(vm, vis), SV.band(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))))), ha, L.band_i(L.subl(b, vis), SV.band(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis)))), hs, L.band_i(closed(vm, adj, b, vis, vis), KA.natle(1n+L.mlen(vm), Nat.add(f, SV.len(vis))), hc, hf))))

def so_d(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {SV.distinct(ST.somes(vm2)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))), h)

def so_r1(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))) == True{} : Bool}:
  L.band_r(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))), h)

def so_n(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {SV.len(ST.somes(vm2)) == 1n+SV.len(ST.somes(vm)) : Nat}:
  L.eq_ok(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm)), L.band_l(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))), so_r1(vm, e, vm2, h)))

def so_r2(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))) == True{} : Bool}:
  L.band_r(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))), so_r1(vm, e, vm2, h))

def so_s(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)), so_r2(vm, e, vm2, h))

def so_m(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, h: {succ_ok(vm, e, vm2) == True{} : Bool}) -> {L.mlen(vm2) == L.mlen(vm) : Nat}:
  L.eq_ok(L.mlen(vm2), L.mlen(vm), L.band_r(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)), so_r2(vm, e, vm2, h)))

def so_mk(+vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +vm2: List<&2, Maybe<&2, Nat>>, hd: {SV.distinct(ST.somes(vm2)) == True{} : Bool}, hn: {SV.len(ST.somes(vm2)) == 1n+SV.len(ST.somes(vm)) : Nat}, hs: {L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}) == True{} : Bool}, hm: {L.mlen(vm2) == L.mlen(vm) : Nat}) -> {succ_ok(vm, e, vm2) == True{} : Bool}:
  L.band_i(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))), hd, L.band_i(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))), eq_of(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm)), hn), L.band_i(L.subl(ST.somes(vm2), Con{e, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)), hs, eq_of(L.mlen(vm2), L.mlen(vm), hm))))

# One level, through its caller's eyes
# ------------------------------------

# what the caller (which visited vis, then v) learns from the level's
# failed result: v and vis were visited
def extra(+v: Nat, +vis: List<&2, Nat>, r: ST.DS) -> Bool:
  match r:
    case ST.DS{True{}, m, x}:
      True{}
    case ST.DS{False{}, m, +vis2}:
      SV.band(SV.mem(v, vis2), L.subl(vis, vis2))

def sub2(+v: Nat, +vis: List<&2, Nat>, +vis2: List<&2, Nat>, h: {L.subl(Con{v, vis}, vis2) == True{} : Bool}) -> {L.subl(vis, vis2) == True{} : Bool}:
  L.subl_trans(vis, Con{v, vis}, vis2, L.subl_cons_r(vis, v, vis, L.subl_refl(vis)), h)

def tr_succ(+e: Nat, +e2: Nat, +vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +vm3: List<&2, Maybe<&2, Nat>>, +hr: {succ_ok(ST.setm(vm, v, Some{e}), e2, vm3) == True{} : Bool}, +hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}) -> {succ_ok(vm, e, vm3) == True{} : Bool}:
  +vm2 = ST.setm(vm, v, Some{e})
  so_mk(vm, e, vm3, so_d(vm2, e2, vm3, hr), %L.set_some_len(vm, v, e, e2, hs) : {SV.len(ST.somes(vm3)) == 1n+_ : Nat}
    so_n(vm2, e2, vm3, hr), L.subl_trans(ST.somes(vm3), Con{e2, ST.somes(vm2)}, Con{e, ST.somes(vm)}, so_s(vm2, e2, vm3, hr), L.subl_con(e2, ST.somes(vm2), Con{e, ST.somes(vm)}, L.mem_tl(e2, e, ST.somes(vm), L.some_mem(vm, v, e2, hs)), L.set_subl(vm, v, e))), %L.mlen_set(vm, v, Some{e}) : {L.mlen(vm3) == _ : Nat}
    so_m(vm2, e2, vm3, hr))

# the level from e2 (entered through v, matched to e2, set to e) ended
# with r: the caller's state r is sound, and v and vis were visited
def tr(+g: Nat, +e: Nat, +e2: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +vis: List<&2, Nat>, r: ST.DS, +hr: {res(g, e2, adj, ST.setm(vm, v, Some{e}), Con{v, vis}, ST.DS{False{}, vm, Con{v, vis}}, ST.nthl(adj, e2), r) == True{} : Bool}, +hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}, +ho: {vis_ok(vm, adj, b, 1n+g, vis) == True{} : Bool}) -> {SV.band(inv(1n+g, e, adj, vm, b, r), extra(v, vis, r)) == True{} : Bool}:
  match r:
    case ST.DS{True{}, +vm3, x}:
      L.band_i(succ_ok(vm, e, vm3), True{}, tr_succ(e, e2, vm, v, vm3, hr, hs), {==})
    case ST.DS{False{}, m, +vis2}:
      +vm2 = ST.setm(vm, v, Some{e})
      +hv = vo_r1(vm2, adj, Con{v, vis}, g, vis2, L.band_l(vis_ok(vm2, adj, Con{v, vis}, g, vis2), SV.band(L.subl(ST.nthl(adj, e2), vis2), SV.band(L.subl(Con{v, vis}, vis2), True{})), hr))
      +hq = L.band_r(vis_ok(vm2, adj, Con{v, vis}, g, vis2), SV.band(L.subl(ST.nthl(adj, e2), vis2), SV.band(L.subl(Con{v, vis}, vis2), True{})), hr)
      +hi = L.band_l(vis_ok(vm2, adj, Con{v, vis}, g, vis2), SV.band(L.subl(ST.nthl(adj, e2), vis2), SV.band(L.subl(Con{v, vis}, vis2), True{})), hr)
      +he2 = L.band_l(L.subl(ST.nthl(adj, e2), vis2), SV.band(L.subl(Con{v, vis}, vis2), True{}), hq)
      +hvv = L.band_l(L.subl(Con{v, vis}, vis2), True{}, L.band_r(L.subl(ST.nthl(adj, e2), vis2), SV.band(L.subl(Con{v, vis}, vis2), True{}), hq))
      +hsub = sub2(v, vis, vis2, hvv)
      L.band_i(vis_ok(vm, adj, b, 1n+g, vis2), SV.band(SV.mem(v, vis2), L.subl(vis, vis2)), vo_mk(vm, adj, b, 1n+g, vis2, vo_d(vm2, adj, Con{v, vis}, g, vis2, hi), allm_unset(vm, v, Some{e}, vis2, vo_a(vm2, adj, Con{v, vis}, g, vis2, hi), %Equal.sym(Maybe<&2, Nat>, ST.getm(vm, v), Some{e2}, hs) : {L.issome(_) == True{} : Bool}
        {==}), L.subl_trans(b, vis, vis2, vo_s(vm, adj, b, 1n+g, vis, ho), hsub), closed_tr(vm, adj, b, v, e, e2, vis, vis2, vis2, vo_c(vm2, adj, Con{v, vis}, g, vis2, hi), vo_c(vm, adj, b, 1n+g, vis, ho), he2, hsub, hs), L.le_succ(1n+L.mlen(vm), Nat.add(g, SV.len(vis2)), %L.mlen_set(vm, v, Some{e}) : {KA.natle(1n+_, Nat.add(g, SV.len(vis2))) == True{} : Bool}
        vo_f(vm2, adj, Con{v, vis}, g, vis2, hi))), L.band_i(SV.mem(v, vis2), L.subl(vis, vis2), L.subl_hd(v, vis, vis2, hvv), hsub))

# the continuation after the level ended with r: trying v :: rest
def fin(+f: Nat, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +rest: List<&2, Nat>, +m0: List<&2, Maybe<&2, Nat>>, +vis: List<&2, Nat>, r: ST.DS, fr: ST.DS, +hx: {extra(v, vis, r) == True{} : Bool}, +hc: {res(f, e, adj, vm, b, r, rest, fr) == True{} : Bool}) -> {res(f, e, adj, vm, b, ST.DS{False{}, m0, vis}, Con{v, rest}, fr) == True{} : Bool}:
  match r fr:
    case r ST.DS{True{}, m, x}:
      hc
    case ST.DS{True{}, mr, +visr} ST.DS{False{}, m, +visf}:
      absurd({res(f, e, adj, vm, b, ST.DS{False{}, m0, vis}, Con{v, rest}, ST.DS{False{}, m, visf}) == True{} : Bool}, L.ft(L.band_r(L.subl(visr, visf), False{}, L.band_r(L.subl(rest, visf), SV.band(L.subl(visr, visf), False{}), L.band_r(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(rest, visf), SV.band(L.subl(visr, visf), False{})), hc)))))
    case ST.DS{False{}, mr, +visr} ST.DS{False{}, m, +visf}:
      +hq = L.band_r(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(rest, visf), SV.band(L.subl(visr, visf), True{})), hc)
      +hrf = L.band_l(L.subl(visr, visf), True{}, L.band_r(L.subl(rest, visf), SV.band(L.subl(visr, visf), True{}), hq))
      L.band_i(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(Con{v, rest}, visf), SV.band(L.subl(vis, visf), True{})), L.band_l(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(rest, visf), SV.band(L.subl(visr, visf), True{})), hc), L.band_i(L.subl(Con{v, rest}, visf), SV.band(L.subl(vis, visf), True{}), L.subl_con(v, rest, visf, L.subl_mem(v, visr, visf, L.band_l(SV.mem(v, visr), L.subl(vis, visr), hx), hrf), L.band_l(L.subl(rest, visf), SV.band(L.subl(visr, visf), True{}), hq)), L.band_i(L.subl(vis, visf), True{}, L.subl_trans(vis, visr, visf, L.band_r(SV.mem(v, visr), L.subl(vis, visr), hx), hrf), {==})))

def hq_tail(+rest: List<&2, Nat>, +vis: List<&2, Nat>, +visf: List<&2, Nat>, h: {SV.band(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{})) == True{} : Bool}) -> {SV.band(L.subl(vis, visf), True{}) == True{} : Bool}:
  L.band_r(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{}), h)

# v was visited before: trying v :: rest is trying rest
def seen_fix(+f: Nat, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, +v: Nat, +rest: List<&2, Nat>, +m0: List<&2, Maybe<&2, Nat>>, +vis: List<&2, Nat>, hv: {SV.mem(v, vis) == True{} : Bool}, fr: ST.DS, +hc: {res(f, e, adj, vm, b, ST.DS{False{}, m0, vis}, rest, fr) == True{} : Bool}) -> {res(f, e, adj, vm, b, ST.DS{False{}, m0, vis}, Con{v, rest}, fr) == True{} : Bool}:
  match fr:
    case ST.DS{True{}, m, x}:
      hc
    case ST.DS{False{}, m, +visf}:
      +hq = L.band_r(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{})), hc)
      +hvf = L.band_l(L.subl(vis, visf), True{}, L.band_r(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{}), hq))
      L.band_i(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(Con{v, rest}, visf), SV.band(L.subl(vis, visf), True{})), L.band_l(vis_ok(vm, adj, b, f, visf), SV.band(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{})), hc), L.band_i(L.subl(Con{v, rest}, visf), SV.band(L.subl(vis, visf), True{}), L.subl_con(v, rest, visf, L.subl_mem(v, vis, visf, hv, hvf), L.band_l(L.subl(rest, visf), SV.band(L.subl(vis, visf), True{}), hq)), hq_tail(rest, vis, visf, hq)))

# nothing left to try
def nil_res(+f: Nat, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +b: List<&2, Nat>, +m0: List<&2, Maybe<&2, Nat>>, +vis: List<&2, Nat>, hi: {vis_ok(vm, adj, b, f, vis) == True{} : Bool}) -> {res(f, e, adj, vm, b, ST.DS{False{}, m0, vis}, Nil{}, ST.DS{False{}, m0, vis}) == True{} : Bool}:
  L.band_i(vis_ok(vm, adj, b, f, vis), SV.band(L.subl(Nil{}, vis), SV.band(L.subl(vis, vis), True{})), hi, L.band_i(L.subl(vis, vis), True{}, L.subl_refl(vis), {==}))

# a free variable v for the unmatched e
def free_res(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +e: Nat, hn: {ST.getm(vm, v) == None{} : Maybe<&2, Nat>}, hl: {KA.natle(1n+v, L.mlen(vm)) == True{} : Bool}, +h1: {SV.mem(e, ST.somes(vm)) == False{} : Bool}, +h2: {SV.distinct(ST.somes(vm)) == True{} : Bool}) -> {succ_ok(vm, e, ST.setm(vm, v, Some{e})) == True{} : Bool}:
  so_mk(vm, e, ST.setm(vm, v, Some{e}), L.set_dist(vm, v, e, h2, h1), L.set_none_len(vm, v, e, hn, hl), L.set_subl(vm, v, e), L.mlen_set(vm, v, Some{e}))

# out of fuel with a matched variable left: impossible
def no_fuel(+vm: List<&2, Maybe<&2, Nat>>, +adj: List<&2, List<&2, Nat>>, +b: List<&2, Nat>, +vis: List<&2, Nat>, +hi: {vis_ok(vm, adj, b, 0n, vis) == True{} : Bool}) -> Empty:
  L.lt_irr(L.mlen(vm), L.le_trans(1n+L.mlen(vm), SV.len(vis), L.mlen(vm), vo_f(vm, adj, b, 0n, vis, hi), vis_pig(vm, vis, vo_d(vm, adj, b, 0n, vis, hi), vo_a(vm, adj, b, 0n, vis, hi))))

# Entering a level through v
# --------------------------

def seen_mem(+v: Nat, +vis: List<&2, Nat>, m: Maybe<&2, Nat>, hc: {ST.Seen{} == ST.cls.of(ST.mem(v, vis), m) : ST.Cls}) -> {SV.mem(v, vis) == True{} : Bool}:
  %Equal.sym(Bool, SV.mem(v, vis), ST.mem(v, vis), L.mem_sv(v, vis)) : {_ == True{} : Bool}
  cls_seen(ST.mem(v, vis), m, hc)

def mate_mem(+v: Nat, +vis: List<&2, Nat>, m: Maybe<&2, Nat>, +e2: Nat, hc: {ST.Mate{e2} == ST.cls.of(ST.mem(v, vis), m) : ST.Cls}) -> {SV.mem(v, vis) == False{} : Bool}:
  %Equal.sym(Bool, SV.mem(v, vis), ST.mem(v, vis), L.mem_sv(v, vis)) : {_ == False{} : Bool}
  cls_mate_b(ST.mem(v, vis), m, e2, hc)

def h3_in(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +e: Nat, +e2: Nat, h4: {adjb(adj, L.mlen(vm)) == True{} : Bool}) -> {SV.below(ST.nthl(adj, e2), L.mlen(ST.setm(vm, v, Some{e}))) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(ST.setm(vm, v, Some{e})), L.mlen(vm), L.mlen_set(vm, v, Some{e})) : {SV.below(ST.nthl(adj, e2), _) == True{} : Bool}
  nthl_below(adj, e2, L.mlen(vm), h4)

def h4_in(+adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +e: Nat, h4: {adjb(adj, L.mlen(vm)) == True{} : Bool}) -> {adjb(adj, L.mlen(ST.setm(vm, v, Some{e}))) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(ST.setm(vm, v, Some{e})), L.mlen(vm), L.mlen_set(vm, v, Some{e})) : {adjb(adj, _) == True{} : Bool}
  h4

def isv(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +e: Nat, hl: {KA.natle(1n+v, L.mlen(vm)) == True{} : Bool}) -> {L.issome(ST.getm(ST.setm(vm, v, Some{e}), v)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, ST.getm(ST.setm(vm, v, Some{e}), v), Some{e}, L.getm_set_eq(vm, v, Some{e}, hl)) : {L.issome(_) == True{} : Bool}
  {==}

def fuel_in(+vm: List<&2, Maybe<&2, Nat>>, +v: Nat, +e: Nat, +g: Nat, +vis: List<&2, Nat>, h: {KA.natle(1n+L.mlen(vm), 1n+Nat.add(g, SV.len(vis))) == True{} : Bool}) -> {KA.natle(1n+L.mlen(ST.setm(vm, v, Some{e})), Nat.add(g, 1n+SV.len(vis))) == True{} : Bool}:
  %Equal.sym(Nat, L.mlen(ST.setm(vm, v, Some{e})), L.mlen(vm), L.mlen_set(vm, v, Some{e})) : {KA.natle(1n+_, Nat.add(g, 1n+SV.len(vis))) == True{} : Bool}
  %LN.add_succ(g, SV.len(vis)) : {KA.natle(1n+L.mlen(vm), _) == True{} : Bool}
  h

# The search
# ----------

# trying vs (c: how the first stands) for e, unmatched in vm, from the
# state st of the level whose base is b
def dfs_ok(f: Nat, vs: List<&2, Nat>, c: ST.Cls, +e: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +st: ST.DS, +b: List<&2, Nat>, +hc: {c == ST.cnext(st, vm, vs) : ST.Cls}, +h1: {SV.mem(e, ST.somes(vm)) == False{} : Bool}, +h2: {SV.distinct(ST.somes(vm)) == True{} : Bool}, +h3: {SV.below(vs, L.mlen(vm)) == True{} : Bool}, +h4: {adjb(adj, L.mlen(vm)) == True{} : Bool}, +hi: {inv(f, e, adj, vm, b, st) == True{} : Bool}) -> {res(f, e, adj, vm, b, st, vs, ST.dfs(f, vs, c, e, adj, vm, st)) == True{} : Bool}:
  match f vs c st:
    case 0n Nil{} ST.Seen{} ST.DS{True{}, +m, +vis}:
      hi
    case 0n Nil{} ST.Seen{} ST.DS{False{}, +m, +vis}:
      nil_res(0n, e, adj, vm, b, m, vis, hi)
    case 0n Nil{} ST.Free{} ST.DS{True{}, +m, +vis}:
      hi
    case 0n Nil{} ST.Free{} ST.DS{False{}, +m, +vis}:
      nil_res(0n, e, adj, vm, b, m, vis, hi)
    case 0n Nil{} ST.Mate{+e2} ST.DS{True{}, +m, +vis}:
      hi
    case 0n Nil{} ST.Mate{+e2} ST.DS{False{}, +m, +vis}:
      nil_res(0n, e, adj, vm, b, m, vis, hi)
    case 0n Nil{} ST.Done{} ST.DS{True{}, +m, +vis}:
      hi
    case 0n Nil{} ST.Done{} ST.DS{False{}, +m, +vis}:
      nil_res(0n, e, adj, vm, b, m, vis, hi)
    case 0n Con{+v, +rest} ST.Seen{} ST.DS{True{}, +m, +vis}:
      absurd({res(0n, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(0n, Con{v, rest}, ST.Seen{}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Seen{}, Equal.sym(ST.Cls, ST.Seen{}, ST.Done{}, hc))))
    case 0n Con{+v, +rest} ST.Seen{} ST.DS{False{}, +m, +vis}:
      seen_fix(0n, e, adj, vm, b, v, rest, m, vis, seen_mem(v, vis, ST.getm(vm, v), hc), ST.dfs(0n, rest, ST.cls(vm, vis, rest), e, adj, vm, ST.DS{False{}, m, vis}), dfs_ok(0n, rest, ST.cls(vm, vis, rest), e, adj, vm, ST.DS{False{}, m, vis}, b, {==}, h1, h2, below_tl(v, rest, L.mlen(vm), h3), h4, hi))
    case 0n Con{+v, +rest} ST.Free{} ST.DS{True{}, +m, +vis}:
      absurd({res(0n, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(0n, Con{v, rest}, ST.Free{}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Free{}, Equal.sym(ST.Cls, ST.Free{}, ST.Done{}, hc))))
    case 0n Con{+v, +rest} ST.Free{} ST.DS{False{}, +m, +vis}:
      free_res(vm, v, e, cls_free_m(ST.mem(v, vis), ST.getm(vm, v), hc), below_hd(v, rest, L.mlen(vm), h3), h1, h2)
    case 0n Con{+v, +rest} ST.Mate{+e2} ST.DS{True{}, +m, +vis}:
      absurd({res(0n, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(0n, Con{v, rest}, ST.Mate{e2}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Mate{e2}, Equal.sym(ST.Cls, ST.Mate{e2}, ST.Done{}, hc))))
    case 0n Con{+v, +rest} ST.Mate{+e2} ST.DS{False{}, +m, +vis}:
      absurd({res(0n, e, adj, vm, b, ST.DS{False{}, m, vis}, Con{v, rest}, ST.dfs(0n, Con{v, rest}, ST.Mate{e2}, e, adj, vm, ST.DS{False{}, m, vis})) == True{} : Bool}, no_fuel(vm, adj, b, vis, hi))
    case 0n Con{+v, +rest} ST.Done{} ST.DS{True{}, +m, +vis}:
      hi
    case 0n Con{+v, +rest} ST.Done{} ST.DS{False{}, +m, +vis}:
      absurd({res(0n, e, adj, vm, b, ST.DS{False{}, m, vis}, Con{v, rest}, ST.dfs(0n, Con{v, rest}, ST.Done{}, e, adj, vm, ST.DS{False{}, m, vis})) == True{} : Bool}, cls_done(ST.mem(v, vis), ST.getm(vm, v), hc))
    case 1n++g Nil{} ST.Seen{} ST.DS{True{}, +m, +vis}:
      hi
    case 1n++g Nil{} ST.Seen{} ST.DS{False{}, +m, +vis}:
      nil_res(1n+g, e, adj, vm, b, m, vis, hi)
    case 1n++g Nil{} ST.Free{} ST.DS{True{}, +m, +vis}:
      hi
    case 1n++g Nil{} ST.Free{} ST.DS{False{}, +m, +vis}:
      nil_res(1n+g, e, adj, vm, b, m, vis, hi)
    case 1n++g Nil{} ST.Mate{+e2} ST.DS{True{}, +m, +vis}:
      hi
    case 1n++g Nil{} ST.Mate{+e2} ST.DS{False{}, +m, +vis}:
      nil_res(1n+g, e, adj, vm, b, m, vis, hi)
    case 1n++g Nil{} ST.Done{} ST.DS{True{}, +m, +vis}:
      hi
    case 1n++g Nil{} ST.Done{} ST.DS{False{}, +m, +vis}:
      nil_res(1n+g, e, adj, vm, b, m, vis, hi)
    case 1n++g Con{+v, +rest} ST.Seen{} ST.DS{True{}, +m, +vis}:
      absurd({res(1n+g, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(1n+g, Con{v, rest}, ST.Seen{}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Seen{}, Equal.sym(ST.Cls, ST.Seen{}, ST.Done{}, hc))))
    case 1n++g Con{+v, +rest} ST.Seen{} ST.DS{False{}, +m, +vis}:
      seen_fix(1n+g, e, adj, vm, b, v, rest, m, vis, seen_mem(v, vis, ST.getm(vm, v), hc), ST.dfs(1n+g, rest, ST.cls(vm, vis, rest), e, adj, vm, ST.DS{False{}, m, vis}), dfs_ok(1n+g, rest, ST.cls(vm, vis, rest), e, adj, vm, ST.DS{False{}, m, vis}, b, {==}, h1, h2, below_tl(v, rest, L.mlen(vm), h3), h4, hi))
    case 1n++g Con{+v, +rest} ST.Free{} ST.DS{True{}, +m, +vis}:
      absurd({res(1n+g, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(1n+g, Con{v, rest}, ST.Free{}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Free{}, Equal.sym(ST.Cls, ST.Free{}, ST.Done{}, hc))))
    case 1n++g Con{+v, +rest} ST.Free{} ST.DS{False{}, +m, +vis}:
      free_res(vm, v, e, cls_free_m(ST.mem(v, vis), ST.getm(vm, v), hc), below_hd(v, rest, L.mlen(vm), h3), h1, h2)
    case 1n++g Con{+v, +rest} ST.Mate{+e2} ST.DS{True{}, +m, +vis}:
      absurd({res(1n+g, e, adj, vm, b, ST.DS{True{}, m, vis}, Con{v, rest}, ST.dfs(1n+g, Con{v, rest}, ST.Mate{e2}, e, adj, vm, ST.DS{True{}, m, vis})) == True{} : Bool}, L.tf(Equal.cong(ST.Cls, Bool, isdone, ST.Done{}, ST.Mate{e2}, Equal.sym(ST.Cls, ST.Mate{e2}, ST.Done{}, hc))))
    case 1n++g Con{+v, +rest} ST.Mate{+e2} ST.DS{False{}, +m, +vis}:
      +hs = cls_mate_m(ST.mem(v, vis), ST.getm(vm, v), e2, hc)
      +hmv = mate_mem(v, vis, ST.getm(vm, v), e2, hc)
      +hl = below_hd(v, rest, L.mlen(vm), h3)
      +vm2 = ST.setm(vm, v, Some{e})
      +vis1 = {Con{v, vis} : List<&2, Nat>}
      +hne = L.mem_ne(e2, e, ST.somes(vm), L.some_mem(vm, v, e2, hs), h1)
      +hi2 = vo_mk(vm2, adj, vis1, g, vis1, L.dist_con(v, vis, hmv, vo_d(vm, adj, b, 1n+g, vis, hi)), L.band_i(L.issome(ST.getm(vm2, v)), L.allm(vm2, vis), isv(vm, v, e, hl), allm_set(vm, v, Some{e}, vis, vo_a(vm, adj, b, 1n+g, vis, hi), hmv)), L.subl_refl(vis1), closed_base(vm2, adj, vis1, vis1, vis1, L.subl_refl(vis1)), fuel_in(vm, v, e, g, vis, vo_f(vm, adj, b, 1n+g, vis, hi)))
      +r = ST.dfs(g, ST.nthl(adj, e2), ST.cls(vm2, vis1, ST.nthl(adj, e2)), e2, adj, vm2, ST.DS{False{}, vm, vis1})
      +t = tr(g, e, e2, adj, vm, b, v, vis, r, dfs_ok(g, ST.nthl(adj, e2), ST.cls(vm2, vis1, ST.nthl(adj, e2)), e2, adj, vm2, ST.DS{False{}, vm, vis1}, vis1, {==}, L.set_unm(vm, v, e, e2, hs, h2, hne), L.set_dist(vm, v, e, h2, h1), h3_in(adj, vm, v, e, e2, h4), h4_in(adj, vm, v, e, h4), hi2), hs, hi)
      fin(1n+g, e, adj, vm, b, v, rest, m, vis, r, ST.dfs(1n+g, rest, ST.cnext(r, vm, rest), e, adj, vm, r), L.band_r(inv(1n+g, e, adj, vm, b, r), extra(v, vis, r), t), dfs_ok(1n+g, rest, ST.cnext(r, vm, rest), e, adj, vm, r, b, {==}, h1, h2, below_tl(v, rest, L.mlen(vm), h3), h4, L.band_l(inv(1n+g, e, adj, vm, b, r), extra(v, vis, r), t)))
    case 1n++g Con{+v, +rest} ST.Done{} ST.DS{True{}, +m, +vis}:
      hi
    case 1n++g Con{+v, +rest} ST.Done{} ST.DS{False{}, +m, +vis}:
      absurd({res(1n+g, e, adj, vm, b, ST.DS{False{}, m, vis}, Con{v, rest}, ST.dfs(1n+g, Con{v, rest}, ST.Done{}, e, adj, vm, ST.DS{False{}, m, vis})) == True{} : Bool}, cls_done(ST.mem(v, vis), ST.getm(vm, v), hc))

def hi0(+f: Nat, +vm: List<&2, Maybe<&2, Nat>>, hf: {KA.natle(1n+L.mlen(vm), f) == True{} : Bool}) -> {KA.natle(1n+L.mlen(vm), Nat.add(f, 0n)) == True{} : Bool}:
  %LN.add_zero(f) : {KA.natle(1n+L.mlen(vm), _) == True{} : Bool}
  hf

# a search from e, unmatched in vm, with fuel f > |vm|
def search_ok(+f: Nat, +adj: List<&2, List<&2, Nat>>, +vm: List<&2, Maybe<&2, Nat>>, +e: Nat, +h1: {SV.mem(e, ST.somes(vm)) == False{} : Bool}, +h2: {SV.distinct(ST.somes(vm)) == True{} : Bool}, +h4: {adjb(adj, L.mlen(vm)) == True{} : Bool}, hf: {KA.natle(1n+L.mlen(vm), f) == True{} : Bool}) -> {res(f, e, adj, vm, Nil{}, ST.DS{False{}, vm, Nil{}}, ST.nthl(adj, e), ST.search(f, adj, vm, e)) == True{} : Bool}:
  dfs_ok(f, ST.nthl(adj, e), ST.cls(vm, Nil{}, ST.nthl(adj, e)), e, adj, vm, ST.DS{False{}, vm, Nil{}}, Nil{}, {==}, h1, h2, nthl_below(adj, e, L.mlen(vm), h4), h4, hi0(f, vm, hf))

# The witness
# -----------
# A failed search from j (unmatched) leaves visited variables W: j and the
# mates of W are distinct equations, |W| + 1 of them, every variable of
# which is in W.

def rev_go_subl(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {SV.band(L.subl(xs, ST.rev.go(xs, acc)), L.subl(acc, ST.rev.go(xs, acc))) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.band_i(True{}, L.subl(acc, acc), {==}, L.subl_refl(acc))
    case Con{+x, +t}:
      +ih = rev_go_subl(t, Con{x, acc})
      +hacc = L.band_r(L.subl(t, ST.rev.go(t, Con{x, acc})), L.subl(Con{x, acc}, ST.rev.go(t, Con{x, acc})), ih)
      L.band_i(L.subl(Con{x, t}, ST.rev.go(t, Con{x, acc})), L.subl(acc, ST.rev.go(t, Con{x, acc})), L.subl_con(x, t, ST.rev.go(t, Con{x, acc}), L.subl_hd(x, acc, ST.rev.go(t, Con{x, acc}), hacc), L.band_l(L.subl(t, ST.rev.go(t, Con{x, acc})), L.subl(Con{x, acc}, ST.rev.go(t, Con{x, acc})), ih)), L.subl_tl(x, acc, ST.rev.go(t, Con{x, acc}), hacc))

def rev_subl(+xs: List<&2, Nat>, +w: List<&2, Nat>, h: {L.subl(ST.rev(xs), w) == True{} : Bool}) -> {L.subl(xs, w) == True{} : Bool}:
  L.subl_trans(xs, ST.rev(xs), w, L.band_l(L.subl(xs, ST.rev.go(xs, Nil{})), L.subl(Nil{}, ST.rev.go(xs, Nil{})), rev_go_subl(xs, Nil{})), h)

def ev_var.go(+v: Nat, +acc: List<&2, Nat>, +w: List<&2, Nat>, c: Bool, e: {ST.mem(v, acc) == c : Bool}, +h: {L.subl(ST.addv.go(c, v, acc), w) == True{} : Bool}) -> {SV.band(SV.mem(v, w), L.subl(acc, w)) == True{} : Bool}:
  match c:
    case True{}:
      L.band_i(SV.mem(v, w), L.subl(acc, w), L.subl_mem(v, acc, w, %Equal.sym(Bool, SV.mem(v, acc), ST.mem(v, acc), L.mem_sv(v, acc)) : {_ == True{} : Bool}
        e, h), h)
    case False{}:
      h

# every variable evars lists is in w: e's variables are, and acc's
def ev_inside(e: E.QExpr, +acc: List<&2, Nat>, +w: List<&2, Nat>, h: {L.subl(ST.evars(e, acc), w) == True{} : Bool}) -> {SV.band(SV.inside(e, w), L.subl(acc, w)) == True{} : Bool}:
  match e:
    case E.QVar{+v}:
      ev_var.go(v, acc, w, ST.mem(v, acc), {==}, h)
    case E.QCst{q}:
      h
    case E.QAdd{+a, +b}:
      +hb = ev_inside(b, ST.evars(a, acc), w, h)
      +ha = ev_inside(a, acc, w, L.band_r(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb))
      L.band_i(SV.band(SV.inside(a, w), SV.inside(b, w)), L.subl(acc, w), L.band_i(SV.inside(a, w), SV.inside(b, w), L.band_l(SV.inside(a, w), L.subl(acc, w), ha), L.band_l(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb)), L.band_r(SV.inside(a, w), L.subl(acc, w), ha))
    case E.QSub{+a, +b}:
      +hb = ev_inside(b, ST.evars(a, acc), w, h)
      +ha = ev_inside(a, acc, w, L.band_r(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb))
      L.band_i(SV.band(SV.inside(a, w), SV.inside(b, w)), L.subl(acc, w), L.band_i(SV.inside(a, w), SV.inside(b, w), L.band_l(SV.inside(a, w), L.subl(acc, w), ha), L.band_l(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb)), L.band_r(SV.inside(a, w), L.subl(acc, w), ha))
    case E.QMul{+a, +b}:
      +hb = ev_inside(b, ST.evars(a, acc), w, h)
      +ha = ev_inside(a, acc, w, L.band_r(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb))
      L.band_i(SV.band(SV.inside(a, w), SV.inside(b, w)), L.subl(acc, w), L.band_i(SV.inside(a, w), SV.inside(b, w), L.band_l(SV.inside(a, w), L.subl(acc, w), ha), L.band_l(SV.inside(b, w), L.subl(ST.evars(a, acc), w), hb)), L.band_r(SV.inside(a, w), L.subl(acc, w), ha))
    case E.QNeg{+a}:
      ev_inside(a, acc, w, h)

# the variables adj lists for equation k are in w: equation k is inside w
def adj_inside(es: List<&2, E.QExpr>, k: Nat, +w: List<&2, Nat>, h: {L.subl(ST.nthl(ST.adj(es), k), w) == True{} : Bool}) -> {SV.inside(SV.eqat(es, k), w) == True{} : Bool}:
  match es k:
    case Nil{} k:
      {==}
    case Con{+e, t} 0n:
      L.band_l(SV.inside(e, w), L.subl(Nil{}, w), ev_inside(e, Nil{}, w, rev_subl(ST.evars(e, Nil{}), w, h)))
    case Con{e, t} 1n+j:
      adj_inside(t, j, w, h)

def below_mem.go(+x: Nat, +y: Nat, +t: List<&2, Nat>, +n: Nat, c: Bool, e: {SV.eq(x, y) == c : Bool}, hm: {SV.bor(c, SV.mem(x, t)) == True{} : Bool}, hb: {SV.below(Con{y, t}, n) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {SV.below(t, n) == True{} : Bool} -> {SV.lt(x, n) == True{} : Bool}) -> {SV.lt(x, n) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, x, y, L.eq_ok(x, y, e)) : {SV.lt(_, n) == True{} : Bool}
      L.band_l(SV.lt(y, n), SV.below(t, n), hb)
    case False{}:
      ih(hm, L.band_r(SV.lt(y, n), SV.below(t, n), hb))

def below_mem(+x: Nat, ys: List<&2, Nat>, +n: Nat, hm: {SV.mem(x, ys) == True{} : Bool}, hb: {SV.below(ys, n) == True{} : Bool}) -> {SV.lt(x, n) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({SV.lt(x, n) == True{} : Bool}, L.ft(hm))
    case Con{+y, +t}:
      below_mem.go(x, y, t, n, SV.eq(x, y), {==}, hm, hb, p => q => below_mem(x, t, n, p, q))

def below_subl(xs: List<&2, Nat>, +ys: List<&2, Nat>, +n: Nat, +hs: {L.subl(xs, ys) == True{} : Bool}, +hb: {SV.below(ys, n) == True{} : Bool}) -> {SV.below(xs, n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.lt(x, n), SV.below(t, n), below_mem(x, ys, n, L.subl_hd(x, t, ys, hs), hb), below_subl(t, ys, n, L.subl_tl(x, t, ys, hs), hb))

def lt_self(n: Nat) -> {SV.lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      lt_self(m)

# the mates of xs (all closed, over the base Nil) are inside w
def look_inside(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +w: List<&2, Nat>, +h: {closed(vm, ST.adj(es), Nil{}, w, xs) == True{} : Bool}) -> {SV.all_inside(es, ST.look(vm, xs), w) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      L.band_i(SV.inside(SV.eqat(es, mate(vm, v)), w), SV.all_inside(es, ST.look(vm, t), w), adj_inside(es, mate(vm, v), w, L.band_l(L.subl(ST.nthl(ST.adj(es), mate(vm, v)), w), closed(vm, ST.adj(es), Nil{}, w, t), h)), look_inside(es, vm, t, w, L.band_r(L.subl(ST.nthl(ST.adj(es), mate(vm, v)), w), closed(vm, ST.adj(es), Nil{}, w, t), h)))

# a failed search from j: its witness over-determines its variables
def wit_ok(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, +j: Nat, +f: Nat, +vis: List<&2, Nat>, +h1: {SV.mem(j, ST.somes(vm)) == False{} : Bool}, +h2: {SV.distinct(ST.somes(vm)) == True{} : Bool}, hb: {SV.below(ST.somes(vm), SV.neqs(es)) == True{} : Bool}, hj: {SV.lt(j, SV.neqs(es)) == True{} : Bool}, +hv: {vis_ok(vm, ST.adj(es), Nil{}, f, vis) == True{} : Bool}, hn: {L.subl(ST.nthl(ST.adj(es), j), vis) == True{} : Bool}) -> {SV.overdet(es, Con{j, ST.look(vm, vis)}, vis) == True{} : Bool}:
  +adj = ST.adj(es)
  +lk = ST.look(vm, vis)
  +ha = vo_a(vm, adj, Nil{}, f, vis, hv)
  L.band_i(SV.distinct(Con{j, lk}), SV.band(SV.below(Con{j, lk}, SV.neqs(es)), SV.band(SV.lt(SV.len(vis), SV.len(Con{j, lk})), SV.all_inside(es, Con{j, lk}, vis))), L.dist_con(j, lk, L.notin_subl(j, lk, ST.somes(vm), h1, L.look_subl(vm, vis, ha)), L.look_dist(vm, vis, vo_d(vm, adj, Nil{}, f, vis, hv), ha, h2)), L.band_i(SV.below(Con{j, lk}, SV.neqs(es)), SV.band(SV.lt(SV.len(vis), SV.len(Con{j, lk})), SV.all_inside(es, Con{j, lk}, vis)), L.band_i(SV.lt(j, SV.neqs(es)), SV.below(lk, SV.neqs(es)), hj, below_subl(lk, ST.somes(vm), SV.neqs(es), L.look_subl(vm, vis, ha), hb)), L.band_i(SV.lt(SV.len(vis), SV.len(Con{j, lk})), SV.all_inside(es, Con{j, lk}, vis), %Equal.sym(Nat, SV.len(ST.look(vm, vis)), SV.len(vis), L.look_len(vm, vis)) : {SV.lt(SV.len(vis), 1n+_) == True{} : Bool}
    lt_self(SV.len(vis)), L.band_i(SV.inside(SV.eqat(es, j), vis), SV.all_inside(es, lk, vis), adj_inside(es, j, vis, hn), look_inside(es, vm, vis, vis, vo_c(vm, adj, Nil{}, f, vis, hv))))))
