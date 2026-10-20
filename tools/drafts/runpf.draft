# bend-cad: the simplex's run (PLAN-sk13a S3). Bland's choices as "first
# index" facts, the run as steps from the start, the dictionary's
# invariants (lib/simppf.bend) at every step, and the facts each step's
# choices give: the leaving slack is the smallest below its bound, the
# entering variable the smallest that can raise it.
#
# Generated from tools/drafts/runpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./elim.bend as EL
import ./simplex.bend as SX
import ./simppf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# First indices
# -------------

# the first True of bs, counting from j
def firstfrom(bs: List<&2, Bool>, +j: Nat) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, t}:
      SX.pick(b, j, firstfrom(t, 1n+j))

def mapS(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{1n+x}

def mval(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def issome(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def some_inj(+a: Nat, +b: Nat, h: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, mval, Some{a}, Some{b}, h)

def none_some(+b: Nat, h: {None{} == Some{b} : Maybe<&2, Nat>}) -> Empty:
  KA.ft(Equal.cong(Maybe<&2, Nat>, Bool, issome, None{}, Some{b}, h))

def pick_map(b: Bool, +j: Nat, +r: Maybe<&2, Nat>) -> {SX.pick(b, 1n+j, mapS(r)) == mapS(SX.pick(b, j, r)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# counting from j + 1 shifts every index by one
def first_shift(bs: List<&2, Bool>, +j: Nat) -> {firstfrom(bs, 1n+j) == mapS(firstfrom(bs, j)) : Maybe<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(Maybe<&2, Nat>, firstfrom(t, 2n+j), mapS(firstfrom(t, 1n+j)), first_shift(t, 1n+j)) : {SX.pick(b, 1n+j, _) == mapS(SX.pick(b, j, firstfrom(t, 1n+j))) : Maybe<&2, Nat>}
      pick_map(b, j, firstfrom(t, 1n+j))

def succ_ne0(+k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  KA.tf(Equal.cong(Nat, Bool, x => SX.ltn(0n, x), 1n+k, 0n, e))

def map_zero(m: Maybe<&2, Nat>, h: {mapS(m) == Some{0n} : Maybe<&2, Nat>}) -> Empty:
  match m:
    case None{}:
      none_some(0n, h)
    case Some{+x}:
      succ_ne0(x, some_inj(1n+x, 0n, h))

def map_succ(m: Maybe<&2, Nat>, +k: Nat, h: {mapS(m) == Some{1n+k} : Maybe<&2, Nat>}) -> {m == Some{k} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      absurd({None{} == Some{k} : Maybe<&2, Nat>}, none_some(1n+k, h))
    case Some{+x}:
      Equal.cong(Nat, Maybe<&2, Nat>, y => Some{y}, x, k, LN.succ_inj(x, k, some_inj(1n+x, 1n+k, h)))

def map_none(m: Maybe<&2, Nat>, h: {mapS(m) == None{} : Maybe<&2, Nat>}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      absurd({Some{x} == None{} : Maybe<&2, Nat>}, none_some(1n+x, Equal.sym(Maybe<&2, Nat>, Some{1n+x}, None{}, h)))

# the first True from 0, at i: bs_i is True, every bs_k (k < i) False, and
# i is below bs's length
def first_some(bs: List<&2, Bool>, i: Nat, h: {firstfrom(bs, 0n) == Some{i} : Maybe<&2, Nat>}) -> {SP.bat(bs, i) == True{} : Bool}:
  match bs i:
    case Nil{} i:
      absurd({SP.bat(Nil{}, i) == True{} : Bool}, none_some(i, h))
    case Con{True{}, t} 0n:
      {==}
    case Con{True{}, t} 1n++k:
      absurd({SP.bat(Con{True{}, t}, 1n+k) == True{} : Bool}, succ_ne0(k, Equal.sym(Nat, 0n, 1n+k, some_inj(0n, 1n+k, h))))
    case Con{False{}, +t} 0n:
      absurd({SP.bat(Con{False{}, t}, 0n) == True{} : Bool}, map_zero(firstfrom(t, 0n), (%first_shift(t, 0n) : {_ == Some{0n} : Maybe<&2, Nat>}
        h)))
    case Con{False{}, +t} 1n++k:
      first_some(t, k, map_succ(firstfrom(t, 0n), k, (%first_shift(t, 0n) : {_ == Some{1n+k} : Maybe<&2, Nat>}
        h)))

def first_min(bs: List<&2, Bool>, i: Nat, h: {firstfrom(bs, 0n) == Some{i} : Maybe<&2, Nat>}, k: Nat, hk: {SX.ltn(k, i) == True{} : Bool}) -> {SP.bat(bs, k) == False{} : Bool}:
  match bs i k:
    case Nil{} i k:
      {==}
    case Con{True{}, t} 0n k:
      absurd({SP.bat(Con{True{}, t}, k) == False{} : Bool}, KA.ft(SP.ltn0(k, hk)))
    case Con{True{}, t} 1n++j k:
      absurd({SP.bat(Con{True{}, t}, k) == False{} : Bool}, succ_ne0(j, Equal.sym(Nat, 0n, 1n+j, some_inj(0n, 1n+j, h))))
    case Con{False{}, +t} 0n k:
      absurd({SP.bat(Con{False{}, t}, k) == False{} : Bool}, map_zero(firstfrom(t, 0n), (%first_shift(t, 0n) : {_ == Some{0n} : Maybe<&2, Nat>}
        h)))
    case Con{False{}, +t} 1n++j 0n:
      {==}
    case Con{False{}, +t} 1n++j 1n++g:
      first_min(t, j, map_succ(firstfrom(t, 0n), j, (%first_shift(t, 0n) : {_ == Some{1n+j} : Maybe<&2, Nat>}
        h)), g, hk)

def first_none(bs: List<&2, Bool>, h: {firstfrom(bs, 0n) == None{} : Maybe<&2, Nat>}, k: Nat) -> {SP.bat(bs, k) == False{} : Bool}:
  match bs k:
    case Nil{} k:
      {==}
    case Con{True{}, t} k:
      absurd({SP.bat(Con{True{}, t}, k) == False{} : Bool}, none_some(0n, Equal.sym(Maybe<&2, Nat>, Some{0n}, None{}, h)))
    case Con{False{}, +t} 0n:
      {==}
    case Con{False{}, +t} 1n++g:
      first_none(t, map_none(firstfrom(t, 0n), (%first_shift(t, 0n) : {_ == None{} : Maybe<&2, Nat>}
        h)), g)

def first_lt(bs: List<&2, Bool>, i: Nat, h: {firstfrom(bs, 0n) == Some{i} : Maybe<&2, Nat>}) -> {SX.ltn(i, SP.blen(bs)) == True{} : Bool}:
  match bs i:
    case Nil{} i:
      absurd({SX.ltn(i, SP.blen(Nil{})) == True{} : Bool}, none_some(i, h))
    case Con{True{}, t} 0n:
      {==}
    case Con{True{}, t} 1n++k:
      absurd({SX.ltn(1n+k, SP.blen(Con{True{}, t})) == True{} : Bool}, succ_ne0(k, Equal.sym(Nat, 0n, 1n+k, some_inj(0n, 1n+k, h))))
    case Con{False{}, +t} 0n:
      {==}
    case Con{False{}, +t} 1n++k:
      first_lt(t, k, map_succ(firstfrom(t, 0n), k, (%first_shift(t, 0n) : {_ == Some{1n+k} : Maybe<&2, Nat>}
        h)))

# The choices as first indices
# ----------------------------

# which slacks are below their bounds
def viols(qs: List<&2, SX.Ineq>, rs: List<&2, SX.Rw>, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>) -> List<&2, Bool>:
  match qs rs:
    case Nil{} rs:
      Nil{}
    case Con{q, qt} Nil{}:
      Nil{}
    case Con{q, qt} Con{r, rt}:
      Con{SX.viol(r, v0, v1, q), viols(qt, rt, v0, v1)}

def leave_eq(qs: List<&2, SX.Ineq>, rs: List<&2, SX.Rw>, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>, +j: Nat) -> {SX.leave.go(qs, rs, v0, v1, j) == firstfrom(viols(qs, rs, v0, v1), j) : Maybe<&2, Nat>}:
  match qs rs:
    case Nil{} rs:
      {==}
    case Con{q, qt} Nil{}:
      {==}
    case Con{+q, +qt} Con{+r, +rt}:
      %leave_eq(qt, rt, v0, v1, 1n+j) : {SX.pick(SX.viol(r, v0, v1, q), j, SX.leave.go(qt, rt, v0, v1, 1n+j)) == SX.pick(SX.viol(r, v0, v1, q), j, _) : Maybe<&2, Nat>}
      {==}

# inequality k (0 >= 0 past the end)
def qat(qs: List<&2, SX.Ineq>, k: Nat) -> SX.Ineq:
  match qs k:
    case Nil{} k:
      SX.Ineq{Nil{}, S.Z0{}, False{}}
    case Con{q, t} 0n:
      q
    case Con{q, t} 1n++j:
      qat(t, j)

def bat_viols(qs: List<&2, SX.Ineq>, rs: List<&2, SX.Rw>, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>, k: Nat, hk: {SX.ltn(k, SX.qlen(qs)) == True{} : Bool}, hr: {KA.natle(SX.qlen(qs), SP.nrows(rs)) == True{} : Bool}) -> {SP.bat(viols(qs, rs, v0, v1), k) == SX.viol(SX.rowat(rs, k), v0, v1, qat(qs, k)) : Bool}:
  match qs rs k:
    case Nil{} rs k:
      absurd({SP.bat(viols(Nil{}, rs, v0, v1), k) == SX.viol(SX.rowat(rs, k), v0, v1, qat(Nil{}, k)) : Bool}, KA.ft(SP.ltn0(k, hk)))
    case Con{q, qt} Nil{} k:
      absurd({SP.bat(viols(Con{q, qt}, Nil{}, v0, v1), k) == SX.viol(SX.rowat(Nil{}, k), v0, v1, qat(Con{q, qt}, k)) : Bool}, KA.ft(hr))
    case Con{q, qt} Con{r, rt} 0n:
      {==}
    case Con{q, qt} Con{r, rt} 1n++j:
      bat_viols(qt, rt, v0, v1, j, hk, hr)

def blen_viols(qs: List<&2, SX.Ineq>, rs: List<&2, SX.Rw>, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>) -> {KA.natle(SP.blen(viols(qs, rs, v0, v1)), SX.qlen(qs)) == True{} : Bool}:
  match qs rs:
    case Nil{} rs:
      {==}
    case Con{q, qt} Nil{}:
      {==}
    case Con{q, qt} Con{r, rt}:
      blen_viols(qt, rt, v0, v1)

# which variables can raise a row, counting from j (free: j >= m)
def helps(r: List<&2, S.Z>, +m: Nat, +j: Nat) -> List<&2, Bool>:
  match r:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{SX.helpful(c, Nat.is_le(m, j)), helps(t, m, 1n+j)}

def enter_eq(r: List<&2, S.Z>, +m: Nat, +j: Nat) -> {SX.enter.go(r, m, j) == firstfrom(helps(r, m, j), j) : Maybe<&2, Nat>}:
  match r:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %enter_eq(t, m, 1n+j) : {SX.pick(SX.helpful(c, Nat.is_le(m, j)), j, SX.enter.go(t, m, 1n+j)) == SX.pick(SX.helpful(c, Nat.is_le(m, j)), j, _) : Maybe<&2, Nat>}
      {==}

def bat_helps(r: List<&2, S.Z>, +m: Nat, +j: Nat, k: Nat) -> {SP.bat(helps(r, m, j), k) == SX.helpful(SX.at(r, k), Nat.is_le(m, Nat.add(k, j))) : Bool}:
  match r k:
    case Nil{} k:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, +t} 1n++g:
      %Equal.sym(Nat, 1n+Nat.add(g, j), Nat.add(g, 1n+j), LN.add_succ(g, j)) : {SP.bat(helps(t, m, 1n+j), g) == SX.helpful(SX.at(t, g), Nat.is_le(m, _)) : Bool}
      bat_helps(t, m, 1n+j, g)

def blen_helps(r: List<&2, S.Z>, +m: Nat, +j: Nat) -> {SX.vlen(r) == SP.blen(helps(r, m, j)) : Nat}:
  match r:
    case Nil{}:
      {==}
    case Con{c, +t}:
      %blen_helps(t, m, 1n+j) : {1n+SX.vlen(t) == 1n+_ : Nat}
      {==}

# a variable that can raise the row has a nonzero entry
def helpful_nz(c: S.Z, +f: Bool, h: {SX.helpful(c, f) == True{} : Bool}) -> {SX.iszero(c) == False{} : Bool}:
  match c:
    case S.Z0{}:
      absurd({SX.iszero(S.Z0{}) == False{} : Bool}, KA.ft(h))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}
