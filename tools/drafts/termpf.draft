# bend-cad: the simplex finishes (PLAN-sk13a S3). solve runs 2^N steps
# (N variables). If it were still going after them, the 2^N + 1 bases seen
# would be distinct (Bland, lib/blandpf.bend), each a list of N flags: one
# more than there are (lib/pigeon.bend).
#
# Generated from tools/drafts/termpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ./karith.bend as KA
import ./nat.bend as LN
import ./qfield.bend as QF
import ./simplex.bend as SX
import ./simppf.bend as SP
import ./runpf.bend as RN
import ./blandpf.bend as BL
import ./pigeon.bend as PH

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The run's steps
# ---------------

def iter_add(a: Nat, +b: Nat, +lp: SX.LP, +r: SX.Run) -> {RN.iter(Nat.add(a, b), lp, r) == RN.iter(b, lp, RN.iter(a, lp, r)) : SX.Run}:
  match a:
    case 0n:
      {==}
    case 1n+k:
      iter_add(k, b, lp, SX.adv(lp, r))

# run k takes 2^k steps
def run_iter(k: Nat, +lp: SX.LP, +r: SX.Run) -> {SX.run(k, lp, r) == RN.iter(PH.pow2(k), lp, r) : SX.Run}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      %Equal.sym(SX.Run, SX.run(j, lp, r), RN.iter(PH.pow2(j), lp, r), run_iter(j, lp, r)) : {SX.run(j, lp, _) == RN.iter(Nat.add(PH.pow2(j), PH.pow2(j)), lp, r) : SX.Run}
      %Equal.sym(SX.Run, SX.run(j, lp, RN.iter(PH.pow2(j), lp, r)), RN.iter(PH.pow2(j), lp, RN.iter(PH.pow2(j), lp, r)), run_iter(j, lp, RN.iter(PH.pow2(j), lp, r))) : {_ == RN.iter(Nat.add(PH.pow2(j), PH.pow2(j)), lp, r) : SX.Run}
      Equal.sym(SX.Run, RN.iter(Nat.add(PH.pow2(j), PH.pow2(j)), lp, r), RN.iter(PH.pow2(j), lp, RN.iter(PH.pow2(j), lp, r)), iter_add(PH.pow2(j), PH.pow2(j), lp, r))

def solve_st(+lp: SX.LP) -> {SX.solve(lp) == RN.st(lp, PH.pow2(SX.LP.nv(lp))) : SX.Run}:
  run_iter(SX.LP.nv(lp), lp, SX.Go{SX.init(lp)})

# The bases seen
# --------------

# the bases at steps p .. p + c - 1
def blst(+lp: SX.LP, c: Nat, +p: Nat) -> List<&2, List<&2, Bool>>:
  match c:
    case 0n:
      Nil{}
    case 1n+k:
      Con{BL.B(lp, p), blst(lp, k, 1n+p)}

def llen_blst(+lp: SX.LP, c: Nat, +p: Nat) -> {PH.llen(blst(lp, c, p)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %llen_blst(lp, k, 1n+p) : {1n+PH.llen(blst(lp, k, 1n+p)) == 1n+_ : Nat}
      {==}

def blen_eq(u: List<&2, Bool>) -> {PH.blen(u) == SP.blen(u) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %blen_eq(t) : {1n+PH.blen(t) == 1n+_ : Nat}
      {==}

def alllen_blst(+lp: SX.LP, c: Nat, +p: Nat) -> {PH.alllen(blst(lp, c, p), SX.LP.nv(lp)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      KA.band_i(KA.nateq(PH.blen(BL.B(lp, p)), SX.LP.nv(lp)), PH.alllen(blst(lp, k, 1n+p), SX.LP.nv(lp)),
        KA.nateq_of(PH.blen(BL.B(lp, p)), SX.LP.nv(lp), Equal.trans(Nat, PH.blen(BL.B(lp, p)), SP.blen(BL.B(lp, p)), SX.LP.nv(lp), blen_eq(BL.B(lp, p)), RN.bl_at(lp, p))),
        alllen_blst(lp, k, 1n+p))

# No basis comes back
# -------------------

# go at step p + 1 + L, read off go at the last step looked at
def go_head(+lp: SX.LP, k: Nat, +L: Nat, +p: Nat, hg: {RN.isgo(RN.st(lp, BL.plus(k, 1n+BL.plus(L, p)))) == True{} : Bool}) -> {RN.isgo(RN.st(lp, BL.plus(1n+L, p))) == True{} : Bool}:
  %Equal.sym(Nat, BL.plus(L, 1n+p), 1n+BL.plus(L, p), BL.plus_succ(L, p)) : {RN.isgo(RN.st(lp, _)) == True{} : Bool}
  BL.go_down(lp, k, 0n, 1n+BL.plus(L, p), {==}, hg)

# the bases at p and p + 1 + L differ
def nb.go(b: Bool, +lp: SX.LP, +L: Nat, +p: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, BL.plus(1n+L, p))) == True{} : Bool}, hb: {b == PH.beq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p))) : Bool}) -> {False{} == PH.beq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p))) : Bool}:
  match b:
    case True{}:
      absurd({False{} == PH.beq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p))) : Bool},
        BL.bland_main(~QF.qfield(), lp, L, p, hwf, hG, PH.beq_eq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p)), Equal.sym(Bool, True{}, PH.beq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p))), hb))))
    case False{}:
      hb

# B(p) is not among the k bases from p + 1 + L on, while the run is still
# going at the last of them
def nm(+lp: SX.LP, k: Nat, +L: Nat, +p: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hg: {RN.isgo(RN.st(lp, BL.plus(k, BL.plus(L, p)))) == True{} : Bool}) -> {PH.memb(BL.B(lp, p), blst(lp, k, BL.plus(1n+L, p))) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      %nb.go(PH.beq(BL.B(lp, p), BL.B(lp, BL.plus(1n+L, p))), lp, L, p, hwf, go_head(lp, j, L, p, hg), {==}) : {PH.bor(_, PH.memb(BL.B(lp, p), blst(lp, j, 1n+BL.plus(1n+L, p)))) == False{} : Bool}
      %BL.plus_succ(1n+L, p) : {PH.memb(BL.B(lp, p), blst(lp, j, _)) == False{} : Bool}
      nm(lp, j, 1n+L, p, hwf,
        (%Equal.sym(Nat, BL.plus(L, 1n+p), 1n+BL.plus(L, p), BL.plus_succ(L, p)) : {RN.isgo(RN.st(lp, BL.plus(j, _))) == True{} : Bool}
          hg))

# while the run is still going at p + c, the bases at p .. p + c differ
def nd(+lp: SX.LP, c: Nat, +p: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hg: {RN.isgo(RN.st(lp, BL.plus(c, p))) == True{} : Bool}) -> {PH.nodup(blst(lp, 1n+c, p)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      KA.band_i(PH.bnot(PH.memb(BL.B(lp, p), blst(lp, 1n+k, 1n+p))), PH.nodup(blst(lp, 1n+k, 1n+p)),
        (%Equal.sym(Bool, PH.memb(BL.B(lp, p), blst(lp, 1n+k, 1n+p)), False{}, nm(lp, 1n+k, 0n, p, hwf, hg)) : {PH.bnot(_) == True{} : Bool}
          {==}),
        nd(lp, k, 1n+p, hwf, hg))

# The run stops
# -------------

def plus0(c: Nat) -> {BL.plus(c, 0n) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, BL.plus(k, 1n), 1n+BL.plus(k, 0n), BL.plus_succ(k, 0n)) : {_ == 1n+k : Nat}
      %plus0(k) : {1n+BL.plus(k, 0n) == 1n+_ : Nat}
      {==}

def contra(+lp: SX.LP, hwf: {SP.lpwf(lp) == True{} : Bool}, hg: {RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))) == True{} : Bool}) -> Empty:
  KA.natlt_irr(PH.pow2(SX.LP.nv(lp)),
    (%llen_blst(lp, 1n+PH.pow2(SX.LP.nv(lp)), 0n) : {KA.natle(_, PH.pow2(SX.LP.nv(lp))) == True{} : Bool}
      PH.ph(SX.LP.nv(lp), blst(lp, 1n+PH.pow2(SX.LP.nv(lp)), 0n), alllen_blst(lp, 1n+PH.pow2(SX.LP.nv(lp)), 0n),
        nd(lp, PH.pow2(SX.LP.nv(lp)), 0n, hwf,
          (%Equal.sym(Nat, BL.plus(PH.pow2(SX.LP.nv(lp)), 0n), PH.pow2(SX.LP.nv(lp)), plus0(PH.pow2(SX.LP.nv(lp)))) : {RN.isgo(RN.st(lp, _)) == True{} : Bool}
            hg)))))

def ends.go(b: Bool, +lp: SX.LP, hwf: {SP.lpwf(lp) == True{} : Bool}, hb: {b == RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))) : Bool}) -> {RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))) == False{} : Bool}:
  match b:
    case True{}:
      absurd({RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))) == False{} : Bool}, contra(lp, hwf, Equal.sym(Bool, True{}, RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))), hb)))
    case False{}:
      Equal.sym(Bool, False{}, RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))), hb)

# the simplex finishes: Sat or Unsat, never still going
def solve_ends(+lp: SX.LP, hwf: {SP.lpwf(lp) == True{} : Bool}) -> {RN.isgo(SX.solve(lp)) == False{} : Bool}:
  %Equal.sym(SX.Run, SX.solve(lp), RN.st(lp, PH.pow2(SX.LP.nv(lp))), solve_st(lp)) : {RN.isgo(_) == False{} : Bool}
  ends.go(RN.isgo(RN.st(lp, PH.pow2(SX.LP.nv(lp)))), lp, hwf, {==})
