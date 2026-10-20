# bend-cad: the system solved has a perfect matching onto the free
# variables, by dependence (PLAN-sk13a S4, law 9's new part). Proofs
# only.
#
# The pass ends (lib/passpf.bend: final_inv) with the solved positions bp
# and a valid matching vmr of exactly them (equations matched to
# variables they depend on). The pins are the variable side's failed
# searches over them (lib/pass.bend: pins). lib/maxpf.bend's count
# carries over with the dependence adjacency in place of the syntactic
# one (into1d.go, intod_of, pfind are its into1.go, into_of, pfin): the
# pins are distinct variables, nv - |bp| of them, and the variable side's
# matching vm matches every other variable, each to a solved equation
# that depends on it. So reading vm at bp in order matches the system
# solved with the free variables one to one: Perfect.
#
# Generated from tools/drafts/perfpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/box.bend as BX
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./struct.bend as ST
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./deppf.bend as DP
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./gmpf.bend as GM
import ./passpf.bend as PP
import ./solve.bend as SO
import ./clslpf.bend as CL
import ./tarjanpf.bend as TJ
import ./structpf.bend as STP

def absurd(-A: Type, x: Empty) -> A:
  match x:


# lib/maxpf.bend's count, by dependence
# -------------------------------------

def nthl_ltd(es: List<&2, E.QExpr>, j: Nat, +v: Nat, h: {SV.mem(v, ST.nthl(PA.dadjs(es), j)) == True{} : Bool}) -> {SV.lt(j, ST.len.q(es)) == True{} : Bool}:
  match es j:
    case Nil{} j:
      absurd({SV.lt(j, 0n) == True{} : Bool}, KA.ft(h))
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+i:
      nthl_ltd(t, i, v, h)

def into1d.go(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +hs1: {L.subl(ST.somes(vmr), good) == True{} : Bool}, +hs2: {L.subl(good, ST.somes(vmr)) == True{} : Bool}, +hgb: {SV.below(good, ST.len.q(full)) == True{} : Bool}, +r: Nat, +dd: List<&2, Nat>, m: Maybe<&2, Nat>, +e: {ST.getm(vmr, r) == m : Maybe<&2, Nat>}, hl: {KA.natle(1n+r, nv) == True{} : Bool},
  hs: {L.subl(ST.nthl(ST.transpose(nv, 0n, good, PA.dadjs(full)), r), dd) == True{} : Bool}, hvr: {MX.valid(PA.dadjs(full), vmr) == True{} : Bool}) -> {SV.bor(SV.bnot(L.issome(m)), SV.mem(ST.look.of(m), dd)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      +adj = PA.dadjs(full)
      +nq = ST.len.q(full)
      +hrj = MX.valid_get(adj, vmr, r, 0n, j, hvr, e)
      +hg = L.subl_mem(j, ST.somes(vmr), good, L.some_mem(vmr, r, j, e), hs1)
      L.subl_mem(j, ST.nthl(ST.transpose(nv, 0n, good, PA.dadjs(full)), r), dd, MX.in_tr(good, adj, nv, r, j, hl, MX.users_mem(good, adj, r, j, hg, hrj)), hs)

def intod_of(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +hs1: {L.subl(ST.somes(vmr), good) == True{} : Bool}, +hs2: {L.subl(good, ST.somes(vmr)) == True{} : Bool}, +hgb: {SV.below(good, ST.len.q(full)) == True{} : Bool}, xs: List<&2, Nat>, +dd: List<&2, Nat>, +hb: {SV.below(xs, nv) == True{} : Bool}, +hd: {MX.dead(ST.transpose(nv, 0n, good, PA.dadjs(full)), xs, dd) == True{} : Bool}, +hvr: {MX.valid(PA.dadjs(full), vmr) == True{} : Bool})
  -> {MX.into(vmr, xs, dd) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      L.band_i(SV.bor(SV.bnot(L.issome(ST.getm(vmr, r))), SV.mem(ST.look.of(ST.getm(vmr, r)), dd)), MX.into(vmr, t, dd),
        into1d.go(full, nv, vmr, good, hs1, hs2, hgb, r, dd, ST.getm(vmr, r), {==}, D.below_hd(r, t, nv, hb), L.band_l(L.subl(ST.nthl(ST.transpose(nv, 0n, good, PA.dadjs(full)), r), dd), MX.dead(ST.transpose(nv, 0n, good, PA.dadjs(full)), t, dd), hd), hvr),
        intod_of(full, nv, vmr, good, hs1, hs2, hgb, t, dd, D.below_tl(r, t, nv, hb), L.band_r(L.subl(ST.nthl(ST.transpose(nv, 0n, good, PA.dadjs(full)), r), dd), MX.dead(ST.transpose(nv, 0n, good, PA.dadjs(full)), t, dd), hd), hvr))

# what the variable side ends with: its failed searches fs (the pins), its
# matching vm (each equation's variable)
def vsf(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>) -> Bool:
  SV.band(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))))

def vsf_fdist(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {SV.distinct(fs) == True{} : Bool}:
  L.band_l(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h)

def vsf_fbelow(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {SV.below(fs, nv) == True{} : Bool}:
  L.band_l(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h))

def vsf_cnt(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {SV.eq(Nat.add(kn, SV.len(fs)), nv) == True{} : Bool}:
  L.band_l(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h)))

def vsf_valid(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm) == True{} : Bool}:
  L.band_l(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h))))

def vsf_vdist(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), L.band_r(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h)))))

def vsf_ffree(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {MX.disj(fs, ST.somes(vm)) == True{} : Bool}:
  L.band_l(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), L.band_r(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h))))))

def vsf_mus(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), L.band_r(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h)))))))

def vsf_scnt(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {SV.eq(SV.len(ST.somes(vm)), kn) == True{} : Bool}:
  L.band_l(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), L.band_r(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h))))))))

def vsf_fus(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h: {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}) -> {L.subl(fs, ST.down(nv)) == True{} : Bool}:
  L.band_r(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)), L.band_r(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))), L.band_r(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), L.band_r(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), L.band_r(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), L.band_r(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), L.band_r(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h))))))))

def vsf_mk(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +kn: Nat, +vm: List<&2, Maybe<&2, Nat>>, +fs: List<&2, Nat>, h_fdist: {SV.distinct(fs) == True{} : Bool}, h_fbelow: {SV.below(fs, nv) == True{} : Bool}, h_cnt: {SV.eq(Nat.add(kn, SV.len(fs)), nv) == True{} : Bool}, h_valid: {MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm) == True{} : Bool}, h_vdist: {SV.distinct(ST.somes(vm)) == True{} : Bool}, h_ffree: {MX.disj(fs, ST.somes(vm)) == True{} : Bool}, h_mus: {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool}, h_scnt: {SV.eq(SV.len(ST.somes(vm)), kn) == True{} : Bool}, h_fus: {L.subl(fs, ST.down(nv)) == True{} : Bool}) -> {vsf(full, nv, vmr, good, kn, vm, fs) == True{} : Bool}:
  L.band_i(SV.distinct(fs), SV.band(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))))), h_fdist, L.band_i(SV.below(fs, nv), SV.band(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))))), h_fbelow, L.band_i(SV.eq(Nat.add(kn, SV.len(fs)), nv), SV.band(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))))), h_cnt, L.band_i(MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(full)), vm), SV.band(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))))), h_valid, L.band_i(SV.distinct(ST.somes(vm)), SV.band(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))))), h_vdist, L.band_i(MX.disj(fs, ST.somes(vm)), SV.band(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)))), h_ffree, L.band_i(L.subl(ST.somes(vm), ST.down(nv)), SV.band(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv))), h_mus, L.band_i(SV.eq(SV.len(ST.somes(vm)), kn), L.subl(fs, ST.down(nv)), h_scnt, h_fus))))))))

def cancel_r(+a: Nat, +b: Nat, +c: Nat, +n: Nat, h1: {Nat.add(a, b) == n : Nat}, h2: {Nat.add(c, b) == n : Nat}) -> {a == c : Nat}:
  LN.add_cancel(b, a, c, Equal.trans(Nat, Nat.add(b, a), Nat.add(a, b), Nat.add(b, c), LN.add_comm(b, a), Equal.trans(Nat, Nat.add(a, b), n, Nat.add(b, c), h1, Equal.trans(Nat, n, Nat.add(c, b), Nat.add(b, c), Equal.sym(Nat, Nat.add(c, b), n, h2), LN.add_comm(c, b)))))

def pfind(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +hs1: {L.subl(ST.somes(vmr), good) == True{} : Bool}, +hs2: {L.subl(good, ST.somes(vmr)) == True{} : Bool}, +hgb: {SV.below(good, ST.len.q(full)) == True{} : Bool}, +kn: Nat, st: ST.KD, +h: {MX.kinvs(ST.transpose(nv, 0n, good, PA.dadjs(full)), ST.len.q(full), ST.down(nv), SV.len(ST.down(nv)), Nil{}, st) == True{} : Bool}, +hvr: {MX.valid(PA.dadjs(full), vmr) == True{} : Bool},
  +hdr: {SV.distinct(ST.somes(vmr)) == True{} : Bool}, +hmr: {L.mlen(vmr) == nv : Nat}, +hcr: {SV.len(ST.somes(vmr)) == kn : Nat}) -> {vsf(full, nv, vmr, good, kn, ST.KD.vm(st), ST.KD.red(st)) == True{} : Bool}:
  match st:
    case ST.KD{+vm, +fs, +dd}:
      +adj = PA.dadjs(full)
      +nq = ST.len.q(full)
      +adjt = ST.transpose(nv, 0n, good, PA.dadjs(full))
      +us = ST.down(nv)
      +c = SV.len(ST.down(nv))
      +js = {Nil{} : List<&2, Nat>}
      +hfd = MX.kinv_fdist(adjt, nq, us, c, js, vm, fs, dd, h)
      +hfb = D.below_subl(fs, us, nv, MX.kinv_fus(adjt, nq, us, c, js, vm, fs, dd, h), MX.down_below(nv))
      +hab = MX.cnt_end(SV.len(ST.somes(vm)), SV.len(fs), nv, MX.kinv_cnt(adjt, nq, us, c, js, vm, fs, dd, h))
      +hkr = L.subl_trans(MX.keys(vm, 0n), good, ST.somes(vmr), MX.keys_tr(vm, 0n, nv, 0n, good, adj, MX.kinv_valid(adjt, nq, us, c, js, vm, fs, dd, h)), hs2)
      +hak = MX.le_keys(vm, vmr, kn, L.pig(MX.keys(vm, 0n), ST.somes(vmr), MX.keys_dist(vm, 0n), hkr), hcr)
      +lk = ST.look(vm, dd)
      +hls = L.look_subl(vm, dd, MX.kinv_dallm(adjt, nq, us, c, js, vm, fs, dd, h))
      +hdd = MX.dist_app(fs, lk, hfd, L.look_dist(vm, dd, MX.kinv_ddist(adjt, nq, us, c, js, vm, fs, dd, h), MX.kinv_dallm(adjt, nq, us, c, js, vm, fs, dd, h), MX.kinv_dist(adjt, nq, us, c, js, vm, fs, dd, h)), MX.disj_sub(fs, ST.somes(vm), lk, MX.kinv_ffree(adjt, nq, us, c, js, vm, fs, dd, h), hls))
      +hdb = MX.below_app(fs, lk, nv, hfb, D.below_subl(lk, us, nv, L.subl_trans(lk, ST.somes(vm), us, hls, MX.kinv_mus(adjt, nq, us, c, js, vm, fs, dd, h)), MX.down_below(nv)))
      +hdead = MX.dead_app(adjt, fs, lk, dd, MX.kinv_fdead(adjt, nq, us, c, js, vm, fs, dd, h), MX.dead_look(vm, adjt, dd, dd, MX.kinv_dclosed(adjt, nq, us, c, js, vm, fs, dd, h)))
      +hdf = MX.defic(vmr, ST.app(fs, lk), dd, hdd, MX.below_rw(ST.app(fs, lk), L.mlen(vmr), nv, hmr, hdb), hdr, intod_of(full, nv, vmr, good, hs1, hs2, hgb, ST.app(fs, lk), dd, hdb, hdead, hvr))
      +hbh = MX.le_cancel_l(SV.len(dd), SV.len(fs), SV.len(ST.holes(vmr, 0n)), MX.le_fh2(fs, vm, dd, SV.len(ST.holes(vmr, 0n)), hdf))
      +hsq = MX.squeeze(SV.len(ST.somes(vm)), SV.len(fs), kn, SV.len(ST.holes(vmr, 0n)), nv, hab, MX.kh(vmr, kn, nv, hcr, hmr), hak, hbh)
      vsf_mk(full, nv, vmr, good, kn, vm, fs, hfd, hfb, D.eq_of(Nat.add(kn, SV.len(fs)), nv, hsq), MX.kinv_valid(adjt, nq, us, c, js, vm, fs, dd, h), MX.kinv_dist(adjt, nq, us, c, js, vm, fs, dd, h),
        MX.kinv_ffree(adjt, nq, us, c, js, vm, fs, dd, h), MX.kinv_mus(adjt, nq, us, c, js, vm, fs, dd, h), D.eq_of(SV.len(ST.somes(vm)), kn, cancel_r(SV.len(ST.somes(vm)), SV.len(fs), kn, nv, hab, hsq)), MX.kinv_fus(adjt, nq, us, c, js, vm, fs, dd, h))

# vmr: a valid matching of the system full, by dependence, whose matched
# equations are distinct, kn of them, nv long: what the variable side
# over them ends with
def pins_kvd(+full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +hs1: {L.subl(ST.somes(vmr), good) == True{} : Bool}, +hs2: {L.subl(good, ST.somes(vmr)) == True{} : Bool}, +hgb: {SV.below(good, ST.len.q(full)) == True{} : Bool}, +kn: Nat, +hvr: {MX.valid(PA.dadjs(full), vmr) == True{} : Bool}, +hdr: {SV.distinct(ST.somes(vmr)) == True{} : Bool}, +hmr: {L.mlen(vmr) == nv : Nat}, +hcr: {SV.len(ST.somes(vmr)) == kn : Nat})
  -> {vsf(full, nv, vmr, good, kn, ST.KD.vm(PA.kvs(PA.dadjs(full), ST.len.q(full), nv, good)), ST.KD.red(PA.kvs(PA.dadjs(full), ST.len.q(full), nv, good))) == True{} : Bool}:
  +adj = PA.dadjs(full)
  +nq = ST.len.q(full)
  +adjt = ST.transpose(nv, 0n, good, PA.dadjs(full))
  +hbg = hgb
  pfind(full, nv, vmr, good, hs1, hs2, hgb, kn, PA.kvs(adj, nq, nv, good), MX.kwalk(ST.down(nv), adjt, nq, ST.down(nv), SV.len(ST.down(nv)), 1n+nq, ST.KD{ST.nones(nq), Nil{}, Nil{}}, MX.down_dist(nv), L.subl_refl(ST.down(nv)), MX.adjb_tr(nv, 0n, good, adj, nq, hbg), KA.natle_refl(1n+nq), MX.kinit(adjt, nq, ST.down(nv), ST.down(nv))), hvr, hdr, hmr, hcr)

# what lib/structpf.bend's variable-side facts ask, read off vsf (the
# adjacency plays no part in them)
def vside_kd(kd: ST.KD, +full: List<&2, E.QExpr>, +nv: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +hs1: {L.subl(ST.somes(vmr), good) == True{} : Bool}, +hs2: {L.subl(good, ST.somes(vmr)) == True{} : Bool}, +hgb: {SV.below(good, ST.len.q(full)) == True{} : Bool}, +kn: Nat, +hdr: {SV.distinct(ST.somes(vmr)) == True{} : Bool}, +hcr: {SV.len(ST.somes(vmr)) == kn : Nat}, +hgd: {SV.distinct(good) == True{} : Bool},
  +hv: {vsf(full, nv, vmr, good, kn, ST.KD.vm(kd), ST.KD.red(kd)) == True{} : Bool}) -> {STP.vsides(ST.len.q(full), nv, good, kd) == True{} : Bool}:
  match kd:
    case ST.KD{+vm, +fs, dd}:
      +hk = L.eq_ok(SV.len(ST.somes(vm)), kn, vsf_scnt(full, nv, vmr, good, kn, vm, fs, hv))
      +hc = Equal.trans(Nat, Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), Nat.add(kn, SV.len(fs)), nv, Equal.cong(Nat, Nat, z => Nat.add(z, SV.len(fs)), SV.len(ST.somes(vm)), kn, hk), L.eq_ok(Nat.add(kn, SV.len(fs)), nv, vsf_cnt(full, nv, vmr, good, kn, vm, fs, hv)))
      +hfd = vsf_fdist(full, nv, vmr, good, kn, vm, fs, hv)
      +hvd = vsf_vdist(full, nv, vmr, good, kn, vm, fs, hv)
      +hff = vsf_ffree(full, nv, vmr, good, kn, vm, fs, hv)
      +hmus = vsf_mus(full, nv, vmr, good, kn, vm, fs, hv)
      +hgk = KA.natle_antisym(SV.len(good), kn, (%hcr : {KA.natle(SV.len(good), _) == True{} : Bool}
          L.pig(good, ST.somes(vmr), hgd, hs2)),
        (%hcr : {KA.natle(_, SV.len(good)) == True{} : Bool}
          L.pig(ST.somes(vmr), good, hdr, hs1)))
      STP.vside_mk(ST.len.q(full), nv, good, vm, fs, MX.keys_tr(vm, 0n, nv, 0n, good, PA.dadjs(full), vsf_valid(full, nv, vmr, good, kn, vm, fs, hv)), hvd, hfd, hff,
        STP.pigc(ST.app(fs, ST.somes(vm)), ST.down(nv), MX.dist_app(fs, ST.somes(vm), hfd, hvd, hff), TJ.subl_app(fs, ST.somes(vm), ST.down(nv), vsf_fus(full, nv, vmr, good, kn, vm, fs, hv), hmus), STP.all_len(fs, ST.somes(vm), nv, hc)),
        hmus, vsf_fbelow(full, nv, vmr, good, kn, vm, fs, hv), hgd, hgb, D.eq_of(SV.len(good), SV.len(ST.somes(vm)), Equal.trans(Nat, SV.len(good), kn, SV.len(ST.somes(vm)), hgk, Equal.sym(Nat, SV.len(ST.somes(vm)), kn, hk))), D.eq_of(Nat.add(SV.len(ST.somes(vm)), SV.len(fs)), nv, hc))

# The free variables
# ------------------

def free_ge.c(b: Bool, +k: Nat, +rest: List<&2, Nat>, +h: {OW.geall(rest, 1n+k) == True{} : Bool}) -> {OW.geall(SV.free.go(b, k, rest), k) == True{} : Bool}:
  match b:
    case True{}:
      OW.geall_up(rest, k, h)
    case False{}:
      OW.ge_con(k, k, rest, KB.lt_irr(k), OW.geall_up(rest, k, h))

def free_ge(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {OW.geall(SV.free(n, k, pins), k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      free_ge.c(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), free_ge(m, 1n+k, pins))

def free_dist.c(b: Bool, +k: Nat, +rest: List<&2, Nat>, +hg: {OW.geall(rest, 1n+k) == True{} : Bool}, +hd: {SV.distinct(rest) == True{} : Bool}) -> {SV.distinct(SV.free.go(b, k, rest)) == True{} : Bool}:
  match b:
    case True{}:
      hd
    case False{}:
      L.band_i(SV.bnot(SV.mem(k, rest)), SV.distinct(rest), KB.bnot_f(SV.mem(k, rest), SP.ge_notmem(rest, 1n+k, k, hg, KB.lt_succ(k))), hd)

def free_dist(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {SV.distinct(SV.free(n, k, pins)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      free_dist.c(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), free_ge(m, 1n+k, pins), free_dist(m, 1n+k, pins))

def free_np.c(b: Bool, +k: Nat, +rest: List<&2, Nat>, +pins: List<&2, Nat>, e: {SV.mem(k, pins) == b : Bool}, +h: {MX.disj(rest, pins) == True{} : Bool}) -> {MX.disj(SV.free.go(b, k, rest), pins) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.band_i(SV.bnot(SV.mem(k, pins)), MX.disj(rest, pins), KB.bnot_f(SV.mem(k, pins), e), h)

# no free variable is a pin
def free_np(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {MX.disj(SV.free(n, k, pins), pins) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      free_np.c(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), pins, {==}, free_np(m, 1n+k, pins))

def subl_go(b: Bool, +k: Nat, +rest: List<&2, Nat>) -> {L.subl(rest, SV.free.go(b, k, rest)) == True{} : Bool}:
  match b:
    case True{}:
      L.subl_refl(rest)
    case False{}:
      L.subl_cons_r(rest, k, rest, L.subl_refl(rest))

def TJ_app_r(+u: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, b) == True{} : Bool}) -> {SV.mem(u, ST.app(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+x, +t}:
      L.mem_tl(u, x, ST.app(t, b), TJ_app_r(u, t, b, h))

def mem_go(b: Bool, +k: Nat, +rest: List<&2, Nat>, +pins: List<&2, Nat>, e: {SV.mem(k, pins) == b : Bool}) -> {SV.mem(k, ST.app(SV.free.go(b, k, rest), pins)) == True{} : Bool}:
  match b:
    case True{}:
      TJ_app_r(k, rest, pins, e)
    case False{}:
      L.mem_hd(k, ST.app(rest, pins))

def app_l_mem.c(c: Bool, +u: Nat, +x: Nat, +t: List<&2, Nat>, +b: List<&2, Nat>, e: {SV.eq(u, x) == c : Bool}, h: {SV.bor(c, SV.mem(u, t)) == True{} : Bool}, ih: {SV.mem(u, t) == True{} : Bool} -> {SV.mem(u, ST.app(t, b)) == True{} : Bool})
  -> {SV.bor(c, SV.mem(u, ST.app(t, b))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih(h)

def app_l_mem(+u: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {SV.mem(u, a) == True{} : Bool}) -> {SV.mem(u, ST.app(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      absurd({SV.mem(u, ST.app(Nil{}, b)) == True{} : Bool}, KA.ft(h))
    case Con{+x, +t}:
      app_l_mem.c(SV.eq(u, x), u, x, t, b, {==}, h, q => app_l_mem(u, t, b, q))

def subl_appr(ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {L.subl(zs, ST.app(ys, zs)) == True{} : Bool}:
  match ys:
    case Nil{}:
      L.subl_refl(zs)
    case Con{+y, +t}:
      L.subl_cons_r(zs, y, ST.app(t, zs), subl_appr(t, zs))

# every variable from k (n of them) is free or a pin

def subl_app_l(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>, +h: {L.subl(xs, ys) == True{} : Bool}) -> {L.subl(ST.app(xs, zs), ST.app(ys, zs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      subl_appr(ys, zs)
    case Con{+x, +t}:
      L.subl_con(x, ST.app(t, zs), ST.app(ys, zs), app_l_mem(x, ys, zs, L.subl_hd(x, t, ys, h)), subl_app_l(t, ys, zs, L.subl_tl(x, t, ys, h)))

def free_cover(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {L.subl(ST.iota(n, k), ST.app(SV.free(n, k, pins), pins)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.subl_con(k, ST.iota(m, 1n+k), ST.app(SV.free.go(SV.mem(k, pins), k, SV.free(m, 1n+k, pins)), pins), mem_go(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), pins, {==}),
        L.subl_trans(ST.iota(m, 1n+k), ST.app(SV.free(m, 1n+k, pins), pins), ST.app(SV.free.go(SV.mem(k, pins), k, SV.free(m, 1n+k, pins)), pins), free_cover(m, 1n+k, pins),
          subl_app_l(SV.free(m, 1n+k, pins), SV.free.go(SV.mem(k, pins), k, SV.free(m, 1n+k, pins)), pins, subl_go(SV.mem(k, pins), k, SV.free(m, 1n+k, pins)))))

def CL_lt_add(+m: Nat, +i: Nat) -> {SV.lt(i, 1n+Nat.add(m, i)) == True{} : Bool}:
  Equal.trans(Bool, SV.lt(i, 1n+Nat.add(m, i)), KA.natle(1n+i, 1n+Nat.add(m, i)), True{}, L.lt_sv(i, 1n+Nat.add(m, i)), KA.natle_add_l(m, i))

def free_below.c(b: Bool, +k: Nat, +rest: List<&2, Nat>, +n: Nat, +hk: {SV.lt(k, n) == True{} : Bool}, +h: {SV.below(rest, n) == True{} : Bool}) -> {SV.below(SV.free.go(b, k, rest), n) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.band_i(SV.lt(k, n), SV.below(rest, n), hk, h)

def free_below(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> {SV.below(SV.free(n, k, pins), Nat.add(n, k)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      free_below.c(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), Nat.add(1n+m, k), CL_lt_add(m, k),
        (%Equal.sym(Nat, 1n+Nat.add(m, k), Nat.add(m, 1n+k), LN.add_succ(m, k)) : {SV.below(SV.free(m, 1n+k, pins), _) == True{} : Bool}
          free_below(m, 1n+k, pins)))

def iota_len(n: Nat, +k: Nat) -> {SV.len(ST.iota(n, k)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      %Equal.sym(Nat, SV.len(ST.iota(m, 1n+k)), m, iota_len(m, 1n+k)) : {1n+_ == 1n+m : Nat}
      {==}

def iota_ge(n: Nat, +k: Nat) -> {OW.geall(ST.iota(n, k), k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      OW.ge_con(k, k, ST.iota(m, 1n+k), KB.lt_irr(k), OW.geall_up(ST.iota(m, 1n+k), k, iota_ge(m, 1n+k)))

def iota_dist(n: Nat, +k: Nat) -> {SV.distinct(ST.iota(n, k)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.band_i(SV.bnot(SV.mem(k, ST.iota(m, 1n+k))), SV.distinct(ST.iota(m, 1n+k)), KB.bnot_f(SV.mem(k, ST.iota(m, 1n+k)), SP.ge_notmem(ST.iota(m, 1n+k), 1n+k, k, iota_ge(m, 1n+k), KB.lt_succ(k))), iota_dist(m, 1n+k))

def below_iota(xs: List<&2, Nat>, +n: Nat, +h: {SV.below(xs, n) == True{} : Bool}) -> {L.subl(xs, ST.iota(n, 0n)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, ST.iota(n, 0n), MX.iota_mem(n, 0n, x, MX.lt_nat(x, n, L.band_l(SV.lt(x, n), SV.below(t, n), h))), below_iota(t, n, L.band_r(SV.lt(x, n), SV.below(t, n), h)))

# pins distinct and below n: the free variables and the pins number n
def free_len(+n: Nat, +pins: List<&2, Nat>, +hd: {SV.distinct(pins) == True{} : Bool}, +hb: {SV.below(pins, n) == True{} : Bool}) -> {Nat.add(SV.len(SV.free(n, 0n, pins)), SV.len(pins)) == n : Nat}:
  +F = SV.free(n, 0n, pins)
  +ha = MX.dist_app(F, pins, free_dist(n, 0n, pins), hd, free_np(n, 0n, pins))
  +hs = below_iota(ST.app(F, pins), n, MX.below_app(F, pins, n, (%Equal.sym(Nat, n, Nat.add(n, 0n), LN.add_zero(n)) : {SV.below(F, _) == True{} : Bool}
    free_below(n, 0n, pins)), hb))
  Equal.trans(Nat, Nat.add(SV.len(F), SV.len(pins)), SV.len(ST.app(F, pins)), n, Equal.sym(Nat, SV.len(ST.app(F, pins)), Nat.add(SV.len(F), SV.len(pins)), MX.len_app(F, pins)),
    KA.natle_antisym(SV.len(ST.app(F, pins)), n, (%iota_len(n, 0n) : {KA.natle(SV.len(ST.app(F, pins)), _) == True{} : Bool}
      L.pig(ST.app(F, pins), ST.iota(n, 0n), ha, hs)),
      (%iota_len(n, 0n) : {KA.natle(_, SV.len(ST.app(F, pins))) == True{} : Bool}
        L.pig(ST.iota(n, 0n), ST.app(F, pins), iota_dist(n, 0n), free_cover(n, 0n, pins)))))

def mem_free.c(b: Bool, +k: Nat, +rest: List<&2, Nat>, +v: Nat, +pins: List<&2, Nat>, e: {SV.mem(k, pins) == b : Bool}, hv: {SV.mem(v, pins) == False{} : Bool}, +ek: {SV.eq(v, k) == True{} : Bool}) -> {SV.mem(v, SV.free.go(b, k, rest)) == True{} : Bool}:
  match b:
    case True{}:
      absurd({SV.mem(v, rest) == True{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.mem(v, pins), False{}, (%Equal.sym(Nat, v, k, L.eq_ok(v, k, ek)) : {True{} == SV.mem(_, pins) : Bool}
        Equal.sym(Bool, SV.mem(k, pins), True{}, e)), hv)))
    case False{}:
      L.bor_l(SV.eq(v, k), SV.mem(v, rest), ek)

def mem_free.r(b: Bool, +k: Nat, +rest: List<&2, Nat>, +v: Nat, h: {SV.mem(v, rest) == True{} : Bool}) -> {SV.mem(v, SV.free.go(b, k, rest)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.mem_tl(v, k, rest, h)

def mem_free.e(c: Bool, +m: Nat, +k: Nat, +v: Nat, +pins: List<&2, Nat>, ec: {SV.eq(v, k) == c : Bool}, +h1: {SV.lt(v, k) == False{} : Bool}, +h2: {SV.lt(v, Nat.add(1n+m, k)) == True{} : Bool}, +h3: {SV.mem(v, pins) == False{} : Bool},
  ih: {SV.lt(v, 1n+k) == False{} : Bool} -> {SV.lt(v, Nat.add(m, 1n+k)) == True{} : Bool} -> {SV.mem(v, SV.free(m, 1n+k, pins)) == True{} : Bool}) -> {SV.mem(v, SV.free(1n+m, k, pins)) == True{} : Bool}:
  match c:
    case True{}:
      mem_free.c(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), v, pins, {==}, h3, ec)
    case False{}:
      mem_free.r(SV.mem(k, pins), k, SV.free(m, 1n+k, pins), v, ih(SP.nlt_succ(v, k, h1, ec), (%LN.add_succ(m, k) : {SV.lt(v, _) == True{} : Bool}
        h2)))

# v in k .. k + n - 1 and not a pin: v is free
def mem_free(n: Nat, +k: Nat, +pins: List<&2, Nat>, +v: Nat, +h1: {SV.lt(v, k) == False{} : Bool}, +h2: {SV.lt(v, Nat.add(n, k)) == True{} : Bool}, +h3: {SV.mem(v, pins) == False{} : Bool}) -> {SV.mem(v, SV.free(n, k, pins)) == True{} : Bool}:
  match n:
    case 0n:
      absurd({SV.mem(v, Nil{}) == True{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.lt(v, k), False{}, Equal.sym(Bool, SV.lt(v, k), True{}, h2), h1)))
    case 1n++m:
      mem_free.e(SV.eq(v, k), m, k, v, pins, {==}, h1, h2, h3, q => r => mem_free(m, 1n+k, pins, v, q, r, h3))

# The variable side's matching at the solved positions
# ----------------------------------------------------

def key_get(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, j: Nat, h: {SV.mem(Nat.add(j, k), MX.keys(vm, k)) == True{} : Bool}) -> {L.issome(ST.getm(vm, j)) == True{} : Bool}:
  match vm j:
    case Nil{} j:
      absurd({L.issome(ST.getm(Nil{}, j)) == True{} : Bool}, KA.ft(h))
    case Con{None{}, +t} 0n:
      absurd({L.issome(ST.getm(Con{None{}, t}, 0n)) == True{} : Bool}, KA.natlt_irr(k, MX.keys_ge(t, 1n+k, k, h)))
    case Con{None{}, +t} 1n++i:
      key_get(t, 1n+k, i, (%LN.add_succ(i, k) : {SV.mem(_, MX.keys(t, 1n+k)) == True{} : Bool}
        h))
    case Con{Some{x}, t} 0n:
      {==}
    case Con{Some{x}, +t} 1n++i:
      key_get(t, 1n+k, i, (%LN.add_succ(i, k) : {SV.mem(_, MX.keys(t, 1n+k)) == True{} : Bool}
        L.bor_rf(SV.eq(1n+Nat.add(i, k), k), SV.mem(1n+Nat.add(i, k), MX.keys(t, 1n+k)), h, CL.ne_add(i, k))))

def keys_allm(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +h: {L.subl(xs, MX.keys(vm, 0n)) == True{} : Bool}) -> {L.allm(vm, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(L.issome(ST.getm(vm, x)), L.allm(vm, t), key_get(vm, 0n, x, (%LN.add_zero(x) : {SV.mem(_, MX.keys(vm, 0n)) == True{} : Bool}
        L.subl_hd(x, t, MX.keys(vm, 0n), h))), keys_allm(vm, t, L.subl_tl(x, t, MX.keys(vm, 0n), h)))

def inter_dist.c(b: Bool, +h: Nat, +R: List<&2, Nat>, +t: List<&2, Nat>, +hn: {SV.mem(h, t) == False{} : Bool}, +hs: {L.subl(R, t) == True{} : Bool}, +hd: {SV.distinct(R) == True{} : Bool}) -> {SV.distinct(ST.minus.go(b, h, R)) == True{} : Bool}:
  match b:
    case True{}:
      hd
    case False{}:
      L.band_i(SV.bnot(SV.mem(h, R)), SV.distinct(R), KB.bnot_f(SV.mem(h, R), L.notin_subl(h, R, t, hn, hs)), hd)

def inter_dist(xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SV.distinct(xs) == True{} : Bool}) -> {SV.distinct(ST.inter(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      inter_dist.c(ST.bnot(ST.mem(x, ys)), x, ST.inter(t, ys), t, KB.bnot_t(SV.mem(x, t), L.band_l(SV.bnot(SV.mem(x, t)), SV.distinct(t), h)), MX.inter_subx(t, ys), inter_dist(t, ys, L.band_r(SV.bnot(SV.mem(x, t)), SV.distinct(t), h)))

def lenq_neqs(es: List<&2, E.QExpr>) -> {ST.len.q(es) == SV.neqs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, +t}:
      %lenq_neqs(t) : {1n+ST.len.q(t) == 1n+_ : Nat}
      {==}

# positions below nq, matched in vmr: among the matched positions in order
def bp_good(ps: List<&2, Nat>, +nq: Nat, +vmr: List<&2, Maybe<&2, Nat>>, +hs: {L.subl(ps, ST.somes(vmr)) == True{} : Bool}, +hb: {SV.below(ps, nq) == True{} : Bool}) -> {L.subl(ps, ST.inter(ST.iota(nq, 0n), ST.somes(vmr))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      L.subl_con(p, t, ST.inter(ST.iota(nq, 0n), ST.somes(vmr)), MX.inter_mem(ST.iota(nq, 0n), ST.somes(vmr), p, MX.iota_mem(nq, 0n, p, MX.lt_nat(p, nq, L.band_l(SV.lt(p, nq), SV.below(t, nq), hb))), L.subl_hd(p, t, ST.somes(vmr), hs)),
        bp_good(t, nq, vmr, L.subl_tl(p, t, ST.somes(vmr), hs), L.band_r(SV.lt(p, nq), SV.below(t, nq), hb)))

def some_of(x: Maybe<&2, Nat>, h: {L.issome(x) == True{} : Bool}) -> {x == Some{ST.look.of(x)} : Maybe<&2, Nat>}:
  match x:
    case None{}:
      absurd({None{} == Some{0n} : Maybe<&2, Nat>}, KA.ft(h))
    case Some{y}:
      {==}

def bnot_ft(a: Bool, h: {ST.bnot(a) == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, KA.tf(h))

def users_in.e(c: Bool, +j: Nat, +R: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +v: Nat, +p: Nat, ec: {SV.eq(p, j) == c : Bool}, e: {ST.bnot(ST.mem(v, ST.nthl(adj, j))) == False{} : Bool}, h: {SV.bor(c, SV.mem(p, R)) == True{} : Bool},
  ih: {SV.mem(p, R) == True{} : Bool} -> {SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}) -> {SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}:
  match c:
    case True{}:
      (%Equal.sym(Nat, p, j, L.eq_ok(p, j, ec)) : {SV.mem(v, ST.nthl(adj, _)) == True{} : Bool}
        Equal.trans(Bool, SV.mem(v, ST.nthl(adj, j)), ST.mem(v, ST.nthl(adj, j)), True{}, L.mem_sv(v, ST.nthl(adj, j)), bnot_ft(ST.mem(v, ST.nthl(adj, j)), e)))
    case False{}:
      ih(h)

# p uses v among the users of v: v is one of p's

def users_in.c(b: Bool, +j: Nat, +R: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +v: Nat, +p: Nat, e: {ST.bnot(ST.mem(v, ST.nthl(adj, j))) == b : Bool}, h: {SV.mem(p, ST.minus.go(b, j, R)) == True{} : Bool},
  ih: {SV.mem(p, R) == True{} : Bool} -> {SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}) -> {SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}:
  match b:
    case True{}:
      ih(h)
    case False{}:
      users_in.e(SV.eq(p, j), j, R, adj, v, p, {==}, e, h, ih)

def users_in(js: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +v: Nat, +p: Nat, h: {SV.mem(p, ST.users(js, adj, v)) == True{} : Bool}) -> {SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}:
  match js:
    case Nil{}:
      absurd({SV.mem(v, ST.nthl(adj, p)) == True{} : Bool}, KA.ft(h))
    case Con{+j, +t}:
      users_in.c(ST.bnot(ST.mem(v, ST.nthl(adj, j))), j, ST.users(t, adj, v), adj, v, p, {==}, h, q => users_in(t, adj, v, p, q))

def disj_rev.c(b: Bool, +x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, +v: Nat, e: {SV.eq(v, x) == b : Bool}, hx: {SV.mem(x, ys) == False{} : Bool}, hv: {SV.mem(v, ys) == True{} : Bool}, ih: {SV.mem(v, t) == False{} : Bool})
  -> {SV.bor(b, SV.mem(v, t)) == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.mem(x, ys), False{}, (%L.eq_ok(v, x, e) : {True{} == SV.mem(_, ys) : Bool}
        Equal.sym(Bool, SV.mem(v, ys), True{}, hv)), hx)))
    case False{}:
      ih

# no x of xs in ys, v in ys: v not in xs
def disj_rev(xs: List<&2, Nat>, +ys: List<&2, Nat>, +v: Nat, +h: {MX.disj(xs, ys) == True{} : Bool}, +hv: {SV.mem(v, ys) == True{} : Bool}) -> {SV.mem(v, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      disj_rev.c(SV.eq(v, x), x, t, ys, v, {==}, KB.bnot_t(SV.mem(x, ys), L.band_l(SV.bnot(SV.mem(x, ys)), MX.disj(t, ys), h)), hv, disj_rev(t, ys, v, L.band_r(SV.bnot(SV.mem(x, ys)), MX.disj(t, ys), h), hv))

# matched variables, none a pin: all free
def sub_free(xs: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +nv: Nat, +pins: List<&2, Nat>, +hs: {L.subl(xs, ST.somes(vm)) == True{} : Bool}, +hmus: {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool}, +hff: {MX.disj(pins, ST.somes(vm)) == True{} : Bool})
  -> {SV.sub(xs, SV.free(nv, 0n, pins)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      +hv = L.subl_hd(v, t, ST.somes(vm), hs)
      L.band_i(SV.mem(v, SV.free(nv, 0n, pins)), SV.sub(t, SV.free(nv, 0n, pins)),
        mem_free(nv, 0n, pins, v, KB.lt_z(v), (%LN.add_zero(nv) : {SV.lt(v, _) == True{} : Bool}
          D.below_mem(v, ST.somes(vm), nv, hv, D.below_subl(ST.somes(vm), ST.down(nv), nv, hmus, MX.down_below(nv)))), disj_rev(pins, ST.somes(vm), v, hff, hv)),
        sub_free(t, vm, nv, pins, L.subl_tl(v, t, ST.somes(vm), hs), hmus, hff))


def dep_at(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, +p: Nat, +nv: Nat, +good: List<&2, Nat>, +v: Nat, +hv: {MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(es)), vm) == True{} : Bool}, +hs: {ST.getm(vm, p) == Some{v} : Maybe<&2, Nat>}, +hmus: {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool})
  -> SV.Depends(SV.eqat(es, p), v):
  +hlt = D.below_mem(v, ST.somes(vm), nv, L.some_mem(vm, p, v, hs), D.below_subl(ST.somes(vm), ST.down(nv), nv, hmus, MX.down_below(nv)))
  DP.dadj_depends(SV.eqat(es, p), v, (%GM.nthl_dadjs(es, p) : {SV.mem(v, _) == True{} : Bool}
    users_in(good, PA.dadjs(es), v, p, (%MX.tr_nth(nv, 0n, good, PA.dadjs(es), v, MX.lt_nat(v, nv, hlt)) : {SV.mem(p, _) == True{} : Bool}
      MX.valid_get(ST.transpose(nv, 0n, good, PA.dadjs(es)), vm, p, 0n, v, hv, hs)))))

# each equation at ps depends on its variable in the variable side's matching
def depall_v(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, ps: List<&2, Nat>, +nv: Nat, +good: List<&2, Nat>, +hv: {MX.valid(ST.transpose(nv, 0n, good, PA.dadjs(es)), vm) == True{} : Bool}, +hall: {L.allm(vm, ps) == True{} : Bool}, +hmus: {L.subl(ST.somes(vm), ST.down(nv)) == True{} : Bool})
  -> SV.DepAll(SV.picked(es, ps), ST.look(vm, ps)):
  match ps:
    case Nil{}:
      Unit{}
    case Con{+p, +t}:
      (dep_at(es, vm, p, nv, good, ST.look.of(ST.getm(vm, p)), hv, some_of(ST.getm(vm, p), L.band_l(L.issome(ST.getm(vm, p)), L.allm(vm, t), hall)), hmus),
        depall_v(es, vm, t, nv, good, hv, L.band_r(L.issome(ST.getm(vm, p)), L.allm(vm, t), hall), hmus))

# The system solved is matched onto the free variables
# ----------------------------------------------------


def vm_eq(st: PA.PS) -> {PA.PS.vm(st) == PP.ps.vm(st) : List<&2, Maybe<&2, Nat>>}:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      {==}

def bp_eq(st: PA.PS) -> {PA.PS.bp(st) == PP.ps.bp(st) : List<&2, Nat>}:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      {==}

def keys_kn(+vv: List<&2, Maybe<&2, Nat>>, +kn: Nat, h: {SV.eq(SV.len(ST.somes(vv)), kn) == True{} : Bool}) -> {SV.len(MX.keys(vv, 0n)) == kn : Nat}:
  Equal.trans(Nat, SV.len(MX.keys(vv, 0n)), SV.len(ST.somes(vv)), kn, MX.keys_len(vv, 0n), L.eq_ok(SV.len(ST.somes(vv)), kn, h))

def perfect_of(+sk: SK.Sketch, +hvalid: {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), PA.PS.vm(PA.final_st(sk))) == True{} : Bool}, +hdist: {SV.distinct(ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}, +hml: {L.mlen(PA.PS.vm(PA.final_st(sk))) == PA.nvars(sk) : Nat},
  +hs1: {L.subl(ST.somes(PA.PS.vm(PA.final_st(sk))), PA.PS.bp(PA.final_st(sk))) == True{} : Bool}, +hs2: {L.subl(PA.PS.bp(PA.final_st(sk)), ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}, +hbpd: {SV.distinct(PA.PS.bp(PA.final_st(sk))) == True{} : Bool}, +hbpb: {SV.below(PA.PS.bp(PA.final_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hB: {PP.ps.B(PA.final_st(sk)) == SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)) : List<&2, E.QExpr>}, +hp: {PP.ps.B(PA.final_st(sk)) == SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(PA.final_st(sk))) : List<&2, E.QExpr>})
  -> SK.Both({SV.distinct(PA.pins(sk)) == True{} : Bool}, {SV.below(PA.pins(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk)), m)):
  +vs = pins_kvd(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), hs1, hs2, (%Equal.sym(Nat, ST.len.q(SK.Sketch.eqs(sk)), SV.neqs(SK.Sketch.eqs(sk)), lenq_neqs(SK.Sketch.eqs(sk))) : {SV.below(PA.PS.bp(PA.final_st(sk)), _) == True{} : Bool}
    hbpb), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), hvalid, hdist, hml, {==})
  +hcnt = L.eq_ok(Nat.add(SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), SV.len(PA.pins(sk))), PA.nvars(sk), vsf_cnt(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs))
  +hfk = cancel_r(SV.len(SV.free(PA.nvars(sk), 0n, PA.pins(sk))), SV.len(PA.pins(sk)), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), PA.nvars(sk), free_len(PA.nvars(sk), PA.pins(sk), vsf_fdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs), vsf_fbelow(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs)), hcnt)
  +hbk = KA.natle_antisym(SV.len(PA.PS.bp(PA.final_st(sk))), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), L.pig(PA.PS.bp(PA.final_st(sk)), ST.somes(PA.PS.vm(PA.final_st(sk))), hbpd, hs2), L.pig(ST.somes(PA.PS.vm(PA.final_st(sk))), PA.PS.bp(PA.final_st(sk)), hdist, hs1))
  +nq = ST.len.q(SK.Sketch.eqs(sk))
  +hkg = MX.keys_tr(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n, PA.nvars(sk), 0n, PA.solved_pos(sk), PA.dadjs(SK.Sketch.eqs(sk)), vsf_valid(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs))
  +hkl = keys_kn(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), vsf_scnt(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs))
  +hgk = GM.pigc(MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n), PA.solved_pos(sk), MX.keys_dist(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n), hkg, (%Equal.sym(Nat, SV.len(MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n)), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), hkl) : {KA.natle(SV.len(PA.solved_pos(sk)), _) == True{} : Bool}
    L.pig(PA.solved_pos(sk), ST.somes(PA.PS.vm(PA.final_st(sk))), hbpd, hs2)))
  +hbg = L.subl_refl(PA.PS.bp(PA.final_st(sk)))
  +hall = keys_allm(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk)), L.subl_trans(PA.PS.bp(PA.final_st(sk)), PA.solved_pos(sk), MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n), hbg, hgk))
  +m = ST.look(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk)))
  +hmus = vsf_mus(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs)
  ((vsf_fdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs), vsf_fbelow(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs)),
    (m, (L.band_i(SV.eq(SV.len(SV.free(PA.nvars(sk), 0n, PA.pins(sk))), SV.len(m)), SV.band(SV.distinct(m), SV.sub(m, SV.free(PA.nvars(sk), 0n, PA.pins(sk)))),
        D.eq_of(SV.len(SV.free(PA.nvars(sk), 0n, PA.pins(sk))), SV.len(m), Equal.trans(Nat, SV.len(SV.free(PA.nvars(sk), 0n, PA.pins(sk))), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), SV.len(m), hfk, Equal.sym(Nat, SV.len(m), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), Equal.trans(Nat, SV.len(m), SV.len(PA.PS.bp(PA.final_st(sk))), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), L.look_len(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk))), hbk)))),
        L.band_i(SV.distinct(m), SV.sub(m, SV.free(PA.nvars(sk), 0n, PA.pins(sk))), L.look_dist(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk)), hbpd, hall, vsf_vdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs)),
          sub_free(m, ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.nvars(sk), PA.pins(sk), L.look_subl(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk)), hall), hmus, vsf_ffree(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs)))),
      (%Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(PA.final_st(sk))), PP.ps.B(PA.final_st(sk)), SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), Equal.sym(List<&2, E.QExpr>, PP.ps.B(PA.final_st(sk)), SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(PA.final_st(sk))), hp),
          Equal.trans(List<&2, E.QExpr>, PP.ps.B(PA.final_st(sk)), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)), SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), hB, Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)), SP.solved_end(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)))))) : SV.DepAll(_, m)
        depall_v(SK.Sketch.eqs(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.PS.bp(PA.final_st(sk)), PA.nvars(sk), PA.solved_pos(sk), vsf_valid(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), PA.pins(sk), vs), hall, hmus)))))

# the pass's final state, from the dependence adjacency's bound
def final_inv.a(+sk: SK.Sketch, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> PP.PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk)):
  (%Equal.sym(Nat, SV.ncons(sk), Nat.add(SV.clen(PA.recs(sk)), 0n), Equal.trans(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), Nat.add(SV.clen(PA.recs(sk)), 0n), PP.ncons_recs(sk), LN.add_zero(SV.clen(PA.recs(sk))))) : PP.PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), _, PA.final_st(sk))
    PP.pass_inv(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), {==}, {==}, hA, PP.classes_down(sk), PP.pinv0(sk)))


def f_valid(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), PA.PS.vm(PA.final_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), vm_eq(PA.final_st(sk))) : {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), _) == True{} : Bool}
    PP.pib_valid(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb))

def f_dist(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {SV.distinct(ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), vm_eq(PA.final_st(sk))) : {SV.distinct(ST.somes(_)) == True{} : Bool}
    PP.pib_dist(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb))

def f_mlen(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {L.mlen(PA.PS.vm(PA.final_st(sk))) == PA.nvars(sk) : Nat}:
  L.eq_ok(L.mlen(PA.PS.vm(PA.final_st(sk))), PA.nvars(sk), (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), vm_eq(PA.final_st(sk))) : {SV.eq(L.mlen(_), PA.nvars(sk)) == True{} : Bool}
    PP.pib_mlen(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb)))

def f_s1(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {L.subl(ST.somes(PA.PS.vm(PA.final_st(sk))), PA.PS.bp(PA.final_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), vm_eq(PA.final_st(sk))) : {L.subl(ST.somes(_), PA.PS.bp(PA.final_st(sk))) == True{} : Bool}
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), bp_eq(PA.final_st(sk))) : {L.subl(ST.somes(PP.ps.vm(PA.final_st(sk))), _) == True{} : Bool}
      PP.pib_s1(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb)))

def f_s2(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {L.subl(PA.PS.bp(PA.final_st(sk)), ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), vm_eq(PA.final_st(sk))) : {L.subl(PA.PS.bp(PA.final_st(sk)), ST.somes(_)) == True{} : Bool}
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), bp_eq(PA.final_st(sk))) : {L.subl(_, ST.somes(PP.ps.vm(PA.final_st(sk)))) == True{} : Bool}
      PP.pib_s2(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb)))

def f_bpd(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {SV.distinct(PA.PS.bp(PA.final_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, PA.PS.bp(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), bp_eq(PA.final_st(sk))) : {SV.distinct(_) == True{} : Bool}
    PP.pib_bpd(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb))

def f_bpb(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk))) == True{} : Bool}) -> {SV.below(PA.PS.bp(PA.final_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, PA.PS.bp(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), bp_eq(PA.final_st(sk))) : {SV.below(_, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}
    PP.pib_bpb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PP.ps.rows(PA.final_st(sk)), PP.ps.B(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), PP.ps.vm(PA.final_st(sk)), hb))



# the variable side over the system solved ends as lib/structpf.bend's
# blocks want it
def f_gb(+sk: SK.Sketch, +hbpb: {SV.below(PA.PS.bp(PA.final_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.below(PA.PS.bp(PA.final_st(sk)), ST.len.q(SK.Sketch.eqs(sk))) == True{} : Bool}:
  (%Equal.sym(Nat, ST.len.q(SK.Sketch.eqs(sk)), SV.neqs(SK.Sketch.eqs(sk)), lenq_neqs(SK.Sketch.eqs(sk))) : {SV.below(PA.PS.bp(PA.final_st(sk)), _) == True{} : Bool}
    hbpb)

def vend_of(+sk: SK.Sketch, +hvalid: {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), PA.PS.vm(PA.final_st(sk))) == True{} : Bool}, +hdist: {SV.distinct(ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}, +hml: {L.mlen(PA.PS.vm(PA.final_st(sk))) == PA.nvars(sk) : Nat}, +hs1: {L.subl(ST.somes(PA.PS.vm(PA.final_st(sk))), PA.PS.bp(PA.final_st(sk))) == True{} : Bool}, +hs2: {L.subl(PA.PS.bp(PA.final_st(sk)), ST.somes(PA.PS.vm(PA.final_st(sk)))) == True{} : Bool}, +hbpd: {SV.distinct(PA.PS.bp(PA.final_st(sk))) == True{} : Bool}, +hbpb: {SV.below(PA.PS.bp(PA.final_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {STP.vsides(ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))) == True{} : Bool}:
  +hgb = f_gb(sk, hbpb)
  vside_kd(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)), SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), hs1, hs2, hgb, SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), hdist, {==}, hbpd, pins_kvd(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(PA.final_st(sk)), PA.solved_pos(sk), hs1, hs2, hgb, SV.len(ST.somes(PA.PS.vm(PA.final_st(sk)))), hvalid, hdist, hml, {==}))

def vend_pass(+sk: SK.Sketch, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {STP.vsides(ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))) == True{} : Bool}:
  +hi = final_inv.a(sk, hA)
  +hb = PP.pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi)
  vend_of(sk, f_valid(sk, hb), f_dist(sk, hb), f_mlen(sk, hb), f_s1(sk, hb), f_s2(sk, hb), f_bpd(sk, hb), f_bpb(sk, hb))

# law 9's new part, for the pass: the pins are distinct variables, and the
# system solved has a perfect matching onto the free variables, by
# dependence
def total_pass.a(+sk: SK.Sketch, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool})
  -> SK.Both({SV.distinct(PA.pins(sk)) == True{} : Bool}, {SV.below(PA.pins(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk)), m)):
  +hi = final_inv.a(sk, hA)
  +hb = PP.pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi)
  perfect_of(sk, f_valid(sk, hb), f_dist(sk, hb), f_mlen(sk, hb), f_s1(sk, hb), f_s2(sk, hb), f_bpd(sk, hb), f_bpb(sk, hb),
    PP.pinv_B(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi),
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(PA.final_st(sk)), PP.ps.bp(PA.final_st(sk)), bp_eq(PA.final_st(sk))) : {PP.ps.B(PA.final_st(sk)) == SV.picked(SK.Sketch.eqs(sk), _) : List<&2, E.QExpr>}
      PP.pinv_p(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi)))

def total_pass(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool})
  -> SK.Both({SV.distinct(PA.pins(sk)) == True{} : Bool}, {SV.below(PA.pins(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk)), m)):
  total_pass.a(sk, PP.adjb_of(sk, w, cov))
