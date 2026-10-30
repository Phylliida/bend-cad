# bend-cad: K's pivots are among the bases' monomials (PLAN-sk13b B3,
# termination). kslack(M, P) counts the monomials of M that are not yet a
# pivot. Adding to K a generator in the bases' span that K does not hold
# makes a row whose pivot is in DC.kmons (else every coefficient there
# would be 0, the pivot's own included) and is no earlier pivot (the
# residual is 0 at each), so kslack goes down (ks_add_dec). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./natring.bend as NR
import ./redpoly.bend as RP
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LP2
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./spanpf.bend as SN
import ./dclose.bend as DC
import ./dcbasepf.bend as BS

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Counting
# --------

# the rows' pivots
def pivs(rows: List<&2, EL.Row>) -> List<&2, List<&2, Nat>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{row, t}:
      Con{EP.rowpv(row), pivs(t)}

def free(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# the monomials of ms that are not among P
def kslack(ms: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, t}:
      Nat.add(free(BS.mmem(m, P)), kslack(t, P))

def msnoc(P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match P:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, msnoc(t, x)}

def pivs_snoc(rows: List<&2, EL.Row>, +row: EL.Row) -> {pivs(EL.rsnoc(rows, row)) == msnoc(pivs(rows), EP.rowpv(row)) : List<&2, List<&2, Nat>>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, List<&2, Nat>>, pivs(EL.rsnoc(t, row)), msnoc(pivs(t), EP.rowpv(row)), pivs_snoc(t, row)) : {Con{EP.rowpv(h), _} == Con{EP.rowpv(h), msnoc(pivs(t), EP.rowpv(row))} : List<&2, List<&2, Nat>>}
      {==}

def bor_f(c: Bool) -> {SV.bor(c, False{}) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def bor_assoc(a: Bool, +b: Bool, +c: Bool) -> {SV.bor(a, SV.bor(b, c)) == SV.bor(SV.bor(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mmem_snoc(+m: List<&2, Nat>, P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {BS.mmem(m, msnoc(P, x)) == SV.bor(BS.mmem(m, P), EL.iseq(NR.mcmp(m, x))) : Bool}:
  match P:
    case Nil{}:
      bor_f(EL.iseq(NR.mcmp(m, x)))
    case Con{+h, +t}:
      %Equal.sym(Bool, BS.mmem(m, msnoc(t, x)), SV.bor(BS.mmem(m, t), EL.iseq(NR.mcmp(m, x))), mmem_snoc(m, t, x)) : {SV.bor(EL.iseq(NR.mcmp(m, h)), _) == SV.bor(SV.bor(EL.iseq(NR.mcmp(m, h)), BS.mmem(m, t)), EL.iseq(NR.mcmp(m, x))) : Bool}
      bor_assoc(EL.iseq(NR.mcmp(m, h)), BS.mmem(m, t), EL.iseq(NR.mcmp(m, x)))

def free_le(a: Bool, b: Bool) -> {KA.natle(free(SV.bor(a, b)), free(a)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def free_snoc(+m: List<&2, Nat>, +P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {KA.natle(free(BS.mmem(m, msnoc(P, x))), free(BS.mmem(m, P))) == True{} : Bool}:
  %Equal.sym(Bool, BS.mmem(m, msnoc(P, x)), SV.bor(BS.mmem(m, P), EL.iseq(NR.mcmp(m, x))), mmem_snoc(m, P, x)) : {KA.natle(free(_), free(BS.mmem(m, P))) == True{} : Bool}
  free_le(BS.mmem(m, P), EL.iseq(NR.mcmp(m, x)))

# one more pivot frees nothing
def kslack_le(M: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {KA.natle(kslack(M, msnoc(P, x)), kslack(M, P)) == True{} : Bool}:
  match M:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      KA.natle_add2(free(BS.mmem(m, msnoc(P, x))), kslack(t, msnoc(P, x)), free(BS.mmem(m, P)), kslack(t, P), free_snoc(m, P, x), kslack_le(t, P, x))

def iseq_eq(o: Cmp, h: {EL.iseq(o) == True{} : Bool}) -> {EQ{} == o : Cmp}:
  match o:
    case LT{}:
      absurd({EQ{} == LT{} : Cmp}, KA.ft(h))
    case EQ{}:
      {==}
    case GT{}:
      absurd({EQ{} == GT{} : Cmp}, KA.ft(h))

def kslack_lt.hd(+x: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>, hp: {BS.mmem(x, P) == False{} : Bool})
  -> {KA.natle(1n+kslack(Con{x, t}, msnoc(P, x)), kslack(Con{x, t}, P)) == True{} : Bool}:
  %Equal.sym(Bool, BS.mmem(x, msnoc(P, x)), SV.bor(BS.mmem(x, P), EL.iseq(NR.mcmp(x, x))), mmem_snoc(x, P, x)) : {KA.natle(1n+Nat.add(free(_), kslack(t, msnoc(P, x))), Nat.add(free(BS.mmem(x, P)), kslack(t, P))) == True{} : Bool}
  %Equal.sym(Bool, BS.mmem(x, P), False{}, hp) : {KA.natle(1n+Nat.add(free(SV.bor(_, EL.iseq(NR.mcmp(x, x)))), kslack(t, msnoc(P, x))), Nat.add(free(_), kslack(t, P))) == True{} : Bool}
  %RP.mcmp_refl(x) : {KA.natle(1n+Nat.add(free(SV.bor(False{}, EL.iseq(_))), kslack(t, msnoc(P, x))), Nat.add(free(False{}), kslack(t, P))) == True{} : Bool}
  kslack_le(t, P, x)

def kslack_lt.go(b: Bool, +m: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, eb: {b == EL.iseq(NR.mcmp(x, m)) : Bool},
  hx: {SV.bor(b, BS.mmem(x, t)) == True{} : Bool}, +hp: {BS.mmem(x, P) == False{} : Bool},
  ih: {BS.mmem(x, t) == True{} : Bool} -> {KA.natle(1n+kslack(t, msnoc(P, x)), kslack(t, P)) == True{} : Bool})
  -> {KA.natle(1n+kslack(Con{m, t}, msnoc(P, x)), kslack(Con{m, t}, P)) == True{} : Bool}:
  match b:
    case True{}:
      %NR.mcmp_eq(x, m, iseq_eq(NR.mcmp(x, m), Equal.sym(Bool, True{}, EL.iseq(NR.mcmp(x, m)), eb))) : {KA.natle(1n+kslack(Con{_, t}, msnoc(P, x)), kslack(Con{_, t}, P)) == True{} : Bool}
      kslack_lt.hd(x, t, P, hp)
    case False{}:
      %Equal.sym(Nat, 1n+Nat.add(free(BS.mmem(m, msnoc(P, x))), kslack(t, msnoc(P, x))), Nat.add(free(BS.mmem(m, msnoc(P, x))), 1n+kslack(t, msnoc(P, x))), LN.add_succ(free(BS.mmem(m, msnoc(P, x))), kslack(t, msnoc(P, x))))
        : {KA.natle(_, Nat.add(free(BS.mmem(m, P)), kslack(t, P))) == True{} : Bool}
      KA.natle_add2(free(BS.mmem(m, msnoc(P, x))), 1n+kslack(t, msnoc(P, x)), free(BS.mmem(m, P)), kslack(t, P), free_snoc(m, P, x), ih(hx))

# a new pivot among M that was not a pivot frees one less
def kslack_lt(M: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hx: {BS.mmem(x, M) == True{} : Bool}, +hp: {BS.mmem(x, P) == False{} : Bool})
  -> {KA.natle(1n+kslack(M, msnoc(P, x)), kslack(M, P)) == True{} : Bool}:
  match M:
    case Nil{}:
      absurd({KA.natle(1n+kslack(Nil{}, msnoc(P, x)), kslack(Nil{}, P)) == True{} : Bool}, KA.ft(hx))
    case Con{+m, +t}:
      kslack_lt.go(EL.iseq(NR.mcmp(x, m)), m, t, P, x, {==}, hx, hp, h => kslack_lt(t, P, x, h, hp))

def free_bound(b: Bool) -> {KA.natle(free(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# at most one per monomial
def kslack_bound(M: List<&2, List<&2, Nat>>, +P: List<&2, List<&2, Nat>>) -> {KA.natle(kslack(M, P), DC.mlen(M)) == True{} : Bool}:
  match M:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      KA.natle_add2(free(BS.mmem(m, P)), kslack(t, P), 1n, DC.mlen(t), free_bound(BS.mmem(m, P)), kslack_bound(t, P))

# The new pivot
# -------------

def AllIn(xs: List<&2, E.QExpr>, +B: List<&2, E.QExpr>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, t}:
      SK.Both(SN.InSpan(x, B), AllIn(t, B))

def allin_snoc(xs: List<&2, E.QExpr>, +x: E.QExpr, +B: List<&2, E.QExpr>, h: AllIn(xs, B), hx: SN.InSpan(x, B)) -> AllIn(EP.qsnoc(xs, x), B):
  match xs:
    case Nil{}:
      (hx, Unit{})
    case Con{+y, +t}:
      (a, b) = h
      (a, allin_snoc(t, x, B, b, hx))

def zdot_z(u: List<&2, S.Z>, Bk: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +m: List<&2, Nat>, h: AllIn(Bk, B), +hz: {BS.czs0(B, m) == True{} : Bool}) -> {EP.zdot(u, EP.zv(m, Bk)) == S.Z0{} : S.Z}:
  match u Bk:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bt}:
      {==}
    case Con{x, ut} Nil{}:
      {==}
    case Con{+x, +ut} Con{+b, +bt}:
      (hb, ht) = h
      %Equal.sym(S.Z, EL.cz(m, EP.NE(b)), S.Z0{}, BS.span_cz(b, B, m, hb, hz)) : {S.Z.add(S.Z.mul(x, _), EP.zdot(ut, EP.zv(m, bt))) == S.Z0{} : S.Z}
      %ZL.mul_zero(x) : {S.Z.add(_, EP.zdot(ut, EP.zv(m, bt))) == S.Z0{} : S.Z}
      zdot_z(ut, bt, B, m, ht, hz)

def cz_piv0(+p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +Bk: List<&2, E.QExpr>, +B: List<&2, E.QExpr>,
  hrel: {EL.cz(EL.pivot(p), p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(EL.pivot(p), EP.NE(e))), EP.zdot(cb, EP.zv(EL.pivot(p), Bk))) : S.Z},
  +he: SN.InSpan(e, B), hk: AllIn(Bk, B), +hz: {BS.czs0(B, EL.pivot(p)) == True{} : Bool}) -> {EL.cz(EL.pivot(p), p) == S.Z0{} : S.Z}:
  %BS.span_cz(e, B, EL.pivot(p), he, hz) : {EL.cz(EL.pivot(p), p) == S.Z.add(S.Z.mul(S.Zpos{bt}, _), S.Z0{}) : S.Z}
  %zdot_z(cb, Bk, B, EL.pivot(p), hk, hz) : {EL.cz(EL.pivot(p), p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(EL.pivot(p), EP.NE(e))), _) : S.Z}
  hrel

def piv_in.go(f: Bool, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +Bk: List<&2, E.QExpr>, +B: List<&2, E.QExpr>,
  ef: {f == BS.mmem(EL.pivot(p), DC.kmons(B)) : Bool},
  hrel: {EL.cz(EL.pivot(p), p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(EL.pivot(p), EP.NE(e))), EP.zdot(cb, EP.zv(EL.pivot(p), Bk))) : S.Z},
  hnz: {RP.nz(EL.cz(EL.pivot(p), p)) == True{} : Bool}, he: SN.InSpan(e, B), hk: AllIn(Bk, B)) -> {BS.mmem(EL.pivot(p), DC.kmons(B)) == True{} : Bool}:
  match f:
    case True{}:
      Equal.sym(Bool, True{}, BS.mmem(EL.pivot(p), DC.kmons(B)), ef)
    case False{}:
      +hz = BS.czs_out(B, EL.pivot(p), Equal.sym(Bool, False{}, BS.mmem(EL.pivot(p), DC.kmons(B)), ef))
      absurd({BS.mmem(EL.pivot(p), DC.kmons(B)) == True{} : Bool}, KA.ft(
        (%cz_piv0(p, cb, bt, e, Bk, B, hrel, he, hk, hz) : {RP.nz(_) == True{} : Bool}
          hnz)))

def piv_new.go(g: Bool, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +row: EL.Row, +t: List<&2, EL.Row>, eg: {g == EL.iseq(NR.mcmp(EL.pivot(p), EP.rowpv(row))) : Bool},
  hz: {EP.iszero(EL.cz(EP.rowpv(row), p)) == True{} : Bool}, hnz: {RP.nz(EL.cz(EL.pivot(p), p)) == True{} : Bool}, ih: {BS.mmem(EL.pivot(p), pivs(t)) == False{} : Bool})
  -> {SV.bor(g, BS.mmem(EL.pivot(p), pivs(t))) == False{} : Bool}:
  match g:
    case True{}:
      absurd({SV.bor(True{}, BS.mmem(EL.pivot(p), pivs(t))) == False{} : Bool}, KA.ft(
        (%EP.zero_of(EL.cz(EP.rowpv(row), p), hz) : {RP.nz(_) == True{} : Bool}
          (%NR.mcmp_eq(EL.pivot(p), EP.rowpv(row), iseq_eq(NR.mcmp(EL.pivot(p), EP.rowpv(row)), Equal.sym(Bool, True{}, EL.iseq(NR.mcmp(EL.pivot(p), EP.rowpv(row))), eg))) : {RP.nz(EL.cz(_, p)) == True{} : Bool}
            hnz))))
    case False{}:
      ih

# the residual's pivot is no row's pivot: it is 0 at each
def piv_new(rows: List<&2, EL.Row>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, hz: {EP.zp(rows, EL.Res{p, cb, bt}) == True{} : Bool}, +hnz: {RP.nz(EL.cz(EL.pivot(p), p)) == True{} : Bool})
  -> {BS.mmem(EL.pivot(p), pivs(rows)) == False{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      +hz2 = hz
      piv_new.go(EL.iseq(NR.mcmp(EL.pivot(p), EP.rowpv(row))), p, cb, bt, row, t, {==},
        KA.band_l(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz2), hnz,
        piv_new(t, p, cb, bt, KA.band_r(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz2), hnz))

def dec.r(r: EL.Res, +rows: List<&2, EL.Row>, +e: E.QExpr, +Bk: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, hrel: @m: List<&2, Nat> -> EP.Rel(m, r, e, Bk), hred: {EP.RedR(r) == True{} : Bool},
  hzp: {EP.zp(rows, r) == True{} : Bool}, hne: {EP.isnil(EP.resp(r)) == False{} : Bool}, he: SN.InSpan(e, B), hk: AllIn(Bk, B))
  -> {KA.natle(1n+kslack(DC.kmons(B), pivs(EL.rsnoc(rows, EL.row_of(r)))), kslack(DC.kmons(B), pivs(rows))) == True{} : Bool}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      +hnz = EP.pivot_nz(p, hred, hne)
      %Equal.sym(List<&2, List<&2, Nat>>, pivs(EL.rsnoc(rows, EL.row_of(EL.Res{p, cb, bt}))), msnoc(pivs(rows), EL.pivot(p)), pivs_snoc(rows, EL.row_of(EL.Res{p, cb, bt}))) : {KA.natle(1n+kslack(DC.kmons(B), _), kslack(DC.kmons(B), pivs(rows))) == True{} : Bool}
      kslack_lt(DC.kmons(B), pivs(rows), EL.pivot(p), piv_in.go(BS.mmem(EL.pivot(p), DC.kmons(B)), p, cb, bt, e, Bk, B, {==}, hrel(EL.pivot(p)), hnz, he, hk), piv_new(rows, p, cb, bt, hzp, hnz))

# adding to K a generator in the bases' span that K does not hold frees one
# less of the bases' monomials
def ks_add_dec(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS.KS, +d: DR.Der, +B: List<&2, E.QExpr>,
  hr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), 0n) == True{} : Bool}, hk: AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), B),
  he: SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), B), +hn: {KS.ks.inb(k, DR.Jd.e(DR.concl(es, fs, d))) == False{} : Bool})
  -> {KA.natle(1n+kslack(DC.kmons(B), pivs(KS.ks.rows(KS.ks.add(es, fs, k, d)))), kslack(DC.kmons(B), pivs(KS.ks.rows(k)))) == True{} : Bool}:
  match k:
    case KS.KS{+rows, +ds}:
      +hr2 = hr
      +e = DR.Jd.e(DR.concl(es, fs, d))
      %Equal.sym(Bool, KS.ks.inb(KS.KS{rows, ds}, e), False{}, hn) : {KA.natle(1n+kslack(DC.kmons(B), pivs(KS.ks.rows(KS.ks.pick(_, rows, ds, EL.resid(rows, e), d)))), kslack(DC.kmons(B), pivs(rows))) == True{} : Bool}
      dec.r(EL.resid(rows, e), rows, e, KS.kexprs(es, fs, ds), B, m => EP.resid_rel(m, rows, e, KS.kexprs(es, fs, ds), EP.rinv_allok(KS.kexprs(es, fs, ds), rows, 0n, hr2)),
        EP.resid_red(rows, e, KS.kexprs(es, fs, ds), EP.rinv_allok(KS.kexprs(es, fs, ds), rows, 0n, hr2)),
        EP.reduce_zp(rows, EL.start(e, EL.rlen(rows)), KS.kexprs(es, fs, ds), EP.rinv_allok(KS.kexprs(es, fs, ds), rows, 0n, hr2), EP.rinv_ech(KS.kexprs(es, fs, ds), rows, 0n, hr2)),
        hn, he, hk)
