# Proofs of the block certificate laws (DESIGN §8.3; stated in ROADMAP.bend
# while sk-05 is open). Untrusted: proofs only. Each law takes a block and
# a certificate apart, extracts the checker's facts from check == True,
# and carries them into F through the map H.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./karith.bend as KA
import ./kball.bend as KB
import ./slope.bend as SL
import ./cert.bend as CK
import ./nat.bend as LN

# The checker's facts
# -------------------

def x_shape(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.shape(~K, eqs, n, yc, yr, ym, pc, pr) == True{} : Bool}:
  KA.band_l(CK.shape(~K, eqs, n, yc, yr, ym, pc, pr), CK.rest1(~K, eqs, n, yc, yr, q, ym, pc, pr), ok)

def x_r1(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.rest1(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}:
  KA.band_r(CK.shape(~K, eqs, n, yc, yr, ym, pc, pr), CK.rest1(~K, eqs, n, yc, yr, q, ym, pc, pr), ok)

def x_factor(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.factor(~K, q) == True{} : Bool}:
  KA.band_l(CK.factor(~K, q), CK.rest2(~K, eqs, n, yc, yr, q, ym, pc, pr), x_r1(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_r2(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.rest2(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}:
  KA.band_r(CK.factor(~K, q), CK.rest2(~K, eqs, n, yc, yr, q, ym, pc, pr), x_r1(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_con(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.ccon(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}:
  KA.band_l(CK.ccon(~K, eqs, n, yc, yr, q, ym, pc, pr), CK.rest3(~K, eqs, n, yc, yr, ym, pc, pr), x_r2(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_r3(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.rest3(~K, eqs, n, yc, yr, ym, pc, pr) == True{} : Bool}:
  KA.band_r(CK.ccon(~K, eqs, n, yc, yr, q, ym, pc, pr), CK.rest3(~K, eqs, n, yc, yr, ym, pc, pr), x_r2(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_self(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.cself(~K, eqs, n, yc, yr, ym, pc, pr) == True{} : Bool}:
  KA.band_l(CK.cself(~K, eqs, n, yc, yr, ym, pc, pr), CK.cinj(~K, eqs, n, yc, yr, ym, pc, pr), x_r3(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_inj(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.cinj(~K, eqs, n, yc, yr, ym, pc, pr) == True{} : Bool}:
  KA.band_r(CK.cself(~K, eqs, n, yc, yr, ym, pc, pr), CK.cinj(~K, eqs, n, yc, yr, ym, pc, pr), x_r3(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

# the shape facts: shape = s1 && (s2 && (... && s9))

def xs_r0(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))))) == True{} : Bool}:
  x_shape(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)

def xs_r1(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))))) == True{} : Bool}:
  KA.band_r(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))))), xs_r0(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r2(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))) == True{} : Bool}:
  KA.band_r(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))), xs_r1(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r3(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))) == True{} : Bool}:
  KA.band_r(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))), xs_r2(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r4(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))) == True{} : Bool}:
  KA.band_r(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))), xs_r3(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r5(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))) == True{} : Bool}:
  KA.band_r(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))), xs_r4(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r6(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))) == True{} : Bool}:
  KA.band_r(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))), xs_r5(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r7(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)) == True{} : Bool}:
  KA.band_r(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)), xs_r6(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def xs_r8(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs) == True{} : Bool}:
  KA.band_r(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs), xs_r7(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_len_eqs(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.nateq(CK.eqlen(eqs), n) == True{} : Bool}:
  KA.band_l(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))))), xs_r0(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_len_ym(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.nateq(CK.mlen(~K, ym), n) == True{} : Bool}:
  KA.band_l(KA.nateq(CK.mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))))), xs_r1(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_len_yc(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.nateq(KA.klen(~K, yc), n) == True{} : Bool}:
  KA.band_l(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))), xs_r2(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_len_yr(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.natle(KA.klen(~K, yr), n) == True{} : Bool}:
  KA.band_l(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))))), xs_r3(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_len_p(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)) == True{} : Bool}:
  KA.band_l(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))), xs_r4(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_nn_yr(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.kvle(~K, Nil{}, yr) == True{} : Bool}:
  KA.band_l(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs))), xs_r5(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_nn_pr(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.kvle(~K, Nil{}, pr) == True{} : Bool}:
  KA.band_l(KA.kvle(~K, Nil{}, pr), KA.band(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)), xs_r6(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_held(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.allheld(~K, eqs) == True{} : Bool}:
  KA.band_l(CK.allheld(~K, eqs), CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs), xs_r7(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def x_below(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {CK.allbelow(Nat.add(n, KA.klen(~K, pc)), eqs) == True{} : Bool}:
  xs_r8(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)

# The factor and the center
# -------------------------

def klt1_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +q: N.NC(K), h: {KA.klt(~K, q, N.none(K)) == True{} : Bool}) -> O.lt(F, N.emap(K, F, H, q), O.one(F)):
  %N.e_one(K, F, H) : O.lt(F, N.emap(K, F, H, q), _)
  KA.klt_ok(~K, ~F, ~H, q, N.none(K), h)

def factor_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +q: N.NC(K), +hf: {CK.factor(~K, q) == True{} : Bool}) -> M.Both(O.le(~F, O.zero(F), N.emap(K, F, H, q)), O.lt(F, N.emap(K, F, H, q), O.one(F))):
  (KA.kle0_ok(~K, ~F, ~H, q, KA.band_l(KA.kle(~K, N.nzero(K), q), KA.klt(~K, q, N.none(K)), hf)), klt1_ok(~K, ~F, ~H, q, KA.band_r(KA.kle(~K, N.nzero(K), q), KA.klt(~K, q, N.none(K)), hf)))

def cert_factor.c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>, ok: {CK.check.c(~K, eqs, n, c) == True{} : Bool}) -> M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F))):
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      factor_ok(~K, ~F, ~H, q, x_factor(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

# LAW cert_factor: the contraction factor is in [0, 1)
def cert_factor(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: C.Block, c: C.Cert<K>, ok: {CK.check(~K, b, c) == True{} : Bool}) -> M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F))):
  match b:
    case C.Block{+eqs, +n}:
      cert_factor.c(~K, ~F, ~H, eqs, n, c, ok)

def cert_center.c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>, ok: {CK.check.c(~K, eqs, n, c) == True{} : Bool}) -> C.ball(~K, ~F, ~H, c, C.center(~K, ~F, ~H, c)):
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      ({==}, FV.rbnd_self(~F, N.ofkv(~K, ~F, ~H, yc), N.ofkv(~K, ~F, ~H, yr), KA.kvle_ok(~K, ~F, ~H, Nil{}, yr, x_nn_yr(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))))

# LAW cert_center: the box contains its center
def cert_center(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: C.Block, c: C.Cert<K>, ok: {CK.check(~K, b, c) == True{} : Bool}) -> C.ball(~K, ~F, ~H, c, C.center(~K, ~F, ~H, c)):
  match b:
    case C.Block{+eqs, +n}:
      cert_center.c(~K, ~F, ~H, eqs, n, c, ok)

# Lengths and naturals
# --------------------

def nateq_ok(a: Nat, b: Nat, h: {KA.nateq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      FO.absurd({0n == 1n+j : Nat}, KA.ft(h))
    case 1n+i 0n:
      FO.absurd({1n+i == 0n : Nat}, KA.ft(h))
    case 1n++i 1n+j:
      %nateq_ok(i, j, h) : {1n+i == 1n+_ : Nat}
      {==}

def len_ofkv(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, v: N.KVec(~K)) -> {M.len(~F, N.ofkv(~K, ~F, ~H, v)) == KA.klen(~K, v) : Nat}:
  match v:
    case Nil{}:
      {==}
    case Con{a, vs}:
      %len_ofkv(~K, ~F, ~H, vs) : {1n+M.len(~F, N.ofkv(~K, ~F, ~H, vs)) == 1n+_ : Nat}
      {==}

def klen_kfit(~K: N.Num, n: Nat, r: N.KVec(~K)) -> {KA.klen(~K, KA.kfit(~K, n, r)) == n : Nat}:
  match n r:
    case 0n r:
      {==}
    case 1n++k Nil{}:
      %klen_kfit(~K, k, Nil{}) : {1n+KA.klen(~K, KA.kfit(~K, k, Nil{})) == 1n+_ : Nat}
      {==}
    case 1n++k Con{x, xs}:
      %klen_kfit(~K, k, xs) : {1n+KA.klen(~K, KA.kfit(~K, k, xs)) == 1n+_ : Nat}
      {==}

# u - w has length n, for u and w of length n
def len_vsub(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), n: Nat, h1: {M.len(~F, u) == n : Nat}, h2: {M.len(~F, w) == n : Nat}) -> {M.len(~F, C.vsub(~F, u, w)) == n : Nat}:
  match u w n:
    case Nil{} Nil{} n:
      h1
    case Nil{} Con{+b, +bs} n:
      FO.absurd({M.len(~F, C.vsub(~F, Nil{}, Con{b, bs})) == n : Nat}, FV.zero_ne(M.len(~F, bs), Equal.trans(Nat, 0n, n, 1n+M.len(~F, bs), h1, Equal.sym(Nat, 1n+M.len(~F, bs), n, h2))))
    case Con{+a, +as} Nil{} n:
      FO.absurd({M.len(~F, C.vsub(~F, Con{a, as}, Nil{})) == n : Nat}, FV.succ_ne(M.len(~F, as), Equal.trans(Nat, 1n+M.len(~F, as), n, 0n, h1, Equal.sym(Nat, 0n, n, h2))))
    case Con{+a, +as} Con{+b, +bs} 0n:
      FO.absurd({M.len(~F, C.vsub(~F, Con{a, as}, Con{b, bs})) == 0n : Nat}, FV.succ_ne(M.len(~F, as), h1))
    case Con{a, +as} Con{b, +bs} 1n++k:
      %Equal.sym(Nat, M.len(~F, C.vsub(~F, as, bs)), k, len_vsub(~F, as, bs, k, FV.succ_inj(M.len(~F, as), k, h1), FV.succ_inj(M.len(~F, bs), k, h2))) : {1n+_ == 1n+k : Nat}
      {==}

# |a| <= H 0 from |a| <= 0
def rbnd_e0(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: O.C(F), h: M.bnd(~F, a, O.zero(F))) -> M.bnd(~F, a, N.emap(K, F, H, N.nzero(K))):
  %KA.ez(~K, ~F, ~H) : M.bnd(~F, a, _)
  h

# Radii fitted to n entries
# -------------------------

def rbnd_kfit(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat, d: M.Vec(~F), r: N.KVec(~K), h: C.rbnd(~F, d, N.ofkv(~K, ~F, ~H, r)), hl: {M.len(~F, d) == n : Nat}) -> C.rbnd(~F, d, N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, r))):
  match n d r:
    case 0n Nil{} r:
      Unit{}
    case 0n Con{+a, +ds} r:
      FO.absurd(C.rbnd(~F, Con{a, ds}, N.ofkv(~K, ~F, ~H, KA.kfit(~K, 0n, r))), FV.succ_ne(M.len(~F, ds), hl))
    case 1n++k Nil{} r:
      FO.absurd(C.rbnd(~F, Nil{}, N.ofkv(~K, ~F, ~H, KA.kfit(~K, 1n+k, r))), FV.zero_ne(k, hl))
    case 1n+k Con{+a, +ds} Nil{}:
      (ha, hds) = h
      (rbnd_e0(~K, ~F, ~H, a, ha), rbnd_kfit(~K, ~F, ~H, k, ds, Nil{}, hds, FV.succ_inj(M.len(~F, ds), k, hl)))
    case 1n+k Con{+a, +ds} Con{x, xs}:
      (ha, hds) = h
      (ha, rbnd_kfit(~K, ~F, ~H, k, ds, xs, hds, FV.succ_inj(M.len(~F, ds), k, hl)))

def rnn_kfit(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat, r: N.KVec(~K), h: FV.rnn(~F, N.ofkv(~K, ~F, ~H, r))) -> FV.rnn(~F, N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, r))):
  match n r:
    case 0n r:
      Unit{}
    case 1n+k Nil{}:
      (KB.e0_nonneg(~K, ~F, ~H), rnn_kfit(~K, ~F, ~H, k, Nil{}, Unit{}))
    case 1n+k Con{x, xs}:
      (hx, hxs) = h
      (hx, rnn_kfit(~K, ~F, ~H, k, xs, hxs))

# From entrywise bounds to the checker's box
# ------------------------------------------

def sub0_eq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: O.C(F)) -> {a == O.sub(~F, a, N.emap(K, F, H, N.nzero(K))) : O.C(F)}:
  %KA.ez(~K, ~F, ~H) : {a == O.sub(~F, a, _) : O.C(F)}
  FR.fring_eq(~F, [a], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==})

def neg_eq(~F: O.OField, +c: O.C(F)) -> {O.neg(F, c) == O.sub(~F, O.zero(F), c) : O.C(F)}:
  FR.fring_eq(~F, [c], E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{0n}}, {==})

def rbnd_vnil(~F: O.OField, +u: M.Vec(~F), +r: M.Vec(~F), h: C.rbnd(~F, u, r)) -> C.rbnd(~F, C.vsub(~F, u, Nil{}), r):
  %FV.vadd_nil_r(~F, u) : C.rbnd(~F, _, r)
  h

# |0 - H 0| <= s, for 0 <= s
def rbnd_e0z(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +s: O.C(F), hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, O.sub(~F, O.zero(F), N.emap(K, F, H, N.nzero(K))), s):
  %KA.ez(~K, ~F, ~H) : M.bnd(~F, O.sub(~F, O.zero(F), _), s)
  FV.bnd_sself(~F, O.zero(F), s, hs)

# |u - c| <= r entrywise puts u in the box of balls (c_i, r_i)
def rbnd_inbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: M.Vec(~F), cs: N.KVec(~K), rs: N.KVec(~K), h: C.rbnd(~F, C.vsub(~F, u, N.ofkv(~K, ~F, ~H, cs)), N.ofkv(~K, ~F, ~H, rs)), hn: FV.rnn(~F, N.ofkv(~K, ~F, ~H, rs))) -> KB.inbox(~K, ~F, ~H, u, CK.zipb(~K, cs, rs)):
  match u cs rs:
    case Nil{} Nil{} Nil{}:
      Unit{}
    case Nil{} Nil{} Con{+r, rt}:
      (hr, hrt) = hn
      (rbnd_e0z(~K, ~F, ~H, N.emap(K, F, H, r), hr), rbnd_inbox(~K, ~F, ~H, Nil{}, Nil{}, rt, Unit{}, hrt))
    case Nil{} Con{+c, ct} Nil{}:
      (hc, hct) = h
      (rbnd_e0(~K, ~F, ~H, O.sub(~F, O.zero(F), N.emap(K, F, H, c)), KB.bnd_val(~F, O.neg(F, N.emap(K, F, H, c)), O.sub(~F, O.zero(F), N.emap(K, F, H, c)), O.zero(F), neg_eq(~F, N.emap(K, F, H, c)), hc)), rbnd_inbox(~K, ~F, ~H, Nil{}, ct, Nil{}, hct, Unit{}))
    case Nil{} Con{+c, ct} Con{+r, rt}:
      (hc, hct) = h
      (hr, hrt) = hn
      (KB.bnd_val(~F, O.neg(F, N.emap(K, F, H, c)), O.sub(~F, O.zero(F), N.emap(K, F, H, c)), N.emap(K, F, H, r), neg_eq(~F, N.emap(K, F, H, c)), hc), rbnd_inbox(~K, ~F, ~H, Nil{}, ct, rt, hct, hrt))
    case Con{+a, +as} Nil{} Nil{}:
      (ha, has) = h
      (rbnd_e0(~K, ~F, ~H, O.sub(~F, a, N.emap(K, F, H, N.nzero(K))), KB.bnd_val(~F, a, O.sub(~F, a, N.emap(K, F, H, N.nzero(K))), O.zero(F), sub0_eq(~K, ~F, ~H, a), ha)), rbnd_inbox(~K, ~F, ~H, as, Nil{}, Nil{}, rbnd_vnil(~F, as, Nil{}, has), Unit{}))
    case Con{+a, +as} Nil{} Con{+r, +rt}:
      (ha, has) = h
      (hr, hrt) = hn
      (KB.bnd_val(~F, a, O.sub(~F, a, N.emap(K, F, H, N.nzero(K))), N.emap(K, F, H, r), sub0_eq(~K, ~F, ~H, a), ha), rbnd_inbox(~K, ~F, ~H, as, Nil{}, rt, rbnd_vnil(~F, as, N.ofkv(~K, ~F, ~H, rt), has), hrt))
    case Con{+a, +as} Con{+c, ct} Nil{}:
      (ha, has) = h
      (rbnd_e0(~K, ~F, ~H, O.sub(~F, a, N.emap(K, F, H, c)), ha), rbnd_inbox(~K, ~F, ~H, as, ct, Nil{}, has, Unit{}))
    case Con{+a, +as} Con{+c, ct} Con{+r, rt}:
      (ha, has) = h
      (hr, hrt) = hn
      (ha, rbnd_inbox(~K, ~F, ~H, as, ct, rt, has, hrt))

# u ++ w in the concatenated box, for u in the first part and w in the rest
def inbox_app(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: M.Vec(~F), +w: M.Vec(~F), cs: N.KVec(~K), +cs2: N.KVec(~K), rs: N.KVec(~K), +rs2: N.KVec(~K), hu: KB.inbox(~K, ~F, ~H, u, CK.zipb(~K, cs, rs)), hw: KB.inbox(~K, ~F, ~H, w, CK.zipb(~K, cs2, rs2)), hl1: {M.len(~F, u) == KA.klen(~K, cs) : Nat}, hl2: {KA.klen(~K, cs) == KA.klen(~K, rs) : Nat}) -> KB.inbox(~K, ~F, ~H, C.app(~F, u, w), CK.zipb(~K, KA.kapp(~K, cs, cs2), KA.kapp(~K, rs, rs2))):
  match u cs rs:
    case Nil{} Nil{} Nil{}:
      hw
    case Nil{} Nil{} Con{+r, +rt}:
      FO.absurd(KB.inbox(~K, ~F, ~H, w, CK.zipb(~K, cs2, KA.kapp(~K, Con{r, rt}, rs2))), FV.zero_ne(KA.klen(~K, rt), hl2))
    case Nil{} Con{+c, +ct} rs:
      FO.absurd(KB.inbox(~K, ~F, ~H, w, CK.zipb(~K, KA.kapp(~K, Con{c, ct}, cs2), KA.kapp(~K, rs, rs2))), FV.zero_ne(KA.klen(~K, ct), hl1))
    case Con{+a, +as} Nil{} rs:
      FO.absurd(KB.inbox(~K, ~F, ~H, Con{a, C.app(~F, as, w)}, CK.zipb(~K, cs2, KA.kapp(~K, rs, rs2))), FV.succ_ne(M.len(~F, as), hl1))
    case Con{+a, +as} Con{+c, +ct} Nil{}:
      FO.absurd(KB.inbox(~K, ~F, ~H, Con{a, C.app(~F, as, w)}, CK.zipb(~K, Con{c, KA.kapp(~K, ct, cs2)}, rs2)), FV.succ_ne(KA.klen(~K, ct), hl2))
    case Con{+a, +as} Con{+c, +ct} Con{+r, +rt}:
      (hu1, hus) = hu
      (hu1, inbox_app(~K, ~F, ~H, as, w, ct, cs2, rt, rs2, hus, hw, FV.succ_inj(M.len(~F, as), KA.klen(~K, ct), hl1), FV.succ_inj(KA.klen(~K, ct), KA.klen(~K, rt), hl2)))

# a point of the unknowns' box, followed by pinned parameters, lies in the
# checker's box
def box_in(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +n: Nat, +y: M.Vec(~F), +z: M.Vec(~F), +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), hy: C.rbnd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, yc)), N.ofkv(~K, ~F, ~H, yr)), +hly: {M.len(~F, y) == n : Nat}, +hyc: {KA.klen(~K, yc) == n : Nat}, hnr: FV.rnn(~F, N.ofkv(~K, ~F, ~H, yr)), hz: C.rbnd(~F, C.vsub(~F, z, N.ofkv(~K, ~F, ~H, pc)), N.ofkv(~K, ~F, ~H, pr)), hnp: FV.rnn(~F, N.ofkv(~K, ~F, ~H, pr))) -> KB.inbox(~K, ~F, ~H, C.app(~F, C.fit(~F, n, y), z), CK.box(~K, n, yc, yr, pc, pr)):
  %Equal.sym(M.Vec(~F), C.fit(~F, n, y), y, FV.fit_len(~F, n, y, hly)) : KB.inbox(~K, ~F, ~H, C.app(~F, _, z), CK.box(~K, n, yc, yr, pc, pr))
  inbox_app(~K, ~F, ~H, y, z, yc, pc, KA.kfit(~K, n, yr), pr,
    rbnd_inbox(~K, ~F, ~H, y, yc, KA.kfit(~K, n, yr), rbnd_kfit(~K, ~F, ~H, n, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, yc)), yr, hy, len_vsub(~F, y, N.ofkv(~K, ~F, ~H, yc), n, hly, Equal.trans(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, yc)), KA.klen(~K, yc), n, len_ofkv(~K, ~F, ~H, yc), hyc))), rnn_kfit(~K, ~F, ~H, n, yr, hnr)),
    rbnd_inbox(~K, ~F, ~H, z, pc, pr, hz, hnp),
    Equal.trans(Nat, M.len(~F, y), n, KA.klen(~K, yc), hly, Equal.sym(Nat, KA.klen(~K, yc), n, hyc)),
    Equal.trans(Nat, KA.klen(~K, yc), n, KA.klen(~K, KA.kfit(~K, n, yr)), hyc, Equal.sym(Nat, KA.klen(~K, KA.kfit(~K, n, yr)), n, klen_kfit(~K, n, yr))))

# Slope rows of a block
# ---------------------

def smat(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat) -> M.Mat(~F):
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{SL.srange(~F, x1, x2, e, cnt, lo), smat(~F, x1, x2, es, cnt, lo)}

def len_srange(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +e: E.QExpr, cnt: Nat, +lo: Nat) -> {M.len(~F, SL.srange(~F, x1, x2, e, cnt, lo)) == cnt : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, M.len(~F, SL.srange(~F, x1, x2, e, k, 1n+lo)), k, len_srange(~F, x1, x2, e, k, 1n+lo)) : {1n+_ == 1n+k : Nat}
      {==}

# the slopes in n + p variables are those in the first n, then the next p
def srange_app(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +e: E.QExpr, n: Nat, +p: Nat, +lo: Nat) -> {SL.srange(~F, x1, x2, e, Nat.add(n, p), lo) == C.app(~F, SL.srange(~F, x1, x2, e, n, lo), SL.srange(~F, x1, x2, e, p, Nat.add(n, lo))) : M.Vec(~F)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(M.Vec(~F), SL.srange(~F, x1, x2, e, Nat.add(k, p), 1n+lo), C.app(~F, SL.srange(~F, x1, x2, e, k, 1n+lo), SL.srange(~F, x1, x2, e, p, Nat.add(k, 1n+lo))), srange_app(~F, x1, x2, e, k, p, 1n+lo)) : {Con{SL.sl(~F, lo, x1, x2, e), _} == Con{SL.sl(~F, lo, x1, x2, e), C.app(~F, SL.srange(~F, x1, x2, e, k, 1n+lo), SL.srange(~F, x1, x2, e, p, 1n+Nat.add(k, lo)))} : M.Vec(~F)}
      %LN.add_succ(k, lo) : {Con{SL.sl(~F, lo, x1, x2, e), C.app(~F, SL.srange(~F, x1, x2, e, k, 1n+lo), SL.srange(~F, x1, x2, e, p, _))} == Con{SL.sl(~F, lo, x1, x2, e), C.app(~F, SL.srange(~F, x1, x2, e, k, 1n+lo), SL.srange(~F, x1, x2, e, p, 1n+Nat.add(k, lo)))} : M.Vec(~F)}
      {==}

# e(u1 ++ z1) - e(u2 ++ z2) = sy . (u1 - u2) + sz . (z1 - z2)
def eq_slope(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z1: M.Vec(~F), +z2: M.Vec(~F), +e: E.QExpr, +n: Nat, +p: Nat, hb: {SL.below(Nat.add(n, p), e) == True{} : Bool}, +h1: {M.len(~F, u1) == n : Nat}, +h2: {M.len(~F, u2) == n : Nat}) -> {O.sub(~F, O.eval(~F, C.app(~F, u1, z1), e), O.eval(~F, C.app(~F, u2, z2), e)) == O.add(F, M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, n, 0n), C.vsub(~F, u1, u2)), M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, p, Nat.add(n, 0n)), C.vsub(~F, z1, z2))) : O.C(F)}:
  +x1 = C.app(~F, u1, z1)
  +x2 = C.app(~F, u2, z2)
  %FV.dot_app(~F, SL.srange(~F, x1, x2, e, n, 0n), SL.srange(~F, x1, x2, e, p, Nat.add(n, 0n)), C.vsub(~F, u1, u2), C.vsub(~F, z1, z2), Equal.trans(Nat, M.len(~F, SL.srange(~F, x1, x2, e, n, 0n)), n, M.len(~F, C.vsub(~F, u1, u2)), len_srange(~F, x1, x2, e, n, 0n), Equal.sym(Nat, M.len(~F, C.vsub(~F, u1, u2)), n, len_vsub(~F, u1, u2, n, h1, h2)))) : {O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)) == _ : O.C(F)}
  %FV.vsub_app(~F, u1, u2, z1, z2, Equal.trans(Nat, M.len(~F, u1), n, M.len(~F, u2), h1, Equal.sym(Nat, M.len(~F, u2), n, h2))) : {O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)) == M.dot(~F, C.app(~F, SL.srange(~F, x1, x2, e, n, 0n), SL.srange(~F, x1, x2, e, p, Nat.add(n, 0n))), _) : O.C(F)}
  %srange_app(~F, x1, x2, e, n, p, 0n) : {O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)) == M.dot(~F, _, C.vsub(~F, x1, x2)) : O.C(F)}
  SL.slope_ok(~F, x1, x2, e, Nat.add(n, p), hb)

# a + b = a, for 0 = b
def zero_tail(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {O.zero(F) == b : O.C(F)}) -> {O.add(F, a, b) == a : O.C(F)}:
  %h : {O.add(F, a, _) == a : O.C(F)}
  O.add_zero(F)(a)

# with the same parameters, e(u1 ++ z) - e(u2 ++ z) = sy . (u1 - u2)
def eq_slope_con(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z: M.Vec(~F), +e: E.QExpr, +n: Nat, +p: Nat, hb: {SL.below(Nat.add(n, p), e) == True{} : Bool}, +h1: {M.len(~F, u1) == n : Nat}, +h2: {M.len(~F, u2) == n : Nat}) -> {O.sub(~F, O.eval(~F, C.app(~F, u1, z), e), O.eval(~F, C.app(~F, u2, z), e)) == M.dot(~F, SL.srange(~F, C.app(~F, u1, z), C.app(~F, u2, z), e, n, 0n), C.vsub(~F, u1, u2)) : O.C(F)}:
  +x1 = C.app(~F, u1, z)
  +x2 = C.app(~F, u2, z)
  +sy = M.dot(~F, SL.srange(~F, x1, x2, e, n, 0n), C.vsub(~F, u1, u2))
  Equal.trans(O.C(F), O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), O.add(F, sy, M.dot(~F, SL.srange(~F, x1, x2, e, p, Nat.add(n, 0n)), C.vsub(~F, z, z))), sy,
    eq_slope(~F, u1, u2, z, z, e, n, p, hb, h1, h2),
    zero_tail(~F, sy, M.dot(~F, SL.srange(~F, x1, x2, e, p, Nat.add(n, 0n)), C.vsub(~F, z, z)), FV.dot_self0(~F, SL.srange(~F, x1, x2, e, p, Nat.add(n, 0n)), z)))

# the block's differences, row by row: f(u1; z) - f(u2; z) = S (u1 - u2)
def fvecs_con(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z: M.Vec(~F), eqs: List<&2, E.QExpr>, +n: Nat, +p: Nat, +hb: {CK.allbelow(Nat.add(n, p), eqs) == True{} : Bool}, +h1: {M.len(~F, u1) == n : Nat}, +h2: {M.len(~F, u2) == n : Nat}) -> {C.vsub(~F, C.fvals(~F, eqs, C.app(~F, u1, z)), C.fvals(~F, eqs, C.app(~F, u2, z))) == M.matvec(~F, smat(~F, C.app(~F, u1, z), C.app(~F, u2, z), eqs, n, 0n), C.vsub(~F, u1, u2)) : M.Vec(~F)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      +x1 = C.app(~F, u1, z)
      +x2 = C.app(~F, u2, z)
      %eq_slope_con(~F, u1, u2, z, e, n, p, KA.band_l(SL.below(Nat.add(n, p), e), CK.allbelow(Nat.add(n, p), es), hb), h1, h2) : {Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), C.vsub(~F, C.fvals(~F, es, x1), C.fvals(~F, es, x2))} == Con{_, M.matvec(~F, smat(~F, x1, x2, es, n, 0n), C.vsub(~F, u1, u2))} : M.Vec(~F)}
      %fvecs_con(~F, u1, u2, z, es, n, p, KA.band_r(SL.below(Nat.add(n, p), e), CK.allbelow(Nat.add(n, p), es), hb), h1, h2) : {Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), C.vsub(~F, C.fvals(~F, es, x1), C.fvals(~F, es, x2))} == Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), _} : M.Vec(~F)}
      {==}
