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

# Slope enclosures as matrix bounds
# ---------------------------------

def bin_cr(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), b: KB.KB<K>, h: KB.bin(~K, ~F, ~H, x, b)) -> M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, KB.KB.c(K, b))), N.emap(K, F, H, KB.KB.r(K, b))):
  match b:
    case KB.KB{c, r}:
      h

# |S - J| <= D along one row of slopes
def row_bnd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat, h: KB.inbox(~K, ~F, ~H, SL.srange(~F, x1, x2, e, cnt, lo), KB.krange(~K, box, e, cnt, lo))) -> C.rbnd(~F, C.vsub(~F, SL.srange(~F, x1, x2, e, cnt, lo), N.ofkv(~K, ~F, ~H, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo)))), N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo)))):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (h0, hs) = h
      (bin_cr(~K, ~F, ~H, SL.sl(~F, lo, x1, x2, e), KB.ksl(~K, lo, box, e), h0), row_bnd(~K, ~F, ~H, x1, x2, box, e, k, 1n+lo, hs))

def row_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat, h: KB.inbox(~K, ~F, ~H, SL.srange(~F, x1, x2, e, cnt, lo), KB.krange(~K, box, e, cnt, lo))) -> FV.rnn(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo)))):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (h0, hs) = h
      (FM.bnd_nonneg(~F, O.sub(~F, SL.sl(~F, lo, x1, x2, e), N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, lo, box, e)))), N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), bin_cr(~K, ~F, ~H, SL.sl(~F, lo, x1, x2, e), KB.ksl(~K, lo, box, e), h0)), row_nn(~K, ~F, ~H, x1, x2, box, e, k, 1n+lo, hs))

# |S - J| <= D for the whole block, and D >= 0
def mat_bnd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat, +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box)) -> FV.mbnd(~F, M.madd(~F, smat(~F, x1, x2, eqs, cnt, lo), M.mneg(~F, N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))))), N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs)))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      (row_bnd(~K, ~F, ~H, x1, x2, box, e, cnt, lo, KB.range_ok(~K, ~F, ~H, x1, x2, box, e, KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2, cnt, lo)), mat_bnd(~K, ~F, ~H, x1, x2, box, es, cnt, lo, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2))

def mat_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat, +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box)) -> FV.mnn(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs)))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      (row_nn(~K, ~F, ~H, x1, x2, box, e, cnt, lo, KB.range_ok(~K, ~F, ~H, x1, x2, box, e, KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2, cnt, lo)), mat_nn(~K, ~F, ~H, x1, x2, box, es, cnt, lo, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2))

# The checker's matrices in F
# ---------------------------

# (I - Y J) d = d - Y (J d), for d of length n
def imm_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +n: Nat, +ym: N.KMat(~K), +j: N.KMat(~K), +d: M.Vec(~F), hl: {M.len(~F, d) == n : Nat}) -> {M.matvec(~F, N.ofkm(~K, ~F, ~H, CK.imm(~K, n, ym, j)), d) == C.vsub(~F, d, M.matvec(~F, N.ofkm(~K, ~F, ~H, ym), M.matvec(~F, N.ofkm(~K, ~F, ~H, j), d))) : M.Vec(~F)}:
  +y = N.ofkm(~K, ~F, ~H, ym)
  +jf = N.ofkm(~K, ~F, ~H, j)
  +rhs = C.vsub(~F, d, M.matvec(~F, y, M.matvec(~F, jf, d)))
  %KA.kmadd_ofk(~K, ~F, ~H, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, ym, j))) : {M.matvec(~F, _, d) == rhs : M.Vec(~F)}
  %KA.kident_ofk(~K, ~F, ~H, n) : {M.matvec(~F, M.madd(~F, _, N.ofkm(~K, ~F, ~H, KA.kmneg(~K, KA.kmatmul(~K, ym, j)))), d) == rhs : M.Vec(~F)}
  %KA.kmneg_ofk(~K, ~F, ~H, KA.kmatmul(~K, ym, j)) : {M.matvec(~F, M.madd(~F, M.ident(~F, n), _), d) == rhs : M.Vec(~F)}
  %KA.kmatmul_ofk(~K, ~F, ~H, ym, j) : {M.matvec(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, _)), d) == rhs : M.Vec(~F)}
  %FM.mat_add(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, y, jf)), d) : {_ == rhs : M.Vec(~F)}
  %FM.mat_neg(~F, M.matmul(~F, y, jf), d) : {M.vadd(~F, M.matvec(~F, M.ident(~F, n), d), _) == rhs : M.Vec(~F)}
  %FM.mat_assoc(~F, y, jf, d) : {M.vadd(~F, M.matvec(~F, M.ident(~F, n), d), M.vneg(~F, _)) == rhs : M.Vec(~F)}
  %hl : {M.vadd(~F, M.matvec(~F, M.ident(~F, _), d), M.vneg(~F, M.matvec(~F, y, M.matvec(~F, jf, d)))) == rhs : M.Vec(~F)}
  %FM.mat_ident(~F, d) : {M.vadd(~F, _, M.vneg(~F, M.matvec(~F, y, M.matvec(~F, jf, d)))) == rhs : M.Vec(~F)}
  {==}

# (S - J) d = S d - J d
def sj_ok(~F: O.OField, +s: M.Mat(~F), +j: M.Mat(~F), +d: M.Vec(~F)) -> {M.matvec(~F, M.madd(~F, s, M.mneg(~F, j)), d) == C.vsub(~F, M.matvec(~F, s, d), M.matvec(~F, j, d)) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), M.vneg(~F, M.matvec(~F, j, d)), M.matvec(~F, M.mneg(~F, j), d), FM.mat_neg(~F, j, d)) : {M.matvec(~F, M.madd(~F, s, M.mneg(~F, j)), d) == M.vadd(~F, M.matvec(~F, s, d), _) : M.Vec(~F)}
  Equal.sym(M.Vec(~F), M.vadd(~F, M.matvec(~F, s, d), M.matvec(~F, M.mneg(~F, j), d)), M.matvec(~F, M.madd(~F, s, M.mneg(~F, j)), d), FM.mat_add(~F, s, M.mneg(~F, j), d))

def rows_ofkm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> {FV.rows(~F, N.ofkm(~K, ~F, ~H, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %rows_ofkm(~K, ~F, ~H, rs) : {1n+FV.rows(~F, N.ofkm(~K, ~F, ~H, rs)) == 1n+_ : Nat}
      {==}

# the checker's G r, read in F
def gF_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {N.ofkv(~K, ~F, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr)) == M.vadd(~F, M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))))), N.ofkv(~K, ~F, ~H, yr)), M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, ym)), M.matvec(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))), N.ofkv(~K, ~F, ~H, yr)))) : M.Vec(~F)}:
  +aa = KA.kmabs(~K, CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))))
  +ay = KA.kmabs(~K, ym)
  +dd = CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))
  +lhs = N.ofkv(~K, ~F, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr))
  %Equal.sym(M.Vec(~F), M.matvec(~F, N.ofkm(~K, ~F, ~H, dd), N.ofkv(~K, ~F, ~H, yr)), N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, dd, yr)), KA.kmatvec_ofk(~K, ~F, ~H, dd, yr)) : {lhs == M.vadd(~F, M.matvec(~F, N.ofkm(~K, ~F, ~H, aa), N.ofkv(~K, ~F, ~H, yr)), M.matvec(~F, N.ofkm(~K, ~F, ~H, ay), _)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), M.matvec(~F, N.ofkm(~K, ~F, ~H, ay), N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, dd, yr))), N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, ay, KA.kmatvec(~K, dd, yr))), KA.kmatvec_ofk(~K, ~F, ~H, ay, KA.kmatvec(~K, dd, yr))) : {lhs == M.vadd(~F, M.matvec(~F, N.ofkm(~K, ~F, ~H, aa), N.ofkv(~K, ~F, ~H, yr)), _) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), M.matvec(~F, N.ofkm(~K, ~F, ~H, aa), N.ofkv(~K, ~F, ~H, yr)), N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, aa, yr)), KA.kmatvec_ofk(~K, ~F, ~H, aa, yr)) : {lhs == M.vadd(~F, _, N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, ay, KA.kmatvec(~K, dd, yr)))) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), M.vadd(~F, N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, aa, yr)), N.ofkv(~K, ~F, ~H, KA.kmatvec(~K, ay, KA.kmatvec(~K, dd, yr)))), N.ofkv(~K, ~F, ~H, KA.kvadd(~K, KA.kmatvec(~K, aa, yr), KA.kmatvec(~K, ay, KA.kmatvec(~K, dd, yr)))), KA.kvadd_ofk(~K, ~F, ~H, KA.kmatvec(~K, aa, yr), KA.kmatvec(~K, ay, KA.kmatvec(~K, dd, yr)))) : {lhs == _ : M.Vec(~F)}
  {==}

# a bound on y1 - y2 is one on their fits to n entries, for y1, y2 of length n
def fit_rbnd(~F: O.OField, +n: Nat, +y1: M.Vec(~F), +y2: M.Vec(~F), +r: M.Vec(~F), +h1: {M.len(~F, y1) == n : Nat}, +h2: {M.len(~F, y2) == n : Nat}, h: C.rbnd(~F, C.vsub(~F, y1, y2), r)) -> C.rbnd(~F, C.vsub(~F, C.fit(~F, n, y1), C.fit(~F, n, y2)), r):
  %Equal.sym(M.Vec(~F), C.fit(~F, n, y1), y1, FV.fit_len(~F, n, y1, h1)) : C.rbnd(~F, C.vsub(~F, _, C.fit(~F, n, y2)), r)
  %Equal.sym(M.Vec(~F), C.fit(~F, n, y2), y2, FV.fit_len(~F, n, y2, h2)) : C.rbnd(~F, C.vsub(~F, y1, _), r)
  h

# d - Y u = d - Y u2, for u = u2
def sub_rw(~F: O.OField, +d: M.Vec(~F), +y: M.Mat(~F), +u: M.Vec(~F), +u2: M.Vec(~F), e: {u2 == u : M.Vec(~F)}) -> {C.vsub(~F, d, M.matvec(~F, y, u)) == C.vsub(~F, d, M.matvec(~F, y, u2)) : M.Vec(~F)}:
  %e : {C.vsub(~F, d, M.matvec(~F, y, _)) == C.vsub(~F, d, M.matvec(~F, y, u2)) : M.Vec(~F)}
  {==}

# back from the fits to the vectors themselves, outside f
def unfit2(~F: O.OField, +n: Nat, +y1: M.Vec(~F), +y2: M.Vec(~F), +a1: M.Vec(~F), +a2: M.Vec(~F), +r: M.Vec(~F), +h1: {M.len(~F, y1) == n : Nat}, +h2: {M.len(~F, y2) == n : Nat}, h: C.rbnd(~F, C.vsub(~F, C.vsub(~F, C.fit(~F, n, y1), a1), C.vsub(~F, C.fit(~F, n, y2), a2)), r)) -> C.rbnd(~F, C.vsub(~F, C.vsub(~F, y1, a1), C.vsub(~F, y2, a2)), r):
  %FV.fit_len(~F, n, y1, h1) : C.rbnd(~F, C.vsub(~F, C.vsub(~F, _, a1), C.vsub(~F, y2, a2)), r)
  %FV.fit_len(~F, n, y2, h2) : C.rbnd(~F, C.vsub(~F, C.vsub(~F, C.fit(~F, n, y1), a1), C.vsub(~F, _, a2)), r)
  h

# The contraction
# ---------------

# with z pinned and y1, y2 in the box within s radii of each other, the
# Newton images are within q s radii
def contract.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}, +z: M.Vec(~F), +hz: C.rbnd(~F, C.vsub(~F, z, N.ofkv(~K, ~F, ~H, pc)), N.ofkv(~K, ~F, ~H, pr)), +y1: M.Vec(~F), +hl1: {M.len(~F, y1) == M.len(~F, N.ofkv(~K, ~F, ~H, yc)) : Nat}, +hb1: C.rbnd(~F, C.vsub(~F, y1, N.ofkv(~K, ~F, ~H, yc)), N.ofkv(~K, ~F, ~H, yr)), +y2: M.Vec(~F), +hl2: {M.len(~F, y2) == M.len(~F, N.ofkv(~K, ~F, ~H, yc)) : Nat}, +hb2: C.rbnd(~F, C.vsub(~F, y2, N.ofkv(~K, ~F, ~H, yc)), N.ofkv(~K, ~F, ~H, yr)), +s: O.C(F), +hs0: O.le(~F, O.zero(F), s), +hs: C.rbnd(~F, C.vsub(~F, y1, y2), M.vscale(~F, s, N.ofkv(~K, ~F, ~H, yr)))) -> C.rbnd(~F, C.vsub(~F, C.vsub(~F, y1, M.matvec(~F, N.ofkm(~K, ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, C.fit(~F, n, y1), z)))), C.vsub(~F, y2, M.matvec(~F, N.ofkm(~K, ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, C.fit(~F, n, y2), z))))), M.vscale(~F, O.mul(F, N.emap(K, F, H, q), s), N.ofkv(~K, ~F, ~H, yr))):
  +p = KA.klen(~K, pc)
  +box = CK.box(~K, n, yc, yr, pc, pr)
  +yF = N.ofkm(~K, ~F, ~H, ym)
  +rF = N.ofkv(~K, ~F, ~H, yr)
  +qF = N.emap(K, F, H, q)
  +rowsK = CK.srows(~K, box, n, 0n, eqs)
  +jK = CK.mcenters(~K, rowsK)
  +dK = CK.mradii(~K, rowsK)
  +jF = N.ofkm(~K, ~F, ~H, jK)
  +dF = N.ofkm(~K, ~F, ~H, dK)
  +aK = CK.imm(~K, n, ym, jK)
  +u1 = C.fit(~F, n, y1)
  +u2 = C.fit(~F, n, y2)
  +x1 = C.app(~F, u1, z)
  +x2 = C.app(~F, u2, z)
  +f1 = C.fvals(~F, eqs, x1)
  +f2 = C.fvals(~F, eqs, x2)
  +sF = smat(~F, x1, x2, eqs, n, 0n)
  +d = C.vsub(~F, u1, u2)
  +w = M.vscale(~F, s, rF)
  +r1 = M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, aK)), w)
  +r2 = M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, ym)), M.matvec(~F, dF, w))
  +hyc = nateq_ok(KA.klen(~K, yc), n, x_len_yc(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))
  +hly1 = Equal.trans(Nat, M.len(~F, y1), M.len(~F, N.ofkv(~K, ~F, ~H, yc)), n, hl1, Equal.trans(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, yc)), KA.klen(~K, yc), n, len_ofkv(~K, ~F, ~H, yc), hyc))
  +hly2 = Equal.trans(Nat, M.len(~F, y2), M.len(~F, N.ofkv(~K, ~F, ~H, yc)), n, hl2, Equal.trans(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, yc)), KA.klen(~K, yc), n, len_ofkv(~K, ~F, ~H, yc), hyc))
  +hnr = KA.kvle_ok(~K, ~F, ~H, Nil{}, yr, x_nn_yr(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))
  +hnp = KA.kvle_ok(~K, ~F, ~H, Nil{}, pr, x_nn_pr(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))
  +hh = x_held(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)
  +in1 = box_in(~K, ~F, ~H, n, y1, z, yc, yr, pc, pr, hb1, hly1, hyc, hnr, hz, hnp)
  +in2 = box_in(~K, ~F, ~H, n, y2, z, yc, yr, pc, pr, hb2, hly2, hyc, hnr, hz, hnp)
  +hlu1 = FV.len_fit(~F, n, y1)
  +hlu2 = FV.len_fit(~F, n, y2)
  +hdl = len_vsub(~F, u1, u2, n, hlu1, hlu2)
  +hd = fit_rbnd(~F, n, y1, y2, w, hly1, hly2, hs)
  +hw = FV.rnn_scale(~F, s, hs0, rF, hnr)
  +hmb = mat_bnd(~K, ~F, ~H, x1, x2, box, eqs, n, 0n, hh, in1, in2)
  +hmn = mat_nn(~K, ~F, ~H, x1, x2, box, eqs, n, 0n, hh, in1, in2)
  +p1 = FV.rbnd_rw(~F, M.matvec(~F, N.ofkm(~K, ~F, ~H, aK), d), C.vsub(~F, d, M.matvec(~F, yF, M.matvec(~F, jF, d))), r1, imm_ok(~K, ~F, ~H, n, ym, jK, d, hdl), FV.mbnd_matvec(~F, N.ofkm(~K, ~F, ~H, aK), N.ofkm(~K, ~F, ~H, KA.kmabs(~K, aK)), d, w, KA.kmabs_bnd(~K, ~F, ~H, aK), hd, KA.kmabs_nn(~K, ~F, ~H, aK), hw))
  +p2a = FV.rbnd_rw(~F, M.matvec(~F, M.madd(~F, sF, M.mneg(~F, jF)), d), C.vsub(~F, M.matvec(~F, sF, d), M.matvec(~F, jF, d)), M.matvec(~F, dF, w), sj_ok(~F, sF, jF, d), FV.mbnd_matvec(~F, M.madd(~F, sF, M.mneg(~F, jF)), dF, d, w, hmb, hd, hmn, hw))
  +p2 = FV.mbnd_matvec(~F, yF, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, ym)), C.vsub(~F, M.matvec(~F, sF, d), M.matvec(~F, jF, d)), M.matvec(~F, dF, w), KA.kmabs_bnd(~K, ~F, ~H, ym), p2a, KA.kmabs_nn(~K, ~F, ~H, ym), FV.matvec_nonneg(~F, dF, w, hmn, hw))
  +hrows = Equal.trans(Nat, M.len(~F, d), n, FV.rows(~F, yF), hdl, Equal.sym(Nat, FV.rows(~F, yF), n, Equal.trans(Nat, FV.rows(~F, yF), CK.mlen(~K, ym), n, rows_ofkm(~K, ~F, ~H, ym), nateq_ok(CK.mlen(~K, ym), n, x_len_ym(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)))))
  +p3 = FV.split_bnd(~F, d, yF, M.matvec(~F, sF, d), M.matvec(~F, jF, d), r1, r2, hrows, p1, p2)
  +hfd = fvecs_con(~F, u1, u2, z, eqs, n, p, x_below(~K, eqs, n, yc, yr, q, ym, pc, pr, ok), hlu1, hlu2)
  +p4 = FV.rbnd_rw(~F, C.vsub(~F, d, M.matvec(~F, yF, M.matvec(~F, sF, d))), C.vsub(~F, d, M.matvec(~F, yF, C.vsub(~F, f1, f2))), M.vadd(~F, r1, r2), sub_rw(~F, d, yF, M.matvec(~F, sF, d), C.vsub(~F, f1, f2), hfd), p3)
  +p5 = FV.newton_diff(~F, u1, u2, yF, f1, f2, M.vadd(~F, r1, r2), Equal.trans(Nat, M.len(~F, u1), n, M.len(~F, u2), hlu1, Equal.sym(Nat, M.len(~F, u2), n, hlu2)), Equal.trans(Nat, M.len(~F, u2), n, FV.rows(~F, yF), hlu2, Equal.sym(Nat, FV.rows(~F, yF), n, Equal.trans(Nat, FV.rows(~F, yF), CK.mlen(~K, ym), n, rows_ofkm(~K, ~F, ~H, ym), nateq_ok(CK.mlen(~K, ym), n, x_len_ym(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))))), p4)
  +gF = M.vadd(~F, M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, aK)), rF), M.matvec(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, ym)), M.matvec(~F, dF, rF)))
  +hg = FV.rle_rw(~F, N.ofkv(~K, ~F, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr)), gF, N.ofkv(~K, ~F, ~H, KA.kvscale(~K, q, yr)), M.vscale(~F, qF, rF), gF_ok(~K, ~F, ~H, eqs, n, yc, yr, ym, pc, pr), Equal.sym(M.Vec(~F), M.vscale(~F, qF, rF), N.ofkv(~K, ~F, ~H, KA.kvscale(~K, q, yr)), KA.kvscale_ofk(~K, ~F, ~H, q, yr)), KA.kvle_ok(~K, ~F, ~H, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr), KA.kvscale(~K, q, yr), x_con(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)))
  +p6 = FV.rle_rw(~F, M.vscale(~F, s, gF), M.vadd(~F, r1, r2), M.vscale(~F, s, M.vscale(~F, qF, rF)), M.vscale(~F, O.mul(F, qF, s), rF), Equal.sym(M.Vec(~F), M.vadd(~F, r1, r2), M.vscale(~F, s, gF), FV.r12_ok(~F, s, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, aK)), N.ofkm(~K, ~F, ~H, KA.kmabs(~K, ym)), dF, rF)), FV.vscale2(~F, qF, s, rF), FV.rle_scale(~F, s, hs0, gF, M.vscale(~F, qF, rF), hg))
  +p7 = FV.rbnd_mono(~F, C.vsub(~F, C.vsub(~F, u1, M.matvec(~F, yF, f1)), C.vsub(~F, u2, M.matvec(~F, yF, f2))), M.vadd(~F, r1, r2), M.vscale(~F, O.mul(F, qF, s), rF), p5, p6)
  unfit2(~F, n, y1, y2, M.matvec(~F, yF, f1), M.matvec(~F, yF, f2), M.vscale(~F, O.mul(F, qF, s), rF), hly1, hly2, p7)

def cert_contract.c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>, ok: {CK.check.c(~K, eqs, n, c) == True{} : Bool}, +z: M.Vec(~F), hz: C.pinned(~K, ~F, ~H, c, z), +y1: M.Vec(~F), h1: C.ball(~K, ~F, ~H, c, y1), +y2: M.Vec(~F), h2: C.ball(~K, ~F, ~H, c, y2), +s: O.C(F), hs0: O.le(~F, O.zero(F), s), hs: C.near(~K, ~F, ~H, c, s, y1, y2)) -> C.near(~K, ~F, ~H, c, O.mul(F, C.factor(~K, ~F, ~H, c), s), C.newton(~K, ~F, ~H, C.Block{eqs, n}, c, z, y1), C.newton(~K, ~F, ~H, C.Block{eqs, n}, c, z, y2)):
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      (hl1, hb1) = h1
      (hl2, hb2) = h2
      contract.go(~K, ~F, ~H, eqs, n, yc, yr, q, ym, pc, pr, ok, z, hz, y1, hl1, hb1, y2, hl2, hb2, s, hs0, hs)

# LAW cert_contract: the Newton map contracts the box by q
def cert_contract(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: C.Block, c: C.Cert<K>, ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), hz: C.pinned(~K, ~F, ~H, c, z), +y1: M.Vec(~F), h1: C.ball(~K, ~F, ~H, c, y1), +y2: M.Vec(~F), h2: C.ball(~K, ~F, ~H, c, y2), +s: O.C(F), hs0: O.le(~F, O.zero(F), s), hs: C.near(~K, ~F, ~H, c, s, y1, y2)) -> C.near(~K, ~F, ~H, c, O.mul(F, C.factor(~K, ~F, ~H, c), s), C.newton(~K, ~F, ~H, b, c, z, y1), C.newton(~K, ~F, ~H, b, c, z, y2)):
  match b:
    case C.Block{+eqs, +n}:
      cert_contract.c(~K, ~F, ~H, eqs, n, c, ok, z, hz, y1, h1, y2, h2, s, hs0, hs)

# The equations evaluated in K
# ----------------------------

def klook_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, env: N.KVec(~K), i: Nat) -> {N.emap(K, F, H, KB.klook(~K, env, i)) == O.lookup(~F, N.ofkv(~K, ~F, ~H, env), i) : O.C(F)}:
  match env i:
    case Nil{} j:
      N.e_zero(K, F, H)
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      klook_ofk(~K, ~F, ~H, t, j)

# K's value of a held expression is its value in F
def keval_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +env: N.KVec(~K), e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> {N.emap(K, F, H, KB.keval(~K, env, e)) == O.eval(~F, N.ofkv(~K, ~F, ~H, env), e) : O.C(F)}:
  match e:
    case E.QVar{i}:
      klook_ofk(~K, ~F, ~H, env, i)
    case E.QCst{+q}:
      KB.kcst_ok(~K, ~F, ~H, q, hh)
    case E.QAdd{+a, +b}:
      %KA.ea(~K, ~F, ~H, KB.keval(~K, env, a), KB.keval(~K, env, b)) : {_ == O.add(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, a)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), keval_ok(~K, ~F, ~H, env, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh))) : {O.add(F, _, N.emap(K, F, H, KB.keval(~K, env, b))) == O.add(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, b)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b), keval_ok(~K, ~F, ~H, env, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))) : {O.add(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), _) == O.add(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      {==}
    case E.QSub{+a, +b}:
      %KA.es(~K, ~F, ~H, KB.keval(~K, env, a), KB.keval(~K, env, b)) : {_ == O.sub(~F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, a)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), keval_ok(~K, ~F, ~H, env, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh))) : {O.sub(~F, _, N.emap(K, F, H, KB.keval(~K, env, b))) == O.sub(~F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, b)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b), keval_ok(~K, ~F, ~H, env, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))) : {O.sub(~F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), _) == O.sub(~F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      {==}
    case E.QMul{+a, +b}:
      %KA.em(~K, ~F, ~H, KB.keval(~K, env, a), KB.keval(~K, env, b)) : {_ == O.mul(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, a)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), keval_ok(~K, ~F, ~H, env, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh))) : {O.mul(F, _, N.emap(K, F, H, KB.keval(~K, env, b))) == O.mul(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, b)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b), keval_ok(~K, ~F, ~H, env, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))) : {O.mul(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), _) == O.mul(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), O.eval(~F, N.ofkv(~K, ~F, ~H, env), b)) : O.C(F)}
      {==}
    case E.QNeg{+a}:
      %KA.en(~K, ~F, ~H, KB.keval(~K, env, a)) : {_ == O.neg(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a)) : O.C(F)}
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, a)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), a), keval_ok(~K, ~F, ~H, env, a, hh)) : {O.neg(F, _) == O.neg(F, O.eval(~F, N.ofkv(~K, ~F, ~H, env), a)) : O.C(F)}
      {==}

def kvals_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +env: N.KVec(~K), eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~K, eqs) == True{} : Bool}) -> {N.ofkv(~K, ~F, ~H, CK.kvals(~K, env, eqs)) == C.fvals(~F, eqs, N.ofkv(~K, ~F, ~H, env)) : M.Vec(~F)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.keval(~K, env, e)), O.eval(~F, N.ofkv(~K, ~F, ~H, env), e), keval_ok(~K, ~F, ~H, env, e, KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh))) : {Con{_, N.ofkv(~K, ~F, ~H, CK.kvals(~K, env, es))} == C.fvals(~F, Con{e, es}, N.ofkv(~K, ~F, ~H, env)) : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, CK.kvals(~K, env, es)), C.fvals(~F, es, N.ofkv(~K, ~F, ~H, env)), kvals_ofk(~K, ~F, ~H, env, es, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh))) : {Con{O.eval(~F, N.ofkv(~K, ~F, ~H, env), e), _} == C.fvals(~F, Con{e, es}, N.ofkv(~K, ~F, ~H, env)) : M.Vec(~F)}
      {==}

def kapp_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), +w: N.KVec(~K)) -> {N.ofkv(~K, ~F, ~H, KA.kapp(~K, u, w)) == C.app(~F, N.ofkv(~K, ~F, ~H, u), N.ofkv(~K, ~F, ~H, w)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, KA.kapp(~K, us, w)), C.app(~F, N.ofkv(~K, ~F, ~H, us), N.ofkv(~K, ~F, ~H, w)), kapp_ofk(~K, ~F, ~H, us, w)) : {Con{N.emap(K, F, H, a), _} == Con{N.emap(K, F, H, a), C.app(~F, N.ofkv(~K, ~F, ~H, us), N.ofkv(~K, ~F, ~H, w))} : M.Vec(~F)}
      {==}

# The self-map
# ------------

# e(u1 ++ z1) - e(u2 ++ z2) = sy . (u1 - u2) + sz . (z1 - z2), the
# parameter slopes taken from variable n
def eq_slope_n(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z1: M.Vec(~F), +z2: M.Vec(~F), +e: E.QExpr, +n: Nat, +p: Nat, hb: {SL.below(Nat.add(n, p), e) == True{} : Bool}, +h1: {M.len(~F, u1) == n : Nat}, +h2: {M.len(~F, u2) == n : Nat}) -> {O.sub(~F, O.eval(~F, C.app(~F, u1, z1), e), O.eval(~F, C.app(~F, u2, z2), e)) == O.add(F, M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, n, 0n), C.vsub(~F, u1, u2)), M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, p, n), C.vsub(~F, z1, z2))) : O.C(F)}:
  %Equal.sym(Nat, n, Nat.add(n, 0n), LN.add_zero(n)) : {O.sub(~F, O.eval(~F, C.app(~F, u1, z1), e), O.eval(~F, C.app(~F, u2, z2), e)) == O.add(F, M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, n, 0n), C.vsub(~F, u1, u2)), M.dot(~F, SL.srange(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), e, p, _), C.vsub(~F, z1, z2))) : O.C(F)}
  eq_slope(~F, u1, u2, z1, z2, e, n, p, hb, h1, h2)

# f(u1; z1) - f(u2; z2) = Sy (u1 - u2) + Sz (z1 - z2)
def fvecs_self(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z1: M.Vec(~F), +z2: M.Vec(~F), eqs: List<&2, E.QExpr>, +n: Nat, +p: Nat, +hb: {CK.allbelow(Nat.add(n, p), eqs) == True{} : Bool}, +h1: {M.len(~F, u1) == n : Nat}, +h2: {M.len(~F, u2) == n : Nat}) -> {C.vsub(~F, C.fvals(~F, eqs, C.app(~F, u1, z1)), C.fvals(~F, eqs, C.app(~F, u2, z2))) == M.vadd(~F, M.matvec(~F, smat(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), eqs, n, 0n), C.vsub(~F, u1, u2)), M.matvec(~F, smat(~F, C.app(~F, u1, z1), C.app(~F, u2, z2), eqs, p, n), C.vsub(~F, z1, z2))) : M.Vec(~F)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      +x1 = C.app(~F, u1, z1)
      +x2 = C.app(~F, u2, z2)
      %eq_slope_n(~F, u1, u2, z1, z2, e, n, p, KA.band_l(SL.below(Nat.add(n, p), e), CK.allbelow(Nat.add(n, p), es), hb), h1, h2) : {Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), C.vsub(~F, C.fvals(~F, es, x1), C.fvals(~F, es, x2))} == Con{_, M.vadd(~F, M.matvec(~F, smat(~F, x1, x2, es, n, 0n), C.vsub(~F, u1, u2)), M.matvec(~F, smat(~F, x1, x2, es, p, n), C.vsub(~F, z1, z2)))} : M.Vec(~F)}
      %fvecs_self(~F, u1, u2, z1, z2, es, n, p, KA.band_r(SL.below(Nat.add(n, p), e), CK.allbelow(Nat.add(n, p), es), hb), h1, h2) : {Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), C.vsub(~F, C.fvals(~F, es, x1), C.fvals(~F, es, x2))} == Con{O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)), _} : M.Vec(~F)}
      {==}

# |x| <= |c| + r, for x in the ball (c, r)
def abs_plus(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), b: KB.KB<K>, h: KB.bin(~K, ~F, ~H, x, b)) -> M.bnd(~F, x, N.emap(K, F, H, N.nadd(K, KA.kabs(~K, KB.KB.c(K, b)), KB.KB.r(K, b)))):
  match b:
    case KB.KB{+c, +r}:
      %KA.ea(~K, ~F, ~H, KA.kabs(~K, c), r) : M.bnd(~F, x, _)
      KB.bnd_val(~F, O.add(F, N.emap(K, F, H, c), O.sub(~F, x, N.emap(K, F, H, c))), x, O.add(F, N.emap(K, F, H, KA.kabs(~K, c)), N.emap(K, F, H, r)), FR.fring_eq(~F, [x, N.emap(K, F, H, c)], E.ZAdd{E.ZVar{1n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZVar{0n}, {==}), FM.bnd_add(~F, N.emap(K, F, H, c), N.emap(K, F, H, KA.kabs(~K, c)), O.sub(~F, x, N.emap(K, F, H, c)), N.emap(K, F, H, r), KA.kabs_bnd(~K, ~F, ~H, c), h))

def abs_plus_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), b: KB.KB<K>, h: KB.bin(~K, ~F, ~H, x, b)) -> O.le(~F, O.zero(F), N.emap(K, F, H, N.nadd(K, KA.kabs(~K, KB.KB.c(K, b)), KB.KB.r(K, b)))):
  match b:
    case KB.KB{+c, +r}:
      %KA.ea(~K, ~F, ~H, KA.kabs(~K, c), r) : O.le(~F, O.zero(F), _)
      FO.nonneg_add(~F, N.emap(K, F, H, KA.kabs(~K, c)), N.emap(K, F, H, r), KA.kabs_nonneg(~K, ~F, ~H, c), FM.bnd_nonneg(~F, O.sub(~F, x, N.emap(K, F, H, c)), N.emap(K, F, H, r), h))

# |S| <= |J| + D along one row
def row_bndz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat, h: KB.inbox(~K, ~F, ~H, SL.srange(~F, x1, x2, e, cnt, lo), KB.krange(~K, box, e, cnt, lo))) -> C.rbnd(~F, SL.srange(~F, x1, x2, e, cnt, lo), N.ofkv(~K, ~F, ~H, KA.kvadd(~K, KA.kvabs(~K, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo))), KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))))):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (h0, hs) = h
      (abs_plus(~K, ~F, ~H, SL.sl(~F, lo, x1, x2, e), KB.ksl(~K, lo, box, e), h0), row_bndz(~K, ~F, ~H, x1, x2, box, e, k, 1n+lo, hs))

def row_nnz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat, h: KB.inbox(~K, ~F, ~H, SL.srange(~F, x1, x2, e, cnt, lo), KB.krange(~K, box, e, cnt, lo))) -> FV.rnn(~F, N.ofkv(~K, ~F, ~H, KA.kvadd(~K, KA.kvabs(~K, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo))), KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))))):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (h0, hs) = h
      (abs_plus_nn(~K, ~F, ~H, SL.sl(~F, lo, x1, x2, e), KB.ksl(~K, lo, box, e), h0), row_nnz(~K, ~F, ~H, x1, x2, box, e, k, 1n+lo, hs))

def mat_bndz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat, +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box)) -> FV.mbnd(~F, smat(~F, x1, x2, eqs, cnt, lo), N.ofkm(~K, ~F, ~H, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))), CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      (row_bndz(~K, ~F, ~H, x1, x2, box, e, cnt, lo, KB.range_ok(~K, ~F, ~H, x1, x2, box, e, KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2, cnt, lo)), mat_bndz(~K, ~F, ~H, x1, x2, box, es, cnt, lo, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2))

def mat_nnz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB.KB<K>>, eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat, +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box)) -> FV.mnn(~F, N.ofkm(~K, ~F, ~H, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))), CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      (row_nnz(~K, ~F, ~H, x1, x2, box, e, cnt, lo, KB.range_ok(~K, ~F, ~H, x1, x2, box, e, KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2, cnt, lo)), mat_nnz(~K, ~F, ~H, x1, x2, box, es, cnt, lo, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh), h1, h2))
