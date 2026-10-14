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
