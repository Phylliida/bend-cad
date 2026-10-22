# bend-cad: WD.ofd maps KI.dnum() into wnum (lib/wnum.bend) and commutes
# with every operation of spec/knum.bend's Num: zero, one, add, mul, neg,
# cmp and ofq, for every base 2^(1 + lp): a map of computing numbers
# (lib/khom.bend), wh. With the proposer's operations at words (wops),
# the laws lib/gnumerpf.bend needs (lib/pops.bend), wlaws.

import Base
import ../spec/num.bend as S
import ../spec/knum.bend as N
import ./kinst.bend as KI
import ./wnum.bend as WN
import ./khom.bend as KH
import ./wdyadpf.bend as WDP
import ./wsigpf.bend as WSP
import ./numer.bend as NU
import ./pops.bend as PO
import ../rt/wmag.bend as RW
import ../rt/wdyad.bend as RD

def w_zero(+bp: Nat, +lp: Nat) -> {N.nzero(WN.wnum(bp, lp)) == RD.WD.ofd(lp, N.nzero(KI.dnum())) : RD.WD}:
  {==}

def w_one(+bp: Nat, +lp: Nat) -> {N.none(WN.wnum(bp, lp)) == RD.WD.ofd(lp, N.none(KI.dnum())) : RD.WD}:
  {==}

def w_add(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {N.nadd(WN.wnum(bp, lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, N.nadd(KI.dnum(), a, b)) : RD.WD}:
  WDP.add_ok(bp, lp, hb, a, b)

def w_mul(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {N.nmul(WN.wnum(bp, lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, N.nmul(KI.dnum(), a, b)) : RD.WD}:
  WDP.mul_ok(bp, lp, hb, a, b)

def w_neg(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D) -> {N.nneg(WN.wnum(bp, lp), RD.WD.ofd(lp, a)) == RD.WD.ofd(lp, N.nneg(KI.dnum(), a)) : RD.WD}:
  WDP.neg_ok(bp, lp, hb, a)

def w_cmp(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {N.ncmp(WN.wnum(bp, lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == N.ncmp(KI.dnum(), a, b) : Cmp}:
  WDP.cmp_ok(bp, lp, hb, a, b)

def w_ofq(+bp: Nat, +lp: Nat, q: S.Q) -> {N.nofq(WN.wnum(bp, lp), q) == WN.wofq.m(lp, N.nofq(KI.dnum(), q)) : Maybe<&2, RD.WD>}:
  {==}

# the Maybe map of lib/wnum.bend is KH.mmap's
def wofq_mm(+bp: Nat, +lp: Nat, m: Maybe<&2, S.D>) -> {WN.wofq.m(lp, m) == KH.mmap(~KI.dnum(), ~WN.wnum(bp, lp), x => RD.WD.ofd(lp, x), m) : Maybe<&2, RD.WD>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# WD.ofd, a map of computing numbers from KI.dnum() to the words
def wh(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> KH.Hom<KI.dnum(), WN.wnum(bp, lp)>:
  KH.Hom{x => RD.WD.ofd(lp, x),
    w_zero(bp, lp),
    w_one(bp, lp),
    a => b => w_add(bp, lp, hb, a, b),
    a => b => w_mul(bp, lp, hb, a, b),
    a => w_neg(bp, lp, hb, a),
    a => b => w_cmp(bp, lp, hb, a, b),
    q => wofq_mm(bp, lp, KI.dofq(q))}

# the rare operations go through S.D, so they commute by tod_ofd
def sdiv_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +w: Nat, +a: S.D, +b: S.D) -> {RD.WD.ofd(lp, NU.dsdiv(w, RD.WD.tod(lp, RD.WD.ofd(lp, a)), RD.WD.tod(lp, RD.WD.ofd(lp, b)))) == RD.WD.ofd(lp, NU.dsdiv(w, a, b)) : RD.WD}:
  %Equal.sym(S.D, RD.WD.tod(lp, RD.WD.ofd(lp, a)), a, WDP.tod_ofd(bp, lp, hb, a)) : {RD.WD.ofd(lp, NU.dsdiv(w, _, RD.WD.tod(lp, RD.WD.ofd(lp, b)))) == RD.WD.ofd(lp, NU.dsdiv(w, a, b)) : RD.WD}
  %Equal.sym(S.D, RD.WD.tod(lp, RD.WD.ofd(lp, b)), b, WDP.tod_ofd(bp, lp, hb, b)) : {RD.WD.ofd(lp, NU.dsdiv(w, a, _)) == RD.WD.ofd(lp, NU.dsdiv(w, a, b)) : RD.WD}
  {==}

def sigup_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +x: S.D, +b: Nat) -> {RD.WD.ofd(lp, NU.dsigup(RD.WD.tod(lp, RD.WD.ofd(lp, x)), b)) == RD.WD.ofd(lp, NU.dsigup(x, b)) : RD.WD}:
  %Equal.sym(S.D, RD.WD.tod(lp, RD.WD.ofd(lp, x)), x, WDP.tod_ofd(bp, lp, hb, x)) : {RD.WD.ofd(lp, NU.dsigup(_, b)) == RD.WD.ofd(lp, NU.dsigup(x, b)) : RD.WD}
  {==}

# the proposer's laws at words
def wlaws(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> PO.PLaws<WN.wnum(bp, lp), WN.wops(bp, lp)>:
  PO.PLaws{wh(bp, lp, hb),
    x => {==},
    x => WDP.tod_ofd(bp, lp, hb, x),
    x => b => WSP.sig_ok(bp, lp, hb, x, b),
    x => p => WSP.round_ok(bp, lp, hb, x, p),
    w => a => b => sdiv_ok(bp, lp, hb, w, a, b),
    x => b => sigup_ok(bp, lp, hb, x, b)}
