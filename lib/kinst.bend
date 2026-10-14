# bend-cad: computing numbers the checker runs on (spec/knum.bend), with
# their maps into every ordered field. Untrusted: each map's laws are
# checked by Bend when the record is built.
#   dnum/demb: the dyadics m/2^e (the fast path); a rational is held when
#              its denominator is a power of two.
#   qnum/qemb: the rationals (unreduced); every rational is held.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ./qemb.bend as QE
import ./qord.bend as LQO
import ./dmat.bend as DM

# Comparison verdicts, by the rational comparison
# -----------------------------------------------

def qcmp_sound.go(~F: O.OField, +x: S.Q, +y: S.Q, c: Cmp, e: {S.Q.cmp(x, y) == c : Cmp}) -> N.cmeans(F, c, O.ofq(~F, x), O.ofq(~F, y)):
  match c:
    case LT{}:
      QE.ofq_lt(~F, x, y, e)
    case EQ{}:
      QE.ofq_eq(~F, x, y, LQO.q_cmp_eq(x, y, e))
    case GT{}:
      QE.ofq_lt(~F, y, x, LQO.q_cmp_gt(x, y, e))

def qcmp_sound(~F: O.OField, +x: S.Q, +y: S.Q) -> N.cmeans(F, S.Q.cmp(x, y), O.ofq(~F, x), O.ofq(~F, y)):
  qcmp_sound.go(~F, x, y, S.Q.cmp(x, y), {==})

# The rationals
# -------------

def qnum() -> N.Num:
  N.Num{S.Q, S.Q{S.Z0{}, S.XH{}}, S.Q{S.Zpos{S.XH{}}, S.XH{}}, a => b => S.Q.add(a, b), a => b => S.Q.mul(a, b), a => S.Q.neg(a), a => b => S.Q.cmp(a, b), q => Some{q}}

# what Some{k} promises for a held rational q
def qok(~F: O.OField, m: Maybe<&2, S.Q>, +q: S.Q) -> Type:
  match m:
    case None{}:
      Unit
    case Some{k}:
      {O.ofq(~F, k) == O.ofq(~F, q) : O.C(F)}

def q_ofq(~F: O.OField, +q: S.Q, +k: S.Q, h: {Some{q} == Some{k} : Maybe<&2, S.Q>}) -> {O.ofq(~F, k) == O.ofq(~F, q) : O.C(F)}:
  %h : qok(~F, _, q)
  {==}

def qemb(~F: O.OField) -> N.Emb<qnum(), F>:
  N.Emb{x => O.ofq(~F, x),
    QE.ofq_zero(~F),
    QE.ofq_one(~F),
    a => b => QE.ofq_add(~F, a, b),
    a => b => QE.ofq_mul(~F, a, b),
    a => QE.ofq_neg(~F, a),
    a => b => qcmp_sound(~F, a, b),
    q => k => h => q_ofq(~F, q, k, h)}

# The dyadics
# -----------

def dcmp(+a: S.D, +b: S.D) -> Cmp:
  S.Q.cmp(S.D.toq(a), S.D.toq(b))

def plog.succ(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{1n+e}

# e with p = 2^e, if p is a power of two
def plog(p: S.Pos) -> Maybe<&2, Nat>:
  match p:
    case S.XH{}:
      Some{0n}
    case S.XO{q}:
      plog.succ(plog(q))
    case S.XI{q}:
      None{}

def dofq.go(n: S.Z, m: Maybe<&2, Nat>) -> Maybe<&2, S.D>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{S.D{n, e}}

# n/d as a dyadic, when d is a power of two
def dofq(+q: S.Q) -> Maybe<&2, S.D>:
  dofq.go(S.Q.num(q), plog(S.Q.den(q)))

def dnum() -> N.Num:
  N.Num{S.D, M.d0(), M.d1(), a => b => S.D.add(a, b), a => b => S.D.mul(a, b), a => S.D.neg(a), a => b => dcmp(a, b), q => dofq(q)}

# what plog's answer promises
def pok(m: Maybe<&2, Nat>, +p: S.Pos) -> Type:
  match m:
    case None{}:
      Unit
    case Some{e}:
      {S.Pos.pow2(e) == p : S.Pos}

def pok.succ(m: Maybe<&2, Nat>, +p: S.Pos, h: pok(m, p)) -> pok(plog.succ(m), S.XO{p}):
  match m:
    case None{}:
      Unit{}
    case Some{e}:
      %h : {S.XO{S.Pos.pow2(e)} == S.XO{_} : S.Pos}
      {==}

def plog_ok(p: S.Pos) -> pok(plog(p), p):
  match p:
    case S.XH{}:
      {==}
    case S.XO{+q}:
      pok.succ(plog(q), q, plog_ok(q))
    case S.XI{q}:
      Unit{}

# what Some{k} promises for a held rational q
def dok(~F: O.OField, m: Maybe<&2, S.D>, +q: S.Q) -> Type:
  match m:
    case None{}:
      Unit
    case Some{k}:
      {M.ofd(~F, k) == O.ofq(~F, q) : O.C(F)}

def dofq_ok.go(~F: O.OField, +n: S.Z, +d: S.Pos, m: Maybe<&2, Nat>, h: pok(m, d)) -> dok(~F, dofq.go(n, m), S.Q{n, d}):
  match m:
    case None{}:
      Unit{}
    case Some{e}:
      %h : {M.ofd(~F, S.D{n, e}) == O.ofq(~F, S.Q{n, _}) : O.C(F)}
      {==}

def dofq_ok(~F: O.OField, q: S.Q) -> dok(~F, dofq(q), q):
  match q:
    case S.Q{+n, +d}:
      dofq_ok.go(~F, n, d, plog(d), plog_ok(d))

def d_ofq(~F: O.OField, +q: S.Q, +k: S.D, h: {dofq(q) == Some{k} : Maybe<&2, S.D>}) -> {M.ofd(~F, k) == O.ofq(~F, q) : O.C(F)}:
  %h : dok(~F, _, q)
  dofq_ok(~F, q)

def dcmp_sound.go(~F: O.OField, +a: S.D, +b: S.D, c: Cmp, e: {dcmp(a, b) == c : Cmp}) -> N.cmeans(F, c, M.ofd(~F, a), M.ofd(~F, b)):
  match c:
    case LT{}:
      QE.ofq_lt(~F, S.D.toq(a), S.D.toq(b), e)
    case EQ{}:
      QE.ofq_eq(~F, S.D.toq(a), S.D.toq(b), LQO.q_cmp_eq(S.D.toq(a), S.D.toq(b), e))
    case GT{}:
      QE.ofq_lt(~F, S.D.toq(b), S.D.toq(a), LQO.q_cmp_gt(S.D.toq(a), S.D.toq(b), e))

def dcmp_sound(~F: O.OField, +a: S.D, +b: S.D) -> N.cmeans(F, dcmp(a, b), M.ofd(~F, a), M.ofd(~F, b)):
  dcmp_sound.go(~F, a, b, dcmp(a, b), {==})

def demb(~F: O.OField) -> N.Emb<dnum(), F>:
  N.Emb{x => M.ofd(~F, x),
    Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F)),
    Equal.sym(O.C(F), O.one(F), M.ofd(~F, M.d1()), DM.ofd_one(~F)),
    a => b => Equal.sym(O.C(F), O.add(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.add(a, b)), DM.ofd_add(~F, a, b)),
    a => b => Equal.sym(O.C(F), O.mul(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.mul(a, b)), DM.ofd_mul(~F, a, b)),
    a => Equal.sym(O.C(F), O.neg(F, M.ofd(~F, a)), M.ofd(~F, S.D.neg(a)), DM.ofd_neg(~F, a)),
    a => b => dcmp_sound(~F, a, b),
    q => k => h => d_ofq(~F, q, k, h)}
