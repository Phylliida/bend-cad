# bend-cad: lean residuals (PLAN-sk13b B4.8 B.1). sk-13a's reduction
# (lib/elim.bend) carries, beside the residual's polynomial, the
# combination that made it; the polynomial never reads the combination
# (a step reads only the residual's and the row's polynomials and the
# row's pivot). Every Bool the closure decides on is a zero test of such a
# polynomial, so here the same reduction keeps only the polynomials:
# rows as (polynomial, pivot), a residual as its polynomial. Each lean
# value is the projection of the full one (lib/lrespf.bend), so a test
# computed here is the test computed there.
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./zring.bend as R
import ./qnorm.bend as QN
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspace.bend as HS

# Rows
# ----

# a row's polynomial, pivot, and the polynomial's coefficient at the
# pivot (computed once, where each step would look it up)
type LRow is Data:
  LRow{p: List<&2, R.ZTerm>, pv: List<&2, Nat>, pc: S.Z}

def lrow.mk(+p: List<&2, R.ZTerm>, +pv: List<&2, Nat>) -> LRow:
  LRow{p, pv, EL.cz(pv, p)}

def lrow(r: EL.Row) -> LRow:
  match r:
    case EL.Row{p, cb, bt, pv}:
      lrow.mk(p, pv)

def lproj(rows: List<&2, EL.Row>) -> List<&2, LRow>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{lrow(h), lproj(t)}

def lsnoc(rows: List<&2, LRow>, +x: LRow) -> List<&2, LRow>:
  match rows:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, lsnoc(t, x)}

# the residual as a new row
def lrow_of(+p: List<&2, R.ZTerm>) -> LRow:
  lrow.mk(p, EL.pivot(p))

# Reduction
# ---------

# EL.step.go's polynomial: |b| r - sgn(b) a R
def lstep.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +p: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match a:
    case S.Z0{}:
      rp
    case S.Zpos{+q}:
      R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zpos{q}), Nil{}, p)))
    case S.Zneg{+q}:
      R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zneg{q}), Nil{}, p)))

def lstep(row: LRow, +rp: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match row:
    case LRow{+p, +pv, pc}:
      lstep.go(EL.cz(pv, rp), pc, rp, p)

# rp reduced against the rows, oldest first
def lreduce(rows: List<&2, LRow>, rp: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match rows:
    case Nil{}:
      rp
    case Con{row, t}:
      lreduce(t, lstep(row, rp))

# e's residual against the rows
def lresid(+rows: List<&2, LRow>, e: E.QExpr) -> List<&2, R.ZTerm>:
  lreduce(rows, R.norm(QN.clr(e)))

# e is in the rows' span
def linb(+rows: List<&2, LRow>, +e: E.QExpr) -> Bool:
  EP.isnil(lresid(rows, e))

# K
# -

def ks.lrows(+k: KS.KS) -> List<&2, LRow>:
  lproj(KS.ks.rows(k))

# e is in K
def ks.linb(+k: KS.KS, +e: E.QExpr) -> Bool:
  linb(ks.lrows(k), e)

# Hulls
# -----

# a hull's rows, lean, and its kept generators
type LH is Data:
  LH{rows: List<&2, LRow>, ds: List<&2, DR.Der>}

def lean(h: HS.HS) -> LH:
  match h:
    case HS.HS{rows, ds}:
      LH{lproj(rows), ds}

def lh.rows(h: LH) -> List<&2, LRow>:
  match h:
    case LH{rows, ds}:
      rows

def lh.ds(h: LH) -> List<&2, DR.Der>:
  match h:
    case LH{rows, ds}:
      ds

def lh.pick(b: Bool, +rows: List<&2, LRow>, +ds: List<&2, DR.Der>, +rp: List<&2, R.ZTerm>, +d: DR.Der) -> LH:
  match b:
    case True{}:
      LH{rows, ds}
    case False{}:
      LH{lsnoc(rows, lrow_of(rp)), KS.dsnoc(ds, d)}

# HS.hs.add, lean
def lh.add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: LH, +d: DR.Der) -> LH:
  match h:
    case LH{+rows, +ds}:
      +rp = lresid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))
      lh.pick(EP.isnil(rp), rows, ds, rp, d)

# lib/dclose.bend's hfold, lean
def lfold(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: LH) -> LH:
  match ds:
    case Nil{}:
      h
    case Con{+d, tl}:
      lfold(tl, es, fs, t, lh.add(es, fs, t, h, d))

# y is in the hull
def lh.inb(+h: LH, +y: SK.VE, +t: Nat) -> Bool:
  linb(lh.rows(h), HS.enc(y, t))

# The pair test
# -------------
# lib/pair.bend's ptest found a pair: u in the span, or v in the span of
# the rows and u

def lpt.first(b: Bool, +rows: List<&2, LRow>, +u: E.QExpr, +v: E.QExpr) -> Bool:
  match b:
    case True{}:
      True{}
    case False{}:
      linb(lsnoc(rows, lrow_of(lresid(rows, u))), v)

def lptest(+rows: List<&2, LRow>, +u: E.QExpr, +v: E.QExpr) -> Bool:
  lpt.first(linb(rows, u), rows, u, v)

# the hull label test (lib/lab.bend's hs.lab) finds a label
def lh.lab(+h: LH, +z: SK.VE, +t: Nat) -> Bool:
  lptest(lh.rows(h), HS.enc(z, t), HS.enc(DR.imul(z), t))

# the frame test (lib/lab.bend's ks.lab) finds a label
def ks.llab(+k: KS.KS, +z: SK.VE) -> Bool:
  lptest(ks.lrows(k), SK.VE.y(z), SK.VE.x(z))
