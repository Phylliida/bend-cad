# bend-cad: lean residuals are the full ones' polynomials (PLAN-sk13b
# B4.8 B.1). A step's polynomial is the lean step's on the row's
# projection (step_eq), so a whole reduction's is (reduce_eq, resid_eq)
# and every zero test agrees (inb_eq). Appending a row projects to
# appending its projection (snoc_eq), so a hull's insertion and fold
# project to the lean ones (add_eq, fold_eq), and the pair test and both
# label tests find a pair exactly when the lean ones say so (ptest_eq,
# hs_lab_eq, ks_lab_eq). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./zring.bend as R
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./pair.bend as PT
import ./lab.bend as LB
import ./dclose.bend as DC
import ./lres.bend as LR

# Reduction
# ---------

def lstep_eq(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos)
  -> {EP.resp(EL.step.go(a, b, rp, rcb, rbt, p, cb, bt)) == LR.lstep.go(a, b, rp, p) : List<&2, R.ZTerm>}:
  match a:
    case S.Z0{}:
      {==}
    case S.Zpos{+q}:
      {==}
    case S.Zneg{+q}:
      {==}

def step_eq(row: EL.Row, r: EL.Res) -> {EP.resp(EL.step(row, r)) == LR.lstep(LR.lrow(row), EP.resp(r)) : List<&2, R.ZTerm>}:
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      lstep_eq(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt)

def reduce_eq(rows: List<&2, EL.Row>, +r: EL.Res) -> {EP.resp(EL.reduce(rows, r)) == LR.lreduce(LR.lproj(rows), EP.resp(r)) : List<&2, R.ZTerm>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      %step_eq(row, r) : {EP.resp(EL.reduce(t, EL.step(row, r))) == LR.lreduce(LR.lproj(t), _) : List<&2, R.ZTerm>}
      reduce_eq(t, EL.step(row, r))

def resid_eq(+rows: List<&2, EL.Row>, +e: E.QExpr) -> {EP.resp(EL.resid(rows, e)) == LR.lresid(LR.lproj(rows), e) : List<&2, R.ZTerm>}:
  reduce_eq(rows, EL.start(e, EL.rlen(rows)))

# a zero test on the rows is the lean one on their projection
def inb_eq(+rows: List<&2, EL.Row>, +e: E.QExpr) -> {EP.isnil(EP.resp(EL.resid(rows, e))) == LR.linb(LR.lproj(rows), e) : Bool}:
  %resid_eq(rows, e) : {EP.isnil(EP.resp(EL.resid(rows, e))) == EP.isnil(_) : Bool}
  {==}

def ks_inb_eq(k: KS.KS, +e: E.QExpr) -> {KS.ks.inb(k, e) == LR.ks.linb(k, e) : Bool}:
  match k:
    case KS.KS{+rows, +ds}:
      inb_eq(rows, e)

# Rows
# ----

def lsnoc_eq(rows: List<&2, EL.Row>, +x: EL.Row) -> {LR.lproj(EL.rsnoc(rows, x)) == LR.lsnoc(LR.lproj(rows), LR.lrow(x)) : List<&2, LR.LRow>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %lsnoc_eq(t, x) : {Con{LR.lrow(h), LR.lproj(EL.rsnoc(t, x))} == Con{LR.lrow(h), _} : List<&2, LR.LRow>}
      {==}

def row_of_eq(r: EL.Res) -> {LR.lrow(EL.row_of(r)) == LR.lrow_of(EP.resp(r)) : LR.LRow}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      {==}

# appending a residual as a row
def snoc_eq(+rows: List<&2, EL.Row>, +r: EL.Res) -> {LR.lproj(EL.rsnoc(rows, EL.row_of(r))) == LR.lsnoc(LR.lproj(rows), LR.lrow_of(EP.resp(r))) : List<&2, LR.LRow>}:
  %row_of_eq(r) : {LR.lproj(EL.rsnoc(rows, EL.row_of(r))) == LR.lsnoc(LR.lproj(rows), _) : List<&2, LR.LRow>}
  lsnoc_eq(rows, EL.row_of(r))

# Hulls
# -----

def pick_eq(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der)
  -> {LR.lean(HS.hs.pick(b, rows, ds, r, d)) == LR.lh.pick(b, LR.lproj(rows), ds, EP.resp(r), d) : LR.LH}:
  match b:
    case True{}:
      {==}
    case False{}:
      %snoc_eq(rows, r) : {LR.LH{LR.lproj(EL.rsnoc(rows, EL.row_of(r))), KS.dsnoc(ds, d)} == LR.LH{_, KS.dsnoc(ds, d)} : LR.LH}
      {==}

# an insertion, lean
def add_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +d: DR.Der)
  -> {LR.lean(HS.hs.add(es, fs, t, h, d)) == LR.lh.add(es, fs, t, LR.lean(h), d) : LR.LH}:
  match h:
    case HS.HS{+rows, +ds}:
      %resid_eq(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)) : {LR.lean(HS.hs.add(es, fs, t, HS.HS{rows, ds}, d)) == LR.lh.pick(EP.isnil(_), LR.lproj(rows), ds, _, d) : LR.LH}
      pick_eq(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d)

# a fold, lean
def fold_eq(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS)
  -> {LR.lean(DC.hfold(ds, es, fs, t, h)) == LR.lfold(ds, es, fs, t, LR.lean(h)) : LR.LH}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      %add_eq(es, fs, t, h, d) : {LR.lean(DC.hfold(tl, es, fs, t, HS.hs.add(es, fs, t, h, d))) == LR.lfold(tl, es, fs, t, _) : LR.LH}
      fold_eq(tl, es, fs, t, HS.hs.add(es, fs, t, h, d))

def hs_inb_eq(h: HS.HS, +y: SK.VE, +t: Nat) -> {HS.hs.inb(h, y, t) == LR.lh.inb(LR.lean(h), y, t) : Bool}:
  match h:
    case HS.HS{+rows, +ds}:
      inb_eq(rows, HS.enc(y, t))

# The pair test
# -------------

def pr.some(m: Maybe<&2, PT.Pr>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def lab.some(m: Maybe<&2, DR.Lab>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def sec_some(c: Bool, +rows2: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr) -> {pr.some(PT.pt.second(c, rows2, B, u, v)) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the second half: v against the rows with u appended
def sec_eq(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr)
  -> {pr.some(PT.pt.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v))
      == LR.linb(LR.lsnoc(LR.lproj(rows), LR.lrow_of(LR.lresid(LR.lproj(rows), u))), v) : Bool}:
  %resid_eq(rows, u) : {pr.some(PT.pt.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == LR.linb(LR.lsnoc(LR.lproj(rows), LR.lrow_of(_)), v) : Bool}
  %snoc_eq(rows, EL.resid(rows, u)) : {pr.some(PT.pt.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == LR.linb(_, v) : Bool}
  %inb_eq(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v) : {pr.some(PT.pt.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == _ : Bool}
  sec_some(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)

def first_eq(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr)
  -> {pr.some(PT.pt.first(b, rows, B, u, v)) == LR.lpt.first(b, LR.lproj(rows), u, v) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      sec_eq(rows, B, u, v)

# the pair test finds a pair exactly when the lean one says so
def ptest_eq(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr) -> {pr.some(PT.ptest(rows, B, u, v)) == LR.lptest(LR.lproj(rows), u, v) : Bool}:
  %inb_eq(rows, u) : {pr.some(PT.ptest(rows, B, u, v)) == LR.lpt.first(_, LR.lproj(rows), u, v) : Bool}
  first_eq(EP.isnil(EP.resp(EL.resid(rows, u))), rows, B, u, v)

def map_some(m: Maybe<&2, PT.Pr>) -> {lab.some(LB.lab_map(m)) == pr.some(m) : Bool}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def hs_lab_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +z: SK.VE) -> {lab.some(LB.hs.lab(es, fs, t, h, z)) == LR.lh.lab(LR.lean(h), z, t) : Bool}:
  match h:
    case HS.HS{+rows, +ds}:
      Equal.trans(Bool, lab.some(LB.hs.lab(es, fs, t, HS.HS{rows, ds}, z)), pr.some(PT.ptest(rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t))), LR.lh.lab(LR.LH{LR.lproj(rows), ds}, z, t),
        map_some(PT.ptest(rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t))),
        ptest_eq(rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t)))

def ks_lab_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS.KS, +z: SK.VE) -> {lab.some(LB.ks.lab(es, fs, k, z)) == LR.ks.llab(k, z) : Bool}:
  match k:
    case KS.KS{+rows, +ds}:
      Equal.trans(Bool, lab.some(LB.ks.lab(es, fs, KS.KS{rows, ds}, z)), pr.some(PT.ptest(rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z))), LR.ks.llab(KS.KS{rows, ds}, z),
        map_some(PT.ptest(rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z))),
        ptest_eq(rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z)))
