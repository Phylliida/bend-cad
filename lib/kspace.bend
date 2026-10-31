# bend-cad: the direction layer's linear part K (PLAN-sk13b B2). K is the
# span of its generators, each a K judgment's derivation (spec/dir.bend):
# a premise fact (DPrem), or a fact the closure derived. The generators
# are kept in sk-13a's fraction-free echelon form (lib/elim.bend): adding
# one reduces it against the rows and keeps it only if its residual is not
# 0. Membership is a zero residual; its witness is the chain of K-add
# steps over the generators with sk-13a's multipliers (lib/drvpf.bend:
# dropls), whose conclusion is exactly spec/solve.bend's lin of them.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/kspacepf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV

# K: its rows, and one derivation per generator (in order)
type KS is Data:
  KS{rows: List<&2, EL.Row>, ds: List<&2, DR.Der>}

def ks0() -> KS:
  KS{Nil{}, Nil{}}

# the generators: what each derivation proves
def kexprs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, ds: List<&2, DR.Der>) -> List<&2, E.QExpr>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{DR.Jd.e(DR.concl(es, fs, d)), kexprs(es, fs, t)}

def dsnoc(ds: List<&2, DR.Der>, +d: DR.Der) -> List<&2, DR.Der>:
  match ds:
    case Nil{}:
      Con{d, Nil{}}
    case Con{h, t}:
      Con{h, dsnoc(t, d)}

def ks.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der) -> KS:
  match b:
    case True{}:
      KS{rows, ds}
    case False{}:
      KS{EL.rsnoc(rows, EL.row_of(r)), dsnoc(ds, d)}

# K with the generator d proves added (unchanged if it is already in K)
def ks.add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS, +d: DR.Der) -> KS:
  match k:
    case KS{+rows, +ds}:
      +r = EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d)))
      ks.pick(EP.isnil(EP.resp(r)), rows, ds, r, d)

def ks.rows(k: KS) -> List<&2, EL.Row>:
  match k:
    case KS{rows, ds}:
      rows

def ks.ds(k: KS) -> List<&2, DR.Der>:
  match k:
    case KS{rows, ds}:
      ds

# e is in K
def ks.inb(+k: KS, +e: E.QExpr) -> Bool:
  EP.isnil(EP.resp(EL.resid(ks.rows(k), e)))

# the K-add chain l_1 d_1 + (l_2 d_2 + ... (0)), without the generators
# whose multiplier is 0
def kc.pick(b: Bool, +l: S.Q, +d: DR.Der, rest: DR.Der) -> DR.Der:
  match b:
    case True{}:
      DR.DKAdd{l, d, rest}
    case False{}:
      rest

def kchain(ls: List<&2, S.Q>, ds: List<&2, DR.Der>) -> DR.Der:
  match ls ds:
    case Con{+l, lt} Con{+d, dt}:
      kc.pick(DR.qnz(l), l, d, kchain(lt, dt))
    case Nil{} ds:
      DR.DZero{}
    case Con{l, lt} Nil{}:
      DR.DZero{}

# a derivation of e from K's generators (valid when e is in K)
def ks.der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS, +e: E.QExpr) -> DR.Der:
  kchain(DV.dropls(DV.rescb(EL.resid(ks.rows(k), e)), DV.resbt(EL.resid(ks.rows(k), e)), e, kexprs(es, fs, ks.ds(k))), ks.ds(k))
