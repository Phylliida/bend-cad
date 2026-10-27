# bend-cad: independence of a set (PLAN-sk13b B3): the forms vs, inserted
# in turn after the rows of a span, each leave a nonzero residual. Then a
# combination of them lies in the span only with every coefficient 0
# (lib/indsetpf.bend). A hull has no complex line outside K squared when
# i times its other generators pass this test.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/indsetpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP

# every one of vs, inserted in turn after the rows, has a nonzero residual
def indset(vs: List<&2, E.QExpr>, +rows: List<&2, EL.Row>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{+v, vt}:
      SV.band(SV.bnot(EP.isnil(EP.resp(EL.resid(rows, v)))), indset(vt, EL.rsnoc(rows, EL.row_of(EL.resid(rows, v)))))

# the coefficients paired with vs are all 0
def allz(ls: List<&2, S.Q>, vs: List<&2, E.QExpr>) -> Bool:
  match ls vs:
    case Con{l, lt} Con{v, vt}:
      SV.band(SV.bnot(DR.qnz(l)), allz(lt, vt))
    case Nil{} vs:
      True{}
    case Con{l, lt} Nil{}:
      True{}
