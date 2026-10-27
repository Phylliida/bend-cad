# bend-cad: a hull, the forms known parallel to a root node r (PLAN-sk13b
# B3). Its generators are derivations of par(r, g_j): the closure's
# facts, and K's generators as the forms (k, 0) and (0, k) (by par-known),
# so that K squared lies inside. A form x is encoded as the polynomial
# x_re + t x_im (lib/seppf.bend: tag), t a variable index past every
# expression's variables, and the encoded generators are kept in sk-13a's
# echelon form (lib/elim.bend), as K's are (lib/kspace.bend). Membership
# of y is a zero residual of y's encoding; its witness is the par-lin
# chain over the generators with sk-13a's multipliers, whose conclusion is
# the real combination clin of the generators' forms.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/hspacepf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./seppf.bend as SP
import ./kspace.bend as KS

# a form's encoding
def enc(+x: SK.VE, +t: Nat) -> E.QExpr:
  SP.tag(SK.VE.x(x), SK.VE.y(x), t)

def encs(xs: List<&2, SK.VE>, +t: Nat) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, tl}:
      Con{enc(x, t), encs(tl, t)}

# the forms the derivations prove parallel to the root
def hxs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, ds: List<&2, DR.Der>) -> List<&2, SK.VE>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, tl}:
      Con{DR.Jd.x(DR.concl(es, fs, d)), hxs(es, fs, tl)}

# a hull: its rows, and one derivation per generator (in order)
type HS is Data:
  HS{rows: List<&2, EL.Row>, ds: List<&2, DR.Der>}

def hs0() -> HS:
  HS{Nil{}, Nil{}}

def hs.rows(h: HS) -> List<&2, EL.Row>:
  match h:
    case HS{rows, ds}:
      rows

def hs.ds(h: HS) -> List<&2, DR.Der>:
  match h:
    case HS{rows, ds}:
      ds

def hs.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der) -> HS:
  match b:
    case True{}:
      HS{rows, ds}
    case False{}:
      HS{EL.rsnoc(rows, EL.row_of(r)), KS.dsnoc(ds, d)}

# the hull with the generator d proves added (unchanged if already in it)
def hs.add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS, +d: DR.Der) -> HS:
  match h:
    case HS{+rows, +ds}:
      +r = EL.resid(rows, enc(DR.Jd.x(DR.concl(es, fs, d)), t))
      hs.pick(EP.isnil(EP.resp(r)), rows, ds, r, d)

# y is in the hull
def hs.inb(+h: HS, +y: SK.VE, +t: Nat) -> Bool:
  EP.isnil(EP.resp(EL.resid(hs.rows(h), enc(y, t))))

# m1 x1 + 1 (m2 x2 + ...), ending in 0 z_r + 0 z_r
def clin(+es: List<&2, SK.Ent>, +r: DR.Node, ls: List<&2, S.Q>, xs: List<&2, SK.VE>) -> SK.VE:
  match ls xs:
    case Con{l, lt} Con{x, xt}:
      DR.vlin(l, x, DR.qo(), clin(es, r, lt, xt))
    case Nil{} xs:
      DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))
    case Con{l, lt} Nil{}:
      DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))

# the par-lin chain l_1 d_1 + 1 (l_2 d_2 + ...), ending in 0 self + 0 self
def pchain(+r: DR.Node, ls: List<&2, S.Q>, ds: List<&2, DR.Der>) -> DR.Der:
  match ls ds:
    case Con{l, lt} Con{d, dt}:
      DR.DPLin{l, d, DR.qo(), pchain(r, lt, dt)}
    case Nil{} ds:
      DR.DPLin{DR.qz(), DR.DSelf{r}, DR.qz(), DR.DSelf{r}}
    case Con{l, lt} Nil{}:
      DR.DPLin{DR.qz(), DR.DSelf{r}, DR.qz(), DR.DSelf{r}}

# a derivation of par(r, y) from the hull's generators (valid when y is in
# the hull)
def hs.der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS, +y: SK.VE) -> DR.Der:
  pchain(r, DV.dropls(DV.rescb(EL.resid(hs.rows(h), enc(y, t))), DV.resbt(EL.resid(hs.rows(h), enc(y, t))), enc(y, t), encs(hxs(es, fs, hs.ds(h)), t)), hs.ds(h))

# K's generator k (derived by dk) as the forms (k, 0) and (0, k), each
# parallel to r by par-known on 0 z_r + 0 z_r
def kre(+r: DR.Node, +dk: DR.Der) -> DR.Der:
  DR.DKnown{DR.DPLin{DR.qz(), DR.DSelf{r}, DR.qz(), DR.DSelf{r}}, dk, DR.DZero{}}

def kim(+r: DR.Node, +dk: DR.Der) -> DR.Der:
  DR.DKnown{DR.DPLin{DR.qz(), DR.DSelf{r}, DR.qz(), DR.DSelf{r}}, DR.DZero{}, dk}
