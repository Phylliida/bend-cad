# bend-cad: balls under solve_complete (DESIGN §10.4, C3a), restated here
# so the gate checks lib/bndpf.bend until the completeness proof imports
# it. In every ordered field F that the computing numbers K map into:
# - The checker's slope centers are the Jacobian at the box's centers,
#   whatever the radii (the slope between a point and itself is the
#   derivative there).
# - Ball tightness: over a box whose balls have |c| + r <= bb and
#   r <= rho, an expression's ball has radius at most lp rho and
#   |center| + radius at most mj, and its slope balls at most ls rho and
#   ms (mj, lp, ms, ls: F values computed from the expression and bb).
# - So at points of the box an expression is within lp rho of its value
#   at the centers, and its slopes within ls rho of the derivative there;
#   with K = F (fnum) this holds for boxes centered at any point of F.
# - Renumbering variables by position (a distinct order, v in it) and a
#   block's renumbering (v one of its unknowns) commute with d/dv.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/ring.bend as E
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../lib/karith.bend as KA
import ../lib/kball.bend as KB
import ../lib/cert.bend as CK
import ../lib/slope.bend as SL
import ../lib/struct.bend as ST
import ../lib/plan.bend as PL
import ../lib/bndpf.bend as BP

def slope_is_derivative(~F: O.OField, +i: Nat, +x: M.Vec(~F), e: E.QExpr) -> {SL.sl(~F, i, x, x, e) == O.eval(~F, x, DV.deriv(e, i)) : O.C(F)}:
  BP.sl_deriv(~F, i, x, e)

def checker_jacobian(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~K, eqs) == True{} : Bool}) -> {N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))) == DV.jac(~F, BP.cen(~K, ~F, ~H, box), eqs, ST.iota(cnt, lo)) : M.Mat(~F)}:
  BP.mcen_jac(~K, ~F, ~H, box, cnt, lo, eqs, hh)

def ball_tight(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> BP.grade(~K, ~F, ~H, rho, KB.kball(~K, box, e), BP.mj(~F, bb, e), BP.lp(~F, bb, e)):
  BP.kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, e, hh)

def slope_ball_tight(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +i: Nat, e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> BP.grade(~K, ~F, ~H, rho, KB.ksl(~K, i, box, e), BP.ms(~F, bb, e), BP.ls(~F, bb, e)):
  BP.ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, e, hh)

def value_lipschitz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +x: M.Vec(~F), +hx: KB.inbox(~K, ~F, ~H, x, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.eval(~F, x, e), O.eval(~F, BP.cen(~K, ~F, ~H, box), e)), O.mul(F, BP.lp(~F, bb, e), rho)):
  BP.eval_lip(~K, ~F, ~H, rho, bb, hr, hb, box, hg, x, hx, e, hh)

def slope_lipschitz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, SL.sl(~F, i, x1, x2, e), SL.sl(~F, i, BP.cen(~K, ~F, ~H, box), BP.cen(~K, ~F, ~H, box), e)), O.mul(F, BP.ls(~F, bb, e), rho)):
  BP.sl_lip(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, x1, x2, h1, h2, e, hh)

# the same in F's own numbers: a box centered at any points of F
def value_lipschitz_f(~F: O.OField, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rho, bb, box), +x: M.Vec(~F), +hx: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x, box), +e: E.QExpr) -> M.bnd(~F, O.sub(~F, O.eval(~F, x, e), O.eval(~F, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), e)), O.mul(F, BP.lp(~F, bb, e), rho)):
  BP.eval_lip(~BP.fnum(~F), ~F, ~BP.femb(~F), rho, bb, hr, hb, box, hg, x, hx, e, BP.held_f(~F, e))

def renumber_deriv(+vp: List<&2, Nat>, +v: Nat, +hv: {SV.mem(v, vp) == True{} : Bool}, e: E.QExpr) -> {DV.deriv(PL.rnv(vp, e), PL.pos(v, vp)) == PL.rnv(vp, DV.deriv(e, v)) : E.QExpr}:
  BP.deriv_rnv(vp, v, hv, e)

def block_deriv(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +v: Nat, +hv1: {KA.natle(1n+v, o) == False{} : Bool}, +hv2: {KA.natle(1n+v, Nat.add(o, n)) == True{} : Bool}, e: E.QExpr) -> {DV.deriv(PL.rename(o, n, pars, e), PL.loc(o, n, pars, v)) == PL.rename(o, n, pars, DV.deriv(e, v)) : E.QExpr}:
  BP.deriv_rename(o, n, pars, v, hv1, hv2, e)
