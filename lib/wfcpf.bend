# bend-cad: a well-formed sketch passes the solver's check (lib/wfdec.bend:
# wf_dec), also once some of its constraints are made driven (the check
# does not look at the driven flag). For the solver's totality (ROADMAP:
# solve_total). Proofs only.

import Base
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./wfdec.bend as WF

def absurd(-A: Type, x: Empty) -> A:
  match x:

def kpair(+a: Bool, +b: Bool, h: {a == True{} : Bool} & {b == True{} : Bool}) -> {KA.band(a, b) == True{} : Bool}:
  (x, y) = h
  KA.band_i(a, b, x, y)

def ktriple(+a: Bool, +b: Bool, +c: Bool, h: {a == True{} : Bool} & ({b == True{} : Bool} & {c == True{} : Bool})) -> {KA.band(a, KA.band(b, c)) == True{} : Bool}:
  (x, yz) = h
  KA.band_i(a, KA.band(b, c), x, kpair(b, c, yz))

# Entities
# --------

def ent_dec(+es: List<&2, SK.Ent>, e: SK.Ent, h: SK.Ent.wf_refs(es, e)) -> {WF.ent(es, e) == True{} : Bool}:
  match e:
    case SK.Ent{id, cst, SK.GPoint{x, y}}:
      {==}
    case SK.Ent{id, cst, SK.GSeg{+p, +q}}:
      kpair(WF.ispt(es, p), WF.ispt(es, q), h)
    case SK.Ent{id, cst, SK.GCirc{+c, r}}:
      h
    case SK.Ent{id, cst, SK.GArc{+s, +f, b}}:
      kpair(WF.ispt(es, s), WF.ispt(es, f), h)

def ents_dec(+es: List<&2, SK.Ent>, xs: List<&2, SK.Ent>, h: SK.Sketch.wf.ents(es, xs)) -> {WF.ents(es, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      (a, b) = h
      KA.band_i(WF.ent(es, e), WF.ents(es, t), ent_dec(es, e, a), ents_dec(es, t, b))

# Constraints
# -----------

def crefs_dec(+es: List<&2, SK.Ent>, k: SK.Constraint, h: SK.Constraint.wf_refs(es, k)) -> {WF.crefs(es, k) == True{} : Bool}:
  match k:
    case SK.Coincident{+a, +b}:
      kpair(WF.ispt(es, a), WF.ispt(es, b), h)
    case SK.Horizontal{+a, +b}:
      kpair(WF.ispt(es, a), WF.ispt(es, b), h)
    case SK.Vertical{+a, +b}:
      kpair(WF.ispt(es, a), WF.ispt(es, b), h)
    case SK.Concentric{+a, +b}:
      kpair(WF.iscirc(es, a), WF.iscirc(es, b), h)
    case SK.EqualRadius{+a, +b}:
      kpair(WF.iscirc(es, a), WF.iscirc(es, b), h)
    case SK.Fix{v, c}:
      {==}
    case SK.Distance{+p, +q, d}:
      kpair(WF.ispt(es, p), WF.ispt(es, q), h)
    case SK.HDistance{+p, +q, d}:
      kpair(WF.ispt(es, p), WF.ispt(es, q), h)
    case SK.VDistance{+p, +q, d}:
      kpair(WF.ispt(es, p), WF.ispt(es, q), h)
    case SK.Radius{c, d}:
      h
    case SK.Diameter{c, d}:
      h
    case SK.LineDistance{+p, +a, rev, d, l}:
      kpair(WF.ispt(es, p), WF.isseg(es, a), h)
    case SK.Angle{+a, ra, +b, rb, c, s}:
      kpair(WF.isseg(es, a), WF.isseg(es, b), h)
    case SK.EqualLength{+a, +b}:
      kpair(WF.isseg(es, a), WF.isseg(es, b), h)
    case SK.Perpendicular{+a, +b}:
      kpair(WF.isseg(es, a), WF.isseg(es, b), h)
    case SK.Parallel{+a, +b}:
      kpair(WF.isseg(es, a), WF.isseg(es, b), h)
    case SK.OnLine{+p, +a}:
      kpair(WF.ispt(es, p), WF.isseg(es, a), h)
    case SK.OnCircle{+p, +c}:
      kpair(WF.ispt(es, p), WF.iscirc(es, c), h)
    case SK.Midpoint{+m, +a}:
      kpair(WF.ispt(es, m), WF.isseg(es, a), h)
    case SK.Symmetric{+p, +q, +a}:
      ktriple(WF.ispt(es, p), WF.ispt(es, q), WF.isseg(es, a), h)

def cons_dec.go(+es: List<&2, SK.Ent>, +k: SK.Constraint, +t: List<&2, SK.Rec>, h: SK.Constraint.wf(es, k) & SK.Sketch.wf.cons(es, t), ih: SK.Sketch.wf.cons(es, t) -> {WF.cons(es, t) == True{} : Bool}) -> {WF.cons(es, t) == True{} : Bool}:
  (a, b) = h
  ih(b)

def cons_dec(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, h: SK.Sketch.wf.cons(es, cs)) -> {WF.cons(es, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, dr, +k}, +t}:
      (a, bc) = h
      KA.band_i(WF.crefs(es, k), WF.cons(es, t), crefs_dec(es, k, a), cons_dec.go(es, k, t, bc, x => cons_dec(es, t, x)))

# a well-formed sketch passes the check
def wf_dec_ok(sk: SK.Sketch, h: SK.Sketch.wf(sk)) -> {WF.wf_dec(sk) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      (a, b) = h
      KA.band_i(WF.ents(es, es), WF.cons(es, cs), ents_dec(es, es, a), cons_dec(es, cs, b))

# Driven flags
# ------------

def mark_cons(+es: List<&2, SK.Ent>, +red: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat) -> {WF.cons(es, SV.mark.cons(red, cs, i)) == WF.cons(es, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, dr, +k}, +t}:
      %Equal.sym(Bool, WF.cons(es, SV.mark.cons(red, t, 1n+i)), WF.cons(es, t), mark_cons(es, red, t, 1n+i)) : {KA.band(WF.crefs(es, k), _) == KA.band(WF.crefs(es, k), WF.cons(es, t)) : Bool}
      {==}

# making constraints driven keeps a sketch passing the check
def wf_mark(+red: List<&2, Nat>, sk: SK.Sketch, h: {WF.wf_dec(sk) == True{} : Bool}) -> {WF.wf_dec(SV.mark(red, sk)) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      %Equal.sym(Bool, WF.cons(es, SV.mark.cons(red, cs, 0n)), WF.cons(es, cs), mark_cons(es, red, cs, 0n)) : {KA.band(WF.ents(es, es), _) == True{} : Bool}
      h
