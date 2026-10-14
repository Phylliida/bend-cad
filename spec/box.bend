# bend-cad spec: the box a plan certifies (DESIGN §8.4). Trusted.
#
# A box gives every variable of a system a center and a radius, numbers of
# a checker's computing numbers K (spec/knum.bend) sent into F by H. A point
# x of F lies in the box when it has one entry per center and
# |x_v - c_v| <= r_v for every v (a radius past the end of the radii reads
# 0). A pinned variable has radius 0, so every point of the box gives it
# exactly its center.
#
# A lookup past the end of x reads 0, so a box shorter than the variables a
# sketch names would silently put the rest at 0. The sketch-level laws
# therefore require Sketch.within(sk, n) for the box's length n: every
# variable the sketch names is below n.

import Base
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N
import ./cert.bend as C
import ./ring.bend as E
import ./sketch.bend as SK

def inbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F)) -> Data:
  M.Both({M.len(~F, x) == M.len(~F, N.ofkv(~K, ~F, ~H, gc)) : Nat}, C.rbnd(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, gr)))

# Variables a sketch names
# ------------------------

def lt(i: Nat, n: Nat) -> Bool:
  match i n:
    case i 0n:
      False{}
    case 0n 1n+m:
      True{}
    case 1n+j 1n+m:
      lt(j, m)

# every variable of the expression is below n
def QExpr.within(e: E.QExpr, +n: Nat) -> Bool:
  match e:
    case E.QVar{i}:
      lt(i, n)
    case E.QCst{c}:
      True{}
    case E.QAdd{a, b}:
      Bool.and(QExpr.within(a, n), QExpr.within(b, n))
    case E.QSub{a, b}:
      Bool.and(QExpr.within(a, n), QExpr.within(b, n))
    case E.QMul{a, b}:
      Bool.and(QExpr.within(a, n), QExpr.within(b, n))
    case E.QNeg{a}:
      QExpr.within(a, n)

# an entity's own variables: a point's coordinates, a circle's radius, an
# arc's bulge (segments, centers and ends name point entities)
def Ent.within(e: SK.Ent, +n: Nat) -> Bool:
  match e:
    case SK.Ent{id, cst, SK.GPoint{x, y}}:
      Bool.and(lt(x, n), lt(y, n))
    case SK.Ent{id, cst, SK.GCirc{c, r}}:
      lt(r, n)
    case SK.Ent{id, cst, SK.GArc{s, f, b}}:
      lt(b, n)
    case _:
      True{}

# a constraint's own variables and its dimensions' (other arguments name
# entities)
def Constraint.within(k: SK.Constraint, +n: Nat) -> Bool:
  match k:
    case SK.Fix{v, c}:
      lt(v, n)
    case SK.Distance{p, q, d}:
      QExpr.within(d, n)
    case SK.HDistance{p, q, d}:
      QExpr.within(d, n)
    case SK.VDistance{p, q, d}:
      QExpr.within(d, n)
    case SK.Radius{c, d}:
      QExpr.within(d, n)
    case SK.Diameter{c, d}:
      QExpr.within(d, n)
    case SK.LineDistance{p, a, rev, d, l}:
      Bool.and(QExpr.within(d, n), lt(l, n))
    case SK.Angle{a, ra, b, rb, c, s}:
      Bool.and(QExpr.within(c, n), QExpr.within(s, n))
    case _:
      True{}

def Sketch.within.ents(es: List<&2, SK.Ent>, +n: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Ent.within(e, n), Sketch.within.ents(t, n))

# driven constraints too: their dimensions are measured from the geometry
def Sketch.within.cons(cs: List<&2, SK.Rec>, +n: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{SK.Rec{id, dr, k}, t}:
      Bool.and(Constraint.within(k, n), Sketch.within.cons(t, n))

# every variable the sketch names is below n
def Sketch.within(sk: SK.Sketch, +n: Nat) -> Bool:
  match sk:
    case SK.Sketch{vs, es, cs}:
      Bool.and(Sketch.within.ents(es, n), Sketch.within.cons(cs, n))
