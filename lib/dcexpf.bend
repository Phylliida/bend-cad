# bend-cad: what the pass needs of a closure's outcome (PLAN-sk13b B4.8,
# the incremental closure). Ex: it is never a step; a fixpoint comes with
# the closure's hypotheses (RR.Hyp: the invariant, the shape, every check
# of its last round, which the closure theorem, dec_none and dref_complete
# read); an explosion with its invariant (its derivations valid). Every
# decision the pass takes from an outcome (lib/dcwpf.bend dd_ok,
# lib/dconflictpf.bend dsome_o and dn.o) needs only that, so any run that
# gives Ex serves: dclose from sk0 (dclose_ex), or a run from any state
# that keeps the invariants (lib/dwarmpf.bend).
# Proofs only.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./dclose.bend as DC
import ./dcroundpf.bend as RD
import ./dcfixpf.bend as FX
import ./dcreprpf.bend as RR
import ./dctermpf.bend as TRM

def absurd(-A: Type, x: Empty) -> A:
  match x:

def Ex(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, o: DC.Out) -> Data:
  match o:
    case DC.OStep{s}:
      Empty
    case DC.OFix{+s}:
      RR.Hyp(es, fs, ctx, t, s)
    case DC.OOne{+d}:
      RD.OutInv(es, fs, ctx, t, DC.OOne{d})
    case DC.OVoid{+g, +dr, +di}:
      RD.OutInv(es, fs, ctx, t, DC.OVoid{g, dr, di})

# the outcome keeps the invariant
def ex_inv(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, h: Ex(es, fs, ctx, t, o)) -> RD.OutInv(es, fs, ctx, t, o):
  match o:
    case DC.OStep{+s}:
      absurd(RD.OutInv(es, fs, ctx, t, DC.OStep{s}), h)
    case DC.OFix{+s}:
      RR.h.sk(es, fs, ctx, t, s, h)
    case DC.OOne{+d}:
      h
    case DC.OVoid{+g, +dr, +di}:
      h

# a run's outcome with the invariant, the fixpoint facts, and no step
def ex_of(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, h1: RD.OutInv(es, fs, ctx, t, o), h2: FX.FixOut(es, fs, ctx, t, DC.segids(es), o),
  h3: {TRM.isstep(o) == False{} : Bool}, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> Ex(es, fs, ctx, t, o):
  match o:
    case DC.OStep{+s}:
      absurd(Ex(es, fs, ctx, t, DC.OStep{s}), KA.tf(h3))
    case DC.OFix{+s}:
      (h2, (hz, hb))
    case DC.OOne{+d}:
      h1
    case DC.OVoid{+g, +dr, +di}:
      h1

# the closure from sk0, with DC.dfuel
def dclose_ex(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> Ex(es, fs, ctx, t, DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs))):
  ex_of(DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs)), es, fs, ctx, t, RD.dclose_ok(es, fs, ctx, t, DC.dfuel(es, fs), hz, hb), FX.dclose_fix(es, fs, ctx, t, DC.dfuel(es, fs), hz, hb),
    TRM.dclose_term(es, fs, ctx, t, hz, hb), hz, hb)
