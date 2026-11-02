# bend-cad: the pass's drops are correct by construction, and its classes
# pass the verdict's exact check (lib/verdict.bend: exact; PLAN-sk13a S5,
# PLAN-sk13b B4.6). Proofs only.
#
# Since the sk-13b switch (2026-11-02), what this file proved about
# sk-13a's pass, Honest or solver is proven in lib/dpasspf.bend; what is
# left here is what that proof reuses, and the description below is of
# the sk-13a proof.
#
# - Along one constraint's walk (lib/pass.bend: cwalk) every recorded
#   drop's reason is a combination on positions of the basis's bp, the
#   one lib/drvpf.bend's derivable proves, so its identity normalizes to
#   0 (dgood).
# - When the constraint ends kept or amber, every position of its final
#   bp is in the system solved: those before it by the pass's invariant
#   (allpre), its own by not being dropped (its class drops exactly the
#   walk's drops). So its drops' reasons pass (lib/dropok.bend: drop.ok).
# - An amber constraint's refutations are refute's certificates over the
#   premises before it (kb is kept_before), so they pass (ref.ok).
# - Along the pass: every class passes, so the classes do: their drops
#   (why_pass) and the verdict's check (ck_pass).
#
# Generated from tools/drafts/ckpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/box.bend as BX
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./qnorm.bend as QN
import ./identpf.bend as ID
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DR
import ./conflict.bend as CO
import ./struct.bend as ST
import ./refute.bend as RF
import ./satpf.bend as SA
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./cwpf.bend as CW
import ./passpf.bend as PP
import ./dfspf.bend as D
import ./solve.bend as SO
import ./verdict.bend as VD
import ./dropok.bend as DK
import ./vrdpf.bend as VR

def absurd(-A: Type, x: Empty) -> A:
  match x:


# What a walk's drops carry
# -------------------------

def mulpos(qs: List<&2, SV.Mul>) -> List<&2, Nat>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{SV.Mul{i, q}, t}:
      Con{i, mulpos(t)}

# each drop: a combination on positions in bp, g minus it normalizing
# to 0
def dgood(+es: List<&2, E.QExpr>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{SV.Drop{+j, +nd, SV.WLin{+qs}}, t}:
      SV.band(L.subl(mulpos(qs), bp), SV.band(QN.qzero(E.QSub{SV.eqat(es, j), SV.mlin(es, qs)}), dgood(es, bp, t)))
    case Con{SV.Drop{+j, +nd, SV.WDer{dv}}, t}:
      False{}

def subl_snoc(xs: List<&2, Nat>, +bp: List<&2, Nat>, +k: Nat, +h: {L.subl(xs, bp) == True{} : Bool}) -> {L.subl(xs, CO.lsnoc(bp, k)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, CO.lsnoc(bp, k),
        Equal.trans(Bool, SV.mem(x, CO.lsnoc(bp, k)), SV.bor(SV.mem(x, bp), SV.eq(x, k)), True{}, KB.mem_snoc(x, bp, k), L.bor_l(SV.mem(x, bp), SV.eq(x, k), L.subl_hd(x, t, bp, h))),
        subl_snoc(t, bp, k, L.subl_tl(x, t, bp, h)))

def dgood_up(+es: List<&2, E.QExpr>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>, +k: Nat, +h: {dgood(es, bp, ds) == True{} : Bool}) -> {dgood(es, CO.lsnoc(bp, k), ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{SV.Drop{+j, +nd, SV.WLin{+qs}}, +t}:
      +b2 = L.subl(mulpos(qs), bp)
      +b3 = QN.qzero(E.QSub{SV.eqat(es, j), SV.mlin(es, qs)})
      +b4 = dgood(es, bp, t)
      +h34 = L.band_r(b2, SV.band(b3, b4), h)
      L.band_i(L.subl(mulpos(qs), CO.lsnoc(bp, k)), SV.band(b3, dgood(es, CO.lsnoc(bp, k), t)), subl_snoc(mulpos(qs), bp, k, L.band_l(b2, SV.band(b3, b4), h)),
        L.band_i(b3, dgood(es, CO.lsnoc(bp, k), t), L.band_l(b3, b4, h34), dgood_up(es, bp, t, k, L.band_r(b3, b4, h34))))
    case Con{SV.Drop{+j, +nd, SV.WDer{+dv}}, +t}:
      absurd({dgood(es, CO.lsnoc(bp, k), Con{SV.Drop{j, nd, SV.WDer{dv}}, t}) == True{} : Bool}, KA.ft(h))

def mp_sub(bp: List<&2, Nat>, ls: List<&2, S.Q>) -> {L.subl(mulpos(PA.muls(bp, ls)), bp) == True{} : Bool}:
  match bp ls:
    case Nil{} ls:
      {==}
    case Con{+i, +it} Nil{}:
      {==}
    case Con{+i, +it} Con{+l, +lt}:
      L.subl_con(i, mulpos(PA.muls(it, lt)), Con{i, it}, L.mem_hd(i, it), L.subl_cons_r(mulpos(PA.muls(it, lt)), i, it, mp_sub(it, lt)))

# the pass's combination is lin over the basis at bp
def rhs_lin(+es: List<&2, E.QExpr>, bp: List<&2, Nat>, ls: List<&2, S.Q>) -> {SV.mlin(es, PA.muls(bp, ls)) == SV.lin(ls, SV.picked(es, bp)) : E.QExpr}:
  match bp ls:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{l, lt}:
      {==}
    case Con{+i, +it} Nil{}:
      {==}
    case Con{+i, +it} Con{+l, +lt}:
      Equal.cong(E.QExpr, E.QExpr, y => E.QAdd{E.QMul{E.QCst{l}, SV.eqat(es, i)}, y}, SV.mlin(es, PA.muls(it, lt)), SV.lin(lt, SV.picked(es, it)), rhs_lin(es, it, lt))


# a drop the walk records
def dg_drop(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr},
  +hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}, +hg: {dgood(SK.Sketch.eqs(sk), bp, ds) == True{} : Bool}) -> {dgood(SK.Sketch.eqs(sk), bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}) == True{} : Bool}:
  (+hb, q1) = hi
  (hl, q2) = q1
  (hB, q3) = q2
  (hp, hbp) = q3
  +qz = QN.qzero(E.QSub{SV.eqat(SK.Sketch.eqs(sk), k), SV.mlin(SK.Sketch.eqs(sk), PA.muls(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B)))})
  L.band_i(L.subl(mulpos(PA.muls(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B))), bp), SV.band(qz, dgood(SK.Sketch.eqs(sk), bp, ds)), mp_sub(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B)),
    L.band_i(qz, dgood(SK.Sketch.eqs(sk), bp, ds),
      ID.qzero_ident(SV.eqat(SK.Sketch.eqs(sk), k), SV.mlin(SK.Sketch.eqs(sk), PA.muls(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B))),
        (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : SV.Ident(_, SV.mlin(SK.Sketch.eqs(sk), PA.muls(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B))))
          (%Equal.sym(E.QExpr, SV.mlin(SK.Sketch.eqs(sk), PA.muls(bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B))), SV.lin(DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), SV.picked(SK.Sketch.eqs(sk), bp)), rhs_lin(SK.Sketch.eqs(sk), bp, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B))) : SV.Ident(e, _)
            (%hp : SV.Ident(e, SV.lin(DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), _))
              DR.derivable(B, rows, e, CW.cwb_rinv(sk, c, k, rows, B, ds, us, hb), hnil))))),
      hg))


def dg.k(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +eb: {EP.isnil(EP.resp(EL.resid(rows, e))) == b : Bool}, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +hg: {dgood(SK.Sketch.eqs(sk), bp, ds) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st2), CW.cw.ds(st2)) == True{} : Bool} -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2)), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2))) == True{} : Bool})
  -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(EP.isnil(EP.resp(EL.resid(rows, e))), k, e, EL.resid(rows, e), rows, B, bp, ds, us))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(EP.isnil(EP.resp(EL.resid(rows, e))), k, e, EL.resid(rows, e), rows, B, bp, ds, us)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), True{}, eb) : {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us)))) == True{} : Bool}
      ih(PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, CW.inv_drop(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt), dg_drop(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), eb, hg))
    case False{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), False{}, eb) : {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us)))) == True{} : Bool}
      ih(PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, CW.inv_keep(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt, eb, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq)), dgood_up(SK.Sketch.eqs(sk), bp, ds, k, hg))

def dg.s(st: PA.CW, +e: E.QExpr, +t: List<&2, E.QExpr>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hg: {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st), CW.cw.ds(st)) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st2), CW.cw.ds(st2)) == True{} : Bool} -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2)), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2))) == True{} : Bool}) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.res(k, e, st))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.res(k, e, st)))) == True{} : Bool}:
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      dg.k(EP.isnil(EP.resp(EL.resid(rows, e))), e, t, sk, R, D, c, bp0, k, rows, B, bp, ds, us, {==}, heq, hq, hlt, hi, hg, ih)

def dg.o(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW, +eb: {SV.eq(SV.nth(SV.owners(sk), k), c) == b : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hg: {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st), CW.cw.ds(st)) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st2), CW.cw.ds(st2)) == True{} : Bool} -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2)), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, st2))) == True{} : Bool}) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st)), CW.cw.ds(PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), True{}, eb) : {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st)))) == True{} : Bool}
      dg.s(st, e, t, sk, R, D, c, bp0, k, eb, hq, hlt, hi, hg, ih)
    case False{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), False{}, eb) : {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st))), CW.cw.ds(PA.cwalk(t, SV.owners(sk), c, 1n+k, PA.cw.at(_, k, e, st)))) == True{} : Bool}
      ih(st, CW.inv_skip(sk, R, D, c, bp0, k, st, hi, eb, hlt), hg)

# the walk from position k keeps every recorded drop good
def dg_go(es: List<&2, E.QExpr>, own_k: List<&2, Nat>, +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +st: PA.CW, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == own_k : List<&2, Nat>}, +hl: {SV.len(own_k) == SV.neqs(es) : Nat},
  +hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hg: {dgood(SK.Sketch.eqs(sk), CW.cw.bp(st), CW.cw.ds(st)) == True{} : Bool}) -> {dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(es, SV.owners(sk), c, k, st)), CW.cw.ds(PA.cwalk(es, SV.owners(sk), c, k, st))) == True{} : Bool}:
  match es own_k:
    case Nil{} Nil{}:
      hg
    case Nil{} Con{+o, +ot}:
      absurd({dgood(SK.Sketch.eqs(sk), CW.cw.bp(st), CW.cw.ds(st)) == True{} : Bool}, CW.len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({dgood(SK.Sketch.eqs(sk), CW.cw.bp(PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st)), CW.cw.ds(PA.cwalk(Con{e, t}, SV.owners(sk), c, k, st))) == True{} : Bool}, CW.len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      dg.o(SV.eq(SV.nth(SV.owners(sk), k), c), e, t, sk, R, D, c, bp0, k, st, {==}, hq, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), hi, hg,
        st2 => h2 => g2 => dg_go(t, ot, sk, R, D, c, bp0, 1n+k, st2, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), OW.ndrop_step(k, SV.owners(sk), o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), h2, g2))

# Positions in the system solved
# ------------------------------

def allsol(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      SV.band(DK.solved_at(own, R, D, x), allsol(own, R, D, t))

def as_mem.c(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, eb: {SV.eq(x, y) == b : Bool}, hm: {SV.bor(b, SV.mem(x, t)) == True{} : Bool},
  +h: {SV.band(DK.solved_at(own, R, D, y), allsol(own, R, D, t)) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {allsol(own, R, D, t) == True{} : Bool} -> {DK.solved_at(own, R, D, x) == True{} : Bool})
  -> {DK.solved_at(own, R, D, x) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, y, L.eq_ok(x, y, eb)) : {DK.solved_at(own, R, D, _) == True{} : Bool}
      L.band_l(DK.solved_at(own, R, D, y), allsol(own, R, D, t), h)
    case False{}:
      ih(hm, L.band_r(DK.solved_at(own, R, D, y), allsol(own, R, D, t), h))

def as_mem(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, xs: List<&2, Nat>, +x: Nat, +h: {allsol(own, R, D, xs) == True{} : Bool}, hm: {SV.mem(x, xs) == True{} : Bool}) -> {DK.solved_at(own, R, D, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({DK.solved_at(own, R, D, x) == True{} : Bool}, KA.ft(hm))
    case Con{+y, +t}:
      as_mem.c(own, R, D, x, y, t, SV.eq(x, y), {==}, hm, h, a => b => as_mem(own, R, D, t, x, b, a))

def cs_of(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, qs: List<&2, SV.Mul>, +bp: List<&2, Nat>, +hs: {L.subl(mulpos(qs), bp) == True{} : Bool}, +ha: {allsol(own, R, D, bp) == True{} : Bool}) -> {DK.comb.solved(own, R, D, qs) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{SV.Mul{+i, +q}, +t}:
      L.band_i(DK.solved_at(own, R, D, i), DK.comb.solved(own, R, D, t), as_mem(own, R, D, bp, i, ha, L.subl_hd(i, mulpos(t), bp, hs)), cs_of(own, R, D, t, bp, L.subl_tl(i, mulpos(t), bp, hs), ha))

# good drops whose bp is in the system solved pass
def dok_of(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>, +hg: {dgood(es, bp, ds) == True{} : Bool}, +ha: {allsol(own, R, D, bp) == True{} : Bool}) -> {DK.drops.ok(es, own, R, D, ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{SV.Drop{+j, +nd, SV.WLin{+qs}}, +t}:
      +b2 = L.subl(mulpos(qs), bp)
      +b3 = QN.qzero(E.QSub{SV.eqat(es, j), SV.mlin(es, qs)})
      +b4 = dgood(es, bp, t)
      +h34 = L.band_r(b2, SV.band(b3, b4), hg)
      L.band_i(DK.drop.ok(es, own, R, D, SV.Drop{j, nd, SV.WLin{qs}}), DK.drops.ok(es, own, R, D, t),
        L.band_i(DK.comb.solved(own, R, D, qs), b3, cs_of(own, R, D, qs, bp, L.band_l(b2, SV.band(b3, b4), hg), ha), L.band_l(b3, b4, h34)),
        dok_of(es, own, R, D, bp, t, L.band_r(b3, b4, h34), ha))
    case Con{SV.Drop{+j, +nd, SV.WDer{+dv}}, +t}:
      absurd({DK.drops.ok(es, own, R, D, Con{SV.Drop{j, nd, SV.WDer{dv}}, t}) == True{} : Bool}, KA.ft(hg))

def as_cat(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {allsol(own, R, D, a) == True{} : Bool}, +hb: {allsol(own, R, D, b) == True{} : Bool}) -> {allsol(own, R, D, SV.cat(a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +t}:
      L.band_i(DK.solved_at(own, R, D, x), allsol(own, R, D, SV.cat(t, b)), L.band_l(DK.solved_at(own, R, D, x), allsol(own, R, D, t), ha), as_cat(own, R, D, t, b, L.band_r(DK.solved_at(own, R, D, x), allsol(own, R, D, t), ha), hb))

# the solved positions before c
def ap_as(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, xs: List<&2, Nat>, +h: {PP.allpre(xs, own, R, D, c) == True{} : Bool}) -> {allsol(own, R, D, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(DK.solved_at(own, R, D, x), allsol(own, R, D, t), L.band_r(SV.lt(SV.nth(own, x), c), DK.solved_at(own, R, D, x), L.band_l(PP.psel(own, R, D, c, x), PP.allpre(t, own, R, D, c), h)),
        ap_as(own, R, D, c, t, L.band_r(PP.psel(own, R, D, c, x), PP.allpre(t, own, R, D, c), h)))

# c's own, not dropped, c not red: in the system solved (the classes drop
# exactly what c's class drops among c's equations)
def us_as.d(+own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, +u: Nat, +dd: List<&2, Nat>, +hu: {SV.eq(SV.nth(own, u), c) == True{} : Bool}, +hR: {SV.mem(c, R) == False{} : Bool}, +hnu: {SV.mem(u, dd) == False{} : Bool},
  +hdn: {CL.downs(own, cls, 0n) == True{} : Bool}, +hdk: {SV.kdrops(SV.class_at(cls, c)) == dd : List<&2, Nat>}) -> {DK.solved_at(own, R, SV.dropped(cls), u) == True{} : Bool}:
  +hc = L.eq_ok(SV.nth(own, u), c, hu)
  VR.sa_of(own, R, SV.dropped(cls), u,
    (%Equal.sym(Nat, SV.nth(own, u), c, hc) : {SV.mem(_, R) == False{} : Bool}
      hR),
    Equal.trans(Bool, SV.mem(u, SV.dropped(cls)), SV.mem(u, SV.kdrops(SV.class_at(cls, SV.nth(own, u)))), False{}, CL.mem_dropped(own, cls, u, hdn),
      (%Equal.sym(Nat, SV.nth(own, u), c, hc) : {SV.mem(u, SV.kdrops(SV.class_at(cls, _))) == False{} : Bool}
        (%Equal.sym(List<&2, Nat>, SV.kdrops(SV.class_at(cls, c)), dd, hdk) : {SV.mem(u, _) == False{} : Bool}
          hnu))))

def us_as(+own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +c: Nat, us: List<&2, Nat>, +dd: List<&2, Nat>, +hown: {KB.allo(own, us, c) == True{} : Bool}, +hR: {SV.mem(c, R) == False{} : Bool}, +hnd: {SV.none_in(us, dd) == True{} : Bool},
  +hdn: {CL.downs(own, cls, 0n) == True{} : Bool}, +hdk: {SV.kdrops(SV.class_at(cls, c)) == dd : List<&2, Nat>}) -> {allsol(own, R, SV.dropped(cls), us) == True{} : Bool}:
  match us:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      L.band_i(DK.solved_at(own, R, SV.dropped(cls), u), allsol(own, R, SV.dropped(cls), t),
        us_as.d(own, R, cls, c, u, dd, L.band_l(SV.eq(SV.nth(own, u), c), KB.allo(own, t, c), hown), hR, KB.bnot_t(SV.mem(u, dd), L.band_l(SV.bnot(SV.mem(u, dd)), SV.none_in(t, dd), hnd)), hdn, hdk),
        us_as(own, R, cls, c, t, dd, L.band_r(SV.eq(SV.nth(own, u), c), KB.allo(own, t, c), hown), hR, L.band_r(SV.bnot(SV.mem(u, dd)), SV.none_in(t, dd), hnd), hdn, hdk))

# Amber refutations
# -----------------

def fsome(m: Maybe<&2, List<&2, SV.Ref>>) -> List<&2, SV.Ref>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def isnone(m: Maybe<&2, List<&2, SV.Ref>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def ref_of(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, h: SV.Refutes0(es, ss, ls, ms, k)) -> {VD.ref.ok(es, ss, SV.Ref{ls, ms, k}) == True{} : Bool}:
  (hro, hid) = h
  L.band_i(SV.refok(ls, ms, k, es, ss), QN.qzero(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}), hro, ID.qzero_ident(E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}, hid))

# refute's certificate passes
def ref_ok_of(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, h: {RF.refute(es, ss) == Some{RF.Cert{ls, ms, k}} : Maybe<&2, RF.Cert>}) -> {VD.ref.ok(es, ss, SV.Ref{ls, ms, k}) == True{} : Bool}:
  ref_of(es, ss, ls, ms, k,
    (%h : SA.RefOk(es, ss, _)
      SA.refute_ok(es, ss)))


def sro.c(m: Maybe<&2, RF.Cert>, r: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +i: Nat, +t: List<&2, SK.Side>, +rs: List<&2, SV.Ref>,
  em: {RF.refute(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i)) == m : Maybe<&2, RF.Cert>}, er: {PA.srefs(t, sk, SV.kept_before(sk, R, c), c, 1n+i) == r : Maybe<&2, List<&2, SV.Ref>>}, h: {PA.srefs.c(m, r) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>},
  ih: @rs2: List<&2, SV.Ref> -> {PA.srefs(t, sk, SV.kept_before(sk, R, c), c, 1n+i) == Some{rs2} : Maybe<&2, List<&2, SV.Ref>>} -> {VD.refs.ok(sk, R, c, SV.slen(t), rs2, 1n+i) == True{} : Bool})
  -> {VD.refs.ok(sk, R, c, 1n+SV.slen(t), rs, i) == True{} : Bool}:
  match m r:
    case None{} r:
      absurd({VD.refs.ok(sk, R, c, 1n+SV.slen(t), rs, i) == True{} : Bool}, KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, z => isnone(z), None{}, Some{rs}, h)))
    case Some{RF.Cert{ls, ms, k}} None{}:
      absurd({VD.refs.ok(sk, R, c, 1n+SV.slen(t), rs, i) == True{} : Bool}, KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, z => isnone(z), None{}, Some{rs}, h)))
    case Some{RF.Cert{+ls, +ms, +k}} Some{+rs2}:
      %Equal.cong(Maybe<&2, List<&2, SV.Ref>>, List<&2, SV.Ref>, z => fsome(z), Some{Con{SV.Ref{ls, ms, k}, rs2}}, Some{rs}, h) : {VD.refs.ok(sk, R, c, 1n+SV.slen(t), _, i) == True{} : Bool}
      L.band_i(VD.ref.ok(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i), SV.Ref{ls, ms, k}), VD.refs.ok(sk, R, c, SV.slen(t), rs2, 1n+i),
        ref_ok_of(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i), ls, ms, k, em), ih(rs2, er))

# the pass's side refutations (kb being kept_before) pass
def srefs_ok(ss: List<&2, SK.Side>, +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +i: Nat, +rs: List<&2, SV.Ref>, h: {PA.srefs(ss, sk, SV.kept_before(sk, R, c), c, i) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>})
  -> {VD.refs.ok(sk, R, c, SV.slen(ss), rs, i) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      sro.c(RF.refute(SV.eqs_of(sk, SV.kept_before(sk, R, c)), PA.neg_kb(sk, SV.kept_before(sk, R, c), c, i)), PA.srefs(t, sk, SV.kept_before(sk, R, c), c, 1n+i), sk, R, c, i, t, rs, {==}, {==}, h, rs2 => h2 => srefs_ok(t, sk, R, c, 1n+i, rs2, h2))

# A kept or amber class
# ---------------------

def kdo_onea(m: Maybe<&2, List<&2, SV.Ref>>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +dd: List<&2, SV.Drop>) -> {DK.kdrops.ok(es, own, R, D, PA.one.a(m, dd)) == DK.drops.ok(es, own, R, D, dd) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{rs}:
      {==}

def kdo_onek(a: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> {DK.kdrops.ok(es, own, R, D, PA.one.k(a, sk, kb, c, dd)) == DK.drops.ok(es, own, R, D, dd) : Bool}:
  match a:
    case True{}:
      kdo_onea(PA.srefs(SV.csides(sk, [c]), sk, kb, c, 0n), es, own, R, D, dd)
    case False{}:
      {==}

def kam_onea(m: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, em: {PA.srefs(SV.csides(sk, [c]), sk, SV.kept_before(sk, R, c), c, 0n) == m : Maybe<&2, List<&2, SV.Ref>>})
  -> {VD.kamber.ok(sk, R, c, PA.one.a(m, dd)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+rs}:
      srefs_ok(SV.csides(sk, [c]), sk, R, c, 0n, rs, em)

def kam_onek(a: Bool, +sk: SK.Sketch, +R: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, +hkb: {kb == SV.kept_before(sk, R, c) : List<&2, Nat>}) -> {VD.kamber.ok(sk, R, c, PA.one.k(a, sk, kb, c, dd)) == True{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(List<&2, Nat>, kb, SV.kept_before(sk, R, c), hkb) : {VD.kamber.ok(sk, R, c, PA.one.k(True{}, sk, _, c, dd)) == True{} : Bool}
      kam_onea(PA.srefs(SV.csides(sk, [c]), sk, SV.kept_before(sk, R, c), c, 0n), sk, R, c, dd, {==})
    case False{}:
      {==}

# One constraint of the pass
# --------------------------


# the class at i passes both checks
def ckb(+sk: SK.Sketch, +i: Nat, +K: SV.Class) -> Bool:
  SV.band(DK.kdrops.ok(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), K), VD.kamber.ok(sk, SV.reds(PA.classes(sk)), i, K))

def ck.ok(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), +hg: {dgood(SK.Sketch.eqs(sk), bp2, dd) == True{} : Bool}, +hK: {SV.class_at(PA.classes(sk), i) == PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd) : SV.Class}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> {ckb(sk, i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)) == True{} : Bool}:
  (+hcb, c1) = hci
  (hcl, c2) = c1
  (hcB, c3) = c2
  (hcp, hbp2) = c3
  +hb = PP.pinv_b(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
  +hR = Equal.trans(Bool, SV.mem(i, SV.reds(PA.classes(sk))), SV.is_red(PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), False{}, PP.red_of(sk, i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hK), PP.onek_red(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd))
  +hdk = Equal.trans(List<&2, Nat>, SV.kdrops(SV.class_at(PA.classes(sk), i)), SV.kdrops(PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), SV.drops(dd), Equal.cong(SV.Class, List<&2, Nat>, z => SV.kdrops(z), SV.class_at(PA.classes(sk), i), PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hK), PP.onek_kd(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd))
  L.band_i(DK.kdrops.ok(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), VD.kamber.ok(sk, SV.reds(PA.classes(sk)), i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)),
    Equal.trans(Bool, DK.kdrops.ok(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), DK.drops.ok(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), dd), True{}, kdo_onek(SV.is_amberable(sk, i, SV.drops(dd)), SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), sk, kb, i, dd),
      dok_of(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), bp2, dd, hg,
        (%Equal.sym(List<&2, Nat>, bp2, SV.cat(bp, us), hbp2) : {allsol(SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), _) == True{} : Bool}
          as_cat(SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), bp, us, ap_as(SV.owners(sk), SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, PP.pib_pre(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, rows, B, bp, vm, hb)),
            us_as(SV.owners(sk), SV.reds(PA.classes(sk)), PA.classes(sk), i, us, SV.drops(dd), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), hR, CW.cwb_udisj(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), hD, hdk))))),
    kam_onek(SV.is_amberable(sk, i, SV.drops(dd)), sk, SV.reds(PA.classes(sk)), kb, i, dd, PP.pinv_kb(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)))


def ck.g(g: ST.GS, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), +hg: {dgood(SK.Sketch.eqs(sk), bp2, dd) == True{} : Bool}, +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> {ckb(sk, i, PA.PO.k(PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us}))) == True{} : Bool}:
  match g:
    case ST.GFail{ST.Red{j, s, x}}:
      {==}
    case ST.GOk{+vm2}:
      ck.ok(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hci, hg, hK, hD)


def ck.w(w: PA.CW, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hi: PP.PInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, PA.PS{kb, rows, B, bp, vm}),
  +hci: CW.CWInv(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), w), +hg: {dgood(SK.Sketch.eqs(sk), CW.cw.bp(w), CW.cw.ds(w)) == True{} : Bool}, +hK: {SV.class_at(PA.classes(sk), i) == PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class}, +hD: {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool})
  -> {ckb(sk, i, PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm))) == True{} : Bool}:
  match w:
    case PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      ck.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hci, hg, hK, hD)

def cw_snd(-A: Type, -B: Data, h: (A & B)) -> B:
  (a, b) = h
  b


# The pass
# --------

def band4(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +h1: {SV.band(a, c) == True{} : Bool}, +h2: {SV.band(b, d) == True{} : Bool}) -> {SV.band(SV.band(a, b), SV.band(c, d)) == True{} : Bool}:
  L.band_i(SV.band(a, b), SV.band(c, d), L.band_i(a, b, L.band_l(a, c, h1), L.band_l(b, d, h2)), L.band_i(c, d, L.band_r(a, c, h1), L.band_r(b, d, h2)))


