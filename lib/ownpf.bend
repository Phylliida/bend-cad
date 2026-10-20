# bend-cad: which constraint each equation comes from (spec/solve.bend:
# owners), for the single pass (PLAN-sk13a S4). Proofs only.
# - owners is as long as the sketch's equations;
# - it is sorted: from an equation whose constraint is at c or later, every
#   later one's is too (so the solved equations before c + 1 are those
#   before c and then c's own);
# - a driven constraint owns no equation, and every owner is a
#   constraint's position.
# Lists from a position: qdrop for equations, ndrop for owners.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./listpf.bend as LI
import ./nat.bend as LN
import ./kbpf.bend as KB

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Lists from a position
# ---------------------

def qdrop(k: Nat, xs: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match k xs:
    case 0n xs:
      xs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      qdrop(j, t)

def ndrop(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k xs:
    case 0n xs:
      xs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      ndrop(j, t)

def qtl(xs: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def ntl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def qdrop_tl(k: Nat, xs: List<&2, E.QExpr>) -> {qdrop(1n+k, xs) == qtl(qdrop(k, xs)) : List<&2, E.QExpr>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      qdrop_tl(j, t)

def ndrop_tl(k: Nat, xs: List<&2, Nat>) -> {ndrop(1n+k, xs) == ntl(ndrop(k, xs)) : List<&2, Nat>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      ndrop_tl(j, t)

def qdrop_step(+k: Nat, +xs: List<&2, E.QExpr>, +e: E.QExpr, +t: List<&2, E.QExpr>, h: {qdrop(k, xs) == Con{e, t} : List<&2, E.QExpr>}) -> {qdrop(1n+k, xs) == t : List<&2, E.QExpr>}:
  Equal.trans(List<&2, E.QExpr>, qdrop(1n+k, xs), qtl(qdrop(k, xs)), t, qdrop_tl(k, xs), Equal.cong(List<&2, E.QExpr>, List<&2, E.QExpr>, x => qtl(x), qdrop(k, xs), Con{e, t}, h))

def ndrop_step(+k: Nat, +xs: List<&2, Nat>, +o: Nat, +t: List<&2, Nat>, h: {ndrop(k, xs) == Con{o, t} : List<&2, Nat>}) -> {ndrop(1n+k, xs) == t : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, ndrop(1n+k, xs), ntl(ndrop(k, xs)), t, ndrop_tl(k, xs), Equal.cong(List<&2, Nat>, List<&2, Nat>, x => ntl(x), ndrop(k, xs), Con{o, t}, h))

def qhd(xs: List<&2, E.QExpr>) -> E.QExpr:
  match xs:
    case Nil{}:
      E.QCst{SV.qzero()}
    case Con{h, t}:
      h

def nhd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

def eqat_qdrop(xs: List<&2, E.QExpr>, k: Nat) -> {SV.eqat(xs, k) == qhd(qdrop(k, xs)) : E.QExpr}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      eqat_qdrop(t, j)

def nth_ndrop(xs: List<&2, Nat>, k: Nat) -> {SV.nth(xs, k) == nhd(ndrop(k, xs)) : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      nth_ndrop(t, j)

# the k-th equation, when the list from k is e :: t
def eqat_of(+xs: List<&2, E.QExpr>, +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, h: {qdrop(k, xs) == Con{e, t} : List<&2, E.QExpr>}) -> {SV.eqat(xs, k) == e : E.QExpr}:
  Equal.trans(E.QExpr, SV.eqat(xs, k), qhd(qdrop(k, xs)), e, eqat_qdrop(xs, k), Equal.cong(List<&2, E.QExpr>, E.QExpr, x => qhd(x), qdrop(k, xs), Con{e, t}, h))

def nth_of(+xs: List<&2, Nat>, +k: Nat, +o: Nat, +t: List<&2, Nat>, h: {ndrop(k, xs) == Con{o, t} : List<&2, Nat>}) -> {SV.nth(xs, k) == o : Nat}:
  Equal.trans(Nat, SV.nth(xs, k), nhd(ndrop(k, xs)), o, nth_ndrop(xs, k), Equal.cong(List<&2, Nat>, Nat, x => nhd(x), ndrop(k, xs), Con{o, t}, h))

# Lengths
# -------

def len_cat_reps(n: Nat, +i: Nat, +ys: List<&2, Nat>) -> {SV.len(SV.cat(SV.reps(n, i), ys)) == Nat.add(n, SV.len(ys)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Nat, SV.len(SV.cat(SV.reps(m, i), ys)), Nat.add(m, SV.len(ys)), len_cat_reps(m, i, ys)) : {1n+_ == 1n+Nat.add(m, SV.len(ys)) : Nat}
      {==}

def neqs_cat(xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>) -> {SV.neqs(SK.cat(xs, ys)) == Nat.add(SV.neqs(xs), SV.neqs(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, SV.neqs(SK.cat(t, ys)), Nat.add(SV.neqs(t), SV.neqs(ys)), neqs_cat(t, ys)) : {1n+_ == 1n+Nat.add(SV.neqs(t), SV.neqs(ys)) : Nat}
      {==}

def len_go(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat) -> {SV.len(SV.owners.go(es, cs, i)) == SV.neqs(SK.Sketch.eqs.go(es, cs)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, t}:
      len_go(es, t, 1n+i)
    case Con{SK.Rec{id, False{}, +k}, +t}:
      %Equal.sym(Nat, SV.len(SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, k)), i), SV.owners.go(es, t, 1n+i))), Nat.add(SV.neqs(SK.Constraint.eqs(es, k)), SV.len(SV.owners.go(es, t, 1n+i))), len_cat_reps(SV.neqs(SK.Constraint.eqs(es, k)), i, SV.owners.go(es, t, 1n+i))) : {_ == SV.neqs(SK.cat(SK.Constraint.eqs(es, k), SK.Sketch.eqs.go(es, t))) : Nat}
      %Equal.sym(Nat, SV.neqs(SK.cat(SK.Constraint.eqs(es, k), SK.Sketch.eqs.go(es, t))), Nat.add(SV.neqs(SK.Constraint.eqs(es, k)), SV.neqs(SK.Sketch.eqs.go(es, t))), neqs_cat(SK.Constraint.eqs(es, k), SK.Sketch.eqs.go(es, t))) : {Nat.add(SV.neqs(SK.Constraint.eqs(es, k)), SV.len(SV.owners.go(es, t, 1n+i))) == _ : Nat}
      %Equal.sym(Nat, SV.len(SV.owners.go(es, t, 1n+i)), SV.neqs(SK.Sketch.eqs.go(es, t)), len_go(es, t, 1n+i)) : {Nat.add(SV.neqs(SK.Constraint.eqs(es, k)), _) == Nat.add(SV.neqs(SK.Constraint.eqs(es, k)), SV.neqs(SK.Sketch.eqs.go(es, t))) : Nat}
      {==}

# one owner per equation
def len_owners(sk: SK.Sketch) -> {SV.len(SV.owners(sk)) == SV.neqs(SK.Sketch.eqs(sk)) : Nat}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      len_go(es, cs, 0n)

def isz(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      False{}

def zs(+n: Nat, h: {0n == 1n+n : Nat}) -> Empty:
  KA.tf(Equal.cong(Nat, Bool, x => isz(x), 0n, 1n+n, h))

def len_drops(k: Nat, xs: List<&2, Nat>, ys: List<&2, E.QExpr>, h: {SV.len(xs) == SV.neqs(ys) : Nat}) -> {SV.len(ndrop(k, xs)) == SV.neqs(qdrop(k, ys)) : Nat}:
  match k xs ys:
    case 0n xs ys:
      h
    case 1n+j Nil{} Nil{}:
      {==}
    case 1n+j Nil{} Con{y, +yt}:
      absurd({SV.len(Nil{}) == SV.neqs(qdrop(j, yt)) : Nat}, zs(SV.neqs(yt), h))
    case 1n+j Con{x, +xt} Nil{}:
      absurd({SV.len(ndrop(j, xt)) == SV.neqs(Nil{}) : Nat}, zs(SV.len(xt), Equal.sym(Nat, 1n+SV.len(xt), 0n, h)))
    case 1n+j Con{x, +xt} Con{y, +yt}:
      len_drops(j, xt, yt, LN.succ_inj(SV.len(xt), SV.neqs(yt), h))

# Sorted
# ------

# every entry is at least c
def geall(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      SV.band(SV.bnot(SV.lt(h, c)), geall(t, c))

def sorted(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      SV.band(geall(t, h), sorted(t))

# x >= o >= c: x >= c
def nlt_trans(x: Nat, o: Nat, c: Nat, h1: {SV.lt(x, o) == False{} : Bool}, h2: {SV.lt(o, c) == False{} : Bool}) -> {SV.lt(x, c) == False{} : Bool}:
  match x o c:
    case x o 0n:
      KB.lt_z(x)
    case 0n 0n 1n+m:
      absurd({SV.lt(0n, 1n+m) == False{} : Bool}, KA.tf(h2))
    case 0n 1n+p 1n+m:
      absurd({SV.lt(0n, 1n+m) == False{} : Bool}, KA.tf(h1))
    case 1n+i 0n 1n+m:
      absurd({SV.lt(1n+i, 1n+m) == False{} : Bool}, KA.tf(h2))
    case 1n+i 1n+p 1n+m:
      nlt_trans(i, p, m, h1, h2)

def ge_head(+h: Nat, +c: Nat, +t: List<&2, Nat>, g: {geall(Con{h, t}, c) == True{} : Bool}) -> {SV.lt(h, c) == False{} : Bool}:
  KB.bnot_t(SV.lt(h, c), LI.band_l(SV.bnot(SV.lt(h, c)), geall(t, c), g))

def ge_tail(+h: Nat, +c: Nat, +t: List<&2, Nat>, g: {geall(Con{h, t}, c) == True{} : Bool}) -> {geall(t, c) == True{} : Bool}:
  LI.band_r(SV.bnot(SV.lt(h, c)), geall(t, c), g)

def ge_con(+h: Nat, +c: Nat, +t: List<&2, Nat>, h1: {SV.lt(h, c) == False{} : Bool}, h2: {geall(t, c) == True{} : Bool}) -> {geall(Con{h, t}, c) == True{} : Bool}:
  LI.band_i(SV.bnot(SV.lt(h, c)), geall(t, c), KB.bnot_f(SV.lt(h, c), h1), h2)

def geall_mono(xs: List<&2, Nat>, +o: Nat, +c: Nat, +h: {geall(xs, o) == True{} : Bool}, +ho: {SV.lt(o, c) == False{} : Bool}) -> {geall(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ge_con(x, c, t, nlt_trans(x, o, c, ge_head(x, o, t, h), ho), geall_mono(t, o, c, ge_tail(x, o, t, h), ho))

def geall_up(xs: List<&2, Nat>, +c: Nat, +h: {geall(xs, 1n+c) == True{} : Bool}) -> {geall(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ge_con(x, c, t, KB.nlt_down(x, c, ge_head(x, 1n+c, t, h)), geall_up(t, c, ge_tail(x, 1n+c, t, h)))

def geall_cat_reps(n: Nat, +i: Nat, +ys: List<&2, Nat>, +h: {geall(ys, i) == True{} : Bool}) -> {geall(SV.cat(SV.reps(n, i), ys), i) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n++m:
      ge_con(i, i, SV.cat(SV.reps(m, i), ys), KB.lt_irr(i), geall_cat_reps(m, i, ys, h))

def sorted_cat_reps(n: Nat, +i: Nat, +ys: List<&2, Nat>, +hs: {sorted(ys) == True{} : Bool}, +hg: {geall(ys, i) == True{} : Bool}) -> {sorted(SV.cat(SV.reps(n, i), ys)) == True{} : Bool}:
  match n:
    case 0n:
      hs
    case 1n++m:
      LI.band_i(geall(SV.cat(SV.reps(m, i), ys), i), sorted(SV.cat(SV.reps(m, i), ys)), geall_cat_reps(m, i, ys, hg), sorted_cat_reps(m, i, ys, hs, hg))

def owners_ge(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat) -> {geall(SV.owners.go(es, cs, i), i) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      geall_up(SV.owners.go(es, t, 1n+i), i, owners_ge(es, t, 1n+i))
    case Con{SK.Rec{id, False{}, +k}, +t}:
      geall_cat_reps(SV.neqs(SK.Constraint.eqs(es, k)), i, SV.owners.go(es, t, 1n+i), geall_up(SV.owners.go(es, t, 1n+i), i, owners_ge(es, t, 1n+i)))

def owners_sorted(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat) -> {sorted(SV.owners.go(es, cs, i)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, t}:
      owners_sorted(es, t, 1n+i)
    case Con{SK.Rec{id, False{}, +k}, +t}:
      sorted_cat_reps(SV.neqs(SK.Constraint.eqs(es, k)), i, SV.owners.go(es, t, 1n+i), owners_sorted(es, t, 1n+i), geall_up(SV.owners.go(es, t, 1n+i), i, owners_ge(es, t, 1n+i)))

def sorted_owners(sk: SK.Sketch) -> {sorted(SV.owners(sk)) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      owners_sorted(es, cs, 0n)

def sorted_drop(k: Nat, xs: List<&2, Nat>, h: {sorted(xs) == True{} : Bool}) -> {sorted(ndrop(k, xs)) == True{} : Bool}:
  match k xs:
    case 0n xs:
      h
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{+x, +t}:
      sorted_drop(j, t, LI.band_r(geall(t, x), sorted(t), h))

# from an owner at c or later, every later owner is at c or later
def up_of(+xs: List<&2, Nat>, +k: Nat, +o: Nat, +t: List<&2, Nat>, +c: Nat, hs: {sorted(xs) == True{} : Bool}, hd: {ndrop(k, xs) == Con{o, t} : List<&2, Nat>}, ho: {SV.lt(o, c) == False{} : Bool}) -> {geall(t, c) == True{} : Bool}:
  geall_mono(t, o, c, LI.band_l(geall(t, o), sorted(t), (%hd : {sorted(_) == True{} : Bool}
    sorted_drop(k, xs, hs))), ho)

# Driven constraints own nothing
# ------------------------------

# no entry is c
def noc(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      SV.band(SV.bnot(SV.eq(h, c)), noc(t, c))

def ne_of_ge(x: Nat, c: Nat, h: {SV.lt(x, 1n+c) == False{} : Bool}) -> {SV.eq(x, c) == False{} : Bool}:
  match x c:
    case 0n 0n:
      absurd({SV.eq(0n, 0n) == False{} : Bool}, KA.tf(h))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      ne_of_ge(i, j, h)

def noc_of_ge(xs: List<&2, Nat>, +c: Nat, +h: {geall(xs, 1n+c) == True{} : Bool}) -> {noc(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.band_i(SV.bnot(SV.eq(x, c)), noc(t, c), KB.bnot_f(SV.eq(x, c), ne_of_ge(x, c, ge_head(x, 1n+c, t, h))), noc_of_ge(t, c, ge_tail(x, 1n+c, t, h)))

def noc_cat_reps(n: Nat, +i: Nat, +ys: List<&2, Nat>, +c: Nat, +hi: {SV.eq(i, c) == False{} : Bool}, +h: {noc(ys, c) == True{} : Bool}) -> {noc(SV.cat(SV.reps(n, i), ys), c) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n++m:
      LI.band_i(SV.bnot(SV.eq(i, c)), noc(SV.cat(SV.reps(m, i), ys), c), KB.bnot_f(SV.eq(i, c), hi), noc_cat_reps(m, i, ys, c, hi, h))

def noc_dr.t(b: Bool, +es: List<&2, SK.Ent>, +t: List<&2, SK.Rec>, +i: Nat, +c: Nat, +hi: {SV.lt(c, i) == False{} : Bool}, +e: {SV.eq(i, c) == b : Bool},
  ih: {SV.lt(c, 1n+i) == False{} : Bool} -> {noc(SV.owners.go(es, t, 1n+i), c) == True{} : Bool}) -> {noc(SV.owners.go(es, t, 1n+i), c) == True{} : Bool}:
  match b:
    case True{}:
      noc_of_ge(SV.owners.go(es, t, 1n+i), c, (%LI.eq_ok(i, c, e) : {geall(SV.owners.go(es, t, 1n+i), 1n+_) == True{} : Bool}
        owners_ge(es, t, 1n+i)))
    case False{}:
      ih(KB.lt_nle_s(i, c, KB.lt_of_nlt(i, c, hi, e)))

def drv_false(+csF: List<&2, SK.Rec>, +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, hd: {KB.rdrop(i, csF) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}) -> {SV.driven.at(csF, i) == False{} : Bool}:
  Equal.trans(Bool, SV.driven.at(csF, i), SV.driven.at(KB.rdrop(i, csF), 0n), False{}, KB.driven_drop(csF, i), Equal.cong(List<&2, SK.Rec>, Bool, x => SV.driven.at(x, 0n), KB.rdrop(i, csF), Con{SK.Rec{id, False{}, k}, t}, hd))

def noc_dr.f(b: Bool, +es: List<&2, SK.Ent>, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +c: Nat, +csF: List<&2, SK.Rec>, +id: Nat, +hi: {SV.lt(c, i) == False{} : Bool}, +e: {SV.eq(i, c) == b : Bool},
  hd: {KB.rdrop(i, csF) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, hdr: {SV.driven.at(csF, c) == True{} : Bool},
  ih: {SV.lt(c, 1n+i) == False{} : Bool} -> {noc(SV.owners.go(es, t, 1n+i), c) == True{} : Bool}) -> {noc(SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, k)), i), SV.owners.go(es, t, 1n+i)), c) == True{} : Bool}:
  match b:
    case True{}:
      absurd({noc(SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, k)), i), SV.owners.go(es, t, 1n+i)), c) == True{} : Bool},
        KA.ft(Equal.trans(Bool, False{}, SV.driven.at(csF, c), True{}, Equal.sym(Bool, SV.driven.at(csF, c), False{}, (%LI.eq_ok(i, c, e) : {SV.driven.at(csF, _) == False{} : Bool}
          drv_false(csF, i, id, k, t, hd))), hdr)))
    case False{}:
      noc_cat_reps(SV.neqs(SK.Constraint.eqs(es, k)), i, SV.owners.go(es, t, 1n+i), c, e, ih(KB.lt_nle_s(i, c, KB.lt_of_nlt(i, c, hi, e))))

# a driven constraint at c >= i owns none of the equations from i
def owners_noc(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +csF: List<&2, SK.Rec>, +c: Nat, +hd: {KB.rdrop(i, csF) == cs : List<&2, SK.Rec>}, +hi: {SV.lt(c, i) == False{} : Bool}, +hdr: {SV.driven.at(csF, c) == True{} : Bool})
  -> {noc(SV.owners.go(es, cs, i), c) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      noc_dr.t(SV.eq(i, c), es, t, i, c, hi, {==}, h2 => owners_noc(es, t, 1n+i, csF, c, KB.rdrop_step(i, csF, SK.Rec{id, True{}, k}, t, hd), h2, hdr))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      noc_dr.f(SV.eq(i, c), es, k, t, i, c, csF, id, hi, {==}, hd, hdr, h2 => owners_noc(es, t, 1n+i, csF, c, KB.rdrop_step(i, csF, SK.Rec{id, False{}, k}, t, hd), h2, hdr))

def noc_nth(xs: List<&2, Nat>, +c: Nat, +h: {noc(xs, c) == True{} : Bool}, k: Nat, hk: {SV.lt(k, SV.len(xs)) == True{} : Bool}) -> {SV.eq(SV.nth(xs, k), c) == False{} : Bool}:
  match xs k:
    case Nil{} k:
      absurd({SV.eq(SV.nth(Nil{}, k), c) == False{} : Bool}, KA.ft(Equal.trans(Bool, False{}, SV.lt(k, 0n), True{}, Equal.sym(Bool, SV.lt(k, 0n), False{}, KB.lt_z(k)), hk)))
    case Con{+x, +t} 0n:
      KB.bnot_t(SV.eq(x, c), LI.band_l(SV.bnot(SV.eq(x, c)), noc(t, c), h))
    case Con{+x, +t} 1n+j:
      noc_nth(t, c, LI.band_r(SV.bnot(SV.eq(x, c)), noc(t, c), h), j, hk)

# a driven constraint owns no equation
def driven_noown(sk: SK.Sketch, +c: Nat, +h: {SV.driven(sk, c) == True{} : Bool}, +k: Nat, +hk: {SV.lt(k, SV.len(SV.owners(sk))) == True{} : Bool}) -> {SV.eq(SV.nth(SV.owners(sk), k), c) == False{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      noc_nth(SV.owners.go(es, cs, 0n), c, owners_noc(es, cs, 0n, cs, c, {==}, KB.lt_z(c), h), k, hk)

# Owners are constraints
# ----------------------

def below_cat_reps(n: Nat, +i: Nat, +ys: List<&2, Nat>, +N: Nat, +hi: {SV.lt(i, N) == True{} : Bool}, +h: {SV.below(ys, N) == True{} : Bool}) -> {SV.below(SV.cat(SV.reps(n, i), ys), N) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n++m:
      LI.band_i(SV.lt(i, N), SV.below(SV.cat(SV.reps(m, i), ys), N), hi, below_cat_reps(m, i, ys, N, hi, h))

def owners_below(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +csF: List<&2, SK.Rec>, +hd: {KB.rdrop(i, csF) == cs : List<&2, SK.Rec>}) -> {SV.below(SV.owners.go(es, cs, i), SV.clen(csF)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      owners_below(es, t, 1n+i, csF, KB.rdrop_step(i, csF, SK.Rec{id, True{}, k}, t, hd))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      below_cat_reps(SV.neqs(SK.Constraint.eqs(es, k)), i, SV.owners.go(es, t, 1n+i), SV.clen(csF), KB.lt_drop(csF, i, SK.Rec{id, False{}, k}, t, hd), owners_below(es, t, 1n+i, csF, KB.rdrop_step(i, csF, SK.Rec{id, False{}, k}, t, hd)))

# every owner is below the number of constraints
def below_ncons(sk: SK.Sketch) -> {SV.below(SV.owners(sk), SV.ncons(sk)) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      owners_below(es, cs, 0n, cs, {==})
