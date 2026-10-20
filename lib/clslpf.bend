# bend-cad: what a list of classes says, position by position, for the
# single pass (PLAN-sk13a S4). Proofs only.
# - j is red (in reds(cls)) exactly when the class at j is (mem_reds);
# - when each class's dropped equations are its own constraint's (downs),
#   equation k is dropped exactly when its owner's class drops it
#   (mem_dropped);
# - the classes from position i (cdrop), and their head.

import Base
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./kbpf.bend as KB
import ./solvedpf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The classes from position i
# ---------------------------

def cdrop(k: Nat, cls: List<&2, SV.Class>) -> List<&2, SV.Class>:
  match k cls:
    case 0n cls:
      cls
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      cdrop(j, t)

def chd(cls: List<&2, SV.Class>) -> SV.Class:
  match cls:
    case Nil{}:
      SV.Kept{Nil{}}
    case Con{h, t}:
      h

def ctl(cls: List<&2, SV.Class>) -> List<&2, SV.Class>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def ca_drop(cls: List<&2, SV.Class>, i: Nat) -> {SV.class_at(cls, i) == chd(cdrop(i, cls)) : SV.Class}:
  match cls i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      ca_drop(t, j)

def ctl_drop(k: Nat, cls: List<&2, SV.Class>) -> {cdrop(1n+k, cls) == ctl(cdrop(k, cls)) : List<&2, SV.Class>}:
  match k cls:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, t}:
      ctl_drop(j, t)

# the class at i, the classes from i being x :: y
def ca_of(+cls: List<&2, SV.Class>, +i: Nat, +x: SV.Class, +y: List<&2, SV.Class>, h: {cdrop(i, cls) == Con{x, y} : List<&2, SV.Class>}) -> {SV.class_at(cls, i) == x : SV.Class}:
  Equal.trans(SV.Class, SV.class_at(cls, i), chd(cdrop(i, cls)), x, ca_drop(cls, i), Equal.cong(List<&2, SV.Class>, SV.Class, z => chd(z), cdrop(i, cls), Con{x, y}, h))

def cdrop_step(+cls: List<&2, SV.Class>, +i: Nat, +x: SV.Class, +y: List<&2, SV.Class>, h: {cdrop(i, cls) == Con{x, y} : List<&2, SV.Class>}) -> {cdrop(1n+i, cls) == y : List<&2, SV.Class>}:
  Equal.trans(List<&2, SV.Class>, cdrop(1n+i, cls), ctl(cdrop(i, cls)), y, ctl_drop(i, cls), Equal.cong(List<&2, SV.Class>, List<&2, SV.Class>, z => ctl(z), cdrop(i, cls), Con{x, y}, h))

# Booleans and numbers
# --------------------

def band_f(a: Bool, +b: Bool, h: {b == False{} : Bool}) -> {SV.band(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def band_t(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {SV.band(a, b) == a : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# i < 1 + (m + i)
def lt_add(+m: Nat, +i: Nat) -> {SV.lt(i, 1n+Nat.add(m, i)) == True{} : Bool}:
  Equal.trans(Bool, SV.lt(i, 1n+Nat.add(m, i)), KA.natle(1n+i, 1n+Nat.add(m, i)), True{}, LI.lt_sv(i, 1n+Nat.add(m, i)), KA.natle_add_l(m, i))

def ne_add(+m: Nat, +i: Nat) -> {SV.eq(1n+Nat.add(m, i), i) == False{} : Bool}:
  KB.ne_of_lt(i, 1n+Nat.add(m, i), lt_add(m, i))

# Red positions
# -------------

# the class at absolute position j is red, cls starting at i
def rjk(cls: List<&2, SV.Class>, +i: Nat, +j: Nat) -> Bool:
  match cls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      SV.bor(SV.band(SV.is_red(h), SV.eq(j, i)), rjk(t, 1n+i, j))

def rr.c(b: Bool, +i: Nat, +j: Nat, +R: List<&2, Nat>, +r: Bool, ih: {SV.mem(j, R) == r : Bool}) -> {SV.mem(j, SV.pos.pick(b, i, R)) == SV.bor(SV.band(b, SV.eq(j, i)), r) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.mem(j, R), r, ih) : {SV.bor(SV.eq(j, i), _) == SV.bor(SV.eq(j, i), r) : Bool}
      {==}
    case False{}:
      ih

def mem_reds_rjk(cls: List<&2, SV.Class>, +i: Nat, +j: Nat) -> {SV.mem(j, SV.reds.go(cls, i)) == rjk(cls, i, j) : Bool}:
  match cls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      rr.c(SV.is_red(h), i, j, SV.reds.go(t, 1n+i), rjk(t, 1n+i, j), mem_reds_rjk(t, 1n+i, j))

def rjk_lt(cls: List<&2, SV.Class>, +i: Nat, +j: Nat, +h: {SV.lt(j, i) == True{} : Bool}) -> {rjk(cls, i, j) == False{} : Bool}:
  match cls:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.bor_f(SV.band(SV.is_red(x), SV.eq(j, i)), rjk(t, 1n+i, j), band_f(SV.is_red(x), SV.eq(j, i), Equal.trans(Bool, SV.eq(j, i), SV.eq(i, j), False{}, LI.eq_sym(j, i), KB.ne_of_lt(j, i, h))),
        rjk_lt(t, 1n+i, j, KB.lt_up(j, i, h)))

def rjk_at(cls: List<&2, SV.Class>, +i: Nat, m: Nat) -> {rjk(cls, i, Nat.add(m, i)) == SV.is_red(SV.class_at(cls, m)) : Bool}:
  match cls m:
    case Nil{} m:
      {==}
    case Con{+h, +t} 0n:
      %Equal.sym(Bool, rjk(t, 1n+i, i), False{}, rjk_lt(t, 1n+i, i, KB.lt_succ(i))) : {SV.bor(SV.band(SV.is_red(h), SV.eq(i, i)), _) == SV.is_red(h) : Bool}
      %Equal.sym(Bool, SV.band(SV.is_red(h), SV.eq(i, i)), SV.is_red(h), band_t(SV.is_red(h), SV.eq(i, i), LI.eq_refl(i))) : {SV.bor(_, False{}) == SV.is_red(h) : Bool}
      KB.bor_f(SV.is_red(h))
    case Con{+h, +t} 1n++k:
      %Equal.sym(Bool, SV.band(SV.is_red(h), SV.eq(1n+Nat.add(k, i), i)), False{}, band_f(SV.is_red(h), SV.eq(1n+Nat.add(k, i), i), ne_add(k, i))) : {SV.bor(_, rjk(t, 1n+i, 1n+Nat.add(k, i))) == SV.is_red(SV.class_at(t, k)) : Bool}
      %Equal.sym(Nat, 1n+Nat.add(k, i), Nat.add(k, 1n+i), LN.add_succ(k, i)) : {rjk(t, 1n+i, _) == SV.is_red(SV.class_at(t, k)) : Bool}
      rjk_at(t, 1n+i, k)

# j is red exactly when its class is
def mem_reds(+cls: List<&2, SV.Class>, +j: Nat) -> {SV.mem(j, SV.reds(cls)) == SV.is_red(SV.class_at(cls, j)) : Bool}:
  Equal.trans(Bool, SV.mem(j, SV.reds(cls)), rjk(cls, 0n, j), SV.is_red(SV.class_at(cls, j)), mem_reds_rjk(cls, 0n, j),
    (%Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {rjk(cls, 0n, _) == SV.is_red(SV.class_at(cls, j)) : Bool}
      rjk_at(cls, 0n, j)))

# Dropped equations
# -----------------

# each class's dropped equations (from position i) are owned by its
# constraint
def downs(+own: List<&2, Nat>, cls: List<&2, SV.Class>, +i: Nat) -> Bool:
  match cls:
    case Nil{}:
      True{}
    case Con{h, t}:
      SV.band(KB.allo(own, SV.kdrops(h), i), downs(own, t, 1n+i))

def dk.pick(b: Bool, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

# the dropped equations of the class at absolute position o, cls starting
# at i
def dk_abs(cls: List<&2, SV.Class>, +i: Nat, +o: Nat) -> List<&2, Nat>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      dk.pick(SV.eq(o, i), SV.kdrops(h), dk_abs(t, 1n+i, o))

def dk_lt(cls: List<&2, SV.Class>, +i: Nat, +o: Nat, +h: {SV.lt(o, i) == True{} : Bool}) -> {dk_abs(cls, i, o) == Nil{} : List<&2, Nat>}:
  match cls:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Bool, SV.eq(o, i), False{}, Equal.trans(Bool, SV.eq(o, i), SV.eq(i, o), False{}, LI.eq_sym(o, i), KB.ne_of_lt(o, i, h))) : {dk.pick(_, SV.kdrops(x), dk_abs(t, 1n+i, o)) == Nil{} : List<&2, Nat>}
      dk_lt(t, 1n+i, o, KB.lt_up(o, i, h))

def dk_at(cls: List<&2, SV.Class>, +i: Nat, m: Nat) -> {dk_abs(cls, i, Nat.add(m, i)) == SV.kdrops(SV.class_at(cls, m)) : List<&2, Nat>}:
  match cls m:
    case Nil{} m:
      {==}
    case Con{+h, +t} 0n:
      %Equal.sym(Bool, SV.eq(i, i), True{}, LI.eq_refl(i)) : {dk.pick(_, SV.kdrops(h), dk_abs(t, 1n+i, i)) == SV.kdrops(h) : List<&2, Nat>}
      {==}
    case Con{+h, +t} 1n++k:
      %Equal.sym(Bool, SV.eq(1n+Nat.add(k, i), i), False{}, ne_add(k, i)) : {dk.pick(_, SV.kdrops(h), dk_abs(t, 1n+i, 1n+Nat.add(k, i))) == SV.kdrops(SV.class_at(t, k)) : List<&2, Nat>}
      %Equal.sym(Nat, 1n+Nat.add(k, i), Nat.add(k, 1n+i), LN.add_succ(k, i)) : {dk_abs(t, 1n+i, _) == SV.kdrops(SV.class_at(t, k)) : List<&2, Nat>}
      dk_at(t, 1n+i, k)

def allo_nm.c(b: Bool, +own: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +i: Nat, +k: Nat, e: {SV.eq(k, x) == b : Bool}, hx: {SV.eq(SV.nth(own, x), i) == True{} : Bool},
  hk: {SV.eq(SV.nth(own, k), i) == False{} : Bool}, ih: {SV.mem(k, t) == False{} : Bool}) -> {SV.bor(b, SV.mem(k, t)) == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.eq(SV.nth(own, k), i), False{}, (%Equal.sym(Nat, k, x, LI.eq_ok(k, x, e)) : {True{} == SV.eq(SV.nth(own, _), i) : Bool}
        Equal.sym(Bool, SV.eq(SV.nth(own, x), i), True{}, hx)), hk)))
    case False{}:
      ih

# all of xs owned by i, k not: k is not in xs
def allo_nm(+own: List<&2, Nat>, xs: List<&2, Nat>, +i: Nat, +k: Nat, +h: {KB.allo(own, xs, i) == True{} : Bool}, +hk: {SV.eq(SV.nth(own, k), i) == False{} : Bool}) -> {SV.mem(k, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      allo_nm.c(SV.eq(k, x), own, x, t, i, k, {==}, LI.band_l(SV.eq(SV.nth(own, x), i), KB.allo(own, t, i), h), hk, allo_nm(own, t, i, k, LI.band_r(SV.eq(SV.nth(own, x), i), KB.allo(own, t, i), h), hk))

def md.c(b: Bool, +own: List<&2, Nat>, +h: SV.Class, +t: List<&2, SV.Class>, +i: Nat, +k: Nat, e: {SV.eq(SV.nth(own, k), i) == b : Bool}, ha: {KB.allo(own, SV.kdrops(h), i) == True{} : Bool},
  ih: {SV.mem(k, SV.dropped(t)) == SV.mem(k, dk_abs(t, 1n+i, SV.nth(own, k))) : Bool})
  -> {SV.bor(SV.mem(k, SV.kdrops(h)), SV.mem(k, SV.dropped(t))) == SV.mem(k, dk.pick(b, SV.kdrops(h), dk_abs(t, 1n+i, SV.nth(own, k)))) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, SV.mem(k, SV.dropped(t)), SV.mem(k, dk_abs(t, 1n+i, SV.nth(own, k))), ih) : {SV.bor(SV.mem(k, SV.kdrops(h)), _) == SV.mem(k, SV.kdrops(h)) : Bool}
      %Equal.sym(List<&2, Nat>, dk_abs(t, 1n+i, SV.nth(own, k)), Nil{}, dk_lt(t, 1n+i, SV.nth(own, k), (%Equal.sym(Nat, SV.nth(own, k), i, LI.eq_ok(SV.nth(own, k), i, e)) : {SV.lt(_, 1n+i) == True{} : Bool}
        KB.lt_succ(i)))) : {SV.bor(SV.mem(k, SV.kdrops(h)), SV.mem(k, _)) == SV.mem(k, SV.kdrops(h)) : Bool}
      KB.bor_f(SV.mem(k, SV.kdrops(h)))
    case False{}:
      %Equal.sym(Bool, SV.mem(k, SV.kdrops(h)), False{}, allo_nm(own, SV.kdrops(h), i, k, ha, e)) : {SV.bor(_, SV.mem(k, SV.dropped(t))) == SV.mem(k, dk_abs(t, 1n+i, SV.nth(own, k))) : Bool}
      ih

def mem_dropped_dk(+own: List<&2, Nat>, cls: List<&2, SV.Class>, +i: Nat, +k: Nat, +hd: {downs(own, cls, i) == True{} : Bool}) -> {SV.mem(k, SV.dropped(cls)) == SV.mem(k, dk_abs(cls, i, SV.nth(own, k))) : Bool}:
  match cls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, SV.mem(k, SV.cat(SV.kdrops(h), SV.dropped(t))), SV.bor(SV.mem(k, SV.kdrops(h)), SV.mem(k, SV.dropped(t))), SP.mem_cat(k, SV.kdrops(h), SV.dropped(t))) : {_ == SV.mem(k, dk.pick(SV.eq(SV.nth(own, k), i), SV.kdrops(h), dk_abs(t, 1n+i, SV.nth(own, k)))) : Bool}
      md.c(SV.eq(SV.nth(own, k), i), own, h, t, i, k, {==}, LI.band_l(KB.allo(own, SV.kdrops(h), i), downs(own, t, 1n+i), hd),
        mem_dropped_dk(own, t, 1n+i, k, LI.band_r(KB.allo(own, SV.kdrops(h), i), downs(own, t, 1n+i), hd)))

# with each class dropping only its own: k is dropped exactly when its
# owner's class drops it
def mem_dropped(+own: List<&2, Nat>, +cls: List<&2, SV.Class>, +k: Nat, +hd: {downs(own, cls, 0n) == True{} : Bool}) -> {SV.mem(k, SV.dropped(cls)) == SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(own, k)))) : Bool}:
  Equal.trans(Bool, SV.mem(k, SV.dropped(cls)), SV.mem(k, dk_abs(cls, 0n, SV.nth(own, k))), SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(own, k)))), mem_dropped_dk(own, cls, 0n, k, hd),
    (%Equal.sym(Nat, SV.nth(own, k), Nat.add(SV.nth(own, k), 0n), LN.add_zero(SV.nth(own, k))) : {SV.mem(k, dk_abs(cls, 0n, _)) == SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(own, k)))) : Bool}
      Equal.cong(List<&2, Nat>, Bool, z => SV.mem(k, z), dk_abs(cls, 0n, Nat.add(SV.nth(own, k), 0n)), SV.kdrops(SV.class_at(cls, SV.nth(own, k))), dk_at(cls, 0n, SV.nth(own, k)))))
