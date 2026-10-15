# bend-cad: balls, for solve_complete (DESIGN §10.4, C3a). Proofs only.
#
# F is its own computing numbers (fnum: compared by lt_total, every
# rational held; femb: the identity map), so the K-generic ball lemmas of
# lib/kball.bend also hold for balls centered at points of F. A ball's
# center is the value at the box's centers (kball_c), and a slope ball's
# center is the slope between the centers and themselves, which is the
# derivative there (ksl_c, sl_deriv), whatever the radii. A ball's radius
# is at most a Lipschitz constant times the box's radius (kball_grade,
# ksl_grade: ball tightness), so in fnum(F) values and slopes move by at
# most that much across a box (eval_lip, sl_lip). Renaming variables
# commutes with derivatives (deriv_rnv, deriv_rename).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./slope.bend as SL
import ./struct.bend as ST
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./qemb.bend as QE

# Equations in F
# --------------

def cadd(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.add(F, a1, b1) == O.add(F, a2, b2) : O.C(F)}:
  %ea : {O.add(F, a1, b1) == O.add(F, _, b2) : O.C(F)}
  %eb : {O.add(F, a1, b1) == O.add(F, a1, _) : O.C(F)}
  {==}

def csub(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.sub(~F, a1, b1) == O.sub(~F, a2, b2) : O.C(F)}:
  %ea : {O.sub(~F, a1, b1) == O.sub(~F, _, b2) : O.C(F)}
  %eb : {O.sub(~F, a1, b1) == O.sub(~F, a1, _) : O.C(F)}
  {==}

def cmul(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.mul(F, a1, b1) == O.mul(F, a2, b2) : O.C(F)}:
  %ea : {O.mul(F, a1, b1) == O.mul(F, _, b2) : O.C(F)}
  %eb : {O.mul(F, a1, b1) == O.mul(F, a1, _) : O.C(F)}
  {==}

def cneg(~F: O.OField, +a1: O.C(F), +a2: O.C(F), ea: {a1 == a2 : O.C(F)}) -> {O.neg(F, a1) == O.neg(F, a2) : O.C(F)}:
  %ea : {O.neg(F, a1) == O.neg(F, _) : O.C(F)}
  {==}

# F as computing numbers
# ----------------------

def fcmp.go(~F: O.OField, +a: O.C(F), +b: O.C(F), t: Or(O.lt(F, a, b), Or({a == b : O.C(F)}, O.lt(F, b, a)))) -> Cmp:
  match t:
    case Inl{l}:
      LT{}
    case Inr{Inl{e}}:
      EQ{}
    case Inr{Inr{g}}:
      GT{}

def fcmp(~F: O.OField, +a: O.C(F), +b: O.C(F)) -> Cmp:
  fcmp.go(~F, a, b, O.lt_total(F)(a, b))

# F's own numbers: every rational is held
def fnum(~F: O.OField) -> N.Num:
  N.Num{O.C(F), O.zero(F), O.one(F), a => b => O.add(F, a, b), a => b => O.mul(F, a, b), a => O.neg(F, a), a => b => fcmp(~F, a, b), q => Some{O.ofq(~F, q)}}

def fcmp_ok.go(~F: O.OField, +a: O.C(F), +b: O.C(F), t: Or(O.lt(F, a, b), Or({a == b : O.C(F)}, O.lt(F, b, a)))) -> N.cmeans(F, fcmp.go(~F, a, b, t), a, b):
  match t:
    case Inl{l}:
      l
    case Inr{Inl{e}}:
      e
    case Inr{Inr{g}}:
      g

def fcmp_ok(~F: O.OField, +a: O.C(F), +b: O.C(F)) -> N.cmeans(F, fcmp(~F, a, b), a, b):
  fcmp_ok.go(~F, a, b, O.lt_total(F)(a, b))

def mget(~F: O.OField, m: Maybe<&2, O.C(F)>) -> O.C(F):
  match m:
    case None{}:
      O.zero(F)
    case Some{k}:
      k

def fofq_ok(~F: O.OField, +q: S.Q, +k: O.C(F), h: {Some{O.ofq(~F, q)} == Some{k} : Maybe<&2, O.C(F)>}) -> {k == O.ofq(~F, q) : O.C(F)}:
  Equal.sym(O.C(F), O.ofq(~F, q), k, Equal.cong(Maybe<&2, O.C(F)>, O.C(F), m => mget(~F, m), Some{O.ofq(~F, q)}, Some{k}, h))

# the identity map
def femb(~F: O.OField) -> N.Emb<fnum(~F), F>:
  N.Emb{x => x, {==}, {==}, a => b => {==}, a => b => {==}, a => {==}, a => b => fcmp_ok(~F, a, b), q => k => h => fofq_ok(~F, q, k, h)}

# every constant is held
def held_f(~F: O.OField, e: E.QExpr) -> {KB.held(~fnum(~F), e) == True{} : Bool}:
  match e:
    case E.QVar{i}:
      {==}
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      %Equal.sym(Bool, KB.held(~fnum(~F), a), True{}, held_f(~F, a)) : {KA.band(_, KB.held(~fnum(~F), b)) == True{} : Bool}
      held_f(~F, b)
    case E.QSub{+a, +b}:
      %Equal.sym(Bool, KB.held(~fnum(~F), a), True{}, held_f(~F, a)) : {KA.band(_, KB.held(~fnum(~F), b)) == True{} : Bool}
      held_f(~F, b)
    case E.QMul{+a, +b}:
      %Equal.sym(Bool, KB.held(~fnum(~F), a), True{}, held_f(~F, a)) : {KA.band(_, KB.held(~fnum(~F), b)) == True{} : Bool}
      held_f(~F, b)
    case E.QNeg{a}:
      held_f(~F, a)

def ofkv_id(~F: O.OField, v: M.Vec(~F)) -> {N.ofkv(~fnum(~F), ~F, ~femb(~F), v) == v : M.Vec(~F)}:
  match v:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      %Equal.sym(M.Vec(~F), N.ofkv(~fnum(~F), ~F, ~femb(~F), xs), xs, ofkv_id(~F, xs)) : {Con{x, _} == Con{x, xs} : M.Vec(~F)}
      {==}

# Ball centers
# ------------

# the box's centers in F
def cen(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, box: List<&2, KB.KB<K>>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, KB.bcenters(~K, box))

def cadd_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, x: KB.KB<K>, y: KB.KB<K>, +va: O.C(F), +vb: O.C(F), ea: {N.emap(K, F, H, KB.KB.c(K, x)) == va : O.C(F)}, eb: {N.emap(K, F, H, KB.KB.c(K, y)) == vb : O.C(F)}) -> {N.emap(K, F, H, KB.KB.c(K, KB.badd(~K, x, y))) == O.add(F, va, vb) : O.C(F)}:
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      %KA.ea(~K, ~F, ~H, c1, c2) : {_ == O.add(F, va, vb) : O.C(F)}
      cadd(~F, N.emap(K, F, H, c1), va, N.emap(K, F, H, c2), vb, ea, eb)

def cneg_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, x: KB.KB<K>, +va: O.C(F), ea: {N.emap(K, F, H, KB.KB.c(K, x)) == va : O.C(F)}) -> {N.emap(K, F, H, KB.KB.c(K, KB.bneg(~K, x))) == O.neg(F, va) : O.C(F)}:
  match x:
    case KB.KB{+c, +r}:
      %KA.en(~K, ~F, ~H, c) : {_ == O.neg(F, va) : O.C(F)}
      cneg(~F, N.emap(K, F, H, c), va, ea)

def cmul_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, x: KB.KB<K>, y: KB.KB<K>, +va: O.C(F), +vb: O.C(F), ea: {N.emap(K, F, H, KB.KB.c(K, x)) == va : O.C(F)}, eb: {N.emap(K, F, H, KB.KB.c(K, y)) == vb : O.C(F)}) -> {N.emap(K, F, H, KB.KB.c(K, KB.bmul(~K, x, y))) == O.mul(F, va, vb) : O.C(F)}:
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      %KA.em(~K, ~F, ~H, c1, c2) : {_ == O.mul(F, va, vb) : O.C(F)}
      cmul(~F, N.emap(K, F, H, c1), va, N.emap(K, F, H, c2), vb, ea, eb)

def blook_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, box: List<&2, KB.KB<K>>, i: Nat) -> {N.emap(K, F, H, KB.KB.c(K, KB.blook(~K, box, i))) == O.lookup(~F, cen(~K, ~F, ~H, box), i) : O.C(F)}:
  match box i:
    case Nil{} 0n:
      N.e_zero(K, F, H)
    case Nil{} 1n+j:
      N.e_zero(K, F, H)
    case Con{b, bs} 0n:
      {==}
    case Con{b, bs} 1n+j:
      blook_c(~K, ~F, ~H, bs, j)

def kind_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Bool) -> {N.emap(K, F, H, KB.KB.c(K, KB.kind(~K, b))) == SL.find(~F, b) : O.C(F)}:
  match b:
    case True{}:
      N.e_one(K, F, H)
    case False{}:
      N.e_zero(K, F, H)

# the center of e's ball is e at the box's centers
def kball_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> {N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, box, e))) == O.eval(~F, cen(~K, ~F, ~H, box), e) : O.C(F)}:
  match e:
    case E.QVar{i}:
      blook_c(~K, ~F, ~H, box, i)
    case E.QCst{+q}:
      KB.kcst_ok(~K, ~F, ~H, q, hh)
    case E.QAdd{+a, +b}:
      cadd_c(~K, ~F, ~H, KB.kball(~K, box, a), KB.kball(~K, box, b), O.eval(~F, cen(~K, ~F, ~H, box), a), O.eval(~F, cen(~K, ~F, ~H, box), b), kball_c(~K, ~F, ~H, box, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), kball_c(~K, ~F, ~H, box, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      cadd_c(~K, ~F, ~H, KB.kball(~K, box, a), KB.bneg(~K, KB.kball(~K, box, b)), O.eval(~F, cen(~K, ~F, ~H, box), a), O.neg(F, O.eval(~F, cen(~K, ~F, ~H, box), b)), kball_c(~K, ~F, ~H, box, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), cneg_c(~K, ~F, ~H, KB.kball(~K, box, b), O.eval(~F, cen(~K, ~F, ~H, box), b), kball_c(~K, ~F, ~H, box, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      cmul_c(~K, ~F, ~H, KB.kball(~K, box, a), KB.kball(~K, box, b), O.eval(~F, cen(~K, ~F, ~H, box), a), O.eval(~F, cen(~K, ~F, ~H, box), b), kball_c(~K, ~F, ~H, box, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), kball_c(~K, ~F, ~H, box, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QNeg{+a}:
      cneg_c(~K, ~F, ~H, KB.kball(~K, box, a), O.eval(~F, cen(~K, ~F, ~H, box), a), kball_c(~K, ~F, ~H, box, a, hh))

# the center of e's slope ball is e's slope between the centers and
# themselves
def ksl_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +i: Nat, +box: List<&2, KB.KB<K>>, e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> {N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, box, e))) == SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e) : O.C(F)}:
  match e:
    case E.QVar{j}:
      kind_c(~K, ~F, ~H, KA.nateq(i, j))
    case E.QCst{q}:
      N.e_zero(K, F, H)
    case E.QAdd{+a, +b}:
      cadd_c(~K, ~F, ~H, KB.ksl(~K, i, box, a), KB.ksl(~K, i, box, b), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), a), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), b), ksl_c(~K, ~F, ~H, i, box, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), ksl_c(~K, ~F, ~H, i, box, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      cadd_c(~K, ~F, ~H, KB.ksl(~K, i, box, a), KB.bneg(~K, KB.ksl(~K, i, box, b)), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), a), O.neg(F, SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), b)), ksl_c(~K, ~F, ~H, i, box, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), cneg_c(~K, ~F, ~H, KB.ksl(~K, i, box, b), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), b), ksl_c(~K, ~F, ~H, i, box, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      +ha = KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)
      +hb = KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)
      cadd_c(~K, ~F, ~H, KB.bmul(~K, KB.kball(~K, box, a), KB.ksl(~K, i, box, b)), KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)), O.mul(F, O.eval(~F, cen(~K, ~F, ~H, box), a), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), b)), O.mul(F, O.eval(~F, cen(~K, ~F, ~H, box), b), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), a)),
        cmul_c(~K, ~F, ~H, KB.kball(~K, box, a), KB.ksl(~K, i, box, b), O.eval(~F, cen(~K, ~F, ~H, box), a), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), b), kball_c(~K, ~F, ~H, box, a, ha), ksl_c(~K, ~F, ~H, i, box, b, hb)),
        cmul_c(~K, ~F, ~H, KB.kball(~K, box, b), KB.ksl(~K, i, box, a), O.eval(~F, cen(~K, ~F, ~H, box), b), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), a), kball_c(~K, ~F, ~H, box, b, hb), ksl_c(~K, ~F, ~H, i, box, a, ha)))
    case E.QNeg{+a}:
      cneg_c(~K, ~F, ~H, KB.ksl(~K, i, box, a), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), a), ksl_c(~K, ~F, ~H, i, box, a, hh))

# Slopes at equal points
# ----------------------

def nateq_flip(a: Nat, b: Nat) -> {KA.nateq(a, b) == DV.eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      nateq_flip(i, j)

def dvar_ok(~F: O.OField, +x: M.Vec(~F), b: Bool) -> {SL.find(~F, b) == O.eval(~F, x, DV.dvar(b)) : O.C(F)}:
  match b:
    case True{}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Zpos{S.XH{}}, S.XH{}}), O.one(F), QE.ofq_one(~F))
    case False{}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))

# the slope between a point and itself is the derivative there
def sl_deriv(~F: O.OField, +i: Nat, +x: M.Vec(~F), e: E.QExpr) -> {SL.sl(~F, i, x, x, e) == O.eval(~F, x, DV.deriv(e, i)) : O.C(F)}:
  match e:
    case E.QVar{+j}:
      %Equal.sym(Bool, KA.nateq(i, j), DV.eq(j, i), nateq_flip(i, j)) : {SL.find(~F, _) == O.eval(~F, x, DV.dvar(DV.eq(j, i))) : O.C(F)}
      dvar_ok(~F, x, DV.eq(j, i))
    case E.QCst{q}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case E.QAdd{+a, +b}:
      cadd(~F, SL.sl(~F, i, x, x, a), O.eval(~F, x, DV.deriv(a, i)), SL.sl(~F, i, x, x, b), O.eval(~F, x, DV.deriv(b, i)), sl_deriv(~F, i, x, a), sl_deriv(~F, i, x, b))
    case E.QSub{+a, +b}:
      csub(~F, SL.sl(~F, i, x, x, a), O.eval(~F, x, DV.deriv(a, i)), SL.sl(~F, i, x, x, b), O.eval(~F, x, DV.deriv(b, i)), sl_deriv(~F, i, x, a), sl_deriv(~F, i, x, b))
    case E.QMul{+a, +b}:
      %Equal.sym(O.C(F), SL.sl(~F, i, x, x, b), O.eval(~F, x, DV.deriv(b, i)), sl_deriv(~F, i, x, b)) : {O.add(F, O.mul(F, O.eval(~F, x, a), _), O.mul(F, O.eval(~F, x, b), SL.sl(~F, i, x, x, a))) == O.add(F, O.mul(F, O.eval(~F, x, DV.deriv(a, i)), O.eval(~F, x, b)), O.mul(F, O.eval(~F, x, a), O.eval(~F, x, DV.deriv(b, i)))) : O.C(F)}
      %Equal.sym(O.C(F), SL.sl(~F, i, x, x, a), O.eval(~F, x, DV.deriv(a, i)), sl_deriv(~F, i, x, a)) : {O.add(F, O.mul(F, O.eval(~F, x, a), O.eval(~F, x, DV.deriv(b, i))), O.mul(F, O.eval(~F, x, b), _)) == O.add(F, O.mul(F, O.eval(~F, x, DV.deriv(a, i)), O.eval(~F, x, b)), O.mul(F, O.eval(~F, x, a), O.eval(~F, x, DV.deriv(b, i)))) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, x, a), O.eval(~F, x, b), O.eval(~F, x, DV.deriv(a, i)), O.eval(~F, x, DV.deriv(b, i))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})
    case E.QNeg{+a}:
      cneg(~F, SL.sl(~F, i, x, x, a), O.eval(~F, x, DV.deriv(a, i)), sl_deriv(~F, i, x, a))

# the centers of e's slope balls in cnt variables from lo
def krange_c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}, cnt: Nat, +lo: Nat) -> {N.ofkv(~K, ~F, ~H, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo))) == SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, cnt, lo) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(O.C(F), N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, lo, box, e))), SL.sl(~F, lo, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e), ksl_c(~K, ~F, ~H, lo, box, e, hh)) : {Con{_, N.ofkv(~K, ~F, ~H, KB.bcenters(~K, KB.krange(~K, box, e, k, 1n+lo)))} == Con{SL.sl(~F, lo, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e), SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, k, 1n+lo)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, KB.bcenters(~K, KB.krange(~K, box, e, k, 1n+lo))), SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, k, 1n+lo), krange_c(~K, ~F, ~H, box, e, hh, k, 1n+lo)) : {Con{SL.sl(~F, lo, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e), _} == Con{SL.sl(~F, lo, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e), SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, k, 1n+lo)} : M.Vec(~F)}
      {==}

# slopes at equal points, in cnt variables from lo, are a Jacobian row
def srange_jrow(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, cnt: Nat, +lo: Nat) -> {SL.srange(~F, x, x, e, cnt, lo) == DV.jrow(~F, x, e, ST.iota(cnt, lo)) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(O.C(F), SL.sl(~F, lo, x, x, e), O.eval(~F, x, DV.deriv(e, lo)), sl_deriv(~F, lo, x, e)) : {Con{_, SL.srange(~F, x, x, e, k, 1n+lo)} == Con{O.eval(~F, x, DV.deriv(e, lo)), DV.jrow(~F, x, e, ST.iota(k, 1n+lo))} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), SL.srange(~F, x, x, e, k, 1n+lo), DV.jrow(~F, x, e, ST.iota(k, 1n+lo)), srange_jrow(~F, x, e, k, 1n+lo)) : {Con{O.eval(~F, x, DV.deriv(e, lo)), _} == Con{O.eval(~F, x, DV.deriv(e, lo)), DV.jrow(~F, x, e, ST.iota(k, 1n+lo))} : M.Vec(~F)}
      {==}

# the checker's slope centers are the Jacobian at the box's centers
def mcen_jac(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~K, eqs) == True{} : Bool}) -> {N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))) == DV.jac(~F, cen(~K, ~F, ~H, box), eqs, ST.iota(cnt, lo)) : M.Mat(~F)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      +he = KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh)
      %Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo))), SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, cnt, lo), krange_c(~K, ~F, ~H, box, e, he, cnt, lo)) : {Con{_, N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, es)))} == Con{DV.jrow(~F, cen(~K, ~F, ~H, box), e, ST.iota(cnt, lo)), DV.jac(~F, cen(~K, ~F, ~H, box), es, ST.iota(cnt, lo))} : M.Mat(~F)}
      %Equal.sym(M.Vec(~F), SL.srange(~F, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e, cnt, lo), DV.jrow(~F, cen(~K, ~F, ~H, box), e, ST.iota(cnt, lo)), srange_jrow(~F, cen(~K, ~F, ~H, box), e, cnt, lo)) : {Con{_, N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, es)))} == Con{DV.jrow(~F, cen(~K, ~F, ~H, box), e, ST.iota(cnt, lo)), DV.jac(~F, cen(~K, ~F, ~H, box), es, ST.iota(cnt, lo))} : M.Mat(~F)}
      %Equal.sym(M.Mat(~F), N.ofkm(~K, ~F, ~H, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, es))), DV.jac(~F, cen(~K, ~F, ~H, box), es, ST.iota(cnt, lo)), mcen_jac(~K, ~F, ~H, box, cnt, lo, es, KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh))) : {Con{DV.jrow(~F, cen(~K, ~F, ~H, box), e, ST.iota(cnt, lo)), _} == Con{DV.jrow(~F, cen(~K, ~F, ~H, box), e, ST.iota(cnt, lo)), DV.jac(~F, cen(~K, ~F, ~H, box), es, ST.iota(cnt, lo))} : M.Mat(~F)}
      {==}

# Order helpers
# -------------

# a <= b and c <= d give a + c <= b + d
def le_add2(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), h1: O.le(~F, a, b), h2: O.le(~F, c, d)) -> O.le(~F, O.add(F, a, c), O.add(F, b, d)):
  FV.le_of_sub(~F, O.add(F, a, c), O.add(F, b, d), FM.nn_eq(~F, O.sub(~F, O.add(F, b, d), O.add(F, a, c)), O.add(F, O.sub(~F, b, a), O.sub(~F, d, c)), FR.fring_eq(~F, [a, b, c, d], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, b, a), O.sub(~F, d, c), FM.sub_nonneg(~F, a, b, h1), FM.sub_nonneg(~F, c, d, h2))))

# 0 <= 0 rho
def zl(~F: O.OField, +rho: O.C(F)) -> O.le(~F, O.zero(F), O.mul(F, O.zero(F), rho)):
  FM.nn_eq(~F, O.mul(F, O.zero(F), rho), O.zero(F), Equal.sym(O.C(F), O.mul(F, O.zero(F), rho), O.zero(F), FL.zero_mul(~F, rho)), FO.le_refl(~F, O.zero(F)))

# 0 <= 1 rho, for 0 <= rho
def ol(~F: O.OField, +rho: O.C(F), h: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), O.mul(F, O.one(F), rho)):
  FM.nn_eq(~F, O.mul(F, O.one(F), rho), rho, FR.fring_eq(~F, [rho], E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, {==}), h)

def kabs_le.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cmp, +a: N.NC(K), +s: O.C(F), h: M.bnd(~F, N.emap(K, F, H, a), s)) -> O.le(~F, N.emap(K, F, H, KA.kabs.go(~K, c, a)), s):
  match c:
    case LT{}:
      (h1, h2) = h
      %KA.en(~K, ~F, ~H, a) : O.le(~F, _, s)
      FV.le_of_sub(~F, O.neg(F, N.emap(K, F, H, a)), s, FM.nn_eq(~F, O.sub(~F, s, O.neg(F, N.emap(K, F, H, a))), O.add(F, s, N.emap(K, F, H, a)), FR.fring_eq(~F, [s, N.emap(K, F, H, a)], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, {==}), h2))
    case EQ{}:
      (h1, h2) = h
      FV.le_of_sub(~F, N.emap(K, F, H, a), s, h1)
    case GT{}:
      (h1, h2) = h
      FV.le_of_sub(~F, N.emap(K, F, H, a), s, h1)

# |H a| <= s gives H |a| <= s
def kabs_le(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +s: O.C(F), h: M.bnd(~F, N.emap(K, F, H, a), s)) -> O.le(~F, N.emap(K, F, H, KA.kabs(~K, a)), s):
  kabs_le.go(~K, ~F, ~H, N.ncmp(K, a, N.nzero(K)), a, s, h)

# Grades
# ------
# With bb a bound on |c| + r over the box's balls: an expression's
# magnitude mj and Lipschitz constant lp, and its slopes' ms and ls.

def mj(~F: O.OField, +bb: O.C(F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{i}:
      bb
    case E.QCst{q}:
      FV.fabs(~F, O.ofq(~F, q))
    case E.QAdd{a, b}:
      O.add(F, mj(~F, bb, a), mj(~F, bb, b))
    case E.QSub{a, b}:
      O.add(F, mj(~F, bb, a), mj(~F, bb, b))
    case E.QMul{a, b}:
      O.mul(F, mj(~F, bb, a), mj(~F, bb, b))
    case E.QNeg{a}:
      mj(~F, bb, a)

def lp(~F: O.OField, +bb: O.C(F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{i}:
      O.one(F)
    case E.QCst{q}:
      O.zero(F)
    case E.QAdd{a, b}:
      O.add(F, lp(~F, bb, a), lp(~F, bb, b))
    case E.QSub{a, b}:
      O.add(F, lp(~F, bb, a), lp(~F, bb, b))
    case E.QMul{+a, +b}:
      O.add(F, O.mul(F, mj(~F, bb, a), lp(~F, bb, b)), O.mul(F, mj(~F, bb, b), lp(~F, bb, a)))
    case E.QNeg{a}:
      lp(~F, bb, a)

def ms(~F: O.OField, +bb: O.C(F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{i}:
      O.one(F)
    case E.QCst{q}:
      O.zero(F)
    case E.QAdd{a, b}:
      O.add(F, ms(~F, bb, a), ms(~F, bb, b))
    case E.QSub{a, b}:
      O.add(F, ms(~F, bb, a), ms(~F, bb, b))
    case E.QMul{+a, +b}:
      O.add(F, O.mul(F, mj(~F, bb, a), ms(~F, bb, b)), O.mul(F, mj(~F, bb, b), ms(~F, bb, a)))
    case E.QNeg{a}:
      ms(~F, bb, a)

def ls(~F: O.OField, +bb: O.C(F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{i}:
      O.zero(F)
    case E.QCst{q}:
      O.zero(F)
    case E.QAdd{a, b}:
      O.add(F, ls(~F, bb, a), ls(~F, bb, b))
    case E.QSub{a, b}:
      O.add(F, ls(~F, bb, a), ls(~F, bb, b))
    case E.QMul{+a, +b}:
      O.add(F, O.add(F, O.mul(F, mj(~F, bb, a), ls(~F, bb, b)), O.mul(F, ms(~F, bb, b), lp(~F, bb, a))), O.add(F, O.mul(F, mj(~F, bb, b), ls(~F, bb, a)), O.mul(F, ms(~F, bb, a), lp(~F, bb, b))))
    case E.QNeg{a}:
      ls(~F, bb, a)

# a value cv with radius rv has grade (m, l) at rho: 0 <= rv,
# |cv| <= m - rv and rv <= l rho
def gf(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F)) -> Data:
  M.Both(O.le(~F, O.zero(F), rv), M.Both(M.bnd(~F, cv, O.sub(~F, m, rv)), O.le(~F, rv, O.mul(F, l, rho))))

def gf_0(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), g: gf(~F, rho, cv, rv, m, l)) -> O.le(~F, O.zero(F), rv):
  (h0, h) = g
  h0

def gf_cl(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), g: gf(~F, rho, cv, rv, m, l)) -> M.Both(M.bnd(~F, cv, O.sub(~F, m, rv)), O.le(~F, rv, O.mul(F, l, rho))):
  (h0, h) = g
  h

def gf_c.go(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), h: M.Both(M.bnd(~F, cv, O.sub(~F, m, rv)), O.le(~F, rv, O.mul(F, l, rho)))) -> M.bnd(~F, cv, O.sub(~F, m, rv)):
  (hc, hl) = h
  hc

def gf_l.go(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), h: M.Both(M.bnd(~F, cv, O.sub(~F, m, rv)), O.le(~F, rv, O.mul(F, l, rho)))) -> O.le(~F, rv, O.mul(F, l, rho)):
  (hc, hl) = h
  hl

def gf_c(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), g: gf(~F, rho, cv, rv, m, l)) -> M.bnd(~F, cv, O.sub(~F, m, rv)):
  gf_c.go(~F, rho, cv, rv, m, l, gf_cl(~F, rho, cv, rv, m, l, g))

def gf_l(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), g: gf(~F, rho, cv, rv, m, l)) -> O.le(~F, rv, O.mul(F, l, rho)):
  gf_l.go(~F, rho, cv, rv, m, l, gf_cl(~F, rho, cv, rv, m, l, g))

# a point: radius 0
def gf_pt(~F: O.OField, +rho: O.C(F), +cv: O.C(F), +m: O.C(F), +l: O.C(F), hm: M.bnd(~F, cv, m), hl: O.le(~F, O.zero(F), O.mul(F, l, rho))) -> gf(~F, rho, cv, O.zero(F), m, l):
  (FO.le_refl(~F, O.zero(F)), (FM.bnd_eq(~F, cv, m, O.sub(~F, m, O.zero(F)), FR.fring_eq(~F, [m], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==}), hm), hl))

def gf_add(~F: O.OField, +rho: O.C(F), +c1: O.C(F), +r1: O.C(F), +c2: O.C(F), +r2: O.C(F), +m1: O.C(F), +l1: O.C(F), +m2: O.C(F), +l2: O.C(F), +g1: gf(~F, rho, c1, r1, m1, l1), +g2: gf(~F, rho, c2, r2, m2, l2)) -> gf(~F, rho, O.add(F, c1, c2), O.add(F, r1, r2), O.add(F, m1, m2), O.add(F, l1, l2)):
  (FO.nonneg_add(~F, r1, r2, gf_0(~F, rho, c1, r1, m1, l1, g1), gf_0(~F, rho, c2, r2, m2, l2, g2)),
   (FM.bnd_eq(~F, O.add(F, c1, c2), O.add(F, O.sub(~F, m1, r1), O.sub(~F, m2, r2)), O.sub(~F, O.add(F, m1, m2), O.add(F, r1, r2)), FR.fring_eq(~F, [m1, r1, m2, r2], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{2n}, E.ZVar{3n}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, {==}), FM.bnd_add(~F, c1, O.sub(~F, m1, r1), c2, O.sub(~F, m2, r2), gf_c(~F, rho, c1, r1, m1, l1, g1), gf_c(~F, rho, c2, r2, m2, l2, g2))),
    FV.le_rw_r(~F, O.add(F, r1, r2), O.add(F, O.mul(F, l1, rho), O.mul(F, l2, rho)), O.mul(F, O.add(F, l1, l2), rho), FR.fring_eq(~F, [l1, l2, rho], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}), le_add2(~F, r1, O.mul(F, l1, rho), r2, O.mul(F, l2, rho), gf_l(~F, rho, c1, r1, m1, l1, g1), gf_l(~F, rho, c2, r2, m2, l2, g2)))))

def gf_neg(~F: O.OField, +rho: O.C(F), +c: O.C(F), +r: O.C(F), +m: O.C(F), +l: O.C(F), +g: gf(~F, rho, c, r, m, l)) -> gf(~F, rho, O.neg(F, c), r, m, l):
  (gf_0(~F, rho, c, r, m, l, g), (FM.bnd_neg(~F, c, O.sub(~F, m, r), gf_c(~F, rho, c, r, m, l, g)), gf_l(~F, rho, c, r, m, l, g)))


# a product, with 0 <= k1 <= m1 - r1 and 0 <= k2 <= m2 - r2 (the factors'
# sizes as K computes them)
def gf_mul(~F: O.OField, +rho: O.C(F), +c1: O.C(F), +r1: O.C(F), +c2: O.C(F), +r2: O.C(F), +m1: O.C(F), +l1: O.C(F), +m2: O.C(F), +l2: O.C(F), +k1: O.C(F), +k2: O.C(F), +g1: gf(~F, rho, c1, r1, m1, l1), +g2: gf(~F, rho, c2, r2, m2, l2), +hk1: O.le(~F, O.zero(F), k1), +hk1m: O.le(~F, k1, O.sub(~F, m1, r1)), +hk2: O.le(~F, O.zero(F), k2), +hk2m: O.le(~F, k2, O.sub(~F, m2, r2))) -> gf(~F, rho, O.mul(F, c1, c2), O.add(F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, r1, r2)), O.mul(F, m1, m2), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1))):
  +h01 = gf_0(~F, rho, c1, r1, m1, l1, g1)
  +h02 = gf_0(~F, rho, c2, r2, m2, l2, g2)
  +gc1 = gf_c(~F, rho, c1, r1, m1, l1, g1)
  +gc2 = gf_c(~F, rho, c2, r2, m2, l2, g2)
  +a1 = FM.bnd_nonneg(~F, c1, O.sub(~F, m1, r1), gc1)
  +a2 = FM.bnd_nonneg(~F, c2, O.sub(~F, m2, r2), gc2)
  +q1 = FM.sub_nonneg(~F, r1, O.mul(F, l1, rho), gf_l(~F, rho, c1, r1, m1, l1, g1))
  +q2 = FM.sub_nonneg(~F, r2, O.mul(F, l2, rho), gf_l(~F, rho, c2, r2, m2, l2, g2))
  +s1 = FM.sub_nonneg(~F, k1, O.sub(~F, m1, r1), hk1m)
  +s2 = FM.sub_nonneg(~F, k2, O.sub(~F, m2, r2), hk2m)
  +rr = O.add(F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, r1, r2))
  +t5 = O.mul(F, O.sub(~F, O.sub(~F, m1, r1), k1), r2)
  +t6 = O.mul(F, O.sub(~F, O.sub(~F, m2, r2), k2), r1)
  +n5 = FO.mul_nonneg(~F, O.sub(~F, O.sub(~F, m1, r1), k1), r2, s1, h02)
  +n6 = FO.mul_nonneg(~F, O.sub(~F, O.sub(~F, m2, r2), k2), r1, s2, h01)
  +t1 = O.mul(F, O.sub(~F, m1, r1), O.sub(~F, O.mul(F, l2, rho), r2))
  +t2 = O.mul(F, r1, O.sub(~F, O.mul(F, l2, rho), r2))
  +t3 = O.mul(F, O.sub(~F, m2, r2), O.sub(~F, O.mul(F, l1, rho), r1))
  +t4 = O.mul(F, r2, O.sub(~F, O.mul(F, l1, rho), r1))
  +t7 = O.mul(F, r1, r2)
  +xx = O.mul(F, O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)), rho)
  (FO.nonneg_add(~F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, r1, r2), FO.nonneg_add(~F, O.mul(F, k1, r2), O.mul(F, k2, r1), FO.mul_nonneg(~F, k1, r2, hk1, h02), FO.mul_nonneg(~F, k2, r1, hk2, h01)), FO.mul_nonneg(~F, r1, r2, h01, h02)),
   (FM.bnd_mono(~F, O.mul(F, c1, c2), O.mul(F, O.sub(~F, m1, r1), O.sub(~F, m2, r2)), O.sub(~F, O.mul(F, m1, m2), rr), FM.bnd_mul(~F, c1, O.sub(~F, m1, r1), c2, O.sub(~F, m2, r2), gc1, gc2),
      FM.nn_eq(~F, O.sub(~F, O.sub(~F, O.mul(F, m1, m2), rr), O.mul(F, O.sub(~F, m1, r1), O.sub(~F, m2, r2))), O.add(F, t5, t6), FR.fring_eq(~F, [m1, m2, l1, l2, rho, r1, r2, k1, k2], E.ZAdd{E.ZMul{E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{7n}}, E.ZVar{6n}}, E.ZMul{E.ZSub{E.ZSub{E.ZVar{1n}, E.ZVar{6n}}, E.ZVar{8n}}, E.ZVar{5n}}}, E.ZSub{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{7n}, E.ZVar{6n}}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{5n}}, E.ZSub{E.ZVar{1n}, E.ZVar{6n}}}}, {==}), FO.nonneg_add(~F, t5, t6, n5, n6))),
    FV.le_of_sub(~F, rr, xx, FM.nn_eq(~F, O.sub(~F, xx, rr), O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, t1, t2), t3), t4), t5), t6), t7),
      FR.fring_eq(~F, [m1, m2, l1, l2, rho, r1, r2, k1, k2], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{6n}}}, E.ZMul{E.ZVar{5n}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{6n}}}}, E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZVar{5n}}}}, E.ZMul{E.ZVar{6n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZVar{5n}}}}, E.ZMul{E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{7n}}, E.ZVar{6n}}}, E.ZMul{E.ZSub{E.ZSub{E.ZVar{1n}, E.ZVar{6n}}, E.ZVar{8n}}, E.ZVar{5n}}}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{4n}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{7n}, E.ZVar{6n}}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}}, {==}),
      FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, t1, t2), t3), t4), t5), t6), t7, FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.add(F, t1, t2), t3), t4), t5), t6, FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, t1, t2), t3), t4), t5, FO.nonneg_add(~F, O.add(F, O.add(F, t1, t2), t3), t4, FO.nonneg_add(~F, O.add(F, t1, t2), t3, FO.nonneg_add(~F, t1, t2, FO.mul_nonneg(~F, O.sub(~F, m1, r1), O.sub(~F, O.mul(F, l2, rho), r2), a1, q2), FO.mul_nonneg(~F, r1, O.sub(~F, O.mul(F, l2, rho), r2), h01, q2)), FO.mul_nonneg(~F, O.sub(~F, m2, r2), O.sub(~F, O.mul(F, l1, rho), r1), a2, q1)), FO.mul_nonneg(~F, r2, O.sub(~F, O.mul(F, l1, rho), r1), h02, q1)), n5), n6), FO.mul_nonneg(~F, r1, r2, h01, h02))))))

# Grades of balls
# ---------------

def grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +b: KB.KB<K>, +m: O.C(F), +l: O.C(F)) -> Data:
  gf(~F, rho, N.emap(K, F, H, KB.KB.c(K, b)), N.emap(K, F, H, KB.KB.r(K, b)), m, l)

def grade_of(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +c: N.NC(K), +r: N.NC(K), +cv: O.C(F), +rv: O.C(F), +m: O.C(F), +l: O.C(F), ec: {N.emap(K, F, H, c) == cv : O.C(F)}, er: {N.emap(K, F, H, r) == rv : O.C(F)}, g: gf(~F, rho, cv, rv, m, l)) -> grade(~K, ~F, ~H, rho, KB.KB{c, r}, m, l):
  %Equal.sym(O.C(F), N.emap(K, F, H, c), cv, ec) : gf(~F, rho, _, N.emap(K, F, H, r), m, l)
  %Equal.sym(O.C(F), N.emap(K, F, H, r), rv, er) : gf(~F, rho, cv, _, m, l)
  g

def g_add(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), x: KB.KB<K>, y: KB.KB<K>, +m1: O.C(F), +l1: O.C(F), +m2: O.C(F), +l2: O.C(F), gx: grade(~K, ~F, ~H, rho, x, m1, l1), gy: grade(~K, ~F, ~H, rho, y, m2, l2)) -> grade(~K, ~F, ~H, rho, KB.badd(~K, x, y), O.add(F, m1, m2), O.add(F, l1, l2)):
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      grade_of(~K, ~F, ~H, rho, N.nadd(K, c1, c2), N.nadd(K, r1, r2), O.add(F, N.emap(K, F, H, c1), N.emap(K, F, H, c2)), O.add(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2)), O.add(F, m1, m2), O.add(F, l1, l2), Equal.sym(O.C(F), O.add(F, N.emap(K, F, H, c1), N.emap(K, F, H, c2)), N.emap(K, F, H, N.nadd(K, c1, c2)), KA.ea(~K, ~F, ~H, c1, c2)), Equal.sym(O.C(F), O.add(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2)), N.emap(K, F, H, N.nadd(K, r1, r2)), KA.ea(~K, ~F, ~H, r1, r2)), gf_add(~F, rho, N.emap(K, F, H, c1), N.emap(K, F, H, r1), N.emap(K, F, H, c2), N.emap(K, F, H, r2), m1, l1, m2, l2, gx, gy))

def g_neg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), x: KB.KB<K>, +m: O.C(F), +l: O.C(F), gx: grade(~K, ~F, ~H, rho, x, m, l)) -> grade(~K, ~F, ~H, rho, KB.bneg(~K, x), m, l):
  match x:
    case KB.KB{+c, +r}:
      grade_of(~K, ~F, ~H, rho, N.nneg(K, c), r, O.neg(F, N.emap(K, F, H, c)), N.emap(K, F, H, r), m, l, Equal.sym(O.C(F), O.neg(F, N.emap(K, F, H, c)), N.emap(K, F, H, N.nneg(K, c)), KA.en(~K, ~F, ~H, c)), {==}, gf_neg(~F, rho, N.emap(K, F, H, c), N.emap(K, F, H, r), m, l, gx))

def bmul_r(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c1: N.NC(K), +r1: N.NC(K), +c2: N.NC(K), +r2: N.NC(K)) -> {N.emap(K, F, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2))) == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}:
  %KA.ea(~K, ~F, ~H, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2)) : {_ == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}
  %KA.ea(~K, ~F, ~H, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)) : {O.add(F, _, N.emap(K, F, H, N.nmul(K, r1, r2))) == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}
  %KA.em(~K, ~F, ~H, KA.kabs(~K, c1), r2) : {O.add(F, O.add(F, _, N.emap(K, F, H, N.nmul(K, KA.kabs(~K, c2), r1))), N.emap(K, F, H, N.nmul(K, r1, r2))) == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}
  %KA.em(~K, ~F, ~H, KA.kabs(~K, c2), r1) : {O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), _), N.emap(K, F, H, N.nmul(K, r1, r2))) == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}
  %KA.em(~K, ~F, ~H, r1, r2) : {O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), _) == O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))) : O.C(F)}
  {==}

def g_mul(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), x: KB.KB<K>, y: KB.KB<K>, +m1: O.C(F), +l1: O.C(F), +m2: O.C(F), +l2: O.C(F), +gx: grade(~K, ~F, ~H, rho, x, m1, l1), +gy: grade(~K, ~F, ~H, rho, y, m2, l2)) -> grade(~K, ~F, ~H, rho, KB.bmul(~K, x, y), O.mul(F, m1, m2), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1))):
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      grade_of(~K, ~F, ~H, rho, N.nmul(K, c1, c2), N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2)), O.mul(F, N.emap(K, F, H, c1), N.emap(K, F, H, c2)), O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))), O.mul(F, m1, m2), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)), Equal.sym(O.C(F), O.mul(F, N.emap(K, F, H, c1), N.emap(K, F, H, c2)), N.emap(K, F, H, N.nmul(K, c1, c2)), KA.em(~K, ~F, ~H, c1, c2)), bmul_r(~K, ~F, ~H, c1, r1, c2, r2),
        gf_mul(~F, rho, N.emap(K, F, H, c1), N.emap(K, F, H, r1), N.emap(K, F, H, c2), N.emap(K, F, H, r2), m1, l1, m2, l2, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, KA.kabs(~K, c2)), gx, gy, KA.kabs_nonneg(~K, ~F, ~H, c1), kabs_le(~K, ~F, ~H, c1, O.sub(~F, m1, N.emap(K, F, H, r1)), gf_c(~F, rho, N.emap(K, F, H, c1), N.emap(K, F, H, r1), m1, l1, gx)), KA.kabs_nonneg(~K, ~F, ~H, c2), kabs_le(~K, ~F, ~H, c2, O.sub(~F, m2, N.emap(K, F, H, r2)), gf_c(~F, rho, N.emap(K, F, H, c2), N.emap(K, F, H, r2), m2, l2, gy))))

def bzero_grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +m: O.C(F), +l: O.C(F), +hm: O.le(~F, O.zero(F), m), hl: O.le(~F, O.zero(F), O.mul(F, l, rho))) -> grade(~K, ~F, ~H, rho, KB.bzero(~K), m, l):
  grade_of(~K, ~F, ~H, rho, N.nzero(K), N.nzero(K), O.zero(F), O.zero(F), m, l, N.e_zero(K, F, H), N.e_zero(K, F, H), gf_pt(~F, rho, O.zero(F), m, l, FM.bnd_zero(~F, m, hm), hl))

def kind_grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), b: Bool) -> grade(~K, ~F, ~H, rho, KB.kind(~K, b), O.one(F), O.zero(F)):
  match b:
    case True{}:
      grade_of(~K, ~F, ~H, rho, N.none(K), N.nzero(K), O.one(F), O.zero(F), O.one(F), O.zero(F), N.e_one(K, F, H), N.e_zero(K, F, H), gf_pt(~F, rho, O.one(F), O.one(F), O.zero(F), FV.bnd_self(~F, O.one(F), Inl{O.zero_lt_one(F)}), zl(~F, rho)))
    case False{}:
      bzero_grade(~K, ~F, ~H, rho, O.one(F), O.zero(F), Inl{O.zero_lt_one(F)}, zl(~F, rho))

# every ball of the box has grade (bb, 1)
def gbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), box: List<&2, KB.KB<K>>) -> Data:
  match box:
    case Nil{}:
      Unit
    case Con{b, bs}:
      M.Both(grade(~K, ~F, ~H, rho, b, bb, O.one(F)), gbox(~K, ~F, ~H, rho, bb, bs))

def blook_grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), box: List<&2, KB.KB<K>>, i: Nat, hg: gbox(~K, ~F, ~H, rho, bb, box)) -> grade(~K, ~F, ~H, rho, KB.blook(~K, box, i), bb, O.one(F)):
  match box i:
    case Nil{} 0n:
      bzero_grade(~K, ~F, ~H, rho, bb, O.one(F), hb, ol(~F, rho, hr))
    case Nil{} 1n+j:
      bzero_grade(~K, ~F, ~H, rho, bb, O.one(F), hb, ol(~F, rho, hr))
    case Con{b, bs} 0n:
      (g, gs) = hg
      g
    case Con{b, bs} 1n+j:
      (g, gs) = hg
      blook_grade(~K, ~F, ~H, rho, bb, hr, hb, bs, j, gs)

# ball tightness: e's ball has grade (mj, lp)
def kball_grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> grade(~K, ~F, ~H, rho, KB.kball(~K, box, e), mj(~F, bb, e), lp(~F, bb, e)):
  match e:
    case E.QVar{i}:
      blook_grade(~K, ~F, ~H, rho, bb, hr, hb, box, i, hg)
    case E.QCst{+q}:
      grade_of(~K, ~F, ~H, rho, KB.kcst(~K, q), N.nzero(K), O.ofq(~F, q), O.zero(F), FV.fabs(~F, O.ofq(~F, q)), O.zero(F), KB.kcst_ok(~K, ~F, ~H, q, hh), N.e_zero(K, F, H), gf_pt(~F, rho, O.ofq(~F, q), FV.fabs(~F, O.ofq(~F, q)), O.zero(F), FV.fabs_bnd(~F, O.ofq(~F, q)), zl(~F, rho)))
    case E.QAdd{+a, +b}:
      g_add(~K, ~F, ~H, rho, KB.kball(~K, box, a), KB.kball(~K, box, b), mj(~F, bb, a), lp(~F, bb, a), mj(~F, bb, b), lp(~F, bb, b), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      g_add(~K, ~F, ~H, rho, KB.kball(~K, box, a), KB.bneg(~K, KB.kball(~K, box, b)), mj(~F, bb, a), lp(~F, bb, a), mj(~F, bb, b), lp(~F, bb, b), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), g_neg(~K, ~F, ~H, rho, KB.kball(~K, box, b), mj(~F, bb, b), lp(~F, bb, b), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      g_mul(~K, ~F, ~H, rho, KB.kball(~K, box, a), KB.kball(~K, box, b), mj(~F, bb, a), lp(~F, bb, a), mj(~F, bb, b), lp(~F, bb, b), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QNeg{+a}:
      g_neg(~K, ~F, ~H, rho, KB.kball(~K, box, a), mj(~F, bb, a), lp(~F, bb, a), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, a, hh))

# ball tightness: e's slope ball in variable i has grade (ms, ls)
def ksl_grade(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), +i: Nat, e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> grade(~K, ~F, ~H, rho, KB.ksl(~K, i, box, e), ms(~F, bb, e), ls(~F, bb, e)):
  match e:
    case E.QVar{j}:
      kind_grade(~K, ~F, ~H, rho, KA.nateq(i, j))
    case E.QCst{q}:
      bzero_grade(~K, ~F, ~H, rho, O.zero(F), O.zero(F), FO.le_refl(~F, O.zero(F)), zl(~F, rho))
    case E.QAdd{+a, +b}:
      g_add(~K, ~F, ~H, rho, KB.ksl(~K, i, box, a), KB.ksl(~K, i, box, b), ms(~F, bb, a), ls(~F, bb, a), ms(~F, bb, b), ls(~F, bb, b), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      g_add(~K, ~F, ~H, rho, KB.ksl(~K, i, box, a), KB.bneg(~K, KB.ksl(~K, i, box, b)), ms(~F, bb, a), ls(~F, bb, a), ms(~F, bb, b), ls(~F, bb, b), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), g_neg(~K, ~F, ~H, rho, KB.ksl(~K, i, box, b), ms(~F, bb, b), ls(~F, bb, b), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      +ha = KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)
      +hb2 = KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)
      g_add(~K, ~F, ~H, rho, KB.bmul(~K, KB.kball(~K, box, a), KB.ksl(~K, i, box, b)), KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)), O.mul(F, mj(~F, bb, a), ms(~F, bb, b)), O.add(F, O.mul(F, mj(~F, bb, a), ls(~F, bb, b)), O.mul(F, ms(~F, bb, b), lp(~F, bb, a))), O.mul(F, mj(~F, bb, b), ms(~F, bb, a)), O.add(F, O.mul(F, mj(~F, bb, b), ls(~F, bb, a)), O.mul(F, ms(~F, bb, a), lp(~F, bb, b))),
        g_mul(~K, ~F, ~H, rho, KB.kball(~K, box, a), KB.ksl(~K, i, box, b), mj(~F, bb, a), lp(~F, bb, a), ms(~F, bb, b), ls(~F, bb, b), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, a, ha), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, b, hb2)),
        g_mul(~K, ~F, ~H, rho, KB.kball(~K, box, b), KB.ksl(~K, i, box, a), mj(~F, bb, b), lp(~F, bb, b), ms(~F, bb, a), ls(~F, bb, a), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, b, hb2), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, a, ha)))
    case E.QNeg{+a}:
      g_neg(~K, ~F, ~H, rho, KB.ksl(~K, i, box, a), ms(~F, bb, a), ls(~F, bb, a), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, a, hh))

# Lipschitz bounds
# ----------------

def bin_cr(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), b: KB.KB<K>, h: KB.bin(~K, ~F, ~H, x, b)) -> M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, KB.KB.c(K, b))), N.emap(K, F, H, KB.KB.r(K, b))):
  match b:
    case KB.KB{c, r}:
      h

# |x - c| <= r and |c| <= m - r give |x| <= m
def bnd_join(~F: O.OField, +x: O.C(F), +c: O.C(F), +r: O.C(F), +m: O.C(F), h1: M.bnd(~F, O.sub(~F, x, c), r), h2: M.bnd(~F, c, O.sub(~F, m, r))) -> M.bnd(~F, x, m):
  KB.bnd_val(~F, O.add(F, O.sub(~F, x, c), c), x, m, FR.fring_eq(~F, [x, c], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZVar{0n}, {==}), FM.bnd_eq(~F, O.add(F, O.sub(~F, x, c), c), O.add(F, r, O.sub(~F, m, r)), m, FR.fring_eq(~F, [r, m], E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZVar{1n}, {==}), FM.bnd_add(~F, O.sub(~F, x, c), r, c, O.sub(~F, m, r), h1, h2)))

# in a ball of grade (m, l): within l rho of its center
def bin_lip(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +x: O.C(F), +b: KB.KB<K>, +m: O.C(F), +l: O.C(F), h: KB.bin(~K, ~F, ~H, x, b), g: grade(~K, ~F, ~H, rho, b, m, l)) -> M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, KB.KB.c(K, b))), O.mul(F, l, rho)):
  FM.bnd_mono(~F, O.sub(~F, x, N.emap(K, F, H, KB.KB.c(K, b))), N.emap(K, F, H, KB.KB.r(K, b)), O.mul(F, l, rho), bin_cr(~K, ~F, ~H, x, b, h), FM.sub_nonneg(~F, N.emap(K, F, H, KB.KB.r(K, b)), O.mul(F, l, rho), gf_l(~F, rho, N.emap(K, F, H, KB.KB.c(K, b)), N.emap(K, F, H, KB.KB.r(K, b)), m, l, g)))

# in a ball of grade (m, l): at most m
def bin_maj(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +x: O.C(F), +b: KB.KB<K>, +m: O.C(F), +l: O.C(F), h: KB.bin(~K, ~F, ~H, x, b), g: grade(~K, ~F, ~H, rho, b, m, l)) -> M.bnd(~F, x, m):
  bnd_join(~F, x, N.emap(K, F, H, KB.KB.c(K, b)), N.emap(K, F, H, KB.KB.r(K, b)), m, bin_cr(~K, ~F, ~H, x, b, h), gf_c(~F, rho, N.emap(K, F, H, KB.KB.c(K, b)), N.emap(K, F, H, KB.KB.r(K, b)), m, l, g))

# at a point of a box of grade (bb, rho), e is within lp rho of its value
# at the centers
def eval_lip(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), +x: M.Vec(~F), +hx: KB.inbox(~K, ~F, ~H, x, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.eval(~F, x, e), O.eval(~F, cen(~K, ~F, ~H, box), e)), O.mul(F, lp(~F, bb, e), rho)):
  %kball_c(~K, ~F, ~H, box, e, hh) : M.bnd(~F, O.sub(~F, O.eval(~F, x, e), _), O.mul(F, lp(~F, bb, e), rho))
  bin_lip(~K, ~F, ~H, rho, O.eval(~F, x, e), KB.kball(~K, box, e), mj(~F, bb, e), lp(~F, bb, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, e, hh))

# and is at most mj
def eval_maj(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), +x: M.Vec(~F), +hx: KB.inbox(~K, ~F, ~H, x, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, O.eval(~F, x, e), mj(~F, bb, e)):
  bin_maj(~K, ~F, ~H, rho, O.eval(~F, x, e), KB.kball(~K, box, e), mj(~F, bb, e), lp(~F, bb, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), kball_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, e, hh))

# between two points of the box, e's slope in variable i is within ls rho
# of its slope at the centers (the derivative there, sl_deriv)
def sl_lip(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, SL.sl(~F, i, x1, x2, e), SL.sl(~F, i, cen(~K, ~F, ~H, box), cen(~K, ~F, ~H, box), e)), O.mul(F, ls(~F, bb, e), rho)):
  %ksl_c(~K, ~F, ~H, i, box, e, hh) : M.bnd(~F, O.sub(~F, SL.sl(~F, i, x1, x2, e), _), O.mul(F, ls(~F, bb, e), rho))
  bin_lip(~K, ~F, ~H, rho, SL.sl(~F, i, x1, x2, e), KB.ksl(~K, i, box, e), ms(~F, bb, e), ls(~F, bb, e), KB.sl_ok(~K, ~F, ~H, i, x1, x2, box, e, hh, h1, h2), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, e, hh))

# and is at most ms
def sl_maj(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: gbox(~K, ~F, ~H, rho, bb, box), +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~K, ~F, ~H, x1, box), +h2: KB.inbox(~K, ~F, ~H, x2, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> M.bnd(~F, SL.sl(~F, i, x1, x2, e), ms(~F, bb, e)):
  bin_maj(~K, ~F, ~H, rho, SL.sl(~F, i, x1, x2, e), KB.ksl(~K, i, box, e), ms(~F, bb, e), ls(~F, bb, e), KB.sl_ok(~K, ~F, ~H, i, x1, x2, box, e, hh, h1, h2), ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, i, e, hh))
