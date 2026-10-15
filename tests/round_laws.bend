# bend-cad: the solver's rounding under solve_complete (DESIGN §10.4, C3b),
# restated here so the gate checks lib/roundpf.bend until the completeness
# proof imports it. In every ordered field F (dyadics read through ofd,
# rationals through ofq):
# - Euclid's division as lib/qreduce.bend computes it: n = q d + r with
#   0 <= r < d; so zfloor(n, d) is the floor of n / d.
# - dround(x, p) (to a multiple of 2^-p, the Newton iterates) is within
#   2^-(p+1) of x.
# - dsig(x, b) (to b significant bits, the elimination's arithmetic and Y)
#   is within |x| 2^-b of x; so is qsig(q, b) of a rational q (dsdiv).
# - dsigup(x, b) (rounded up, the radius search) is at least x and at most
#   x + |x| 2^(1-b).

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/qreduce.bend as QRD
import ../lib/numer.bend as NU
import ../lib/fvec.bend as FV
import ../lib/roundpf.bend as RP

def euclid(~F: O.OField, n: S.Pos, +d: S.Pos) -> RP.dvok(~F, n, d, QRD.div(n, d)):
  RP.div_ok(~F, n, d)

def floor_is_floor(~F: O.OField, n: S.Z, +d: S.Pos) -> RP.zfl(~F, n, d, NU.zfloor(n, d)):
  RP.zfloor_ok(~F, n, d)

def dround_close(~F: O.OField, x: S.D, +p: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dround(x, p)), M.ofd(~F, x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p})):
  RP.dround_err(~F, x, p)

def dsig_close(~F: O.OField, x: S.D, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig(x, b)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  RP.dsig_err(~F, x, b)

def qsig_close(~F: O.OField, x: S.Q, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.qsig(x, b)), O.ofq(~F, x)), O.mul(F, FV.fabs(~F, O.ofq(~F, x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  RP.qsig_err(~F, x, b)

def dsigup_close(~F: O.OField, x: S.D, +b: Nat) -> M.Both(O.le(~F, M.ofd(~F, x), M.ofd(~F, NU.dsigup(x, b))), O.le(~F, O.sub(~F, M.ofd(~F, NU.dsigup(x, b)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, b})))):
  RP.dsigup_ok(~F, x, b)
