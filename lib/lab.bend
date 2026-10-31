# bend-cad: labels (PLAN-sk13b B3). A label is a Gaussian rational c + i s
# (spec/dir.bend's Lab); gmul multiplies a form by it. Here: products of
# labels, and the label tests, by the pair test (lib/pair.bend), since
# w z = a z + b (i z) for w = a + i b:
# - a nonzero w with w z in a hull, on the encodings of z and i z;
# - the frame test: a nonzero w with Im(w z) in K (w z parallel to the
#   frame), on Im z and Im(i z) = Re z.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/labpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./pair.bend as PT
import ./kspace.bend as KS
import ./hspace.bend as HS

def lmul.go(+c1: S.Q, +s1: S.Q, h: DR.Lab) -> DR.Lab:
  match h:
    case DR.Lab{+c2, +s2}:
      DR.Lab{S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2))}

# g h
def lmul(g: DR.Lab, +h: DR.Lab) -> DR.Lab:
  match g:
    case DR.Lab{+c1, +s1}:
      lmul.go(c1, s1, h)

# Trimming
# --------
# The closure stores labels (members', ties', the label tests'), and a
# product of labels multiplies all four denominators, so a stored label is
# trimmed: a zero part becomes 0/1, and the factors of 2 its numerator and
# denominator share are taken out (lib/labpf.bend: qtrim_ok, the same
# rational).

def qtrim.mk(sg: Bool, +p: S.Pos, +d: S.Pos) -> S.Q:
  match sg:
    case True{}:
      S.Q{S.Zpos{p}, d}
    case False{}:
      S.Q{S.Zneg{p}, d}

# +-p/d, common twos out
def qtrim.p(p: S.Pos, d: S.Pos, sg: Bool) -> S.Q:
  match p d:
    case S.XO{a} S.XO{b}:
      qtrim.p(a, b, sg)
    case S.XO{a} S.XH{}:
      qtrim.mk(sg, S.XO{a}, S.XH{})
    case S.XO{a} S.XI{b}:
      qtrim.mk(sg, S.XO{a}, S.XI{b})
    case S.XH{} d:
      qtrim.mk(sg, S.XH{}, d)
    case S.XI{a} d:
      qtrim.mk(sg, S.XI{a}, d)

def qtrim.z(n: S.Z, +d: S.Pos) -> S.Q:
  match n:
    case S.Z0{}:
      S.Q{S.Z0{}, S.XH{}}
    case S.Zpos{p}:
      qtrim.p(p, d, True{})
    case S.Zneg{p}:
      qtrim.p(p, d, False{})

def qtrim(q: S.Q) -> S.Q:
  match q:
    case S.Q{n, d}:
      qtrim.z(n, d)

def ltrim(w: DR.Lab) -> DR.Lab:
  match w:
    case DR.Lab{c, s}:
      DR.Lab{qtrim(c), qtrim(s)}

def lab_of(p: PT.Pr) -> DR.Lab:
  match p:
    case PT.Pr{a, b}:
      DR.Lab{qtrim(a), qtrim(b)}

def lab_map(m: Maybe<&2, PT.Pr>) -> Maybe<&2, DR.Lab>:
  match m:
    case Some{p}:
      Some{lab_of(p)}
    case None{}:
      None{}

# the pair test for w z in the hull h
def hs.ptest(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +z: SK.VE) -> Maybe<&2, PT.Pr>:
  PT.ptest(HS.hs.rows(h), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.enc(z, t), HS.enc(DR.imul(z), t))

# a nonzero label w with w z in the hull h, or none
def hs.lab(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +z: SK.VE) -> Maybe<&2, DR.Lab>:
  lab_map(hs.ptest(es, fs, t, h, z))

# the pair test for Im(w z) in K
def ks.ptest(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +z: SK.VE) -> Maybe<&2, PT.Pr>:
  PT.ptest(KS.ks.rows(k), KS.kexprs(es, fs, KS.ks.ds(k)), SK.VE.y(z), SK.VE.x(z))

# a nonzero label w with Im(w z) in K, or none
def ks.lab(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +z: SK.VE) -> Maybe<&2, DR.Lab>:
  lab_map(ks.ptest(es, fs, k, z))
