# bend-cad: labels (PLAN-sk13b B3). A label is a Gaussian rational c + i s
# (spec/dir.bend's Lab); gmul multiplies a form by it. Here: products of
# labels, and the label test: a nonzero w with w z in a hull, by the pair
# test (lib/pair.bend) on the encodings of z and i z, since w z = a z +
# b (i z) for w = a + i b.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/labpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./pair.bend as PT
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

def lab_of(p: PT.Pr) -> DR.Lab:
  match p:
    case PT.Pr{a, b}:
      DR.Lab{a, b}

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
