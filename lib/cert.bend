# bend-cad: the block certificate checker (DESIGN §8.3). Untrusted: only the
# cert_* laws (ROADMAP.bend while sk-05 is open) say what a passing check
# means.
#
# Draft for review: the signature is final, the body is a stub that rejects
# everything. Against this stub every cert_* law is trivially provable (the
# hypothesis check == True is absurd), which proves nothing; the laws stay
# in ROADMAP.bend until the real checker lands, and moving them needs a
# gated positive test (check == True on a real block).

import Base
import ../spec/knum.bend as N
import ../spec/cert.bend as C

def check(~K: N.Num, b: C.Block, c: C.Cert<K>) -> Bool:
  False{}
