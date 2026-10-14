# bend-cad: the block certificate checker (DESIGN §8.3). Untrusted: only the
# cert_* laws (ROADMAP.bend while sk-05 is open) say what a passing check
# means.
#
# Draft for review: the signature is final, the body is a stub that rejects
# everything (so nothing may be proven against it; the laws stay in
# ROADMAP.bend until the real checker lands).

import Base
import ../spec/knum.bend as N
import ../spec/cert.bend as C

def check(~K: N.Num, b: C.Block, c: C.Cert<K>) -> Bool:
  False{}
