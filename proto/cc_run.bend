import Base
import ../lib/certdef.bend as C
import ../lib/kinst.bend as KI
import ../lib/cert.bend as CK
import ../tests/cc_data.bend as D

def main() -> Bool:
  CK.check(~KI.dnum(), D.cc_block(), D.cc_cert())
