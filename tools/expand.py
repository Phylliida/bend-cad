# Expands a draft into Bend: conjunction predicates (conj.py) and
# certificate macros (zexpr.py) first, then the
# shorthand @A( @M( @N( @S( (field add, mul, neg, sub), @0 @1 @T (zero, one,
# carrier), @LK( @EM( @EP( @OZ( @ON( @ZE( (lookups and evaluations).
# Usage: python3 tools/expand.py tools/drafts/X.draft lib/X.bend
import sys
src = open(sys.argv[1]).read()
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zexpr
import conj
src = conj.expand(src)
src = zexpr.expand(src)
for k, v in [("@LK(", "O.lookup(~F, env, "), ("@EM(", "femono(~F, env, "), ("@EP(", "fepoly(~F, env, "),
             ("@OZ(", "O.ofz(~F, "), ("@ON(", "ofn(~F, "), ("@ZE(", "zeval(~F, env, "),
             ("@A(", "O.add(F, "), ("@M(", "O.mul(F, "), ("@N(", "O.neg(F, "),
             ("@S(", "O.sub(~F, "), ("@0", "O.zero(F)"), ("@1", "O.one(F)"), ("@T", "O.C(F)")]:
    src = src.replace(k, v)
import re
# what is left of "@" must be Bend's own (a dependent binder "@x: T")
left = re.sub(r'@[a-z_][A-Za-z_0-9]*:', '', src)
assert "@" not in left, [l for l in left.splitlines() if "@" in l][:3]
open(sys.argv[2], "w").write(src)
