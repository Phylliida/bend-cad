# Expands a draft into Bend: conjunction predicates (conj.py) and
# certificate macros (zexpr.py) first, then the
# shorthand @A( @M( @N( @S( (field add, mul, neg, sub), @0 @1 @T (zero, one,
# carrier), @LK( @EM( @EP( @OZ( @ON( @ZE( (lookups and evaluations), @H( (a
# computing number's image in F).
# @MACRO NAME text lines define textual macros used as $NAME.
# Usage: python3 tools/expand.py tools/drafts/X.draft lib/X.bend
import sys
src = open(sys.argv[1]).read()
import re as _re
# @MACRO NAME text: every $NAME below is replaced by text (macros may use
# macros; the longest names are replaced first)
_macros = {}
_lines = []
for _l in src.split("\n"):
    if _l.startswith("@MACRO "):
        _name, _body = _l[len("@MACRO "):].split(" ", 1)
        _macros[_name] = _body
    else:
        _lines.append(_l)
src = "\n".join(_lines)
for _ in range(20):
    _new = src
    for _name in sorted(_macros, key=len, reverse=True):
        _new = _re.sub(r'\$' + _re.escape(_name) + r'(?![A-Za-z0-9_])', lambda _m, _b=_macros[_name]: _b, _new)
    if _new == src:
        break
    src = _new
assert not _re.search(r'\$[A-Za-z_]', src), "unknown macro"
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zexpr
import conj
src = conj.expand(src)
src = zexpr.expand(src)
for k, v in [("@LK(", "O.lookup(~F, env, "), ("@EM(", "femono(~F, env, "), ("@EP(", "fepoly(~F, env, "),
             ("@OZ(", "O.ofz(~F, "), ("@ON(", "ofn(~F, "), ("@ZE(", "zeval(~F, env, "), ("@H(", "N.emap(K, F, H, "),
             ("@A(", "O.add(F, "), ("@M(", "O.mul(F, "), ("@N(", "O.neg(F, "),
             ("@S(", "O.sub(~F, "), ("@0", "O.zero(F)"), ("@1", "O.one(F)"), ("@T", "O.C(F)")]:
    src = src.replace(k, v)
import re
# what is left of "@" must be Bend's own (a dependent binder "@x: T")
left = re.sub(r'@[a-z_][A-Za-z_0-9]*:', '', src)
assert "@" not in left, [l for l in left.splitlines() if "@" in l][:3]
open(sys.argv[2], "w").write(src)
