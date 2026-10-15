# The @CONJ macro: a predicate that is a conjunction, with an accessor lemma
# per conjunct and a constructor.
#
#   @CONJ name
#   params: +a: T, +b: U
#   - tag1: expr1
#   - tag2: expr2
#   @END
#
# becomes
#
#   def name(+a: T, +b: U) -> Bool:
#     SV.band(expr1, expr2)
#   def name_tag1(+a: T, +b: U, h: {name(a, b) == True{} : Bool}) -> {expr1 == True{} : Bool}: ...
#   def name_tag2(...) ...
#   def name_mk(+a: T, +b: U, h_tag1: {expr1 == True{} : Bool}, h_tag2: ...) -> {name(a, b) == True{} : Bool}: ...
#
# using SV.band and the lemmas L.band_l, L.band_r, L.band_i.
import re


def split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(<{[":
            depth += 1
        elif ch in ")>}]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def band(cs):
    return cs[0] if len(cs) == 1 else "SV.band(%s, %s)" % (cs[0], band(cs[1:]))


def gen(name, params, conj):
    args = ", ".join(p.split(":")[0].strip().lstrip("+-~") for p in split_top(params))
    tags = [t for t, _ in conj]
    cs = [c for _, c in conj]
    n = len(cs)
    whole = "{%s(%s) == True{} : Bool}" % (name, args)
    out = ["def %s(%s) -> Bool:\n  %s\n" % (name, params, band(cs))]
    for i in range(n):
        # h_i : {band(cs[i:]) == True}
        h = "h"
        for k in range(i):
            h = "L.band_r(%s, %s, %s)" % (cs[k], band(cs[k + 1:]), h)
        body = h if i == n - 1 else "L.band_l(%s, %s, %s)" % (cs[i], band(cs[i + 1:]), h)
        out.append("def %s_%s(%s, h: %s) -> {%s == True{} : Bool}:\n  %s\n" % (name, tags[i], params, whole, cs[i], body))
    hs = ", ".join("h_%s: {%s == True{} : Bool}" % (t, c) for t, c in conj)
    body = "h_%s" % tags[-1]
    for i in range(n - 2, -1, -1):
        body = "L.band_i(%s, %s, h_%s, %s)" % (cs[i], band(cs[i + 1:]), tags[i], body)
    out.append("def %s_mk(%s, %s) -> %s:\n  %s\n" % (name, params, hs, whole, body))
    return "\n".join(out)


def expand(src):
    pat = re.compile(r"^@CONJ (\S+)\nparams: (.*)\n((?:- .*\n)+)@END\n", re.M)

    def rep(m):
        conj = []
        for line in m.group(3).splitlines():
            tag, expr = line[2:].split(":", 1)
            conj.append((tag.strip(), expr.strip()))
        return gen(m.group(1), m.group(2).strip(), conj)
    return pat.sub(rep, src)
