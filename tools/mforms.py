# Generates lib/mforms.bend (per-kind by-value holds/means/wf types) and the
# dispatcher block (tools/drafts/dispatch.draft, already part of
# meaning.draft), from spec/sketch.bend's Constraint arms. Rerun after
# changing a constraint kind; the checker rejects a stale lib/mforms.bend.
import re, sys
import os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, 'spec/sketch.bend')
src = open(SPEC).read()

def arms(fname):
    i = src.index('def ' + fname + '(')
    j = src.find('\ndef ', i + 1)
    body = src[i:j if j > 0 else len(src)]
    res = {}; cur = None; lines = []
    for line in body.splitlines()[2:]:
        m = re.match(r'    case (\w+)(\{([^}]*)\})?:\s*$', line)
        if m:
            if cur: res[cur[0]] = (cur[1], "\n".join(lines).strip())
            cur = (m.group(1), [f.strip() for f in m.group(3).split(',')] if m.group(3) else []); lines = []
        elif line.startswith('      '):
            lines.append(line.strip())
        elif line.strip() == '' or line.startswith('#'):
            pass
        else:
            break
    if cur: res[cur[0]] = (cur[1], "\n".join(lines).strip())
    return res

# constructor fields and types
ti = src.index('type Constraint is Data:')
kinds = []
for line in src[ti:].splitlines()[1:]:
    if not line.startswith('  '): break
    m = re.match(r'  (\w+)\{(.*)\}\s*$', line)
    if m:
        fields = [tuple(x.strip().split(': ')) for x in m.group(2).split(', ')]
        kinds.append((m.group(1), fields))

E, Si, W, M = arms('Constraint.eqs'), arms('Constraint.sides'), arms('Constraint.wf'), arms('Constraint.means')
LOCAL = ['VE.x','VE.y','VE.add','VE.sub','VE.dot','VE.cross','VE.norm2','VE.rot','Pt.ve','Pt.x','Pt.y',
         'Seg.dir','Seg.p','Seg.q','Seg.rev_if','Circ.c','Circ.r','sym.eqs','Zeros','Sides','dirv']
def qualify(t):
    t = re.sub(r'\bpt\(es, (\w+)\)', r'\1', t)
    t = re.sub(r'\bcirc\(es, (\w+)\)', r'\1', t)
    t = re.sub(r'\bdseg\(es, (\w+), (\w+)\)', r'Seg.rev_if(\1, \2)', t)
    t = re.sub(r'\bseg\(es, (\w+)\)', r'\1', t)
    for n in LOCAL:
        t = re.sub(r'(?<![\w.])' + re.escape(n) + r'\(', 'K.' + n + '(', t)
    t = re.sub(r'(?<![\w.])var\(', 'K.var(', t)
    t = re.sub(r'(?<![\w.])at\(', 'K.at(', t)
    t = re.sub(r'(?<![\w.])(Gt0|Ge0|Pt|Seg|Circ)\{', r'K.\1{', t)
    t = re.sub(r': (Pt|Seg|Circ)\}', r': K.\1}', t)
    return t

def resolved(name, texts):
    for t in texts:
        if re.search(r'\bpt\(es, ' + name + r'\)', t): return 'K.Pt'
        if re.search(r'\b(d?seg)\(es, ' + name + r'\b', t): return 'K.Seg'
        if re.search(r'\bcirc\(es, ' + name + r'\)', t): return 'K.Circ'
    return None

def call_arg(name, ty):
    return {'K.Pt': 'K.pt(es, %s)', 'K.Seg': 'K.seg(es, %s)', 'K.Circ': 'K.circ(es, %s)'}.get(ty, '%s') % name

out = ["# Generated from spec/sketch.bend by mforms.py: each constraint kind's",
       "# holds (H), meaning (M) and merge condition (W), with its references",
       "# already resolved (points, segments and circles as values).", "",
       "import Base", "import ../spec/num.bend as S", "import ../spec/ring.bend as E",
       "import ../spec/field.bend as O", "import ../spec/geom.bend as G", "import ../spec/sketch.bend as K", ""]
disp_s, disp_c = [], []
for kind, fields in kinds:
    names = E[kind][0] if kind in E else [f[0] for f in fields]
    texts = [E.get(kind, ([], ''))[1], Si.get(kind, ([], ''))[1], W.get(kind, ([], ''))[1], M.get(kind, ([], ''))[1]]
    for d in (Si, W, M):
        if kind in d: assert d[kind][0] == names, (kind, d[kind][0], names)
    params = []
    for (fname, fty), n in zip(fields, names):
        params.append((n, resolved(n, texts) or fty))
    ps = ", ".join("+%s: %s" % (n, t) for n, t in params)
    args = ", ".join(n for n, _ in params)
    eqs = qualify(E[kind][1]).replace("\n", "\n    ")
    sides = qualify(Si[kind][1]) if kind in Si else '[]'
    wf = qualify(W[kind][1]) if kind in W else 'Unit'
    mean = qualify(M[kind][1])
    out.append("def H.%s(~F: O.OField, +env: List<&2, O.C(F)>, %s) -> Type:" % (kind, ps))
    out.append("  K.Zeros(~F, env, %s) & K.Sides(~F, env, %s)" % (eqs, sides.replace("\n", "\n    ")))
    out.append("")
    out.append("def M.%s(~F: O.OField, +env: List<&2, O.C(F)>, %s) -> Type:" % (kind, ps))
    out.append("  " + mean)
    out.append("")
    out.append("def W.%s(%s) -> Type:" % (kind, ps))
    out.append("  " + wf)
    out.append("")
    cargs = ", ".join(call_arg(n, t) for n, t in params)
    disp_s.append("    case K.%s{%s}:\n      %s.sound(~F, env, %s, w, h)" % (kind, ", ".join(names), kind, cargs))
    disp_c.append("    case K.%s{%s}:\n      %s.complete(~F, env, %s, h)" % (kind, ", ".join(names), kind, cargs))
open(os.path.join(ROOT, 'lib/mforms.bend'), 'w').write("\n".join(out))
open(os.path.join(ROOT, 'tools/drafts/dispatch.draft'), 'w').write(
"""# Every kind: the exact form implies the meaning
def means_sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +k: K.Constraint, w: K.Constraint.wf(es, k), h: K.Constraint.holds(~F, env, es, k)) -> K.Constraint.means(~F, env, es, k):
  match k:
""" + "\n".join(disp_s) + """

# Every kind: the meaning implies the exact form
def means_complete(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +k: K.Constraint, h: K.Constraint.means(~F, env, es, k)) -> K.Constraint.holds(~F, env, es, k):
  match k:
""" + "\n".join(disp_c) + "\n")
print(len(kinds), "kinds")
