#!/usr/bin/env python3
"""Check that the laws drafted in ROADMAP.bend say exactly what their
restatements in tests/ prove.

`bend ROADMAP.bend` stops at the count of open laws before type-checking,
so a draft statement there is checked only through a restatement in a
gated test (a def of the same name whose body is the proof). For every
`law X:` in ROADMAP.bend that some tests/*.bend defines as `def X(...)`,
this turns the law into a def signature and compares: same binders in the
same order, same types, same conclusion. Binder reuse markers (`+`) and
parentheses around the whole conclusion are ignored. A law with no
restatement is simply open. Run from bend-cad/; exit 1 on any difference.
"""
import glob, re, sys

def norm(binders, concl):
    bs = [re.sub(r'^\+', '', b.strip()) for b in binders]
    c = concl.strip()
    if c.startswith('(') and c.endswith(')'):
        depth = 0
        whole = True
        for i, ch in enumerate(c):
            depth += ch == '('
            depth -= ch == ')'
            if depth == 0 and i < len(c) - 1:
                whole = False
                break
        if whole:
            c = c[1:-1].strip()
    return bs, c

def split_top(s):
    out, depth, cur = [], 0, ''
    for k, ch in enumerate(s):
        if ch in '({<':
            depth += 1
        elif ch in ')}' or (ch == '>' and s[k - 1:k] != '-'):
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur); cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out

road = open('ROADMAP.bend').read()
tests = {p: open(p).read() for p in sorted(glob.glob('tests/*.bend'))}
ok = True
for m in re.finditer(r'^law (\w+):\n((?:  .*\n?)+)', road, re.M):
    name = m.group(1)
    found = [(p, t) for p, t in tests.items() if re.search(r'^def ' + name + r'\(', t, re.M)]
    if not found:
        print('open', name); continue
    if len(found) > 1:
        print('TWO restatements of', name, [p for p, _ in found]); ok = False; continue
    path, test = found[0]
    lines = [l.strip() for l in m.group(2).splitlines() if l.strip()]
    binders = [l[len('for'):].strip() for l in lines if l.startswith('for ')]
    concl = [l for l in lines if not l.startswith('for ')]
    if len(concl) != 1:
        print('CANNOT READ', name); ok = False; continue
    lb, lc = norm(binders, concl[0])
    d = re.search(r'^def ' + name + r'\((.*):$', test, re.M)
    if not d:
        print('CANNOT FIND the def', name, 'in', path); ok = False; continue
    sig, depth = d.group(1), 1
    for j, ch in enumerate(sig):
        depth += ch == '('
        depth -= ch == ')'
        if depth == 0:
            break
    if not sig[j + 1:].startswith(' -> '):
        print('CANNOT READ the test def', name); ok = False; continue
    db, dc = norm(split_top(sig[:j]), sig[j + 5:])
    if (lb, lc) == (db, dc):
        print('ok  ', name)
    else:
        ok = False
        print('DIFF', name)
        for i in range(max(len(lb), len(db))):
            a = lb[i] if i < len(lb) else '-'
            b = db[i] if i < len(db) else '-'
            if a != b:
                print('   binder %d: ROADMAP %s | test %s' % (i, a, b))
        if lc != dc:
            print('   conclusion: ROADMAP %s | test %s' % (lc, dc))
print('DRAFTS IN SYNC' if ok else 'DRAFTS DIFFER')
sys.exit(0 if ok else 1)
