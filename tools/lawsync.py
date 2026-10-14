#!/usr/bin/env python3
"""Check that the sk-06 laws in ROADMAP.bend say exactly what
tests/plan_laws.bend proves.

`bend ROADMAP.bend` stops at the count of open laws before type-checking,
so the statements there are checked only through their restatements in
tests/plan_laws.bend (each a def whose body is the proof). This turns
every `law X:` of the sk-06 sections into a def signature and compares it
with the test's `def X(...)` line: same binders in the same order, same
types, same conclusion. Binder reuse markers (`+`) and parentheses around
the whole conclusion are ignored. Run from bend-cad/; exit 1 on any
difference.
"""
import re, sys

LAWS = ['plan_exists', 'plan_unique', 'box_sides', 'sketch_exists', 'sketch_unique']

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
test = open('tests/plan_laws.bend').read()
ok = True
for name in LAWS:
    m = re.search(r'^law ' + name + r':\n((?:  .*\n?)+)', road, re.M)
    if not m:
        print('MISSING in ROADMAP.bend:', name); ok = False; continue
    lines = [l.strip() for l in m.group(1).splitlines() if l.strip()]
    binders = [l[len('for'):].strip() for l in lines if l.startswith('for ')]
    concl = [l for l in lines if not l.startswith('for ')]
    if len(concl) != 1:
        print('CANNOT READ', name); ok = False; continue
    lb, lc = norm(binders, concl[0])
    d = re.search(r'^def ' + name + r'\((.*):$', test, re.M)
    if not d:
        print('MISSING in tests/plan_laws.bend:', name); ok = False; continue
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
print('LAWS IN SYNC' if ok else 'LAWS DIFFER')
sys.exit(0 if ok else 1)
