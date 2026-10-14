#!/usr/bin/env python3
"""Type-check the open law statements in ROADMAP.bend.

`bend ROADMAP.bend` stops at the count of open laws before type-checking,
so an open law's statement would otherwise go unchecked. This turns each
law of ROADMAP.bend that no tests/*.bend restates (those are checked by
the gate through their restatements and tools/lawsync.py) into a def that
takes one more hypothesis, False == True, and is filled by it: so only the
statement is checked, nothing is proven. Run from bend-cad/; exit 1 if
Bend rejects any statement.
"""
import glob, re, subprocess, sys

road = open('ROADMAP.bend').read()
tests = ''.join(open(p).read() for p in glob.glob('tests/*.bend'))
imports = '\n'.join(l.replace('import ./', 'import ../') for l in road.splitlines()
                    if l.startswith('import ') and 'LAWS.bend' not in l)
out = [imports, '''
def stmt_pick(b: Bool, P: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      P

def stmt_absurd(P: Type, e: {False{} == True{} : Bool}) -> P:
  %e : stmt_pick(_, P)
  Unit{}
''']
names = []
for m in re.finditer(r'^law (\w+):\n((?:  .*\n?)+)', road, re.M):
    name = m.group(1)
    if re.search(r'^def ' + name + r'\(', tests, re.M):
        continue
    lines = [l.strip() for l in m.group(2).splitlines() if l.strip()]
    params = [l[4:].strip() for l in lines if l.startswith('for ')]
    concl = [l for l in lines if not l.startswith('for ')]
    if len(concl) != 1:
        print('CANNOT READ', name); sys.exit(1)
    names.append(name)
    out.append('def stmt_' + name + '(' + ', '.join(params + ['stmt_bot: {False{} == True{} : Bool}'])
               + ') -> ' + concl[0] + ':\n  stmt_absurd(' + concl[0] + ', stmt_bot)\n')
if not names:
    print('no open statements'); sys.exit(0)
path = 'proto/_stmtcheck.bend'
open(path, 'w').write('\n'.join(out))
r = subprocess.run(['bin/bend', path, '--check-only'], capture_output=True, text=True)
text = r.stdout + r.stderr
ok = r.returncode == 0 and 'All terms check.' in text
print(('STATEMENTS CHECK: ' if ok else 'STATEMENTS REJECTED: ') + ', '.join(names))
if not ok:
    print(text[-3000:])
sys.exit(0 if ok else 1)
