#!/usr/bin/env python3
"""Type-check the open cert_* law statements in ROADMAP.bend.

`bend ROADMAP.bend` stops at the count of open laws before type-checking,
so this fills each cert_* law against the reject-everything stub checker
(the `check == True` hypothesis is absurd) in a throwaway file and checks
that. It proves nothing about a real checker. Prints Bend's verdict; open
laws imported from LAWS.bend still count as TODOs. Run from bend-cad/.
"""
import re, subprocess, os, sys
src = open('ROADMAP.bend').read()
sec = src[src.index('law cert_'):]
laws = re.findall(r'law (cert_\w+):\n((?:  .*\n?)+)', sec)
out = ['''import Base
import ../ROADMAP.bend as Laws
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/cert.bend as C

def pick(b: Bool, P: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      P

def absurd(P: Type, e: {False{} == True{} : Bool}) -> P:
  %e : pick(_, P)
  Unit{}
''']
for name, body in laws:
    lines = [l.strip() for l in body.strip('\n').split('\n')]
    params = [re.match(r'for\s+([~+]?)(\w+):', l).group(2) for l in lines if l.startswith('for')]
    concl = [l for l in lines if not l.startswith('for')][0]
    out.append('def Laws.' + name + '(' + ', '.join(params) + '):\n  absurd(' + concl + ', ok)\n')
path = 'proto/_stmtcheck.bend'
open(path, 'w').write('\n'.join(out))
try:
    r = subprocess.run(['bin/bend', path, '--check-only'], capture_output=True, text=True)
    print((r.stdout + r.stderr).strip()[-2000:])
    print('filled:', ', '.join(n for n, _ in laws))
finally:
    os.remove(path)
