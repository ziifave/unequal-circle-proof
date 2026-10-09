#!/usr/bin/env python3
"""One-command exact certificate replay for the 9-disk integer-radius case."""
import sys,subprocess
from pathlib import Path
if sys.flags.optimize:raise SystemExit('run without -O/-OO')
HERE=Path(__file__).resolve().parent
for name,markers in [('verify_nine_upper.py', ['PASS exact angle-root existence','PASS exact upper witness']),('verify_nine_global_tree.py',['PASS exhaustive 60 cyclic orders', 'PASS near-boundary local angular monotonicity certificate'])]:
    proc=subprocess.run([sys.executable,str(HERE/name)],cwd=HERE,text=True,capture_output=True)
    if proc.returncode:
        raise SystemExit(name+' failed:\n'+proc.stdout+'\n'+proc.stderr)
    if not all(m in proc.stdout for m in markers):
        raise SystemExit(name+' missing expected acceptance markers:\n'+proc.stdout)
    print(name+': PASS')
    for line in proc.stdout.splitlines():
        if line.startswith(('TREE','strict noncontacts','root bracket')):print(line)
print('GLOBAL OPTIMALITY CHECKS COMPLETED (under verifier trust assumptions)')
