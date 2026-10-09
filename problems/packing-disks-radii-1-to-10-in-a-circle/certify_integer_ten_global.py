#!/usr/bin/env python3
"""Replay the exact lower and upper witnesses for the 10 integer-radius disks.

Runs exact Fraction-only proof components, rejecting assertion-removing Python modes.
The certificate is read as DATA, never executed as code.
"""
from pathlib import Path
import subprocess, sys
if sys.flags.optimize: raise SystemExit('Run without -O/-OO')
HERE=Path(__file__).resolve().parent
for name,required in (
    ('verify_ten_upper.py', ('PASS exact angle-root existence and uniqueness','PASS exact upper witness')),
    ('verify_ten_global_tree.py', ('PASS exhaustive 60 cyclic orders','PASS near-boundary local angular monotonicity')),
):
    p=subprocess.run([sys.executable,str(HERE/name)],cwd=HERE,capture_output=True,text=True)
    if p.returncode:
        raise SystemExit(f'{name}: FAIL\n{p.stdout}\n{p.stderr}')
    if not all(mark in p.stdout for mark in required):
        raise SystemExit(f'{name}: missing PASS markers\n{p.stdout}')
    print(f'{name}: PASS')
    for line in p.stdout.splitlines():
        if line.startswith(('root bracket','strict noncontacts','TREE')):print(line)
print('VERIFIED (under the explicitly stated Python/standard-library trust assumptions): R* = R0')
