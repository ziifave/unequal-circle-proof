#!/usr/bin/env python3
"""One-command global 8-disk packing proof replay; verification does not use floats.
Runs two independently specified stages: exact upper witness and exact global lower tree.
"""
import sys,subprocess
from pathlib import Path
if sys.flags.optimize:raise SystemExit('run without -O/-OO')
HERE=Path(__file__).resolve().parent

def verify(stage,path,markers):
    result=subprocess.run([sys.executable,str(HERE/path)],cwd=HERE,text=True,capture_output=True)
    if result.returncode:
        print(result.stdout);print(result.stderr,file=sys.stderr)
        raise SystemExit(f'{stage} FAILED: exit={result.returncode}')
    if not all(k in result.stdout for k in markers):
        raise SystemExit(f'{stage} FAILED: missing expected success markers\n'+result.stdout)
    print('PASS',stage)
    return result.stdout

if __name__=='__main__':
    verify('Exact root and eight-disk witness','verify_eight_upper.py',
           ['PASS exact angle-root existence and uniqueness by monotonicity',
            'PASS exact upper witness: 6 tangent wall disks and 2 rational small disk centers'])
    report=verify('Finite rational global lower certificate','verify_eight_global_tree.py',
                  ['PASS strict pi lower and upper bounds','PASS exhaustive 60 cyclic orders',
                   'PASS near-boundary local angular monotonicity certificate',
                   'CERTIFIED: No six disks of radii 3,...,8 can fit in radius R<R0'])
    for line in report.splitlines():
        if line.startswith('TREE '):print(line)
    print('GLOBAL OPTIMALITY CERTIFIED (subject to soundness of verifier implementations)')
    print('Exact R0: unique root in [16.22174667655772,16.22174667655773]')
    print('Root equation: beta_48+beta_83+beta_36+beta_65+beta_57+beta_74=2*pi')
