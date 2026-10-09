#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
echo '1/9: exact audit of the fixed coarse angular table'
python3 verify_coarse_angles.py > coarse_angle_report.txt
echo '2/9: full 760-pattern stage 0'
g++ -O3 -std=c++17 verify_integer_cycles.cpp -o .stage0
./.stage0 --list > verified_orbits.tsv
grep -q 'TOTAL 760 = analytic 0 + graph 382 + UNKNOWN 378' verified_orbits.tsv
echo '3/9: rational angular table generation'
python3 build_bounds3.py > q3_report.txt
python3 build_bounds4.py > q4_report.txt
# Guard against accidentally running a C++ checker using an unverified table.
python3 - <<'PY'
import re
for typ,file,tab in [('Q3','verify_subdivided_prune3.cpp','Q3.txt'),('Q4','verify_subdivided_prune4.cpp','Q4.txt')]:
    src=open(file).read()
    m=re.search(r'constexpr int Q\[\d+\]\[\d+\]\s*=\s*\{(.*?)\n\};',src,re.S)
    assert m is not None,(typ,'missing C++ table')
    rows=re.findall(r'\{([^{}]+)\}',m.group(1))
    ints=[[int(x.strip()) for x in z.split(',') if x.strip()] for z in rows]
    regenerated=[[int(x) for x in line.split()] for line in open(tab)]
    assert ints==regenerated,(typ,'table mismatch')
    print(typ,'verified table matches C++ source')
PY
echo '4/9: branch/rank pruning 378 -> 23'
g++ -O3 -std=c++17 verify_subdivided_prune3.cpp -o .stage3
./.stage3 8 > stage3.tsv 2> stage3.log
echo '5/9: branch/rank pruning 23 -> 4'
g++ -O3 -std=c++17 verify_subdivided_prune4.cpp -o .stage4
./.stage4 8 > stage4.tsv 2> stage4.log
python3 - <<'PY'
a=[p.rstrip('\n').split('\t') for p in open('stage4.tsv') if p.startswith('UNKNOWN')]
assert len(a)==4,a
assert {(x[1],x[2]) for x in a}=={('5','000100100010101'),('5','000100100100101'),('5','001001001001001'),('6','001001001001011')},a
print('Exactly 4 surviving canonical/near-canonical pattern classes')
PY
echo '6/9: enumerate all coarse radial survivors (not merely first witness)'
g++ -O3 -std=c++17 enumerate_residual.cpp -o .enumerate
./.enumerate 6 > full_residuals.txt 2> enumerate.log
python3 - <<'PY'
a={r[2]:int(r[3]) for l in open('full_residuals.txt') if len(r:=l.rstrip('\n').split('\t'))>=6 and r[0]=='UNKNOWN'}
assert a=={'000100100010101':47,'000100100100101':38,'001001001001001':1181,'001001001001011':3},a
print('Full coarse radial box list matches expectation')
PY
echo '7/9: certify 6+9 orbit, 2 noncanonical 5+10 orbits'
python3 certify_six_nine.py > six_nine.log
python3 verify_noncanonical_exact.py > noncanonical.log
echo '8/9: certify canonical orbit outside local angular region'
python3 verify_canonical_exact.py > canonical.log
echo '9/9: verify exact algebraic/local derivative bounds'
python3 verify_local_constants.py > local.log
cat local.log
echo 'ALL COMPUTATIONAL CHECKS PASSED (analytic proof obligations described in PROOF_SKETCH.md)'
