#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
echo '1/10: exact audit of the fixed coarse angular table'
python3 verify_coarse_angles.py > coarse_angle_report.txt
python3 verify_pi_bounds.py > pi_bounds.log
echo '2/10: full 760-pattern stage 0'
g++ -O3 -std=c++17 verify_integer_cycles.cpp -o .stage0
./.stage0 --list > verified_orbits.tsv
grep -q 'TOTAL 760 = analytic 0 + graph 382 + UNKNOWN 378' verified_orbits.tsv
echo '3/10: rational angular table generation'
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
echo '4/10: branch/rank pruning 378 -> 23'
g++ -O3 -std=c++17 verify_subdivided_prune3.cpp -o .stage3
./.stage3 8 > stage3.tsv 2> stage3.log
python3 - <<'PY'
rows=[line.rstrip('\n').split('\t') for line in open('stage3.tsv')]
unknown=[r for r in rows if r[0]=='UNKNOWN']
assert len(rows)==378, len(rows)
assert len(unknown)==23, len(unknown)
assert len({(r[1],r[2]) for r in rows})==len(rows), 'duplicate stage-3 orbit'
print('Stage 3 coverage:',len(rows),'classes;',len(unknown),'survive')
PY
echo '5/10: branch/rank pruning 23 -> 4'
g++ -O3 -std=c++17 verify_subdivided_prune4.cpp -o .stage4
./.stage4 8 > stage4.tsv 2> stage4.log
python3 - <<'PY'
a=[p.rstrip('\n').split('\t') for p in open('stage4.tsv')]
assert len(a)==23,a
assert len({(x[1],x[2]) for x in a})==len(a),'duplicate stage-4 orbit'
unknown=[x for x in a if x[0]=='UNKNOWN']
assert len(unknown)==4,unknown
assert {(x[1],x[2]) for x in unknown}=={('5','000100100010101'),('5','000100100100101'),('5','001001001001001'),('6','001001001001011')},unknown
print('Stage 4 coverage:',len(a),'classes;',len(unknown),'survivors match the expected four')
PY
echo '6/10: enumerate all coarse radial survivors (not merely first witness)'
g++ -O3 -std=c++17 enumerate_residual.cpp -o .enumerate
./.enumerate 6 > full_residuals.txt 2> enumerate.log
python3 - <<'PY'
rows=[l.rstrip('\n').split('\t') for l in open('full_residuals.txt') if l.startswith('UNKNOWN\t')]
expected={'000100100010101':47,'000100100100101':38,'001001001001001':1181,'001001001001011':3}
assert len(rows)==4, rows
assert {r[2]:int(r[3]) for r in rows}==expected, rows
for r in rows:
    assignments=[x for x in r[5].split(',') if x]
    assert int(r[3])==int(r[4])==len(assignments),(r[2],r[3],r[4],len(assignments))
    assert len(assignments)==len(set(assignments)),('duplicate radial assignment',r[2])
    assert all(len(x)==int(r[1]) and x.isdigit() for x in assignments),(r[2],'bad assignment encoding')
print('All coarse radial survivors are listed exactly once:',sum(expected.values()))
PY
echo '7/10: certify 6+9 orbit, 2 noncanonical 5+10 orbits'
python3 certify_six_nine.py > six_nine.log
python3 verify_noncanonical_exact.py > noncanonical.log
echo '8/10: certify canonical orbit outside local angular region'
python3 verify_canonical_exact.py > canonical.log
echo '9/10: generate and independently check exact subdivision trees'
python3 make_exact_certificate.py > certificate_generation.log
python3 check_exact_certificate.py > certificate_check.log
cat certificate_check.log
echo '10/10: verify exact algebraic/local derivative bounds'
python3 verify_local_constants.py > local.log
cat local.log
echo 'ALL COMPUTATIONAL CHECKS PASSED (analytic proof obligations described in PROOF_SKETCH.md)'
