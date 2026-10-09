"""Verify full characteristic-zero coefficient table against 10391 modular images.
The C++ generating code independently checks interpolation against 3 held-out integer evaluations.
"""
import csv,json,hashlib
from fractions import Fraction
from pathlib import Path
p=10391
fn=Path('/mnt/data/circle_G112_exact_coefficients.tsv')
assert fn.exists(), f'Missing {fn}: run exact_coeffs_quotient_omp first'
with fn.open() as f:
    rows=list(csv.DictReader(f,delimiter='\t'))
assert len(rows)==113
before=json.loads(Path('/mnt/data/circle_degree112_mod_10391.json').read_text())
errors=[]
for i,row in enumerate(rows):
    assert int(row['power'])==i
    for j in range(16):
        rat=Fraction(row[f'basis_{j}'])
        den=rat.denominator%p
        if not den:
            errors.append(f'noninvertible denominator at i={i}, mask={j}')
            continue
        val=(rat.numerator%p)*pow(den,-1,p)%p
        exp=before['basis_coefficients_ascending'][i][j]
        if val!=exp:
            errors.append(f'coefficient mismatch: i={i}, mask={j}, got={val}, expected={exp}')
print('rows',len(rows),'basis coordinates checked',len(rows)*16)
print('unexpected discrepancies',len(errors))
for e in errors[:10]:print(e)
if errors:raise SystemExit(1)
print('PASS: all exact coefficients reduce to earlier independently computed finite-field coefficients')
print('bytes:',fn.stat().st_size,'sha256:',hashlib.sha256(fn.read_bytes()).hexdigest())
for i in (112,111,110,1,0):
    coeff={j:rows[i][f'basis_{j}'] for j in range(16) if rows[i][f'basis_{j}']!='0'}
    print('degree',i,'nonzero basis',len(coeff),'first:', list(coeff.items())[:3])
