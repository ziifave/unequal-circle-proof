"""Run core independent exact arithmetic checks for the degree-1792 claim."""
from pathlib import Path
import sys, subprocess
base=Path(__file__).resolve().parent
scripts=(
 'circle_content_lower_bounds.py',
 'circle_local_field.py',
 'circle_degree_leading_mod.py',
 'circle_modular_certificate.py',
 'circle_radius_root_interval_certificate.py',
)
for n in scripts:
 c=subprocess.run([sys.executable,str(base/n)],text=True,capture_output=True,check=True)
 print('PASS:',n)
 print(c.stdout.strip()[-500:])
assert (base/'circle_field_modular_recheck.exit').read_text().strip()=='0'
assert 'ALL 120 CONJUGATE PAIRS COPRIME' in (base/'circle_field_modular_recheck.log').read_text()
print('PASS: independent 16-conjugate recomputation, all 120 pairwise gcds')
