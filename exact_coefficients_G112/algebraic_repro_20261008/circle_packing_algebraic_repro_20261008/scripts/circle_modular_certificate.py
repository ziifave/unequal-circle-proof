"""Independent Rabin irreducibility check for finite-field degree-112 factor.
This certificate proves only the finite-field statement, not the characteristic-zero minimal polynomial.
"""
import ast
from pathlib import Path
from sympy.polys.galoistools import gf_pow_mod, gf_gcd, gf_sub
from sympy.polys.domains import ZZ

import json
p=10391
report=json.loads((Path(__file__).resolve().parents[1]/'data/G112_mod10391_reference.json').read_text())
ascending=report['all_embedding_coefficients_ascending']['(1, 1, 1, 1)']
assert len(ascending)==113
lead=ascending[-1]
poly=[(x*pow(lead,-1,p))%p for x in reversed(ascending)]
assert len(poly)==113 and poly[0]==1
x=[1,0]
# Rabin criterion: for n=112=2^4*7, check gcd(X^(p^(112/q))-X,f)=1 for q=2,7
# and X^(p^112)=X (mod f).
frobenius=x
for i in range(1,113):
    frobenius=gf_pow_mod(frobenius,p,poly,p,ZZ)
    if i in [16,56,112]:
        h=gf_gcd(poly,gf_sub(frobenius,x,p,ZZ),p,ZZ)
        print('k=',i,'gcd_degree=',len(h)-1,'is_x=',frobenius==x,flush=True)
        if i in [16,56]:assert len(h)==1
        if i==112:assert frobenius==x
print('RABIN IRREDUCIBILITY TEST: PASS, degree=112, F_%d'%p,flush=True)
