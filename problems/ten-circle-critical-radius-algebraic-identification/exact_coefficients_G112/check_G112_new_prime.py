"""Compare exact coefficients to independent resultant computation modulo a *new* prime 1129."""
from fractions import Fraction
import csv
from itertools import product
import sympy as sp
import modular_eliminant as m
p=1129
m.p=p
roots={i:int(sp.sqrt_mod(i,p)) for i in (2,3,5,7)}
assert all(v for v in roots.values())
rows=list(csv.DictReader(open('/mnt/data/circle_G112_exact_coefficients.tsv'),delimiter='\t'))
coeffs=[]
for row in rows:
    z=[]
    for i in range(16):
        q=Fraction(row[f'basis_{i}'])
        z.append(q.numerator*pow(q.denominator,-1,p)%p)
    coeffs.append(z)
counts=0
for signs in ((1,1,1,1),(1,-1,1,1),(-1,-1,-1,1),(1,-1,-1,-1)):
    m.sqs={i:roots[i]*s%p for i,s in zip((2,3,5,7),signs)}
    r={i:m.rad(i) for i in (2,5,6,7,8,9,10)}
    m.R5,m.R7,m.R10=r[5],r[7],r[10]
    m.d=(r[5]+r[7])%p;m.b=(r[7]+r[10])%p;m.a=(r[5]+r[10])%p
    m.lam=(m.b*m.b+m.d*m.d-m.a*m.a)*pow(2*m.d*m.d,-1,p)%p
    m.kap=4*m.R5*m.R7*m.R10*(m.R5+m.R7+m.R10)*pow(m.d,-4,p)%p
    bvec=[]
    for i in range(16):
        v=1
        for j,root in enumerate((2,3,5,7)):
            if (i>>j)&1: v=v*m.sqs[root]%p
        bvec.append(v)
    coefs=[sum(a*b for a,b in zip(row,bvec))%p for row in coeffs]
    for x in (0,1,2,14,100,241,441,850,1019):
        den=pow((x+r[10])%p,16,p)
        for i in (2,5,6,7,8,9):den=den*pow((x-r[i])%p,32,p)%p
        if den==0: continue
        expect=sum(a*pow(x,i,p) for i,a in enumerate(coefs))%p
        got=m.evaluate(x)*pow(den,-1,p)%p
        # Our characteristic-zero G is monic; divide by char-zero LC mod p
        # Normalize by ratio at one point, checking all subsequent points
        if x==0: ratio=got*pow(expect,-1,p)%p
        assert got==expect*ratio%p,(signs,x,got,expect,ratio)
        counts+=1
    print('verified sign embedding',signs,'at 9 points')
print('new prime p',p,'independent evaluations',counts,'PASS')
