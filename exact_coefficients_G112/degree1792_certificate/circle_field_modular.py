"""Reconstruct the monic degree-112 candidate eliminant in K mod 10391.
K=Q(sqrt2,sqrt3,sqrt5,sqrt7); p totally splits.
This is FINITE FIELD evidence only.
"""
import sympy as sp
import modular_eliminant as m
from itertools import product, combinations
from hashlib import sha256
from pathlib import Path
import json
p=10391
X=sp.Symbol('X')
m.p=p
primes=(2,3,5,7)
roots={j:int(sp.sqrt_mod(j,p)) for j in primes}

def interp_conjugate(sgn):
    m.sqs={j:roots[j]*sgn[i]%p for i,j in enumerate(primes)}
    rr={j:m.rad(j) for j in (2,5,6,7,8,9,10)}
    m.R5,m.R7,m.R10=rr[5],rr[7],rr[10]
    m.d=(rr[5]+rr[7])%p;m.b=(rr[7]+rr[10])%p;m.a=(rr[5]+rr[10])%p
    m.lam=(m.b*m.b+m.d*m.d-m.a*m.a)*pow(2*m.d*m.d,-1,p)%p
    m.kap=4*m.R5*m.R7*m.R10*(m.R5+m.R7+m.R10)*pow(m.d,-4,p)%p
    def den(v):
        ret=pow((v+rr[10])%p,16,p)
        for j in (2,5,6,7,8,9):ret=ret*pow((v-rr[j])%p,32,p)%p
        return ret
    n=113
    xs=[];ys=[]
    for x in range(p):
        d=den(x)
        if d==0:continue
        try:y=m.evaluate(x)*pow(d,-1,p)%p
        except (ValueError, ZeroDivisionError): continue
        xs.append(x);ys.append(y)
        if len(xs)>=n+12:break
    assert len(xs)==n+12
    diff=ys[:n]
    for j in range(1,n):
        for i in range(n-1,j-1,-1):diff[i]=(diff[i]-diff[i-1])*pow(xs[i]-xs[i-j],-1,p)%p
    P=[0]*n;basis=[1]
    for i,a in enumerate(diff):
        for k,c in enumerate(basis):P[k]=(P[k]+a*c)%p
        if i+1<n:basis=m.mul(basis,[-xs[i],1])
    # Verification at held-out points not used to interpolate
    assert all(sum(v*pow(xs[i],j,p) for j,v in enumerate(P))%p==ys[i] for i in range(n,n+12))
    # Distant held-out evaluations, guarding against low-degree interpolation artefacts.
    for x in (619, 2711, 5999, 10003):
        if den(x)==0: continue
        try: val=m.evaluate(x)*pow(den(x),-1,p)%p
        except (ValueError, ZeroDivisionError): continue
        assert sum(v*pow(x,j,p) for j,v in enumerate(P))%p == val
    assert P[-1]!=0
    inv=pow(P[-1],-1,p)
    return [v*inv%p for v in P]

signs=list(product((1,-1), repeat=4))
images={str(s):interp_conjugate(s) for s in signs}
polys={s:sp.Poly.from_list(images[str(s)][::-1],X,modulus=p) for s in signs}
for i,s in enumerate(signs):
    f=polys[s]
    print('conjugate',i,'degree',f.degree(),'irreducible',f.is_irreducible,flush=True)
# Different conjugates must be coprime (a stronger check than distinct polynomials)
assert all(sp.gcd(polys[a],polys[b]).degree()==0 for a,b in combinations(signs,2))
print('ALL 120 CONJUGATE PAIRS COPRIME',flush=True)
# Invert the Walsh/Galois transform: c_s = sum_B a_B * e_B(s)
# e_B(s) = prod sqrt(j) for j in B, with signs multiplied.
Kcoeff=[]
for degree in range(113):
    row=[]
    for mask in range(16):
        subset=[j for k,j in enumerate(primes) if (mask>>k)&1]
        numerator=sum(((-1)**sum(1 for k in range(4) if mask>>k&1 and s[k]==-1))
                      *images[str(s)][degree] for s in signs)
        denom=16
        for j in subset:denom=denom*roots[j]%p
        row.append(numerator*pow(denom,-1,p)%p)
    Kcoeff.append(row)
# Check all embeddings exactly from the 16 coefficients in K tensor Fp.
for s in signs:
    for degree in range(113):
        value=0
        for mask,a in enumerate(Kcoeff[degree]):
            factor=1
            for k,j in enumerate(primes):
                if mask>>k&1: factor=factor*roots[j]*s[k]%p
            value=(value+a*factor)%p
        assert value==images[str(s)][degree]
print('16 GALOIS EMBEDDINGS RECOVERED FROM K-BASIS COEFFICIENTS',flush=True)
assert Kcoeff[112] == [1]+[0]*15
print('MONIC DEGREE-112 POLYNOMIAL OVER K / p, VERIFIED',flush=True)
# Norm polynomial mod p is product across embeddings, monic, degree 1792
norm=sp.Poly(1,X,modulus=p)
for s in signs:norm=norm*polys[s]
assert norm.degree()==1792
normcoeff=[int(v)%p for v in norm.all_coeffs()]
print('NORM degree',norm.degree(),'SHA256',sha256(json.dumps(normcoeff).encode()).hexdigest(),flush=True)
report={
 'warning':'MODULAR PROJECTION ONLY. Not the characteristic-zero minimal polynomial.',
 'p':p,'base_roots':roots,'extension_basis':'sqrt2^a sqrt3^b sqrt5^c sqrt7^d, mask bits a,b,c,d',
 'basis_coefficients_ascending':Kcoeff,
 'all_embedding_coefficients_ascending':images,
 'norm_mod_p_coefficients_descending':normcoeff,
 'norm_SHA256':sha256(json.dumps(normcoeff).encode()).hexdigest(),
 'properties':{'degree_K':112,'conjugates':16,'pairwise_coprime':True,'degree_modular_norm':1792,
 'all_degree112_irreducible_mod_p':all(polys[s].is_irreducible for s in signs)}
}
path=Path('/mnt/data/circle_degree112_mod_10391.json')
path.write_text(json.dumps(report,ensure_ascii=False))
print('OUTPUT',path,'SIZE',path.stat().st_size,flush=True)
